# VVMF modular module API, version 1.
#
# The evaluation layer of generated modular modules (Stage 9), embedded verbatim after the modular runtime
# (modular_runtime.py). ModularPythonIR.wl selects the "common" section and the "model" or "forms" section. The code
# reads module constants written by the generator before it:
#   (imports re as _mm_re and time as _mm_time; Stage 6 helpers own names such as _re) backend, working_precision, form_ids, output_names, _MM_RECIPES, _MM_EVIDENCE, _MM_DIMENSIONS, _MM_POLICY and
#   either _MM_OUTPUT_SLOTS, form_evaluation and the Stage 6 helpers (_context, _c, _vector, _validate_inputs,
#   _evaluate_all, _evaluate_output) of a model module, or _MM_OUTPUT_NODES of a form module.
# Points are closed tagged records made by tau_point / q_point; nothing is evaluated as source.

# ==== section: common

_MM_DECIMAL = _mm_re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")


def _mm_decimal_text(text, where):
    if not _MM_DECIMAL.fullmatch(text):
        raise ValueError(where + " is not a decimal number: " + repr(text))
    return text


def _mm_complex_text(text, where):
    """A strict parse of a decimal complex string: "a", "bj", "a+bj" or "a-bj" (no expressions are evaluated)."""
    t = text.replace(" ", "")
    if not t.endswith(("j", "J")):
        return _mm_decimal_text(t, where), "0"
    body = t[:-1]
    split = None
    for i in range(len(body) - 1, 0, -1):
        if body[i] in "+-" and body[i - 1] not in "eE":
            split = i
            break
    re_part, im_part = ("0", body) if split is None else (body[:split], body[split:])
    if im_part in ("", "+", "-"):
        im_part += "1"
    return _mm_decimal_text(re_part, where), _mm_decimal_text(im_part, where)


def _mm_number_record(value, where):
    """Exact or decimal records of the real and imaginary parts of an input number."""
    if isinstance(value, bool) or type(value).__name__ in ("bool", "bool_"):
        raise TypeError(where + " must be a number, not " + type(value).__name__)
    if isinstance(value, str):
        re_text, im_text = _mm_complex_text(value, where)
        return ["d", re_text], ["d", im_text]
    if isinstance(value, (_fractions.Fraction, _numbers.Integral)):
        f = _fractions.Fraction(value)
        return ["q", str(f.numerator), str(f.denominator)], ["q", "0", "1"]
    if isinstance(value, _decimal.Decimal):
        if not value.is_finite():
            raise ValueError(where + " must be finite")
        return ["d", str(value)], ["q", "0", "1"]
    if hasattr(value, "_mpf_") or hasattr(value, "_mpc_"):
        import mpmath
        ctx = mpmath.mp.clone()
        ctx.dps = max(working_precision or 17, 17) + 5
        z = ctx.mpc(value)
        if not ctx.isfinite(z):
            raise ValueError(where + " must be finite")
        return ["d", ctx.nstr(z.real, ctx.dps)], ["d", ctx.nstr(z.imag, ctx.dps)]
    if isinstance(value, _numbers.Complex):
        z = complex(value)
        if not (_math.isfinite(z.real) and _math.isfinite(z.imag)):
            raise ValueError(where + " must be finite")
        return ["d", repr(z.real)], ["d", repr(z.imag)]
    raise TypeError(where + " must be a number or a decimal string, not " + type(value).__name__)


def _mm_backend(deadline=None):
    b = _MrBackend(backend, working_precision)
    b.deadline = deadline
    return b


def tau_point(tau):
    """A point of the upper half plane, Im(tau) > 0: a number, Fraction, Decimal, mpmath value or decimal string ("0.1+1.2j").

    Fractional powers are exp(2 pi i r tau); no reduction to a fundamental domain is made.
    """
    re_record, im_record = _mm_number_record(tau, "tau")
    point = {"kind": "tau", "tau": [re_record, im_record], "backend": backend, "working_precision": working_precision}
    _mr_point(point, _mm_backend())
    return point


def q_point(q, sheet=0):
    """A point given by q = exp(2 pi i tau), 0 <= |q| < 1, and an integer sheet n: 2 pi i tau = log(q) + 2 pi i n (q = 0: the cusp)."""
    if isinstance(sheet, bool) or not isinstance(sheet, _numbers.Integral):
        raise TypeError("sheet must be an integer")
    re_record, im_record = _mm_number_record(q, "q")
    point = {"kind": "q", "q": [re_record, im_record], "sheet": int(sheet), "backend": backend, "working_precision": working_precision}
    _mr_point(point, _mm_backend())
    return point


def _mm_check_point(point):
    if not isinstance(point, dict) or point.get("backend") != backend or point.get("working_precision") != working_precision:
        raise TypeError("point must be made by this module's tau_point or q_point")
    keys = {"tau": {"kind", "tau", "backend", "working_precision"}, "q": {"kind", "q", "sheet", "backend", "working_precision"}}.get(point.get("kind"))
    if keys is None or set(point) != keys:
        raise TypeError("point must be made by this module's tau_point or q_point")
    return point


def _mm_goals(round_):
    """Accuracy and precision goals of a refinement round (five more digits per round, at most the backend digits - 2)."""
    # Goals stay strictly below the backend digits: at the digit count two approximations can agree bit for bit.
    cap = _MM_POLICY["digits"] - 2
    return min(_MM_POLICY["accuracy_goal"] + 5 * round_, cap), min(_MM_POLICY["precision_goal"] + 5 * round_, cap)


def _mm_evaluate_keys(keys, point, b, round_):
    """Each needed recipe once (MLDE families are shared through the backend cache)."""
    results = {}
    for key in keys:
        if key in results:
            continue
        recipe = _MM_RECIPES[key]
        if _MM_POLICY["method"] == "FiniteSeries":
            results[key] = mr_evaluate_definition(recipe, point, b, 0, 0, _MM_POLICY["series_order"], _MM_POLICY["max_series_order"])
        else:
            goal, precision_goal = _mm_goals(round_)
            results[key] = mr_evaluate_definition(recipe, point, b, goal, precision_goal, None, _MM_POLICY["max_series_order"], _MM_POLICY["series_order"])
    return results


def _mm_key_report(key, result):
    if _MM_POLICY["method"] == "FiniteSeries":
        status = "FiniteSeriesApproximation"
    elif result.get("Cusp"):
        status = "CuspValue"
    else:
        status = "SuccessiveApproximations"
    return {"order": result["Order"], "converged": bool(result["Converged"]), "cusp": bool(result.get("Cusp", False)),
            "estimated_error": result.get("EstimatedError"), "status": status, "tail_bound": "NoTailBound", "evidence": dict(_MM_EVIDENCE[key])}


# ==== section: model

def _mm_inputs(ctx, params, fields):
    return _validate_inputs(params, fields) if backend == "NumPy" else _validate_inputs(ctx, params, fields)


def _mm_to_module(ctx, value):
    return _c(value) if backend == "NumPy" else ctx.mpc(value)


def _mm_abs(ctx, value):
    return abs(complex(value)) if backend == "NumPy" else ctx.mpf(abs(value))


def _mm_entries(value):
    if backend == "NumPy":
        return [complex(v) for v in _np.asarray(value).ravel()]
    if isinstance(value, list):
        return [v for row in value for v in row]
    return [value]


def _mm_validate_form_values(ctx, form_values):
    """External form values: exactly the declared slot IDs, each a full vector of finite numbers."""
    if not isinstance(form_values, _Mapping):
        raise TypeError("form_values must be a mapping from slot IDs to full component vectors")
    if any(not isinstance(k, str) for k in form_values):
        raise TypeError("slot IDs must be strings")
    missing = [k for k in form_ids if k not in form_values]
    extra = sorted(k for k in form_values if k not in _MM_DIMENSIONS)
    if missing or extra:
        raise ValueError("form_values must have exactly the keys " + repr(form_ids) + "; missing " + repr(missing) + ", unexpected " + repr(extra))
    if backend == "NumPy":
        return {k: _vector(form_values[k], _MM_DIMENSIONS[k], "form_values[" + repr(k) + "]") for k in form_ids}
    return {k: _vector(ctx, form_values[k], _MM_DIMENSIONS[k], "form_values[" + repr(k) + "]") for k in form_ids}


def _mm_outputs(index, p, f, y, ctx):
    if index is None:
        return _evaluate_all(p, f, y, ctx)
    return {output_names[index]: _evaluate_output(index, p, f, y, ctx)}


def _mm_output_errors(index, p, f, ctx, results, values, keys):
    """The estimated error of every output: its largest change over (a) the previous successive approximation of all
    forms and (b) a real and an imaginary move of each single slot component by its roundoff floor (an estimate, not a
    bound).

    Moving one component at a time also reaches outputs that are invariant under a common scaling of a slot (component
    ratios), which a single correlated move would leave without any floor (review rounds 2 and 3: R1, S1).
    """
    if _MM_POLICY["method"] == "FiniteSeries":
        return {name: None for name in values}, "NoTailBound"
    for key in keys:
        if results[key].get("Previous") is None:
            return {name: None for name in values}, "NoTailBound"
    current = {k: tuple(_mm_to_module(ctx, v) for v in results[k]["Value"]) for k in keys}
    variants = [{k: tuple(_mm_to_module(ctx, v) for v in results[k]["Previous"]) for k in keys}]
    for key in keys:
        for i, (real_floor, imaginary_floor) in enumerate(results[key]["RoundoffParts"]):
            # A real and an imaginary move: outputs may depend on the real or imaginary part only (Re, Im, Conjugate); a
            # component exactly on an axis is not moved off it (U1).
            for step in (real_floor, imaginary_floor * 1j):
                if step == 0:
                    continue
                moved = list(results[key]["Value"])
                moved[i] = moved[i] + step
                variants.append(dict(current, **{key: tuple(_mm_to_module(ctx, v) for v in moved)}))
    # Every output's error is at least the roundoff of its own value (a saturated output never reports zero; U2).
    digits = _MM_POLICY["digits"] - 2
    unit = 10.0 ** (-digits) if backend == "NumPy" else ctx.power(10, -ctx.mpf(digits))
    errors = {name: unit * max([_mm_abs(ctx, v) for v in _mm_entries(values[name])] or [_mm_abs(ctx, 0)]) for name in values}
    for y in variants:
        earlier = _mm_outputs(index, p, f, y, ctx)
        for name in values:
            diffs = [_mm_abs(ctx, a - b) for a, b in zip(_mm_entries(values[name]), _mm_entries(earlier[name]))]
            errors[name] = max([errors[name]] + diffs)
    return errors, "SuccessiveApproximations"


def _mm_accurate(ctx, values, errors):
    """Whether every output meets the requested goals (refinement raises only the slot goals, never this test)."""
    goal, precision_goal = _mm_goals(0)
    tiny = (lambda x: 10.0 ** (-x)) if backend == "NumPy" else (lambda x: ctx.power(10, -ctx.mpf(x)))
    for name in values:
        size = max([_mm_abs(ctx, v) for v in _mm_entries(values[name])] or [_mm_abs(ctx, 0)])
        if errors[name] > max(tiny(goal), tiny(precision_goal) * size):
            return False
    return True


def _mm_model(index, params, point, fields, form_values, report):
    ctx = _context()
    p, f = _mm_inputs(ctx, params, fields)
    _mm_check_point(point)
    keys = form_ids if index is None else _MM_OUTPUT_SLOTS[index]
    if form_evaluation == "External":
        if form_values is None:
            raise ValueError("this module needs form_values: a mapping from every slot ID in form_ids to its component vector")
        y = _mm_validate_form_values(ctx, form_values)
        values = _mm_outputs(index, p, f, y, ctx)
        if not report:
            return values
        return {"Values": values, "Point": dict(point), "WorkingPrecision": working_precision, "Strategy": dict(_MM_POLICY),
                "PerFormReports": {k: {"status": "ExternallySuppliedUncheckedModularity", "estimated_error": None, "error_reason": "UnknownExternalError",
                                       "descriptor": form_descriptors[k]} for k in keys},
                "FinalError": {name: None for name in values}, "FinalErrorStatus": "UnknownExternalError", "Refinements": 0}
    if form_values is not None:
        raise ValueError("this module evaluates its forms itself (Embedded); pass form_values=None")
    b = _mm_backend(_mm_time.monotonic() + _MM_POLICY["time_limit"])
    if _mr_point(point, b) == "cusp":
        _mr_fail("OutsideDomain", "model outputs are evaluated in the upper half plane; a cusp value is a property of a form")
    round_ = 0
    while True:
        results = _mm_evaluate_keys(keys, point, b, round_)
        y = {k: tuple(_mm_to_module(ctx, v) for v in results[k]["Value"]) for k in keys}
        values = _mm_outputs(index, p, f, y, ctx)
        errors, status = _mm_output_errors(index, p, f, ctx, results, values, keys)
        if status != "SuccessiveApproximations" or _mm_accurate(ctx, values, errors):
            break
        if round_ >= 3 or _mm_goals(round_ + 1) == _mm_goals(round_):
            _mr_fail("OutputAccuracy", "the outputs did not reach the accuracy goal after refining the form series (cancellation or amplification)",
                     errors={name: str(e) for name, e in errors.items()})
        round_ += 1
    if not report:
        return values
    return {"Values": values, "Point": dict(point), "WorkingPrecision": working_precision, "Strategy": dict(_MM_POLICY),
            "PerFormReports": {k: _mm_key_report(k, results[k]) for k in keys}, "FinalError": errors, "FinalErrorStatus": status, "Refinements": round_}


# ==== section: forms

def _mm_vector(values):
    if backend == "NumPy":
        array = _np.array([complex(v) for v in values], dtype=_np.complex128)
        if not _np.all(_np.isfinite(array)):
            _mr_fail("NonfiniteValue", "a form value is not finite at this point")
        return array
    if not all(v == v and abs(v) != float("inf") for v in values):
        _mr_fail("NonfiniteValue", "a form value is not finite at this point")
    return list(values)


def _mm_forms(index, point, report):
    _mm_check_point(point)
    names = output_names if index is None else (output_names[index],)
    nodes = [_MM_OUTPUT_NODES[output_names.index(name)] for name in names]
    b = _mm_backend(_mm_time.monotonic() + _MM_POLICY["time_limit"])
    results = _mm_evaluate_keys(nodes, point, b, 0)
    values = {name: _mm_vector(results[node]["Value"]) for name, node in zip(names, nodes)}
    if not report:
        return values
    return {"Values": values, "Point": dict(point), "WorkingPrecision": working_precision, "Strategy": dict(_MM_POLICY),
            "PerFormReports": {name: _mm_key_report(node, results[node]) for name, node in zip(names, nodes)},
            "FinalError": {name: (None if _MM_POLICY["method"] == "FiniteSeries" else results[node].get("EstimatedError")) for name, node in zip(names, nodes)},
            "FinalErrorStatus": "NoTailBound" if _MM_POLICY["method"] == "FiniteSeries" else "SuccessiveApproximations"}
