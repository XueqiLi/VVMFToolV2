# VVMF modular runtime, version 1.
#
# A finite library of typed truncated-series operations and closed recipe interpreters for the modular forms of
# VVMFTool (Stage 7), embedded verbatim into generated Python modules (Stage 9). It is a port of the Wolfram
# implementation (Kernel/ModularSeries.wl, ModularScalars.wl, ModularConstructors.wl, ModularNormalization.wl,
# ModularOperations.wl, ModularEvaluation.wl): the same valuation-aware jets with exact rational exponents and cutoffs,
# scalar ingredients, hypergeometric series of K, rational powers with the principal leading branch, MLDE recurrences,
# modular derivatives, basis transports and the adaptive q-series evaluation with its convergence policy.
#
# Coefficients stay exact (fractions.Fraction) wherever the data are rational; algebraic or numerical constants enter
# as backend numbers (Python complex for NumPy modules, mpmath mpc in a private context for mpmath modules). Recipes
# are JSON-like data validated before use; nothing is evaluated as source. All names start with _mr (or are the
# public MR_ constants and ModularEvaluationError) so the library cannot collide with generated names.

import math as _mr_math
from fractions import Fraction as _MrF

MR_RUNTIME_VERSION = 1
_MR_INF = _mr_math.inf


class ModularEvaluationError(RuntimeError):
    """A modular-form evaluation failed: domain, order, time, precision or recipe failure (see .code)."""

    def __init__(self, code, message, **diagnostics):
        RuntimeError.__init__(self, code + ": " + message)
        self.code = code
        self.diagnostics = diagnostics


def _mr_fail(code, message, **diagnostics):
    raise ModularEvaluationError(code, message, **diagnostics)


# ---------------------------------------------------------------------------------------------------------------------
# Backends and numbers
# ---------------------------------------------------------------------------------------------------------------------

class _MrBackend:
    """Numerical environment of one evaluation: 'NumPy' (machine complex) or 'mpmath' (private context, dps digits)."""

    def __init__(self, kind, dps=None):
        if kind == "NumPy":
            import cmath
            self.kind, self.cmath, self.ctx, self.dps = kind, cmath, None, 16
        elif kind == "mpmath":
            import mpmath
            self.kind, self.ctx = kind, mpmath.mp.clone()
            self.ctx.dps = int(dps)
            self.dps = int(dps)
        else:
            raise ValueError("unknown backend " + repr(kind))
        self.cache = {}
        self.deadline = None

    def roundoff(self, x):
        """A roundoff floor for a computed value: |x| times 10**-(digits - 2) (machine numbers: 1e-14 relative)."""
        return self.absval(x) * self.tenth_power(self.dps - 2)

    def tenth_power(self, goal):
        """10**(-goal) in the backend's number type (a Python float underflows to 0 beyond 308 digits)."""
        return 10.0 ** (-goal) if self.ctx is None else self.ctx.power(10, -self.ctx.mpf(goal))

    def check_time(self):
        """Raise TimeLimit when the evaluation deadline (time.monotonic seconds, set by the caller) has passed."""
        if self.deadline is not None:
            import time
            if time.monotonic() > self.deadline:
                _mr_fail("TimeLimit", "the evaluation did not finish within its time limit")

    def decimal(self, text):
        return float(text) if self.ctx is None else self.ctx.mpf(text)

    def complex(self, x):
        if self.ctx is None:
            return complex(x)
        if isinstance(x, _MrF):
            return self.ctx.mpc(self.ctx.mpf(x.numerator) / x.denominator)
        return self.ctx.mpc(x)

    def power(self, c, r):
        """Principal power c**r of a nonzero coefficient; exact for a rational base and integer exponent."""
        if isinstance(c, _MrF) and r.denominator == 1:
            return c ** int(r)
        z = self.complex(c)
        if self.ctx is None:
            return z ** float(r) if r.denominator != 1 else z ** int(r)
        return self.ctx.power(z, self.ctx.mpf(r.numerator) / r.denominator)

    def exp_i_pi(self, a):
        """exp(i pi a) for a rational a (the principal (-1)**a)."""
        if self.ctx is None:
            return self.cmath.exp(1j * self.cmath.pi * (a.numerator / a.denominator))
        return self.ctx.expjpi(self.ctx.mpf(a.numerator) / a.denominator)

    def exp2pii(self, x):
        """exp(2 pi i x) for a complex x (the cusp branch of q^r is exp(2 pi i tau r))."""
        if self.ctx is None:
            return self.cmath.exp(2j * self.cmath.pi * complex(x))
        return self.ctx.exp(2j * self.ctx.pi * self.ctx.mpc(x))

    def absval(self, x):
        return abs(complex(x)) if self.ctx is None else self.ctx.mpf(abs(x))

    def log10(self, x):
        return _mr_math.log10(float(x)) if self.ctx is None else float(self.ctx.log10(x))

    def finite(self, x):
        if self.ctx is None:
            z = complex(x)
            return _mr_math.isfinite(z.real) and _mr_math.isfinite(z.imag)
        return bool(self.ctx.isfinite(x))


# ---------------------------------------------------------------------------------------------------------------------
# Exact scales: r * prod p**e_p * z  (r rational, e_p in [0, 1) for primes p and in [0, 2) for the sign base -1, z an
# irrational backend number or 1). Products and rational powers of radicals of rationals stay exact; only z mixes.
# ---------------------------------------------------------------------------------------------------------------------

def _mr_factor(n):
    """Prime factorization of a positive integer (trial division)."""
    factors, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


class _MrScale:
    """An exact scale r * prod_p p**e_p * (-1)**a * z: r rational, 0 <= e_p < 1 for primes p, (-1)**a = exp(i pi a) with
    0 <= a < 1, z an irrational backend number or 1. Products and principal rational powers stay exact unless z != 1."""
    __slots__ = ("r", "d", "z", "b")

    def __init__(self, r, d=None, z=1, b=None):
        self.r, self.d, self.z, self.b = _MrF(r), {}, z, b
        for base, e in (d or {}).items():
            self.absorb(base, e)

    def absorb(self, base, e):
        e = self.d.pop(base, _MrF(0)) + e
        if base == -1:
            e = e - 2 * (e.numerator // (2 * e.denominator))
            if e >= 1:
                self.r, e = -self.r, e - 1
        else:
            whole = e.numerator // e.denominator
            self.r *= _MrF(base) ** whole
            e = e - whole
        if e:
            self.d[base] = e

    def key(self):
        return (tuple(sorted(self.d.items())), self.z)

    def exact(self):
        return not self.d and self.z == 1

    def times(self, other):
        result = _MrScale(self.r * other.r, dict(self.d), (self.z * other.z) if (self.z != 1 or other.z != 1) else 1, self.b or other.b)
        for base, e in other.d.items():
            result.absorb(base, e)
        return result

    def power(self, s):
        """The principal power of the value: |v|**s exp(i s Arg v), exact when z == 1."""
        if self.z != 1 or self.r == 0:
            v = self.value()
            return _MrScale(1, None, self.b.power(v, s), self.b)
        angle = self.d.get(-1, _MrF(0)) + (1 if self.r < 0 else 0)
        angle = angle - 2 * (angle.numerator // (2 * angle.denominator))
        principal = angle if angle <= 1 else angle - 2
        result = _mr_rational_scale_power(abs(self.r), s, self.b)
        for base, e in self.d.items():
            if base != -1:
                result.absorb(base, e * s)
        result.absorb(-1, principal * s)
        return result

    def value(self):
        v = self.r
        if not self.d and self.z == 1:
            return v
        v = self.b.complex(v)
        for base, e in self.d.items():
            v = v * (self.b.exp_i_pi(e) if base == -1 else self.b.power(_MrF(base), e))
        return v * self.z if self.z != 1 else v


def _mr_scale_of(c, b):
    """A coefficient as a scale (exact rational, scale, or numeric)."""
    if isinstance(c, _MrScale):
        return c
    if _mr_exact(c):
        return _MrScale(c, None, 1, b)
    return _MrScale(1, None, c, b)


def _mr_rational_scale_power(q, r, b):
    """The principal power q**r of a nonzero rational as an exact scale."""
    result = _MrScale(1, None, 1, b)
    if q < 0:
        result.absorb(-1, r)
        q = -q
    for p, k in _mr_factor(q.numerator).items():
        result.absorb(p, k * r)
    for p, k in _mr_factor(q.denominator).items():
        result.absorb(p, -k * r)
    return result


def _mr_value(x):
    """A plain coefficient (an exact scale's value) for arithmetic outside the jet scales."""
    return x.value() if isinstance(x, _MrScale) else x


def _mr_rational(record):
    """An exact rational from ["q", "p", "q"] (or an integer string)."""
    if isinstance(record, str):
        return _MrF(int(record))
    if isinstance(record, list) and len(record) == 3 and record[0] == "q":
        return _MrF(int(record[1]), int(record[2]))
    _mr_fail("InvalidRecipe", "expected an exact rational record", record=repr(record)[:80])


def _mr_number(record, b):
    """A coefficient from its record: ["q", p, q] exact rational, ["d", text] real decimal, ["c", re, im] complex."""
    if not isinstance(record, list) or not record:
        _mr_fail("InvalidRecipe", "malformed number record", record=repr(record)[:80])
    tag = record[0]
    if tag == "q":
        return _mr_rational(record)
    if tag == "d" and len(record) == 2 and isinstance(record[1], str):
        return b.complex(b.decimal(record[1]))
    if tag == "a" and len(record) == 3:
        scale = _MrScale(_mr_rational(record[1]), None, 1, b)
        for base, e in record[2]:
            scale = scale.times(_mr_rational_scale_power(_MrF(int(base)), _mr_rational(e), b))
        return scale
    if tag == "c" and len(record) == 3:
        re, im = _mr_number(record[1], b), _mr_number(record[2], b)
        if isinstance(re, _MrF) and isinstance(im, _MrF) and im == 0:
            return re
        return b.complex(re) + 1j * b.complex(im) if b.ctx is None else b.complex(re) + b.ctx.mpc(0, 1) * b.complex(im)
    _mr_fail("InvalidRecipe", "unknown number record", record=repr(record)[:80])


# ---------------------------------------------------------------------------------------------------------------------
# Jets: exponent -> coefficient below a cutoff (None: an exact finite sum)
# ---------------------------------------------------------------------------------------------------------------------

def _mr_lt(a, b):
    """a < b with None meaning +infinity."""
    if b is None:
        return a is not None
    if a is None:
        return False
    return a < b


def _mr_min(*values):
    finite = [v for v in values if v is not None]
    return min(finite) if finite else None


def _mr_zero(c):
    return c == 0


def _mr_exact(c):
    return isinstance(c, (int, _MrF))


# A jet is (terms, cutoff, scale): the series scale * Sum terms[e] q^e known below cutoff (None: exact finite sum). The
# terms stay exact rationals wherever the Wolfram data are rational; irrational constants (an algebraic coefficient, the
# principal power c0^r of a leading coefficient) are carried in the common scale, so products, powers and reciprocals of
# rational series never cancel numerically. Two jets of different scales are combined numerically only when added.

_MR_ONE = _MrScale(1)


def _mr_jet(terms, cutoff, scale=_MR_ONE):
    if scale.r == 0:
        return ({}, cutoff, _MR_ONE)
    if scale.exact() and scale.r != 1:
        terms, scale = {e: scale.r * c for e, c in terms.items()}, _MR_ONE
    kept = {e: c for e, c in terms.items() if (cutoff is None or e < cutoff) and not _mr_zero(c)}
    return (dict(sorted(kept.items())), cutoff, scale)


def _mr_const(c, b=None):
    if _mr_exact(c):
        return _mr_jet({_MrF(0): c}, None)
    return _mr_jet({_MrF(0): _MrF(1)}, None, _mr_scale_of(c, b))


def _mr_terms(a):
    """The coefficients scale * terms (numeric when the scale is irrational)."""
    terms, cutoff, scale = a
    if scale.exact():
        return terms
    v = scale.value()
    return {e: v * c for e, c in terms.items()}


def _mr_valuation_bound(a):
    terms, cutoff, scale = a
    return next(iter(terms)) if terms else cutoff


def _mr_leading(a):
    terms, cutoff, scale = a
    if not terms:
        return None
    e = next(iter(terms))
    return e, terms[e]


def _mr_add(a, b):
    if a[2].key() == b[2].key():
        # equal irrational parts: the rational factors go into the terms, the sum stays exact
        ra, rb = a[2].r, b[2].r
        terms = {e: ra * c for e, c in a[0].items()}
        for e, c in b[0].items():
            terms[e] = terms.get(e, 0) + rb * c
        return _mr_jet(terms, _mr_min(a[1], b[1]), _MrScale(1, dict(a[2].d), a[2].z, a[2].b or b[2].b))
    if not a[0] and a[1] is None:
        return b
    if not b[0] and b[1] is None:
        return a
    terms = dict(_mr_terms(a))
    for e, c in _mr_terms(b).items():
        terms[e] = terms.get(e, 0) + c
    return _mr_jet(terms, _mr_min(a[1], b[1]))


def _mr_add_all(jets):
    result = _mr_jet({}, None)
    for j in jets:
        result = _mr_add(result, j)
    return result


def _mr_scale(a, c, b=None):
    """c * a; b is the evaluation backend (unit-scale jets carry none, so a numeric c needs it explicitly)."""
    if not isinstance(c, _MrScale) and _mr_zero(c):
        return _mr_jet({}, None)
    if _mr_exact(c):
        return _mr_jet({e: c * v for e, v in a[0].items()}, a[1], a[2])
    backend = b or a[2].b
    if backend is None:
        _mr_fail("BackendRequired", "scaling by a numeric constant needs the evaluation backend")
    return _mr_jet(a[0], a[1], a[2].times(_mr_scale_of(c, backend)))


def _mr_truncate(a, n):
    return _mr_jet(a[0], _mr_min(a[1], n), a[2])


def _mr_plus(x, y):
    """x + y with None as +infinity (cutoff arithmetic)."""
    return None if x is None or y is None else x + y


def _mr_max_hint(bound, hint):
    if bound is None:
        return None
    return bound if hint is None or hint == -_MR_INF else max(bound, hint)


def _mr_multiply(a, b, limit=None, hints=(-_MR_INF, -_MR_INF)):
    """Product known below min(c_a + v_b, c_b + v_a, limit); v the larger of the jet bound and the provable hint."""
    va, vb = _mr_max_hint(_mr_valuation_bound(a), hints[0]), _mr_max_hint(_mr_valuation_bound(b), hints[1])
    cutoff = _mr_min(_mr_plus(a[1], vb), _mr_plus(b[1], va), limit)
    terms = {}
    for e1, c1 in a[0].items():
        for e2, c2 in b[0].items():
            e = e1 + e2
            if cutoff is None or e < cutoff:
                terms[e] = terms.get(e, 0) + c1 * c2
    return _mr_jet(terms, cutoff, a[2].times(b[2]))


def _mr_closure(steps, bound):
    """Sorted exponents generated by sums of positive steps below bound, starting with 0."""
    if not steps or bound is None:
        return [_MrF(0)]
    found, frontier = {_MrF(0)}, [_MrF(0)]
    while frontier:
        new = []
        for x in frontier:
            for s in steps:
                y = x + s
                if y < bound and y not in found:
                    found.add(y)
                    new.append(y)
        frontier = new
    return sorted(found)


def _mr_reciprocal(a, limit=None):
    if not a[0]:
        _mr_fail("DivisionByZero", "a reciprocal needs a known nonzero leading term")
    terms = a[0]
    v = next(iter(terms))
    t0 = terms[v]
    w = {e - v: c / t0 for e, c in terms.items() if e != v}
    relative = _mr_min(_mr_plus(a[1], -v) if a[1] is not None else None, _mr_plus(limit, v) if limit is not None else None)
    if relative is None and w:
        _mr_fail("InfiniteSeries", "the reciprocal of an exact finite sum needs a cutoff")
    result = {_MrF(0): _MrF(1)}
    for e in _mr_closure(list(w), relative)[1:]:
        result[e] = -sum(wf * result.get(e - f, 0) for f, wf in w.items() if f <= e)
    return _mr_jet({e - v: c / t0 for e, c in result.items()}, relative - v if relative is not None else None, a[2].power(_MrF(-1)))


def _mr_rational_power(a, r, limit, b):
    """a**r with the principal power of the leading coefficient and the cusp branch q**(r v) (Miller's recurrence)."""
    if not a[0]:
        _mr_fail("DivisionByZero", "a rational power needs a known nonzero leading term")
    terms = a[0]
    v = next(iter(terms))
    t0 = terms[v]
    w = {e - v: c / t0 for e, c in terms.items() if e != v}
    relative = _mr_min(_mr_plus(a[1], -v) if a[1] is not None else None, (limit - r * v) if limit is not None else None)
    if relative is None and w:
        if r.denominator == 1 and r >= 0:
            relative = r * max(w) + 1
        else:
            _mr_fail("InfiniteSeries", "this power of an exact finite sum is an infinite series")
    result = {_MrF(0): _MrF(1)}
    for e in _mr_closure(list(w), relative)[1:]:
        result[e] = sum(((r + 1) * f - e) * wf * result.get(e - f, 0) for f, wf in w.items() if f <= e) / e
    # (scale t0)^r: the principal power of the whole leading coefficient, carried in the scale (exact for radicals).
    leading = a[2].times(_mr_scale_of(t0, b)).power(r)
    exact_total = a[1] is None and r.denominator == 1 and r >= 0 and limit is None
    cutoff = None if exact_total else relative + r * v
    return _mr_jet({e + r * v: c for e, c in result.items()}, cutoff, leading)


def _mr_theta(a):
    return _mr_jet({e: e * c for e, c in a[0].items()}, a[1], a[2])


def _mr_transport(matrix, jets, b):
    return [_mr_add_all([_mr_scale(j, m, b) for m, j in zip(row, jets) if not (isinstance(m, _MrScale) and m.r == 0) and not (not isinstance(m, _MrScale) and _mr_zero(m))])
            for row in matrix]


# ---------------------------------------------------------------------------------------------------------------------
# Scalar ingredients (cached per evaluation)
# ---------------------------------------------------------------------------------------------------------------------

def _mr_sigma(power, n):
    total, d = 0, 1
    while d * d <= n:
        if n % d == 0:
            total += d ** power
            if d * d != n:
                total += (n // d) ** power
        d += 1
    return total


def _mr_ceiling(x):
    return -((-x.numerator) // x.denominator)


def _mr_eisenstein(power, factor, cutoff):
    terms = {_MrF(0): _MrF(1)}
    for n in range(1, _mr_ceiling(cutoff)):
        terms[_MrF(n)] = _MrF(factor * _mr_sigma(power, n))
    return _mr_jet(terms, cutoff)


def _mr_eta(cutoff):
    terms, k, top = {}, 0, max(cutoff, 1)
    bound = int(_mr_math.isqrt(int(2 * top)) + 2)
    for k in range(0, bound + 1):
        for e in (_MrF(1, 24) + _MrF(k * (3 * k - 1), 2), _MrF(1, 24) + _MrF(k * (3 * k + 1), 2)):
            if e < cutoff:
                terms[e] = _MrF((-1) ** k)
    return _mr_jet(terms, cutoff)


def _mr_scalar(name, requested, b):
    cached = b.cache.get(name)
    if cached is not None and (cached[1] is None or not _mr_lt(cached[1], requested)):
        return _mr_truncate(cached, requested)
    cutoff = max(requested, _MrF(2))
    if name == "E2":
        jet = _mr_eisenstein(1, -24, cutoff)
    elif name == "E4":
        jet = _mr_eisenstein(3, 240, cutoff)
    elif name == "E6":
        jet = _mr_eisenstein(5, -504, cutoff)
    elif name == "Eta":
        jet = _mr_eta(cutoff)
    elif name == "Delta":
        e4, e6 = _mr_scalar("E4", cutoff, b), _mr_scalar("E6", cutoff, b)
        cube = _mr_multiply(_mr_multiply(e4, e4, cutoff), e4, cutoff)
        jet = _mr_scale(_mr_add(cube, _mr_scale(_mr_multiply(e6, e6, cutoff), -1)), _MrF(1, 1728))
    elif name == "j":
        jet = _mr_multiply(_mr_rational_power(_mr_scalar("E4", cutoff + 1, b), _MrF(3), None, b),
                           _mr_reciprocal(_mr_scalar("Delta", cutoff + 2, b)), cutoff)
    elif name == "K":
        jet = _mr_scale(_mr_multiply(_mr_scalar("Delta", cutoff, b),
                                     _mr_reciprocal(_mr_rational_power(_mr_scalar("E4", cutoff - 1, b), _MrF(3), None, b)), cutoff), 1728)
    else:
        _mr_fail("UnsupportedScalar", "unknown scalar ingredient", name=name)
    jet = _mr_truncate(jet, cutoff)
    if jet[1] != cutoff:
        _mr_fail("InvalidSeries", "an ingredient series did not reach the requested order", name=name)
    if cached is None or _mr_lt(cached[1], jet[1]):
        b.cache[name] = jet
    return _mr_truncate(jet, requested)


def _mr_hypergeometric(a_params, b_params, cutoff, b):
    stop = max([x for x in a_params if x.denominator == 1 and x <= 0], default=None)
    for y in b_params:
        if y.denominator == 1 and y <= 0 and not (stop is not None and stop >= y):
            _mr_fail("SingularHypergeometric", "the hypergeometric series is singular")
    k = _mr_scalar("K", cutoff, b)
    total, power, coefficient, m = _mr_jet({_MrF(0): _MrF(1)}, cutoff), _mr_jet({_MrF(0): _MrF(1)}, None), _MrF(1), 0
    while m + 1 < cutoff and not (stop is not None and m + 1 > -stop):
        b.check_time()
        num, den = _MrF(1), _MrF(1)
        for x in a_params:
            num *= x + m
        for y in b_params:
            den *= y + m
        coefficient = coefficient * num / (den * (m + 1))
        m += 1
        power = _mr_multiply(power, k, cutoff)
        total = _mr_add(total, _mr_scale(power, coefficient))
    return _mr_truncate(total, cutoff)


# ---------------------------------------------------------------------------------------------------------------------
# Expression trees of scalar recipes
#   const {value}; q; qpow {exponent}; scalar {name}; hyp {a, b}; plus/times {args}; power {base, exponent}
# ---------------------------------------------------------------------------------------------------------------------

_MR_BOUNDS = {"Eta": _MrF(1, 24), "Delta": _MrF(1), "K": _MrF(1), "j": _MrF(-1)}


def _mr_requirement(node, b):
    """A lower bound for the valuation used to size requests (seriesOrderRequirements)."""
    kind = node["node"]
    if kind == "const":
        value = _mr_number(node["value"], b)
        return _MR_INF if (not isinstance(value, _MrScale) and _mr_zero(value)) or (isinstance(value, _MrScale) and value.r == 0) else _MrF(0)
    if kind == "q":
        return _MrF(1)
    if kind == "qpow":
        return _mr_rational(node["exponent"])
    if kind == "scalar":
        return _MR_BOUNDS.get(node["name"], _MrF(0))
    if kind == "hyp":
        return _MrF(0)
    if kind == "plus":
        return min(_mr_requirement(x, b) for x in node["args"])
    if kind == "times":
        values = [_mr_requirement(x, b) for x in node["args"]]
        return _MR_INF if _MR_INF in values else sum(values, _MrF(0))
    if kind == "power":
        base, r = _mr_requirement(node["base"], b), _mr_rational(node["exponent"])
        if base == _MR_INF:
            return _MR_INF if r > 0 else (-_MR_INF if r < 0 else _MrF(0))
        return r * base
    _mr_fail("InvalidRecipe", "unknown tree node", node=kind)


def _mr_has_sum(node):
    if node["node"] == "plus":
        return True
    for key in ("args",):
        if key in node and any(_mr_has_sum(x) for x in node[key]):
            return True
    return node["node"] == "power" and _mr_has_sum(node["base"])


def _mr_provable(node, b):
    """A provable lower bound of the valuation (provableValuationBound): -inf when nothing is provable."""
    kind = node["node"]
    if kind == "power":
        r = _mr_rational(node["exponent"])
        if r < 0:
            return r * _mr_requirement(node["base"], b) if not _mr_has_sum(node["base"]) else -_MR_INF
        if r == 0:
            return _MrF(0)
        inner = _mr_provable(node["base"], b)
        return -_MR_INF if inner == -_MR_INF else r * inner
    if kind == "plus":
        return min(_mr_provable(x, b) for x in node["args"])
    if kind == "times":
        values = [_mr_provable(x, b) for x in node["args"]]
        if _MR_INF in values:
            return _MR_INF
        if -_MR_INF in values:
            return -_MR_INF
        return sum(values, _MrF(0))
    return _mr_requirement(node, b)


def _mr_tree(node, cutoff, b):
    """The series of a tree below cutoff (treeSeries)."""
    kind = node["node"]
    if kind == "const":
        return _mr_const(_mr_number(node["value"], b), b)
    if kind == "q":
        return _mr_jet({_MrF(1): _MrF(1)}, None)
    if kind == "qpow":
        return _mr_jet({_mr_rational(node["exponent"]): _MrF(1)}, None)
    if kind == "scalar":
        return _mr_scalar(node["name"], cutoff, b)
    if kind == "hyp":
        return _mr_hypergeometric([_mr_rational(x) for x in node["a"]], [_mr_rational(x) for x in node["b"]], cutoff, b)
    if kind == "plus":
        return _mr_truncate(_mr_add_all([_mr_tree(x, cutoff, b) for x in node["args"]]), cutoff)
    if kind == "times":
        return _mr_times(node["args"], cutoff, b)
    if kind == "power":
        return _mr_power(node, cutoff, b)
    _mr_fail("InvalidRecipe", "unknown tree node", node=kind)


def _mr_times(parts, cutoff, b):
    bounds = [_mr_requirement(x, b) for x in parts]
    if _MR_INF in bounds:
        return _mr_jet({}, None)
    total = sum(bounds, _MrF(0))
    proved = [_mr_provable(x, b) for x in parts]

    def product(target):
        acc = _mr_const(_MrF(1))
        for k, part in enumerate(parts):
            factor = _mr_tree(part, target - (total - bounds[k]), b)
            before = proved[:k]
            hint = -_MR_INF if -_MR_INF in before else sum(before, _MrF(0))
            acc = _mr_multiply(acc, factor, target - sum(bounds[k + 1:], _MrF(0)), (hint, proved[k]))
        return acc

    target, result, tries = cutoff, product(cutoff), 0
    while tries < 3 and result[1] is not None and result[1] < cutoff:
        tries += 1
        target = target + (cutoff - result[1])
        result = product(target)
    return _mr_truncate(result, cutoff)


def _mr_power(node, cutoff, b):
    base_node, r = node["base"], _mr_rational(node["exponent"])
    v = _mr_requirement(base_node, b)
    if r.denominator == 1 and r >= 0:
        w = _MrF(0) if v == _MR_INF else v
        p = _mr_provable(base_node, b)
        base = _mr_tree(base_node, cutoff - r * w + w, b)
        acc = _mr_const(_MrF(1))
        for k in range(1, int(r) + 1):
            hints = ((k - 1) * p, p) if p not in (_MR_INF, -_MR_INF) else (-_MR_INF, -_MR_INF)
            acc = _mr_multiply(acc, base, cutoff - (r - k) * w, hints)
        return acc
    if v == _MR_INF:
        _mr_fail("DivisionByZero", "a negative or fractional power of an exact zero")

    def required(x):
        return max(cutoff - r * x + x, x + 1)

    base = _mr_tree(base_node, required(v), b)
    tries = 0
    while tries < 6 and base[1] is not None and (_mr_leading(base) is None or base[1] < required(_mr_valuation_bound(base))):
        tries += 1
        base = _mr_tree(base_node, max(required(_mr_valuation_bound(base)), 2 * max(base[1], _MrF(0)) + 1), b)
    if _mr_leading(base) is None:
        _mr_fail("InsufficientOrder", "the base of a power cancels beyond the orders expanded")
    return _mr_rational_power(base, r, cutoff, b)


# ---------------------------------------------------------------------------------------------------------------------
# Modular derivative and the MLDE source systems
# ---------------------------------------------------------------------------------------------------------------------

def _mr_derivative(jet, k, cutoff, b):
    """D_k = q d/dq - k E2/12 (modularDerivativeJet); the derivative of an empty series is empty below the same cutoff."""
    if not jet[0]:
        return _mr_jet({}, _mr_min(cutoff, jet[1]))
    e2 = _mr_scalar("E2", _mr_min(cutoff, jet[1]) - _mr_valuation_bound(jet), b)
    return _mr_add(_mr_theta(jet), _mr_scale(_mr_multiply(e2, jet, cutoff), _MrF(-k, 12) if isinstance(k, int) else -k / 12))


def _mr_iterated(jet, k, n, cutoff, b):
    for i in range(n):
        jet = _mr_derivative(jet, k + 2 * i, cutoff, b)
    return jet


def _mr_residuals(kind, f, g, c, k, cut, b):
    e4, e6 = _mr_scalar("E4", cut, b), _mr_scalar("E6", cut, b)
    if kind == "Cyclic4D":
        return [_mr_add_all([_mr_scale(_mr_iterated(f, k, 4, cut, b), -1), _mr_scale(_mr_multiply(_mr_multiply(e4, e4, cut), f, cut), c["a1"], b),
                             _mr_scale(_mr_multiply(e6, _mr_derivative(f, k, cut, b), cut), c["a2"], b),
                             _mr_scale(_mr_multiply(e4, _mr_iterated(f, k, 2, cut, b), cut), c["a3"], b)])]
    if kind == "NonCyclic4D":
        return [_mr_add_all([_mr_scale(_mr_iterated(f, k, 3, cut, b), -1), _mr_scale(_mr_multiply(e6, f, cut), c["a1"], b),
                             _mr_scale(_mr_multiply(e4, _mr_derivative(f, k, cut, b), cut), c["a2"], b), _mr_scale(_mr_multiply(e4, g, cut), c["a3"], b)]),
                _mr_add(_mr_scale(_mr_derivative(g, k + 2, cut, b), -1), _mr_multiply(e4, f, cut))]
    if kind == "Coupled5D":
        return [_mr_add(_mr_scale(_mr_derivative(g, k + 2, cut, b), -1), _mr_multiply(e4, f, cut)),
                _mr_add_all([_mr_scale(_mr_iterated(f, k, 4, cut, b), -1), _mr_scale(_mr_multiply(_mr_multiply(e4, e4, cut), f, cut), c["b1"], b),
                             _mr_scale(_mr_multiply(e6, _mr_derivative(f, k, cut, b), cut), c["b2"], b), _mr_scale(_mr_multiply(e6, g, cut), c["b3"], b),
                             _mr_scale(_mr_multiply(e4, _mr_iterated(f, k, 2, cut, b), cut), c["b4"], b)])]
    _mr_fail("UnsupportedConstruction", "unknown MLDE system", kind=kind)


_MR_HAS_G = {"Cyclic4D": False, "NonCyclic4D": True, "Coupled5D": True}


class _MrMldeState:
    """The order-by-order solution of one MLDE family at one exponent r: every intermediate series as a coefficient list.

    The systems are linear in (F, G), so the coefficient at q^(r + n) of each intermediate (D F, D^2 F, E4 F, ...) is an
    affine function c + x f_n + y g_n of the new unknowns given the lower coefficients: one convolution per series and
    order, O(N^2) in all. Values are triples (c, x, y); stored coefficients are concrete (x = y = 0).
    """

    def __init__(self, kind, k, c, r, g0, b):
        self.kind, self.k, self.c, self.r, self.b = kind, k, c, r, b
        self.has_g = _MR_HAS_G[kind]
        self.series = {}
        self.n = -1
        self.extend(0, g0)

    def coefficient(self, name, n):
        """Coefficient n of a scalar series from a cached list (extended by doubling, so the access is O(1) amortized)."""
        cache = self.series.get("_c" + name)
        if cache is None or len(cache) <= n:
            length = max(2 * (n + 1), 8)
            terms = _mr_scalar(name, _MrF(length), self.b)[0]
            cache = [terms.get(_MrF(i), 0) for i in range(length)]
            self.series["_c" + name] = cache
        return cache[n]

    def square(self, i):
        """Coefficient i of E4^2 (cached list, extended by one convolution per new index)."""
        cache = self.series.setdefault("_E4^2", [])
        while len(cache) <= i:
            m = len(cache)
            cache.append(sum(self.coefficient("E4", t) * self.coefficient("E4", m - t) for t in range(m + 1)))
        return cache[i]

    def known(self, key, i):
        return self.series[key][i]

    def derivative(self, source, w, n, top):
        """Top coefficient of D_w X at index n (X = source, its index-n value top): (r + n - w/12) X_n - w/12 sum E2_i X_(n-i)."""
        lead = self.r + n - w / 12
        rest = sum(self.coefficient("E2", i) * self.known(source, n - i)[0] for i in range(1, n + 1))
        return (lead * top[0] - w / 12 * rest, lead * top[1], lead * top[2])

    def product(self, name, source, n, top):
        """Top coefficient of S . X at index n for a known scalar series S (E4, E6 or E4^2)."""
        def s(i):
            return self.square(i) if name == "E4^2" else self.coefficient(name, i)
        rest = sum(s(i) * self.known(source, n - i)[0] for i in range(1, n + 1))
        s0 = s(0)
        return (s0 * top[0] + rest, s0 * top[1], s0 * top[2])

    def tops(self, n, f_top, g_top):
        """All intermediate tops at index n and the residual tops, given the affine tops of F and G."""
        k, c, t = self.k, self.c, {"F": f_top, "G": g_top}
        depth = 4 if self.kind in ("Cyclic4D", "Coupled5D") else 3
        previous = "F"
        for j in range(1, depth + 1):
            t["D" + str(j)] = self.derivative(previous, k + 2 * (j - 1), n, t[previous])
            previous = "D" + str(j)
        if self.has_g:
            t["DG"] = self.derivative("G", k + 2, n, t["G"])

        def p(name, source):
            key = name + "*" + source
            t[key] = self.product(name, source, n, t[source])
            return t[key]

        def combine(parts):
            return tuple(sum(coef * part[i] for coef, part in parts) for i in range(3))

        if self.kind == "Cyclic4D":
            residuals = [combine([(-1, t["D4"]), (c["a1"], p("E4^2", "F")), (c["a2"], p("E6", "D1")), (c["a3"], p("E4", "D2"))])]
        elif self.kind == "NonCyclic4D":
            residuals = [combine([(-1, t["D3"]), (c["a1"], p("E6", "F")), (c["a2"], p("E4", "D1")), (c["a3"], p("E4", "G"))]),
                         combine([(-1, t["DG"]), (1, p("E4", "F"))])]
        else:
            residuals = [combine([(-1, t["DG"]), (1, p("E4", "F"))]),
                         combine([(-1, t["D4"]), (c["b1"], p("E4^2", "F")), (c["b2"], p("E6", "D1")), (c["b3"], p("E6", "G")), (c["b4"], p("E4", "D2"))])]
        return t, residuals

    def extend(self, order, g0=None):
        """Solve the coefficients up to index order (index 0 is the leading term with its indicial data)."""
        while self.n < order:
            self.b.check_time()
            n = self.n + 1
            if n == 0:
                f_top, g_top = (_MrF(1), 0, 0), ((g0, 0, 0) if self.has_g else (0, 0, 0))
            else:
                f_top, g_top = (0, 1, 0), ((0, 0, 1) if self.has_g else (0, 0, 0))
            t, residuals = self.tops(n, f_top, g_top)
            if n == 0:
                if not all(_mr_zero(r[0]) for r in residuals):
                    _mr_fail("IndicialInconsistency", "the leading data do not satisfy the indicial equations", exponent=str(self.r))
                x = y = 0
            elif self.has_g:
                (b1, a11, a12), (b2, a21, a22) = residuals
                det = a11 * a22 - a12 * a21
                if _mr_zero(det):
                    # Consistent (a resonance) exactly when the coefficient matrix and the augmented matrix have equal rank.
                    rank = 0 if all(_mr_zero(v) for v in (a11, a12, a21, a22)) else 1
                    augmented = 2 if not all(_mr_zero(m) for m in (b1 * a22 - b2 * a12, b2 * a11 - b1 * a21, det)) else (
                        0 if all(_mr_zero(v) for v in (a11, a12, a21, a22, b1, b2)) else 1)
                    consistent = rank == augmented
                    _mr_fail("Resonance" if consistent else "IndicialInconsistency",
                             "the MLDE does not determine the series coefficients at this order", exponent=str(self.r), order=n, kind=self.kind)
                x, y = (-b1 * a22 + b2 * a12) / det, (-b2 * a11 + b1 * a21) / det
            else:
                b1, a11, _ = residuals[0]
                if _mr_zero(a11):
                    _mr_fail("Resonance" if _mr_zero(b1) else "IndicialInconsistency",
                             "the MLDE does not determine the series coefficients at this order", exponent=str(self.r), order=n, kind=self.kind)
                x, y = -b1 / a11, 0
            for key, value in t.items():
                if key.startswith("_"):
                    continue
                self.series.setdefault(key, []).append((value[0] + value[1] * x + value[2] * y, 0, 0))
            self.n = n

    def jet(self, part, order):
        coefficients = self.series[part]
        return _mr_jet({self.r + i: coefficients[i][0] for i in range(order + 1)}, self.r + order + 1)


def _mr_mlde_solution(recipe, order, b):
    """F (and G) component jets of an MLDE family through order steps after the leading term (extendMLDESeries).

    One state per exponent, kept in the evaluation cache and extended incrementally; a singular order system is a
    resonance when consistent and an inconsistency otherwise, as in the Wolfram solver.
    """
    kind, k = recipe["system"], _mr_rational(recipe["weight"])
    if kind not in _MR_HAS_G:
        _mr_fail("UnsupportedConstruction", "unknown MLDE system", kind=kind)
    has_g = _MR_HAS_G[kind]
    key = ("mlde", recipe["family_key"])
    states = b.cache.get(key)
    if states is None:
        c = {name: _mr_value(_mr_number(value, b)) for name, value in recipe["coefficients"].items()}
        exponents = [_mr_rational(e) for e in recipe["exponents"]]
        g_leading = [_mr_value(_mr_number(x, b)) for x in recipe["g_leading"]] if has_g else [None] * len(exponents)
        states = [_MrMldeState(kind, k, c, r, g0, b) for r, g0 in zip(exponents, g_leading)]
        b.cache[key] = states
    for state in states:
        state.extend(order)
    return {"F": [s.jet("F", order) for s in states], "G": [s.jet("G", order) for s in states] if has_g else None, "order": order}


# ---------------------------------------------------------------------------------------------------------------------
# Definitions: analytic, jet, mlde, derived; an optional final transform
# ---------------------------------------------------------------------------------------------------------------------

def _mr_component_jets(definition, cutoff, b):
    """The stored-basis component series of a definition below cutoff (formComponentJets)."""
    base = _mr_base_jets(definition, cutoff, b)
    if "transform" in definition:
        matrix = [[_mr_number(x, b) for x in row] for row in definition["transform"]]
        base = [_mr_truncate(j, cutoff) for j in _mr_transport(matrix, base, b)]
    return base


def _mr_base_jets(definition, cutoff, b):
    kind = definition["kind"]
    if kind == "analytic":
        jets = [_mr_tree(t, cutoff, b) for t in definition["components"]]
        if any(j[1] is not None and j[1] < cutoff for j in jets):
            _mr_fail("InsufficientOrder", "a component series could not be determined to the requested order")
        return [_mr_truncate(j, cutoff) for j in jets]
    if kind == "jet":
        jets = [_mr_jet({_mr_rational(e): _mr_value(_mr_number(c, b)) for e, c in comp["terms"]}, None if comp["cutoff"] is None else _mr_rational(comp["cutoff"]))
                for comp in definition["components"]]
        if any(j[1] is not None and j[1] < cutoff for j in jets):
            _mr_fail("InsufficientOrder", "a finite jet does not define coefficients beyond its cutoff")
        return [_mr_truncate(j, cutoff) for j in jets]
    if kind == "mlde":
        recipe = definition["recipe"]
        exponents = [_mr_rational(e) for e in recipe["exponents"]]
        needed = _mr_ceiling(cutoff - min(exponents)) + 1
        solution = _mr_mlde_solution(recipe, max(needed, 1), b)
        seeds = solution["G"] if recipe["seed"] == "G" else solution["F"]
        scales = [_mr_number(x, b) for x in definition["scales"]]
        frame = [_mr_scale(j, s, b) for j, s in zip(seeds, scales)]
        matrix = [[_mr_number(x, b) for x in row] for row in recipe["frame_b_inverse"]]
        return [_mr_truncate(j, cutoff) for j in _mr_transport(matrix, frame, b)]
    if kind == "derived":
        source = _mr_component_jets(definition["source"], cutoff, b)
        k = _mr_rational(definition["source_weight"])
        return [_mr_truncate(_mr_derivative(j, k, cutoff, b), cutoff) for j in source]
    _mr_fail("InvalidRecipe", "unknown definition kind", kind=kind)


# ---------------------------------------------------------------------------------------------------------------------
# Points and adaptive evaluation
# ---------------------------------------------------------------------------------------------------------------------

def _mr_point(record, b):
    """A tagged point: {"kind": "tau", "tau": [re, im]} or {"kind": "q", "q": [re, im], "sheet": n}; returns tau or 'cusp'."""
    if record.get("kind") == "tau":
        tau = b.complex(_mr_number(record["tau"][0], b)) + (1j if b.ctx is None else b.ctx.mpc(0, 1)) * b.complex(_mr_number(record["tau"][1], b))
        if not (tau.imag > 0):
            _mr_fail("OutsideDomain", "a tau point needs Im(tau) > 0")
        return tau
    if record.get("kind") == "q":
        q = b.complex(_mr_number(record["q"][0], b)) + (1j if b.ctx is None else b.ctx.mpc(0, 1)) * b.complex(_mr_number(record["q"][1], b))
        sheet = int(record["sheet"])
        if q == 0:
            return "cusp"
        if not (abs(q) < 1):
            _mr_fail("OutsideDomain", "a q point needs 0 < |q| < 1")
        if b.ctx is None:
            import cmath
            return (cmath.log(q) + 2j * cmath.pi * sheet) / (2j * cmath.pi)
        ctx = b.ctx
        return (ctx.log(q) + 2j * ctx.pi * sheet) / (2j * ctx.pi)
    _mr_fail("InvalidPoint", "points are tagged tau or q records")


def _mr_evaluate_jets(jets, tau, b):
    return [b.complex(j[2].value()) * sum((b.complex(c) * b.exp2pii(tau * (e.numerator / e.denominator if b.ctx is None else b.ctx.mpf(e.numerator) / e.denominator))
                                   for e, c in j[0].items()), b.complex(0)) for j in jets]


def _mr_roundoffs(jets, tau, b, values):
    """Roundoff floors of evaluated series: 10**-(digits - 2) times the larger of |value| and the summed term size
    |scale| Sum |c_e q^e| (cancellation inside a sum leaves the error of its terms; review round 3, S2)."""
    floors = []
    for j, v in zip(jets, values):
        size = b.absval(j[2].value()) * sum((b.absval(c) * b.absval(b.exp2pii(tau * (e.numerator / e.denominator if b.ctx is None else b.ctx.mpf(e.numerator) / e.denominator)))
                                              for e, c in j[0].items()), b.absval(0))
        floors.append(max(b.absval(v), size) * b.tenth_power(b.dps - 2))
    return floors


def _mr_roundoff_parts(jets, tau, b, values, floors):
    """(real floor, imaginary floor) per component: the total floor on each axis, except that an axis cannot be left when
    every term and the value lie exactly on the other one (a real-coefficient form on the imaginary axis is exactly real;
    moving it off the axis would invent a branch cut crossing; review round 5, U1)."""
    parts = []
    for j, v, total in zip(jets, values, floors):
        s = b.complex(j[2].value())
        all_real, all_imaginary = True, True
        for e, c in j[0].items():
            t = s * b.complex(c) * b.exp2pii(tau * (e.numerator / e.denominator if b.ctx is None else b.ctx.mpf(e.numerator) / e.denominator))
            all_real = all_real and t.imag == 0
            all_imaginary = all_imaginary and t.real == 0
        v = b.complex(v)
        all_real = all_real and v.imag == 0
        all_imaginary = all_imaginary and v.real == 0
        parts.append((b.absval(0) if all_imaginary else total, b.absval(0) if all_real else total))
    return parts


def _mr_adaptive(get_jets, tau, goal, precision_goal, explicit, maximum, b, start=None):
    """Successive approximations until two orders agree (adaptiveSeriesValue); never a rigorous tail bound.

    The result carries the previous approximation ("Previous"), so a caller can estimate how the difference of two
    successive approximations propagates through further arithmetic; the backend deadline bounds the whole loop.
    """
    qabs = b.absval(b.exp2pii(tau))
    lq = max(-b.log10(qabs), 1e-3)
    step = max(2, _mr_math.ceil(5 / lq))
    n = explicit if explicit is not None else (min(maximum, start) if start is not None else min(maximum, max(2, _mr_math.ceil((goal + 5) / lq))))
    try:
        jets = get_jets(n)
    except ModularEvaluationError as error:
        if error.code == "InsufficientOrder" and explicit is None:
            _mr_fail("FiniteJet", "a finite jet cannot support adaptive accuracy; give an explicit series order")
        raise
    current = _mr_evaluate_jets(jets, tau, b)
    b.check_time()
    if explicit is not None:
        try:
            longer = _mr_evaluate_jets(get_jets(n + step), tau, b)
            estimate = max(b.absval(x - y) for x, y in zip(longer, current)) if current else b.absval(0)
        except ModularEvaluationError:
            estimate = None
        roundoff = _mr_roundoffs(jets, tau, b, current)
        if estimate is not None:
            estimate = max([estimate] + roundoff)
        return {"Value": current, "Order": n, "EstimatedError": estimate, "Converged": False, "Previous": None, "Roundoff": roundoff,
                "RoundoffParts": _mr_roundoff_parts(jets, tau, b, current, roundoff)}
    while True:
        b.check_time()
        previous = current
        n += step
        if n > maximum:
            _mr_fail("ConvergenceFailure", "the series did not converge to the accuracy goal within the maximal order", order=n - step)
        jets = get_jets(n)
        current = _mr_evaluate_jets(jets, tau, b)
        change = max([b.absval(x - y) for x, y in zip(current, previous)] or [b.absval(0)])
        size = max([b.absval(x) for x in current] or [b.absval(0)])
        if change <= max(b.tenth_power(goal), b.tenth_power(precision_goal) * size):
            # The estimate is never below the roundoff of the computed values (two bit-identical approximations do not
            # make an exact value; review round 2, R1).
            roundoff = _mr_roundoffs(jets, tau, b, current)
            return {"Value": current, "Order": n, "EstimatedError": max([change] + roundoff), "Converged": True, "Previous": previous, "Roundoff": roundoff,
                    "RoundoffParts": _mr_roundoff_parts(jets, tau, b, current, roundoff)}


def mr_evaluate_definition(definition, point, b, goal, precision_goal, explicit=None, maximum=2000, start=None):
    """Evaluate a definition (coefficients already substituted) at a point record: the Stage 7 q-series route.

    explicit: a fixed order (finite approximation, not converged); start: the first order of the adaptive loop.
    """
    tau = _mr_point(point, b)
    if tau == "cusp":
        jets = _mr_component_jets(definition, _MrF(1), b)
        if any(e < 0 for j in jets for e in j[0]):
            _mr_fail("Pole", "a component has a negative leading exponent: the cusp value is infinite")
        values = [b.complex(j[2].value()) * b.complex(j[0].get(_MrF(0), 0)) for j in jets]
        roundoff = [b.roundoff(v) for v in values]
        return {"Value": values, "Order": 1, "EstimatedError": max(roundoff + [b.absval(0)]), "Converged": True, "Cusp": True, "Previous": None, "Roundoff": roundoff,
                "RoundoffParts": [(r, b.absval(0) if b.complex(v).imag == 0 else r) for v, r in zip(values, roundoff)]}
    return _mr_adaptive(lambda n: _mr_component_jets(definition, _MrF(n), b), tau, goal, precision_goal, explicit, maximum, b, start)
