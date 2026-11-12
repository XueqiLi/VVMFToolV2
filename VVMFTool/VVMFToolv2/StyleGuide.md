# VVMFTool — Mathematica Style Guide

**Status: draft for discussion.** This guide covers Wolfram Language source, comments, API documentation, notebooks and tests. It applies to human and AI contributors. Its proposed conventions do not change the mathematical contracts in [the design](VVMFArch/design.md) or the reviewed stage plans.

The guide requires clear names, documentation of public and private code, organized modules, meaningful tests and current-state documentation, following Wolfram Language semantics.

Rules about indentation, private-name casing, comment fields and documentation coverage below are **project conventions**. Wolfram language behavior and documentation tools are identified with official references. This is not presented as an official Wolfram style standard.

## 1. Formatting

- Use four spaces per indentation level and no tabs. Keep source as UTF-8 text.
- Use double quotes for strings. Use `(* ... *)` for comments; there is no JavaScript-style line-comment convention in Wolfram source.
- Write `f[x, y]`, `{x, y}` and `<|"Order" -> 12, "Complete" -> True|>`. Use a space after commas, around assignment and rule operators, and around binary arithmetic where it improves readability.
- Keep short expressions on one line. For longer calls, place one logical argument or option per line, indent the contents, and align the closing delimiter with the containing expression. Aim for about 100 characters per line; do not damage a formula or URL to meet a rigid limit.
- Do not add trailing commas. They are not harmless formatting and can introduce missing arguments/`Null` or invalid input, depending on the construct.
- Separate definitions and logical blocks with blank lines. Avoid long chains of `@`, `//`, replacements and anonymous functions when named intermediate results make evaluation order clearer.
- Prefer explicit `*` where adjacent identifiers could be mistaken for one name. Use `.` only for its intended `Dot` operation. Keep executable package code in readable input syntax; reserve typeset subscripts and decorative notation for display.

Semicolons are semantic. Use them to sequence operations and suppress unwanted output. A final semicolon **inside a function body** normally makes that body return `Null`. The semicolon after a complete definition does not change the function's returned value. See [CompoundExpression](https://reference.wolfram.com/language/ref/CompoundExpression.html).

```wolfram
(* Layout example: the last body expression is the returned value. *)
sumSquares[values_List] := Module[{squares},
    squares = values^2;
    Total[squares]
];
```

Use a Wolfram-aware formatter only after its output has been checked against these conventions. Formatting must preserve evaluation semantics, including semicolons and argument separators. No formatter is assumed to be installed or configured by this draft.

## 2. Naming

### Files

| Kind | Convention | Example |
| --- | --- | --- |
| Wolfram implementation module | Descriptive PascalCase `.wl` | `Kernel/Representation.wl` |
| Package entry point | Standard loader name | `Kernel/init.m` |
| Dedicated schema/validation module, when needed | Name the owning domain | `RepresentationValidation.wl` |
| Helpers extracted from a large module | Name the shared responsibility | `ModularSeries.wl` |
| Unit test file | Match the module, `.wlt` | `Tests/Unit/Representation.wlt` |
| Integration or end-to-end test | Name the workflow, `.wlt` | `Tests/EndToEnd/GroupRestore.wlt` |
| Public reference notebook | Public symbol name, `.nb` | `ReferencePages/Symbols/BuildGroup.nb` |
| Guide/tutorial notebook | Descriptive PascalCase `.nb` | `Tutorials/ConstructingFiniteGroups.nb` |

Test and documentation paths above are proposed organization, not a claim that those files already exist. Preserve the module responsibilities and loader established by the stage plans; a style rule does not require a new directory for every small feature. Existing architecture-document filenames remain as recorded in their links.

### Identifiers

| Kind | Convention | Example |
| --- | --- | --- |
| Public function, constructor or type head | PascalCase | `BuildGroup`, `Rep`, `ModularForm` |
| Public option symbol | PascalCase | `ComputeRepresentations`, `StoreGAPState` |
| Private function or local variable | lowerCamelCase | `validateRepShape`, `generatorNames` |
| Package-level configuration/state symbol | Descriptive `$PascalCase`, in its owning context | a private `$GroupRegistry` |
| Property or stored association key | String, matching the declared schema | `group["IrrepOrder"]` |
| Finite method/format label | Documented value, usually a string | `Basis -> "Unitary"` |
| Internal callback or handler | Name its role | `onProgress`, `handleCancellation` |

Private definitions belong in a private context, normally `VVMFTool\`Private\``. Privacy is not implemented by an underscore prefix. `_` is pattern syntax: `value_Integer` names a pattern; `_value` is not a private variable name. Symbol-name syntax is described under [Symbol](https://reference.wolfram.com/language/ref/Symbol.html).

Use descriptive words instead of ad hoc abbreviations such as `tmp2`, `dat`, `res` or `grp`. Established project vocabulary—`Rep`, `CG`, `GAP`, `JSON`, `ID`, `MLDE`, and `irrep`—is acceptable when its meaning is clear. Conventional mathematical notation such as `q`, `tau`, `k`, `S`, `T`, and indices `i`, `j` is also acceptable in a short, documented mathematical scope. Longer algorithms benefit from names such as `weight`, `sMatrix` and `targetBasis`.

Do not assign to system symbols such as `I`, `E`, `N` or `D` to imitate mathematical notation. Localize ordinary implementation variables; use the specified held/inert parsing interfaces for user-supplied symbolic definitions.

Name a value's role: `source`, `target`, `basisChange`, `generatorNames`. A word such as `matrix` is useful when it distinguishes mathematical roles, as in `sMatrix`; avoid repeating a type without adding meaning.

The agreed `VVMF_` prefix applies to package-owned **GAP** functions/globals. It is not a Wolfram symbol-naming rule. GAP and generated Python retain syntax appropriate to their own languages.

## 3. Wolfram Language contracts and evaluation

### Input contracts and validation

Patterns describe matching conditions; they do not establish every semantic property of an input. A definition using `representation_Rep` checks an expression's head, not that its matrices form a valid representation.

- State the supported input forms and validate their semantic requirements at the owning boundary.
- Use patterns such as `_Integer`, `_String`, `_Association`, or a package head when that restriction expresses the contract. Use predicates and conditions for additional requirements.
- General patterns such as `expression_` are appropriate for symbolic operations. Do not artificially narrow a valid symbolic domain merely to make a signature look typed.
- Private helpers may rely on documented preconditions established by their callers. Avoid repeatedly performing expensive group validation in every low-level helper.
- Invalid public inputs must follow the documented diagnostic contract. A definition that simply remains unevaluated on malformed input does not by itself satisfy VVMFTool's required error handling.

Represent structured data with the heads and associations specified by the design. Document required fields, field domains, ordering, optional fields and absent-data meanings. Distinguish a `Rep` value, a mutable `Group` handle, an immutable snapshot and a backend result record.

For alternative input forms, use explicit heads or the schema's declared tag. This serves the purpose of a discriminated union. Do not add a universal `"type"` field to records whose schema already identifies their kind. Avoid speculative generic frameworks when a concrete mathematical interface is sufficient.

### Options and properties

Public option **names are symbols**; property **keys are strings**. Use existing system option symbols when their meaning fits, document package-owned option symbols with `::usage`, and protect them against accidental assignment. Do not redefine usage messages or defaults belonging to system functions.

```wolfram
(* Planned VVMFTool usage, after the relevant stages are implemented. *)
group = BuildGroup[
    CatalogueGroup["SmallGroup", {12, 3}],
    ComputeRepresentations -> False,
    StoreGAPState -> True
];
group["IrrepOrder"]
```

Declare defaults with `Options`, accept options with `OptionsPattern`, and retrieve values with `OptionValue`. Validate supported option names, values and combinations using the shared validation layer. `OptionsPattern` can match rules for unrecognized options; it does not provide complete option validation. Do not silently discard a user's unsupported option. See [OptionsPattern](https://reference.wolfram.com/language/ref/OptionsPattern.html).

Document configuration-derived defaults, per-call overrides, and what `Automatic` actually chooses. An option default that depends on package configuration must not be documented as an unconditional constant.

### Scoping, definitions and effects

Use `Module` for fresh local symbols, `With` for lexical substitution of fixed values, and `Block` for deliberately temporary values of existing symbols. They are not interchangeable formatting choices. Explain dynamic scoping when the caller must understand it. See [Module](https://reference.wolfram.com/language/ref/Module.html) and [Block](https://reference.wolfram.com/language/ref/Block.html).

Choose `=` versus `:=`, and `->` versus `:>`, according to when evaluation should happen. State nonstandard evaluation behavior and relevant attributes such as `HoldAllComplete` in the function documentation. Use the agreed upvalues for `Rep` methods; do not install unrelated definitions on system symbols.

Localize implementation state. Package loading must not clear the user's `Global\`` context, reset live objects, depend on the notebook's current directory, or start GAP computations. Use scoped setup/cleanup for files, workers and temporary settings. Ordinary failure and user cancellation must preserve accepted state according to the operation's contract.

### Diagnostics and suppression

Use structured `Failure` values for operational failures, with stable tags and useful diagnostic data. Document separately whether a call emits a message. Constructing a `Failure` is not the same as calling `Message`. Named `Missing` values express unavailable or unknown data where the interface permits them; `0`, `{}`, `Null` and `False` have their own meanings. See [Failure](https://reference.wolfram.com/language/ref/Failure.html).

Do not broadly silence warnings with `Off`, blanket `Quiet`, or a catch-all handler that converts every problem to a plausible mathematical answer. When a particular message must be handled, restrict suppression to that message and operation, check the resulting value, and explain the technical reason nearby. Apply the same rule to any analyzer-warning suppression: identify the architectural reason or verified tool limitation.

### Constants and TODOs

Put resource limits, configurable tolerances and protocol constants in their owning module or configuration. Declare option defaults in `Options`. Reuse schema constants where that prevents disagreement between producers and consumers.

Mathematical literals such as `0`, `1`, `2`, `Pi`, an exact rational coefficient, or a clearly documented polynomial are not automatically unexplained magic numbers. Canonical property strings are readable vocabulary and need not each become a new global symbol. Explain the meaning of a non-obvious mathematical constant instead of merely renaming it.

Use actionable comments such as `(* TODO (stage 7): Add the specified holdout-point check. *)`. TODOs identify real outstanding work, optionally with a plan/issue reference. They must not label an unimplemented required method as available or replace the stage's completion requirements.

## 4. Package loading and dependencies

Expose named symbols in the public package context. Declare public `::usage` messages before entering the private implementation context, so implementation references resolve to the intended public symbols. Wolfram's [BeginPackage examples](https://reference.wolfram.com/language/ref/BeginPackage.html), including its shipped `Collatz.m` example, demonstrate this arrangement.

The package entry point coordinates loading and the public interface. Load modules in an explicit dependency order: shared contracts/configuration first, owning implementations next, and presentation/adapters after their dependencies.

Use `Needs["VVMFTool\`"]` at the user boundary. Internal file loads must resolve against the package root with `FileNameJoin`, not a user's absolute path or `NotebookDirectory[]`. Identify dependencies through explicit contexts or package-relative paths.

Keep external integration in named adapters. Loading the Wolfram package should work without a front end and report optional GAP capabilities separately. Dependency installation is not an implicit effect of loading a package. Record supported and tested Wolfram, GAP and auxiliary package versions in project metadata/test evidence.

## 5. Comments and documentation

### Three documentation layers

| Layer | Audience and purpose | Required coverage |
| --- | --- | --- |
| `symbol::usage` | Concise kernel help, including `?symbol` | Every exported function, head and package-owned option symbol |
| Structured `(* ... *)` block | The source reader: contract, algorithm and maintenance information | Every named public/private function, method, constructor and data schema |
| Reference/guide/tutorial notebook | Users learning the API and complete workflows | Public API reference and realistic workflows as their stages are implemented |

Wolfram supports source comments, usage messages and notebook text. The structured comment fields below are our project format; they do not imply automatic documentation extraction. See [Wolfram's documentation constructs](https://reference.wolfram.com/language/tutorial/TextualInputAndOutput.html).

### Short usage messages

Start with the actual calling form, followed by what the function does. Describe meaningful alternative forms on separate lines. Keep a usage message short enough for quick help; put detailed option tables, algorithms and examples in the other layers.

These are proposed usage texts for the planned API:

```wolfram
BuildGroup::usage =
    "BuildGroup[spec, opts] constructs a finite group with its complete irreducible character table and the requested optional data.";

ModularFormQExp::usage =
    "ModularFormQExp[form, n] computes and stores the q-expansion through powers less than n and returns the same form object.\nModularFormQExp[form] uses cutoff 5.";
```

Mention mutation when it is central to the call. The built-in [AppendTo documentation](https://reference.wolfram.com/language/ref/AppendTo.html) is a useful example of documenting both an update and its evaluation requirements. Our registry-based update functions must document their own actual behavior; they do not inherit `AppendTo`'s attributes by analogy.

### Minimum source documentation

Every named public/private entity receives:

- **Summary:** one sentence saying what it does.
- **Signatures:** supported forms. A directly adjacent simple definition may supply the signature; list overloads when they differ.
- **Parameters:** meaning and supported domain for every parameter, including preconditions and ordering where relevant.
- **Options/defaults:** every optional positional argument and option, its default and accepted values; state `None` when there are none. A precise link to the owning shared option table may replace duplication.
- **Returns:** result shape and meaning, including `Failure`/`Missing` cases when applicable.
- **Effects:** object mutation, caches, I/O, workers and ownership; explicitly say when it is pure.
- **Failures:** rejected cases, diagnostics and preservation/cleanup guarantees; document caller-established preconditions for an internal helper.
- **Example:** at least one concrete use and its expected result or property.
- **See also:** relevant functions, schemas, plans or mathematical sources. Do not invent a meaningless cross-reference just to fill a field.

For a data head/schema, replace ordinary parameter/return prose with its constructor fields, validity conditions, identity, access and mutability rules. Configuration symbols/constants document their meaning, default/unit and owning operations. Simple anonymous functions are covered by the containing algorithm's documentation; name and document them separately when they embody a reusable or non-obvious operation.

One block can document an overload family or a shared upvalue method when it explicitly covers each form. Public and private code have the same requirement for a usable explanation and example; private helpers do not need exported usage messages or public reference pages.

### Additional documentation for important or complex entities

Add **Remarks** explaining purpose and the main algorithm actually implemented, rather than restating the summary. Add **Notes** for important constraints. Where applicable include:

- Mathematical conventions, hypotheses, domains and a precise source/equation reference.
- Generator/character/basis correspondence and tensor-factor ordering.
- Exact versus numerical arithmetic, precision, tolerances and evidence status.
- Branch conventions and truncation/cutoff meaning.
- Cache dependencies and invalidation, method selection and timeout behavior.
- Atomic update boundaries, cancellation and concurrency behavior.
- Complexity or measured performance where this affects method choice.

A citation does not establish that the code meets the cited theorem's assumptions. State those assumptions and how the implementation checks or requires them.

### A complete small example

The following standalone package illustrates public usage, public/private source comments and explicit failure handling. `StyleGuideExample\`` is a teaching context, not a proposed VVMFTool API.

```wolfram
BeginPackage["StyleGuideExample`"];

CheckCount::usage =
    "CheckCount[count] returns a positive integer count, or a Failure when count is not a positive integer.";

Begin["`Private`"];

(*
    Summary: Test whether a supplied count is a positive integer.
    Parameters: count — any evaluated Wolfram expression.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: Noninteger and nonpositive inputs return False.
    Example: positiveIntegerQ[3] returns True;
        positiveIntegerQ[0] returns False.
    See also: CheckCount; IntegerQ.
*)
positiveIntegerQ[count_] := IntegerQ[count] && count > 0;

(*
    Summary: Validate a count before passing it to a consumer.
    Status: Experimental, for this documentation example.
    Parameters: count — any evaluated Wolfram expression.
    Options/defaults: None.
    Returns: The supplied positive integer, or
        Failure["InvalidCount", association].
    Effects: Pure; emits no messages.
    Failures: Noninteger or nonpositive input produces InvalidCount.
    Example: CheckCount[3] returns 3;
        FailureQ[CheckCount[0]] returns True.
    See also: positiveIntegerQ; FailureQ.
*)
CheckCount[count_] := If[
    positiveIntegerQ[count],
    count,
    Failure["InvalidCount", <|
        "MessageTemplate" -> "The count must be a positive integer.",
        "Input" -> count
    |>]
];

End[];
EndPackage[];
```

Larger mathematical routines need the additional remarks and conventions described above. This small validation example is not a template for reducing all mathematical validation to a head check.

### Module headers and section comments

Start each major source module with its title, context, summary, responsibilities and important dependencies. Wolfram's installed `Combinatorica.m` provides an example of colon-labelled package header comments; the exact fields we require are a project choice.

```wolfram
(*
    :Title: Representation validation
    :Context: VVMFTool`Private`
    :Summary: Validate representation data against accepted group data.
    :Responsibilities:
        - Check dimensions and recorded generator correspondence.
        - Report exact or numerical validation evidence.
    :Dependencies: Representation contexts and the scalar codec.
    :See Also: VVMFArch/step2Plan.md
*)

(* -------------------------------------------------------------------------
   Generator correspondence
   ------------------------------------------------------------------------- *)
```

Preserve applicable copyright and attribution notices. A header is not a place for conversation history or an automatically growing modification diary. Notebook-export markers such as `(* ::Section:: *)` may organize notebook-backed source; they do not replace contract documentation.

### Native reference pages and examples

Use native reference notebooks for integrated Wolfram documentation. They should provide calling forms, details/options, basic examples, supported scope, relevant applications, important relations/limitations and links to related functions and guides. Option tables identify the symbol, default and meaning; include allowed values in the explanation. Wolfram's [symbol-page authoring guide](https://reference.wolfram.com/language/DocumentationTools/tutorial/AuthoringSymbolPagesUsingDocumentationTools.html) describes its structured cells and linking tools.

Authoring notebooks and built documentation are different artifacts. When packaging Documentation Center integration, use the documented DocumentationTools/PacletTools workflow; Markdown does not become a native reference page merely by putting it in a documentation directory. See [Creating Paclets](https://reference.wolfram.com/language/PacletTools/tutorial/CreatingPaclets.html). This guide does not change the agreed package-loading architecture.

Examples must have enough setup to run in a fresh session, use public interfaces in user documentation, and show an expected value or mathematical property. Avoid `%`, `Out[n]`, hidden notebook assignments and unexplained external files. Mark schematic fragments and prerequisites explicitly; do not label an example with omitted code as runnable.

Show common success, important option variations, invalid input and recovery where applicable. Keep public examples small enough to run, and place resource-heavy examples in a clearly identified section. Use isolated temporary storage for examples that clean caches or overwrite files. Add representative examples to executable tests so documentation and behavior remain consistent.

### Maturity and current-state documentation

Each exported API's full documentation has a status:

| Status | Meaning |
| --- | --- |
| Experimental | Exploratory interface with no stability guarantee |
| Alpha | Early preview whose interface may change substantially |
| Beta | Mostly settled interface with smaller changes still possible |
| Stable | Supported public contract |
| Deprecated | Still available; documentation identifies the supported replacement |

Maturity and exported visibility are separate: an exported symbol is not automatically stable.

Document the current contract and implementation. Replace obsolete descriptions when behavior changes. Keep conversation history, rejected alternatives and implementation chronology in review/history records, not comments, usage messages or reference pages. A necessary deprecation notice describes present availability and migration, not a historical narrative. Do not claim planned functionality is already implemented.

Inline comments explain an invariant, a non-obvious step, a justified workaround or a mathematical choice. Avoid narrating obvious assignments. Keep the explanation next to the code it concerns and revise it with that code.

## 6. File organization

Group code by mathematical or operational responsibility. Keep a helper in its owning file when only that entity uses it; extract substantial shared logic into a clearly named module when several owners need it. Avoid miscellaneous helper collections with no defined responsibility.

The stage plans' `Kernel/` modules remain the implementation layout. Keep GAP adapters under `GAP/`, schemas/data in their designated storage location, and tests grouped by unit, integration and end-to-end purpose. Front-end formatting and export adapters depend on mathematical data interfaces; they do not own the mathematical algorithms.

Within a module, use a consistent order: header, public declarations where owned by the loader arrangement, options/constants/schema information, private helpers, public methods and formatting/adapters where those belong to this module. Dependency requirements take precedence over a cosmetic ordering rule. Create separate files when they have a defined responsibility.

## 7. Notebook interfaces and presentation

Notebook presentation follows these conventions:

- Prefer named, documented builder functions for reusable or substantial interfaces. Short pure functions remain idiomatic for local callbacks and transformations.
- Give public or complex UI data/options an explicit documented schema. A tiny private widget may document its inputs locally.
- Keep scientific state in the specified objects and snapshots. Use `DynamicModule` for interface-local state such as selection and expanded sections; its variables can persist in a notebook, so define save/restore expectations deliberately. See [DynamicModule](https://reference.wolfram.com/language/ref/DynamicModule.html).
- Keep formatting cheap and read-only. Displaying `Group`, `Rep` or `ModularForm` must not unexpectedly launch GAP, solve coefficients, change a basis or mutate scientific state.
- Preserve the plans' distinction between computational expressions and presentation. A `MatrixForm` or typeset table is not the underlying matrix or character-table data.
- Make front-end dependencies explicit. Package loading, computation and export operations specified for headless use must not depend on an open notebook.

Pass the intended data/context explicitly and keep notebook state ownership clear.

## 8. Testing

Use `VerificationTest` and `TestReport` for Wolfram tests, organized in `.wlt` files. `TestReport` supports tests collected in a file or explicit test expressions; see [VerificationTest](https://reference.wolfram.com/language/ref/VerificationTest.html) and [TestReport](https://reference.wolfram.com/language/ref/TestReport.html). GAP and generated Python require tests appropriate to their own runtimes.

Every implemented function, including private helpers, must have unit coverage of its supported input variations and applicable errors. Maintain the implementation workflow's function-to-test inventory. Each stage also has several realistic public-interface end-to-end tests, including relevant recovery paths. A review pass does not replace executed tests.

Give tests stable, descriptive `TestID` values. Structure nontrivial tests as arrange, act, assert, with local fixture state. Assert mathematical properties, structured error details and relevant state preservation. Do not merely assert that a call finished or returned an expression of some head.

After evaluating the standalone example package above, this is a runnable small report:

```wolfram
TestReport[{
    VerificationTest[
        StyleGuideExample`CheckCount[3],
        3,
        TestID -> "CheckCount/positive-integer"
    ],
    VerificationTest[
        MatchQ[
            StyleGuideExample`CheckCount[0],
            Failure["InvalidCount", _Association]
        ],
        True,
        TestID -> "CheckCount/rejects-zero"
    ],
    VerificationTest[
        FailureQ[StyleGuideExample`CheckCount[3.]],
        True,
        TestID -> "CheckCount/rejects-approximate-count"
    ],
    VerificationTest[
        StyleGuideExample`Private`positiveIntegerQ[-1],
        False,
        TestID -> "positiveIntegerQ/negative-integer"
    ]
}]
```

For APIs that intentionally emit messages, declare expected messages in the test and check the returned failure separately. Do not hide unexpected messages to make the test pass. Numerical tests use justified precision/tolerances; exact tests verify exact identities. Where bases or multiplicity choices are not uniquely prescribed, test the specified covariance/equivalence and normalization rather than an incidental printed matrix.

Create fixture and mock factories near the owning tests. Inject backend outcomes through the specified adapter boundary; scope replacements and restore them. Use deterministic failure injection for process errors, timeouts, cancellation and save failures, plus real backend end-to-end runs. Mock state does not prove a real GAP workspace can be restored.

Prefer state assertions over fragile pixel comparisons. Also inspect rendered notebook/export output when its visual correctness is part of the task. Test observable values, not write-only or incidental display internals.

Use the actual project test entry points once implemented, and document their exact commands and prerequisites in the test instructions. This draft does not invent working test-runner commands. Record tested code identity, runtime/dependency versions, pass/fail/skip counts and required unavailable tests. A skipped required test is not a pass.

## 9. Mathematical conventions and reproducibility

Preserve and document the mathematical contracts in the stage plans; do not infer extra mathematical operations from a preferred coding idiom.

| Topic | Required documentation |
| --- | --- |
| Group generators | Their ordered names and correspondence to the computational group; assigned S,T words when present |
| Representations | Which group/context a value is bound to, generator ordering, actual basis, arithmetic and validation status |
| Basis change | Direction of the transformation; for the planned convention, `newMatrix = B . oldMatrix . Inverse[B]` and `newVector = B . oldVector` |
| CG coefficients | Tensor-factor order, source/target bases, multiplicity labels, normalization, and whether the map embeds or extracts a component |
| Conjugation | Whether a formula uses transpose, complex conjugation or conjugate transpose |
| Modular series | Coordinate, branch/sheet, allowed exponents, cutoff and omitted-order meaning |
| Numerical results | Working precision, residual/error evidence, reconstruction checks and whether a claim is exact, numerical or unverified |
| Persistence | Mathematical identity, snapshot/handle semantics, cache dependencies and required runtime compatibility |

In particular, retain these agreed distinctions:

- `Rep` is a transparent value; transformations return new values. `Group` and `ModularForm` are registry-backed objects with controlled updates.
- Coefficient computation and `ModularFormQExp` update the same form. Differentiation and basis change produce new form objects according to stage 7.
- The q cutoff `n` retains powers strictly less than `n`. An empty truncation does not establish that the function is zero.
- Distinct modular realizations remain distinct even when abstract group IDs agree. General group operations do not acquire an S,T requirement without a mathematical reason.
- A small numerical residual is not an exact proof. Changing precision, applying `Chop`, `Rationalize`, `PowerExpand` or a branch-changing rewrite is a mathematical decision requiring the specified justification and checks.
- VVMF tensor operations follow the agreed interfaces. The guide does not introduce ordinary multiplication of modular-form objects or infer equivalences that the design has not established.

Record computational dependencies and reproducible input/basis/normalization information with results where required by the plans. Performance claims require representative measurements and an identified environment.

## 10. Asynchronous and parallel work

Prefer explicit task submission, result collection and cleanup over tangled callback/state chains. Wolfram's `ParallelSubmit` creates scheduled evaluations; its variable-list form captures values, and `WaitAll` collects results. Definitions and required data must be available on the worker kernels. See [ParallelSubmit](https://reference.wolfram.com/language/ref/ParallelSubmit.html) and [Managing Parallel Processes](https://reference.wolfram.com/language/Parallel/tutorial/ConcurrencyManagingParallelProcesses.html).

This is a small language example, not an implementation of the VVMFTool scheduler:

```wolfram
With[{inputs = {5, 6, 7}},
    WaitAll[
        Table[
            ParallelSubmit[{input}, Factorial[input]],
            {input, inputs}
        ]
    ]
]
(* Expected: {120, 720, 5040}; requires available parallel kernels. *)
```

Mathematical routines that launch workers request them through the shared scheduler. They do not independently launch unbudgeted workers. Document what is parallelized: independent method attempts, separate irreps, or work within one algorithm. Ordinary GAP execution does not become a multicore algorithm merely because Wolfram launches it.

Follow the design's core/memory budgets, batching threshold, per-attempt timeouts and cancellation policy. Workers operate on isolated state. The coordinator validates results and saves the coherent result/checkpoint before cancelling competing work. Do not assume separate GAP workspaces or Wolfram object registries merge automatically.

Keep resource ownership and cleanup explicit, including failure and cancellation paths. Shared caches and object mutation require the planned identity/revision checks. Describe these effects in the owning function's documentation rather than hiding them in a callback.

## 11. Review checklist

- The code follows Wolfram evaluation semantics; formatting has not changed returns, patterns, scope or precision.
- Public names/options, private contexts and string properties match the design.
- Every named public/private function and schema has a contract and example; every exported symbol has concise usage help.
- Complex mathematics documents conventions, assumptions and evidence, with precise references where needed.
- Current code, defaults, messages, reference pages and examples agree; planned behavior is not claimed as implemented.
- Unit tests cover supported inputs and applicable failures, and stage end-to-end tests exercise real workflows.
- Presentation, persistence and concurrent work preserve the specified mathematical identity and state.

The existing [implementation workflow](VVMFArch/implementationGoal.md) governs stage reviews and commit checkpoints. This guide adds coding/documentation conventions; it does not replace that workflow.

## 12. Wolfram references

Official examples inspected include Wolfram's shipped `Collatz.m`, referenced by the [BeginPackage documentation](https://reference.wolfram.com/language/ref/BeginPackage.html), and the package headers in `Combinatorica.m`. Their locations relative to `$InstallationDirectory` are `Documentation/English/System/ExampleData/Collatz.m` and `AddOns/Packages/Combinatorica/Combinatorica.m`, where included in the installed distribution. The built-in reference pages linked above and DocumentationTools' authoring instructions also inform this guide; they do not prescribe every project convention in this draft.
