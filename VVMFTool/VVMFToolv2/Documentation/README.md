# VVMFTool documentation

Open [ConstructingFiniteGroups.nb](English/Tutorials/ConstructingFiniteGroups.nb) for a
complete workflow (characters and verified representations), or a symbol notebook under
[ReferencePages/Symbols](English/ReferencePages/Symbols). Keep the notebooks in their
repository locations so their package-loading cells can resolve `Kernel/init.m`.
Evaluate the setup before the examples. A local GAP installation with JSON, IO and
workspace support is required; the bounded normal-subgroup search additionally needs
LINS. `ConfigureVVMFTool[GAPExecutable -> absolutePath]` selects an executable explicitly.

The current APIs are alpha. Builders compute every irreducible representation by default
(`ComputeRepresentations -> True`, `Basis -> "Unitary"`), verified in GAP; use
`ComputeRepresentations -> False` for a character-only group and compute representations later
with `ComputeGroupRepresentations`. Representation reference pages describe the verification tier of
each stored variant (native in GAP, or Wolfram-exact and numerical variants verified in Wolfram).

The reference notebooks are native **authoring notebooks**, with Wolfram's function-page
styles, usage, details/options, examples and local links. They are not yet an installed
Documentation Center paclet. Authoring and built documentation are distinct in the
[official symbol-page guide](https://reference.wolfram.com/language/DocumentationTools/tutorial/AuthoringSymbolPagesUsingDocumentationTools.html).
Documentation Center packaging can use the documented
[PacletTools workflow](https://reference.wolfram.com/language/PacletTools/tutorial/CreatingPaclets.html)
when distribution is prepared; no alternative package loader is introduced here.

Maintain `Source/Stage1.json` and `Source/Tutorial.json`, then run
`WolframKernel -noinit -noprompt -run 'Get["Documentation/Source/Build.wls"]'` from the
repository root. Generation parses the repository-owned examples under HoldComplete
and never evaluates them. Usage and option tables come from the actual package symbols.
`Tests/Integration/Documentation.wls` executes all examples and verifies the notebook
input boxes match the source. `DocumentationNotebook.wls` renders representative pages
and the tutorial with the installed Wolfram front end for visual inspection.

Examples that clean GAP state use an isolated temporary cache. Save examples register
mathematical file digests in the independent local export ledger; cache cleanup leaves
that ledger intact. The documentation test runner isolates both cache and ledger.
