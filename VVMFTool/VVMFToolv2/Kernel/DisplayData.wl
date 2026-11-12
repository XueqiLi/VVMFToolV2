(*
    :Title: Display documents: immutable snapshots of accepted group data
    :Context: VVMFTool`Private`
    :Summary: DisplayDocument values, TeXFragment, the display node registry, document validation and the
        view producers GroupSummary, CharacterTableView, RepresentationTable and RepresentationView.
    :Responsibilities:
        - DisplayDocument[kind, data] and DisplayData: inert snapshots with source identities, ordered
          exact cells, labels and presentation defaults; never a live Group handle.
        - registerDisplayNode: the closed node registry (validator, notebook renderer, TeX renderer,
          dependency collector) that later stages extend.
        - Snapshots read accepted data only: no GAP process, no computation of representations, no change of
          group data, caches or the GAP cache index.
    :Dependencies: Diagnostics.wl; GroupObject.wl (groupData); DisplayLabels.wl; Representation.wl;
        GroupConstruction.wl (resolveOperationOptions).
    :See Also: VVMFArch/step3Plan.md; VVMFArch/implementation/step3Status.md.
*)

$DisplaySchemaVersion = 1;
$DisplayKinds = {"GroupSummary", "Representation", "RepresentationTable", "CharacterTable", "TensorDecomposition"};
$DisplayPresentationOptions = {ScalarNotation, NotationStyle, OneByOneMatrix, DefineOmega, Digits, Caption, Label, PageSize};

(* -------------------------------------------------------------------------
   Node registry
   ------------------------------------------------------------------------- *)

If[!AssociationQ[$DisplayNodeRegistry], $DisplayNodeRegistry = <||>];

(*
    Summary: Register a display node kind with all four of its handlers.
    Parameters: kind — node kind string; handlers — <|"Validate", "Notebook", "TeX", "Dependencies"|>, each a
        function of the node (Notebook and TeX also receive the render settings).
    Options/defaults: Re-registering a kind replaces its handlers.
    Returns: kind, or InvalidDisplayNode Failure.
    Effects: Updates $DisplayNodeRegistry.
    Failures: Missing or extra handlers, non-function handlers or an empty kind.
    Example: registerDisplayNode["Text", <|"Validate" -> ..., "Notebook" -> ..., "TeX" -> ..., "Dependencies" -> ...|>].
    Remarks: Later stages (4, 6, 9) add their nodes here; a node of an unregistered kind fails validation and
        is never rendered.
    See also: displayNodeQ; renderNotebookCell; renderTeXNode.
*)
registerDisplayNode[kind_String, handlers_Association] := If[
    StringLength[kind] > 0 && Sort[Keys[handlers]] === Sort[{"Validate", "Notebook", "TeX", "Dependencies"}] &&
        AllTrue[Values[handlers], MatchQ[#, _Function | _Symbol] &],
    AssociateTo[$DisplayNodeRegistry, kind -> handlers]; kind,
    makeFailure["InvalidDisplayNode", "A display node kind needs Validate, Notebook, TeX and Dependencies handlers.",
        <|"Kind" -> kind|>]];
registerDisplayNode[___] := makeFailure["InvalidDisplayNode", "Expected a node kind and its handlers."];

(*
    Summary: Check a display node against its registered validator.
    Parameters: node — any expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None (False for unknown kinds and malformed nodes).
    Example: displayNodeQ[<|"Kind" -> "Text", "Text" -> "a"|>] is True.
    See also: registerDisplayNode.
*)
displayNodeQ[node_Association] := With[{handlers = Lookup[$DisplayNodeRegistry, Lookup[node, "Kind", None], None]},
    AssociationQ[handlers] && TrueQ[handlers["Validate"][node]]];
displayNodeQ[_] := False;

(* -------------------------------------------------------------------------
   Document kind registry (later stages)
   ------------------------------------------------------------------------- *)

If[!AssociationQ[$DisplayKindRegistry], $DisplayKindRegistry = <||>];

(*
    Summary: Register a display document kind of a later stage with its schema, caption and renderers.
    Parameters: kind — document kind string (not a Stage 3/4 kind); handlers — <|"Fields" -> required cell keys,
        "Check" -> function of the data (True for consistent cells), "Caption" -> function of the data returning the
        caption text, "TeX" -> function (data, settings) returning <|"Tables" -> {Table specs}, "Legend" -> {strings}|>,
        "Notebook" -> function (data, settings) returning <|"Sections" -> {<|"Title", "Header", "Rows"|>...},
        "Legend" -> {strings}|>|>.
    Options/defaults: Re-registering a kind replaces its handlers.
    Returns: kind, or InvalidDisplayKind Failure.
    Effects: Updates $DisplayKindRegistry.
    Failures: Missing or extra handlers, a non-list Fields, a Stage 3/4 kind name or an empty kind.
    Example: Stage 6 registers "Model", "Fields", "Contractions", "Couplings", "MassMatrix" and "ModelOutput".
    Remarks: The shared validation, captions, LaTeX tables (panels, legends, standalone documents), paged notebook
        views, static notebooks and atomic export apply to registered kinds unchanged; a Table spec is the Table node
        of renderTeXTable without its caption and label, plus an optional "Title".
    See also: validateDisplayDocument; renderTeXDocument; notebookTableParts.
*)
registerDisplayKind[kind_String, handlers_Association] := If[
    StringLength[kind] > 0 && !MemberQ[$DisplayKinds, kind] &&
        Sort[Keys[handlers]] === Sort[{"Fields", "Check", "Caption", "TeX", "Notebook"}] && ListQ[handlers["Fields"]] &&
        AllTrue[Values[KeyDrop[handlers, "Fields"]], MatchQ[#, _Function | _Symbol] &],
    AssociateTo[$DisplayKindRegistry, kind -> handlers]; kind,
    makeFailure["InvalidDisplayKind", "A display kind needs Fields, Check, Caption, TeX and Notebook handlers.", <|"Kind" -> kind|>]];
registerDisplayKind[___] := makeFailure["InvalidDisplayKind", "Expected a kind and its handlers."];

(* -------------------------------------------------------------------------
   Documents
   ------------------------------------------------------------------------- *)

(*
    Summary: Immutable display snapshot of accepted data.
    Status: Alpha.
    Fields: SchemaVersion, Kind, Source (StateID, GeneratorIdentity, CharacterIdentity, AssignmentIdentity,
        Revision, StateGeneration), ObservedAt, Group, Presentation, Caption and kind-specific cells.
    Returns: DisplayDocument[kind, data]; v["Field"] reads a field.
    Identity/mutation: A value; later group changes never alter an existing document. Rebuild the view to
        show new state. A document certifies nothing mathematically.
    Example: DisplayData[CharacterTableView[g]]["IrrepIDs"] equals g["IrrepOrder"].
    See also: DisplayData; ToNotebook; ToLaTeX; ExportDisplay.
*)
Unprotect[DisplayDocument, TeXFragment];
DisplayDocument[kind_String, data_Association][key_String] := Lookup[data, key, Missing["UnknownProperty", key]];
(* A document renders itself in a notebook as ToNotebook shows it (uxUpdatePlan.md 2.1, U6): only snapshotted fields are
   used, never group state or GAP; the document stays embedded (Interpretation) so the output can be reused; a rendering
   failure falls back to the one-line summary without a message. OutputForm (ToString, Short) keeps the summary. *)
displayDocumentSummary[kind_String, data_Association] := Row[{"DisplayDocument[", Style[kind, Bold], ", ",
    ToString[Lookup[Lookup[data, "Group", <||>], "Name", ""]], "]"}];
Format[DisplayDocument[kind_String, data_Association], StandardForm] :=
    Interpretation[With[{rendered = Quiet[Check[ToNotebook[DisplayDocument[kind, data], PageSize -> All], $Failed]]},
            If[rendered === $Failed || FailureQ[rendered], displayDocumentSummary[kind, data], rendered]],
        DisplayDocument[kind, data]];
Format[DisplayDocument[kind_String, data_Association], OutputForm] := displayDocumentSummary[kind, data];
Format[TeXFragment[s_String], StandardForm] := Interpretation[Row[{"TeXFragment[", Style[s, "Program"], "]"}], TeXFragment[s]];
Protect[DisplayDocument, TeXFragment];

(*
    Summary: Validate a display document before rendering.
    Parameters: v — any expression.
    Options/defaults: None.
    Returns: The data association, or InvalidDisplayDocument Failure.
    Effects: Pure.
    Failures: Wrong head, kind, schema version, missing fields, cell shapes inconsistent with the ordered IDs,
        and label/caption nodes of unregistered kinds.
    Example: validateDisplayDocument[CharacterTableView[g]] returns its data.
    Remarks: A manually built or altered document fails here, before any rendering.
    See also: DisplayData; makeDisplayDocument.
*)
validateDisplayDocument[DisplayDocument[kind_String, data_Association]] := Module[{invalid, fields, ok},
    invalid[reason_] := makeFailure["InvalidDisplayDocument", "The display document is malformed.", <|"Reason" -> reason|>];
    If[!(MemberQ[$DisplayKinds, kind] || KeyExistsQ[$DisplayKindRegistry, kind]) || Lookup[data, "Kind", None] =!= kind, Return[invalid["Unknown kind"]]];
    If[Lookup[data, "SchemaVersion", None] =!= $DisplaySchemaVersion, Return[invalid["Unsupported schema version"]]];
    fields = Join[{"SchemaVersion", "Kind", "Source", "ObservedAt", "Group", "Presentation", "Caption"},
        Switch[kind,
            "CharacterTable", {"IrrepIDs", "Degrees", "ClassIDs", "ClassSizes", "ClassOrders", "ClassWords", "Values",
                "IdentityClassID", "TrivialIrrepID", "Labels", "LabelData"},
            "RepresentationTable", {"IrrepIDs", "MatrixSet", "RequestedBasis", "Rows", "Labels"},
            "Representation", {"Dimension", "MatrixSet", "Matrices", "Arithmetic", "Validation", "LabelData", "Label"},
            "GroupSummary", {"AvailableData", "Representations", "RequestedBasis", "GAPCache"},
            "TensorDecomposition", {"Products", "IrrepIDs", "LabelData", "Labels"},
            _, $DisplayKindRegistry[kind]["Fields"]]];
    If[!SubsetQ[Keys[data], fields], Return[invalid[{"Missing fields", Complement[fields, Keys[data]]}]]];
    If[!AssociationQ[data["Source"]] || !AssociationQ[data["Group"]] || !AssociationQ[data["Presentation"]] ||
        !displayNodeQ[data["Caption"]], Return[invalid["Source, group, presentation or caption"]]];
    ok = Switch[kind,
        "CharacterTable", With[{r = Length[data["IrrepIDs"]], c = Length[data["ClassIDs"]]},
            DuplicateFreeQ[data["IrrepIDs"]] && DuplicateFreeQ[data["ClassIDs"]] &&
            Dimensions[data["Values"]] === {r, c} && Length[data["Degrees"]] === r &&
            AllTrue[{data["ClassSizes"], data["ClassOrders"], data["ClassWords"]}, Length[#] === c &] &&
            Sort[Keys[data["Labels"]]] === Sort[data["IrrepIDs"]] && AllTrue[Values[data["Labels"]], displayNodeQ]],
        "RepresentationTable", Length[data["Rows"]] === Length[data["IrrepIDs"]] &&
            Lookup[data["Rows"], "IrrepID", None] === data["IrrepIDs"] &&
            AllTrue[data["Rows"], representationRowQ[#, Length[data["MatrixSet"]["Columns"]]] &] &&
            SubsetQ[Keys[data["Labels"]], data["IrrepIDs"]] && AllTrue[Values[data["Labels"]], displayNodeQ],
        "Representation", ListQ[data["Matrices"]] && Length[data["Matrices"]] === Length[data["MatrixSet"]["Columns"]] &&
            AllTrue[data["Matrices"], MatrixQ[#] && Dimensions[#] === {data["Dimension"], data["Dimension"]} &] &&
            displayNodeQ[data["Label"]],
        "GroupSummary", AssociationQ[data["AvailableData"]] && AssociationQ[data["GAPCache"]],
        (* Stage 4: every product's constituents account for its dimension and have labels. *)
        "TensorDecomposition", ListQ[data["Products"]] && AllTrue[data["Products"], Function[row, AssociationQ[row] &&
                ListQ[Lookup[row, "Factors", None]] && IntegerQ[Lookup[row, "Dimension", None]] && ListQ[Lookup[row, "Constituents", None]] &&
                Total[#["Multiplicity"] #["Dimension"] & /@ row["Constituents"]] === row["Dimension"] &&
                SubsetQ[data["IrrepIDs"], Join[row["Factors"], Lookup[row["Constituents"], "IrrepID", {}]]]]] &&
            SubsetQ[Keys[data["Labels"]], data["IrrepIDs"]] && AllTrue[Values[data["Labels"]], displayNodeQ],
        _, TrueQ[$DisplayKindRegistry[kind]["Check"][data]]];
    If[!TrueQ[ok], Return[invalid["Cells are inconsistent with the ordered identities"]]];
    data
];
validateDisplayDocument[_] := makeFailure["InvalidDisplayDocument", "Expected a DisplayDocument."];

(*
    Summary: Check the shape of one RepresentationTable row.
    Parameters: row — row association; columns — number of matrix columns.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: representationRowQ[row, 2] requires two d x d matrices or Missing matrices.
    See also: validateDisplayDocument.
*)
representationRowQ[row_Association, columns_Integer] := StringQ[Lookup[row, "IrrepID", None]] &&
    IntegerQ[Lookup[row, "Dimension", None]] && StringQ[Lookup[row, "Status", None]] &&
    (MissingQ[Lookup[row, "Matrices", Missing[]]] || (ListQ[row["Matrices"]] && Length[row["Matrices"]] === columns &&
        AllTrue[row["Matrices"], MatrixQ[#] && Dimensions[#] === {row["Dimension"], row["Dimension"]} &]));
representationRowQ[___] := False;

(*
    Summary: Which optional columns a table of representations shows (uxUpdatePlan.md 2.2, U4/U5).
    Parameters: names — irrepPresentation result; effective — options (ShowIDs, ShowStatus, ShowAutomaticLabels);
        attention — whether some row needs attention (not complete, numerical, or not exactly verified).
    Options/defaults: ShowStatus -> Automatic shows the status columns exactly when attention is True.
    Returns: <|"IDs", "Status", "Auto", "User"|> Booleans.
    Effects: Pure.
    Failures: None.
    Example: displayColumns[names, <|ShowIDs -> True|>, False]["IDs"] is True.
    See also: attentionRowsQ; irrepPresentation.
*)
displayColumns[names_Association, effective_Association, attention_] := <|"IDs" -> TrueQ[Lookup[effective, ShowIDs, False]],
    "Status" -> Switch[Lookup[effective, ShowStatus, Automatic], True, True, False, False, _, TrueQ[attention]],
    "Auto" -> TrueQ[Lookup[effective, ShowAutomaticLabels, True]] && AnyTrue[Values[names], #["Auto"] =!= None &],
    "User" -> AnyTrue[Values[names], #["User"] =!= None &]|>;
attentionRowsQ[rows_List] := AnyTrue[rows, Lookup[#, "Status", "Complete"] =!= "Complete" || Lookup[#, "Arithmetic", "Exact"] === "Numerical" ||
    MemberQ[{"Numerical", "Unverified"}, Lookup[#, "VerificationStatus", "Exact"]] &];

(*
    Summary: Build a display document from snapshot data.
    Parameters: kind — document kind; data — snapshot cells; settings — the producer's effective options.
    Options/defaults: None.
    Returns: A validated DisplayDocument, or Failure.
    Effects: Pure.
    Failures: InvalidDisplayDocument.
    Example: makeDisplayDocument["CharacterTable", cells, effective].
    See also: validateDisplayDocument.
*)
makeDisplayDocument[kind_String, data_Association, settings_Association] := Module[{full, document, caption},
    full = Join[<|"SchemaVersion" -> $DisplaySchemaVersion, "Kind" -> kind|>, data,
        <|"Presentation" -> KeyTake[settings, $DisplayPresentationOptions]|>];
    caption = Lookup[settings, Caption, Automatic];
    full["Caption"] = Which[caption === Automatic, formatGroupCaption[full], StringQ[caption], textNode[caption],
        True, labelNode[caption]];
    document = DisplayDocument[kind, full];
    With[{checked = validateDisplayDocument[document]}, If[FailureQ[checked], checked, document]]
];

(*
    Summary: The data association of a display document.
    Status: Alpha.
    Parameters: v — DisplayDocument.
    Options/defaults: None.
    Returns: The immutable data association, or Failure for a malformed document.
    Effects: Pure.
    Failures: InvalidDisplayDocument.
    Example: DisplayData[RepresentationTable[g]]["Rows"] lists one association per irrep.
    See also: DisplayDocument.
*)
DisplayData[document_DisplayDocument] := validateDisplayDocument[document];
DisplayData[___] := makeFailure["InvalidDisplayDocument", "DisplayData expects a DisplayDocument."];

(* -------------------------------------------------------------------------
   Shared snapshot pieces
   ------------------------------------------------------------------------- *)

(*
    Summary: Source identities and group metadata of a display snapshot.
    Parameters: data — display group data.
    Options/defaults: None.
    Returns: <|"Source" -> identities, "ObservedAt" -> ISO date, "Group" -> name/order/catalogue/generators/
        assignment/irrep count|>.
    Effects: Pure (reads the clock).
    Failures: None.
    Example: displayHeader[groupData[g]]["Group"]["Order"] is g["Order"].
    See also: makeDisplayDocument.
*)
displayHeader[data_Association] := Module[{assignment = Lookup[data, "ModularAssignment", Missing["NotAssigned"]], names},
    names = Lookup[data["Generators"], "Name", {}];
    <|"Source" -> <|"StateID" -> data["StateID"], "GeneratorIdentity" -> data["GeneratorIdentity"],
            "CharacterIdentity" -> Lookup[Lookup[data, "CharacterData", <||>], "Identity", Missing["NotComputed"]],
            "AssignmentIdentity" -> If[AssociationQ[assignment], assignment["Identity"], Missing["NotAssigned"]],
            "Revision" -> Lookup[data, "Revision", Missing["Unknown"]], "StateGeneration" -> Lookup[data, "StateGeneration", Missing["Unknown"]]|>,
        "ObservedAt" -> DateString["ISODateTime"],
        "Group" -> <|"Name" -> Lookup[data, "Name", "Group of order " <> ToString[data["Order"]]], "Order" -> data["Order"],
            "CatalogueID" -> Replace[Lookup[data, "CatalogueID", Missing["NotAvailable"]], Null | None -> Missing["NotAvailable"]],
            "Generators" -> names,
            "Assignment" -> If[AssociationQ[assignment], <|"Identity" -> assignment["Identity"],
                "SText" -> wordText[assignment["S"]], "TText" -> wordText[assignment["T"]]|>, Missing["NotAssigned"]],
            "IrrepCount" -> Length[Lookup[Lookup[data, "CharacterData", <||>], "IrrepIDs", {}]],
            (* the paper's TeX title (SetGroupTitle, library groups); LaTeX captions use it with NotationStyle -> "Paper" *)
            "TitleTeX" -> Replace[Lookup[data, "TitleTeX", None], Except[_String] -> None],
            (* the group's own status when weaker than "Exact" (methodOptionsPlan.md 2C.6), shown in the caption *)
            Sequence @@ With[{s = groupVerificationStatus[data]}, If[s === "Exact", {}, {"VerificationStatus" -> s}]]|>|>
];

(*
    Summary: Plain text of a group word for display.
    Parameters: word — GroupWord.
    Options/defaults: None.
    Returns: String such as "S.T^-1" ("1" for the empty word).
    Effects: Pure.
    Failures: None.
    Example: wordText[GroupWord[{{"S", 1}, {"T", -1}}]] is "S.T^-1".
    See also: displayHeader.
*)
wordText[GroupWord[syllables_List]] := If[syllables === {}, "1",
    StringRiffle[Map[If[Last[#] === 1, First[#], First[#] <> "^" <> ToString[Last[#]]] &, syllables], "."]];
wordText[GroupWord[text_String]] := text;
wordText[other_] := ToString[other];

(*
    Summary: Read-only availability of a group's retained GAP state, as observed now.
    Parameters: data — group data.
    Options/defaults: None.
    Returns: <|"State" -> "NotStored" | "Missing" | "Present (compatibility unchecked)" | "Incompatible" |
        "Unreadable", "Reason", "ObservedAt"|>.
    Effects: Reads the cache index JSON and checks file existence only; never uses cache accessors that
        update last-use times or consume entries, never launches GAP or restores state.
    Failures: None (read errors are reported as Unreadable).
    Example: a group built with StoreGAPState -> False is NotStored.
    Remarks: A present workspace is not a promise that restoration will succeed.
    See also: GroupSummary; Schemas/GAPCache.md.
*)
gapCacheAvailability[data_Association] := Module[{path, metadata, index, entry, now, state},
    now = DateString["ISODateTime"];
    state[s_, reason_] := <|"State" -> s, "Reason" -> reason, "ObservedAt" -> now|>;
    path = Lookup[data, "GAPCachePath", Missing["NotStored"]];
    metadata = Lookup[data, "GAPCacheMetadata", Missing["NotStored"]];
    If[!StringQ[path] || !AssociationQ[metadata], Return[state["NotStored", "No GAP state was retained for this group."]]];
    If[FileType[path] =!= File, Return[state["Missing", "The retained workspace file no longer exists."]]];
    With[{configured = Lookup[$Configuration, CacheDirectory, None]},
        If[StringQ[configured] && canonicalDisplayPath[configured] =!= canonicalDisplayPath[metadata["Root"]],
            Return[state["Incompatible", "The state was retained in another cache directory than the configured one."], Module]]];
    index = Quiet[Check[Import[FileNameJoin[{metadata["Root"], ".vvmf-cache.json"}], "RawJSON"], $Failed]];
    If[!AssociationQ[index], Return[state["Unreadable", "The cache index cannot be read."]]];
    If[Lookup[index, "CacheID", None] =!= metadata["CacheID"], Return[state["Incompatible", "The cache store was replaced."]]];
    entry = Lookup[Lookup[index, "Entries", <||>], metadata["EntryID"], None];
    If[!AssociationQ[entry], Return[state["Missing", "The cache entry was evicted."]]];
    If[TrueQ[Lookup[entry, "PendingEviction", False]], Return[state["Incompatible", "The cache entry is queued for eviction."]]];
    If[Lookup[entry, "Runtime", None] =!= metadata["Runtime"], Return[state["Incompatible", "The entry's runtime fingerprint differs from the recorded one."]]];
    state["Present (compatibility unchecked)", "The workspace is indexed; restoration is not attempted by a display."]
];

(*
    Summary: A canonical absolute form of a path for comparison (no file access).
    Parameters: path — string.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: canonicalDisplayPath["/tmp/a/../b"] is "/tmp/b".
    See also: gapCacheAvailability.
*)
canonicalDisplayPath[path_String] := Quiet[Check[FileNameJoin[FileNameSplit[ExpandFileName[path]]], path]];

(*
    Summary: The display status of one irrep's stored representation data.
    Parameters: entry — decoded representation entry or Missing; requested — Automatic or a basis.
    Options/defaults: None.
    Returns: <|"Status", "ActiveVariant", "Tier", "Arithmetic", "VerificationStatus" (the active variant's,
        methodOptionsPlan.md 2C.3), "BasisProperties", "Partial", "BasisComparison"|>.
    Effects: Pure.
    Failures: None.
    Example: an entry with only an accepted partial is "Partial: requested basis pending"; a Numerical-tier
        unitary variant under "Unitary" is "Active basis differs" with "Differs from Unitary (numerical evidence only)".
    Remarks: step3Status.md D-S3-1: the group records no requested basis; a partial exists only under an
        unsatisfied unitary request; the active variant is shown with its actual properties.
    See also: snapshotRepresentationRows.
*)
representationRowStatus[entry_, requested_, groupStatus_ : "Exact"] := Module[{active, partial, variant, meets, propertiesMeet, numerical},
    active = If[AssociationQ[entry], Lookup[entry, "ActiveVariant", Missing["NotComputed"]], Missing["NotComputed"]];
    partial = If[AssociationQ[entry], Lookup[entry, "AcceptedPartial", Missing["NotComputed"]], Missing["NotComputed"]];
    variant = If[StringQ[active], entry["Variants"][active], None];
    (* The stored properties decide (General: always; Unitary: unitary; UnitaryTDiagonal: unitary and T-diagonal).
       A Numerical-tier variant's properties are numerical evidence only: as in Stage 2 acceptance, it does not
       satisfy an exact Unitary or UnitaryTDiagonal request, and the comparison says why. *)
    numerical = AssociationQ[variant] && variant["Tier"] === "Numerical";
    propertiesMeet = AssociationQ[variant] && With[{properties = variant["BasisProperties"]}, Switch[requested,
        "General", True, "Unitary", TrueQ[properties["Unitary"]],
        _, TrueQ[properties["Unitary"]] && TrueQ[Lookup[properties, "TDiagonal", False]]]];
    meets = If[AssociationQ[variant] && requested =!= Automatic,
        requested === "General" || (propertiesMeet && !numerical), Missing["NotRequested"]];
    <|"Status" -> Which[
            AssociationQ[variant] && meets === False, "Active basis differs",
            AssociationQ[variant], "Complete",
            StringQ[partial], "Partial: requested basis pending",
            True, "Not computed"],
        "ActiveVariant" -> active,
        "Tier" -> If[AssociationQ[variant], variant["Tier"], Missing["NotComputed"]],
        "Arithmetic" -> If[AssociationQ[variant], variant["Arithmetic"], Missing["NotComputed"]],
        (* bounded by the group's own status, as every reader (methodOptionsPlan.md 2C.6) *)
        "VerificationStatus" -> If[AssociationQ[variant], cgWeakestStatus[{variantVerificationStatus[variant], groupStatus}], Missing["NotComputed"]],
        "BasisProperties" -> If[AssociationQ[variant], variant["BasisProperties"], Missing["NotComputed"]],
        "Partial" -> If[StringQ[partial], With[{p = entry["Variants"][partial]},
            <|"VariantID" -> partial, "Tier" -> p["Tier"], "Arithmetic" -> p["Arithmetic"], "BasisProperties" -> p["BasisProperties"]|>],
            Missing["None"]],
        "BasisComparison" -> Which[requested === Automatic, Missing["NotRequested"], !AssociationQ[variant], Missing["NotComputed"],
            TrueQ[meets], "Meets " <> requested, numerical && propertiesMeet, "Differs from " <> requested <> " (numerical evidence only)",
            True, "Differs from " <> requested]|>
];

(* -------------------------------------------------------------------------
   View producers
   ------------------------------------------------------------------------- *)

Options[CharacterTableView] = {RowOrder -> Automatic, ClassOrder -> Automatic, LabelStyle -> Automatic, IrrepLabels -> <||>,
    DisplayTimeLimit -> 5, ShowIDs -> False, ShowAutomaticLabels -> True, ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar",
    DefineOmega -> True, Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20};

(*
    Summary: Snapshot the character table of a group for display.
    Status: Alpha.
    Parameters: g — live Group with complete characters.
    Options/defaults: RowOrder -> Automatic (g["IrrepOrder"]) or a permutation of the irrep IDs; ClassOrder ->
        Automatic (stored class order) or a permutation of the class IDs; LabelStyle -> Automatic; IrrepLabels
        -> <||>; DisplayTimeLimit -> 5; presentation defaults (ScalarNotation, NotationStyle, OneByOneMatrix,
        DefineOmega, Digits, Caption, Label, PageSize) used by the renderers unless they are given again.
    Returns: DisplayDocument["CharacterTable", data] with ordered irrep IDs, degrees, class IDs, sizes, orders,
        representative words, exact values, identity/trivial IDs and labels; or Failure.
    Effects: Read-only; no GAP process, no representation computation; labels may use certified T phases of
        stored representations (read-only, bounded by DisplayTimeLimit).
    Failures: UnknownGroup; CharactersUnavailable; InvalidOption (orders that are not permutations, labels of
        unknown irreps).
    Example: DisplayData[CharacterTableView[g]]["IrrepIDs"] is g["IrrepOrder"].
    Remarks: Works without matrices and without S,T; permutations move headers, values, sizes, orders and
        words together.
    See also: ToNotebook; ToLaTeX; ExportDisplay; RepresentationTable.
*)
CharacterTableView[group_Group, options : OptionsPattern[]] := Module[
    {effective, data, characters, rows, classes, rowPositions, classPositions, labelData, names},
    effective = resolveOperationOptions[CharacterTableView, "CharacterTableView", {options}];
    If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[group, effective]; If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    characters = data["CharacterData"];
    If[!AssociationQ[characters], Return[makeFailure["CharactersUnavailable", "The group has no complete character table."]]];
    rows = If[effective[RowOrder] === Automatic, data["IrrepOrder"], effective[RowOrder]];
    (* the stored class order and names are the defaults (uxUpdatePlan.md 1.4) *)
    classes = If[effective[ClassOrder] === Automatic, Lookup[data, "ClassOrder", characters["ClassIDs"]], effective[ClassOrder]];
    If[Sort[rows] =!= Sort[characters["IrrepIDs"]] || Sort[classes] =!= Sort[characters["ClassIDs"]],
        Return[makeFailure["InvalidOption", "RowOrder and ClassOrder must be permutations of the irrep and class IDs.",
            <|"Options" -> {RowOrder, ClassOrder}|>]]];
    If[!SubsetQ[characters["IrrepIDs"], Keys[effective[IrrepLabels]]],
        Return[makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>]]];
    rowPositions = First[FirstPosition[characters["IrrepIDs"], #]] & /@ rows;
    classPositions = First[FirstPosition[characters["ClassIDs"], #]] & /@ classes;
    labelData = Association[Map[# -> irrepLabelData[data, #, effective[LabelStyle], effective[DisplayTimeLimit]] &, rows]];
    If[AnyTrue[Values[labelData], FailureQ], Return[FirstCase[Values[labelData], _Failure]]];
    names = irrepPresentation[data, rows, labelData, effective[IrrepLabels]];
    makeDisplayDocument["CharacterTable", Join[displayHeader[data], <|
        "IrrepNames" -> names, "Columns" -> displayColumns[names, effective, False],
        "ClassNames" -> Map[If[KeyExistsQ[Lookup[data, "ClassLabels", <||>], #], <|"Kind" -> "ClassLabel", "Record" -> data["ClassLabels"][#]["Name"]|>, None] &, classes],
        "IrrepIDs" -> rows, "Degrees" -> characters["Degrees"][[rowPositions]], "ClassIDs" -> classes,
        "ClassSizes" -> characters["ClassSizes"][[classPositions]], "ClassOrders" -> characters["ClassOrders"][[classPositions]],
        "ClassWords" -> (wordText /@ characters["ClassRepresentativeWords"][[classPositions]]),
        "Values" -> characters["Values"][[rowPositions, classPositions]],
        "IdentityClassID" -> characters["IdentityClassID"], "TrivialIrrepID" -> characters["TrivialIrrepID"],
        "LabelData" -> labelData, "Labels" -> Map[#["Display"] &, names]|>], effective]
];
CharacterTableView[___] := makeFailure["InvalidInput", "CharacterTableView expects a live group and options."];

(*
    Summary: Label data of one irrep of a group from its stored active variant, read-only.
    Parameters: data — group data; id — irrep ID; style — LabelStyle; limit — DisplayTimeLimit.
    Options/defaults: None.
    Returns: As displayLabelData; without an active variant, dimension/ID data (explicit TPhases then fails).
    Effects: As displayLabelData.
    Failures: As displayLabelData for explicit TPhases.
    Example: irrepLabelData[data, id, "ID", 5]["Style"] is "ID".
    See also: displayLabelData.
*)
irrepLabelData[data_Association, id_String, style_, limit_] := Module[{entry, active, degree},
    entry = Lookup[Lookup[data, "Representations", <||>], id, Missing[]];
    active = If[AssociationQ[entry], Lookup[entry, "ActiveVariant", Missing[]], Missing[]];
    degree = data["CharacterData"]["Degrees"][[First[FirstPosition[data["CharacterData"]["IrrepIDs"], id]]]];
    If[StringQ[active], displayLabelData[data, entry["Variants"][active]["Rep"], style, limit],
        If[style === "TPhases",
            makeFailure["SpectrumUnavailable", "The irrep has no stored representation, so no certified T phases.", <|"IrrepID" -> id|>],
            <|"Dimension" -> degree, "IrrepID" -> id, "TPhases" -> Missing["NotAvailable"], "Arithmetic" -> "Exact",
                "UniqueID" -> Missing["NotBound"], "Style" -> If[style === "ID", "ID", "Dimension"]|>]]
];

Options[RepresentationTable] = {MatrixSet -> Automatic, LabelStyle -> Automatic, IrrepLabels -> <||>, Basis -> Automatic,
    DisplayTimeLimit -> 5, ShowIDs -> False, ShowStatus -> Automatic, ShowAutomaticLabels -> True, ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar",
    DefineOmega -> True, Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20};

(*
    Summary: Snapshot the stored irreducible representations of a group for display.
    Status: Alpha.
    Parameters: g — live Group; ids — All (presentation order), one irrep ID or a duplicate-free list (caller
        order).
    Options/defaults: MatrixSet -> Automatic (assigned S,T for a group with a modular assignment, recorded
        generators otherwise), "Generators", "Modular" or a list of generator names; LabelStyle; IrrepLabels;
        Basis -> Automatic (report actual properties) or "General" | "Unitary" | "UnitaryTDiagonal" (also
        compare each row); DisplayTimeLimit; presentation defaults as for CharacterTableView.
    Returns: DisplayDocument["RepresentationTable", data] whose Rows give irrep ID, dimension, status ("Complete",
        "Active basis differs", "Partial: requested basis pending", "Not computed"), active variant, tier,
        arithmetic, basis properties, accepted partial and the selected matrices of the active variant; or
        Failure.
    Effects: Read-only; nothing is computed on the group (a missing representation stays "Not computed").
    Failures: UnknownGroup; InvalidIrrepID; InvalidOption; MissingModularAssignment (MatrixSet -> "Modular");
        InvalidMatrixSet; explicit LabelStyle -> "TPhases" without a certified spectrum.
    Example: DisplayData[RepresentationTable[g]]["Rows"][[1]]["Status"] is "Not computed" before any computation.
    Remarks: Accepted partial matrices are never shown as completed matrices.
    See also: CharacterTableView; RepresentationView; ToLaTeX.
*)
RepresentationTable[group_Group, selector : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] := withReadableBudget[representationTableSnapshot[group, selector, {options}], 30];
representationTableSnapshot[group_Group, selector_, {options___}] := Module[
    {effective, data, ids, set, names, rows, presentation},
    effective = resolveOperationOptions[RepresentationTable, "RepresentationTable", {options}];
    If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[group, effective]; If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    ids = If[selector === All, data["IrrepOrder"], irrepSelection[selector, data]];
    If[FailureQ[ids], Return[ids]];
    If[!SubsetQ[data["CharacterData"]["IrrepIDs"], Keys[effective[IrrepLabels]]],
        Return[makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>]]];
    set = resolveMatrixSet[effective[MatrixSet], data, Length[data["Generators"]]]; If[FailureQ[set], Return[set]];
    names = Lookup[data["Generators"], "Name", {}];
    rows = Map[Function[id, Module[{entry, status, matrices, labelData},
        entry = Lookup[data["Representations"], id, Missing["NotComputed"]];
        status = representationRowStatus[entry, effective[Basis], groupVerificationStatus[data]];
        matrices = If[StringQ[status["ActiveVariant"]], selectedMatrices[entry["Variants"][status["ActiveVariant"]]["Rep"], set, names],
            Missing["NotComputed"]];
        If[FailureQ[matrices], Return[matrices, Module]];
        labelData = irrepLabelData[data, id, effective[LabelStyle], effective[DisplayTimeLimit]];
        If[FailureQ[labelData], Return[labelData, Module]];
        Join[<|"IrrepID" -> id, "Dimension" -> data["CharacterData"]["Degrees"][[First[FirstPosition[data["CharacterData"]["IrrepIDs"], id]]]]|>,
            status, <|"Matrices" -> matrices, "LabelData" -> labelData|>]]], ids];
    If[AnyTrue[rows, FailureQ], Return[FirstCase[rows, _Failure]]];
    presentation = irrepPresentation[data, ids, AssociationThread[ids, Lookup[rows, "LabelData"]], effective[IrrepLabels]];
    makeDisplayDocument["RepresentationTable", Join[displayHeader[data], <|
        "IrrepIDs" -> ids, "MatrixSet" -> displayMatrixSet[set], "RequestedBasis" -> effective[Basis], "Rows" -> rows,
        "IrrepNames" -> presentation, "Columns" -> displayColumns[presentation, effective, attentionRowsQ[rows]],
        "Labels" -> Map[#["Display"] &, presentation]|>], effective]
];
RepresentationTable[___] := makeFailure["InvalidInput", "RepresentationTable expects a live group, an optional irrep selector and options."];

(*
    Summary: The display form of a resolved matrix set (words as text).
    Parameters: set — resolveMatrixSet result.
    Options/defaults: None.
    Returns: <|"Kind", "Columns" -> {<|"Name", "Word" (text) or "Index"|>...}|>.
    Effects: Pure.
    Failures: None.
    Example: a modular set shows columns S and T with their words.
    See also: resolveMatrixSet.
*)
displayMatrixSet[set_Association] := <|"Kind" -> set["Kind"],
    "Columns" -> Map[If[KeyExistsQ[#, "Word"], <|"Name" -> #["Name"], "Word" -> wordText[#["Word"]]|>, #] &, set["Columns"]]|>;

Options[RepresentationView] = {MatrixSet -> Automatic, LabelStyle -> Automatic, DisplayTimeLimit -> 5, ShowStatus -> Automatic,
    ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar", DefineOmega -> True,
    Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20};

(*
    Summary: Snapshot one representation value for display.
    Status: Alpha.
    Signatures: RepresentationView[r]; RepresentationView[c, r].
    Parameters: r — Rep; c — live Group or bound RepresentationContext whose recorded generators r uses.
    Options/defaults: MatrixSet -> Automatic (bare Rep: its generators g1, ..., gk, or indices; with a context,
        the assigned S,T if present, else the recorded generators, "Modular" or generator names);
        LabelStyle; DisplayTimeLimit; presentation defaults.
    Returns: DisplayDocument["Representation", data] with dimension, selected matrices, arithmetic and the
        validation evidence known without new work ("Stored variant", "Validated" from an existing
        ValidateRepresentation result, or "Unvalidated"); or Failure.
    Effects: Read-only; never starts a validation or any GAP work.
    Failures: InvalidRep; UnverifiedContext; GeneratorBindingMismatch; InvalidMatrixSet; MissingModularAssignment.
    Example: DisplayData[RepresentationView[Rep[{{{0, 1}, {1, 0}}}]]]["Validation"]["Status"] is "Unvalidated".
    Remarks: A bare Rep is never given S,T roles.
    See also: RepresentationTable; RepresentationLabelData.
*)
(* one readable-number budget per view (review F19): past it, entries keep their canonical form *)
RepresentationView[rep_Rep, options : OptionsPattern[]] := withReadableBudget[representationViewSnapshot[None, rep, {options}], 15];
RepresentationView[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] :=
    withReadableBudget[representationViewSnapshot[context, rep, {options}], 15];
RepresentationView[context : (_Group | _RepresentationContext), k_Integer, options : OptionsPattern[]] :=
    With[{rep = irrepActiveRep[context, k]}, Which[FailureQ[rep], rep,
        MissingQ[rep], makeFailure["MissingRepresentation", "The irrep has no computed representation.", <|"Index" -> k|>],
        True, RepresentationView[context, rep, options]]];
RepresentationView[___] := makeFailure["InvalidInput", "RepresentationView expects a Rep, optionally after a Group or RepresentationContext, and options."];

(*
    Summary: The shared body of both RepresentationView signatures.
    Parameters: context — None, Group or RepresentationContext; rep — Rep; options — option rules.
    Options/defaults: As RepresentationView.
    Returns: As RepresentationView.
    Effects: As RepresentationView.
    Failures: As RepresentationView.
    Example: representationViewSnapshot[None, r, {}] displays a bare Rep.
    See also: RepresentationView.
*)
representationViewSnapshot[context_, rep_Rep, options_List] := Module[
    {effective, shape, data, set, names, matrices, match, evidence, validation, labelData, header},
    effective = resolveOperationOptions[RepresentationView, "RepresentationView", options];
    If[FailureQ[effective], Return[effective]];
    shape = validateRepShape[rep]; If[FailureQ[shape], Return[shape]];
    data = If[context === None, None, displayGroupData[context]];
    If[FailureQ[data], Return[data]];
    If[AssociationQ[data] && shape["GeneratorCount"] =!= Length[data["Generators"]],
        Return[makeFailure["GeneratorBindingMismatch", "The representation does not have one matrix per recorded generator."]]];
    set = resolveMatrixSet[effective[MatrixSet], data, shape["GeneratorCount"]]; If[FailureQ[set], Return[set]];
    names = If[AssociationQ[data], Lookup[data["Generators"], "Name", {}], {}];
    matrices = selectedMatrices[rep, set, names]; If[FailureQ[matrices], Return[matrices]];
    match = If[AssociationQ[data], storedVariantMatch[data, rep], None];
    evidence = If[AssociationQ[data] && !AssociationQ[match], validationEvidence[data, rep], None];
    validation = Which[
        AssociationQ[match], <|"Status" -> "Stored variant", "IrrepID" -> match["IrrepID"], "VariantID" -> match["VariantID"],
            "Tier" -> match["Variant"]["Tier"], "BasisProperties" -> match["Variant"]["BasisProperties"],
            (* the stored variant's verification status (methodOptionsPlan.md 2C.3) *)
            "VerificationStatus" -> cgWeakestStatus[{variantVerificationStatus[match["Variant"]], groupVerificationStatus[data]}]|>,
        AssociationQ[evidence], <|"Status" -> "Validated", "IrrepID" -> Replace[Lookup[evidence, "Irreducible", None], None -> Missing["Reducible"]],
            "Homomorphism" -> Lookup[evidence, "Homomorphism", Missing[]], "BasisProperties" -> Lookup[evidence, "BasisProperties", Missing[]],
            "Arithmetic" -> Lookup[evidence, "Arithmetic", Missing[]]|>,
        True, <|"Status" -> "Unvalidated"|>];
    labelData = If[AssociationQ[data], displayLabelData[data, rep, effective[LabelStyle], effective[DisplayTimeLimit]],
        If[effective[LabelStyle] === "TPhases", makeFailure["SpectrumUnavailable", "A bare representation has no certified T phases."],
            <|"Dimension" -> shape["Dimension"], "IrrepID" -> Missing["NotBound"], "TPhases" -> Missing["NotAvailable"],
                "Arithmetic" -> shape["Arithmetic"], "UniqueID" -> Missing["NotBound"],
                "Style" -> If[effective[LabelStyle] === "ID", "ID", "Dimension"]|>]];
    If[FailureQ[labelData], Return[labelData]];
    header = If[AssociationQ[data], displayHeader[data],
        <|"Source" -> <|"StateID" -> Missing["NotBound"], "GeneratorIdentity" -> Missing["NotBound"]|>, "ObservedAt" -> DateString["ISODateTime"],
            "Group" -> <|"Name" -> "unbound representation", "Order" -> Missing["NotBound"], "Generators" -> (#["Name"] & /@ set["Columns"]),
                "Assignment" -> Missing["NotAssigned"], "IrrepCount" -> Missing["NotBound"]|>|>];
    makeDisplayDocument["Representation", Join[header, <|"Dimension" -> shape["Dimension"], "MatrixSet" -> displayMatrixSet[set],
        "Matrices" -> matrices, "Arithmetic" -> shape["Arithmetic"], "Precision" -> shape["Precision"], "Validation" -> validation,
        "LabelData" -> labelData,
        (* the Validation block is shown on request, or when the matrices are not the group's own stored variant (U4) *)
        "Columns" -> <|"Status" -> Switch[effective[ShowStatus], True, True, False, False, _, validation["Status"] =!= "Stored variant" || shape["Arithmetic"] === "Numerical" ||
            Lookup[validation, "VerificationStatus", "Exact"] =!= "Exact"]|>,
        "IrrepNames" -> If[AssociationQ[data] && StringQ[labelData["IrrepID"]],
            irrepPresentation[data, {labelData["IrrepID"]}, <|labelData["IrrepID"] -> labelData|>, <||>], <||>],
        "Label" -> If[labelData["Style"] === "TPhases", <|"Kind" -> "IrrepLabel", "Dimension" -> labelData["Dimension"], "Phases" -> labelData["TPhases"]|>,
            If[labelData["Style"] === "ID" && StringQ[labelData["IrrepID"]], textNode[labelData["IrrepID"]],
                <|"Kind" -> "IrrepLabel", "Dimension" -> labelData["Dimension"], "Phases" -> None|>]]|>], effective]
];

Options[GroupSummary] = {Basis -> Automatic, ShowIDs -> False, ShowStatus -> Automatic, ScalarNotation -> "Standard", NotationStyle -> "Standard",
    OneByOneMatrix -> "Scalar", DefineOmega -> True, Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20};

(*
    Summary: Snapshot a group's identity, generators, assignment and data availability for display.
    Status: Alpha.
    Parameters: g — live Group.
    Options/defaults: Basis -> Automatic (report each irrep's actual representation status) or a basis to
        compare with; presentation defaults.
    Returns: DisplayDocument["GroupSummary", data]: name, order, catalogue ID (or unavailable), recorded
        generators, the modular assignment (its identity only with ShowIDs -> True), every AvailableData status (subgroup
        queries included), per-irrep representation status, and the GAP cache availability observed now
        (NotStored, Missing, Present (compatibility unchecked), Incompatible or Unreadable with a reason).
    Effects: Read-only: no GAP launch or restore, no cache index write or last-use update, no group change.
    Failures: UnknownGroup; InvalidOption.
    Example: DisplayData[GroupSummary[g]]["GAPCache"]["State"] is "NotStored" for StoreGAPState -> False.
    Remarks: Missing, partial, complete and computed-empty data stay distinct; a general group is not called
        modular.
    See also: RepresentationTable; CharacterTableView.
*)
GroupSummary[group_Group, options : OptionsPattern[]] := Module[{effective, data, ids},
    effective = resolveOperationOptions[GroupSummary, "GroupSummary", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    ids = Lookup[data, "IrrepOrder", {}];
    makeDisplayDocument["GroupSummary", Join[displayHeader[data], <|
        "AvailableData" -> data["AvailableData"],
        "Representations" -> Association[Map[# -> Join[<|"Dimension" -> data["CharacterData"]["Degrees"][[First[FirstPosition[data["CharacterData"]["IrrepIDs"], #]]]]|>,
            KeyTake[representationRowStatus[Lookup[data["Representations"], #, Missing["NotComputed"]], effective[Basis], groupVerificationStatus[data]],
                {"Status", "ActiveVariant", "Tier", "Arithmetic", "VerificationStatus", "BasisProperties", "BasisComparison"}]] &, ids]],
        "RequestedBasis" -> effective[Basis], "GAPCache" -> gapCacheAvailability[data],
        "Columns" -> <|"IDs" -> TrueQ[effective[ShowIDs]], "Status" -> True|>|>], effective]
];
GroupSummary[___] := makeFailure["InvalidInput", "GroupSummary expects a live group and options."];

True
