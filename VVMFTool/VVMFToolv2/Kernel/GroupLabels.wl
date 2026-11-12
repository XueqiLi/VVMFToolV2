(*
    :Title: User labels of irreps and classes; group names
    :Context: VVMFTool`Private`
    :Summary: The label grammar (irrep labels such as 1, 1', 2^{iv}, \hat{3}, \rep{2}'; class names such as 4C_{3}^{1}),
        label records with plain-text, notebook and LaTeX renderings from one source, and the group-state API that
        stores them: irrep labels, class labels and order, name, TeX title and catalogue label (uxUpdatePlan.md 1.4-1.5).
    :Responsibilities: parseIrrepLabel, irrepLabelRecordQ, parseClassLabel, classLabelRecordQ, labelPlainText,
        labelTeX, labelBoxes, irrepLabelsQ, classLabelsQ, presentationPatchQ; SetIrrepLabels, SetIrrepLabel,
        RemoveIrrepLabel, RemoveIrrepLabels, IrrepLabel, IrrepIndex, SetClassLabels, ReorderGroupClasses, SetGroupName,
        SetGroupTitle, SetCatalogueLabel.
    :Dependencies: GroupObject.wl (groupData, commitGroup); IrrepIndex.wl (resolveIrrepArguments, irrepIndexOf).
    :See Also: VVMFArch/uxUpdate.md U5, U10; VVMFArch/uxUpdatePlan.md 1.4-1.5.
*)

(* -------------------------------------------------------------------------
   Grammar
   ------------------------------------------------------------------------- *)

$LabelAccents = <|"hat" -> "\\hat", "bar" -> "\\bar", "tilde" -> "\\tilde"|>;

(*
    Summary: Parse the text of a script (the part after ^ or _): a braced group or a run of letters and digits.
    Parameters: chars — remaining characters.
    Options/defaults: None.
    Returns: {script string, remaining characters}, or $Failed.
    Effects: Pure.
    Failures: None ($Failed for an empty or unbalanced script).
    Example: labelScript[Characters["{iv}'"]] is {"iv", {"'"}}.
    See also: parseIrrepLabel.
*)
labelScript[chars_List] := Module[{depth = 0, i, body},
    Which[
        chars === {}, $Failed,
        First[chars] === "{",
            For[i = 1, i <= Length[chars], i++,
                Switch[chars[[i]], "{", depth++, "}", depth--];
                If[depth === 0, Break[]]];
            If[i > Length[chars] || i === 2, $Failed,
                body = StringJoin[chars[[2 ;; i - 1]]];
                If[StringMatchQ[body, RegularExpression["[A-Za-z0-9,]+"]], {body, Drop[chars, i]}, $Failed]],
        True, With[{run = TakeWhile[chars, LetterQ[#] || DigitQ[#] &]},
            If[run === {}, $Failed, {StringJoin[run], Drop[chars, Length[run]]}]]]];

(*
    Summary: Parse an irrep label into a label record.
    Parameters: text — label text: a base (letters and digits, e.g. 1, 3, 2a), optionally wrapped as \rep{base} and/or
        in an accent \hat{...}, \bar{...}, \tilde{...} (also \hat 3), followed in any order by primes ', a superscript
        ^{...} or ^x and a subscript _{...} or _x, each at most once.
    Options/defaults: None.
    Returns: <|"Base", "Primes", "Superscript", "Subscript", "Accent"|> (None for absent parts), or Failure.
    Effects: Pure.
    Failures: InvalidLabel (with the grammar).
    Example: parseIrrepLabel["\\rep{2}^{iv}"] is <|"Base" -> "2", "Primes" -> 0, "Superscript" -> "iv",
        "Subscript" -> None, "Accent" -> None|>; parseIrrepLabel["1''"]["Primes"] is 2.
    Remarks: No free TeX is stored: one record renders as plain text, notebook boxes and LaTeX (uxUpdatePlan.md 1.5).
        All 48 label forms of the VVMFUse display files parse.
    See also: labelPlainText; labelTeX; labelBoxes.
*)
parseIrrepLabel[text_String] := Catch[Module[{s = StringTrim[text], accent = None, base, chars, primes = 0, sup = None, sub = None, fail, r},
    fail[] := Throw[makeFailure["InvalidLabel", "An irrep label is a base (letters and digits) with optional \\rep{...}, an accent \\hat, \\bar or \\tilde, primes ', a superscript ^{...} and a subscript _{...}, for example 1, 2'', 2^{iv}, 3_a, \\hat{3}, \\rep{2}'.", <|"Label" -> text|>], "label"];
    (* accent and \rep wrappers, in either nesting *)
    Do[Which[
        (r = StringCases[s, RegularExpression["^\\\\(hat|bar|tilde)\\s*\\{(.*?)\\}(.*)$"] :> {"$1", "$2", "$3"}]) =!= {},
            If[accent =!= None, fail[]]; accent = r[[1, 1]]; s = r[[1, 2]] <> r[[1, 3]],
        (r = StringCases[s, RegularExpression["^\\\\(hat|bar|tilde)\\s+([A-Za-z0-9]+)(.*)$"] :> {"$1", "$2", "$3"}]) =!= {},
            If[accent =!= None, fail[]]; accent = r[[1, 1]]; s = r[[1, 2]] <> r[[1, 3]],
        (r = StringCases[s, RegularExpression["^\\\\rep\\s*\\{(.*?)\\}(.*)$"] :> {"$1", "$2"}]) =!= {},
            s = r[[1, 1]] <> r[[1, 2]],
        True, Break[]], {3}];
    base = StringCases[s, RegularExpression["^[A-Za-z0-9]+"]];
    If[base === {}, fail[]]; base = First[base];
    chars = Characters[StringDrop[s, StringLength[base]]];
    While[chars =!= {},
        Switch[First[chars],
            "'", primes++; chars = Rest[chars],
            "\[Prime]", primes++; chars = Rest[chars],
            "^", If[sup =!= None, fail[]]; r = labelScript[Rest[chars]]; If[r === $Failed, fail[]]; {sup, chars} = r,
            "_", If[sub =!= None, fail[]]; r = labelScript[Rest[chars]]; If[r === $Failed, fail[]]; {sub, chars} = r,
            " ", chars = Rest[chars],
            _, fail[]]];
    <|"Base" -> base, "Primes" -> primes, "Superscript" -> sup, "Subscript" -> sub, "Accent" -> accent|>
], "label"];
parseIrrepLabel[record_Association] /; irrepLabelRecordQ[record] := record;
parseIrrepLabel[___] := makeFailure["InvalidLabel", "An irrep label is a string such as 1, 2'', 2^{iv} or \\hat{3}."];

(*
    Summary: Whether a value is an irrep label record.
    Parameters: r — any expression.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: irrepLabelRecordQ[parseIrrepLabel["1'"]] is True.
    See also: parseIrrepLabel.
*)
irrepLabelRecordQ[r_] := AssociationQ[r] && Sort[Keys[r]] === {"Accent", "Base", "Primes", "Subscript", "Superscript"} &&
    StringQ[r["Base"]] && StringMatchQ[r["Base"], RegularExpression["[A-Za-z0-9]+"]] && IntegerQ[r["Primes"]] && r["Primes"] >= 0 &&
    (r["Superscript"] === None || StringQ[r["Superscript"]]) && (r["Subscript"] === None || StringQ[r["Subscript"]]) &&
    (r["Accent"] === None || KeyExistsQ[$LabelAccents, r["Accent"]]);

(*
    Summary: Parse a class name into a class label record.
    Parameters: text — optional class size digits, a base letter run, a subscript _{...} and a superscript ^{...}
        (for example 4C_{3}^{1}, 1C_{1}, 6C_{4}).
    Options/defaults: None.
    Returns: <|"Size", "Base", "Subscript", "Superscript"|> (None for absent parts), or Failure.
    Effects: Pure.
    Failures: InvalidLabel.
    Example: parseClassLabel["4C_{3}^{1}"] is <|"Size" -> "4", "Base" -> "C", "Subscript" -> "3", "Superscript" -> "1"|>.
    See also: classLabelRecordQ.
*)
parseClassLabel[text_String] := Catch[Module[{s = StringTrim[text], size, base, chars, sup = None, sub = None, r, fail},
    fail[] := Throw[makeFailure["InvalidLabel", "A class name is an optional class size, a base and optional _{...} and ^{...}, for example 4C_{3}^{1}.", <|"Label" -> text|>], "label"];
    size = StringCases[s, RegularExpression["^[0-9]+"]]; size = If[size === {}, None, First[size]];
    s = If[size === None, s, StringDrop[s, StringLength[size]]];
    base = StringCases[s, RegularExpression["^[A-Za-z]+"]]; If[base === {}, fail[]]; base = First[base];
    chars = Characters[StringDrop[s, StringLength[base]]];
    While[chars =!= {},
        Switch[First[chars],
            "^", If[sup =!= None, fail[]]; r = labelScript[Rest[chars]]; If[r === $Failed, fail[]]; {sup, chars} = r,
            "_", If[sub =!= None, fail[]]; r = labelScript[Rest[chars]]; If[r === $Failed, fail[]]; {sub, chars} = r,
            _, fail[]]];
    <|"Size" -> size, "Base" -> base, "Subscript" -> sub, "Superscript" -> sup|>
], "label"];
parseClassLabel[record_Association] /; classLabelRecordQ[record] := record;
parseClassLabel[___] := makeFailure["InvalidLabel", "A class name is a string such as 4C_{3}^{1}."];
classLabelRecordQ[r_] := AssociationQ[r] && Sort[Keys[r]] === {"Base", "Size", "Subscript", "Superscript"} && StringQ[r["Base"]] &&
    AllTrue[Lookup[r, {"Size", "Subscript", "Superscript"}], # === None || StringQ[#] &];

(* -------------------------------------------------------------------------
   Rendering (one record, three forms)
   ------------------------------------------------------------------------- *)

(*
    Summary: The plain-text, LaTeX and notebook forms of an irrep or class label record.
    Parameters: r — irrep or class label record; style — "Standard" (bold \mathbf base) or "Paper" (\rep{...}).
    Options/defaults: style "Standard".
    Returns: labelPlainText: string (1', 2^iv, 3_a, \hat{3}', 4C_3^1); labelTeX: TeX string; labelBoxes: a display
        expression (bold base, primes as \[Prime], Subscript/Superscript, OverHat/OverBar/OverTilde).
    Effects: Pure.
    Failures: None.
    Example: labelTeX[parseIrrepLabel["2^{iv}"]] is "\\mathbf{2}^{iv}"; labelPlainText[parseIrrepLabel["2''"]] is "2''".
    See also: parseIrrepLabel; parseClassLabel.
*)
labelPlainText[r_?irrepLabelRecordQ] := Module[{core = r["Base"]},
    If[r["Accent"] =!= None, core = $LabelAccents[r["Accent"]] <> "{" <> core <> "}"];
    core <> StringRepeat["'", r["Primes"]] <> If[r["Superscript"] === None, "", "^" <> plainScript[r["Superscript"]]] <>
        If[r["Subscript"] === None, "", "_" <> plainScript[r["Subscript"]]]];
labelPlainText[r_?classLabelRecordQ] := Replace[r["Size"], None -> ""] <> r["Base"] <>
    If[r["Subscript"] === None, "", "_" <> plainScript[r["Subscript"]]] <> If[r["Superscript"] === None, "", "^" <> plainScript[r["Superscript"]]];
plainScript[s_String] := If[StringLength[s] === 1 || StringMatchQ[s, RegularExpression["[A-Za-z]+|[0-9]+"]], s, "{" <> s <> "}"];

labelTeX[r_?irrepLabelRecordQ, style_String : "Standard"] := Module[{core},
    core = If[style === "Paper", "\\rep{" <> r["Base"] <> "}", "\\mathbf{" <> r["Base"] <> "}"];
    If[r["Accent"] =!= None, core = $LabelAccents[r["Accent"]] <> "{" <> core <> "}"];
    core <> StringRepeat["'", r["Primes"]] <> If[r["Superscript"] === None, "", "^{" <> r["Superscript"] <> "}"] <>
        If[r["Subscript"] === None, "", "_{" <> r["Subscript"] <> "}"]];
labelTeX[r_?classLabelRecordQ, ___] := Replace[r["Size"], None -> ""] <> r["Base"] <>
    If[r["Subscript"] === None, "", "_{" <> r["Subscript"] <> "}"] <> If[r["Superscript"] === None, "", "^{" <> r["Superscript"] <> "}"];

labelBoxes[r_?irrepLabelRecordQ] := Module[{core = Style[r["Base"], Bold], sup},
    core = Switch[r["Accent"], "hat", OverHat[core], "bar", OverBar[core], "tilde", OverTilde[core], _, core];
    sup = StringRepeat["\[Prime]", r["Primes"]] <> Replace[r["Superscript"], None -> ""];
    Which[
        sup === "" && r["Subscript"] === None, core,
        r["Subscript"] === None, Superscript[core, sup],
        sup === "", Subscript[core, r["Subscript"]],
        True, Subsuperscript[core, r["Subscript"], sup]]];
labelBoxes[r_?classLabelRecordQ] := Row[{Replace[r["Size"], None -> ""], Which[
    r["Subscript"] === None && r["Superscript"] === None, r["Base"],
    r["Superscript"] === None, Subscript[r["Base"], r["Subscript"]],
    r["Subscript"] === None, Superscript[r["Base"], r["Superscript"]],
    True, Subsuperscript[r["Base"], r["Subscript"], r["Superscript"]]]}];

(* -------------------------------------------------------------------------
   Group state checks (used by commitGroup)
   ------------------------------------------------------------------------- *)

(*
    Summary: Whether the presentation fields of a group state are valid.
    Parameters: state — candidate registry state.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: presentationPatchQ[groupData[g]] is True for every accepted group.
    Remarks: IrrepLabels: irrep IDs -> irrep label records; ClassLabels: class IDs -> <|"Name" -> class label record,
        "Representative" -> word string or None|>; ClassOrder: a permutation of the class IDs; CatalogueLabel and
        TitleTeX: None or a string; RegistrationIndex: a positive integer.
    See also: commitGroup.
*)
presentationPatchQ[state_Association] := With[{characters = state["CharacterData"]},
    AssociationQ[state["IrrepLabels"]] && SubsetQ[characters["IrrepIDs"], Keys[state["IrrepLabels"]]] &&
        AllTrue[Values[state["IrrepLabels"]], irrepLabelRecordQ] &&
    AssociationQ[state["ClassLabels"]] && SubsetQ[characters["ClassIDs"], Keys[state["ClassLabels"]]] &&
        AllTrue[Values[state["ClassLabels"]], AssociationQ[#] && Sort[Keys[#]] === {"Name", "Representative"} &&
            classLabelRecordQ[#["Name"]] && (#["Representative"] === None || StringQ[#["Representative"]]) &] &&
    ListQ[state["ClassOrder"]] && DuplicateFreeQ[state["ClassOrder"]] && Sort[state["ClassOrder"]] === Sort[characters["ClassIDs"]] &&
    (state["CatalogueLabel"] === None || StringQ[state["CatalogueLabel"]]) && (state["TitleTeX"] === None || StringQ[state["TitleTeX"]]) &&
    IntegerQ[state["RegistrationIndex"]] && state["RegistrationIndex"] > 0 && (state["LibrarySource"] === None || StringQ[state["LibrarySource"]])];

(* -------------------------------------------------------------------------
   Public API
   ------------------------------------------------------------------------- *)

Options[SetIrrepLabels] = Options[SetIrrepLabel] = {AllowDuplicates -> False};

(*
    Summary: Add, edit and remove user labels of irreps, and read them.
    Status: Alpha.
    Signatures: SetIrrepLabels[g, labels]; SetIrrepLabel[g, irrep, label]; RemoveIrrepLabel[g, irrep];
        RemoveIrrepLabels[g]; IrrepLabel[g, irrep]; IrrepIndex[g, label | id].
    Parameters: g — live Group; labels — a list in irrep order (None for no label) or an association irrep -> label;
        irrep — index in g["IrrepOrder"] or irrep ID; label — label text (grammar of parseIrrepLabel) or record.
    Options/defaults: AllowDuplicates -> False (two irreps with the same label are refused).
    Returns: SetIrrepLabels/SetIrrepLabel/RemoveIrrepLabel/RemoveIrrepLabels: g. IrrepLabel: the plain text of the label,
        or Missing["NoLabel"]. IrrepIndex: the index of the irrep with that user label (or ID).
    Effects: Change the group's stored labels (presentation data; no mathematical change, no new generation).
    Failures: InvalidLabel; InvalidIrrep; InvalidIrrepID; DuplicateIrrepLabel; UnknownIrrepLabel;
        AmbiguousIrrepLabel; state conflicts.
    Example: SetIrrepLabels[g, {"1", "1'", "1''", "2", "2'", "2''", "3"}]; IrrepLabel[g, 2] is "1'"; IrrepIndex[g, "2'"] is 5.
    Remarks: SetIrrepLabels with a list replaces all labels; with an association it adds or replaces the named ones.
        Labels are saved with the group (SaveGroupData) and shown by every view (uxUpdatePlan.md 1.4).
    See also: SetClassLabels; IrrepLabels.
*)
SetIrrepLabels[group_Group, labels : (_List | _Association), options : OptionsPattern[]] := Module[
    {effective, data, order, pairs, records, combined},
    effective = resolveOperationOptions[SetIrrepLabels, "SetIrrepLabels", {options}]; If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    order = data["IrrepOrder"];
    pairs = If[ListQ[labels],
        If[Length[labels] =!= Length[order], Return[makeFailure["InvalidInput", "A label list must have one entry (or None) per irrep, in irrep order.",
            <|"Expected" -> Length[order], "Given" -> Length[labels]|>]]];
        Select[Transpose[{order, labels}], Last[#] =!= None &],
        With[{keys = resolveIrrepArguments[group, Keys[labels]]}, If[FailureQ[keys], Return[keys]];
            If[!SubsetQ[order, keys], Return[makeFailure["InvalidIrrepID", "A label names an irrep that is not in this group.", <|"IrrepIDs" -> Complement[keys, order]|>]]];
            Transpose[{keys, Values[labels]}]]];
    records = Map[{First[#], parseIrrepLabel[Last[#]]} &, pairs];
    If[AnyTrue[records[[All, 2]], FailureQ], Return[FirstCase[records[[All, 2]], _Failure]]];
    combined = If[ListQ[labels], Association[Rule @@@ records], Join[data["IrrepLabels"], Association[Rule @@@ records]]];
    commitIrrepLabels[group, data, combined, effective[AllowDuplicates]]
];
SetIrrepLabels[___] := makeFailure["InvalidInput", "SetIrrepLabels expects a live group and a list (irrep order) or association of labels."];
SetIrrepLabel[group_Group, irrep : (_Integer | _String), label_, options : OptionsPattern[]] := SetIrrepLabels[group, <|irrep -> label|>, options];
SetIrrepLabel[___] := makeFailure["InvalidInput", "SetIrrepLabel expects a live group, an irrep (index or ID) and a label."];
RemoveIrrepLabel[group_Group, irrep : (_Integer | _String)] := Module[{data = groupData[group], id},
    If[FailureQ[data], Return[data]];
    id = resolveIrrepArguments[group, irrep]; If[FailureQ[id], Return[id]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id], Return[makeFailure["InvalidIrrepID", "The irrep ID does not belong to this group.", <|"ID" -> id|>]]];
    commitIrrepLabels[group, data, KeyDrop[data["IrrepLabels"], id], True]];
RemoveIrrepLabel[___] := makeFailure["InvalidInput", "RemoveIrrepLabel expects a live group and an irrep (index or ID)."];
RemoveIrrepLabels[group_Group] := With[{data = groupData[group]}, If[FailureQ[data], data, commitIrrepLabels[group, data, <||>, True]]];
RemoveIrrepLabels[___] := makeFailure["InvalidInput", "RemoveIrrepLabels expects a live group."];

(*
    Summary: Commit a complete irrep-label association to a group.
    Parameters: group; data — current group data; labels — irrep ID -> label record; allowDuplicates — Boolean.
    Options/defaults: None.
    Returns: group, or Failure.
    Effects: commitGroup.
    Failures: DuplicateIrrepLabel; state conflicts.
    Example: commitIrrepLabels[g, groupData[g], <||>, True] removes every label.
    See also: SetIrrepLabels.
*)
commitIrrepLabels[group_Group, data_Association, labels_Association, allowDuplicates_] := Module[{texts = labelPlainText /@ labels, repeated},
    repeated = Select[GatherBy[Keys[texts], texts], Length[#] > 1 &];
    If[!TrueQ[allowDuplicates] && repeated =!= {},
        Return[makeFailure["DuplicateIrrepLabel", "Two irreps would have the same label; use AllowDuplicates -> True to allow it.",
            <|"Labels" -> Map[texts[First[#]] -> Map[irrepIndexOf[group, #] &, #] &, repeated]|>]]];
    commitGroup[group, data["Revision"], <|"IrrepLabels" -> KeySortBy[labels, Position[data["IrrepOrder"], #] &]|>]];

(* IrrepLabel[g, irrep, form]: "Text" (default) the plain text accepted by SetIrrepLabels; "Display" an expression that
   shows the label typeset as in the views (bold base, primes and super/subscripts, accents) and evaluates to the plain
   text through Interpretation; "TeX" the LaTeX of ToLaTeX. *)
IrrepLabel[group_Group, irrep : (_Integer | _String), form : ("Text" | "Display" | "TeX") : "Text"] := Module[{data = groupData[group], id, record},
    If[FailureQ[data], Return[data]];
    id = resolveIrrepArguments[group, irrep]; If[FailureQ[id], Return[id]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id], Return[makeFailure["InvalidIrrepID", "The irrep ID does not belong to this group.", <|"ID" -> id|>]]];
    If[!KeyExistsQ[data["IrrepLabels"], id], Return[Missing["NoLabel"]]];
    record = data["IrrepLabels"][id];
    Switch[form, "Text", labelPlainText[record], "TeX", labelTeX[record],
        "Display", With[{text = labelPlainText[record]}, Interpretation[Evaluate[labelBoxes[record]], text]]]];
IrrepLabel[___] := makeFailure["InvalidInput", "IrrepLabel expects a live group, an irrep (index or ID) and optionally the form \"Text\", \"Display\" or \"TeX\"."];

(*
    Summary: The irrep index of a user label (or of an irrep ID).
    Parameters: c — Group or RepresentationContext; label — label text in any spelling of the grammar ("2'", "\\rep{2}'")
        or an irrep ID.
    Options/defaults: None.
    Returns: Positive integer, or Failure.
    Effects: As presentationData.
    Failures: UnknownIrrepLabel; AmbiguousIrrepLabel (several irreps carry it; the indices are listed); InvalidLabel.
    Example: IrrepIndex[g, "\\rep{3}"] is 7 for T' labelled as in the paper.
    Remarks: Labels are not accepted as irrep input elsewhere (decision D4); IrrepIndex converts them.
    See also: IrrepLabel; SetIrrepLabels.
*)
IrrepIndex[c : (_Group | _RepresentationContext), label_String] := Module[{p = presentationData[c], record, matches},
    If[FailureQ[p], Return[p]];
    If[MemberQ[p["CharacterData"]["IrrepIDs"], label], Return[irrepIndexOf[c, label]]];
    record = parseIrrepLabel[label]; If[FailureQ[record], Return[record]];
    matches = Select[p["IrrepOrder"], Lookup[p["IrrepLabels"], #, None] === record &];
    Switch[Length[matches],
        0, makeFailure["UnknownIrrepLabel", "No irrep carries this label.", <|"Label" -> label|>],
        1, First[FirstPosition[p["IrrepOrder"], First[matches], {0}, {1}]],
        _, makeFailure["AmbiguousIrrepLabel", "Several irreps carry this label.", <|"Label" -> label,
            "Indices" -> Map[First[FirstPosition[p["IrrepOrder"], #, {0}, {1}]] &, matches]|>]]];
IrrepIndex[___] := makeFailure["InvalidInput", "IrrepIndex expects a Group or RepresentationContext and a label or irrep ID."];

(*
    Summary: Class names and representatives, and the class order.
    Status: Alpha.
    Signatures: SetClassLabels[g, names]; ReorderGroupClasses[g, order].
    Parameters: g — live Group; names — a list in the current class order (None for no name; an entry may be
        {name, representative word}) or an association class (index in g["ClassOrder"] or class ID) -> name or
        {name, representative}; order — a permutation of the class IDs or of 1..n (positions in g["ClassOrder"]).
    Options/defaults: None.
    Returns: g, or Failure.
    Effects: Change the group's stored class labels or order (presentation data only).
    Failures: InvalidLabel; InvalidClassOrder; InvalidInput; state conflicts.
    Example: SetClassLabels[g, {"1C_{1}", "1C_{2}", "4C_{3}^{1}", ...}].
    Remarks: CharacterTableView uses the stored class order and names by default (uxUpdatePlan.md 1.4).
    See also: SetIrrepLabels; CharacterTableView.
*)
SetClassLabels[group_Group, names : (_List | _Association)] := Module[{data = groupData[group], order, keys, values, records},
    If[FailureQ[data], Return[data]];
    order = data["ClassOrder"];
    {keys, values} = If[ListQ[names],
        If[Length[names] =!= Length[order], Return[makeFailure["InvalidInput", "A class-name list must have one entry (or None) per class, in class order."]]];
        With[{kept = Select[Transpose[{order, names}], Last[#] =!= None &]}, If[kept === {}, {{}, {}}, Transpose[kept]]],
        {Map[If[IntegerQ[#], If[1 <= # <= Length[order], order[[#]], Return[makeFailure["InvalidInput", "A class index is out of range."], Module]], #] &, Keys[names]], Values[names]}];
    If[!SubsetQ[order, keys], Return[makeFailure["InvalidInput", "A class name names an unknown class."]]];
    records = MapThread[Function[{id, v}, id -> With[{nm = parseClassLabel[If[ListQ[v], First[v], v]]},
        If[FailureQ[nm], Return[nm, Module], <|"Name" -> nm, "Representative" -> If[ListQ[v] && Length[v] === 2 && StringQ[Last[v]], Last[v], None]|>]]], {keys, values}];
    commitGroup[group, data["Revision"], <|"ClassLabels" -> If[ListQ[names], Association[records], Join[data["ClassLabels"], Association[records]]]|>]];
SetClassLabels[___] := makeFailure["InvalidInput", "SetClassLabels expects a live group and a list or association of class names."];
ReorderGroupClasses[group_Group, order_List] := Module[{data = groupData[group], ids},
    If[FailureQ[data], Return[data]];
    ids = Replace[order, k_Integer :> If[1 <= k <= Length[data["ClassOrder"]], data["ClassOrder"][[k]], k], {1}];
    If[!(DuplicateFreeQ[ids] && Sort[ids] === Sort[data["CharacterData"]["ClassIDs"]]),
        Return[makeFailure["InvalidClassOrder", "Expected a permutation of the group's classes.", <|"Order" -> order|>]]];
    commitGroup[group, data["Revision"], <|"ClassOrder" -> ids|>]];
ReorderGroupClasses[___] := makeFailure["InvalidInput", "ReorderGroupClasses expects a live group and a permutation of its classes."];

(*
    Summary: Set the display name, TeX title and catalogue label of a group.
    Status: Alpha.
    Signatures: SetGroupName[g, name]; SetGroupTitle[g, tex]; SetCatalogueLabel[g, label].
    Parameters: g — live Group; name — string; tex — TeX string or None; label — a label of the modular catalogue
        (Data/ModularGroups.json), a label "order-number" with an optional roman suffix (e.g. "78-1I") whose order and
        number are the group's GAP ID, or None.
    Options/defaults: None.
    Returns: g, or Failure.
    Effects: Change presentation data only.
    Failures: InvalidGroupName; InvalidInput; UnknownCatalogueLabel; state conflicts.
    Example: SetCatalogueLabel[g, "24-3I"] makes g display as Group[24-3I].
    See also: LoadGroup; BuildModularGroup.
*)
SetGroupName[group_Group, name_String] := With[{data = groupData[group]}, If[FailureQ[data], data, commitGroup[group, data["Revision"], <|"Name" -> name|>]]];
SetGroupName[___] := makeFailure["InvalidGroupName", "SetGroupName expects a live group and a string."];
SetGroupTitle[group_Group, tex : (_String | None)] := With[{data = groupData[group]}, If[FailureQ[data], data, commitGroup[group, data["Revision"], <|"TitleTeX" -> tex|>]]];
SetGroupTitle[___] := makeFailure["InvalidInput", "SetGroupTitle expects a live group and a TeX string or None."];
SetCatalogueLabel[group_Group, label : (_String | None)] := Module[{data = groupData[group]},
    If[FailureQ[data], Return[data]];
    If[StringQ[label] && !catalogueLabelForQ[label, data],
        Return[makeFailure["UnknownCatalogueLabel", "The label is neither in the modular catalogue nor of the form order-number (with an optional roman suffix such as I) for this group's GAP ID.", <|"Label" -> label|>]]];
    commitGroup[group, data["Revision"], <|"CatalogueLabel" -> label|>]];
(* A label of the modular catalogue, or one of the paper's form "o-n" + roman suffix whose {o, n} is the group's GAP ID
   (the library's groups beyond Data/ModularGroups.json, e.g. 78-1I; review F2). *)
catalogueLabelForQ[label_String, data_Association] := With[{parts = StringCases[label, RegularExpression["^([0-9]+)-([0-9]+)([IVX]*)$"] :> {"$1", "$2"}],
        id = Lookup[data, "CatalogueID", None]},
    (* every label names its GAP ID (catalogue labels too, review F17); a catalogue label is accepted for a group whose
       GAP ID is unknown *)
    If[MatchQ[id, {_Integer, _Integer}], parts =!= {} && ToExpression /@ First[parts] === id, KeyExistsQ[modularCatalogue[], label]]];
SetCatalogueLabel[___] := makeFailure["InvalidInput", "SetCatalogueLabel expects a live group and a catalogue label or None."];

(* -------------------------------------------------------------------------
   Catalogue and snapshots
   ------------------------------------------------------------------------- *)

(*
    Summary: The groups of the modular catalogue (Data/ModularGroups.json), read once per kernel.
    Parameters: None.
    Options/defaults: None.
    Returns: Association label -> catalogue record, or <||> when the catalogue is unavailable.
    Effects: Reads the package file once and memoizes it.
    Failures: None.
    Example: KeyExistsQ[modularCatalogue[], "24-3I"] is True.
    See also: ModularGroupSpecification; inferCatalogueLabel.
*)
modularCatalogue[] := modularCatalogue[] = With[{c = Quiet[Check[Import[FileNameJoin[{$PackageRoot, "Data", "ModularGroups.json"}], "RawJSON"], $Failed]]},
    If[AssociationQ[c] && AssociationQ[Lookup[c, "groups", None]], c["groups"], <||>]];

(*
    Summary: The catalogue label of a saved group that predates stored labels.
    Parameters: name — the snapshot's name; data — decoded group data.
    Options/defaults: None.
    Returns: name when it is a catalogue label and the group's construction is that entry's presentation, else None.
    Effects: Reads the catalogue.
    Failures: None.
    Example: a 24-3I snapshot saved by BuildModularGroup["24-3I"] gives "24-3I".
    See also: decodeGroupSnapshot.
*)
inferCatalogueLabel[name_String, data_Association] := Module[{spec, enc},
    If[!KeyExistsQ[modularCatalogue[], name], Return[None]];
    spec = ModularGroupSpecification[name]; If[FailureQ[spec], Return[None]];
    enc = encodeConstruction[spec];
    If[AssociationQ[enc] && AssociationQ[data["Construction"]] && Lookup[enc, "relators", 1] === Lookup[data["Construction"], "relators", 2] &&
        Lookup[enc, "names", 1] === Lookup[data["Construction"], "names", 2], name, None]];
inferCatalogueLabel[___] := None;

(*
    Summary: The presentation part of a group snapshot (schema 3), encoded and decoded.
    Parameters: accepted — group data; snapshot — saved snapshot association; data — decoded group data.
    Options/defaults: None.
    Returns: encodeSnapshotPresentation: association of the optional schema-3 keys that are present (irrepLabels,
        classLabels, classOrder, catalogueLabel, titleTeX; labels as their plain grammar text), possibly empty.
        decodeSnapshotPresentation: <|"IrrepLabels", "ClassLabels", "ClassOrder", "CatalogueLabel", "TitleTeX"|>, or Failure.
    Effects: Pure (the decoder reads the catalogue for older files).
    Failures: InvalidSnapshot (unparsable labels, foreign IDs, a class order that is not a permutation).
    Example: a group with no labels and the canonical class order encodes to <||> (saved as schema 2).
    Remarks: "Present" means non-empty labels, a class order different from the canonical one, or a label/title that is
        not None (uxUpdatePlan.md 1.4, review N9).
    See also: groupSnapshot; decodeGroupSnapshot.
*)
$SnapshotPresentationKeys = {"irrepLabels", "classLabels", "classOrder", "catalogueLabel", "titleTeX"};
encodeSnapshotPresentation[accepted_Association] := Join[
    If[accepted["IrrepLabels"] =!= <||>, <|"irrepLabels" -> Map[labelPlainText, accepted["IrrepLabels"]]|>, <||>],
    If[accepted["ClassLabels"] =!= <||>, <|"classLabels" -> Map[<|"name" -> labelPlainText[#["Name"]], "representative" -> Replace[#["Representative"], None -> Null]|> &, accepted["ClassLabels"]]|>, <||>],
    If[accepted["ClassOrder"] =!= accepted["CharacterData"]["ClassIDs"], <|"classOrder" -> accepted["ClassOrder"]|>, <||>],
    If[StringQ[accepted["CatalogueLabel"]], <|"catalogueLabel" -> accepted["CatalogueLabel"]|>, <||>],
    If[StringQ[accepted["TitleTeX"]], <|"titleTeX" -> accepted["TitleTeX"]|>, <||>]];
decodeSnapshotPresentation[snapshot_Association, data_Association] := Catch[Module[{fail, characters = data["CharacterData"], irrep, class, order},
    fail[] := Throw[makeFailure["InvalidSnapshot", "The saved labels or class order are malformed."], "presentation"];
    irrep = Lookup[snapshot, "irrepLabels", <||>];
    If[!AssociationQ[irrep] || !SubsetQ[characters["IrrepIDs"], Keys[irrep]] || !AllTrue[Values[irrep], StringQ], fail[]];
    irrep = Map[parseIrrepLabel, irrep]; If[AnyTrue[irrep, FailureQ], fail[]];
    class = Lookup[snapshot, "classLabels", <||>];
    If[!AssociationQ[class] || !SubsetQ[characters["ClassIDs"], Keys[class]] ||
        !AllTrue[Values[class], AssociationQ[#] && Sort[Keys[#]] === {"name", "representative"} && StringQ[#["name"]] && (#["representative"] === Null || StringQ[#["representative"]]) &], fail[]];
    class = Map[<|"Name" -> parseClassLabel[#["name"]], "Representative" -> Replace[#["representative"], Null -> None]|> &, class];
    If[AnyTrue[class, FailureQ[#["Name"]] &], fail[]];
    order = Lookup[snapshot, "classOrder", characters["ClassIDs"]];
    If[!ListQ[order] || !DuplicateFreeQ[order] || Sort[order] =!= Sort[characters["ClassIDs"]], fail[]];
    If[!MatchQ[Lookup[snapshot, "catalogueLabel", None], None | _String] || !MatchQ[Lookup[snapshot, "titleTeX", None], None | _String], fail[]];
    <|"IrrepLabels" -> irrep, "ClassLabels" -> class, "ClassOrder" -> order,
        "CatalogueLabel" -> If[KeyExistsQ[snapshot, "catalogueLabel"], snapshot["catalogueLabel"], inferCatalogueLabel[snapshot["name"], data]],
        "TitleTeX" -> Lookup[snapshot, "titleTeX", None]|>
], "presentation"];
