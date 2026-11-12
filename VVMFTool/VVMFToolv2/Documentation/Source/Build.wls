(* Generate native authoring notebooks from the maintained API content.
   The source strings below are repository-owned documentation, not imported user data.
   No example code is evaluated by generation. Integrated Documentation Center builds
   can use DocumentationTools/PacletTools when a paclet is packaged. *)
docRoot = DirectoryName[DirectoryName[$InputFileName]];
packageRoot = DirectoryName[docRoot];
If[Get[FileNameJoin[{packageRoot,"Kernel","init.m"}]] =!= True, Quit[2]];
(* One page per public symbol, authored per stage in Source/Stage<n>.json. *)
pages = Join @@ (Import[#,"RawJSON"]& /@ Sort[FileNames["Stage*.json",FileNameJoin[{docRoot,"Source"}]]]);
referenceDirectory = FileNameJoin[{docRoot,"English","ReferencePages","Symbols"}];
If[!DirectoryQ[referenceDirectory],CreateDirectory[referenceDirectory,CreateIntermediateDirectories->True]];
(* Convert trusted authored code to display boxes without executing it. *)
codeBoxes[text_String] := ToExpression[text, InputForm, HoldComplete] /.
    HoldComplete[expression_] :> ToBoxes[Defer[expression], StandardForm];
(* Local native authoring links work before a Documentation Center paclet is installed. *)
symbolLink[name_String] := ButtonBox[name, BaseStyle->"Hyperlink", ButtonData->{name<>".nb",None}];
Do[
    data = pages[name];
    (* a package option may reuse a System symbol (Weights): resolve through the context path, never create a shadow,
       and take its usage from the page, not from the System symbol *)
    symbol = If[Names["VVMFTool`"<>name] =!= {}, ToExpression["VVMFTool`"<>name], ToExpression["System`"<>name]];
    usage = If[Context[Evaluate[symbol]] === "System`", First[data["Details"]], ToExpression["VVMFTool`"<>name<>"::usage"]];
    optionRows = Map[Function[rule, Module[{key=SymbolName[First[rule]],default,description},
        default = ToString[Last[rule],InputForm];
        If[key==="CacheDirectory",default="user-local GAPCache directory"];
        description = If[KeyExistsQ[pages,key], pages[key]["Details"][[2]],
            "See the method choices in this page's details."];
        {Cell[" ","TableRowIcon"],Cell[BoxData[ToBoxes[First[rule]]],"TableText"],Cell[default,"TableText"],Cell[description,"TableText"]}
    ]],Options[symbol]];
    cells = Join[{
        Cell[name,"ObjectName"], Cell[usage,"Usage"],
        Cell["Status: Alpha.","Notes"]},
        Cell[#,"Notes"]& /@ data["Details"],
        If[optionRows==={}, {}, {Cell["Options (shared configured settings can override these defaults):","Notes"],
            Cell[BoxData[GridBox[optionRows,GridBoxAlignment->{"Columns"->{{Left}}},GridBoxItemSize->{"Columns"->{Scaled[0.02],Scaled[0.30],Scaled[0.18],Scaled[0.50]}}]],"3ColumnTableMod"]}],
        {Cell["See Also","SeeAlsoSection"],Cell[TextData[Riffle[symbolLink /@ data["SeeAlso"],"  |  "]],"SeeAlso"],
         Cell["Examples Initialization","ExamplesInitializationSection"],
         Cell["Open this notebook in its repository location. GAP must be installed; LINS is required for its bounded search page. Evaluate the setup before the examples.","ExampleText"],
         Cell[BoxData[codeBoxes["Get[FileNameJoin[{Nest[DirectoryName, NotebookFileName[], 5], \"Kernel\", \"init.m\"}]];"]],"ExampleInitialization"],
         Cell["Basic Examples","PrimaryExamplesSection"],
         Cell[BoxData[codeBoxes[data["Example"]]],"Input",CellTags->"VerifiedExample"],
         Cell[BoxData[codeBoxes[data["Expected"]]],"Output"]},
        If[KeyExistsQ[data,"ErrorExample"],{
            Cell["Possible Issues","ExampleSection"],Cell["Invalid input returns a structured Failure. Check FailureQ before using the result.","ExampleText"],
            Cell[BoxData[codeBoxes[data["ErrorExample"]]],"Input",CellTags->"VerifiedErrorExample"],Cell[BoxData[codeBoxes["True"]],"Output"]},{}],
        {Cell["Related Guides","MoreAboutSection"],
         Cell[TextData[{ButtonBox["Constructing finite groups",BaseStyle->"Hyperlink",ButtonData->{"../../Tutorials/ConstructingFiniteGroups.nb",None}]}],"MoreAbout"],
         Cell[CellGroupData[{Cell["Metadata","MetadataSection"],Cell["Symbol","Categorization",CellLabel->"Entity Type"],
            Cell["VVMFTool","Categorization",CellLabel->"Paclet Name"],Cell["VVMFTool`","Categorization",CellLabel->"Context"],
            Cell["VVMFTool/ref/"<>name,"Categorization",CellLabel->"URI"]},Closed]]}];
    notebook = Notebook[cells,WindowTitle->name<>" — VVMFTool",WindowSize->{1000,850},
        TaggingRules-><|"Paclet"->"VVMFTool","Status"->"Alpha"|>,
        StyleDefinitions->FrontEnd`FileName[{"Wolfram"},"FunctionPageStylesExt.nb",CharacterEncoding->"UTF-8"]];
    Put[notebook,FileNameJoin[{referenceDirectory,name<>".nb"}]],
    {name,Keys[pages]}];
tutorial=Import[FileNameJoin[{docRoot,"Source","Tutorial.json"}],"RawJSON"];
tutorialDirectory=FileNameJoin[{docRoot,"English","Tutorials"}];
If[!DirectoryQ[tutorialDirectory],CreateDirectory[tutorialDirectory,CreateIntermediateDirectories->True]];
tutorialNotebook=Notebook[Join[{Cell["Constructing finite groups","Title"],
    Cell["Status: Alpha. Stage 1 provides character-only workflows; use ComputeRepresentations->False until stage 2 is implemented.","Text"]},
    Cell[#,"Text"]& /@ tutorial["Details"],{
    Cell["Load the package","Section"],
    Cell[BoxData[codeBoxes["Get[FileNameJoin[{Nest[DirectoryName, NotebookFileName[], 4], \"Kernel\", \"init.m\"}]];"]],"Input"],
    Cell["Build, save, restore and enrich","Section"],
    Cell[BoxData[codeBoxes[tutorial["Example"]]],"Input",CellTags->"VerifiedExample"],
    Cell[BoxData[codeBoxes[tutorial["Expected"]]],"Output"],
    Cell["General groups","Section"],
    Cell["BuildGroup does not assign S,T. Character and subgroup work does not require them. AssignModularGenerators checks supplied words and changes the same object; a failed pair leaves the previous assignment unchanged.","Text"],
    Cell[TextData[{ButtonBox["BuildGroup reference",BaseStyle->"Hyperlink",ButtonData->{"../ReferencePages/Symbols/BuildGroup.nb",None}]}],"Text"]}],
    WindowSize->{1000,850},WindowTitle->"Constructing finite groups — VVMFTool",StyleDefinitions->"Default.nb"];
Put[tutorialNotebook,FileNameJoin[{tutorialDirectory,"ConstructingFiniteGroups.nb"}]];
Print[Length[pages]," native reference notebooks generated."];
Quit[0];
