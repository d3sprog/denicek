module Denicek.App.Datnicek

open Denicek
open Denicek.Html
open Denicek.Doc
open Denicek.Demos

// --------------------------------------------------------------------------------------
// Helpers
// --------------------------------------------------------------------------------------

let withUniqueId s idOpt =
  match idOpt with 
  | Some id -> id
  | None -> s + "-" + hash(System.Guid.NewGuid()).ToString("x")

let (|Lookup|) args = 
  dict args

let (|Find|_|) k (dict:System.Collections.Generic.IDictionary<_, _>) = 
  if dict.ContainsKey k then Some dict.[k] else None

let (|Fail|) msg _ = 
  failwith $"Fail: {msg}"

// --------------------------------------------------------------------------------------
// Object model and completions
// --------------------------------------------------------------------------------------

let rec (|FormulaEvaluated|_|) nd = 
  match nd with 
  | Record("x-evaluated", Lookup(Find "result" nd & Find "formula" formula)) ->
      Some(nd, formula)
  | _ -> None

let rec (|FormulaGlobal|FormulaMember|FormulaPrimitive|) nd = 
  match nd with 
  | Reference(_, [Field "$datnicek"; Field glob]) -> 
      FormulaGlobal glob
  | Record("x-formula", args & Lookup(Find "inst" inst & 
        Find "op" (Reference(_, [Field "$datnicek"; Field ns; Field op] )))) ->
      let otherArgs = args |> OrdList.toList |> List.filter (fun (k, _) -> k <> "op" && k <> "inst")
      FormulaMember(ns, op, inst, otherArgs)
  | Primitive(p) ->
      FormulaPrimitive(p)
  | _ -> failwith $"FormulaGlobal|FormulaMember|FormulaPrimitive: Not a formula or missing op: {nd}"

type Member = 
  { Name : string 
    Arguments : (string * string) list
    Type : unit -> Type }

and Type =
  { Name : string
    Members : Member list }

type CompletionAction = 
  { ActionName : string 
    ActionEdits : EditKind list
    EditPath : Selectors option }

let stringObj = { Name = "string"; Members = [] }
let numberObj = { Name = "number"; Members = [] }
let rec chartObj = 
  { Name = "chart"
    Members = [
      { Name = "with title"; Arguments = [ "title", "string" ]; Type = fun () -> chartObj }
  ]}
let rec tableObj = 
  { Name = "table"
    Members = [
      { Name = "sum"; Arguments = []; Type = fun () -> tableObj }
  ]}


let globalDataObj = 
  { Name = "data"
    Members = [ 
      { Name = "load"; Arguments = [ "file", "string" ]; Type = fun () -> tableObj }
  ]}
let globalVisObj =
  { Name = "vis"
    Members = [ 
      { Name = "bar"; Arguments = [ "data", "table" ]; Type = fun () -> chartObj }
      { Name = "line"; Arguments = [ "data", "table" ]; Type = fun () -> chartObj }
  ]}
let globalMathObj =
  { Name = "math"
    Members = [ 
      { Name = "random"; Arguments = [ "min", "number"; "max", "number" ]; Type = fun () -> numberObj }
  ]}

let globals = [ globalDataObj; globalVisObj; globalMathObj ]
let globalsLookup = dict [ for t in globals -> t.Name, t ]
let types = globals @ [ tableObj; chartObj; stringObj; numberObj ]
let typesLookup = dict [ for t in types -> t.Name, t ]

let getFormulaType nd = 
  match nd with 
  | FormulaPrimitive(String _) -> "string"
  | FormulaPrimitive(Number _) -> "number"
  | FormulaGlobal(glob) -> glob
  | FormulaMember(ns, op, _, _) -> 
      let mems = typesLookup.[ns].Members
      let mem = mems |> List.find (fun mem -> mem.Name = op)
      mem.Type().Name

let getGlobalCompletions path fid lastfid = [
  for gt in globals do
    "use " + gt.Name, fun () -> 
      let ed = RecordAdd(path, fid, lastfid, None, ref [Field "$datnicek"; Field gt.Name])
      { ActionName = $"add formula to {id}"; ActionEdits = [ ed ]; EditPath = None }
  "add \"string\"", fun () ->      
    let ed = RecordAdd(path, fid, lastfid, None, Primitive(String ""))
    { ActionName = $"add string to {id}"; ActionEdits = [ ed ]; EditPath = None }
  "add number", fun () ->      
    let ed = RecordAdd(path, fid, lastfid, None, Primitive(Number 0))
    { ActionName = $"add number to {id}"; ActionEdits = [ ed ]; EditPath = None }
  ]

let rec getCompletions bindings path formula =
  let getArgumentCompletions remainingArgs = [ 
    for ra, ratyp in remainingArgs do 
      if ratyp = "string" then
        ra + " = \"string\"", fun () ->
          let ed = RecordAdd(path, ra, None, None, Primitive(String ""))
          { ActionName = "select completion"; ActionEdits = [ ed ]; EditPath = Some(path @ [Field ra]) }
      if ratyp = "number" then
        ra + " = number", fun () ->
          let ed = RecordAdd(path, ra, None, None, Primitive(Number 0))
          { ActionName = "select completion"; ActionEdits = [ ed ]; EditPath = Some(path @ [Field ra]) }
      for ref, formula in bindings do
        let fld = match List.last ref with Field f -> f | _ -> failwith "getArgumentCompletion: Path didn't end with field"
        if ratyp = getFormulaType formula && not (fld.StartsWith "unnamed-") then 
          ra + " = " + fld, fun () ->
            let ed = RecordAdd(path, ra, None, None, Reference(Absolute, ref))
            { ActionName = "select completion"; ActionEdits = [ ed ]; EditPath = None }
  ]
  let getTypeCompletions typ = [
    for mem in typ.Members -> mem.Name, fun () ->
      let eds = 
        [ WrapRecord(KeepReferences, "inst", "x-formula", path)
          RecordAdd(path, "op", None, None,
            ref [Field "$datnicek"; Field typ.Name; Field mem.Name]) ]
      { ActionName = "select completion"; ActionEdits = eds; EditPath = None }
  ]

  match formula with 
  | FormulaPrimitive(_) -> []
  | FormulaEvaluated(_, formula) -> getCompletions bindings path formula

  | FormulaMember(ns, op, _, args) -> 
      let mem = typesLookup.[ns].Members |> List.find (fun m -> m.Name = op)
      let knownArgs = set (List.map fst args)
      let remainingArgs = mem.Arguments |> List.filter (fst >> knownArgs.Contains >> not)
      if not (List.isEmpty remainingArgs) then 
        getArgumentCompletions remainingArgs
      else
        getTypeCompletions (mem.Type())

  | FormulaGlobal(glob) -> 
      let typ = globalsLookup.[glob]
      getTypeCompletions typ


let evaluateBuiltin op args = 
  //failwith $"op={op}; args={args}"
  Primitive(String "thing!")


// --------------------------------------------------------------------------------------
// Application state
// --------------------------------------------------------------------------------------

type State = 
  { 
    Edits : Edit list
    Document : Node
    Bindings : (Selectors * Node) list

    SelectedCell : string option
    DisplayMenuPath : string list option

    EditingValuePath : Selectors option
    EditingBindingPath : Selectors option
    ViewSource : bool
  }

type CellKind = 
  | TextCell
  | CodeCell
  | GridCell

type Event = 
  | ToggleViewSource 
  | UndoLastEdit
  | ToggleMenu of path:string list option
  | AddCell of CellKind * id:string option * pred:string option * succ:string option
  | SelectCell of string option
  | ApplyEdits of string * EditKind list
  | EditValue of Selectors option
  | EditBinding of Selectors option
  | Evaluate 

  
// --------------------------------------------------------------------------------------
// Document edits
// --------------------------------------------------------------------------------------

let getBindings doc = 
  match doc with 
  | Record(_, cells) ->
      cells |> OrdList.toList |> List.collect (fun (ck, cv) ->  
        match cv with 
        | Record(_, formulas) ->
            formulas |> OrdList.toList |> List.map (fun (fk, fv) -> 
              [Field ck; Field fk], fv)
        | _ -> failwith "getBindings: Expected record of formulas")
  | _ -> failwith "getBindings: Expected record of cells"

let updateDocument state = 
  let doc = Apply.applyHistory (rcd "notebook") state.Edits 
  { state with Document = doc; Bindings = getBindings doc }

let withEdits g state eds = 
  let eds = [ for ed in eds -> { Kind = ed; Dependencies = []; GroupLabel = g } ]
  { state with Edits = state.Edits @ eds } |> updateDocument

let withFullEdits g state eds = 
  let eds = [ for ed in eds -> { ed with GroupLabel = g } ]
  { state with Edits = state.Edits @ eds } |> updateDocument

// --------------------------------------------------------------------------------------
// Notebook cells
// --------------------------------------------------------------------------------------

let asCellKindName = function 
  | TextCell -> "text" | CodeCell -> "code" | GridCell -> "grid"

let ofCellKindName = function 
  | "text" -> TextCell | "code" -> CodeCell  | "grid" -> GridCell 
  | n -> failwith $"ofCellKindName: Invalid kind name {n}"

type Cell = 
  { Kind : CellKind 
    ID : string
    NextID : string option
    Node : Node }

let getNotebookCells nd = 
  match nd with 
  | Record("notebook", cells) ->
      let cells = cells |> OrdList.toList
      let nextids = match cells with _::cells -> (List.map (fst >> Some) cells) @ [None] | _ -> []
      (cells, nextids) ||> List.map2 (fun (id, nd) next -> 
        match nd with 
        | Record(typ, _) when typ.StartsWith("cell-") ->
            { Kind = ofCellKindName (typ.Substring(5))
              ID = id; NextID = next; Node = nd }
        | _ -> failwith "getNotebookCells: expected record cell")
  | _ -> failwith "getNotebookCells: expected document node"

let getCellFormulas nd = 
  match nd with 
  | Record("cell-code", formulas) ->
      formulas |> OrdList.toList
  | _ -> failwith "getCellFormulas: expected cell node"

// --------------------------------------------------------------------------------------
// Update operation
// --------------------------------------------------------------------------------------

let update state trigger evt = 
  match evt with 
  | UndoLastEdit -> { state with Edits = List.truncate (state.Edits.Length - 1) state.Edits } |> updateDocument
  | ToggleViewSource -> { state with ViewSource = not state.ViewSource }
  | SelectCell sel when state.SelectedCell = sel -> state
  | SelectCell sel -> { state with SelectedCell = sel }
  | ToggleMenu path -> { state with DisplayMenuPath = path }
  | EditValue path -> { state with EditingValuePath = path }      
  | EditBinding path -> { state with EditingBindingPath = path }      

  | AddCell(kind, id, pred, succ) ->
      let id = withUniqueId "cell" id
      [ RecordAdd([], id, pred, succ, rcd $"cell-{asCellKindName kind}") ]
      |> withEdits $"add cell {id}" state
  
  | ApplyEdits(lbl, eds) ->
      eds |> withEdits lbl state

  | Evaluate ->
      let eds = Eval.evaluateAll evaluateBuiltin state.Document
      eds |> withFullEdits "evaluate" state

// --------------------------------------------------------------------------------------
// Render source tree (from Webnicek)
// --------------------------------------------------------------------------------------

let (+?) s1 (b, s2) = if b then (s1 + " " + s2) else s1

let isPlainTextNode = function
  | Reference _ | Primitive _ | Primitive _ -> true | _ -> false

let getTag nd = 
  match nd with 
  | List(tag, _) | Record(tag, _) -> tag
  | Primitive(Number _) -> "x-prim-num"
  | Primitive(String _) -> "x-prim-str"
  | Reference _ -> "x-reference"

let renderReference state trigger (baseSel, ref) = 
  let absSel = resolveReference baseSel ref
  h?a [ 
    "href" => "javascript:;"
    "class" => "selector"
  ] [ 
    yield text (Format.formatReference ref)
  ]

let renderSourceTree state trigger =  
  let rec loop path idAttrs nd = 
    h?div [
      "class" => 
        "treenode" 
        +? (isPlainTextNode nd, "inline") 
    ] [
      h?div ["class" => "treetag" ] [
        yield text "<"
        yield h?span [] [ text (getTag nd) ]
        for k, v in idAttrs do  
          yield text " "
          yield h?span [ "class" => "attrname" ] [ text k ]
          yield text "=\""
          yield h?span [ "class" => "attrvalue" ] [ text v ]
          yield text "\""
        yield text ">"
      ]
      h?div ["class" => "treebody" ] [
        match nd with
        | List(_, nds) -> 
            for i, a in nds do
              yield loop (path @ [Index i]) ["index", string i] a
        | Record(_, nds) -> 
            for f, a in nds do
              yield loop (path @ [Field f]) ["id", f] a
        | Reference(kind, sel) -> yield renderReference state trigger (path, (kind, sel))
        | Primitive(String s) -> yield text s
        | Primitive(Number n) -> yield text (string n)              
      ]
      h?div ["class" => "treetag" ] [
        text "</"
        h?span [] [ text (getTag nd) ]
        text ">"
      ]
    ]
  loop

// --------------------------------------------------------------------------------------
// Render datnicek
// --------------------------------------------------------------------------------------

open Browser.Types

let renderResult nd = 
  match nd with 
  | Primitive(String s) -> 
      text $"\"{s}\""
  | _ -> text "???"

let exprTag tag attrs = 
  h?(tag) (attrs @ [
    "class" => "expr"
    "mouseover" =!> fun el _ -> if el.className = "expr" then el.className <- "expr hover"
    "mouseout" =!> fun el _ -> if el.className = "expr hover" then el.className <- "expr"
  ])

let expr = exprTag "span" []
let exprA = exprTag "a"


let renderBinding trigger state parent (var:string) =
  let editVar, displayVar = if var.StartsWith("unnamed-") then "", "_" else var, var
  let path = parent @ [Field var]
  if state.EditingBindingPath = Some(path) then
    expr [ h?input [ 
      "type" => "text"
      "value" => editVar
      "keydown" =!> fun el evt -> 
        let ke = unbox<KeyboardEvent> evt
        let newVar = (unbox<HTMLInputElement> el).value
        if ke.key = "Enter" && newVar.Length > 0 && Seq.forall System.Char.IsLetter newVar then 
          let ed = RecordRenameField(UpdateReferences, parent, var, newVar)
          trigger(ApplyEdits("rename field", [ed]))
          trigger(EditBinding None)
        if ke.key = "Escape" then 
          trigger(EditBinding None)
      ] [] ]
  else
    exprA [ 
      "href" => "javascript:;"
      "click" =!> fun _ _ -> trigger (EditBinding (Some path)) ] [ text displayVar ] 


let renderValue trigger state parent fld nd = 
  let path = parent @ [Field fld]
  match nd with 
  | Primitive(p) when state.EditingValuePath = Some(path) -> 
      let s = match p with String s -> s | Number n -> string n
      let parse s = 
        match p, System.Int32.TryParse(s) with 
        | String _, _ -> Some(String(s))
        | Number _, (true, n) -> Some(Number(n))
        | _ -> None
      expr [ h?input [ 
        "type" => "text"
        "value" => s 
        "keydown" =!> fun el evt -> 
          let ke = unbox<KeyboardEvent> evt
          let ie = unbox<HTMLInputElement> el
          match ke.key, parse ie.value with 
          | "Enter", Some p ->
              let pred, succ = 
                match select parent state.Document with 
                | [Record(_, flds)] -> OrdList.tryFindPred fld flds, OrdList.tryFindSucc fld flds
                | _ -> None, None
              let ed = RecordAdd(parent, fld, pred, succ, Primitive(p))
              trigger(ApplyEdits("update value", [ed]))
              trigger(EditValue None)
          | "Escape", _ ->
              trigger(EditValue None)
          | _ -> ()
        ] [] ]

  | Primitive(p) -> 
      let s = match p with String s -> $"\"{s}\"" | Number n -> string n
      exprA [ 
        "href" => "javascript:;"
        "click" =!> fun _ _ -> trigger (EditValue (Some path)) ] [ text s ] 
  
  | Reference(_, [Field cell; Field formula]) ->
      expr [ text formula ]

  | v -> 
      failwith $"renderValue: Unknown value: {v}"


let rec renderCodeFormula trigger state path nd = h?span [] [
    match nd with
    | FormulaEvaluated(result, formula) ->
        renderCodeFormula trigger state path formula
    | FormulaPrimitive _ ->
        let path, fld = match List.rev path with Field(fld)::path -> List.rev path, fld | _ -> failwith "renderCodeFormula: path too short"
        renderValue trigger state path fld nd 
    | FormulaGlobal glob ->
        expr [ text glob ]

    | FormulaMember(ns, op, inst, otherArgs) ->
        renderCodeFormula trigger state (path @ [Field "inst"]) inst
        expr [
          h?span [ "class" => "expr" ] [ text op ]
          text "("
          for i, (arg, value) in Seq.indexed otherArgs do
            if i <> 0 then text ", "
            text $"{arg}="
            renderValue trigger state path arg value
          text ")"
        ]
  ]

let renderCompletion trigger state path completions = h?div [ "class" => "dropdown" ] [
    let opened = state.DisplayMenuPath = Some path
    if not (List.isEmpty completions) then
      h?button [
        "class" => "" +? (opened, "opened")
        "click" =!> fun _ _ -> 
          trigger (SelectCell(Some (List.head path)))
          if opened then trigger(ToggleMenu None)
          else trigger (ToggleMenu (Some path)) ] [text "+"]
    if opened then
      h?ul [] [
        for k, f in completions -> h?li [] [ 
          h?a ["href"=>"javascript:;"; "click" =!> fun _ _ -> 
            let action : CompletionAction = f () 
            trigger (ApplyEdits(action.ActionName, action.ActionEdits))
            trigger (EditValue action.EditPath)
            trigger (ToggleMenu None) ] [ text k ]
        ]
      ]
  ]

let renderCodeCell trigger state cell = h?div [] [
    h?div [ "class" => "code-block" ] [
      let formulas = getCellFormulas cell.Node
      h?ul [ "class" => "flist" ] [
        for (fid, formula) in formulas do 
          h?li [] [ 
            h?div [ "class" => "flist-let" ] [ 
              h?strong [] [ text "let " ]
              renderBinding trigger state [Field cell.ID] fid 
              text " = " 
            ]
            h?div [ "class" => "flist-eq" ] [
              renderCodeFormula trigger state [Field cell.ID; Field fid] formula
              renderCompletion trigger state [cell.ID; fid] <|
                getCompletions state.Bindings [Field cell.ID; Field fid] formula
              match formula with
              | FormulaEvaluated(res, _) ->
                  h?div [ ] [ renderResult res ]
              | _ -> ()
            ]
          ]
      ]
      renderCompletion trigger state [cell.ID] <|
        let lastFormulaId = List.tryLast formulas |> Option.map fst
        let fid = withUniqueId "unnamed" None
        getGlobalCompletions [Field cell.ID] fid lastFormulaId
    ]
    h?div ["class" => "links actions"] [
      h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger Evaluate ] [ 
        h?i [ "class" => "fa fa-play" ] []
        text "evaluate" ]
    ]
  ]

let renderAddLinks trigger previd nextid = 
  let link s fa e = 
    h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger e ] [ 
      h?i [ "class" => "fa " + fa ] []
      text s ]
  h?div [ "class" => "links"] [
    link "text below" "fa-quote-left" (AddCell(TextCell, None, previd, nextid))
    link "code below" "fa-code" (AddCell(CodeCell, None, previd, nextid))
    link "grid below" "fa-table" (AddCell(GridCell, None, previd, nextid))
    match previd with 
    | Some previd -> link "remove this" "fa-xmark" (ApplyEdits("remove cell", [ RecordDelete(UpdateReferences, [], previd) ]))
    | None -> ()
  ]

let renderTitle kind = 
  match kind with 
  | TextCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-quote-left" ] []; text "text" ] 
  | CodeCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-code" ] []; text "code" ] 
  | GridCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-table" ] []; text "grid" ] 

let render trigger state = 
  let cells = getNotebookCells state.Document
  h?div [ "class" => "notebook" ] [
    let firstid = match cells with c::_ -> Some c.ID | _ -> None
    renderAddLinks trigger None firstid

    for cell in cells do h?div [ "class" => $"cell cell-{asCellKindName cell.Kind}" ] [
      renderTitle cell.Kind

      match cell.Kind with 
      | _ when state.ViewSource ->
          h?div ["class" => "treedoc"] [
            renderSourceTree state trigger [Field cell.ID] [] cell.Node
          ]
      | CodeCell -> 
          renderCodeCell trigger state cell
      | _ -> () // TODO
      renderAddLinks trigger (Some cell.ID) cell.NextID
    ]

    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      let nodes = state.Edits |> List.map (Represent.represent None)
      text (Serializer.nodesToJsonString nodes)
    ]
  ]

// --------------------------------------------------------------------------------------
// Loader
// --------------------------------------------------------------------------------------

module Loader = 
  let jso_ = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]}]"""
  let js__ = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-3cb55e34"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-3cb55e34"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-3cb55e34"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]}]"""
  let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-3cb55e34"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-3cb55e34"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-3cb55e34"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-e86776d5"],["node",""],["pred","unnamed-3cb55e34"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-e86776d5"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","aviaFile"],["node","avia.tsv"],["pred","unnamed-3cb55e34"]]}]"""

  let readJsonOps json = 
    List.collect (Represent.unrepresent >> List.map fst) (Serializer.nodesFromJsonString json) 

  let initial = 
    { DisplayMenuPath = None; SelectedCell = None; ViewSource = false; EditingBindingPath = None
      Edits = readJsonOps json; Document = rcd "notebook"; EditingValuePath = None; Bindings = [] }
    |> updateDocument

  let start () =
    let trigger, _, _ = createVirtualDomApp "out" initial render update 
    Browser.Dom.window.onkeydown <- fun e -> 
      if e.altKey && e.key = "u" then
        trigger(ToggleViewSource)
      if e.altKey && e.key = "z" then
        trigger(UndoLastEdit)
