module Denicek.App.Datnicek

open Denicek
open Denicek.Html
open Denicek.Doc
open Denicek.Demos

// --------------------------------------------------------------------------------------
// Helpers
// --------------------------------------------------------------------------------------

let uniqueId s =
  s + "-" + hash(System.Guid.NewGuid()).ToString("x")

let withUniqueId s idOpt =
  match idOpt with 
  | Some id -> id
  | None -> uniqueId s

let (|Lookup|) args = 
  dict args

let (|Find|_|) k (dict:System.Collections.Generic.IDictionary<_, _>) = 
  if dict.ContainsKey k then Some dict.[k] else None

let (|Fail|) msg _ = 
  failwith $"Fail: {msg}"

// --------------------------------------------------------------------------------------
// Object model and builtins
// --------------------------------------------------------------------------------------

type EvaluationContext = 
  { DataFiles : Map<string, Node> }

type Member = 
  { Name : string 
    Arguments : (string * string) list
    Type : unit -> Type
    Invoke : EvaluationContext * System.Collections.Generic.IDictionary<string, Node> -> Node
   }

and Type =
  { Name : string
    Members : Member list }

type CompletionAction = 
  { ActionName : string 
    ActionEdits : EditKind list
    EditPath : Selectors option }

let (|PS|_|) = function Primitive(String s) -> Some s | _ -> None
let (|PN|_|) = function Primitive(Number s) -> Some s | _ -> None

let stringObj = { Name = "string"; Members = [] }
let numberObj = { Name = "number"; Members = [] }
let rec chartObj = 
  { Name = "chart"
    Members = [
      { Name = "with title"; Arguments = [ "title", "string" ]; Type = fun () -> chartObj 
        Invoke = fun _ -> failwith "chart.with title: not implemented" }
  ]}

let parsePrimitive (s:string) = 
  match System.Double.TryParse(s) with 
  | true, n -> Number(n)
  | _ -> String(s)

let rec tableObj = 

  let mapRows f (List("table", rows) | Fail "mapRows: expected table" rows) =
    let nrows = rows |> OrdList.mapValuesUnordered (fun _ (Record("row", flds) | Fail "mapRows: Expected row" flds) -> 
      Record("row", f flds))
    List("table", nrows)  

  let iterRows f (List("table", rows) | Fail "mapRows: expected table" rows) =
    rows.Members.Values |> Seq.iter (fun (Record("row", flds) | Fail "foldRows: Expected row" flds) -> f flds)

  { Name = "table"
    Members = [
      { Name = "replace"; Arguments = ["substring","string"; "replacement","string" ]; Type = fun () -> tableObj 
        Invoke = function
          | _, Find "inst" table & Find "substring" (PS substr) & Find "replacement" (PS repl) ->
            let replacePrim = function (PS s) -> Primitive(parsePrimitive(s.Replace(substr, repl))) | nd -> nd
            table |> mapRows (OrdList.mapValuesUnordered (fun _ -> replacePrim))            
          | _, args -> failwith $"table.replace: invalid arguments {args}" }

      { Name = "drop"; Arguments = ["column","string" ]; Type = fun () -> tableObj 
        Invoke = function
          | _, Find "inst" table & Find "column" (PS col) ->
            table |> mapRows (OrdList.remove col)            
          | _, args -> failwith $"table.drop: invalid arguments {args}" }

      { Name = "sum"; Arguments = []; Type = fun () -> tableObj 
        Invoke = function
          | _, Find "inst" table ->
            let dict = System.Collections.Generic.Dictionary<_, _>()
            table |> iterRows (fun row ->
              for (KeyValue(k, v)) in row.Members do
                if not (dict.ContainsKey k) then dict.[k] <- 0
                dict.[k] <- dict.[k] + (match v with PN n -> int n | _ -> failwith $"table.sum: not a number {v}") )
            List("table", OrdList.ofList [ 
              for (KeyValue(k, v)) in dict -> 
                string k, Record("row", OrdList.ofList [ "column", Primitive(String k); "value", Primitive(Number v) ]) ])
          | _, args -> failwith $"table.sum: invalid arguments {args}" }
  ]}


let globalDataObj = 
  { Name = "data"
    Members = [ 
      { Name = "load"; Arguments = [ "file", "string" ]; Type = fun () -> tableObj 
        Invoke = function
          | ctx, Find "file" (PS fn) ->
              if ctx.DataFiles.ContainsKey(fn) then ctx.DataFiles.[fn]
              else failwith $"data.load: unknown file {fn}"
          | _, args -> failwith $"data.load: invalid arguments {args}" }
  ]}
let globalVisObj =
  { Name = "vis"
    Members = [ 
      { Name = "bar"; Arguments = [ "data", "table" ]; Type = fun () -> chartObj 
        Invoke = fun _ -> failwith "vis.bar: not implemented" }
      { Name = "line"; Arguments = [ "data", "table" ]; Type = fun () -> chartObj
        Invoke = fun _ -> failwith "vis.linetitle: not implemented" }
  ]}
let globalMathObj =
  let rnd = System.Random()
  { Name = "math"
    Members = [ 
      { Name = "random"; Arguments = [ "min", "number"; "max", "number" ]; Type = fun () -> numberObj 
        Invoke = function
          | _, Find "min" (PN min) & Find "max" (PN max) ->
              Primitive(Number (rnd.Next(int min, int max)))
          | _, args -> failwith $"math.random: invalid arguments {args}" }
  ]}

let globals = [ globalDataObj; globalVisObj; globalMathObj ]
let globalsLookup = dict [ for t in globals -> t.Name, t ]
let types = globals @ [ tableObj; chartObj; stringObj; numberObj ]
let typesLookup = dict [ for t in types -> t.Name, t ]

// --------------------------------------------------------------------------------------
// Evaluation and completions
// --------------------------------------------------------------------------------------

let rec (|FormulaEvaluated|_|) nd = 
  match nd with 
  | Record("x-evaluated", Lookup(Find "result" nd & Find "formula" formula)) ->
      Some(nd, formula)
  | Record("x-evaluated", Lookup(Find "result" nd & Find "reference" formula)) ->
      Some(nd, formula)
  | _ -> None

let rec (|FormulaGlobal|FormulaMember|FormulaReference|FormulaPrimitive|) nd = 
  match nd with 
  | Reference(_, [Field "$datnicek"; Field glob]) -> 
      FormulaGlobal glob
  | Reference(_, [Field _; Field _] & path) ->
      FormulaReference(path)
  | Record("x-formula", args & Lookup(Find "inst" inst & 
        Find "op" (Reference(_, [Field "$datnicek"; Field ns; Field op] )))) ->
      let otherArgs = args |> OrdList.toList |> List.filter (fun (k, _) -> k <> "op" && k <> "inst")
      FormulaMember(ns, op, inst, otherArgs)
  | Primitive(p) ->
      FormulaPrimitive(p)
  | _ -> failwith $"FormulaGlobal|FormulaMember|FormulaPrimitive: Not a formula or missing op: {nd}"

let rec getFormulaType bindings nd = 
  match nd with 
  | FormulaEvaluated(_, formula) -> getFormulaType bindings formula
  | FormulaReference(path) -> getFormulaType bindings (Seq.pick (fun (k, v) -> 
      if k = path then Some v else None) bindings)
  | FormulaPrimitive(String _) -> "string"
  | FormulaPrimitive(Number _) -> "number"
  | FormulaGlobal(glob) -> glob
  | FormulaMember(ns, op, _, _) -> 
      let mems = typesLookup.[ns].Members
      let mem = mems |> List.find (fun mem -> mem.Name = op)
      mem.Type().Name

let getGlobalCompletions bindings path fid lastfid = [
  for gt in globals do
    "use " + gt.Name, fun () -> 
      let ed = RecordAdd(path, fid, lastfid, None, ref [Field "$datnicek"; Field gt.Name])
      { ActionName = $"add formula to {id}"; ActionEdits = [ ed ]; EditPath = None }
  for ref, formula in bindings do
    let fld = match List.last ref with Field f -> f | _ -> failwith "getGlobalCompletions: Path didn't end with field"
    if not (fld.StartsWith "unnamed-") then 
      "use " + fld, fun () ->
        let ed = RecordAdd(path, fid, lastfid, None, Reference(Absolute, ref))
        { ActionName = $"add formula to {id}"; ActionEdits = [ ed ]; EditPath = None }
  "add \"string\"", fun () ->      
    let ed = RecordAdd(path, fid, lastfid, None, Primitive(String ""))
    { ActionName = $"add string to {id}"; ActionEdits = [ ed ]; EditPath = None }
  "add #number", fun () ->      
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
        ra + " = #number", fun () ->
          let ed = RecordAdd(path, ra, None, None, Primitive(Number 0))
          { ActionName = "select completion"; ActionEdits = [ ed ]; EditPath = Some(path @ [Field ra]) }
      for ref, formula in bindings do
        let fld = match List.last ref with Field f -> f | _ -> failwith "getArgumentCompletion: Path didn't end with field"
        if ratyp = getFormulaType bindings formula && not (fld.StartsWith "unnamed-") then 
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
  | FormulaEvaluated(_, formula) -> 
      getCompletions bindings path formula

  | FormulaReference(path) ->
      let refTyp = getFormulaType bindings formula
      typesLookup.[refTyp] |> getTypeCompletions

  | FormulaPrimitive(_) -> 
      []

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


let evaluateBuiltin evalCtx op args = 
  match op with 
  | [Field "$datnicek"; Field ns; Field op] ->
      let m = typesLookup.[ns].Members |> List.find (fun m -> m.Name = op)
      let args = args |> Map.map (fun _ nd -> Eval.getEvaluatedResult nd)
      m.Invoke(evalCtx, args)
  | _ -> 
      failwith $"evaluateBuiltin: Unexpected op: {op}"


// --------------------------------------------------------------------------------------
// Application state
// --------------------------------------------------------------------------------------

type State = 
  { 
    SourceEdits : Edit list
    EvaluatedEdits : Map<string, Edit list>

    Document : Node
    Bindings : (Selectors * Node) list

    DataFiles : Map<string, Node>

    SelectedCell : string option
    DisplayMenuPath : string list option
    EditingValuePath : Selectors option
    EditingBindingPath : Selectors option
    ViewSource : bool
    ShowHistory : bool
  }

type CellKind = 
  | TextCell
  | CodeCell
  | GridCell

type Event = 
  | ToggleViewSource 
  | ToggleShowHistory
  | UndoLastEdit
  | ToggleMenu of path:string list option
  | SelectCell of cellIdOpt:string option
  | ApplyEdits of groupLbl:string * edits:EditKind list
  | EditValue of sel:Selectors option
  | EditBinding of sel:Selectors option
  | Evaluate of cellId:string
  | LoadData of dataFiles:Map<string, Node>
  
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
  let allEds = List.append state.SourceEdits (List.concat state.EvaluatedEdits.Values)  
  let doc = Apply.applyHistory (rcd "notebook") allEds
  { state with Document = doc; Bindings = getBindings doc }

let mergeEdits state g eds = 
  let eds = [ for ed in eds -> { Kind = ed; Dependencies = []; GroupLabel = g } ]
  let origEds = state.SourceEdits 
  let newEds = state.SourceEdits @ eds
  let evalEds = state.EvaluatedEdits |> Map.map (fun _ evalEds -> 
    Eval.updateEvaluatedEdits origEds newEds evalEds)
  { state with SourceEdits = newEds; EvaluatedEdits = evalEds } |> updateDocument

let evaluateCell state cell = 
  match state.Document with 
  | Record(n, cells) -> 
      let singleCellDoc = Record(n, OrdList.ofList [ cell, cells.Members.[cell] ] )
      let previousEvalEds = state.EvaluatedEdits.TryFind(cell) |> Option.defaultValue []
      let evalCtx = { DataFiles = state.DataFiles }
      let newEvalEds = Eval.evaluateAll (evaluateBuiltin evalCtx) singleCellDoc
      let allEvalEds = previousEvalEds @ newEvalEds
      let evaluated = state.EvaluatedEdits.Add(cell, allEvalEds)
      let res = { state with EvaluatedEdits = evaluated } |> updateDocument
      res
  | _ -> failwith "update.Evaluate: Cell not found"

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
  // If there are evaluated edits, we first undo those (all at once). 
  // If there are no evaluated edits, we actually undo the last edit. 
  | UndoLastEdit when Seq.isEmpty (Seq.concat state.EvaluatedEdits.Values) ->
      let oneLess = List.truncate (state.SourceEdits.Length - 1) state.SourceEdits
      { state with SourceEdits = oneLess } |> updateDocument
  | UndoLastEdit -> 
      { state with EvaluatedEdits = Map.empty } |> updateDocument

  | ToggleShowHistory -> { state with ShowHistory = not state.ShowHistory }
  | ToggleViewSource -> { state with ViewSource = not state.ViewSource }
  | SelectCell sel when state.SelectedCell = sel -> state
  | SelectCell sel -> { state with SelectedCell = sel }
  | ToggleMenu path -> { state with DisplayMenuPath = path }
  | EditValue path -> { state with EditingValuePath = path }      
  | EditBinding path -> { state with EditingBindingPath = path }      
  
  | LoadData(dataFiles) -> { state with DataFiles = dataFiles }

  | ApplyEdits(lbl, eds) -> mergeEdits state lbl eds
  | Evaluate(cell) -> evaluateCell state cell

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

let renderReference ref = 
  h?a [ "class" => "selector" ] [ 
    text (Format.formatReference ref)
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
        | Reference(kind, sel) -> yield renderReference (kind, sel)
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

let renderPrimitive = function
  | Primitive(String s) -> s
  | Primitive(Number n) -> string n
  | nd -> failwith $"renderPrimitive: not primitive {nd}"

let renderTable (rows:OrdList.OrdList<_, _>) = 
    Log.logOp "apprender" $"renderTable - {rows.Members.Count} rows" <| fun () ->
  let flds = 
    match Seq.tryHead rows.Members.Values with 
    | Some(Record("row", flds)) -> List.ofSeq (Seq.map fst flds) 
    | _ -> failwith "renderTable: Empty or invalid first row"
  h?div ["class" => "table-box"] [
    h?table [] [
      h?thead [] [ h?tr [] [
        for f in flds -> h?th [] [ text f ]
      ] ]
      h?tbody [] [
        for _, (Record("row", obj) | Fail "renderTable: Expected row" obj) in Seq.truncate 100 rows -> h?tr [] [
          for f in flds -> 
            match obj.Members.TryFind(f) with 
            | Some v -> h?td [] [ text (renderPrimitive v) ]
            | _ -> failwith $"renderTable: Missing {f} in {obj.Members}"
        ]
      ]
    ]
  ]

let renderResult nd = 
  match nd with 
  | Primitive(String s) -> 
      text $"\"{s}\""
  | Primitive(Number n) -> 
      text (string n)
  | List("table", rows) -> 
      renderTable rows
  | _ -> text $"{nd}"

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
  
  | v -> 
      failwith $"renderValue: Unknown value: {v}"

let rec renderArgument trigger state path arg value = 
  match value with 
  | FormulaEvaluated(_, formula) -> 
      renderArgument trigger state path arg formula
  | Reference(_, [Field cell; Field formula]) ->
      expr [ text formula ]
  | _ -> renderValue trigger state path arg value

let rec renderCodeFormula trigger state path nd = h?span [] [
    match nd with
    | FormulaEvaluated(result, formula) ->
        renderCodeFormula trigger state path formula
    
    | FormulaPrimitive _ ->
        let path, fld = match List.rev path with Field(fld)::path -> List.rev path, fld | _ -> failwith "renderCodeFormula: path too short"
        renderValue trigger state path fld nd 
    | FormulaReference([Field _; Field local] | Fail "renderCodeFormula: Invalid reference" local) ->
        expr [ text local ]
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
            renderArgument trigger state path arg value
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

let renderCodeCell trigger state cell = 
    Log.logOp "apprender" $"renderCodeCell {cell.ID}" <| fun () ->
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
      getGlobalCompletions state.Bindings [Field cell.ID] fid lastFormulaId
  ]

let renderEvalLink trigger cell =
  h?div ["class" => "links actions"] [
    h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger (Evaluate cell.ID) ] [ 
      h?i [ "class" => "fa fa-play" ] []
      text "evaluate" ]
  ]

let renderAddLinks trigger previd nextid = 
  let addCellBelow kind pred succ = fun () ->
    let id = uniqueId "cell" 
    let ed = RecordAdd([], id, pred, succ, rcd $"cell-{asCellKindName kind}")
    ApplyEdits($"add cell {id}", [ ed ])
  let link s fa e = 
    h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger (e ()) ] [ 
      h?i [ "class" => "fa " + fa ] []
      text s ]
  h?div [ "class" => "links"] [
    link "text below" "fa-quote-left" (addCellBelow TextCell previd nextid)
    link "code below" "fa-code" (addCellBelow CodeCell previd nextid)
    link "grid below" "fa-table" (addCellBelow GridCell previd nextid)
    match previd with 
    | Some previd -> link "remove this" "fa-xmark" (fun () ->
        ApplyEdits("remove cell", [ RecordDelete(UpdateReferences, [], previd) ]))
    | None -> ()
  ]

let renderTitle kind = 
  match kind with 
  | TextCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-quote-left" ] []; text "text" ] 
  | CodeCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-code" ] []; text "code" ] 
  | GridCell -> h?p ["class" => "title"] [ h?i [ "class" => "fa fa-table" ] []; text "grid" ] 

// --------------------------------------------------------------------------------------
// Rendering of history
// --------------------------------------------------------------------------------------

let formatNode path nd = 
  let rec loop depth path nd = 
    match nd with 
    | _ when depth > 4 -> text "..."
    | Primitive(Number n) -> text (string n)
    | Primitive(String s) -> text s
    | Reference(kind, sel) -> renderReference (kind, sel)
    | List(tag, nds) -> h?span [] [
          yield text (tag + "[")
          for j, (i, nd) in Seq.indexed nds do 
            if j <> 0 then yield text ", "
            yield text $"{i}="
            yield loop (depth+1) (path @ [Index i]) nd
          yield text "]"
        ]
    | Record(tag, nds) -> h?span [] [
          yield text (tag + "{")
          for i, (f, nd) in Seq.indexed nds do 
            if i <> 0 then yield text ", "
            yield text $"{f}="
            yield loop (depth+1) (path @ [Field f]) nd
          yield text "}"
        ]
  loop 0 path nd

let renderEdit (ed:Edit) = 
  let render rb n fa sel args = 
    h?li [] [ 
      h?i [ "class" => "fa " + fa ] [] 
      text " "
      h?strong [] [ text (if rb = KeepReferences then "v." + n else "s." + n) ]
      text " "
      renderReference (Absolute, sel)
      h?br [] []
      for i, (k, v) in Seq.indexed args do
        if i <> 0 then text ", "
        text $"{k} = "
        h?span [] [ v ]
      if ed.Dependencies <> [] then 
        h?br [] [] 
        text "deps=("
        for i, dep in Seq.indexed ed.Dependencies do
          if i <> 0 then text ", "
          renderReference (Absolute, dep)
        text ")"
    ]
  let renderv = render KeepReferences
  let fmtprev k = function Some s -> [k, text s] | _ -> []
  match ed.Kind with 
  | PrimitiveEdit(sel, fn, None) -> renderv "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
  | PrimitiveEdit(sel, fn, Some arg) -> renderv "edit" "fa-solid fa-i-cursor" sel ["fn", text fn; "arg", text arg]
  | RecordAdd(sel, f, prev, succ, nd) -> renderv "addfield" "fa-plus" sel <| ["node", formatNode sel nd; "fld", text f] @ fmtprev "prev" prev @ fmtprev "succ" succ
  | UpdateTag(sel, t) -> renderv "retag" "fa-code" sel ["t", text t]
  | ListAppend(sel, i, prev, succ, nd) -> renderv "append" "fa-at" sel <| ["i", text i; "node", formatNode sel nd ] @ fmtprev "prev" prev @ fmtprev "succ" succ
  | ListReorder(sel, perm) -> renderv "reorder" "fa-list-ol" sel ["perm", text (string perm)]
  | Copy(rk, tgt, src) -> render rk "copy" "fa-copy" tgt ["from", renderReference (Absolute, src)]
  | WrapRecord(rk, id, tg, sel) -> render rk "wraprec" "fa-regular fa-square" sel ["id", text id; "tag", text tg]
  | WrapList(rk, tg, i, sel) -> render rk "wraplist" "fa-solid fa-list-ul" sel ["i", text i; "tag", text tg]
  | RecordRenameField(rk, sel, fold, fnew) -> render rk "updid" "fa-font" sel ["old", text fold; "new", text fnew]
  | ListDelete(sel, i) -> renderv "delitm" "fa-xmark" sel ["index", text (string i)]
  | RecordDelete(rk, sel, fld) -> render rk "delfld" "fa-rectangle-xmark" sel ["fld", text fld]

let renderHistory state = h?div [ "id" => "history" ] [
    for (KeyValue(k,v)) in state.EvaluatedEdits do
      if not (List.isEmpty v) then
        h?h3 [] [ text $"Evaluated for {k}" ]
        h?ol [] (List.map renderEdit (List.rev v))
    h?h3 [] [ text $"Source edits" ]
    h?ol [] (List.map renderEdit (List.rev state.SourceEdits))
  ]

let render trigger state = h?div [ "id" => "main" ] [
  let cells = getNotebookCells state.Document
  h?div [ "id" => "notebook" ] [
    let firstid = match cells with c::_ -> Some c.ID | _ -> None
    renderAddLinks trigger None firstid

    for cell in cells do h?div [ "class" => $"cell cell-{asCellKindName cell.Kind}" ] [
      renderTitle cell.Kind

      match cell.Kind with 
      | ck when state.ViewSource ->
          h?div ["class" => "treedoc"] [
            renderSourceTree state trigger [Field cell.ID] [] cell.Node
          ]
          if ck = CodeCell then
            renderEvalLink trigger cell
      | CodeCell -> 
          renderCodeCell trigger state cell
          renderEvalLink trigger cell
      | _ -> () // TODO
      renderAddLinks trigger (Some cell.ID) cell.NextID
    ]

    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      let nodes = state.SourceEdits |> List.map (Represent.represent None)
      text (Serializer.nodesToJsonString nodes)
    ]
  ]
  if state.ShowHistory then 
    renderHistory state
]

// --------------------------------------------------------------------------------------
// Loader
// --------------------------------------------------------------------------------------

module Loader = 
  open Browser.XMLHttpRequest

  let asyncRequest file = 
    Async.FromContinuations(fun (cont, econt, ccont) -> 
      let req = XMLHttpRequest.Create()
      req.addEventListener("load", fun _ -> cont req.responseText)
      req.``open``("GET", file)
      req.send())

  let readTsv (s:string) = 
    let lines = s.Trim().Replace("\r", "").Split('\n')
    let cols = lines.[0].Split('\t')
    let rows = lines.[1..] |> Seq.map (fun l ->
      let data = l.Split('\t') |> Array.map (fun s -> Primitive(parsePrimitive s))
      let fields = Seq.zip cols data |> List.ofSeq |> OrdList.ofList
      Record("row", fields) ) |> List.ofSeq
    List("table", OrdList.ofList (List.mapi (fun i v -> string i, v) rows))

  let loadData trigger = async { 
    let data = [ "eurostat/sf_aviaca.tsv"; "eurostat/sf_railvi.tsv" ]
    let! tsvs = [ for d in data -> asyncRequest $"/data/{d}" ] |> Async.Parallel
    let dataFiles = Map.ofSeq (Seq.zip data (Seq.map readTsv tsvs))
    trigger(LoadData dataFiles)  } 


  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]}]"""
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-c842cd9e"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",10]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",100]]}]"""
  
  // incremental evaluation demo using math.random
  let random = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-c842cd9e"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",10]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",100]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-c842cd9e"],["new","nf"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","nf"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-d2aa98a3"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}],["pred","nf"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","min"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","nf"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","max"],["node",100]]}]"""

  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]}]"""
  let traffic = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-a3d603f1"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railTable"]}],["pred","railTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",":"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node","0"]]}]"""
  let traffic2 = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-a3d603f1"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railTable"]}],["pred","railTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",":"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node","0"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node","fof"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node","freq,unit,accident,victim,pers_cat,geo\\\\TIME_PERIOD"]]}]"""

  // 
  let trafficBasic = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]}]"""
//  let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]}]"""
  let json = trafficBasic

  let readJsonOps json = 
    List.collect (Represent.unrepresent >> List.map fst) (Serializer.nodesFromJsonString json) 

  let initial = 
    { DisplayMenuPath = None; SelectedCell = None; ViewSource = false; EditingBindingPath = None
      SourceEdits = readJsonOps json; EvaluatedEdits = Map.empty; ShowHistory = false
      Document = rcd "notebook"; EditingValuePath = None; Bindings = []; DataFiles = Map.empty }
    |> updateDocument

  let start () =
    let trigger, _, _ = createVirtualDomApp "out" initial render update 
    loadData trigger |> Async.Start
    Browser.Dom.window.onkeydown <- fun e -> 
      if e.altKey && e.key = "u" then
        e.preventDefault(); trigger(ToggleViewSource)
      if e.altKey && e.key = "h" then
        e.preventDefault(); trigger(ToggleShowHistory)
      if e.altKey && e.key = "z" then
        e.preventDefault(); trigger(UndoLastEdit)
