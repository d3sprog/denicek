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

let (|TryParse|_|) s = match System.Double.TryParse s with true, n -> Some n | _ -> None

let (|TryFind|) k (dict:System.Collections.Generic.IDictionary<_, _>) =
  if dict.ContainsKey k then Some dict.[k] else None

let (|Find|_|) k (dict:System.Collections.Generic.IDictionary<_, _>) =
  if dict.ContainsKey k then Some dict.[k] else None

let (|Fail|) msg input =
  failwith $"Fail: {msg} Got: {input}"

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
let (|PPS|_|) = function Primitive(String s) -> Some s | Primitive(Number n) -> Some(string n) | _ -> None
let (|PN|_|) = function Primitive(Number n) -> Some n | _ -> None
let (|PPN|_|) = function Primitive(Number n) | Primitive(String (TryParse n)) -> Some n | _ -> None

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

  let filterRows f (List("table", rows) | Fail "mapRows: expected table" rows) =
    let nrows = rows |> OrdList.toList |> List.filter (fun (i, (Record("row", flds) | Fail "filterRows: Expected row" flds)) -> f i flds)
    List("table", OrdList.ofList nrows)

  let iterRows f (List("table", rows) | Fail "mapRows: expected table" rows) =
    rows.Members.Values |> Seq.iter (fun (Record("row", flds) | Fail "foldRows: Expected row" flds) -> f flds)

  { Name = "table"
    Members = [
      { Name = "replace"; Arguments = ["column","string"; "old","string"; "new","string" ]; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table & Find "column" (PS col) & Find "old" (PS substr) & Find "new" (PS repl) ->
            let replacePrim = function (PS s) -> Primitive(parsePrimitive(s.Replace(substr, repl))) | nd -> nd
            table |> mapRows (OrdList.mapValuesUnordered (fun k v -> if col = "*" || k = col then replacePrim v else v))
          | _, args -> failwith $"table.replace: invalid arguments {args}" }

      { Name = "filter"; Arguments = ["column","string"; "cond","string"; "value","string" ]; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table & Find "column" (PS col) & Find "cond" (PS cond) & Find "value" (PS value) ->
            let op = if cond = "equals" then (<>) else (=)
            table |> filterRows (fun i obj -> match obj.Members.TryFind(col) with Some (PPS s) -> op s value | _ -> false)
          | _, args -> failwith $"table.filter: invalid arguments {args}" }

      { Name = "split"; Arguments = ["column","string"; "by","string"]; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table & Find "column" (PS col) & Find "by" (PS delim) -> 
            table |> mapRows (fun row -> 
              let value = match row.Members.[col] with PS s -> s | PN n -> string n | _ -> ""
              let prev, succ = OrdList.tryFindPred col row, OrdList.tryFindSucc col row
              let ncols = col.Split(delim.[0]) |> List.ofArray
              let vals = value.Split(delim.[0]) |> List.ofArray
              let vals = if vals.Length < ncols.Length then vals @ List.init (ncols.Length - vals.Length) (fun _ -> "") else vals
              let prevs = prev :: List.take (ncols.Length - 1) (List.map Some ncols)
              let colsToAdd = List.zip3 ncols vals prevs
              let row = OrdList.remove col row 
              let row = colsToAdd |> List.fold (fun row (ncol, nval, prev) -> OrdList.add (ncol, ps nval) prev row) row
              match succ with None -> row | Some succ -> OrdList.add (succ, row.Members.[succ]) (Some (List.last ncols)) row
            )
          | _, args -> failwith $"table.split: invalid arguments {args}" }

      { Name = "rename"; Arguments = ["old","string"; "new","string"]; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table & Find "old" (PS oldf) & Find "new" (PS newf) -> table |> mapRows (OrdList.renameKey oldf newf)
          | _, args -> failwith $"table.rename: invalid arguments {args}" }

      { Name = "drop"; Arguments = ["column","string" ]; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table & Find "column" (PS col) -> table |> mapRows (OrdList.remove col)
          | _, args -> failwith $"table.drop: invalid arguments {args}" }

      { Name = "sum"; Arguments = []; Type = fun () -> tableObj
        Invoke = function
          | _, Find "inst" table ->
            let dict = System.Collections.Generic.Dictionary<_, _>()
            table |> iterRows (fun row ->
              for (KeyValue(k, v)) in row.Members do
                if not (dict.ContainsKey k) then dict.[k] <- Some 0.0
                dict.[k] <- Option.map2 (+) dict.[k] (match v with PPN n -> Some n | _ -> None))
            List("table", OrdList.ofList [
              for (KeyValue(k, v)) in dict do
                if v.IsSome then
                  string k, Record("row", OrdList.ofList [ "column", Primitive(String k); "value", Primitive(Number v.Value) ]) ])
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
        Invoke = function 
          | _, Find "data" tbl -> Record("x-compost", OrdList.ofList ["source", tbl; "kind", ps "bar"])
          | _, args -> failwith $"vis.bar: invalid arguments {args}" }
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

let rec (|FormulaGlobal|FormulaMember|FormulaReference|FormulaPrimitive|FormulaGrid|) nd =
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
  | Record("cell-grid", Lookup(Find "name" (Primitive(String n)))) -> FormulaGrid n
  | _ -> failwith $"Formula: Not a formula or missing op: {nd}"

let rec getFormulaType bindings nd =
  match nd with
  | FormulaEvaluated(_, formula) -> getFormulaType bindings formula
  | FormulaReference(path) -> getFormulaType bindings (Seq.pick (fun (k, v) ->
      if k = path then Some v else None) bindings)
  | FormulaPrimitive(String _) -> "string"
  | FormulaPrimitive(Number _) -> "number"
  | FormulaGlobal(glob) -> glob
  | FormulaGrid _ -> "table"
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

  | FormulaGrid _ ->
      getTypeCompletions typesLookup.["table"]

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

type EditExpansion =
  { Target : Selectors 
    Condition : Selectors 
    Prefix : Selectors } 

type ExpandedEdit = 
  { Expansion : EditExpansion option
    Edit : EditKind } 

type GridEdit =
  { Title : string
    Icon : string
    EditType : string
    Description : string
    Edits : ExpandedEdit list 
    Code : Node }

type GridLocation =
  { CellId:string;
    RowIndex:string option;
    Field:string }

type GridCellState =
  { Data : (Node * int * Node) option  // input, hash, output
    Source : Selectors }

type State =
  {
    SourceEdits : Edit list
    EvaluatedEdits : Map<string, Edit list>
    GridEvaluatedEdits : Map<string, Edit list>

    Document : Node
    Bindings : (Selectors * Node) list

    DataFiles : Map<string, Node>

    SelectedCell : string option
    DisplayMenuPath : string list option
    ViewSource : bool
    ShowHistory : bool

    // Code editing
    EditingBindingPath : Selectors option
    EditingValuePath : Selectors option
    // Grid editing
    EditingGridPath : Map<string, GridLocation option>
    GridRecommendations : Map<string, GridEdit list>

    GridCellState : Map<string, GridCellState>
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
  | Evaluate of cellId:string
  | LoadData of dataFiles:Map<string, Node>
  // Code editing
  | EditValue of sel:Selectors option
  | EditBinding of sel:Selectors option
  // Grid editing
  | GridToCode of cell:string * nextCell:string option
  | EditGrid of cell:string * sel:GridLocation option
  | GridRecommend of cell:string * kind:string * recs:GridEdit list
  | GridApplyEdit of cell:string * edits:GridEdit
  | UpdateGridState of cell:string

// --------------------------------------------------------------------------------------
// Document edits
// --------------------------------------------------------------------------------------

let getBindings doc =
  match doc with
  | Record(_, cells) ->
      cells |> OrdList.toList |> List.collect (fun (ck, cv) ->
        match cv with
        | Record("cell-code", formulas) ->
            formulas |> OrdList.toList |> List.map (fun (fk, fv) ->
              [Field ck; Field fk], fv)
        | Record("cell-grid", Lookup(Find "name" (Primitive(String nm)))) -> 
            [ [Field ck; Field nm], cv ]
        | Record("cell-grid", _) 
        | Record("cell-text", _) -> []
        | _ -> failwith "getBindings: Expected record of formulas")
  | _ -> failwith "getBindings: Expected record of cells"

let updateDocument state =
  let allEds = 
    state.SourceEdits @ (List.concat state.GridEvaluatedEdits.Values)
      @ (List.concat state.EvaluatedEdits.Values) 
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
  // Scope filters the document to only parts that we want to evaluate in
  let scope doc = 
    match doc with 
    | Record(n, cells) -> Record(n, OrdList.ofList [ cell, cells.Members.[cell] ] )
    | _ -> failwith "update.Evaluate: Cell not found"
  Log.log "codeeval" $"Evaluating for {cell}"
  let previousEvalEds = state.EvaluatedEdits.TryFind(cell) |> Option.defaultValue []
  let evalCtx = { DataFiles = state.DataFiles }
  let newEvalEds = Eval.evaluateAllScoped (evaluateBuiltin evalCtx) scope state.Document
  let allEvalEds = previousEvalEds @ newEvalEds
  for e in allEvalEds do  
    Log.log "codeeval" $"Evaluated for {cell}: {Format.formatEdit e}"
  let evaluated = state.EvaluatedEdits.Add(cell, allEvalEds)
  let res = { state with EvaluatedEdits = evaluated } |> updateDocument
  res

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
    Id : string
    NextId : string option
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
              Id = id; NextId = next; Node = nd }
        | _ -> failwith "getNotebookCells: expected record cell")
  | _ -> failwith "getNotebookCells: expected document node"

// --------------------------------------------------------------------------------------
// Grid state
// --------------------------------------------------------------------------------------

let getAppliedEditsMetadata cellNode = 
  match cellNode with 
  | Record("cell-grid", { Members = Find "edits" (List("edits", edits)) }) ->
      edits |> OrdList.toList |> List.map (function
        | _, Record("transform", { Members = Find "title" (PS title) 
          & Find "icon" (PS icon) & Find "description" (PS description) }) -> 
          {| icon = icon; description = description; title = title |}
        | _ -> failwith "getAppliedEditsMetadata: not transform")
  | _ -> failwith "getAppliedEditsMetadata: no edits in cell-grid" 


let getGridState cellId state = 
  let parseEd nd = 
    match nd with 
    | Record("x-expandable-edit", Lookup(Find "condition" (Reference(_, cond)) & Find "edit" ed &
        Find "prefix" (Reference(_, prefix)) & Find "target" (Reference(_, target)))) ->
          { Edit = (fst (List.exactlyOne (Represent.unrepresent ed))).Kind
            Expansion = Some { Condition = cond; Target = target; Prefix = prefix } }
    | ed ->
          { Edit = (fst (List.exactlyOne (Represent.unrepresent ed))).Kind
            Expansion = None }

  match select [Field cellId] state.Document with
  | [ Record(_, { Members = Find "target" (Reference(Absolute, src))
        & Find "edits" (List("edits", edits)) & TryFind "name" name }) ] ->
      let edits = edits |> OrdList.toList 
      let codes = edits |> List.map (function
        | _, Record("transform", { Members = Find "code" code }) -> code
        | _ -> failwith "getGridState: not transform")
      let edits = edits |> List.collect (function
        | _, Record("transform", { Members = Find "edits" (List(_, eds)) }) ->           
          eds |> OrdList.toList |> List.map (snd >> parseEd)
        | _ -> failwith "getGridState: not transform")
      let name = match name with Some(Primitive(String s)) -> s | _ -> ""
      Some(src, name, codes, edits)
  | _ -> None


let evaluateAll doc = 
  let eds = Eval.evaluateAll (Eval.webnicekEvaluateBuiltins Map.empty) doc
  if List.isEmpty eds then doc else 
  Log.log "grideval" $"Applying {eds.Length} edits"
  let doc = Apply.applyHistory doc eds
  Log.log "grideval" "Evaluated grid formulas"
  doc

let applyExpandedEdit doc edit =
  match edit.Expansion with 
  | Some exp ->
      let check markerSel = 
        let condSel = resolveReference markerSel (Relative, exp.Condition)
        select (condSel @ [Field "result"]) doc = [Primitive(String "true")]
      let eds = [ 
        for markerSel in expandWildcards exp.Target doc do
          if check markerSel then 
            yield! Webnicek.Helpers.replacePrefixInEdits exp.Prefix markerSel [mkEd edit.Edit] ]
      Apply.applyHistory doc eds
  | None -> 
      Apply.apply doc (mkEd edit.Edit)

let updateGridState cellId state =
  match getGridState cellId state with 
  | Some(src, nm, _, edits) ->
      Log.log "grideval" $"Update {cellId}, name {nm}"
      let cellState = state.GridCellState.TryFind(cellId) |> Option.defaultValue { Source = src; Data = None }
      let cellData = cellState.Data |> Option.orElseWith (fun () ->
        match select src state.Document with
        | [ FormulaEvaluated(table & List("table", _), _) ] -> Some(table, 0, table)
        | _ -> None )      
      let cellData = cellData |> Option.map (fun (input, outputHash, output) ->
        let output = 
          match Merge.takeAfterHash outputHash edits with 
          | Some edits -> 
              Log.log "grideval" $"Applying {edits.Length} edits (prev hash {outputHash})"
              List.fold (fun doc ed -> evaluateAll (applyExpandedEdit doc ed)) output edits
          | _ -> 
              Log.log "grideval" $"Applying all edits (prev hash {outputHash})"
              List.fold (fun doc ed -> evaluateAll (applyExpandedEdit doc ed)) input edits
        input, Merge.hashEditList 0 edits, output)
      let resultEds = 
        match cellData with 
        | Some(_, _, res) when nm <> "" -> 
            Log.log "grideval" $"Returning record-add edit"
            [ mkEd(RecordAdd([Field cellId], nm, None, None, res)) ]
        | _ -> []
      { state with 
          GridEvaluatedEdits = state.GridEvaluatedEdits.Add(cellId, resultEds)
          GridCellState = state.GridCellState.Add(cellId, { cellState with Data = cellData })  }
  | None -> state


let applyGridEdits cellId recm state =
  let state = { state with GridRecommendations = Map.empty }
  let editsSel = [Field cellId; Field "edits"]
  let prevIndex = 
    match select editsSel state.Document with
    | [List(_, items)] -> OrdList.tryLastKey items | _ -> None
  let index = match prevIndex with Some i -> (int i) + 1 | _ -> 0

  Log.log "grideval" $"Expanding edits for cell {cellId}"
  let edits = OrdList.ofList [ 
    for i, ed in Seq.indexed recm.Edits -> 
      let edNode = Represent.represent None (mkEd ed.Edit)
      match ed.Expansion with 
      | Some exp -> 
          string i, Record("x-expandable-edit", OrdList.ofList [
            "condition", Reference(Relative, exp.Condition)
            "prefix", Reference(Absolute, exp.Prefix);
            "target", Reference(Absolute, exp.Target);
            "edit", edNode])
      | None -> 
          string i, edNode ]

  let simpleEd = Record("transform", OrdList.ofList [
      "title", ps recm.Title; "icon", ps recm.Icon; "description", ps recm.Description; 
      "code", recm.Code; "edits", List("edits", edits) ])
  [ ListAppend(editsSel, string index, prevIndex, None, simpleEd) ]
  |> mergeEdits { state with EditingGridPath = state.EditingGridPath.Add(cellId, None) } "add edits"
  |> updateGridState cellId


let turnGridToCode cellId nextCell state = 
  match getGridState cellId state with 
  | Some(src, name, ops, _) ->
      let id = uniqueId "cell"
      let name = if name = "" then uniqueId "unnamed" else name
      let code = Reference(Absolute, src)
      let code = ops |> List.fold (fun inst op -> replace (fun _ nd -> 
        match nd with Record("x-hole", _) -> Some inst | _ -> None) op ) code
      let eds = [
        RecordAdd([], id, Some cellId, nextCell, rcd $"cell-{asCellKindName CodeCell}")
        RecordAdd([Field id], name, None, None, code)
      ]
      mergeEdits state "turn to code" eds
  | _ -> state

// --------------------------------------------------------------------------------------
// Update operation
// --------------------------------------------------------------------------------------

let update state trigger evt =
  match evt with
  // If there are evaluated edits, we first undo those (all at once).
  // If there are no evaluated edits, we actually undo the last edit.
  | UndoLastEdit when Seq.isEmpty (Seq.concat state.EvaluatedEdits.Values) ->
      let oneLess = List.truncate (state.SourceEdits.Length - 1) state.SourceEdits
      //let updateGrids = getNotebookCells state.Document |> List.choose (fun c -> 
      //  if c.Kind = GridCell then Some(updateGridState c.Id) else None) |> List.reduce (>>)
      { state with SourceEdits = oneLess } |> updateDocument
  | UndoLastEdit ->
      { state with EvaluatedEdits = Map.empty } |> updateDocument

  | ToggleShowHistory -> { state with ShowHistory = not state.ShowHistory }
  | ToggleViewSource -> { state with ViewSource = not state.ViewSource }
  | SelectCell sel when state.SelectedCell = sel -> state
  | SelectCell sel -> { state with SelectedCell = sel }
  | ToggleMenu path -> { state with DisplayMenuPath = path }

  | LoadData(dataFiles) -> { state with DataFiles = dataFiles }

  | ApplyEdits(lbl, eds) -> mergeEdits state lbl eds
  | Evaluate(cell) -> evaluateCell state cell

  | EditValue path -> { state with EditingValuePath = path }
  | EditBinding path -> { state with EditingBindingPath = path }

  | EditGrid(id, path) -> 
      let recs = state.GridRecommendations
      let recs = if path = None then recs.Add(id, []) else recs
      { state with EditingGridPath = state.EditingGridPath.Add(id, path); GridRecommendations = recs }

  | GridRecommend(id, kind, recm) ->
      let oldrecs = state.GridRecommendations.TryFind(id) |> Option.defaultValue []
      let newrecs = List.filter (fun r -> r.EditType <> kind) oldrecs @ recm
      { state with GridRecommendations = state.GridRecommendations.Add(id, newrecs) }

  | GridApplyEdit(cellId, recm) -> applyGridEdits cellId recm state 
  | UpdateGridState(cellId) -> updateGridState cellId state |> updateDocument
  | GridToCode(cellId, nextCell) -> turnGridToCode cellId nextCell state

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

let renderEvalLink trigger label cellId =
  h?div ["class" => "links actions"] [
    h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger (Evaluate cellId) ] [
      h?i [ "class" => "fa fa-play" ] []
      text label ]
  ]

let renderCompletion trigger state path extra completions = h?div [ "class" => "dropdown" ] [
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
            trigger (ToggleMenu None) 
            extra |> Option.iter trigger ] [ text k ]
        ]
      ]
  ]

let parseFormat p =
  let s = match p with String s -> s | Number n -> string n
  let parse s =
    match p, System.Int32.TryParse(s) with
    | String _, _ -> Some(String(s))
    | Number _, (true, n) -> Some(Number(n))
    | _ -> None
  s, parse

let rec getPrimitive = function
  | Primitive(p) -> p
  | Record("x-formula", _) -> String "=(...)"
  | Record("x-evaluated", Lookup(Find "result" res)) -> getPrimitive res
  | nd -> failwith $"getPrimitive: not primitive {nd}"

let rec renderPrimitive = function
  | Primitive(String s) -> s
  | Primitive(Number n) -> string n
  | Record("x-formula", _) -> "=(...)"
  | Record("x-evaluated", Lookup(Find "result" res)) -> renderPrimitive res
  | nd -> failwith $"renderPrimitive: not primitive {nd}"

let getTableHeaders (rows:OrdList.OrdList<_, _>) =
  match Seq.tryHead rows.Members.Values with
  | Some(Record("row", flds)) -> List.ofSeq (Seq.map fst flds)
  | _ -> failwith "renderTable: Empty or invalid first row"

let getTableRows flds (rows:OrdList.OrdList<_, _>) =
  rows |> Seq.truncate 100 |> Seq.map (fun (i, (Record("row", obj) | Fail "renderTable: Expected row" obj)) ->
    i, flds |> Seq.map (fun f ->
      match obj.Members.TryFind(f) with
      | Some v -> f, v
      | _ -> failwith $"renderTable: Missing {f} in {obj.Members}") )

let renderTable (table:OrdList.OrdList<_, _>) =
    Log.logOp "apprender" $"renderTable - {table.Members.Count} rows" <| fun () ->
  let flds = getTableHeaders table
  h?div ["class" => "table-box"] [
    h?table [] [
      h?thead [] [ h?tr [] [
        for f in flds -> h?th [] [ text f ]
      ] ]
      h?tbody [] [
        for _, obj in getTableRows flds table -> h?tr [] [
          for _, v in obj -> h?td [] [ text (renderPrimitive v) ]
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
  | Record("x-compost", Lookup(Find "kind" (PS kind) & Find "source" (List("table", rows)))) ->
      let headers = getTableHeaders rows
      let getRow (Record("row", vals) | Fail "renderResult: Expected row" vals) = 
        vals.Members |> Map.map (fun _ (Primitive p | Fail "renderResult: expected primitive" p) -> p)
      let data = OrdList.toList rows |> List.map (snd >> getRow)
      Compost.Charts.render kind headers data
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
      "keyup" =!> fun el evt ->
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
      let s, parse = parseFormat p
      expr [ h?input [
        "type" => "text"
        "value" => s
        "style" => $"width:{s.Length*8+10}px"
        "keyup" =!> fun el evt ->
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
    | FormulaGrid n ->
        expr [ text n ]

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

let getCellFormulas nd =
  match nd with
  | Record("cell-code", formulas) ->
      formulas |> OrdList.toList
  | _ -> failwith "getCellFormulas: expected cell node"

let renderCodeCell trigger state cell =
    Log.logOp "apprender" $"renderCodeCell {cell.Id}" <| fun () ->
  h?div [ "class" => "code-block" ] [
    let formulas = getCellFormulas cell.Node
    h?ul [ "class" => "flist" ] [
      for (fid, formula) in formulas do
        h?li [] [
          h?div [ "class" => "flist-let" ] [
            h?strong [] [ text "let " ]
            renderBinding trigger state [Field cell.Id] fid
            text " = "
          ]
          h?div [ "class" => "flist-eq" ] [
            renderCodeFormula trigger state [Field cell.Id; Field fid] formula
            renderCompletion trigger state [cell.Id; fid] None <|
              getCompletions state.Bindings [Field cell.Id; Field fid] formula
            match formula with
            | FormulaEvaluated(res, _) ->
                h?div [ "class" => "flist-out" ] [ renderResult res ]
            | _ -> ()
          ]
        ]
    ]
    renderCompletion trigger state [cell.Id] None <|
      let lastFormulaId = List.tryLast formulas |> Option.map fst
      let fid = withUniqueId "unnamed" None
      getGlobalCompletions state.Bindings [Field cell.Id] fid lastFormulaId
  ]

// --------------------------------------------------------------------------------------
// Grid cells
// --------------------------------------------------------------------------------------

module CodeBuilder = 
  let fl op args = 
    let hl = Record("x-hole", OrdList.empty ())
    let op = Reference(Absolute, (Field "$datnicek")::List.map Field op)
    Record("x-formula", OrdList.ofList (("op", op)::("inst", hl)::args))

  let filterRows cond col value = fl ["table";"filter"] ["column", ps col; "cond", ps cond; "value", ps value] 
  let replaceString fld olds news = fl ["table";"replace"] ["column", ps fld; "old", ps olds; "new", ps news ] 
  let renameCol oldf newf = fl ["table";"rename"] ["old", ps oldf; "new", ps newf ] 
  let dropCol fld = fl ["table";"drop"] ["column", ps fld ] 
  let splitCol fld delim = fl ["table";"split"] ["column", ps fld; "by", ps (string delim) ] 

let sharedPrefixLength (s1:string) (s2:string) =
  let rec loop i =
    if i < s1.Length && i < s2.Length && s1.[i] = s2.[i] then loop (i+1) else i
  loop 0

let sharedSuffixLength (s1:string) (s2:string) =
  let rec loop i =
    if i < s1.Length && i < s2.Length && s1.[s1.Length-i-1] = s2.[s2.Length-i-1] then loop (i+1) else i
  loop 0

let (!!) ed = { Edit = ed; Expansion = None }

let suggestRowFilters trigger loc current =
  let s = match current with String s -> s | Number n -> string n
  let colEquals cond = Record("x-formula", OrdList.ofList [
    "op", Reference(Absolute, [Field "$builtins"; Field cond ])
    "left", ps s
    "right", Reference(Relative, [DotDot; DotDot; Field loc.Field])
  ])
  let filterEds cond = [
    !!RecordAdd([All], "$cond", None, None, colEquals cond)
    { Edit = ListDelete([], "0"); 
      Expansion = Some { Condition = [Field "$cond" ]; 
      Target = [All]; Prefix = [Index "0"] } }
    !!RecordDelete(UpdateReferences, [All], "$cond") ]
  let recms = [
    { Icon = "fa-circle-xmark"; Title = "Delete rows by value"; EditType = "edrows"; 
      Description = $"Delete rows with value `{s}' in column `{loc.Field}'"; 
      Code = CodeBuilder.filterRows "equals" loc.Field s
      Edits = filterEds "equals" }
    { Icon = "fa-circle-check"; Title = "Keep rows by value"; EditType = "edrows"
      Description = $"Keep only rows with value `{s}' in column `{loc.Field}'"
      Code = CodeBuilder.filterRows "nequals" loc.Field s
      Edits = filterEds "nequals" } ]
  trigger(GridRecommend(loc.CellId, "edrows", recms))


let inferValueEdit trigger flds loc prev current =
  match prev, current with
  | String(sp), String(sc) ->
      let prefix = sharedPrefixLength sp sc
      let suffix = sharedSuffixLength sp sc
      let olds = sp.[prefix .. sp.Length-suffix-1]
      let news = sc.[prefix .. sc.Length-suffix-1]
      let recm =
        if olds = news then [] else
        [ { Icon = "fa-pencil"; Title = "Replace string in column"; EditType = "replace"
            Code = CodeBuilder.replaceString loc.Field olds news
            Description = $"Replace `{olds}' with `{news}' in column `{loc.Field}'"; Edits = [
              !!PrimitiveEdit([All; Field loc.Field],"replace",Some $"{olds}/{news}") ] } 
          { Icon = "fa-pencil"; Title = "Replace string in all columns"; EditType = "replace"
            Code = CodeBuilder.replaceString "*" olds news
            Description = $"Replace `{olds}' with `{news}' in all columns"; Edits = [
              for fld in flds -> !!PrimitiveEdit([All; Field fld],"replace",Some $"{olds}/{news}") ] } ]
      trigger(GridRecommend(loc.CellId, "replace", recm))
  | _ -> ()

let suggestHeaderEdits trigger flds loc oldf newf =
  let recms = [
    if oldf <> newf then 
      { Icon = "fa-i-cursor"; Title = "Rename columns"; EditType = "headered"
        Code = CodeBuilder.renameCol oldf newf
        Description = $"Rename column `{oldf}' to `{newf}'"; Edits = [
          !!RecordRenameField(UpdateReferences, [All], oldf, newf) ] }
    { Icon = "fa-rectangle-xmark"; Title = "Drop columns"; EditType = "headered"
      Code = CodeBuilder.dropCol oldf
      Description = $"Drop column `{oldf}'"; Edits = [
        !!RecordDelete(UpdateReferences, [All], oldf) ] }
    for c in Seq.distinct oldf do 
      if not(System.Char.IsLetterOrDigit(c)) then 
        { Icon = "fa-scissors"; Title = "Split column by delimiter"; EditType = "headered"
          Code = CodeBuilder.splitCol oldf c
          Description = $"Split column `{oldf}' by delimiter `{c}'"; Edits = [
            let newCols = oldf.Split(c)
            let fldAfter = flds |> List.skipWhile ((<>) oldf) |> List.tail |> List.tryHead
            for i in 1 .. newCols.Length - 1 do
              let newCol = newCols.[i] 
              let prev = if i = 1 then Some oldf else Some newCols.[i-1]
              let next = if i = newCols.Length - 1 then fldAfter else None
              !!RecordAdd([All], newCol, prev, next, Primitive(String ""))
              !!Copy(UpdateReferences, [All; Field newCol], [All; Field oldf])
              !!PrimitiveEdit([All; Field newCol],"take-by",Some $"{c}/{i}")
            !!RecordRenameField(UpdateReferences, [All], oldf, newCols.[0])
            !!PrimitiveEdit([All; Field newCols.[0]],"take-by",Some $"{c}/0")
          ] } 
    ]
  trigger(GridRecommend(loc.CellId, "headered", recms))


let renderGridEditorCell trigger state flds cell loc v =
  let s = renderPrimitive v
  let v = getPrimitive v
  if state.EditingGridPath.TryFind(cell.Id) <> Some(Some loc) then text s
  else
    let s, parse = parseFormat v
    h?input [
      "type" => "text"
      "value" => s
      "keyup" =!> fun el evt ->
        let ke = unbox<KeyboardEvent> evt
        let ie = unbox<HTMLInputElement> el
        match ke.key, parse ie.value with
        | ("Enter" | "Escape"), _ -> trigger(EditGrid(cell.Id, None))
        | _, Some p ->
            inferValueEdit trigger flds loc v p
            suggestRowFilters trigger loc p
        | _ -> () ] []

let renderGridEditorColumnHeader trigger state flds cell loc f =
  if state.EditingGridPath.TryFind(cell.Id) <> Some(Some loc) then text f
  else
    h?input [
      "type" => "text"
      "value" => f
      "keyup" =!> fun el evt ->
        let ke = unbox<KeyboardEvent> evt
        let ie = unbox<HTMLInputElement> el
        match ke.key, ie.value with
        | ("Enter" | "Escape"), _ -> trigger(EditGrid(cell.Id, None))
        | _, nf -> suggestHeaderEdits trigger flds loc f nf ] []

let renderGridEditorHeader trigger state cell loc name =
  let display = if name = "" then "(untitled)" else name
  if state.EditingGridPath.TryFind(cell.Id) <> Some(Some loc) then text display
  else
    h?input [
      "type" => "text"
      "value" => name
      "keyup" =!> fun el evt ->
        let ke = unbox<KeyboardEvent> evt
        let ie = unbox<HTMLInputElement> el
        match ke.key, ie.value with
        | "Enter", nn -> 
            trigger(ApplyEdits("rename", [ RecordAdd([Field cell.Id], "name", None, None, Primitive(String nn)) ]))
            trigger(UpdateGridState(cell.Id))
            trigger(EditGrid(cell.Id, None))
        | "Escape", _ -> trigger(EditGrid(cell.Id, None)) 
        | _ -> () ] []

let renderGridEditor trigger state cell (table:OrdList.OrdList<_, _>) = 
    Log.logOp "apprender" $"renderTableEditor - {table.Members.Count} rows" <| fun () -> [
  let name = match getGridState cell.Id state with Some(_, n, _, _) -> n | _ -> ""
  let flds = getTableHeaders table
  h?div ["class" => "table-caption"] [ 
    let loc = { CellId=cell.Id; Field=""; RowIndex=None }
    h?span [ "click" =!> fun _ _ -> trigger(EditGrid(cell.Id, Some loc)) ] [ 
      renderGridEditorHeader trigger state cell loc name ] 
  ]
  h?div ["class" => "table-box"] [
    h?table [] [
      h?thead [] [ h?tr [] [
        h?th [] []
        for f in flds do 
          let loc = { CellId=cell.Id; Field=f; RowIndex=None }
          h?th [
            "click" =!> fun _ _ -> 
              suggestHeaderEdits trigger flds loc f f
              trigger(EditGrid(cell.Id, Some loc))
          ] [ renderGridEditorColumnHeader trigger state flds cell loc f ]
      ] ]
      h?tbody [] [
        for idx, obj in getTableRows flds table -> h?tr [] [
          h?th [] [ text idx ]
          for f, v in obj do
            let loc = { CellId=cell.Id; Field=f; RowIndex=Some idx }
            h?td [
              "click" =!> fun _ _ -> 
                inferValueEdit trigger flds loc (getPrimitive v) (getPrimitive v)
                suggestRowFilters trigger loc (getPrimitive v)
                trigger(EditGrid(cell.Id, Some loc))
            ] [ renderGridEditorCell trigger state flds cell loc v ]
        ]
      ]
    ]
  ] ]

let getEditCompletions state cell =
  [ for ref, formula in state.Bindings do
      let fld = match List.last ref with Field f -> f | _ -> failwith "getEditCompletions: Path didn't end with field"
      if "table" = getFormulaType state.Bindings formula && not (fld.StartsWith "unnamed-") then
        "edit " + fld, fun () ->
          let eds =
            [ RecordAdd([Field cell.Id], "target", None, None, Reference(Absolute, ref))
              RecordAdd([Field cell.Id], "edits", None, None, List("edits", OrdList.empty ())) ]
          { ActionName = $"choose edit for {cell.Id}"; ActionEdits = eds; EditPath = None } ]

let textWithCode (s:string) =
  let tos cs = System.String(Array.rev (Array.ofList cs)) |> text
  let quote (s:string) = if s.Trim() <> s || s = "" then $"'{s}'" else s
  let toc cs = h?code [] [ text (quote (System.String(Array.rev (Array.ofList cs)))) ]
  let rec loop acc curacc s =
    match s with 
    | '`'::s -> loop (tos curacc::acc) [] s
    | '\''::s -> loop (toc curacc::acc) [] s
    | c::s -> loop acc (c::curacc) s
    | [] -> (tos curacc)::acc |> List.rev
  loop [] [] (List.ofSeq s)

let renderGridCell trigger state cell =
    Log.logOp "apprender" $"renderCodeCell {cell.Id}" <| fun () ->
  match state.GridCellState.TryFind(cell.Id) with
  | None ->
      h?div [ "class" => "grid-block" ] [
        renderCompletion trigger state [cell.Id] (Some(UpdateGridState(cell.Id))) <|
          getEditCompletions state cell ]
  | Some { Data = Some(_, _, List("table", rows)) } ->
      h?div [ "class" => "grid-container" ] [
        h?div [ "class" => "grid-block" ] 
          (renderGridEditor trigger state cell rows)
        h?div [ "class" => "grid-context" ] [
          let recs = state.GridRecommendations.TryFind(cell.Id) |> Option.defaultValue []
          let eds = getAppliedEditsMetadata cell.Node
          if not (List.isEmpty recs) then
            h?div [ "class" => "panel" ] [
              h?h3 [] [ text "Suggested edits" ]
              h?div [ "class" => "panel-body" ] [
                for recm in recs do
                  h?h4 [] [ h?i ["class" => "fa " + recm.Icon] []; text recm.Title ]
                  h?p [ "class" => "break" ] (textWithCode recm.Description)
                  h?p [ "class" => "action" ] [
                    h?a [ 
                      "href" => "javascript:;" 
                      "click" =!> fun _ _ -> trigger(GridApplyEdit(cell.Id, recm))
                    ] [ h?i ["class" => "fa fa-play"] []; text "apply edit "]]
              ]
            ]
          h?div [ "class" => "panel" ] [            
            h?h3 [] [ text "Applied edits" ]
            h?div [ "class" => "panel-body" ] [              
              if List.isEmpty eds then
                h?p [] [ h?em [] [ text "Click on a column, row or a cell to edit the table and get edit suggestions!" ] ]
              h?ul [] [ 
                for ed in eds -> h?li [] [
                  yield h?i ["class" => $"fa {ed.icon}"] []
                  yield! textWithCode ed.description ] ]
            ]
          ]
          if not (List.isEmpty eds) then
            h?div [ "class" => "panel" ] [            
              h?h3 [] [ text "Actions" ]
              h?div [ "class" => "panel-body" ] [ h?p [] [ 
                h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(GridToCode(cell.Id, cell.NextId)) ] [ 
                  h?i ["class" => $"fa fa-code"] []; text "Insert as code cell" ] ]
              ]
            ]
        ]
      ]
  | Some { Source = (Field srcCell)::_ } ->
      let t e = trigger e; trigger (UpdateGridState cell.Id) 
      renderEvalLink t "evaluate source" srcCell
  | _ ->
      failwith "renderGridCell: No data and invalid source reference"

// --------------------------------------------------------------------------------------
// Grid cells
// --------------------------------------------------------------------------------------

let renderTextCell trigger state cell =
    Log.logOp "apprender" $"renderCodeCell {cell.Id}" <| fun () ->
  let content = 
    match select [Field cell.Id] state.Document with 
    | [ Record(_, content) ] -> content
    | _ -> failwith "renderTextCell: cell not found"
  h?div [ ] [
    if state.SelectedCell = Some cell.Id then 
      h?div [
        "contenteditable" => "true"
        "keyup" =!> fun el evt ->
          let ke = unbox<KeyboardEvent> evt
          let text = (unbox<HTMLDivElement> el).innerText
          if ke.key = "Enter" then
            let ed = RecordAdd([Field cell.Id], uniqueId "p", None, None, Record("p", OrdList.ofList ["value", ps text]))
            trigger(ApplyEdits("edit", [ed]))
        ] [ text "foof" ]
    else 
      h?div [] [ text "foof" ]
  ]
  
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
    h?h3 [] [ text $"Source edits" ]
    h?ol [] (List.map renderEdit (List.rev state.SourceEdits))
    for cell in getNotebookCells state.Document do
      match getGridState cell.Id state with 
      | Some(_, _, _, eds) ->
          h?h3 [] [ text $"Grid edits for {cell.Id}" ]
          h?ol [] (List.map renderEdit (List.rev [ for ed in eds -> mkEd ed.Edit ]))
      | _ -> ()
    for (KeyValue(k,v)) in state.EvaluatedEdits do
      if not (List.isEmpty v) then
        h?h3 [] [ text $"Evaluated for {k}" ]
        h?ol [] (List.map renderEdit (List.rev v))
  ]

// --------------------------------------------------------------------------------------
// Render cells and main
// --------------------------------------------------------------------------------------

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

let render trigger state = h?div [ "id" => "main" ] [
  let cells = getNotebookCells state.Document
  h?div [ "id" => "notebook" ] [
    let firstid = match cells with c::_ -> Some c.Id | _ -> None
    renderAddLinks trigger None firstid

    for cell in cells do h?div [ 
        "class" => $"cell cell-{asCellKindName cell.Kind}" 
        "click" =!> fun _ _ -> trigger(SelectCell (Some cell.Id)) ] [
      renderTitle cell.Kind

      match cell.Kind with
      | ck when state.ViewSource ->
          h?div ["class" => "treedoc"] [
            renderSourceTree state trigger [Field cell.Id] [] cell.Node
          ]
          if ck = CodeCell then
            renderEvalLink trigger "evaluate" cell.Id
      | CodeCell ->
          renderCodeCell trigger state cell
          renderEvalLink trigger "evaluate" cell.Id
      | GridCell ->
          renderGridCell trigger state cell
      | TextCell ->
          renderTextCell trigger state cell
      
      renderAddLinks trigger (Some cell.Id) cell.NextId
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

  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]}]"""
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-c842cd9e"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",10]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",100]]}]"""

  // incremental evaluation demo using math.random
  let random = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-c842cd9e"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","min"],["node",10]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-c842cd9e"]]}],["field","max"],["node",100]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-c842cd9e"],["new","nf"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","nf"]]}],["field","min"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-d2aa98a3"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math"]}],["pred","nf"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","math","random"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","min"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","nf"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","max"],["node",0]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-d2aa98a3"]]}],["field","max"],["node",100]]}]"""

  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]}]"""
  let traffic = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-a3d603f1"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railTable"]}],["pred","railTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",":"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node","0"]]}]"""
  let traffic2 = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7a7a0dc"],["node","eurostat/sf_aviaca.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7a7a0dc"],["new","aviaFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-7588a399"],["node",""],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-7588a399"],["new","railFile"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","railFile"],["node","eurostat/sf_railvi.tsv"],["pred","aviaFile"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-52a1d32c"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","railFile"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-52a1d32c"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-52a1d32c"],["new","aviaTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","aviaTable"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","aviaFile"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-719ef4da"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}],["pred","aviaTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-719ef4da"]]}],["field","file"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railFile"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-719ef4da"],["new","railTable"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-a3d603f1"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","railTable"]}],["pred","railTable"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","substring"],["node",":"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","replacement"],["node","0"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node","fof"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-a3d603f1"]]}],["field","column"],["node","freq,unit,accident,victim,pers_cat,geo\\\\TIME_PERIOD"]]}]"""

  // with no edits
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]}]"""
  // with clean 
  let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Rename columns"],["icon","fa-i-cursor"],["description","Rename column `freq,unit,victim,c_regis,geo\\TIME_PERIOD' to `freq,unit,victim,c_regis,geo'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","rename"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["old","freq,unit,victim,c_regis,geo\\TIME_PERIOD"],["new","freq,unit,victim,c_regis,geo"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo\\TIME_PERIOD"],["new","freq,unit,victim,c_regis,geo"],["refs","update"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Split column by delimiter"],["icon","fa-scissors"],["description","Split column `freq,unit,victim,c_regis,geo' by delimiter `,'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","split"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","freq,unit,victim,c_regis,geo"],["by",","]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","unit"],["node",""],["pred","freq,unit,victim,c_regis,geo"]]}],["1",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["2",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["op","take-by"],["arg",",/1"]]}],["3",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","victim"],["node",""],["pred","unit"]]}],["4",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["5",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["op","take-by"],["arg",",/2"]]}],["6",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","c_regis"],["node",""],["pred","victim"]]}],["7",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["8",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["op","take-by"],["arg",",/3"]]}],["9",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","geo"],["node",""],["pred","c_regis"],["succ","2006"]]}],["10",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["11",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["op","take-by"],["arg",",/4"]]}],["12",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo"],["new","freq"],["refs","update"]]}],["13",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq"]]}],["op","take-by"],["arg",",/0"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `freq'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","freq"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","freq"]]}]]}]]}],["index","2"],["pred","1"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `unit'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","unit"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","unit"]]}]]}]]}],["index","3"],["pred","2"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `victim'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","victim"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","victim"]]}]]}]]}],["index","4"],["pred","3"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Keep rows by value"],["icon","fa-circle-check"],["description","Keep only rows with value `EU27_2020' in column `c_regis'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","c_regis"],["cond","nequals"],["value","EU27_2020"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","nequals"]}],["left","EU27_2020"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","c_regis"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","5"],["pred","4"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `EU27_2020' in column `geo'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","geo"],["cond","equals"],["value","EU27_2020"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","EU27_2020"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","6"],["pred","5"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `EU28' in column `geo'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","geo"],["cond","equals"],["value","EU28"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","EU28"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","7"],["pred","6"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in all columns"],["icon","fa-pencil"],["description","Replace ` p' with `' in all columns"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","*"],["old"," p"],["new",""]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["op","replace"],["arg"," p/"]]}],["1",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["op","replace"],["arg"," p/"]]}],["2",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2006"]]}],["op","replace"],["arg"," p/"]]}],["3",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2007"]]}],["op","replace"],["arg"," p/"]]}],["4",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2008"]]}],["op","replace"],["arg"," p/"]]}],["5",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2009"]]}],["op","replace"],["arg"," p/"]]}],["6",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2010"]]}],["op","replace"],["arg"," p/"]]}],["7",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2011"]]}],["op","replace"],["arg"," p/"]]}],["8",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2012"]]}],["op","replace"],["arg"," p/"]]}],["9",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2013"]]}],["op","replace"],["arg"," p/"]]}],["10",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2014"]]}],["op","replace"],["arg"," p/"]]}],["11",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2015"]]}],["op","replace"],["arg"," p/"]]}],["12",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2016"]]}],["op","replace"],["arg"," p/"]]}],["13",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2017"]]}],["op","replace"],["arg"," p/"]]}],["14",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2018"]]}],["op","replace"],["arg"," p/"]]}],["15",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2019"]]}],["op","replace"],["arg"," p/"]]}],["16",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2020"]]}],["op","replace"],["arg"," p/"]]}],["17",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}],["18",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}],["19",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","8"],["pred","7"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `OTH' in column `geo'"],["code",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-hole","nodes":[]}],["column","geo"],["cond","equals"],["value","OTH"]]}],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","OTH"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","9"],["pred","8"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-6845c1f0"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c3"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-6845c1f0"]]}],["field","unnamed-6babe71b"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","replace"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","filter"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","drop"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","split"]}],["inst",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","rename"]}],["inst",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","avia"]}],["old","freq,unit,victim,c_regis,geo\\TIME_PERIOD"],["new","freq,unit,victim,c_regis,geo"]]}],["column","freq,unit,victim,c_regis,geo"],["by",","]]}],["column","freq"]]}],["column","unit"]]}],["column","victim"]]}],["column","c_regis"],["cond","nequals"],["value","EU27_2020"]]}],["column","geo"],["cond","equals"],["value","EU27_2020"]]}],["column","geo"],["cond","equals"],["value","EU28"]]}],["column","*"],["old"," p"],["new",""]]}],["column","geo"],["cond","equals"],["value","OTH"]]}]]}]"""

  
  // with some edits
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","2"],["pred","1"]]}]"""
  // with some edits and code ref 
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","2"],["pred","1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","name"],["node","foof"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-f2d15d6c"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c3"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"]]}],["field","unnamed-b6b93bc8"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c3","foof"]}]]}]"""
  // ..and with sum
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","2"],["pred","1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","name"],["node","foof"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-f2d15d6c"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c3"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"]]}],["field","unnamed-b6b93bc8"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c3","foof"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"],["1","unnamed-b6b93bc8"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"],["1","unnamed-b6b93bc8"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","table","sum"]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"]]}],["old","unnamed-b6b93bc8"],["new","totals"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"]]}],["field","unnamed-f346076d"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","vis"]}],["pred","totals"]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"],["1","unnamed-f346076d"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"],["1","unnamed-f346076d"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","vis","bar"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-f2d15d6c"],["1","unnamed-f346076d"]]}],["field","data"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-f2d15d6c","totals"]}]]}]"""

  // with more edits
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","2"],["pred","1"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Rename columns"],["icon","fa-i-cursor"],["description","Rename column `freq,unit,victim,c_regis,geo\\TIME_PERIOD' to `freq,unit,victim,c_regis,geo'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo\\TIME_PERIOD"],["new","freq,unit,victim,c_regis,geo"],["refs","update"]]}]]}]]}],["index","3"],["pred","2"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Split column by delimiter"],["icon","fa-scissors"],["description","Split column `freq,unit,victim,c_regis,geo' by delimiter `,'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","unit"],["node",""],["pred","freq,unit,victim,c_regis,geo"]]}],["1",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["2",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["op","take-by"],["arg",",/1"]]}],["3",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","victim"],["node",""],["pred","unit"]]}],["4",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["5",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["op","take-by"],["arg",",/2"]]}],["6",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","c_regis"],["node",""],["pred","victim"]]}],["7",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["8",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["op","take-by"],["arg",",/3"]]}],["9",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","geo"],["node",""],["pred","c_regis"],["succ","2006"]]}],["10",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["11",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["op","take-by"],["arg",",/4"]]}],["12",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo"],["new","freq"],["refs","update"]]}],["13",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq"]]}],["op","take-by"],["arg",",/0"]]}]]}]]}],["index","4"],["pred","3"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `freq'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","freq"]]}]]}]]}],["index","5"],["pred","4"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `unit'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","unit"]]}]]}]]}],["index","6"],["pred","5"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `victim'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","victim"]]}]]}]]}],["index","7"],["pred","6"]]}]"""
  // full clean
  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","unnamed-89855e93"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","inst"],["fld","x-formula"],["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["refs","keep"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node",""]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","unnamed-89855e93"]]}],["field","file"],["node","eurostat/sf_railvi.tsv"]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","unnamed-89855e93"],["new","rail"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","rail"]]}],["field","file"],["node","eurostat/sf_railvi_totalkil.tsv"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","target"],["node",{"kind":"reference","refkind":"absolute","selectors":["cell-c2","rail"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"]]}],["field","edits"],["node",{"kind":"list","tag":"edits","nodes":[]}]]},{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["old","rail"],["new","avia"],["refs","update"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","avia"]]}],["field","file"],["node","eurostat/sf_aviaca_eukil.tsv"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","1"],["pred","0"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace ` p' with `' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg"," p/"]]}]]}]]}],["index","2"],["pred","1"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Rename columns"],["icon","fa-i-cursor"],["description","Rename column `freq,unit,victim,c_regis,geo\\TIME_PERIOD' to `freq,unit,victim,c_regis,geo'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo\\TIME_PERIOD"],["new","freq,unit,victim,c_regis,geo"],["refs","update"]]}]]}]]}],["index","3"],["pred","2"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Split column by delimiter"],["icon","fa-scissors"],["description","Split column `freq,unit,victim,c_regis,geo' by delimiter `,'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","unit"],["node",""],["pred","freq,unit,victim,c_regis,geo"]]}],["1",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["2",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","unit"]]}],["op","take-by"],["arg",",/1"]]}],["3",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","victim"],["node",""],["pred","unit"]]}],["4",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["5",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","victim"]]}],["op","take-by"],["arg",",/2"]]}],["6",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","c_regis"],["node",""],["pred","victim"]]}],["7",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["8",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","c_regis"]]}],["op","take-by"],["arg",",/3"]]}],["9",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","geo"],["node",""],["pred","c_regis"],["succ","2006"]]}],["10",{"kind":"record","tag":"x-edit-copy","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["source",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq,unit,victim,c_regis,geo"]]}],["refs","update"]]}],["11",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","geo"]]}],["op","take-by"],["arg",",/4"]]}],["12",{"kind":"record","tag":"x-edit-renamefld","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["old","freq,unit,victim,c_regis,geo"],["new","freq"],["refs","update"]]}],["13",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","freq"]]}],["op","take-by"],["arg",",/0"]]}]]}]]}],["index","4"],["pred","3"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `freq'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","freq"]]}]]}]]}],["index","5"],["pred","4"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `unit'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","unit"]]}]]}]]}],["index","6"],["pred","5"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Drop columns"],["icon","fa-rectangle-xmark"],["description","Drop column `victim'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","victim"]]}]]}]]}],["index","7"],["pred","6"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `EU27_2020' in column `c_regis'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","EU27_2020"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","c_regis"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","8"],["pred","7"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `OTH' in column `geo'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","OTH"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","9"],["pred","8"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `EU27_2020' in column `geo'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","EU27_2020"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","10"],["pred","9"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Delete rows by value"],["icon","fa-circle-xmark"],["description","Delete rows with value `EU28' in column `geo'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["field","$cond"],["node",{"kind":"record","tag":"x-formula","nodes":[["op",{"kind":"reference","refkind":"absolute","selectors":["$builtins","equals"]}],["left","EU28"],["right",{"kind":"reference","refkind":"relative","selectors":["..","..","geo"]}]]}]]}],["1",{"kind":"record","tag":"x-expandable-edit","nodes":[["condition",{"kind":"reference","refkind":"relative","selectors":["$cond"]}],["prefix",{"kind":"reference","refkind":"absolute","selectors":["#0"]}],["target",{"kind":"reference","refkind":"absolute","selectors":["*"]}],["edit",{"kind":"record","tag":"x-edit-listdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["index","0"]]}]]}],["2",{"kind":"record","tag":"x-edit-recdelete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"]]}],["refs","update"],["field","$cond"]]}]]}]]}],["index","11"],["pred","10"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace `:' with `0' in column `2020'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2020"]]}],["op","replace"],["arg",":/0"]]}]]}]]}],["index","12"],["pred","11"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace `:' with `0' in column `2021'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2021"]]}],["op","replace"],["arg",":/0"]]}]]}]]}],["index","13"],["pred","12"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace `:' with `0' in column `2022'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2022"]]}],["op","replace"],["arg",":/0"]]}]]}]]}],["index","14"],["pred","13"]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c3"],["1","edits"]]}],["node",{"kind":"record","tag":"transform","nodes":[["title","Replace string in column"],["icon","fa-pencil"],["description","Replace `:' with `0' in column `2023'"],["edits",{"kind":"list","tag":"edits","nodes":[["0",{"kind":"record","tag":"x-edit-primitive","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","*"],["1","2023"]]}],["op","replace"],["arg",":/0"]]}]]}]]}],["index","15"],["pred","14"]]}]"""

  //let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-1be7bdf1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]}]"""

  //let json = traffic2
  let readJsonOps json =
    List.collect (Represent.unrepresent >> List.map fst) (Serializer.nodesFromJsonString json)

  let initial =
    { DisplayMenuPath = None; SelectedCell = None; ViewSource = false; EditingBindingPath = None; GridEvaluatedEdits = Map.empty
      SourceEdits = readJsonOps json; EvaluatedEdits = Map.empty; ShowHistory = false; EditingGridPath = Map.empty
      Document = rcd "notebook"; EditingValuePath = None; Bindings = []; DataFiles = Map.empty; GridCellState = Map.empty
      GridRecommendations = Map.empty }
    |> updateDocument


  let updateGridCells trigger doc = 
    let cells = match doc with Record(_, cells) -> cells |> OrdList.toListUnordered | _ -> []
    let gridIds = cells |> List.choose(function cellId, Record("cell-grid", _) -> Some cellId | _ -> None)
    for gi in gridIds do trigger(UpdateGridState gi)

  let asyncRequest file =
    Async.FromContinuations(fun (cont, econt, ccont) ->
      let req = XMLHttpRequest.Create()
      req.addEventListener("load", fun _ -> cont req.responseText)
      req.``open``("GET", file)
      req.send())

  let readTsv (s:string) =
    let lines = s.Trim().Replace("\r", "").Split('\n')
    let cols = lines.[0].Split('\t') |> Array.map (fun c -> c.Trim())
    let rows = lines.[1..] |> Seq.map (fun l ->
      let data = l.Split('\t') |> Array.map (fun s -> Primitive(parsePrimitive(s.Trim())))
      let fields = Seq.zip cols data |> List.ofSeq |> OrdList.ofList
      Record("row", fields) ) |> List.ofSeq
    List("table", OrdList.ofList (List.mapi (fun i v -> string i, v) rows))

  let loadData trigger = async {
    let data = [ "eurostat/sf_aviaca.tsv"; "eurostat/sf_railvi.tsv"; "eurostat/sf_railvi_totalkil.tsv"; "eurostat/sf_aviaca_eukil.tsv" ]
    let! tsvs = [ for d in data -> asyncRequest $"/data/{d}" ] |> Async.Parallel
    let dataFiles = Map.ofSeq (Seq.zip data (Seq.map readTsv tsvs))
    trigger(LoadData dataFiles)
    trigger(Evaluate("cell-c2")) // REMOVE THIS
    updateGridCells trigger initial.Document // DTTO
    }

  let start () =
    let trigger, _, _ = createVirtualDomApp "out" initial render update
    updateGridCells trigger initial.Document
    loadData trigger |> Async.StartImmediate
    Browser.Dom.window.onkeydown <- fun e ->
      if e.altKey && e.key = "u" then
        e.preventDefault(); trigger(ToggleViewSource)
      if e.altKey && e.key = "h" then
        e.preventDefault(); trigger(ToggleShowHistory)
      if e.altKey && e.key = "z" then
        e.preventDefault(); trigger(UndoLastEdit)
