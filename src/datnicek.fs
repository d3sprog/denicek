module Denicek.App.Datnicek

open Denicek
open Denicek.Html
open Denicek.Doc
open Denicek.Demos

// --------------------------------------------------------------------------------------
// Application state
// --------------------------------------------------------------------------------------

type State = 
  { 
    Edits : Edit list
    Document : Node

    SelectedCell : string option
    DisplayMenuPath : string list option
  }

type CellKind = 
  | TextCell
  | CodeCell
  | GridCell

type Event = 
  | ToggleMenu of path:string list option
  | AddCell of CellKind * id:string option * pred:string option * succ:string option
  | SelectCell of string option
  | AddFormula of pred:string option
  | ApplyEdit of string * EditKind
  | Evaluate 

// Helpers

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
  
// Document

let updateDocument state = 
  let doc = Apply.applyHistory (rcd "notebook") state.Edits 
  { state with Document = doc }

let withEdits g state eds = 
  let eds = [ for ed in eds -> { Kind = ed; Dependencies = []; GroupLabel = g } ]
  { state with Edits = state.Edits @ eds } |> updateDocument

let withFullEdits g state eds = 
  let eds = [ for ed in eds -> { ed with GroupLabel = g } ]
  { state with Edits = state.Edits @ eds } |> updateDocument

// Notebook cells

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

// Builtin evaluator

let evaluateBuiltin op args = 
  //failwith $"op={op}; args={args}"
  Primitive(String "thing!")


// Update

let update state trigger evt = 
  match evt with 
  | SelectCell sel when state.SelectedCell = sel -> state
  | SelectCell sel -> { state with SelectedCell = sel }
  | ToggleMenu path -> { state with DisplayMenuPath = path }

  | AddFormula pred ->
      let cell = match state.SelectedCell with Some c -> c | _ -> failwith "update: No selected cell"
      let fid = withUniqueId "var" None
      [ RecordAdd([Field cell], fid, pred, None, rcd "x-formula") 
        RecordAdd([Field cell; Field fid], "op", None, None, ref [Field "$datnicek"; Field "data"])
      ]
      |> withEdits $"add formula to {id}" state

  | AddCell(kind, id, pred, succ) ->
      let id = withUniqueId "cell" id
      [ RecordAdd([], id, pred, succ, rcd $"cell-{asCellKindName kind}") ]
      |> withEdits $"add cell {id}" state
  
  | ApplyEdit(lbl, ed) ->
      [ ed ] |> withEdits lbl state

  | Evaluate ->
      let eds = Eval.evaluateAll evaluateBuiltin state.Document
      eds |> withFullEdits "evaluate" state

// Render

let renderValue nd = 
  match nd with 
  | Primitive(String s) -> text $"\"{s}\""
  | _ -> text "???"

let renderCodeFormula nd = h?span [] [
    match nd with
    | Record("x-formula", args & Lookup(Find "op" (Reference(_, Field "$datnicek"::sels)))) ->
        for (Field sel | Fail "renderCodeFormula" sel) in sels do
          h?span [ "class" => "expr" ] [ text sel ]
        let otherArgs = args |> OrdList.toList |> List.filter (fun (k, _) -> k <> "op")
        if not (List.isEmpty otherArgs) then
          text "("
          for arg, value in otherArgs do
            text $"{arg}="
            renderValue value
          text ")"

    | Record("x-evaluated", Lookup(Find "result" nd)) ->
        renderValue nd

    | _ -> failwith $"renderCodeFormula: Not a formula or missing op: {nd}"
  ]

let renderCompletion trigger state path completions = h?div [ "class" => "dropdown" ] [
    let opened = state.DisplayMenuPath = Some path
    h?button ["click" =!> fun _ _ -> 
      trigger (SelectCell(Some (List.head path)))
      if opened then trigger(ToggleMenu None)
      else trigger (ToggleMenu (Some path)) ] [text "+"]
    if opened then
      h?ul [] [
        for k, f in completions -> h?li [] [ 
          h?a ["href"=>"javascript:;"; "click" =!> fun _ _ -> 
            trigger (f())
            trigger (ToggleMenu None) ] [ text k ]
        ]
      ]
  ]

let renderCodeCell trigger state cell = h?div [] [
    let formulas = getCellFormulas cell.Node
    h?ul [] [
      for fid, formula in formulas do 
        h?li [] [ 
          text fid; text " = "
          renderCodeFormula formula
          renderCompletion trigger state [cell.ID; fid] [
            "load", fun () -> 
              let ed = RecordAdd([Field cell.ID; Field fid], "op", None, None, 
                ref [Field "$datnicek"; Field "data"; Field "load"])
              ApplyEdit("select completion", ed)
            "arg", fun () -> 
              let ed = RecordAdd([Field cell.ID; Field fid], "arg", None, None, 
                Primitive(String "todo"))
              ApplyEdit("select completion", ed)
          ]
        ]
    ]
    renderCompletion trigger state [cell.ID] [
      let lastFormulaId = List.tryLast formulas |> Option.map fst
      "data", fun () -> AddFormula lastFormulaId
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
    link "add text below" "fa-quote-left" (AddCell(TextCell, None, previd, nextid))
    link "add code below" "fa-code" (AddCell(CodeCell, None, previd, nextid))
    link "add grid below" "fa-table" (AddCell(GridCell, None, previd, nextid))
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
      | CodeCell -> renderCodeCell trigger state cell
      | _ -> () // TODO
      renderAddLinks trigger (Some cell.ID) cell.NextID
    ]

    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      let nodes = state.Edits |> List.map (Represent.represent None)
      text (Serializer.nodesToJsonString nodes)
    ]
  ]


module Loader = 
  let jso_ = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]}]"""
  let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c1"],["node",{"kind":"record","tag":"cell-text","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c2"],["node",{"kind":"record","tag":"cell-code","nodes":[]}],["pred","cell-c1"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","cell-c3"],["node",{"kind":"record","tag":"cell-grid","nodes":[]}],["pred","cell-c2"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"]]}],["field","var-cf92e784"],["node",{"kind":"record","tag":"x-formula","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","var-cf92e784"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","var-cf92e784"]]}],["field","op"],["node",{"kind":"reference","refkind":"absolute","selectors":["$datnicek","data","load"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[["0","cell-c2"],["1","var-cf92e784"]]}],["field","arg"],["node","todo"]]}]"""

  let readJsonOps json = 
    List.collect (Represent.unrepresent >> List.map fst) (Serializer.nodesFromJsonString json) 

  let initial = 
    { DisplayMenuPath = None; SelectedCell = None;   
      Edits = readJsonOps json; Document = rcd "notebook" }
    |> updateDocument

  let start () =
    createVirtualDomApp "out" initial render update |> ignore
