module Tbd.App

open Tbd.Html
open Tbd.Doc

type State = 
  { Initial : Node 
    Edits : Edit list 
    SelectedNode : string option
    HighlightedSelector : Selectors option
    ControlsLocation : float * float
    HistoryIndex : Map<string, int>
    Location : int }
  member x.CurrentDocument = 
    x.Edits.[0 .. x.Location]
    |> List.fold apply x.Initial
  member x.FinalDocument = 
    x.Edits
    |> List.fold apply x.Initial

type Event = 
  | Show of int
  | Move of int 
  | Evaluate of all:bool
  | MergeEdits of Edit list
  | HighlightSelector of Selectors option
  | SelectNode of option<string * (float * float)>
  | MoveHistory of int 

let formatSelector state trigger sel = 
  let parts = sel |> List.map (function All -> "*" | Index i -> string i | Field f -> f)
  h?a [ 
    "href" => "javascript:;"
    "class" => if state.HighlightedSelector = Some sel then "hisel" else ""
    "mouseover" =!> fun _ _ -> trigger(HighlightSelector(Some sel)) 
    "mouseout" =!> fun _ _ -> trigger(HighlightSelector None) 
  ] [ 
    text ("/" + (String.concat "/" parts))
  ]

let rec formatNode state trigger (nd:Node) = 
  match nd.Expression with 
  | Primitive(Number n) -> text (string n)
  | Primitive(String s) -> text s
  | Reference(sel) -> formatSelector state trigger sel
  | Record(tag, List, nds) -> h?span [] [
        yield text "["
        for i, nd in Seq.indexed nds do 
          if i <> 0 then yield text ", "
          yield formatNode state trigger nd
        yield text "]"
      ]
  | Record(tag, _, nds) -> h?span [] [
        yield text "{"
        for i, nd in Seq.indexed nds do 
          if i <> 0 then yield text ", "
          yield text $"{nd.ID}="
          yield formatNode state trigger nd
        yield text "}"
      ]

let rec getPreviousNode nd i = 
  match nd.Previous with 
  | _ when i = 0 -> nd 
  | Some nd -> getPreviousNode nd (i - 1)
  | None -> nd

let rec renderNode state trigger path pid nd = 
  let (++) s1 s2 = if s1 <> "" then s1 + "_" + s2 else s2
  let nd, historyIndex = 
    match state.HistoryIndex.TryFind(pid) with 
    | Some hist -> getPreviousNode nd hist, hist
    | _ -> nd, 0
  let tag = 
    match nd.Expression with 
    | Record(tag, _, _) -> tag
    | Primitive(Number _) -> "x-prim-num"
    | Primitive(String _) -> "x-prim-str"
    | Reference _ -> "x-ref"
  h?(tag) [ 
    "id" => pid 
    "class" => 
      ( match state.HighlightedSelector with Some s when matches s path -> "hidoc " | _ -> " ") + 
      ( if historyIndex > 0 then "historical" else "")
    "click" =!> fun h e ->     
      e.cancelBubble <- true;
      trigger(SelectNode(Some(pid, (h.offsetLeft(* + h.offsetWidth*), h.offsetTop))))
  ] [
    if state.SelectedNode = Some pid then 
      let x, y = state.ControlsLocation
      let canDown = historyIndex > 0 
      let canUp = nd.Previous.IsSome
      yield h?div ["id" => "hcontrols"; "style" => $"left:{int x}px; top:{int y}px"] [
        h?i [ "class" => "fa fa-circle-chevron-left " + if canDown then "" else "disabled"; 
              "click" =!> fun _ e -> e.cancelBubble <- true; if canDown then trigger(MoveHistory -1) ] []
        h?span ["class"=>"histindex"] [ text (string historyIndex) ]
        h?i [ "class" => "fa fa-circle-chevron-right " + if canUp then "" else "disabled"; 
              "click" =!> fun _ e -> e.cancelBubble <- true; if canUp then trigger(MoveHistory 1) ] []
        h?span [ "class" => "details" ] [ formatNode state trigger nd ]
      ]
    match nd.Expression with 
    | Record(_, Apply, nds) -> 
        let op = nds |> List.tryFind (fun nd -> nd.ID = "op")
        let args = nds |> List.filter (fun nd -> nd.ID <> "op")
        if op.IsSome then yield renderNode state trigger (path @ [Field "op"]) (pid ++ "op") op.Value
        else yield text "@"
        yield text "("
        for i, a in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{a.ID}="
          yield renderNode state trigger (path @ [Field a.ID]) (pid ++ a.ID) a
        yield text ")"
    | Record(_, List, nds) -> 
        for i, a in Seq.indexed nds -> renderNode state trigger (path @ [Index i]) (pid ++ string i) a
    | Record(_, Object, nds) -> 
        for a in nds -> renderNode state trigger (path @ [Field a.ID]) (pid ++ a.ID) a
    | Reference(sel) -> yield formatSelector state trigger sel
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

let renderEdit i state trigger ed = 
  let render n fa sel args = 
    h?li [] [             
      h?a [ 
        "class" => (if i = state.Location then "sel " else " ") + (if ed.IsEvaluated then "eval" else "")
        "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(Show i) 
      ] [ 
        yield h?i [ "class" => "fa " + fa ] [] 
        yield text " "
        yield h?strong [] [ text n ]
        yield text " at "
        yield formatSelector state trigger sel
        yield text " with ("
        for i, (k, v) in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{k} = "
          yield v
        yield text ")"
      ]
    ]
  match ed.Kind with 
  | Append(sel, nd) -> render "append" "fa-at" sel ["node", formatNode state trigger nd]
  | EditText(sel, fn) -> render "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
  | Reorder(sel, perm) -> render "reorder" "fa-list-ol" sel ["perm", text (string perm)]
  | Copy(src, tgt) -> render "copy" "fa-copy" tgt ["from", formatSelector state trigger src]
  | WrapRecord(id, tg, typ, sel) -> render "wrap" "fa-regular fa-square" sel ["id", text id; "tag", text tg; "typ", text (string typ)]
  | Replace(sel, _, nd) -> render "replace" "fa-repeat" sel ["node", formatNode state trigger nd]
  | AddField(sel, nd) -> render "addfield" "fa-plus" sel ["node", formatNode state trigger nd]
  | UpdateTag(sel, tag) -> render "retag" "fa-code" sel ["tag", text tag]
  | UpdateId(sel, id) -> render "updid" "fa-font" sel ["id", text id]

let render trigger (state:State) = 
  h?div [ "id" => "main" ] [
    h?div [ "id" => "doc" ] [
      let doc = Matcher.applyMatchers state.CurrentDocument 
      renderNode state trigger [] "" doc
    ]
    h?div [ "id" => "edits" ] [
      h?button ["click" =!> fun _ _ -> trigger (Evaluate(false)) ] [text "Eval step!"]
      h?button ["click" =!> fun _ _ -> trigger (Evaluate(true)) ] [text "Eval all!"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ opsBudget)) ] [text "Add budget"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addSpeakerOps)) ] [text "Add speaker"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ fixSpeakerNameOps)) ] [text "Fix name"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ refactorListOps)) ] [text "Refacor list"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addTransformOps)) ] [text "Add transformers"]
      h?ol [] [
        for i, ed in Seq.rev (Seq.indexed state.Edits) -> renderEdit i state trigger ed
      ]
    ]
  ]

//let ops = opsCore @ opsExtras
//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
//let ops1 = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))
//let ops = merge ops1 (opsCore @ opsBudget)
//let ops = merge (opsCore @ opsBudget) ops1
let ops = opsCore 

let state = 
  { Initial = rcd "root" "div"
    HighlightedSelector = None
    Edits = ops
    HistoryIndex = Map.empty
    ControlsLocation = 0.0, 0.0
    SelectedNode = None
    Location = ops.Length - 1 }

let update (state:State) = function
  | MoveHistory diff ->
    match state.SelectedNode with 
    | Some nd -> 
        let hist = state.HistoryIndex.TryFind(nd) |> Option.defaultValue 0
        { state with HistoryIndex = state.HistoryIndex.Add(nd, hist + diff) }
    | _ -> state
  | SelectNode(None) ->
    { state with SelectedNode = None }
  | SelectNode(Some(pid, pos)) ->
    { state with SelectedNode = Some(pid); ControlsLocation = pos }
  | HighlightSelector sel ->
    { state with HighlightedSelector = sel }
  | Evaluate true -> 
    let edits = state.FinalDocument |> evaluateAll |> List.ofSeq
    { state with Edits = state.Edits @ edits }
  | Evaluate false -> 
    let edits = state.FinalDocument |> evaluate
    { state with Edits = state.Edits @ edits } 
  | MergeEdits edits ->
    let state = { state with Edits = merge state.Edits edits } 
    { state with Location = min (state.Edits.Length-1) state.Location }
  | Move d ->
    { state with Location = max 0 (min (state.Edits.Length - 1) (state.Location + d)) }
  | Show i ->
    { state with Location = i }

let trigger, _ = createVirtualDomApp "out" state render update
Browser.Dom.window.onclick <- fun e -> 
  trigger(SelectNode None)
Browser.Dom.window.onkeydown <- fun e -> 
  if e.key = "ArrowUp" then e.preventDefault(); trigger(Move +1)
  if e.key = "ArrowDown" then e.preventDefault(); trigger(Move -1)

//trigger (MergeEdits(opsCore @ opsBudget))
//trigger (Evaluate true)
//trigger (Move 100000)
