module Tbd.App

open Tbd.Html
open Tbd.Doc

type State = 
  { Initial : Node 
    Edits : Edit list 
    HighlightedSelector : Selectors option
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
  | Evaluate 
  | MergeEdits of Edit list
  | HighlightSelector of Selectors option

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

let rec renderNode state trigger path pid nd = 
  //let nd = mostEvalauted nd
  let pid = $"{pid}_{nd.ID}"
  h?(nd.Tag) [ 
    "id" => pid 
    "class" => match state.HighlightedSelector with Some s when matches s path -> "hidoc" | _ -> ""
  ] [
    match nd.Expression with 
    | Record(Apply, nds) -> 
        let op = nds |> List.tryFind (fun nd -> nd.ID = "op")
        let args = nds |> List.filter (fun nd -> nd.ID <> "op")
        if op.IsSome then yield renderNode state trigger (path @ [Field "op"]) pid op.Value
        else yield text "@"
        yield text "("
        for i, a in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{a.ID}="
          yield renderNode state trigger (path @ [Field a.ID]) pid a
        yield text ")"
    | Record(List, nds) -> 
        for i, a in Seq.indexed nds -> renderNode state trigger (path @ [Index i]) pid a
    | Record(Object, nds) -> 
        for a in nds -> renderNode state trigger (path @ [Field a.ID]) pid a
    | Reference(sel) -> yield formatSelector state trigger sel
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

let renderEdit state trigger ed = 
  let render n fa sel args = [ 
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
  match ed.Kind with 
  | Append(sel, nd) -> render "append" "fa-at" sel ["node", text (string nd)]
  | EditText(sel, fn) -> render "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
  | Reorder(sel, perm) -> render "reorder" "fa-list-ol" sel ["perm", text (string perm)]
  | Copy(src, tgt) -> render "copy" "fa-copy" tgt ["from", formatSelector state trigger src]
  | WrapRecord(id, tg, typ, sel) -> render "wrap" "fa-regular fa-square" sel ["id", text id; "tag", text tg; "typ", text (string typ)]
  | Replace(sel, nd) -> render "replace" "fa-repeat" sel ["node", text (string nd)]
  | AddField(sel, nd) -> render "addfield" "fa-plus" sel ["node", text (string nd)]
  | UpdateTag(sel, tag) -> render "retag" "fa-code" sel ["tag", text tag]

let render trigger (state:State) = 
  h?div [ "id" => "main" ] [
    h?div [ "id" => "doc" ] [
      renderNode state trigger [] "" state.CurrentDocument
    ]
    h?div [ "id" => "edits" ] [
      h?button ["click" =!> fun _ _ -> trigger Evaluate ] [text "Evaluate!"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ opsBudget)) ] [text "Add budget"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addSpeakerOps)) ] [text "Add speaker"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ fixSpeakerNameOps)) ] [text "Fix name"]
      h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ refactorListOps)) ] [text "Refacor list"]
      h?ol [] [
        for i, ed in Seq.rev (Seq.indexed state.Edits) ->
          h?li [] [             
            h?a 
              [ "class" => if i = state.Location then "sel" else ""
                "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(Show i) ] 
              (renderEdit state trigger ed)
          ]
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
    Location = ops.Length - 1 }

let update (state:State) = function
  | HighlightSelector sel ->
    { state with HighlightedSelector = sel }
  | Evaluate -> 
    let edits = state.FinalDocument |> evaluate
    { state with Edits = state.Edits @ edits }  
  | MergeEdits edits ->
    // TODO: This is wrong way to merge
    { state with Edits = merge state.Edits edits }  
  | Move d ->
    { state with Location = max 0 (min (state.Edits.Length - 1) (state.Location + d)) }
  | Show i ->
    { state with Location = i }

let trigger, _ = createVirtualDomApp "out" state render update
Browser.Dom.window.onkeydown <- fun e -> 
  if e.key = "ArrowUp" then e.preventDefault(); trigger(Move +1)
  if e.key = "ArrowDown" then e.preventDefault(); trigger(Move -1)
