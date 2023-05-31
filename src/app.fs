module Tbd.App

open Tbd.Html
open Tbd.Doc

type State = 
  { Initial : Node 
    Edits : Edit list 
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
  | AddEdits of Edit list

let rec renderNode pid nd = 
  //let nd = mostEvalauted nd
  let pid = $"{pid}_{nd.ID}"
  h?(nd.Tag) [ "id" => pid ] [
    match nd.Expression with 
    | Record(_, nds) -> 
        for a in nds -> renderNode pid a
    | Reference(sel) -> yield text (sprintf "$(%A)" sel)
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

let render trigger (state:State) = 
  h?div [ "id" => "main" ] [
    h?div [ "id" => "doc" ] [
      renderNode "" state.CurrentDocument
    ]
    h?div [ "id" => "edits" ] [
      h?button ["click" =!> fun _ _ -> trigger Evaluate ] [text "Evaluate!"]
      h?button ["click" =!> fun _ _ -> trigger (AddEdits addSpeakerOps) ] [text "Add speaker"]
      h?button ["click" =!> fun _ _ -> trigger (AddEdits fixSpeakerNameOps) ] [text "Fix name"]
      h?button ["click" =!> fun _ _ -> trigger (AddEdits refactorListOps) ] [text "Refacor list"]
      h?ol [] [
        for i, ed in Seq.rev (Seq.indexed state.Edits) ->
          h?li [] [             
            h?a 
              [ "class" => if i = state.Location then "sel" else ""
                "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(Show i) ] 
              [ text (string ed) ]
          ]
      ]
    ]
  ]

//let ops = opsCore @ opsExtras
//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
let ops = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))

let state = 
  { Initial = rcd "root" "div"
    Edits = ops
    Location = ops.Length - 1 }

let update (state:State) = function
  | Evaluate -> 
    let edits = state.FinalDocument |> evaluate
    { state with Edits = state.Edits @ edits }  
  | AddEdits edits ->
    // TODO: This is wrong way to merge
    { state with Edits = state.Edits @ edits }  
  | Move d ->
    { state with Location = max 0 (min (state.Edits.Length - 1) (state.Location + d)) }
  | Show i ->
    { state with Location = i }

let trigger, _ = createVirtualDomApp "out" state render update
Browser.Dom.window.document.onkeyup <- fun e -> 
  if e.key = "ArrowUp" then trigger(Move +1)
  if e.key = "ArrowDown" then trigger(Move -1)

