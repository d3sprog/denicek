module Tbd.App

open Tbd.Html
open Tbd.Doc

let rec renderNode pid nd = 
  let nd = mostEvalauted nd
  let pid = $"{pid}_{nd.ID}"
  h?(nd.Tag) [ "id" => pid ] [
    match nd.Expression with 
    | Record(_, nds) -> 
        for a in nds -> renderNode pid a
    | Reference(sel) -> yield text (sprintf "$(%A)" sel)
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

let render trigger doc = 
  h?div [] [
    h?button ["click" =!> fun _ _ -> trigger() ] [text "Evaluate!"]
    renderNode "" doc
  ]

let state = doc
let e d = evaluate d d 

let update doc evt = 
  printfn "Evaluate!"
  let doc' = 
    doc 
      |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e
      |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e
  if doc <> doc' then printfn "Not equal?"
  doc'

createVirtualDomApp "out" state render update |> ignore