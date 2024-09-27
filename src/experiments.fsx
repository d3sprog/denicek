#load "utils.fs" "doc.fs" "demos.fs"
open Tbd
open Tbd.Doc
open Tbd.Demos

let eds = opsCore @ opsBudget

let rec generalizeSelectors sels = 
  let allEmpty = List.forall List.isEmpty sels
  let allCons = List.forall (List.isEmpty >> not) sels
  if allEmpty then Some [] else
  if not allCons then None else
  let heads = List.map List.head sels
  let tails = List.map List.tail sels
  generalizeSelectors tails |> Option.bind (fun tail ->
    heads 
    |> List.tryReduce (fun s1 s2 ->
        match s1, s2 with 
        | _ when s1 = s2 -> Some s1
        | (Index _ | Tag _ | All), (Index _ | Tag _ | All) -> Some All
        | _ -> None)
    |> Option.map (fun head -> head :: tail))

[ [Field "greetings"; Index 1; Field "greeting"]
  [Field "greetings"; Index 0; Field "greeting"] ]
|> generalizeSelectors

select
//getTargetSelectorPrefixes eds

let sample = 
  //opsBaseCounter 
  opsCore
  |> Seq.fold apply (rcd "div")

let fmt loc = (String.concat "." (List.map string (List.rev loc))).PadRight(10)

type LocationModifier = Before | After

let rec loop loc sel nd = seq {
  match nd with 
  | Primitive(String s) -> 
      yield (loc, Before), sel
      yield (loc, After), sel
  | Primitive(Number n) ->
      yield (loc, Before), sel
      yield (loc, After), sel
  | Record(tag, nds) ->
      yield (loc, Before), sel
      for i, (k, v) in Seq.indexed nds do 
        yield! loop (i::loc) (Field k::sel) v
      yield (loc, After), sel
  | List(tag, nds) ->
      yield (loc, Before), sel
      for i, v in Seq.indexed nds do 
        yield! loop (i::loc) (Index i::sel) v
      yield (loc, After), sel
  | Reference _ ->
      yield (loc, Before), sel
      yield (loc, After), sel
  }
  //| Reference of Selectors
    
loop [] [] sample
|> Seq.map (fun ((loc, md), sel) -> (List.rev loc, md), List.rev sel)
|> Seq.iter (printfn "%A")

(*
#load "doc.fs" "matcher.fs"
open Tbd.Matcher

let init =  rcd "root" "div"

let rendered = 
  opsCore @ refactorListOps
  |> List.fold apply init

// NOTE: Root ID does not appear in path

let pat =
  [
    add [] (rcd "head" "thead")
    add [ Field "head" ] (rcd "*" "td")
    add [ Field "head"; Field "*" ] (rcd "*" "x-hole")
    add [ Field "head"; Field "*"; Field "*" ] (rcd "td" "td")
    add [ Field "head"; Field "*"; Field "*"; Field "td" ] (rcd "mq" "marquee")
    add [ Field "head"; Field "*"; Field "*"; Field "td"; Field "mq" ] (rcd "" "x-match")
  ] |> List.fold apply (rcd "*" "table")

let tbl = select [Field "speakers"] rendered |> List.exactlyOne
matches tbl pat
*)