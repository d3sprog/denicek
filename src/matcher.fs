module Tbd.Matcher
open Tbd.Doc

(*
let samplePattern =
  [
    add [] (rcd "head" "thead")
    add [ Field "head" ] (rcd "*" "td")
    add [ Field "head"; Field "*" ] (rcd "hole" "x-hole")
    add [ Field "head"; Field "*"; Field "hole" ] (nds "" "td" "hello?")
  ] |> List.fold apply (rcd "*" "table")

let rec matches nd pattern = 
  if (nd.ID <> pattern.ID && pattern.ID <> "*") ||
     (nd.Tag <> pattern.Tag && pattern.Tag <> "*") then None else
  match nd.Expression, pattern.Expression with 
  | _, Record(Object, [ { Tag = "x-hole"; Expression = Record(Object, [ rplc ]) } ]) ->
      let rplc = rplc |> replace false (fun _ innernd -> 
        if innernd.Tag = "x-match" then Some nd else None)
      Some { rplc with ID = nd.ID }
  | Record(nty, nnds), Record(pty, pnds) when nty = pty ->
      match pnds with 
      | [ { ID = "*"} & pnd ] -> 
          let mutable matched = false
          let newNds = nnds |> List.map (fun nd ->
            match matches nd pnd with 
            | Some repls -> 
                matched <- true
                repls
            | _ -> nd)
          if not matched then None else
          Some { nd with Expression = Record(nty, newNds) }
      | _ ->
          for pnd in pnds do if pnd.ID = "*" then failwith "Only one '*' ID allowed in a pattern!" 
          let pndsLookup = Map.ofList [ for pnd in pnds -> pnd.ID, pnd ]
          let mutable pndsMatched = Map.ofList [ for pnd in pnds -> pnd.ID, false ]
          let newNds = nnds |> List.map (fun nnd -> 
            match pndsLookup.TryFind nnd.ID with 
            | Some pnd -> 
                match matches nnd pnd with 
                | Some repl ->
                    pndsMatched <- pndsMatched.Add(nnd.ID, true)
                    repl
                | _ -> nnd
            | _ -> nnd)
          if not (pndsMatched.Values |> Seq.forall id) then None else
          Some { nd with Expression = Record(nty, newNds) }
  | _ -> None

let matchAndReplace doc pattern =
  doc |> replace false (fun path nd -> 
    if List.exists (fun s -> s = Field "x-patterns") path then None 
    else matches nd pattern)

let applyMatchers doc = 
  doc 
  |> fold (fun _ nd st ->
    match nd with 
    | { Tag = "x-patterns"; Expression = Record(_, nodes) } -> nodes @ st
    | _ -> st ) []
  |> List.fold matchAndReplace doc

*)
let applyMatchers doc = doc