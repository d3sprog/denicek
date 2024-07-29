module Tbd.Matcher
open Tbd.Doc

let rec matches nd pattern = 
  if (nd.ID <> pattern.ID && pattern.ID <> "*" && pattern.ID <> "#") then None else
  match nd.Expression, pattern.Expression with 
  | _, Record("x-hole", Object, [ rplc ]) ->
      let rplc = rplc |> replace (fun _ innernd -> 
        match innernd with 
        | { Expression = Record("x-match", _, _) } -> Some nd
        | _ -> None)
      Some { rplc with ID = nd.ID }
  | Record(ntag, nty, nnds), Record(ptag, pty, pnds) when nty = pty && ntag = ptag ->
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
          Some { nd with Expression = Record(ntag, nty, newNds) }
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
          Some { nd with Expression = Record(ntag, nty, newNds) }
  | _ -> 
    None

let matchAndReplace doc pattern =
  doc |> replace (fun path nd -> 
    if List.exists (fun s -> s = Field "x-patterns") path then None 
    else matches nd pattern)

let applyMatchers doc = 
  doc 
  |> fold (fun _ nd st ->
    match nd with 
    | { Expression = Record("x-patterns", _, nodes) } -> nodes @ st
    | _ -> st ) []
  |> List.fold matchAndReplace doc
