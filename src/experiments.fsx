#load "doc.fs"
open Tbd.Doc

let init =  rcd "root" "div"

let rendered = 
  opsCore @ refactorListOps
  |> List.fold apply init

// NOTE: Root ID does not appear in path

let pat =
  [
    add [] (rcd "head" "thead")
    add [ Field "head" ] (rcd "*" "td")
    add [ Field "head"; Field "*" ] (rcd "hole" "hole")
    add [ Field "head"; Field "*"; Field "hole" ] (nds "" "td" "hello?")
  ] |> List.fold apply (rcd "*" "table")

let spreadMap f xs =
  let mutable nxs = [ [] ]
  for x in xs do
    match f x with 
    | None -> nxs <- [ for xs in nxs -> x::xs ]
    | Some axs -> nxs <- [ for ax in axs do for xs in nxs-> ax::xs ]
  List.map List.rev nxs

( [ 1 .. 10 ] |> spreadMap (fun x -> 
    if x % 5 = 0 then Some [x*10; x*100]
    elif x % 2 = 0 then Some [x]
    else None) ) =
  [ [1; 2; 3; 4; 50; 6; 7; 8; 9; 100]; [1; 2; 3; 4; 500; 6; 7; 8; 9; 100];
    [1; 2; 3; 4; 50; 6; 7; 8; 9; 1000]; [1; 2; 3; 4; 500; 6; 7; 8; 9; 1000] ]

let rec matches nd pattern = 
  if (nd.ID <> pattern.ID && pattern.ID <> "*") ||
     (nd.Tag <> pattern.Tag && pattern.Tag <> "*") then None else
  match nd.Expression, pattern.Expression with 
  | _, Record(Object, [ { Tag = "hole"; Expression = Record(Object, [ rplc ]) } ]) ->
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

let tbl = select [Field "speakers"] rendered |> List.exactlyOne
matches tbl pat

let matchAndReplace doc pattern =
  doc |> replace false (fun _ nd -> matches nd pattern)

matchAndReplace rendered pat
|> ignore

