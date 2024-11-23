namespace Denicek

// --------------------------------------------------------------------------------------
// Useful active patterns
// --------------------------------------------------------------------------------------

module Patterns =
  let (|As|) v i = (v, i)
  let (|Last|_|) l = match List.rev l with x::xs -> Some x | _ -> None
  let (|ListFind|_|) k = List.tryFind (fst >> (=) k) >> Option.map snd
  let (|Lookup|) args = dict args
  let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, _>) = 
    if d.ContainsKey k then Some(d.[k]) else None
  let (|TryFind|) k (d:System.Collections.Generic.IDictionary<_, _>) = 
    if d.ContainsKey k then Some(d.[k]) else None

// --------------------------------------------------------------------------------------
// Additional functions for the List module
// --------------------------------------------------------------------------------------

module List = 

  let partitionBy sizes list = 
    let mutable list = list
    [ for s in sizes ->
        let res = List.take s list 
        list <- List.skip s list 
        res ]

  let foldCollect (f:'st -> 'a -> 'b list * 'st) st list = 
    let st, acc = List.fold (fun (st, acc) v -> let res, st = f st v in (st, res::acc)) (st, []) list 
    List.collect id (List.rev acc), st

  let dropLast tgt = List.rev (List.tail (List.rev tgt))
  
  let foldi f st lst = List.indexed lst |> List.fold f st

  let filterWithState f init list = 
    list |> List.fold (fun (state, acc) v -> 
      let res, nstate = f state v
      nstate, if res then v::acc else acc) (init, []) 
    |> snd |> List.rev 

  let mapWithState f init list = 
    list |> List.fold (fun (state, acc) v -> 
      let res, nstate = f state v
      nstate, res::acc) (init, []) 
    |> snd |> List.rev 

  let prefixes list = 
    let rec loop prefix acc list = 
      match list with 
      | [] -> List.rev acc
      | x::xs -> loop (x::prefix) (List.rev (x::prefix) :: acc) xs
    loop [] [] list

  let tryReduce f list =
    let rec loop state list =
      match list with 
      | x::xs -> 
          match f x state with 
          | None -> None
          | Some state -> loop state xs
      | [] -> Some state
    match list with 
    | [] -> None
    | x::xs -> loop x xs 

  let sharedPrefix l1 l2 =
    let rec loop acc l1 l2 =
      match l1, l2 with 
      | x1::xs1, x2::xs2 when x1 = x2 -> loop (x1::acc) xs1 xs2
      | _ -> (List.rev acc), (l1, l2)
    loop [] l1 l2

  let chunkBy f list = 
    let rec loop acc gacc gkey list =
      match list with 
      | x::xs when f x = gkey -> loop acc (x::gacc) gkey xs
      | x::xs -> loop ((List.rev gacc)::acc) [x] (f x) xs
      | [] -> (List.rev gacc)::acc |> List.rev
    match list with 
    | x::xs -> loop [] [x] (f x) xs
    | [] -> []
