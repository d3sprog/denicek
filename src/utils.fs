namespace Tbd

module Patterns =
  let (|As|) v i = (v, i)
  let (|Last|_|) l = match List.rev l with x::xs -> Some x | _ -> None
  let (|ListFind|_|) k = List.tryFind (fst >> (=) k) >> Option.map snd

module List = 

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

  // filterWithState (fun i v -> 
  //   if i < 3 && v % 2 = 0 then true, i+1
  //   else false, i) 0 [10 .. 20]

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

  // chunkBy snd [1,'a'; 2,'a'; 3,'b'; 4,'c'; 5,'c'; 6,'c'; 7,'d']
  // |> List.map List.length
