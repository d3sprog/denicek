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

  let sharedPrefix l1 l2 = 
    let rec loop acc l1 l2 = 
      match l1, l2 with 
      | v1::l1, v2::l2 when v1 = v2 -> loop (v1::acc) l1 l2
      | _ -> List.rev acc, (l1, l2)
    loop [] l1 l2

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
    (*
  let rec skipNested n list = 
    match list with 
    | _ when n <= 0 -> list
    | []::xss -> skipNested n xss
    | [_]::xss -> skipNested (n-1) xss
    | (_::xs)::xss -> skipNested (n-1) (xs::xss)
    | [] -> failwith "skipNested: insufficient number of elements"

  let rec takeNested n list = 
    let rec loop accg accr n list = 
      let addg g = match g with [] -> accr | _ -> (List.rev g)::accr
      match list with 
      | _ when n <= 0 -> List.rev (addg accg)
      | []::xss -> loop accg accr n xss
      | [x]::xss -> loop [] (addg (x::accg)) (n-1) xss
      | (x::xs)::xss -> loop (x::accg) accr (n-1) (xs::xss)
      | [] -> failwith "takeNested: insufficient number of elements"
    loop [] [] n list

  let rec takeWhileNested f list = 
    let rec loop accg accr list = 
      let addg g = match g with [] -> accr | _ -> (List.rev g)::accr
      match list with 
      | (x::_)::_ when not (f x) -> List.rev (addg accg)
      | [] -> List.rev (addg accg)
      | []::xss -> loop accg accr xss
      | [x]::xss -> loop [] (addg (x::accg)) xss
      | (x::xs)::xss -> loop (x::accg) accr (xs::xss)
    loop [] [] list

  //takeWhileNested (fun x -> x%2=0) [[2;4;6];[8;2];[];[4;3]]
  //takeWhileNested (fun x -> x%2=0) [[2;4;6];[8;2];[];[4;2]]

  let rec truncateNested n list = 
    let rec loop accg accr n list = 
      let addg g = match g with [] -> accr | _ -> (List.rev g)::accr
      match list with 
      | _ when n <= 0 -> List.rev (addg accg)
      | []::xss -> loop accg accr n xss
      | [x]::xss -> loop [] (addg (x::accg)) (n-1) xss
      | (x::xs)::xss -> loop (x::accg) accr (n-1) (xs::xss)
      | [] -> List.rev (addg accg)
    loop [] [] n list

  let sliceNested start finish list = 
    list |> skipNested start |> takeNested (finish - start + 1)

  let sharedPrefixNested l1 l2 = 
    let rec loop accg accr l1 l2 = 
      let addg g = match g with [] -> accr | _ -> (List.rev g)::accr
      match l1, l2 with 
      | []::xss, []::yss -> loop accg accr xss yss
      | [x]::xss, [y]::yss when x = y -> loop [] (addg (x::accg)) xss yss
      | (x::xs)::xss, (y::ys)::yss when x = y -> loop (x::accg) accr (xs::xss) (ys::yss)
      | _ -> List.rev (addg accg), (l1, l2)
    loop [] [] l1 l2

  let collectNested f list =
    let rec appendRev acc xs = 
      match xs with x::xs -> appendRev (x::acc) xs | [] -> acc
    let rec loop accg accr list = 
      let addg g = match g with [] -> accr | _ -> (List.rev g)::accr
      match list with 
      | [] -> List.rev (addg accg)
      | []::xss -> loop accg accr xss
      | [x]::xss -> loop [] (addg (appendRev accg (f x))) xss
      | (x::xs)::xss -> loop (appendRev accg (f x)) accr (xs::xss)
    loop [] [] list

  //collectNested (fun x -> [x;x]) [[1;2];[3;4]]

  let mapNested f l = List.map (List.map f) l

  let foldNested f st l = List.fold f st (List.concat l)

  let indexedNested l = 
    [ let mutable n = -1
      for g in l -> [ for v in g do n <- n + 1; yield n, v ] ]

  let revNested l = 
    List.rev (List.map List.rev l)

  // indexedNested [[0;0;0];[0;0]]
  // sliceNested 3 3 [[1;2];[];[3;4];[];[5;6]]

  *)