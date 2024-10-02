namespace Tbd

module List = 
  let foldi f st lst = List.indexed lst |> List.fold f st

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

  let foldNested f st l = List.fold f st (List.concat l)

  let indexedNested l = 
    [ let mutable n = -1
      for g in l -> [ for v in g do n <- n + 1; yield n, v ] ]

  let revNested l = 
    List.rev (List.map List.rev l)

  // indexedNested [[0;0;0];[0;0]]