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