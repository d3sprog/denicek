namespace Tbd

module List = 
  let foldi f st lst = List.indexed lst |> List.fold f st