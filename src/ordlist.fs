namespace Tbd

module rec OrdList = 

  type OrdList<'K, 'V when 'K : comparison> = 
    { Members : Map<'K, 'V> 
      Order : Map<'K, 'K> }
    interface System.Collections.Generic.IEnumerable<'K * 'V> with
      member x.GetEnumerator() = (OrdList.toSeq x : seq<_>).GetEnumerator()
      member x.GetEnumerator () = (OrdList.toSeq x : System.Collections.IEnumerable).GetEnumerator()

  let mapValues f ol = 
    { ol with Members = ol.Members |> Map.map f }

  let rec after k1 k2 ol = 
    match ol.Order.TryFind k1 with 
    | Some v -> k2 = v || after v k2 ol
    | _ -> false

  let toSeq ol =
    let members = ol.Members |> Map.toArray
    members |> Array.sortInPlaceWith (fun (k1, _) (k2, _) -> if after k1 k2 ol then +1 else 0)
    members :> seq<_>

  let toList ol =
    let members = ol.Members |> Map.toArray
    members |> Array.sortInPlaceWith (fun (k1, _) (k2, _) -> if after k1 k2 ol then +1 else 0)
    members |> Array.toList

  let fold f st ol = 
    ol |> toSeq |> Seq.fold f st 

  let add (k, v) pred ol = 
    match pred with 
    | Some pred -> { Members = ol.Members.Add(k, v); Order = ol.Order.Add(k, pred) }
    | None -> { Members = ol.Members.Add(k, v); Order = ol.Order }

  let tryLastKey ol = 
    let mutable lk = None
    for k in ol.Members.Keys do
      if lk.IsNone || lk.IsSome && after k lk.Value ol then lk <- Some k
    lk

  let empty = { Members = Map.empty; Order = Map.empty }

  let remove k ol = 
    let pred = ol.Order.TryFind(k)
    let order = seq {
      for (KeyValue(s, p)) in ol.Order do 
        if pred.IsSome && p = k then yield (s, pred.Value)
        if s <> k && p <> k then yield (s, p) }
    { Members = ol.Members.Remove(k); Order = Map.ofSeq order }

  let withOrder keys ol = 
    { ol with Order = keys |> List.rev |> List.pairwise |> Map.ofList }

  let singleton k v = empty |> add (k, v) None

  let ofList l = 
    { Order = l |> List.map fst |> List.rev |> List.pairwise |> Map.ofList 
      Members = Map.ofList l }

  let renameKey fold fnew ol = 
    let ren k = if k = fold then fnew else k
    let order = seq { for (KeyValue(a, b)) in ol.Order -> ren a, ren b }
    let mems = seq { for (KeyValue(k, v)) in ol.Members -> ren k, v }
    { Order = Map.ofSeq order; Members = Map.ofSeq mems  }

  let (|Find|_|) k ol = 
    ol.Members.TryFind(k)

type OrdList<'K, 'V when 'K : comparison> = OrdList.OrdList<'K, 'V>
