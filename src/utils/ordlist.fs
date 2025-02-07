namespace Denicek

// --------------------------------------------------------------------------------------
// Ordered list inspired by MRDT list that keeps order of its members
// using an "occurs before" relation.
// --------------------------------------------------------------------------------------

module rec OrdList = 

  type OrdList<'K, 'V when 'K : comparison> = 
    { Members : Map<'K, 'V> 
      Order : Map<'K, 'K> }
    interface System.Collections.Generic.IEnumerable<'K * 'V> with
      member x.GetEnumerator() = (OrdList.toSeq x : seq<_>).GetEnumerator()
      member x.GetEnumerator () = (OrdList.toSeq x : System.Collections.IEnumerable).GetEnumerator()

  // When turning OrdList into sorted list, we want to keep items that
  // "occur before" just after each other (to avoid interleaving unrelated
  // things). Do this by building a tree and DFS
  
  type OrdTree<'K when 'K : comparison> = OrdNode of Map<'K, OrdTree<'K>>
  
  let orderPath o ol = 
    let rec loop acc o = 
      match ol.Order.TryFind o with 
      | Some v -> loop (v::acc) v
      | _ -> acc
    loop [o] o

  let rec orderTreeAdd path (OrdNode nds) =
    match path with 
    | [] -> (OrdNode nds)
    | x::xs when nds.ContainsKey x ->
        OrdNode (nds.Add(x, orderTreeAdd xs nds.[x]))
    | x::xs ->
        OrdNode (nds.Add(x, orderTreeAdd xs (OrdNode Map.empty)))
    
  let getOrderTree ol = 
    ol.Members |> Seq.fold (fun ord (KeyValue(k, v)) -> orderTreeAdd (orderPath k ol) ord) (OrdNode Map.empty)

  let toList ol =
    let rec loop acc (OrdNode nds) = 
      nds |> Seq.fold (fun acc (KeyValue(k, sub)) ->
        let acc = if ol.Members.ContainsKey(k) then (k, ol.Members.[k])::acc else acc
        loop acc sub) acc
    loop [] (getOrderTree ol) |> List.rev

  // Various other operations for working with OrdTrees

  let toSeq ol =
    toList ol |> Seq.ofList
  
  let neqAdd (k, v) (m:Map<_, _>) = 
    if k <> v then m.Add(k, v) else m

  let toListUnordered ol = 
    ol.Members |> Map.toList

  let mapValuesUnordered f ol = 
    { ol with Members = ol.Members |> Map.map f }

  let mapValues f ol = 
    let members = ol |> toSeq |> Seq.map (fun (k, v) -> k, f k v) |> Map.ofSeq
    { ol with Members = members }

  let rec after k1 k2 ol = 
    match ol.Order.TryFind k1 with 
    | Some v -> k2 = v || after v k2 ol
    | _ -> false

  let fold f st ol = 
    ol |> toSeq |> Seq.fold f st 

  let add (k, v) pred ol = 
    match pred with 
    | Some pred -> { Members = ol.Members.Add(k, v); Order = ol.Order |> neqAdd (k, pred) }
    | None -> { Members = ol.Members.Add(k, v); Order = ol.Order }

  let tryFindPred k ol = 
    ol.Order.TryFind(k)

  let tryFindSucc k ol = 
    ol.Order |> Seq.tryPick (fun (KeyValue(succ, key)) -> if k = key then Some succ else None)

  let insert (k, v) pred succ ol = 
    let nmembers = ol.Members.Add(k, v)
    let norder = match pred with None -> ol.Order | Some pred -> ol.Order |> neqAdd (k, pred)
    let norder = match succ with None -> norder | Some succ -> norder |> neqAdd (succ, k)
    { Members = nmembers; Order = norder }

  let tryLastKey ol = 
    let mutable lk = None
    for k in ol.Members.Keys do
      if lk.IsNone || lk.IsSome && after k lk.Value ol then lk <- Some k
    lk

  let empty = { Members = Map.empty; Order = Map.empty }

  let remove k ol = 
    if not(ol.Members.ContainsKey(k)) then ol else 
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

// --------------------------------------------------------------------------------------
// Type alias in the global namespace
// --------------------------------------------------------------------------------------

type OrdList<'K, 'V when 'K : comparison> = OrdList.OrdList<'K, 'V>
