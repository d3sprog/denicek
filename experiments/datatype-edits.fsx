// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

type Value = 
  | Record of list<string * Value>
  | List of Value list
  | String of string

type Selector = 
  | Field of string
  | All
  | Index of int 
type Selectors = Selector list

let replace f value = 
  let rec loop path value =
    match f path value with 
    | Some res -> res
    | _ -> 
    match value with 
    | Record(attrs) -> 
        Record(List.map (fun (k, v) -> k, loop (path @ [Field(k)]) v) attrs)
    | List(vals) -> 
        List(List.mapi (fun i v -> loop (path @ [Index(i)]) v) vals)
    | String s -> 
        String s
  loop [] value

let fold f st value = 
  let rec loop path st value =
    let st = f path value st 
    match value with 
    | Record(attrs) -> 
        attrs |> List.fold (fun st (k, v) -> 
          loop (path @ [Field(k)]) st v) st
    | List(vals) ->
        vals |> List.indexed |> List.fold (fun st (i, v) -> 
          loop (path @ [Index(i)]) st v) st
    | String s -> 
        st
  loop [] st value

let rec matches p1 p2 = 
  match p1, p2 with 
  | [], [] -> true
  | [], _ | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && matches p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && matches p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> matches p1 p2
  | _ -> failwithf "matches: Incompatible paths %A and %A" p1 p2

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev


// --------------------------------------------------------------------------------------
// Edits
// --------------------------------------------------------------------------------------

type Edit = 
  | EditText of Selectors * (string -> string)
  | Append of Selectors * Value
  | Reorder of Selectors * list<int>
  | Copy of Selectors * Selectors
  | WrapRecord of Selectors * string
  | AddField of Selectors * string * Value


let apply edit doc =
  match edit with
  | Append(sel, value) ->
      replace (fun p el ->
        match el with 
        | List(vals) when matches p sel -> Some(List(vals @ [value])) 
        | _ -> None ) doc
  | Reorder(sel, indices) ->
      replace (fun p el ->
        match el with 
        | List(vals) when matches p sel -> Some(List [ for i in indices -> vals.[i]]) 
        | _ -> None ) doc
  | EditText(sel, f) ->
      replace (fun p el -> 
        match el with 
        | String(s) when matches p sel -> Some(String(f s))
        | _ -> None ) doc
  | WrapRecord(sel, field) ->
      replace (fun p el -> 
        if matches p sel then Some(Record [field, el])
        else None ) doc
  | AddField(sel, f, v) ->
      replace (fun p el -> 
        match el with 
        | Record(attrs) when matches p sel -> Some(Record(attrs @ [f, v]))
        | _ -> None ) doc
  | Copy(sel1, sel2) ->
      let mutable vals = select sel1 doc
      let next () = match vals with h::tl -> vals <- tl; h | [] -> failwith "apply.Copy: Insufficient number of selected elements"
      replace (fun p el -> 
        if matches p sel2 then Some(next())
        else None ) doc
  
// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------

let getSelectors = function
  | EditText(s, _) | Append(s, _) | Reorder(s, _)
  | WrapRecord(s, _) | AddField(s, _, _) -> [s]
  | Copy(s1, s2) -> [s1; s2]

let withSelectors sels = function
  | EditText(_, f) -> EditText(List.exactlyOne sels, f)
  | Append(_, v) -> Append(List.exactlyOne sels, v) 
  | Reorder(_, m) -> Reorder(List.exactlyOne sels, m)
  | WrapRecord(_, f) -> WrapRecord(List.exactlyOne sels, f) 
  | AddField(_, k, v) -> AddField(List.exactlyOne sels, k, v) 
  | Copy(_, _) -> Copy(List.head sels, List.exactlyOne (List.tail sels))


let project e1 e2 = 
  match e2 with 
  | Reorder(sel, ord) -> 
      let rec reorder selOther selReord =
        match selOther, selReord with 
        | All::selOther, All::selReord -> All::(reorder selOther selReord)
        | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(reorder selOther selReord)
        | Field(fo)::_, _ -> selOther
        | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(reorder selOther selReord)
        | Index(io)::selOther, All::selReord -> Index(io)::(reorder selOther selReord)
        | Index(i)::selOther, [] -> Index(List.findIndex ((=) i) ord)::selOther
        | All::selOther, [] -> All::selOther
        | All::selOther, Index(i)::selReorder -> failwith "tricky"
        | Index(io)::_, _ -> selOther
        //failwith "Reorder.All ???"
        | [], _ -> []
      let nsels = getSelectors e1 |> List.map (fun s1 -> reorder s1 sel)
      withSelectors nsels e1
  | WrapRecord(sel, fld) -> 
      let rec reorder selOther selReord =
        match selOther, selReord with 
        | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(reorder selOther selReord)
        | Field(fo)::_, _ -> selOther
        | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(reorder selOther selReord)
        | Index(io)::selOther, All::selReord -> Index(io)::(reorder selOther selReord)
        | selOther, [] -> Field(fld)::selOther
        | Index(io)::_, _ -> selOther
        | All::_, _ -> failwith "Reorder.All ???"
        | [], _ -> []
      let nsels = getSelectors e1 |> List.map (fun s1 -> reorder s1 sel)
      withSelectors nsels e1  
  | _ -> e1

let merge e1s e2s = 
  let e1sUpd = e1s |> List.map (fun e1 -> List.fold project e1 e2s)
  e2s @ e1sUpd

// --------------------------------------------------------------------------------------
// Demo
// --------------------------------------------------------------------------------------

let doc = 
  Record [
    "heading", String "Programming conference 2023"
    "annotation", String "List of people to invite"
    "invitees", List [
      String "Adele Goldberg, adele@xerox.com" 
      String "Margaret Hamilton, hamilton@mit.com"  
      String "Betty Jean Jennings, betty@rand.com" 
    ]
  ]

let people = [ Field "invitees"; All ]
doc |> select people

// Selects all items of the list inside 'invitees':
//
//   [ String "Adele Goldberg, adele@xerox.com";
//     String "Margaret Hamilton, hamilton@mit.com";
//     String "Betty Jean Jennings, betty@rand.com" ]

let jean = [ Field "invitees"; Index(2) ]
doc |> select jean

// Selects the second item from the list inside 'invitees':
//
//   [String "Betty Jean Jennings, betty@rand.com"]


let edits1 = [
  Append([Field("invitees")], String("Ada Lovelace, lovelace@royalsociety.ac.uk"))
  Reorder([Field("invitees")], [3;0;1;2])
]

doc 
|> apply edits1.[0]
|> apply edits1.[1]

// Adds 'Ada Lovelace' as another item and reorder items in the list:
//
//  Record
//    [("heading", String "Programming conference 2023");
//     ("annotation", String "List of people to invite");
//     ("invitees",
//      List
//        [String "Ada Lovelace, lovelace@royalsociety.ac.uk";
//         String "Adele Goldberg, adele@xerox.com";
//         String "Margaret Hamilton, hamilton@mit.com";
//         String "Betty Jean Jennings, betty@rand.com"])]

let edits2 = [
  EditText([Field("invitees"); Index(2)], fun s -> 
    s.Replace("Betty Jean Jennings", "Jean Jennings Bartik"))
]

doc 
|> apply edits2.[0]

// Replace the text (rename) an item in the list by index:
//
//  Record
//    [("heading", String "Programming conference 2023");
//     ("annotation", String "List of people to invite");
//     ("invitees",
//      List
//        [String "Adele Goldberg, adele@xerox.com";
//         String "Margaret Hamilton, hamilton@mit.com";
//         String "Jean Jennings Bartik, betty@rand.com"])]

let edits3 = [
  WrapRecord([Field("invitees"); All], "name")  
  AddField([Field("invitees"); All], "email", String "")  
  Copy([Field("invitees"); All; Field("name")], 
    [Field("invitees"); All; Field("email")])  
  EditText([Field("invitees"); All; Field("name")], 
    fun s -> s.Substring(0, s.IndexOf(',')))
  EditText([Field("invitees"); All; Field("email")], 
    fun s -> s.Substring(s.IndexOf(',')+1).Trim())
]

doc 
|> apply edits3.[0]
|> apply edits3.[1]
|> apply edits3.[2]
|> apply edits3.[3]
|> apply edits3.[4]

// Turn the list of strings into structured representation. First,
// wrap the string value into a record with a single field 'name'
// containing the string. Then add an empty field 'email' and copy
// value from 'name' into 'field' (now we have the same string 
// duplicated). Then drop stuff before and after ',' respectively.
//
// (NOTE: To do this in bidirectional way, we'd need a single operation
// that splits value into two - not copy and then delete parts - but
// it should be doable).
//
//  Record
//    [("heading", String "Programming conference 2023");
//     ("annotation", String "List of people to invite");
//     ("invitees",
//      List
//        [Record
//           [("name", String "Adele Goldberg");
//            ("email", String "adele@xerox.com")];
//         Record
//           [("name", String "Margaret Hamilton");
//            ("email", String "hamilton@mit.com")];
//         Record
//           [("name", String "Betty Jean Jennings");
//            ("email", String "betty@rand.com")]])]

merge (merge edits3 edits2) edits1
|> List.fold (fun doc ed -> apply ed doc) doc

// Produces a list of edits in order edits1, edits2, edits3
// This way, append and edit happens before restructure & it works.
// 
//
// Record
//   [("heading", String "Programming conference 2023");
//    ("annotation", String "List of people to invite");
//    ("invitees",
//     List
//       [Record
//          [("name", String "Ada Lovelace");
//           ("email", String "lovelace@royalsociety.ac.uk")];
//        Record
//          [("name", String "Adele Goldberg");
//           ("email", String "adele@xerox.com")];
//        Record
//          [("name", String "Margaret Hamilton");
//           ("email", String "hamilton@mit.com")];
//        Record
//          [("name", String "Jean Jennings Bartik");
//           ("email", String "betty@rand.com")]])]

merge (merge edits2 edits1) edits3
|> List.fold (fun doc ed -> apply ed doc) doc

// Produces a list of edits in order edits3, edits1, edits2
// This way, adding a new item to the list happens after 
// the restructuring and this does not currently work:
//
// How should this work?? As we 'project' (is that the right term?)
// The 'Append' edit through the 'WrapRecord/AddField/Copy/EditText' edits
// we could apply these to the thing to be 'Append'ed. This sounds
// tricky as we have to transform data in a quite complex way and 
// transform its structure. Alternatively, we could copy the structure
// transforms and append them to the end, applying only on the newly
// inserted element. I wonder what Jonathan's implementation does!?
//
// Record
//   [("heading", String "Programming conference 2023");
//    ("annotation", String "List of people to invite");
//    ("invitees",
//     List
//       [String "Ada Lovelace, lovelace@royalsociety.ac.uk";
//        Record
//          [("name", String "Adele Goldberg");
//           ("email", String "adele@xerox.com")];
//        Record
//          [("name", String "Margaret Hamilton");
//           ("email", String "hamilton@mit.com")];
//        Record
//          [("name", String "Jean Jennings Bartik");
//           ("email", String "betty@rand.com")]])]


// --------------------------------------------------------------------------------------
// RANDOM NOTES
// --------------------------------------------------------------------------------------

(*
Tricky problem that we talked about. Say we have a list of
people with their most favorite things:

[ 
  { "name": "Joe"
    "favorites": [ "Tea"; "Pizza" ] },
  { "name": "Jim"
    "favorites": [ "Coffee"; "Tea" ] }
]

We can select their top 1 most favorite things:

  All; Field("favorites"); Index(0)

But what if we have an edit that switches the order of the favorite
things for the first person of the list:

  Reorder( [ Index(0); Field("favorites"); ]; [1; 0] )

If we merge this with the above, should the above still return
"Tea" and "Coffee", or does the edit change the order and we get
"Pizza" and "Coffee" instead? 

This is probably semantically tricky. Logically speaking, if their
favorite thing changes, it should probably change the result (maybe
this is the difference between structrue change and data change?)
If we wanted we could represent it as something like:

  Index(0); Field("favorites"); Index(1) + 
  Index(~0); Field("favorites"); Index(0)

Maybe 'All' operation should be allowed only for structure/type
transforms but not for data selection/data transforms to avoid such
issues.

*)