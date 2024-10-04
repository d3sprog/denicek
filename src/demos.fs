module Tbd.Demos
open Tbd
open Tbd.Doc

let ffld f = 
  if f = "" then "=" + System.Convert.ToBase64String(System.Guid.NewGuid().ToByteArray())
  else f

let rcd tag = Record(tag, [])
let lst tag = List(tag, [])
let ref sel = Reference(sel)
let ps s = Primitive(String s)
let pn n = Primitive(Number n)
let nds fld tag s = Record(tag, [ffld fld, Primitive(String s)])
let ndn fld tag n = Record(tag, [ffld fld, Primitive(Number n)])
let ndr fld tag sel = Record(tag, [ffld fld, Reference(sel)])

let ap s n = { Kind = ListAppend(s, ConstSource n) } 
let wr s fld tag = { Kind = WrapRecord(ffld fld, tag, s) }
let wl s tag = { Kind = WrapList(tag, s) }
let ord s l = { Kind = ListReorder(s, l) } 
let ed sel fn f = transformationsLookup.["_" + fn] <- f; { Kind = PrimitiveEdit(sel, "_" + fn) } 
let add sel f n = { Kind = RecordAdd(sel, ffld f, ConstSource n) }
let cp s1 s2 = { Kind = Copy(s2, RefSource s1) }
let tag s t1 t2 = { Kind = UpdateTag(s, t1, t2) }
let uid s id = { Kind = RecordRenameField(s, ffld id) }


let opsBaseCounter = 
  [ 
    add [] "" (nds "title" "h1" "Counter")
    add [] "counter" (rcd "p")
    add [Field "counter"] "" (nds "" "strong" "Count: ")
    add [Field "counter"] "value" (pn 0)
    add [] "inc" (nds "" "button" "Increment")
    add [] "dec" (nds "" "button" "Decrement")
  ]

let opsCounterInc = 
  [
    wr [Field "counter"; Field "value"] "value" "x-formula"
    uid [Field "counter"; Field "value"; Field "value"] "right"
    add [Field "counter"; Field "value"] "left" (pn 1)
    add [Field "counter"; Field "value"] "op" (ref [Field "$builtins"; Field "+"])
  ]

let opsCounterDec = 
  [
    wr [Field "counter"; Field "value"] "value" "x-formula"
    uid [Field "counter"; Field "value"; Field "value"] "right"
    add [Field "counter"; Field "value"] "left" (pn -1)
    add [Field "counter"; Field "value"] "op" (ref [Field "$builtins"; Field "+"])
  ]

let opsCounterHndl = 
  [ yield add [Field "inc"] "click" (lst "x-event-handler")
    for op in opsCounterInc ->
      ap [Field "inc"; Field "click"] (represent op) 
    yield add [Field "dec"] "click" (lst "x-event-handler")
    for op in opsCounterDec ->
      ap [Field "dec"; Field "click"] (represent op) ]

let addSpeakerOps = 
  [ 
    ap [Field "speakers"] (nds "value" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ord [Field "speakers"] [3; 0; 1; 2] 
  ]
  
let fixSpeakerNameOps = 
  [
    ed [Field("speakers"); Index(2); Field("value")] "rename Jean" <| function 
      | (String s) -> String(s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@"))
      | _ -> failwith "fixSpeakerNameOps - wrong primitive"
  ]

let refactorListOps = 
  [
    uid [Field "speakers"; All; Field "value"] "name"
    wr [Field "speakers"; All; Field "name"] "contents" "td"
    
    add [Field "speakers"; All] "email" (nds "contents" "td" "")
    tag [Field "speakers"; All] "li" "tr"
    tag [Field "speakers"] "ul" "tbody"
    
    wr [Field "speakers"] "body" "table"
    add [Field "speakers"] "head" (rcd "thead")
    add [Field "speakers"; Field "head"] "name" (nds "" "td" "Name")
    add [Field "speakers"; Field "head"] "email" (nds "" "td" "E-mail")

    cp [Field "speakers"; Field "body"; All; Field "name"] [Field "speakers"; Field "body"; All; Field "email"]
    ed [Field "speakers"; Field "body"; All; Field "name"; Field "contents"] "get name" <| function 
      | String s -> String(s.Substring(0, s.IndexOf(',')))
      | _ -> failwith "refactorListOps - invalid primitive"
    ed [Field "speakers"; Field "body"; All; Field "email"; Field "contents"] "get email" <| function
      | String s -> String(s.Substring(s.IndexOf(',')+1).Trim())
      | _ -> failwith "refactorListOps - invalid primitive"
  ]
  (*
let addTransformOps = 
  [
    ap [] (nds "ttitle" "h2" "Transformers")
    add [] (rcd "x-patterns" "x-patterns")
    add [ Field "x-patterns"] (rcd "head" "thead")
    add [ Field "x-patterns"; Field "head" ] (rcd "*" "td")
    add [ Field "x-patterns"; Field "head"; Field "*" ] (rcd "*" "x-hole")
    add [ Field "x-patterns"; Field "head"; Field "*"; Field "*" ] (rcd "mq" "marquee")
    add [ Field "x-patterns"; Field "head"; Field "*"; Field "*"; Field "mq" ] (rcd "" "x-match")
  ] 
  *)
let opsCore = 
  [
    add [] "" (nds "" "h1" "Programming conference 2023")
    add [] "" (nds "" "h2" "Speakers")
    add [] "speakers" (lst "ul")
    ap [Field "speakers"] (nds "value" "li" "Adele Goldberg, adele@xerox.com") 
    ap [Field "speakers"] (nds "value" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap [Field "speakers"] (nds "value" "li" "Betty Jean Jennings, betty@rand.com") 
  ]
let opsBudget = 
  [
    add [] "" (nds "" "h2" "Budgeting")
    add [] "" (nds "" "h3" "Number of people")
    add [] "counts" (rcd "ul")
    add [Field "counts"] "attendees" (ps "Attendees: ") 
    wr [Field "counts"; Field "attendees"] "" "li"    
    add [Field "counts"; Field "attendees"] "count" (ndn "value" "strong" 100)
    add [Field "counts"] "speakers" (ps "Speakers: ") 
    wr [Field "counts"; Field "speakers"] "" "li"
    // NOTE: Reference list - not its items using 'speakers/*' because we copy node into another node
    // (and do not want to do any implicit wrapping...)
    add [Field "counts"; Field "speakers"] "count" (ref [Field "speakers"]) 
    wr [Field "counts"; Field "speakers"; Field "count"] "arg" "x-formula"
    add [Field "counts"; Field "speakers"; Field "count"] "op" (ref [Field "$builtins"; Field "count"])
    wr [Field "counts"; Field "speakers"; Field "count"] "value" "strong"

    add [] "" (nds "" "h3" "Item costs")
    add [] "costs" (rcd "ul")
    add [Field "costs"] "travel" (ps "Travel per speaker: ") 
    wr [Field "costs"; Field "travel"] "" "li"
    add [Field "costs"; Field "travel"] "cost" (ndn "value" "strong" 1000)
    add [Field "costs"] "coffee" (ps "Coffee break per person: ") 
    wr [Field "costs"; Field "coffee"] "" "li"
    add [Field "costs"; Field "coffee"] "cost" (ndn "value" "strong" 5)
    add [Field "costs"] "lunch" (ps "Lunch per person: ") 
    wr [Field "costs"; Field "lunch"] "" "li"
    add [Field "costs"; Field "lunch"] "cost" (ndn "value" "strong" 20)
    add [Field "costs"] "dinner" (ps "Dinner per person: ") 
    wr [Field "costs"; Field "dinner"] "" "li"
    add [Field "costs"; Field "dinner"] "cost" (ndn "value" "strong" 80)
    
    add [] "" (nds "" "h3" "Total costs")
    add [] "totals" (lst "ul")
    // NOTE: Construct things in a way where all structural edits (wrapping)
    // are applied to the entire list using All (this should be required!)
    // because otherwise we may end up with inconsistent structures
    ap [Field "totals"] (nds "" "span" "Refreshments: ") 
    ap [Field "totals"] (nds "" "span" "Speaker travel: ") 
    wr [Field "totals"; All] "" "li"
    add [Field "totals"; Index 0] "item" (ref [Field "costs"; Field "coffee"; Field "cost"; Field "value"])
    add [Field "totals"; Index 1] "item" (ref [Field "costs"; Field "travel"; Field "cost"; Field "value"])
    wr [Field "totals"; All; Field "item"] "left" "x-formula"
    wr [Field "totals"; All; Field "item"] "formula" "strong"
    add [Field "totals"; Index 0; Field "item"; Field "formula"] "right" (ref [Field "counts"; Field "attendees"; Field "count"; Field "value"])
    add [Field "totals"; Index 1; Field "item"; Field "formula"] "right" (ref [Field "counts"; Field "speakers"; Field "count"; Field "value"])
    add [Field "totals"; Index 0; Field "item"; Field "formula"] "op" (ref [Field "$builtins"; Field "*"])
    add [Field "totals"; Index 1; Field "item"; Field "formula"] "op" (ref [Field "$builtins"; Field "*"])

    add [] "ultimate" (ps "Total: ") 
    wr [Field "ultimate" ] "" "h3"
    add [Field "ultimate" ] "item" (ref [Field "totals"; All; Field "item"; Field "formula"])
    wr [Field "ultimate"; Field "item"] "arg" "x-formula"
    add [Field "ultimate"; Field "item"] "op" (ref [Field "$builtins"; Field "sum"])
  ]