module Tbd.Demos
open Tbd
open Tbd.Doc
open Tbd.Parsec
open Tbd.Parsec.Operators

// --------------------------------------------------------------------------------------
// Helper functions for constructing things
// --------------------------------------------------------------------------------------

let ffld f = 
  if f = "" then failwith "no field id"
  else f

let rcd tag = Record(tag, [])
let lst tag = List(tag, [])
let ref sel = Reference(sel)
let ps s = Primitive(String s)
let pn n = Primitive(Number n)
let nds fld tag s = Record(tag, [ffld fld, Primitive(String s)])
let ndn fld tag n = Record(tag, [ffld fld, Primitive(Number n)])
let ndr fld tag sel = Record(tag, [ffld fld, Reference(sel)])

let del sel = { Kind = Delete(sel) }
let ap s n = { Kind = ListAppend(s, ConstSource n) } 
let apr s sel = { Kind = ListAppend(s, RefSource sel) } 
let wr s fld tag = { Kind = WrapRecord(ffld fld, tag, s) }
let wl s tag = { Kind = WrapList(tag, s) }
let ord s l = { Kind = ListReorder(s, l) } 
let ed sel fn f = transformationsLookup.["_" + fn] <- f; { Kind = PrimitiveEdit(sel, "_" + fn) } 
let add sel f n = { Kind = RecordAdd(sel, ffld f, ConstSource n) }
let addr sel f src = { Kind = RecordAdd(sel, ffld f, RefSource src) }
let cp s1 s2 = { Kind = Copy(s2, RefSource s1) }
let tag s t1 t2 = { Kind = UpdateTag(s, t1, t2) }
let uid s id = { Kind = RecordRenameField(s, ffld id) }

let selectorPart = 
  ((P.ident <|> P.atIdent) |> P.map Field) <|>
  (P.char '*' |> P.map (fun _ -> All)) <|>
  (P.num |> P.map Index) <|>
  ((P.char '<' <*>> P.ident <<*> P.char '>') |> P.map Tag)

let selector = 
  P.oneOrMore (P.char '/' <*>> selectorPart)

let runOrFail p s = 
  match P.run p s with Parsed(r, []) -> r | e -> failwith $"Parsing failed {e}"
let (!/) s = 
  runOrFail selector s

// --------------------------------------------------------------------------------------
// Conference planning demo
// --------------------------------------------------------------------------------------

// Creates <ul><li> list of speakers
let opsCore = 
  [
    add [] "t1" (nds "value" "h1" "Programming conference 2023")
    add [] "t2" (nds "value" "h2" "Speakers")
    add [] "speakers" (lst "ul")
    ap (!/ "/speakers") (nds "value" "li" "Adele Goldberg, adele@xerox.com") 
    ap (!/ "/speakers") (nds "value" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap (!/ "/speakers") (nds "value" "li" "Betty Jean Jennings, betty@rand.com") 
  ]

// Add <li> and reorder items
let addSpeakerOps = 
  [ 
    ap (!/ "/speakers") (nds "value" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ord (!/ "/speakers") [3; 0; 1; 2] 
  ]

// Create <li> as /temp and then copy into <ul>
let addSpeakerViaTempOps = 
  [
    add [] "temp" (rcd "li")
    add (!/ "/temp") "value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    apr (!/ "/speakers") (!/ "/temp")
    del (!/ "/temp")
    ord (!/ "/speakers") [3; 0; 1; 2] 
  ]

// String replace specific list item
let fixSpeakerNameOps = 
  [
    ed (!/ "/speakers/2/value") "rename Jean" <| function 
      | (String s) -> String(s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@"))
      | _ -> failwith "fixSpeakerNameOps - wrong primitive"
  ]

// Turn <ul> list into <table> and split items into two columns
let refactorListOps = 
  [
    uid (!/ "/speakers/*/value") "name"
    wr (!/ "/speakers/*/name") "contents" "td"
    
    add (!/ "/speakers/*") "email" (nds "contents" "td" "")
    tag (!/ "/speakers/*") "li" "tr"
    tag (!/ "/speakers") "ul" "tbody"
    
    wr (!/ "/speakers") "body" "table"
    add (!/ "/speakers") "head" (rcd "thead")
    add (!/ "/speakers/head") "name" (nds "value" "td" "Name")
    add (!/ "/speakers/head") "email" (nds "value" "td" "E-mail")

    cp (!/ "/speakers/body/*/name") (!/ "/speakers/body/*/email")
    ed (!/ "/speakers/body/*/name/contents") "get name" <| function 
      | String s -> String(s.Substring(0, s.IndexOf(',')))
      | _ -> failwith "refactorListOps - invalid primitive"
    ed (!/ "/speakers/body/*/email/contents") "get email" <| function
      | String s -> String(s.Substring(s.IndexOf(',')+1).Trim())
      | _ -> failwith "refactorListOps - invalid primitive"
  ]

// Create <input> 
let pbdAddInput = 
  [
    add [] "inp" (rcd "input")
  ]

// Use existing <input> to add one speaker
let pbdAddFirstSpeaker = 
  [
    add (!/ "/inp") "@value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    add [] "temp" (rcd "li")
    addr (!/ "/temp") "value" (!/ "/inp/@value")
    apr (!/ "/speakers") (!/ "/temp")
    del (!/ "/temp")
  ]

// Use existing <input> to add another speaker
let pbdAddAnotherSpeaker = 
  [
    add (!/ "/inp") "@value" (ps "Barbara Liskov, liskov@mit.edu")
    add [] "temp" (rcd "li")
    addr (!/ "/temp") "value" (!/ "/inp/@value")
    apr (!/ "/speakers") (!/ "/temp")
    del (!/ "/temp")
  ]
  


// --------------------------------------------------------------------------------------
// Leftovers
// --------------------------------------------------------------------------------------

  (*
let addTransformOps = 
  [
    ap [] (nds "ttitle" "h2" "Transformers")
    add [] (rcd "x-patterns" "x-patterns")
    add [ Field "x-patterns") (rcd "head" "thead")
    add [ Field "x-patterns/head" ] (rcd "*" "td")
    add [ Field "x-patterns/head/*" ] (rcd "*" "x-hole")
    add [ Field "x-patterns/head/*/*" ] (rcd "mq" "marquee")
    add [ Field "x-patterns/head/*/*/mq" ] (rcd "" "x-match")
  ] 
  *)

let opsBaseCounter() = 
  [ 
    add [] "" (nds "title" "h1" "Counter")
    add [] "counter" (rcd "p")
    add (!/ "/counter") "" (nds "" "strong" "Count: ")
    add (!/ "/counter") "value" (pn 0)
    add [] "inc" (nds "" "button" "Increment")
    add [] "dec" (nds "" "button" "Decrement")
  ]

let opsCounterInc() = 
  [
    wr (!/ "/counter/value") "value" "x-formula"
    uid (!/ "/counter/value/value") "right"
    add (!/ "/counter/value") "left" (pn 1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/+"))
  ]

let opsCounterDec() = 
  [
    wr (!/ "/counter/value") "value" "x-formula"
    uid (!/ "/counter/value/value") "right"
    add (!/ "/counter/value") "left" (pn -1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/+"))
  ]

let opsCounterHndl() = 
  [ yield add (!/ "/inc") "click" (lst "x-event-handler")
    for op in opsCounterInc() ->
      ap (!/ "/inc/click") (represent op) 
    yield add (!/ "/dec") "click" (lst "x-event-handler")
    for op in opsCounterDec() ->
      ap (!/ "/dec/click") (represent op) ]

let opsBudget() = 
  [
    add [] "" (nds "" "h2" "Budgeting")
    add [] "" (nds "" "h3" "Number of people")
    add [] "counts" (rcd "ul")
    add (!/ "/counts") "attendees" (ps "Attendees: ") 
    wr (!/ "/counts/attendees") "" "li"    
    add (!/ "/counts/attendees") "count" (ndn "value" "strong" 100)
    add (!/ "/counts") "speakers" (ps "Speakers: ") 
    wr (!/ "/counts/speakers") "" "li"
    // NOTE: Reference list - not its items using 'speakers/*' because we copy node into another node
    // (and do not want to do any implicit wrapping...)
    add (!/ "/counts/speakers") "count" (ref (!/ "/speakers")) 
    wr (!/ "/counts/speakers/count") "arg" "x-formula"
    add (!/ "/counts/speakers/count") "op" (ref (!/ "/$builtins/count"))
    wr (!/ "/counts/speakers/count") "value" "strong"

    add [] "" (nds "" "h3" "Item costs")
    add [] "costs" (rcd "ul")
    add (!/ "/costs") "travel" (ps "Travel per speaker: ") 
    wr (!/ "/costs/travel") "" "li"
    add (!/ "/costs/travel") "cost" (ndn "value" "strong" 1000)
    add (!/ "/costs") "coffee" (ps "Coffee break per person: ") 
    wr (!/ "/costs/coffee") "" "li"
    add (!/ "/costs/coffee") "cost" (ndn "value" "strong" 5)
    add (!/ "/costs") "lunch" (ps "Lunch per person: ") 
    wr (!/ "/costs/lunch") "" "li"
    add (!/ "/costs/lunch") "cost" (ndn "value" "strong" 20)
    add (!/ "/costs") "dinner" (ps "Dinner per person: ") 
    wr (!/ "/costs/dinner") "" "li"
    add (!/ "/costs/dinner") "cost" (ndn "value" "strong" 80)
    
    add [] "" (nds "" "h3" "Total costs")
    add [] "totals" (lst "ul")
    // NOTE: Construct things in a way where all structural edits (wrapping)
    // are applied to the entire list using All (this should be required!)
    // because otherwise we may end up with inconsistent structures
    ap (!/ "/totals") (nds "" "span" "Refreshments: ") 
    ap (!/ "/totals") (nds "" "span" "Speaker travel: ") 
    wr (!/ "/totals/*") "" "li"
    add (!/ "/totals/0") "item" (ref (!/ "/costs/coffee/cost/value"))
    add (!/ "/totals/1") "item" (ref (!/ "/costs/travel/cost/value"))
    wr (!/ "/totals/*/item") "left" "x-formula"
    wr (!/ "/totals/*/item") "formula" "strong"
    add (!/ "/totals/0/item/formula") "right" (ref (!/ "/counts/attendees/count/value"))
    add (!/ "/totals/1/item/formula") "right" (ref (!/ "/counts/speakers/count/value"))
    add (!/ "/totals/0/item/formula") "op" (ref (!/ "/$builtins/*"))
    add (!/ "/totals/1/item/formula") "op" (ref (!/ "/$builtins/*"))

    add [] "ultimate" (ps "Total: ") 
    wr (!/ "/ultimate") "" "h3"
    add (!/ "/ultimate") "item" (ref (!/ "/totals/*/item/formula"))
    wr (!/ "/ultimate/item") "arg" "x-formula"
    add (!/ "/ultimate/item") "op" (ref (!/ "/$builtins/sum"))
  ]