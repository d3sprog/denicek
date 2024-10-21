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

// Node construction
let rcd tag = Record(tag, [])
let lst tag = List(tag, [])
let ref sel = Reference(sel)
let ps s = Primitive(String s)
let pn n = Primitive(Number n)
let nds fld tag s = Record(tag, [ffld fld, Primitive(String s)])
let ndn fld tag n = Record(tag, [ffld fld, Primitive(Number n)])
let ndr fld tag sel = Record(tag, [ffld fld, Reference(sel)])

let mkEd ed = { Kind = ed; Dependencies = []; GroupLabel = "" }

// Value edits
let ap s n = mkEd <| Value(ListAppend(s, n))  
let apf s sel = mkEd <| Value(ListAppendFrom(s, sel))  
let ed sel fn f = transformationsLookup.["_" + fn] <- f; mkEd <| Value(PrimitiveEdit(sel, "_" + fn))  
let add sel f n = mkEd <| Value(RecordAdd(sel, ffld f, n)) 

// Shared structural
let ordS s l = mkEd <| Shared(StructuralKind, ListReorder(s, l))  
let delrV sel f = mkEd <| Shared(ValueKind, RecordDelete(sel, f)) 
let wrS s fld tag = mkEd <| Shared(StructuralKind, WrapRecord(ffld fld, tag, s)) 
let wlS s tag = mkEd <| Shared(StructuralKind, WrapList(tag, s)) 
let cpS s1 s2 = mkEd <| Shared(StructuralKind, Copy(s2, s1)) 
let cpV s1 s2 = mkEd <| Shared(ValueKind, Copy(s2, s1)) 
let tagS s t1 t2 = mkEd <| Shared(StructuralKind, UpdateTag(s, t1, t2)) 
let uidS s fold fnew = mkEd <| Shared(StructuralKind, RecordRenameField(s, fold, ffld fnew)) 

let selectorPart = 
  ((P.ident <|> P.atIdent <|> P.dollarIdent) |> P.map Field) <|>
  (P.char '*' |> P.map (fun _ -> All)) <|>
  (P.num |> P.map Index) <|>
  ((P.char '<' <*>> P.ident <<*> P.char '>') |> P.map Tag)

let selector = 
  (P.oneOrMore (P.char '/' <*>> selectorPart)) <|>
  (P.char '/' |> P.map (fun _ -> []))

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
    ordS (!/ "/speakers") [3; 0; 1; 2] 
  ]

// Create <li> as /temp and then copy into <ul>
let addSpeakerViaTempOps = 
  [
    add [] "temp" (rcd "li")
    add (!/ "/temp") "value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    apf (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
    ordS (!/ "/speakers") [3; 0; 1; 2] 
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
    uidS (!/ "/speakers/*") "value" "name"
    wrS (!/ "/speakers/*/name") "contents" "td"
    
    add (!/ "/speakers/*") "email" (nds "contents" "td" "")
    tagS (!/ "/speakers/*") "li" "tr"
    tagS (!/ "/speakers") "ul" "tbody"
    
    wrS (!/ "/speakers") "body" "table"
    add (!/ "/speakers") "head" (rcd "thead")
    add (!/ "/speakers/head") "name" (nds "value" "td" "Name")
    add (!/ "/speakers/head") "email" (nds "value" "td" "E-mail")

    cpS (!/ "/speakers/body/*/name") (!/ "/speakers/body/*/email")
    ed (!/ "/speakers/body/*/name/contents") "get name" <| function 
      | String s -> String(s.Substring(0, s.IndexOf(',')))
      | _ -> failwith "refactorListOps - invalid primitive"
    ed (!/ "/speakers/body/*/email/contents") "get email" <| function
      | String s -> String(s.Substring(s.IndexOf(',')+1).Trim())
      | _ -> failwith "refactorListOps - invalid primitive"
  ]

// Add budget computation using formulas
let opsBudget = 
  [
    add [] "t3" (nds "v" "h2" "Budgeting")
    add [] "t4" (nds "v" "h3" "Number of people")
    add [] "counts" (rcd "ul")
    add (!/ "/counts") "attendees" (ps "Attendees: ") 
    wrS (!/ "/counts/attendees") "lable" "li"    
    add (!/ "/counts/attendees") "count" (ndn "value" "strong" 100)
    add (!/ "/counts") "speakers" (ps "Speakers: ") 
    wrS (!/ "/counts/speakers") "label" "li"
    
    // NOTE: Reference list - not its items using 'speakers/*' because we copy node into another node
    // (and do not want to do any implicit wrapping...)
    add (!/ "/counts/speakers") "count" (ref (!/ "/speakers")) 
    wrS (!/ "/counts/speakers/count") "arg" "x-formula"
    add (!/ "/counts/speakers/count") "op" (ref (!/ "/$builtins/count"))
    wrS (!/ "/counts/speakers/count") "value" "strong"

    add [] "t5" (nds "v" "h3" "Item costs")
    add [] "costs" (rcd "ul")
    add (!/ "/costs") "travel" (ps "Travel per speaker: ") 
    wrS (!/ "/costs/travel") "label" "li"
    add (!/ "/costs/travel") "cost" (ndn "value" "strong" 1000)
    add (!/ "/costs") "coffee" (ps "Coffee break per person: ") 
    wrS (!/ "/costs/coffee") "label" "li"
    add (!/ "/costs/coffee") "cost" (ndn "value" "strong" 5)
    add (!/ "/costs") "lunch" (ps "Lunch per person: ") 
    wrS (!/ "/costs/lunch") "label" "li"
    add (!/ "/costs/lunch") "cost" (ndn "value" "strong" 20)
    add (!/ "/costs") "dinner" (ps "Dinner per person: ") 
    wrS (!/ "/costs/dinner") "label" "li"
    add (!/ "/costs/dinner") "cost" (ndn "value" "strong" 80)
    
    add [] "t6" (nds "v" "h3" "Total costs")
    add [] "totals" (lst "ul")
    // NOTE: Construct things in a way where all structural edits (wrapping)
    // are applied to the entire list using All (this should be required!)
    // because otherwise we may end up with inconsistent structures
    ap (!/ "/totals") (ps "Refreshments: ") 
    ap (!/ "/totals") (ps "Speaker travel: ") 
    wrS (!/ "/totals/*") "label" "li"    
    add (!/ "/totals/0") "item" (ref (!/ "/costs/coffee/cost/value"))
    add (!/ "/totals/1") "item" (ref (!/ "/costs/travel/cost/value"))
    
    wrS (!/ "/totals/*/item") "left" "x-formula"
    wrS (!/ "/totals/*/item") "formula" "strong"
    add (!/ "/totals/0/item/formula") "right" (ref (!/ "/counts/attendees/count/value"))
    add (!/ "/totals/1/item/formula") "right" (ref (!/ "/counts/speakers/count/value"))
    add (!/ "/totals/0/item/formula") "op" (ref (!/ "/$builtins/mul"))
    add (!/ "/totals/1/item/formula") "op" (ref (!/ "/$builtins/mul"))
    
    add [] "ultimate" (ps "Total: ") 
    wrS (!/ "/ultimate") "t7" "h3"
    add (!/ "/ultimate") "item" (ref (!/ "/totals/*/item/formula"))
    wrS (!/ "/ultimate/item") "arg" "x-formula"
    add (!/ "/ultimate/item") "op" (ref (!/ "/$builtins/sum"))    
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
    add (!/ "/temp") "value" (ps "(empty)") 
    cpV (!/ "/inp/@value") (!/ "/temp/value") 
    apf (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
  ]

// Use existing <input> to add another speaker
let pbdAddAnotherSpeaker = 
  [
    add (!/ "/inp") "@value" (ps "Barbara Liskov, liskov@mit.edu")
    add [] "temp" (rcd "li")
    add (!/ "/temp") "value" (ps "(empty)") 
    cpV (!/ "/inp/@value") (!/ "/temp/value") 
    apf (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
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

let opsBaseCounter = 
  [ 
    add [] "t" (nds "title" "h1" "Counter")
    add [] "counter" (rcd "p")
    add (!/ "/counter") "l" (nds "v" "strong" "Count: ")
    add (!/ "/counter") "value" (pn 0)
    add [] "inc" (nds "v" "button" "Increment")
    add [] "dec" (nds "v" "button" "Decrement")
  ]

let opsCounterInc = 
  [
    wrS (!/ "/counter/value") "value" "x-formula"
    uidS (!/ "/counter/value") "value" "right"
    add (!/ "/counter/value") "left" (pn 1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterDec = 
  [
    wrS (!/ "/counter/value") "value" "x-formula"
    uidS (!/ "/counter/value") "value" "right"
    add (!/ "/counter/value") "left" (pn -1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterHndl = 
  [ yield add (!/ "/inc") "click" (lst "x-event-handler")
    for op in opsCounterInc ->
      ap (!/ "/inc/click") (Represent.represent op) 
    yield add (!/ "/dec") "click" (lst "x-event-handler")
    for op in opsCounterDec ->
      ap (!/ "/dec/click") (Represent.represent op) ]



