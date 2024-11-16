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
let ref sel = Reference(Absolute, sel)
let ps s = Primitive(String s)
let pn n = Primitive(Number n)
let nds fld tag s = Record(tag, [ffld fld, Primitive(String s)])
let ndn fld tag n = Record(tag, [ffld fld, Primitive(Number n)])
let ndr fld tag sel = Record(tag, [ffld fld, Reference(sel)])

let mkEd ed = { Kind = ed; Dependencies = []; GroupLabel = ""; Disabled = false }

// Value edits
let apV s n = mkEd <| Shared(ValueKind, ListAppend(s, n))  
let apS s n = mkEd <| Shared(StructuralKind, ListAppend(s, n))  
let apfV s sel = mkEd <| Shared(ValueKind, ListAppendFrom(s, sel))  
let apfS s sel = mkEd <| Shared(StructuralKind, ListAppendFrom(s, sel))  
let ed sel fn f = transformationsLookup.["_" + fn] <- f; mkEd <| Value(PrimitiveEdit(sel, "_" + fn, None))  
let add sel f n = mkEd <| Value(RecordAdd(sel, ffld f, n)) 

// Shared structural
let ordS s l = mkEd <| Shared(StructuralKind, ListReorder(s, l))  
let delrV sel f = mkEd <| Shared(ValueKind, RecordDelete(sel, f)) 
let wrV s fld tag = mkEd <| Shared(ValueKind, WrapRecord(ffld fld, tag, s)) 
let wrS s fld tag = mkEd <| Shared(StructuralKind, WrapRecord(ffld fld, tag, s)) 
let wlS s tag = mkEd <| Shared(StructuralKind, WrapList(tag, s)) 
let cpS s1 s2 = mkEd <| Shared(StructuralKind, Copy(s2, s1)) 
let cpV s1 s2 = mkEd <| Shared(ValueKind, Copy(s2, s1)) 
let tagS s t1 t2 = mkEd <| Shared(StructuralKind, UpdateTag(s, t1, t2)) 
let uidS s fold fnew = mkEd <| Shared(StructuralKind, RecordRenameField(s, fold, ffld fnew)) 
let uidV s fold fnew = mkEd <| Shared(ValueKind, RecordRenameField(s, fold, ffld fnew)) 

let selPart = 
  ( ((P.ident <|> P.atIdent <|> P.dollarIdent) |> P.map Field) <|>
    (P.char '*' |> P.map (fun _ -> All)) <|>
    (P.keyword ".." |> P.map (fun _ -> DotDot)) <|>
    (P.num |> P.map Index) <|>
    ((P.char '<' <*>> P.ident <<*> P.char '>') |> P.map Tag) ) |> P.hole "sel"
  
let refHoleBase = 
    (P.oneOrMoreEnd (P.char '/' <*>> selPart) |> P.map (fun xs -> Absolute, xs)) <|>
    (P.char '/' |> P.map (fun xs -> Absolute, [] )) <|>
    (P.char '.' <*>> P.oneOrMoreEnd (P.char '/' <*>> selPart) |> P.map (fun xs -> Relative, xs)) 

let refHole = (refHoleBase <<*> P.char '/') <|> refHoleBase

let runOrFail p s = 
  match P.run p s with Parsed(r, []) -> r | e -> failwith $"Parsing of {s} failed {e}"
let (!/) s = 
  snd (runOrFail refHole s)

// --------------------------------------------------------------------------------------
// Conference planning demo
// --------------------------------------------------------------------------------------

// Creates <ul><li> list of speakers
let opsCore = 
  [
    add [] "t1" (nds "value" "h1" "Programming conference 2023")
    add [] "t2" (nds "value" "h2" "Speakers")
    add [] "speakers" (lst "ul")
    apV (!/ "/speakers") (nds "value" "li" "Adele Goldberg, adele@xerox.com") 
    apV (!/ "/speakers") (nds "value" "li" "Margaret Hamilton, hamilton@mit.com") 
    apV (!/ "/speakers") (nds "value" "li" "Betty Jean Jennings, betty@rand.com") 
  ]

// Add <li> and reorder items
let addSpeakerOps = 
  [ 
    apS (!/ "/speakers") (nds "value" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ordS (!/ "/speakers") [3; 0; 1; 2] 
  ]

// Create <li> as /temp and then copy into <ul>
let addSpeakerViaTempOps = 
  [
    add [] "temp" (rcd "li")
    add (!/ "/temp") "value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    apfS (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
    ordS (!/ "/speakers") [3; 0; 1; 2] 
  ]

// String replace specific list item
let fixSpeakerNameOps = 
  [
    ed (!/ "/speakers/2/value") "rename Jean" <| function 
      | (_, String s) -> String(s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@"))
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
      | _, String s -> String(s.Substring(0, s.IndexOf(',')))
      | _ -> failwith "refactorListOps - invalid primitive"
    ed (!/ "/speakers/body/*/email/contents") "get email" <| function
      | _, String s -> String(s.Substring(s.IndexOf(',')+1).Trim())
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
    apV (!/ "/totals") (ps "Refreshments: ") 
    apV (!/ "/totals") (ps "Speaker travel: ") 
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
    apfV (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
  ]

// Use existing <input> to add another speaker
let pbdAddAnotherSpeaker = 
  [
    add (!/ "/inp") "@value" (ps "Barbara Liskov, liskov@mit.edu")
    add [] "temp" (rcd "li")
    add (!/ "/temp") "value" (ps "(empty)") 
    cpV (!/ "/inp/@value") (!/ "/temp/value") 
    apfV (!/ "/speakers") (!/ "/temp")
    delrV (!/ "/") "temp"
  ]
  

// --------------------------------------------------------------------------------------
// TODO list
// --------------------------------------------------------------------------------------

let todoBaseOps = 
  [
    add [] "items" (lst "ul")
  ]

let todoAddOps work = 
  [ 
    add [] "temp" (ps work)
    apS (!/"/items") (rcd "li")
    add (!/"/items/0") "entry" (rcd "label")
    add (!/"/items/0/entry") "done" (rcd "input")
    add (!/"/items/0/entry/done") "@type" (ps "checkbox")
    add (!/"/items/0/entry") "work" (ps "")
    cpV (!/"/temp") (!/"/items/0/entry/work")
    delrV [] "temp"
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
    wrV (!/ "/counter/value") "value" "x-formula"
    uidV (!/ "/counter/value") "value" "right"
    add (!/ "/counter/value") "left" (pn 1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterDec = 
  [
    wrV (!/ "/counter/value") "value" "x-formula"
    uidV (!/ "/counter/value") "value" "right"
    add (!/ "/counter/value") "left" (pn -1)
    add (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterHndl baseList = 
  [ 
    yield add (!/"/") "saved-interactions" (rcd "x-saved-interactions")
    yield add (!/"/saved-interactions") "increment" (rcd "x-interaction")
    yield add (!/"/saved-interactions/increment") "historyhash" (ps ((hashEditList 0 baseList).ToString("x")))
    yield add (!/"/saved-interactions/increment") "interactions" (lst "x-interaction-list")
    for op in opsCounterInc ->
      apV (!/ "/saved-interactions/increment/interactions") (Represent.represent None op) 
    yield add (!/ "/inc") "@click" (ref (!/"/saved-interactions/increment"))

    yield add (!/"/saved-interactions") "decrement" (rcd "x-interaction")
    yield add (!/"/saved-interactions/decrement") "historyhash" (ps ((hashEditList 0 baseList).ToString("x")))
    yield add (!/"/saved-interactions/decrement") "interactions" (lst "x-interaction-list")
    for op in opsCounterDec ->
      apV (!/ "/saved-interactions/decrement/interactions") (Represent.represent None op) 
    yield add (!/ "/dec") "@click" (ref (!/"/saved-interactions/decrement")) ]



