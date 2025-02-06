module Denicek.Demos
open Denicek
open Denicek.Doc
open Denicek.Parsec
open Denicek.Parsec.Operators

// --------------------------------------------------------------------------------------
// Helper functions for constructing things
// --------------------------------------------------------------------------------------

let ffld f = 
  if f = "" then failwith "no field id"
  else f

// Node construction
let rcd tag = Record(tag, OrdList.empty)
let lst tag = List(tag, OrdList.empty)
let ref sel = Reference(Absolute, sel)
let ps s = Primitive(String s)
let pn n = Primitive(Number n)
let nds fld tag s = Record(tag, OrdList.singleton (ffld fld) (Primitive(String s)))
let ndn fld tag n = Record(tag, OrdList.singleton (ffld fld) (Primitive(Number n)))
let ndr fld tag sel = Record(tag, OrdList.singleton (ffld fld) (Reference(sel)))

let mkEd ed = { Kind = ed; Dependencies = []; GroupLabel = "" }

// Value edits
let ap0 s i n = mkEd <| ListAppend(s, i, None, None, n)
let ap s i pi n = mkEd <| ListAppend(s, i, Some pi, None, n)
let ed sel fn f = Apply.transformationsLookup.["_" + fn] <- f; mkEd <| PrimitiveEdit(sel, "_" + fn, None)
let add sel f pred n = mkEd <| RecordAdd(sel, ffld f, Some pred, None, n)
let add0 sel f n = mkEd <| RecordAdd(sel, ffld f, None, None, n)
let ord s l = mkEd <| ListReorder(s, l)
let tag s t = mkEd <| UpdateTag(s, t)

// Structural edits
let delrV sel f = mkEd <| RecordDelete(KeepReferences, sel, f)
let wrV s fld tag = mkEd <| WrapRecord(KeepReferences, ffld fld, tag, s)
let wrS s fld tag = mkEd <| WrapRecord(UpdateReferences, ffld fld, tag, s)
let wlS s i tag = mkEd <| WrapList(UpdateReferences, tag, i, s)
let cpS s1 s2 = mkEd <| Copy(UpdateReferences, s2, s1)
let cpV s1 s2 = mkEd <| Copy(KeepReferences, s2, s1)
let uidS s fold fnew = mkEd <| RecordRenameField(UpdateReferences, s, fold, ffld fnew)
let uidV s fold fnew = mkEd <| RecordRenameField(KeepReferences, s, fold, ffld fnew)

let selPart = 
  ( ((P.ident <|> P.atIdent <|> P.dollarIdent) |> P.map Field) <|>
    (P.char '*' |> P.map (fun _ -> All)) <|>
    (P.keyword ".." |> P.map (fun _ -> DotDot)) <|>
    (P.char '#' <*>> P.ident |> P.map Index) ) |> P.hole "sel"
  
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
    add0 [] "t1" (nds "value" "h1" "Programming conference 2023")
    add [] "t2" "t1" (nds "value" "h2" "Speakers")
    add [] "speakers" "t2" (lst "ul")
    ap0 (!/ "/speakers") "goldberg" (nds "value" "li" "Adele Goldberg, adele@xerox.com") 
    ap (!/ "/speakers") "hamilton" "goldberg" (nds "value" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap (!/ "/speakers") "jennings" "hamilton" (nds "value" "li" "Betty Jean Jennings, betty@rand.com") 
  ]

// Add <li> and reorder items
let addSpeakerOps = 
  [ 
    ap0 (!/ "/speakers") "lovelace" (nds "value" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ord (!/ "/speakers") ["lovelace"; "goldberg"; "jennings"; "hamilton"] 
  ]

  // Add <li> and reorder items
let addSpeakerTwoStepOps = 
  [ 
    ap0 (!/ "/speakers") "floyd" (rcd "li")
    add0 (!/ "/speakers/#floyd") "value" (ps "Christiane Floyd, floyd@tu-berlin.de")
  ]

// Create <li> as /temp and then copy into <ul>
let addSpeakerViaTempOps = 
  [
    add0 [] "temp" (rcd "li")
    add0 (!/ "/temp") "value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ap0 (!/ "/speakers") "lovelace" (ps "")
    cpV (!/"/temp") (!/ "/speakers/#lovelace")
    delrV (!/ "/") "temp"
    ord (!/ "/speakers") ["lovelace"; "goldberg"; "jennings"; "hamilton"]
  ]

// String replace specific list item
let fixSpeakerNameOps = 
  [
    ed (!/ "/speakers/#jennings/value") "rename Jean" <| function 
      | (_, String s) -> String(s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@"))
      | _ -> failwith "fixSpeakerNameOps - wrong primitive"
  ]

// Turn <ul> list into <table> and split items into two columns
let refactorListOps = 
  [
    uidS (!/ "/speakers/*") "value" "name"
    wrS (!/ "/speakers/*/name") "contents" "td"
    
    add (!/ "/speakers/*") "email" "name" (nds "contents" "td" "")
    tag (!/ "/speakers/*") "tr"
    tag (!/ "/speakers") "tbody"
    
    wrS (!/ "/speakers") "body" "table"
    
    add0 (!/ "/speakers") "head" (rcd "thead")
    add0 (!/ "/speakers/head") "name" (nds "value" "td" "Name")
    add (!/ "/speakers/head") "email" "name" (nds "value" "td" "E-mail")

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
    add [] "t3" "speakers" (nds "v" "h2" "Budgeting")
    add [] "t4" "t3" (nds "v" "h3" "Number of people")
    add [] "counts" "t4" (rcd "ul")
    add0 (!/ "/counts") "attendees" (ps "Attendees: ") 
    wrS (!/ "/counts/attendees") "lable" "li"    
    add0 (!/ "/counts/attendees") "count" (ndn "value" "strong" 100)
    add0 (!/ "/counts") "speakers" (ps "Speakers: ") 
    wrS (!/ "/counts/speakers") "label" "li"
    
    // NOTE: Reference list - not its items using 'speakers/*' because we copy node into another node
    // (and do not want to do any implicit wrapping...)
    add0 (!/ "/counts/speakers") "count" (ref (!/ "/speakers")) 
    wrS (!/ "/counts/speakers/count") "arg" "x-formula"
    add0 (!/ "/counts/speakers/count") "op" (ref (!/ "/$builtins/count"))
    wrS (!/ "/counts/speakers/count") "value" "strong"
    
    add [] "t5" "counts" (nds "v" "h3" "Item costs")
    add [] "costs" "t5" (rcd "ul")
    add0 (!/ "/costs") "travel" (ps "Travel per speaker: ") 
    wrS (!/ "/costs/travel") "label" "li"
    add0 (!/ "/costs/travel") "cost" (ndn "value" "strong" 1000)
    add (!/ "/costs") "coffee" "travel" (ps "Coffee break per person: ") 
    wrS (!/ "/costs/coffee") "label" "li"
    add0 (!/ "/costs/coffee") "cost" (ndn "value" "strong" 5)
    add (!/ "/costs") "lunch" "coffee" (ps "Lunch per person: ") 
    wrS (!/ "/costs/lunch") "label" "li"
    add0 (!/ "/costs/lunch") "cost" (ndn "value" "strong" 20)
    add (!/ "/costs") "dinner" "lunch" (ps "Dinner per person: ") 
    wrS (!/ "/costs/dinner") "label" "li"
    add0 (!/ "/costs/dinner") "cost" (ndn "value" "strong" 80)
    
    add [] "t6" "costs" (nds "v" "h3" "Total costs")
    add [] "totals" "t6" (lst "ul")

    ap0 (!/ "/totals") "0" (ps "Refreshments: ") 
    ap (!/ "/totals") "1" "0" (ps "Speaker travel: ") 
    wrS (!/ "/totals/*") "label" "li"    
    add0 (!/ "/totals/#0") "item" (ref (!/ "/costs/coffee/cost/value"))
    add0 (!/ "/totals/#1") "item" (ref (!/ "/costs/travel/cost/value"))
    
    wrS (!/ "/totals/*/item") "left" "x-formula"
    wrS (!/ "/totals/*/item") "formula" "strong"
    add0 (!/ "/totals/#0/item/formula") "right" (ref (!/ "/counts/attendees/count/value"))
    add0 (!/ "/totals/#1/item/formula") "right" (ref (!/ "/counts/speakers/count/value"))
    add0 (!/ "/totals/#0/item/formula") "op" (ref (!/ "/$builtins/mul"))
    add0 (!/ "/totals/#1/item/formula") "op" (ref (!/ "/$builtins/mul"))
    
    add [] "ultimate" "totals" (ps "Total: ") 
    wrS (!/ "/ultimate") "t7" "h3"
    add0 (!/ "/ultimate") "item" (ref (!/ "/totals/*/item/formula"))
    wrS (!/ "/ultimate/item") "arg" "x-formula"
    add0 (!/ "/ultimate/item") "op" (ref (!/ "/$builtins/sum"))    
  ]

// Create <input> 
let pbdAddInput = 
  [
    add [] "inp" "speakers" (rcd "input")
  ]

// Use existing <input> to add one speaker
let pbdAddFirstSpeaker = 
  [
    add0 (!/ "/inp") "@value" (ps "Ada Lovelace, lovelace@royalsociety.ac.uk")
    add0 [] "templovelace" (rcd "li")
    add0 (!/ "/templovelace") "value" (ps "(empty)") 
    cpV (!/ "/inp/@value") (!/ "/templovelace/value") 
    ap0 (!/ "/speakers") "lovelace" (ps "")
    cpV (!/ "/speakers/#lovelace") (!/"/templovelace")
    delrV (!/ "/") "templovelace"
  ]

// Use existing <input> to add another speaker
let pbdAddAnotherSpeaker = 
  [
    add0 (!/ "/inp") "@value" (ps "Barbara Liskov, liskov@mit.edu")
    add0 [] "templiskov" (rcd "li")
    add0 (!/ "/templiskov") "value" (ps "(empty)") 
    cpV (!/ "/inp/@value") (!/ "/templiskov/value") 
    ap0 (!/ "/speakers") "liskov" (ps "")
    cpV (!/ "/speakers/#liskov") (!/"/templiskov")
    delrV (!/ "/") "templiskov"
  ]
  

// --------------------------------------------------------------------------------------
// TODO list
// --------------------------------------------------------------------------------------

let todoBaseOps = 
  [
    add0 [] "items" (lst "ul")
  ]

let todoAddOps idwork work = 
  [ 
    add0 [] ("temp" + idwork) (ps work)
    ap0 (!/"/items") idwork (rcd "li")
    add0 (!/ $"/items/#{idwork}") "entry" (rcd "label")
    add0 (!/ $"/items/#{idwork}/entry") "done" (rcd "input")
    add0 (!/ $"/items/#{idwork}/entry/done") "@type" (ps "checkbox")
    add (!/ $"/items/#{idwork}/entry") "work" "done" (ps "")
    cpV (!/ $"/temp{idwork}") (!/ $"/items/#{idwork}/entry/work")
    delrV [] $"temp{idwork}f"
  ]

// --------------------------------------------------------------------------------------
// Counter demo
// --------------------------------------------------------------------------------------

let opsBaseCounter = 
  [ 
    add0 [] "t" (nds "title" "h1" "Counter")
    add [] "counter" "t" (rcd "p")
    add0 (!/ "/counter") "l" (nds "v" "strong" "Count: ")
    add (!/ "/counter") "value" "l" (pn 0)
    add [] "inc" "counter" (nds "v" "button" "Increment")
    add [] "dec" "inc" (nds "v" "button" "Decrement")
  ]

let opsCounterInc = 
  [
    wrV (!/ "/counter/value") "value" "x-formula"
    uidV (!/ "/counter/value") "value" "right"
    add0 (!/ "/counter/value") "left" (pn 1)
    add0 (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterDec = 
  [
    wrV (!/ "/counter/value") "value" "x-formula"
    uidV (!/ "/counter/value") "value" "right"
    add0 (!/ "/counter/value") "left" (pn -1)
    add0 (!/ "/counter/value") "op" (ref (!/ "/$builtins/plus"))
  ]

let opsCounterHndl baseList = 
  [ 
    yield add0 (!/"/") "saved-interactions" (rcd "x-saved-interactions")
    yield add0 (!/"/saved-interactions") "increment" (rcd "x-interaction")
    yield add0 (!/"/saved-interactions/increment") "historyhash" (ps ((Merge.hashEditList 0 baseList).ToString("x")))
    yield add0 (!/"/saved-interactions/increment") "interactions" (lst "x-interaction-list")
    for i, op in Seq.indexed opsCounterInc ->
      ap0 (!/ "/saved-interactions/increment/interactions") (string i) (Represent.represent None op) 
    yield add0 (!/ "/inc") "@click" (ref (!/"/saved-interactions/increment"))

    yield add0 (!/"/saved-interactions") "decrement" (rcd "x-interaction")
    yield add0 (!/"/saved-interactions/decrement") "historyhash" (ps ((Merge.hashEditList 0 baseList).ToString("x")))
    yield add0 (!/"/saved-interactions/decrement") "interactions" (lst "x-interaction-list")
    for i, op in Seq.indexed opsCounterDec ->
      ap0 (!/ "/saved-interactions/decrement/interactions") (string i) (Represent.represent None op) 
    yield add0 (!/ "/dec") "@click" (ref (!/"/saved-interactions/decrement")) 
  ]
