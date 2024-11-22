#if INTERACTIVE
#nowarn "3353"
#I "../src"
#load "utils.fs" "parsec.fs" "ordlist.fs" "doc.fs" "represent.fs" "eval.fs" "demos.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd
open Tbd.Doc
open Tbd.Demos

let merge h1 h2 = mergeHistories IgnoreConflicts h1 h2 |> fst
let printEdits = List.iter (formatEdit >> printfn " - %s")
let selectTag sel doc = match select sel doc with [List(t, _)] | [Record(t, _)] -> Some t | _ -> None 
let mkEd ed = { Kind = ed; GroupLabel = ""; Dependencies = [] } 
let moveOneBefore e1 e2 = [ for e, es in moveAllBefore (mkEd e1) [mkEd e2, []] do yield! e::es ]
let moveMultiBefore e1 (e2, e2extras) = [ for e, es in moveAllBefore (mkEd e1) [mkEd e2, List.map mkEd e2extras] do yield! e::es ]

[<Tests>]
let moveBeforeTests =
  testList "moveBefore tests" [       
    test "moveBefore scopes record transformation" {
      let actual = 
        moveOneBefore 
          (RecordAdd(!/"/items/*", "condition", None, Record("x-formula", OrdList.empty)))
          (ListAppend(!/"/items", "0", None, Record("li", OrdList.empty)))
      formatEdit actual.[1]
      |> equals """recordAdd(items/#0,"condition",na,x-formula{})"""
    }

    test "moveBefore scopes source of a copy edit" {
      let actual = 
        moveOneBefore 
          (Copy(UpdateReferences, !/"/speakers/body/*/name", !/"/speakers/body/*/email"))
          (ListAppend(!/"/speakers/body", "hamilton", None, Primitive(String "Margaret Hamilton")))
      formatEdit actual.[1]
      |> equals "v.copy(speakers/body/#hamilton/name,speakers/body/#hamilton/email)"
    }

    test "moveBefore does not overwrite record with conflicting add" {
      let actual = 
        moveOneBefore 
          (RecordAdd(!/"/", "demo", None, Primitive(String "original")))
          (RecordAdd(!/"/", "demo", None, Primitive(String "new")))
      select (!/"/demo") (applyHistory (rcd "root") actual)
      |> equals [Primitive(String "new")]
    }

    test "moveBefore applies copy edit to added field" {
      let actual = 
        moveMultiBefore 
          (Copy(UpdateReferences, !/"/speakers/body/*/email", !/"/speakers/body/*/name"))
          ( RecordAdd(!/"/speakers/body/#hamilton", "speaker", None, Primitive(String "Margaret Hamilton")),
            [RecordRenameField(KeepReferences, !/"/speakers/body/#hamilton", "speaker", "name")] )
      formatEdit actual.[2]
      |> equals "v.copy(speakers/body/#hamilton/email,speakers/body/#hamilton/name)"
    }

    test "moveBefore does not apply renames to extra ops and appends it instead" {
      let actual = 
        moveMultiBefore 
          (RecordRenameField(UpdateReferences, !/"/speakers/body/*", "speaker", "name"))
          ( RecordAdd(!/"/speakers/body/#hamilton", "speaker", None, Primitive(String "Margaret Hamilton")),
            [WrapRecord(KeepReferences, "value", "td", !/"/speakers/body/#hamilton/speaker")] )
      formatEdit actual.[1]
      |> equals """v.wrapRec(speakers/body/#hamilton/speaker,"value","td")"""
      formatEdit actual.[2]
      |> equals """v.renameField(speakers/body/#hamilton,"speaker","name")"""
    }

    test "moveBefore does wraps added field but not again the target of copy" {
      let actual1 = 
        moveOneBefore 
          (WrapRecord(UpdateReferences, "value", "td", !/"/speakers/*/speaker"))
          (RecordAdd(!/"/speakers/#n", "speaker", None, Primitive(String "")))
      List.map formatEdit actual1 |> equals [ 
        """recordAdd(speakers/#n,"speaker",na,"")"""
        """v.wrapRec(speakers/#n/speaker,"value","td")"""]
      let actual2 = 
        moveOneBefore 
          (WrapRecord(UpdateReferences, "value", "td", !/"/speakers/*/speaker"))
          (Copy(KeepReferences,!/"/speakers/#n/speaker", !/"/new/@value"))
      List.map formatEdit actual2
      |> equals ["v.copy(speakers/#n/speaker/value,new/@value)"]
    }

    test "moveBefore applies primitive edit to copied" {
      let actual = 
        moveOneBefore 
          (PrimitiveEdit(!/"/speakers/body/*/name/email", "op", None))
          (Copy(KeepReferences, !/"/speakers/body/#hamilton/name/email", !/"/new/@value"))
      formatEdit actual.[1]
      |> equals """primitive(speakers/body/#hamilton/name/email,"op")"""
    }


    test "moveBefore does not wrap target of record add" {
      let actual = 
        moveOneBefore 
          (WrapRecord(UpdateReferences, "contents", "td", !/"/speakers/*/name"))
          (RecordAdd(!/"/speakers/#hamilton", "name", None, Primitive(String "Margaret Hamilton")))
      formatEdit actual.[0]
      |> equals """recordAdd(speakers/#hamilton,"name",na,"Margaret Hamilton")"""
      formatEdit actual.[1]
      |> equals """v.wrapRec(speakers/#hamilton/name,"contents","td")"""
    }

    test "moveBefore renames target of record add" {
      let actual = 
        moveOneBefore 
          (RecordRenameField(UpdateReferences, !/"/speakers/*", "value", "name"))
          (RecordAdd(!/"/speakers/#hamilton", "value", None, Primitive(String "Margaret Hamilton")))
      formatEdit actual.[0]
      |> equals """recordAdd(speakers/#hamilton,"value",na,"Margaret Hamilton")"""
      formatEdit actual.[1]
      |> equals """v.renameField(speakers/#hamilton,"value","name")"""
    }

    test "moveBefore applies wraprec to added field" {
      let actual = 
        moveOneBefore 
          (WrapRecord(UpdateReferences, "td", "value", !/"/speakers/body/*/speaker"))
          (RecordAdd(!/"/speakers/body/#hamilton", "speaker", None, Primitive(String "Margaret Hamilton")))
      formatEdit actual.[1]
      |> equals """v.wrapRec(speakers/body/#hamilton/speaker,"td","value")"""
    }

    test "moveBefore applies wraprec to field added by extra rename" {
      let actual = 
        moveMultiBefore 
          ( WrapRecord(UpdateReferences, "td", "contents", !/"/speakers/*/name") )
          ( RecordAdd(!/"/speakers/#hamilton", "value", None, Primitive(String "Margaret Hamilton")), 
            [RecordRenameField(KeepReferences, !/"/speakers/#hamilton", "value", "name")] )
      formatEdit actual.[2]
      |> equals """v.wrapRec(speakers/#hamilton/name,"td","contents")"""
    }

    test "moveBefore transforms selectors in list append" {
      let actual = 
        moveOneBefore
          (WrapRecord(UpdateReferences, "body", "table", [Field "speakers"]))
          (ListAppend([Field "speakers"],"hamilton", None, Record("li", OrdList.empty)))
      formatEdit actual.[0]
      |> equals """listAppend(speakers/body,"hamilton",na,li{})"""
    }

    test "moveBefore wraps added reference" {
      let actual = 
        moveOneBefore
          (WrapRecord(UpdateReferences, "body", "table", [Field "speakers"]))
          (RecordAdd(!/"/budget", "count", None, Reference(Absolute, [Field "speakers"])))
      List.map formatEdit actual
      |> equals ["""recordAdd(budget,"count",na,/speakers/body)"""]
    }

    // listAppend(items,"0.37a3bc43",na,li{}) [
    //   recordAdd(items/#0.37a3bc43,"condition","lbl",x-formula{}); 
    //   recordAdd(items/#0.37a3bc43/condition,"op",na,/$builtins/equals); 
    //   recordAdd(items/#0.37a3bc43/condition,"left","op","checked"); 
    //   recordAdd(items/#0.37a3bc43/condition,"right","left",./../../lbl/done/@checked); 
    //   v.wrapRec(items/#0.37a3bc43/condition,"comp","span"); 
    //   recordAdd(items/#0.37a3bc43/condition,"@style","comp","display:none")] String.js:169:41
    //  * through: v.wrapRec(items/#0.71d8960d/condition,"comp","span")

    test "moveBefore updates references added in extra edits" {
      let actual = 
        moveMultiBefore 
          (WrapRecord(KeepReferences, "comp", "span", !/"/items/0/condition"))
          ( ListAppend(!/"/items", "0", None, Record("li", OrdList.empty)),
            [RecordAdd(!/"/items/0/condition", "left", None, Reference(Relative, !/"./../../done/@checked"))] )
      formatEdit actual.[1]
      |> equals """recordAdd(items/0/condition,"left",na,./../../../done/@checked)"""
    }
]


[<Tests>]
let evalTests =
  testList "interaction and evaluation" [    

    test "incrementing counter invalidates evalauted result" {
      let doc1 = applyHistory (rcd "div") (opsBaseCounter @ opsCounterInc)
      let evalOps = Eval.evaluateAll doc1
      let doc2 = applyHistory (rcd "div") (opsBaseCounter @ opsCounterInc @ evalOps)

      let mergedOps, _ = 
        mergeHistories RemoveConflicting 
          (opsBaseCounter @ opsCounterInc @ opsCounterInc) 
          (opsBaseCounter @ opsCounterInc @ evalOps)
      let doc3 = applyHistory (rcd "div") mergedOps

      doc2 |> selectTag (!/"/counter/value") |> equals (Some "x-evaluated")
      doc2 |> select (!/"/counter/value/result") |> equals [Primitive(Number 1.0)]

      doc3 |> selectTag (!/"/counter/value") |> equals (Some "x-formula")
      doc3 |> select (!/"/counter/value/result") |> equals []
    }

    test "adding speaker invalidates evaluated results" {
      let doc1 = applyHistory (rcd "div") (opsCore @ opsBudget)
      let evalOps = Eval.evaluateAll doc1
      let doc2 = applyHistory (rcd "div") (opsCore @ opsBudget @ evalOps)

      let mergedOps, _ = 
        mergeHistories RemoveConflicting 
          (opsCore @ opsBudget @ addSpeakerOps) 
          (opsCore @ opsBudget @ evalOps)
      let doc3 = applyHistory (rcd "div") mergedOps

      doc2 |> selectTag (!/"/ultimate/item") |> equals (Some "x-evaluated")
      doc2 |> select (!/"/ultimate/item/result") |> equals [Primitive(Number 3500.0)]
      doc3 |> selectTag (!/"/ultimate/item") |> equals (Some "x-formula")
      doc3 |> select (!/"/ultimate/item/result") |> equals []
    }

    // This is straightforwardly adding the wrapping interactions to the end of the list
    // (i.e. as if you were always doing this by hand repeatedly)
    test "counter can increment state" {
      let ops1 = opsBaseCounter 
      let doc1 = applyHistory (rcd "div") ops1
      select [Field "counter"; Field "value"] doc1 |> equals [ Primitive(Number 0.0) ]
      
      let ops2 = ops1 @ opsCounterInc
      let doc2 = applyHistory (rcd "div") ops2
      let ops3 = ops2 @ Eval.evaluateOne doc2
      let doc3 = applyHistory (rcd "div") ops3
      select [Field "counter"; Field "value"; Field "result"] doc3 |> equals [ Primitive(Number 1.0) ]

      let ops4 = ops3 @ opsCounterInc
      let doc4 = applyHistory (rcd "div") ops4
      let ops5 = ops4 @ Eval.evaluateOne doc4
      let doc5 = applyHistory (rcd "div") ops5
      select [Field "counter"; Field "value"; Field "result"] doc5 |> equals [ Primitive(Number 2.0) ]
    }

    // A more interesting case is when we 'replay' past interactions, because then they are
    // appended onto a base (when they were saved) and are merged with current state
    // (clicking the 'Inc' button twice, merges the current ops with base @ replay twice)
    test "counter can merge increment operations" {
      let currentOps = opsBaseCounter @ opsCounterInc @ opsCounterHndl (opsBaseCounter @ opsCounterInc)
      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)

      let docUnevaluated = applyHistory (rcd "div") currentOps
      let opsEvaluated = currentOps @ Eval.evaluateAll docUnevaluated
      let docEvaluated = applyHistory (rcd "div") opsEvaluated
      select [Field "counter"; Field "value"; Field "result"] docEvaluated |> equals [ Primitive(Number 3.0) ]
    }

    // Even more elaborate case where we click, evaluate, click again, re-evaluate
    test "counter can invalidate after reevaluating" {
      let currentOps1 = 
        opsBaseCounter @ opsCounterInc @ opsCounterHndl (opsBaseCounter @ opsCounterInc)      
      let currentOps2, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps1 (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let currentDoc1 = applyHistory (rcd "div") currentOps2
      
      let evalOps1 = Eval.evaluateAll currentDoc1
      let currentDoc2 = applyHistory (rcd "div") (currentOps2 @ evalOps1)
      select (!/"/counter/value/result") currentDoc2 |> equals [Primitive(Number 2.0)]

      let currentOps3, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps2 (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let evalOps2 = Eval.updateEvaluatedEdits currentOps2 currentOps3 evalOps1
      let currentDoc3 = applyHistory (rcd "div") (currentOps3 @ evalOps2)
      selectTag (!/"/counter/value") currentDoc3 |> equals (Some "x-formula")
      select (!/"/counter/value/result") currentDoc3 |> equals []

      let evalOps3 = evalOps2 @ Eval.evaluateAll currentDoc3
      let currentDoc4 = applyHistory (rcd "div") (currentOps3 @ evalOps3)
      select (!/"/counter/value/result") currentDoc4 |> equals [Primitive(Number 3.0)]
    }
  ]

  
[<Tests>]
let basicMergeTests =
  testList "basic merging" [
    test "merge rename" {
      let ops1 = [ uidS [Field "test"] "f1" "f2" ]
      let ops2 = [ uidS [Field "test"] "f1" "f3" ]
      merge ops1 ops2 |> equals [ uidS [Field "test"] "f1" "f2"; uidS [Field "test"] "f2" "f3" ]
      merge ops2 ops1 |> equals [ uidS [Field "test"] "f1" "f3"; uidS [Field "test"] "f3" "f2" ]
    }
  ]

[<Tests>]
let complexMergeTests =
  testList "complex merging" [    
    test "merging two appends with edits inside list item" {
      let ops1 = todoBaseOps @ todoAddOps "first" "First work"
      let ops2 = todoBaseOps @ todoAddOps "second" "Second work"
      let merged = merge ops1 ops2
      let doc = applyHistory (rcd "div") merged
      select (!/"/items/#first/entry/work") doc |> equals [Primitive (String "First work")]
      select (!/"/items/#second/entry/work") doc |> equals [Primitive (String "Second work")]        
    }

    test "indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = applyHistory (rcd "div") ops2 
      doc1 |> equals doc2
    }

    test "refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = applyHistory (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with two step adding" {
      let ops1 = merge (opsCore @ addSpeakerTwoStepOps) (opsCore @ refactorListOps)
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerTwoStepOps) 
      let doc2 = applyHistory (rcd "div") ops2
      doc1 |> equals doc2
      ()
    }

    test "refactoring merges with name fix" {
      let ops1 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
      let doc2 = applyHistory (rcd "div") ops2 
      doc1 |> equals doc2 
    }

    test "adding speaker directly and via temp is the same" {
      let ops1 = opsCore @ addSpeakerViaTempOps 
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = opsCore @ addSpeakerOps 
      let doc2 = applyHistory (rcd "div") ops2 
      doc1 |> equals doc2 
    }

    test "refactoring merges with adding via temp" {
      let ops1 = merge (opsCore @ addSpeakerViaTempOps) (opsCore @ refactorListOps)
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerViaTempOps) 
      let doc2 = applyHistory (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with adding two speakers by PBD" {
      let pbdCore = opsCore @ pbdAddInput
      let ops1 = merge (pbdCore @ refactorListOps) (pbdCore @ pbdAddFirstSpeaker @ pbdAddAnotherSpeaker) 
      let doc1 = applyHistory (rcd "div") ops1 
      let ops2 = merge (pbdCore @ pbdAddFirstSpeaker @ refactorListOps) (pbdCore @ pbdAddAnotherSpeaker)
      let doc2 = applyHistory (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "adding budget merges with refactoring" {
      let ops1 = merge (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = applyHistory (rcd "div") ops1
      let ops2 = merge (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = applyHistory (rcd "div") ops2
      doc1 |> equals doc2 
    }
  ]

[<Tests>]
let referenceUpdateTests =
  let doc0 = Record("div", OrdList.ofList [
    "first", Reference(Relative, [DotDot; Field "things"; Index "0"; Field "lbl"])
    "things", List("ul", OrdList.ofList [  
      "0", Record("li", OrdList.ofList ["lbl", Primitive(String "abc"); 
        "ref1", Reference(Relative, [DotDot; Field "lbl"]); 
        "ref2", Reference(Relative, [DotDot; DotDot; DotDot; Field "first"]) ])
      "1", Record("li", OrdList.ofList ["lbl", Primitive(String "def"); 
        "ref1", Reference(Relative, [DotDot; Field "error"; DotDot; Field "lbl"]);
        "ref2", Reference(Relative, [DotDot; DotDot; Index "0"; Field "lbl"])])
    ])
  ])


  testList "reference updating" [
    test "wrap record" {
      let doc1 = WrapRecord(UpdateReferences, "list", "section", [Field "things"]) |> mkEd |> apply doc0 

      select [Field "first"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "things"; Field "list"; Index "0"; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index "0"; Field "ref1"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index "0"; Field "ref2"] doc1 
      |> equals [ Reference(Relative, [DotDot; DotDot; DotDot; DotDot; Field "first"]) ]
      select [Field "things"; Field "list"; Index "1"; Field "ref1"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index "1"; Field "ref2"] doc1 
      |> equals [ Reference(Relative, [DotDot; DotDot; Index "0"; Field "lbl"]) ]
    }
  ]

open Tbd.OrdList

[<Tests>]
let ordListTests = 
  let l = 
    { Members = Map.ofList [ 1,"one"; 2,"two"; 3,"three" ]; 
      Order = Map.ofList [ 1,2; 2,3; ]  }
  let l2 = 
    OrdList.empty |> OrdList.add (3, "three") None 
      |> OrdList.add (1, "one") (Some 2)  |> OrdList.add (2, "two") (Some 3)
  let l3 = 
    [ (0, "A"), None; (1, "A.A"), Some 0; (2, "A.A.A"), Some 1; (3, "A.A.A.A"), Some 2
      (10, "A.B"), Some 0; (20, "A.B.A"), Some 10; (30, "A.B.A.A"), Some 20
      (100, "A.C"), Some 0; (200, "A.C.A"), Some 100; (300, "A.C.A.A"), Some 200 ]
    |> Seq.map (fun ((k1,v), k2) -> ((hash $"key {k1}", v), Option.map (fun k2 -> hash $"key {k2}") k2))
    |> Seq.fold (fun ol (el, pred) -> OrdList.add el pred ol) OrdList.empty

  testList "OrdList tests" [
    test "OrdLists sorting keeps things together" {
      l3 |> OrdList.toSeq |> Seq.map snd |> List.ofSeq 
        |> List.tail |> List.chunkBySize 3 |> List.sort
        |> equals [["A.A"; "A.A.A"; "A.A.A.A"]; ["A.B"; "A.B.A"; "A.B.A.A"]; ["A.C"; "A.C.A"; "A.C.A.A"]]
    }
    test "OrdList iterator works" {
      l |> List.ofSeq
      |> equals [(3, "three"); (2, "two"); (1, "one")]
    }
    test "OrdList.after works" {
      l |> OrdList.after 1 2 
      |> equals true
      l |> OrdList.after 1 3 
      |> equals true
    }
    test "OrdList.tryLastKey works" {
      l |> OrdList.tryLastKey
      |> equals (Some 1)
    }
    test "OrdList.remove works" {
      let lrem = l |> OrdList.remove 2
      lrem |> OrdList.after 3 1
      |> equals false
      lrem |> OrdList.after 1 3
      |> equals true
    }
    test "OrdList.renameKey works" {
      let lren = l |> OrdList.renameKey 2 20
      lren |> List.ofSeq
      |> equals [(3, "three"); (20, "two"); (1, "one")]
    }
    test "OrdList iterator works on constructed" {
      [ for k, v in l2 -> k, v ]
      |> equals [(3, "three"); (2, "two"); (1, "one")]
    }
  ]