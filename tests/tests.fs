#if INTERACTIVE
#nowarn "3353"
#I "../src"
#load "utils.fs" "parsec.fs" "doc.fs" "represent.fs" "eval.fs" "demos.fs"
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


[<Tests>]
let adhocTests =
  testList "ad hoc tests" [
    (*
    TODO: This way of recording add-item interaction does not currently work
    (partly because of "applyToAdded: Source out of scope (TODO)" error and partly
    because we would have to use histhash for saved-interactions from a point
    before the edits - now we use just after and so replay really overwrites 0th item).
    
    test "merging two appends" {
      let ops1 = todoBaseOps @ todoAddOps "First work"
      let ops2 = todoBaseOps @ todoAddOps "Second work"
      let merged = merge ops1 ops2
      let doc = applyHistory (rcd "div") merged
        
    }
    *)
    test "scopeEdit can scope edit that adds unrelated reference" {
      let actual = 
        scopeEdit
          (!/"/items/*")
          (!/"/$uniquetemp_7")
          { Kind = Value(RecordAdd(!/"/items/*/condition", "left", Reference(Relative, [DotDot])))
            GroupLabel = ""; Dependencies = []; Disabled = false }
      ( match actual with InScope _ -> "inscope" | _ -> "" )
      |> equals "inscope"
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
  let mkEd ed = 
    { Kind = ed; GroupLabel = ""; Dependencies = []; Disabled = false } 

  let doc0 = Record("div", [
    "first", Reference(Relative, [DotDot; Field "things"; Index 0; Field "lbl"])
    "things", List("ul", [  
      Record("li", ["lbl", Primitive(String "abc"); 
        "ref1", Reference(Relative, [DotDot; Field "lbl"]); 
        "ref2", Reference(Relative, [DotDot; DotDot; DotDot; Field "first"]) ])
      Record("li", ["lbl", Primitive(String "def"); 
        "ref1", Reference(Relative, [DotDot; Field "error"; DotDot; Field "lbl"]);
        "ref2", Reference(Relative, [DotDot; DotDot; Index 0; Field "lbl"])])
    ])
  ])


  testList "reference updating" [
    test "move copy before wrap" {
      let ed = 
        moveBefore { UniqueTempField = "xx"; PrefixEdits = []; SuffixEdits = [] }
          (mkEd (Shared(ValueKind, Copy(!/"/temp/lbl/desc", !/"/form/input/@value"))))
          (mkEd (Shared(StructuralKind, WrapRecord("comp", "span", !/"/items/*/condition"))))
      ()    
    }
    test "wrap record" {
      let doc1 = 
        Shared(StructuralKind, WrapRecord("list", "section", [Field "things"]))
        |> mkEd |> apply doc0 

      select [Field "first"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "things"; Field "list"; Index 0; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index 0; Field "ref1"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index 0; Field "ref2"] doc1 
      |> equals [ Reference(Relative, [DotDot; DotDot; DotDot; DotDot; Field "first"]) ]
      select [Field "things"; Field "list"; Index 1; Field "ref1"] doc1 
      |> equals [ Reference(Relative, [DotDot; Field "lbl"]) ]
      select [Field "things"; Field "list"; Index 1; Field "ref2"] doc1 
      |> equals [ Reference(Relative, [DotDot; DotDot; Index 0; Field "lbl"]) ]
    }
  ]


