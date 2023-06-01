#if INTERACTIVE
#load "../src/doc.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc

let applyAll = List.fold apply (rcd "root" "div")

[<Tests>]
let evalTests =
  testList "merging" [    
    //opsCore @ opsBudget
  ]

[<Tests>]
let mergeTests =
  testList "merging" [    
    test "indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = applyAll ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = applyAll ops2 
      doc1 |> equals doc2
    }

    test "refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = applyAll ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = applyAll ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with name fix" {
      let ops1 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = ops1 |> List.fold apply (rcd "root" "div")
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
      let doc2 = ops2 |> List.fold apply (rcd "root" "div")
      doc1 |> equals doc2 
    }

    test "adding budget merges with refactoring" {
      let ops1 = merge (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = ops1 |> List.fold apply (rcd "root" "div")
      let ops2 = merge (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = ops2 |> List.fold apply (rcd "root" "div")
      doc1 |> equals doc2 
    }
  ]




