#if INTERACTIVE
#load "../src/doc.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc

let evaluate = List.fold apply (rcd "root" "div")

[<Tests>]
let tests =
  testList "merging" [
    
    test "indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = evaluate ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = evaluate ops2 
      doc1 |> equals doc2
    }

    test "refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = evaluate ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = evaluate ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with name fix" {
      let ops1 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = ops1 |> List.fold apply (rcd "root" "div")
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
      let doc2 = ops2 |> List.fold apply (rcd "root" "div")
      doc1 |> equals doc2 
    }
  ]




