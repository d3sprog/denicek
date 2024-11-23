#if INTERACTIVE
#nowarn "3353"
#I "../src/utils" 
#load "utils.fs" "parsec.fs" "ordlist.fs"
let equals a b = a = b
#else
module Denicek.UtilsTests 
open Expecto
let equals a b = Expect.equal b a "Should equal"
#endif
open Denicek
open Denicek.OrdList

// --------------------------------------------------------------------------------------
// Tests for OrdList and Utils
// --------------------------------------------------------------------------------------

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

[<Tests>]
let utilsTests = testList "Utils tests" [
  test "partitionBy works on small example" {
    List.partitionBy [0;1;2;3] (List.ofSeq "abcdef")
    |> equals [[]; ['a']; ['b'; 'c']; ['d'; 'e'; 'f']]
  }
  
  test "filterWithState works on small example" {
    List.filterWithState (fun i v -> 
      if i < 3 && v % 2 = 0 then true, i+1
      else false, i) 0 [10 .. 20]
    |> equals [10; 12; 14]
  }

  test "chunkBy works on small example" {
    List.chunkBy snd [1,'a'; 2,'a'; 3,'b'; 4,'c'; 5,'c'; 6,'c'; 7,'d']
    |> List.map List.length
    |> equals [2;1;3;1]
  }
]

