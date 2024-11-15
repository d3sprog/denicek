module Tbd.TestRunner
open Expecto
open Tbd.Tests

[<EntryPoint>]
let main argv =
    Tests.runTestsInAssemblyWithCLIArgs [] argv
    //Tests.runTestsWithCLIArgs [] argv referenceUpdateTests
