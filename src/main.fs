module Denicek.App.Main

open Denicek.App
open Browser.Dom

// --------------------------------------------------------------------------------------
// Application state
// --------------------------------------------------------------------------------------

if document.URL.Contains("webnicek.html") then
  Webnicek.Loader.start ()

if document.URL.Contains("datnicek.html") then
  Datnicek.Loader.start ()