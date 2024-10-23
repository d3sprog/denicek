module Tbd.Represent
open Tbd.Doc

// --------------------------------------------------------------------------------------
// Representing edits as nodes
// --------------------------------------------------------------------------------------
  
let (|Lookup|) args = dict args
let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  if d.ContainsKey k then Some(d.[k]) else None
let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
let (|Findn|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(Number n) -> Some (int n) | _ -> None
let (|Findsk|_|) (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue("kind") with 
  | true, Primitive(String "structural") -> Some(StructuralKind)
  | true, Primitive(String "value") -> Some(ValueKind)
  | true, v -> failwith $"Findsk: expected 'structural' or 'value' but got '{v}'"
  | _ -> None
let rcd id kvp = Record(id, kvp)

let representKind = function
  | StructuralKind -> "kind", Primitive(String "structural")
  | ValueKind -> "kind", Primitive(String "value")

let representSel sel = 
  List("x-selectors", 
    [ for s in sel ->
        match s with 
        | All -> Primitive(String "*")
        | Tag t -> Primitive(String("#" + t))
        | Index n -> Primitive(Number n)
        | Field f -> Primitive(String f) ])

let unrepresentSel expr =
  match expr with 
  | List("x-selectors", sels) ->
      sels |> List.map (function 
        | Primitive(String "*") -> All 
        | Primitive(String s) when s.Length <> 0 && s.[0] = '#' -> Field (s.Substring(1))
        | Primitive(String s) -> Field s
        | Primitive(Number n) -> Index (int n)
        | _ -> failwith "unrepresentSel: Invalid selector")
  | _ -> failwith $"unrepresentSel: Not a selector: {expr}"

let representIntList ns =
  List("x-int-list", [for n in ns -> Primitive(Number(float n)) ])

let unrepresentIntList nd =
  match nd with 
  | List("x-int-list", nds) ->
      List.map (function Primitive(Number n) -> int n | _ -> failwith "unrepresentIntList - Not a number") nds
  | _ -> failwith $"unrepresentIntList - Invalid node {nd}"

let representCond cond = 
  match cond with 
  | EqualsTo(nd) -> [ "node", Primitive nd ] |> rcd "x-cond-equals"
  | NonEmpty -> [] |> rcd "x-cond-nonempty"

let unrepresentCond nd = 
  match nd with 
  | Record("x-cond-equals", Lookup(Find "node" (Primitive v))) -> EqualsTo(v)
  | Record("x-cond-nonempty", []) -> NonEmpty
  | _ -> failwith $"unrepresentCond - Invalid node {nd}"

let unrepresent nd = 
  // NOTE: This works if the 'match' is not wrapped inside another expression (e.g. let) otherwise
  // Fable creates 600MB JavaScript file (https://x.com/tomaspetricek/status/1845753585163731319)
  let ret nd = { Kind = nd; Dependencies = []; GroupLabel = ""; Disabled = false }
  match nd with
  // Value edits
  | Record("x-edit-append", Lookup (Find "target" sel & Find "node" nd)) ->
      Value(ListAppend(unrepresentSel sel, nd)) |> ret
  | Record("x-edit-appendfrom", Lookup (Find "target" sel & Find "src" src)) ->
      Value(ListAppendFrom(unrepresentSel sel, unrepresentSel src)) |> ret
  | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "node" nd)) ->
      Value(RecordAdd(unrepresentSel sel, f, nd)) |> ret
  | Record("x-edit-check", Lookup (Find "target" tgt & Find "cond" cond)) ->
      Value(Check(unrepresentSel tgt, unrepresentCond cond)) |> ret
  | Record("x-edit-primitive", Lookup (Find "target" tgt & Finds "op" op & Finds "arg" arg)) ->
      Value(PrimitiveEdit(unrepresentSel tgt, op, Some arg)) |> ret
  | Record("x-edit-primitive", Lookup (Find "target" tgt & Finds "op" op)) ->
      Value(PrimitiveEdit(unrepresentSel tgt, op, None)) |> ret
  // Shared edits
  | Record("x-edit-wraprec", Lookup(Findsk sk & Finds "tag" tag & Finds "fld" id & Find "target" target)) ->
      Shared(sk, WrapRecord(tag, id, unrepresentSel target)) |> ret
  | Record("x-edit-renamefld", Lookup (Findsk sk & Find "target" sel & Finds "old" fold & Finds "new" fnew)) ->
      Shared(sk, RecordRenameField(unrepresentSel sel, fold, fnew)) |> ret
  | Record("x-edit-copy", Lookup (Findsk sk & Find "target" tgt & Find "source" src)) ->
      Shared(sk, Copy(unrepresentSel tgt, unrepresentSel src)) |> ret
  | Record("x-edit-listdelete", Lookup (Findsk sk & Find "target" tgt & Findn "index" i)) ->
      Shared(sk, ListDelete(unrepresentSel tgt, i)) |> ret
  | Record("x-edit-recdelete", Lookup (Findsk sk & Find "target" tgt & Finds "field" fld)) ->
      Shared(sk, RecordDelete(unrepresentSel tgt, fld)) |> ret
  | Record("x-edit-wraplist", Lookup (Findsk sk & Find "target" tgt & Finds "tag" tag)) ->
      Shared(sk, WrapList(tag, unrepresentSel tgt)) |> ret
  | Record("x-edit-listreorder", Lookup (Findsk sk & Find "target" tgt & Find "perm" perm)) ->
      Shared(sk, ListReorder(unrepresentSel tgt, unrepresentIntList perm)) |> ret
  | Record("x-edit-updatetag", Lookup (Findsk sk & Find "target" tgt & Finds "old" otag & Finds "new" ntag)) ->
      Shared(sk, UpdateTag(unrepresentSel tgt, otag, ntag)) |> ret
  | _ -> failwith $"unrepresent - Missing case for: {nd}"

let represent op = 
  let ps v = Primitive(String v)
  let pn i = Primitive(Number i)
  match op.Kind with 
  // Value edits
  | Value(ListAppend(target, nd)) ->
      rcd "x-edit-append" [ "target", representSel target; "node", nd ]
  | Value(ListAppendFrom(target, src)) ->
      rcd "x-edit-appendfrom" [ "target", representSel target; "src", representSel src ]
  | Value(RecordAdd(target, f, nd)) ->
      rcd "x-edit-add" [ "target", representSel target; "field", ps f; "node", nd ]
  | Value(Check(target, cond)) -> 
      rcd "x-edit-check" [ "target", representSel target; "cond", representCond cond ]
  | Value(PrimitiveEdit(target, op, None)) ->
      rcd "x-edit-primitive" [ "target", representSel target; "op", ps op ]
  | Value(PrimitiveEdit(target, op, Some arg)) ->
      rcd "x-edit-primitive" [ "target", representSel target; "op", ps op; "arg", ps arg ]
  // Shared edits
  | Shared(sk, WrapRecord(tag, id, target)) ->
      rcd "x-edit-wraprec" [ "tag", ps tag; "fld", ps id; "target", representSel target; representKind sk ] 
  | Shared(sk, RecordRenameField(target, fold, fnew)) ->
      rcd "x-edit-renamefld" [ "target", representSel target; "old", ps fold; "new", ps fnew; representKind sk ]
  | Shared(sk, Copy(target, source)) ->
      rcd "x-edit-copy" [ "target", representSel target; "source", representSel source; representKind sk ]
  | Shared(sk, ListDelete(target, i)) ->
      rcd "x-edit-listdelete" [ "target", representSel target; representKind sk; "index", pn i ]
  | Shared(sk, RecordDelete(target, fld)) ->
      rcd "x-edit-recdelete" [ "target", representSel target; representKind sk; "field", ps fld ]
  | Shared(sk, WrapList(tag, target)) ->
      rcd "x-edit-wraplist" [ "target", representSel target; "tag", ps tag; representKind sk ]
  | Shared(sk, ListReorder(target, perm)) ->
      rcd "x-edit-listreorder" [ "target", representSel target; "perm", representIntList perm; representKind sk ]
  | Shared(sk, UpdateTag(target, otag, ntag)) ->
      rcd "x-edit-updatetag" [ "target", representSel target; "old", ps otag; "new", ps ntag; representKind sk ]

