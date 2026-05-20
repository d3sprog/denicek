# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

Denicek is an F# research codebase exploring an **edit-based document model**: documents are trees of `Record` / `List` / `Primitive` / `Reference` nodes, and all state is derived by applying a list of typed edits to an initial node. Two browser apps sit on top of this core:

- **Webnicek** (`src/webnicek.fs` → `public/webnicek.html`) — interactive structured-document editor with edit history, forking, and merging.
- **Datnicek** (`src/datnicek.fs` → `public/datnicek.html`) — data/computation app built on the same document + formula model.

The F# in `src/` compiles to JavaScript via **Fable 3.7.20** and is then bundled by webpack into `public/bundle.js`.

## Commands

```sh
npm install         # also runs `dotnet tool restore` (fable + femto)
npm start           # Fable watch + webpack-dev-server on http://localhost:8080
npm run build       # one-shot Fable compile + webpack bundle into public/
npm test            # builds and runs the Expecto test suite (tests/tests.fsproj)
npm run clean       # `dotnet fable clean` — wipes generated .fs.js next to sources
```

Single test / filter (Expecto): pass CLI args after `--`:
```sh
dotnet run --project tests/tests.fsproj -- --filter-test-list "moveBefore"
dotnet run --project tests/tests.fsproj -- --list-tests
```

The test project targets `net8.0` and the SDK is pinned by `global.json` to `8.0.400` (rollForward latestFeature). The library project (`src/app.fsproj`) targets `netstandard2.0` so it can be consumed by Fable. CI (`.github/workflows/build.yml`) still installs .NET 6 + Node 16 and runs `npm ci && npm run build && npm test`.

`*.fs.js` / `*.fs.js.map` / `bundle.js` are generated artifacts — do not edit them by hand; they live next to their `.fs` source and are gitignored.

## Architecture

### Core (used by both apps and the tests)

Compile order matters in F#; the `src/app.fsproj` `<Compile>` order is the dependency order. The conceptual layering:

1. **`src/utils/`**
   - `parsec.fs` — small parser-combinator library (used to parse selectors and transformation arguments).
   - `utils.fs` — shared helpers.
   - `ordlist.fs` — `OrdList<'k,'v>`: an order-preserving keyed list. This is the central collection backing both `Record` and `List` nodes, so changes here ripple everywhere.

2. **`src/doc/`** — the document model (no UI, no Fable-specific code; compiled into the test project as well).
   - `doc.fs` — `Node` (Record / List / Primitive / Reference), `Selector` (`All` / `Index` / `Field` / `DotDot`), reference resolution, prefix/match operations on selector paths, and the `Edit` / `EditKind` types (`RecordAdd`, `RecordDelete`, `RecordRenameField`, `ListAppend`, `ListDelete`, `ListReorder`, `UpdateTag`, `WrapRecord`, `WrapList`, `Copy`, `PrimitiveEdit`). Each structural edit carries a `ReferenceBehaviour` (`KeepReferences` vs `UpdateReferences`) — this distinction is load-bearing across the codebase.
   - `apply.fs` — `apply : Node -> Edit -> Node`, plus the table of named primitive `transformations` (`upper`, `replace`, `take-by`, etc.) used by `PrimitiveEdit`.
   - `merge.fs` — three-way merge of edit histories. `moveAllBefore` / `mergeHistories` are the public surface; they rescope selectors so an edit `e1` recorded against one history is rewritten to apply correctly when reordered before an edit `e2`. Most of the test suite (`tests/denicek.fs`) targets this file.

3. **`src/eval.fs`** — formulas. A formula is represented in the document as `<x-formula>` containing `<x-reference>` children; evaluation rewrites children to `<x-evaluated>` (with `formula` + `result` subfields) and finally replaces the formula itself. Evaluation is therefore expressed as more edits, not as a separate execution model.

4. **`src/represent.fs`** — round-trips between `Edit` values and `Node` values (edits-as-data, so edits can themselves live inside documents).

5. **`src/demos.fs`** — tiny DSL shortcuts (`rcd`, `lst`, `ap`, `add`, `wrV`/`wrS`, `cpV`/`cpS`, `!/"/path"`) for constructing nodes, selectors, and edits concisely. **Tests and demo data lean on this heavily; reuse it instead of building `Edit { Kind = ...; Dependencies = []; GroupLabel = "" }` records by hand.**

6. **`src/serializer.fs`** — JSON serialisation of nodes (used for the demo files in `public/demos/`).

7. **`src/matcher.fs`** — pattern matching on nodes (currently mostly commented-out exploratory code).

### Apps (Fable / browser only)

- `src/html.fs` — tiny virtual-DOM-ish helpers and a `Log` module with categorised, colourised `console.log`.
- `src/compost.fs` — minimal charting primitives.
- `src/webnicek.fs` — the document-editing app: state for the document, the edit history panel, cursor/navigation, and forking.
- `src/datnicek.fs` — the data app: an `EvaluationContext` with `DataFiles`, a `Type` / `Member` object model with `Invoke`, and `CompletionAction`s that propose edits.
- `src/main.fs` — entry point; dispatches on `document.URL` to `Webnicek.Loader.start ()` or `Datnicek.Loader.start ()`.

Webpack entry is `./src/main.fs.js` (the Fable-emitted output), so `npm start` requires Fable's watcher to be running — that's why the `start` script chains `dotnet fable watch ... --run webpack-dev-server`.

### Tests

`tests/tests.fsproj` `<Compile Include="../src/...">`s the core files directly (with `<Link>` to keep paths sane) and adds `tests/utils.fs` + `tests/denicek.fs`. The test file is also runnable in F# Interactive — note the `#if INTERACTIVE` block at the top that `#load`s sources and stubs out `Expect.equal`. Test runner is Expecto via `YoloDev.Expecto.TestSdk`; entry point is `tests/main.fs` (`runTestsInAssemblyWithCLIArgs`).

### Static assets

- `public/index.html` — landing page linking to the two apps.
- `public/demos/*.json` — serialised initial documents + edit histories used as fixtures by the apps.
- `public/data/` — sample CSV/TSV inputs for Datnicek.
- `experiments/*.fsx` — scratch scripts, not part of the build.
