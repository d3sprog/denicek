# Denicek

Denicek is a computational substrate for document-oriented end user programming.
It simplifies the implementation of programming experiences including 
collaborative source code editing, programming by demonstration, incremental
recomputation, schema change control, end-user debugging and concrete programming.

Denicek represents a program as a series of edits that construct and transform a 
document consisting of data and formulas. Denicek provides three operations on edit 
histories: edit application, merging of histories and conflict resolution.
The above programming experiences can be easily implemented by composing these 
three operations.

## Running

Denicek is written in [F#](https://fsharp.org/) using [Fable](https://fable.io/)
to target JavaScript. To run it, you will need .NET (version 8.0) and Node.js 
installed (version 22 works, others may too).

The process should be as simple as:

```
npm install
npm run start
```

This should do the trick. `npm install` will also run `dotnet tool restore` to 
install Fable. You can also run `npm run build` to build everything and
`npm run test` to run tests (this runs tests directly on .NET, not via JavaScript).

You can then open running demo at http://localhost:8080.

## How to use

This is an experimental prototype, so using it is tricky! 
The core of the system is a structure editor that you can use for creating documents.
If you have a document you can navigate around using arrows:

- Left/Right - jump into the next element, going into all children
- Up/Down - jump over the next element, skipping all children

The editing of document is done using commands. If you know the command,
just start typing it. Otherwise, you can type `?` for search. For example,
if you want to create an element, type `?add` and you will see commands
including "add record field". If you hit Enter, the start of the command
will be selected and you can type the parameters. To construct hello world:

```
:title=<h1>      // Add <h1> element
[right arrow]    // Move inside it
:value=Hello!    // Add text to element
[left arrow]     // Move outside h1
<marquee title>  // Wrap it in marquee!
```

Use `Alt+U` to switch between the document view and source view. You can
When you hit `Alt`, you will also get a pop-up with various other available
commands.

Use `Ctrl+Up` / `Ctrl+Down` to navigate through the history. You can toggle
the history panel (showing the past edits on the right) using `Alt+H`.

## Running demos

The panel above lists various demos such as _conf (add, rename, table, budget)_.
Clicking on these will load the demo. This can also be used to illustrate the 
merging functionality. Here is how things work:

- Clicking _conf_ will just replace what you have with a baseline history
  (shared with all version of the demo).
- Clicking any of _add, rename, table, budget_ will merge whatever you have
  with extra edits that add some more functionality (support for adding speakers,
  rename one of the speakers, refactor as table, add budget calculation).

This means that you can see how merging works. For example:

- Click on _conf_, then _add_ and _table_ - This first adds a speaker and then
  reconciles _table_ edits with those done by _add_ and refactor all items
  into a table.
- Click on _conf_, then _table_ and _add_ - This first refactors the list into
  a table and then reconciles _add_ edits with those done by _table_ and insert
  speaker as a new table row.

In this case, there are no conflicts and we can merge edits both ways!




