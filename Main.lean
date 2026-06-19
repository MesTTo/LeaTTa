import MettaHyperonFull.Minimal.Stdlib

open Metta
open Metta.Runtime
open Metta.Minimal

/-- A short demo program used when LeaTTa is invoked with no arguments. -/
def demoSource : String := "(= (double $x) ($x $x)) !(double Bob)"

/-- Resolve an `import!` name to a file path, given the module catalog and the importing file's
    directory. Two forms are handled:
    * a plain name `c2_spaces_kb` resolves to the sibling file `c2_spaces_kb.metta`;
    * a namespaced name `chaining:dtl:utils` resolves to `<root>/dtl/utils.metta`, where `<root>`
      is the path registered for module `chaining` by `register-module!`.
    The `:` separator and `register-module!` catalog match Hyperon's module system. -/
def resolveImport (catalog : Std.HashMap String System.FilePath) (dir : System.FilePath)
    (name : String) : Option System.FilePath :=
  match name.splitOn ":" with
  | [] => none
  | [single] => some (dir.join ⟨single ++ ".metta"⟩)
  | mod :: segs => (catalog.get? mod).map fun root =>
      ⟨(segs.foldl (fun acc s => acc ++ "/" ++ s) (toString root)) ++ ".metta"⟩

/-- Recursively load all modules reachable via `import!`, up to `fuel` levels deep. `catalog0` maps
    module names to their root paths (from `register-module!`). `visited` guards against import
    cycles. Missing or unparsable modules are silently skipped. Returns the accumulated
    `name → atoms` map that the pure interpreter consults when it encounters `import!`. -/
def loadImportsFuel : Nat → Std.HashMap String System.FilePath → List String → System.FilePath →
    List Atom → Std.HashMap String (List Atom) → IO (Std.HashMap String (List Atom))
  | 0, _, _, _, _, acc => pure acc
  | fuel + 1, catalog0, visited, dir, atoms, acc => do
      -- Extend the catalog with any `register-module!` roots declared in this file.
      let catalog := (collectModuleRoots atoms).foldl (fun (c : Std.HashMap String System.FilePath) p =>
          let abs := dir.join ⟨p⟩
          c.insert (abs.fileName.getD p) abs) catalog0
      (collectImports atoms).foldlM (init := acc) fun m name => do
        if visited.contains name then pure m
        else match resolveImport catalog dir name with
          | none => pure m
          | some fp =>
              if ← fp.pathExists then
                match parseProgram (← IO.FS.readFile fp) with
                | Except.ok fatoms =>
                    loadImportsFuel fuel catalog (name :: visited) (fp.parent.getD dir) fatoms
                      (m.insert name fatoms)
                | Except.error _ => pure m
              else pure m

/-- Load all modules a program imports, transitively. Returns the `name → atoms` map for `import!`.
    IO is limited to reading files; the `import!` instruction itself is pure. -/
def loadImports (path : String) (src : String) : IO (Std.HashMap String (List Atom)) := do
  let dir := (System.FilePath.mk path).parent.getD (System.FilePath.mk ".")
  match parseProgram src with
  | Except.error _ => pure Std.HashMap.emptyWithCapacity
  | Except.ok atoms => loadImportsFuel 64 Std.HashMap.emptyWithCapacity [] dir atoms Std.HashMap.emptyWithCapacity

/-- CLI entry point for LeaTTa. Runs on the minimal MeTTa interpreter and stdlib (`Minimal/`).
    * no arguments: run the demo program;
    * `--file PATH` / `--min-file PATH`: run a `.metta` file;
    * `--min PROGRAM`: run a program string;
    * `--oracle PATH`: run a test file's `!`-assertions and report how many evaluate to `()`.
    An earlier `Runtime.CLI` four-register runner was retired; see `MettaHyperonFull.lean`. -/
def main : List String → IO UInt32
  | ["--file", path] | ["--min-file", path] => do
      let src ← IO.FS.readFile path
      let imports ← loadImports path src
      IO.println (runMinimalSource src (imports := imports))
      pure 0
  | ["--oracle", path] => do
      -- Run every `!`-assertion through the minimal interpreter in file order.
      -- An assertion passes iff it evaluates to the unit atom `()`.
      let src ← IO.FS.readFile path
      let imports ← loadImports path src
      IO.println (oracleReport src (imports := imports))
      pure 0
  | "--min" :: rest => do
      IO.println (runMinimalSource (" ".intercalate rest))
      pure 0
  | [] => do
      IO.println (runMinimalSource demoSource)
      pure 0
  | args => do
      IO.println (runMinimalSource (" ".intercalate args))
      pure 0
