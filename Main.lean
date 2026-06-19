import MettaHyperonFull.Minimal.Stdlib

open Metta
open Metta.Runtime
open Metta.Minimal

/-- Default demo program, run on the minimal MeTTa interpreter. -/
def demoSource : String := "(= (double $x) ($x $x)) !(double Bob)"

/-- Resolve an `import!` name to a file, given the module **catalog** (`register-module!` roots) and
    the importing file's directory:
    * a plain name `c2_spaces_kb` → the sibling `c2_spaces_kb.metta`;
    * a **namespaced** name `chaining:dtl:utils` → the registered root for module `chaining` joined
      with the sub-path `dtl/utils` and the `.metta` extension, i.e. `<root>/dtl/utils.metta`.
    This mirrors Hyperon's module catalog: `register-module!` names a root by its basename, and
    `:` is the namespace separator into that root. -/
def resolveImport (catalog : Std.HashMap String System.FilePath) (dir : System.FilePath)
    (name : String) : Option System.FilePath :=
  match name.splitOn ":" with
  | [] => none
  | [single] => some (dir.join ⟨single ++ ".metta"⟩)
  | mod :: segs => (catalog.get? mod).map fun root =>
      ⟨(segs.foldl (fun acc s => acc ++ "/" ++ s) (toString root)) ++ ".metta"⟩

/-- Recursively read every module reachable from a program via `import!`, resolved through the
    `register-module!` catalog. `register-module!` roots are recorded relative to the *declaring*
    file's directory (basename = module name); namespaced imports resolve against them. The
    transitive closure is followed (an imported module may itself register/import), with `fuel`
    bounding depth and `visited` guarding against cycles. Builds the `name → atoms` map the pure
    interpreter consults for `import!`. Missing/unparsable modules are skipped. -/
def loadImportsFuel : Nat → Std.HashMap String System.FilePath → List String → System.FilePath →
    List Atom → Std.HashMap String (List Atom) → IO (Std.HashMap String (List Atom))
  | 0, _, _, _, _, acc => pure acc
  | fuel + 1, catalog0, visited, dir, atoms, acc => do
      -- extend the catalog with this file's `register-module!` roots (relative to its own dir)
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

/-- Read and parse every module a program `import!`s (transitively, through the `register-module!`
    catalog), building the `name → atoms` map the pure runner consults for `import!`. This is the
    one piece of `import!` that is genuinely IO; the instruction itself is pure. -/
def loadImports (path : String) (src : String) : IO (Std.HashMap String (List Atom)) := do
  let dir := (System.FilePath.mk path).parent.getD (System.FilePath.mk ".")
  match parseProgram src with
  | Except.error _ => pure Std.HashMap.emptyWithCapacity
  | Except.ok atoms => loadImportsFuel 64 Std.HashMap.emptyWithCapacity [] dir atoms Std.HashMap.emptyWithCapacity

/-- CLI entry point. Everything runs on the faithful **minimal MeTTa interpreter + stdlib**
    (`Minimal/`): the assembly language of MeTTa, with the stdlib written over its 12 instructions.
    (An earlier four-register "MeTTa-style" runtime, `Runtime.CLI`, is retired in favour of this
    faithful interpreter; see `MettaHyperonFull.lean`.)
    * no arguments: run a demo program;
    * `--file PATH` / `--min-file PATH`: run a `.metta` file;
    * `--min PROGRAM`: run a program string;
    * `--oracle PATH`: run a test file's `!`-assertions, reporting how many evaluate to `()`. -/
def main : List String → IO UInt32
  | ["--file", path] | ["--min-file", path] => do
      let src ← IO.FS.readFile path
      let imports ← loadImports path src
      IO.println (runMinimalSource src (imports := imports))
      pure 0
  | ["--oracle", path] => do
      -- Run every `!`-assertion in a MeTTa test file through the minimal interpreter, sequentially
      -- (atoms processed in file order); an assertion passes iff it evaluates to the unit atom `()`.
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
