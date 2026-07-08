-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Runtime.LanguageFile
Layer: Runtime
Purpose: A small external file format for runnable MeTTaIL dialects. A file declares sorts, prefix
  syntax constructors, and base rewrites, then the CLI can run a term through the verified generic
  runtime. The product-facing path is: edit a file, run `LeaTTa --mettail FILE --term TERM`, and the
  result is computed by `runInstMono`.
Imports: MeTTaIL.Runtime.Generic
Trusted boundary: none
Main exports: parseInst, parsePresentation, runSource
Open obligations: this is not the full BNFC MeTTaIL parser. The file format covers the CLI runtime path:
  sorts, prefix constructors, and base rewrites. Richer syntax can elaborate to the same `TheoryInst`.
-/
import MeTTaIL.Runtime.Generic

namespace MeTTaIL
namespace LanguageFile

/-- Declarations collected from one external dialect file. -/
structure Decls where
  exports : List Export := []
  terms : List Rule := []
  rewrites : List RewriteDecl := []
deriving Inhabited

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

def dropWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then dropWs cs else c :: cs

/-- Trim ASCII whitespace from both ends of a string. -/
def trim (s : String) : String :=
  String.ofList ((dropWs (dropWs s.toList).reverse).reverse)

/-- Split a string into non-empty whitespace-separated words. -/
def words (s : String) : List String :=
  (((trim s).replace "\t" " ").splitOn " ").filter (fun w => w != "")

/-- Strip `#` comments and surrounding whitespace. -/
def cleanLine (s : String) : String :=
  trim ((s.splitOn "#").head?.getD "")

def err {α : Type} (line : Nat) (msg : String) : Except String α :=
  .error ("line " ++ toString line ++ ": " ++ msg)

/-- Split at the first occurrence of `sep`, keeping later occurrences in the right side. -/
def splitOne (line : Nat) (sep raw : String) : Except String (String × String) :=
  match raw.splitOn sep with
  | lhs :: rhs :: rest => .ok (trim lhs, trim (sep.intercalate (rhs :: rest)))
  | _ => err line ("expected `" ++ sep ++ "`")

def parseSimpleCat (line : Nat) (raw : String) : Except String Cat :=
  match words raw with
  | [name] => .ok (.idCat name)
  | [] => err line "expected a category name"
  | _ => err line "expected one category name"

def parseCatWords (line : Nat) : List String → Except String (List Cat)
  | [] => .ok []
  | w :: ws => do
      let c ← parseSimpleCat line w
      let cs ← parseCatWords line ws
      pure (c :: cs)

/-- Parse `A B -> C` or `C` into argument categories and the result category. -/
def parseSignature (line : Nat) (raw : String) : Except String (List Cat × Cat) :=
  match raw.splitOn "->" with
  | [out] => do
      let c ← parseSimpleCat line out
      pure ([], c)
  | [args, out] => do
      let argCats ← parseCatWords line (words args)
      let outCat ← parseSimpleCat line out
      pure (argCats, outCat)
  | _ => err line "expected at most one `->` in a term signature"

def parseTermDecl (line : Nat) (raw : String) (d : Decls) : Except String Decls := do
  let (name, sig) ← splitOne line ":" raw
  match words name with
  | [label] =>
      let (args, out) ← parseSignature line sig
      pure { d with terms := d.terms ++
        [{ label := .id label, cat := out, items := args.map Item.nterminal }] }
  | [] => err line "expected a term label"
  | _ => err line "term labels may not contain whitespace"

def parseAST (line : Nat) (raw : String) : Except String AST :=
  match parse raw with
  | some t => .ok t
  | none => err line ("could not parse term `" ++ raw ++ "`")

def parseRewriteDecl (line : Nat) (raw : String) (d : Decls) : Except String Decls := do
  let (name, body) ← splitOne line ":" raw
  let (lhsRaw, rhsRaw) ← splitOne line "=>" body
  match words name with
  | [rwName] =>
      let lhs ← parseAST line lhsRaw
      let rhs ← parseAST line rhsRaw
      pure { d with rewrites := d.rewrites ++
        [{ name := rwName, rw := .base lhs rhs }] }
  | [] => err line "expected a rewrite name"
  | _ => err line "rewrite names may not contain whitespace"

def parseLine (line : Nat) (d : Decls) (raw : String) : Except String Decls :=
  let s := cleanLine raw
  if s == "" then .ok d
  else if s.startsWith "sort " then do
    let c ← parseSimpleCat line ((s.drop 5).toString)
    pure { d with exports := d.exports ++ [.base c] }
  else if s.startsWith "term " then
    parseTermDecl line ((s.drop 5).toString) d
  else if s.startsWith "rewrite " then
    parseRewriteDecl line ((s.drop 8).toString) d
  else
    err line "expected `sort`, `term`, or `rewrite`"

def parseLines : List String → Nat → Decls → Except String Decls
  | [], _, d => .ok d
  | l :: ls, n, d => do
      let d' ← parseLine n d l
      parseLines ls (n + 1) d'

def Decls.toTheoryInst (d : Decls) : TheoryInst :=
  .addRewrites (.addTerms (.addExports .empty d.exports) d.terms) d.rewrites

/-- Parse an external dialect file into the theory-instance algebra. -/
def parseInst (src : String) : Except String TheoryInst := do
  let d ← parseLines (src.splitOn "\n") 1 {}
  pure d.toTheoryInst

/-- Parse and elaborate an external dialect file into a presentation. -/
def parsePresentation (src : String) : Except String Presentation := do
  let ti ← parseInst src
  elaborate {} ti

/-- Run a term through the presentation described by an external dialect file. -/
def runSource (src : String) (fuel : Nat) (term : String) : Except String (Option String) := do
  let ti ← parseInst src
  runInstMono {} ti fuel term

end LanguageFile
end MeTTaIL
