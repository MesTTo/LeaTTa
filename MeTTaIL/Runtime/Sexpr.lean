-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Runtime.Sexpr
Layer: Runtime
Purpose: A generic concrete syntax for any presentation: an S-expression reader and printer. A term is
  written `(label arg ...)` for an applied constructor, a bare atom for a nullary constructor, and `$x`
  for a pattern variable (matching MeTTa's variable sigil). This gives every dialect a uniform surface
  syntax for free, with no per-dialect parser. Parsing is fuel-bounded, so the reader is total with no
  `partial`.
Imports: MeTTaIL.Syntax
Trusted boundary: none
Main exports: tokenize, parseOne, parseArgs, parse, prettyPath, prettyLabel, pretty, prettyArgs
Open obligations: the reader is presentation-agnostic; validating symbols and arities against the
  presentation's symbol table, and richer surface syntax (grammar-driven), are future work.
-/
import MeTTaIL.Syntax

namespace MeTTaIL

/-- Split a string into parenthesis and atom tokens. -/
def tokenize (s : String) : List String :=
  (((s.replace "(" " ( ").replace ")" " ) ").splitOn " ").filter (fun t => t != "")

mutual
  /-- Parse one S-expression from a token list, returning it with the remaining tokens. `(label ...)`
      is an applied constructor, `$x` a variable, and any other atom a nullary constructor. -/
  def parseOne : Nat → List String → Option (AST × List String)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, tok :: rest =>
        if tok == "(" then
          match rest with
          | head :: more =>
              if head == "(" || head == ")" then none
              else (parseArgs fuel more).map (fun r => (AST.sexp (.id head) r.1, r.2))
          | [] => none
        else if tok == ")" then none
        else if tok.startsWith "$" then some (AST.var (.base (String.ofList (tok.toList.drop 1))), rest)
        else some (AST.sexp (.id tok) [], rest)
  /-- Parse a sequence of arguments up to the closing parenthesis. -/
  def parseArgs : Nat → List String → Option (List AST × List String)
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, toks =>
        match toks with
        | ")" :: rest => some ([], rest)
        | _ =>
            match parseOne fuel toks with
            | some (a, rest) => (parseArgs fuel rest).map (fun r => (a :: r.1, r.2))
            | none => none
end

/-- Parse a whole term from a string, requiring all tokens to be consumed. -/
def parse (s : String) : Option AST :=
  let toks := tokenize s
  match parseOne (toks.length + 1) toks with
  | some (a, []) => some a
  | _ => none

/-- Print a dotted path. -/
def prettyPath : DottedPath → String
  | .base s => s
  | .qualified s rest => s ++ "." ++ prettyPath rest

/-- Print a constructor label. -/
def prettyLabel : Label → String
  | .id n => n
  | .wild => "_"
  | .listE _ => "[]"
  | .listCons _ => "::"
  | .listOne _ => "[_]"

mutual
  /-- Print a term in the uniform S-expression syntax. -/
  def pretty : AST → String
    | .var p => "$" ++ prettyPath p
    | .sexp l [] => prettyLabel l
    | .sexp l args => "(" ++ prettyLabel l ++ " " ++ prettyArgs args ++ ")"
    | .subst b r v => "(Subst " ++ pretty b ++ " " ++ pretty r ++ " " ++ prettyPath v ++ ")"
  /-- Print a space-separated argument list. -/
  def prettyArgs : List AST → String
    | [] => ""
    | [a] => pretty a
    | a :: as => pretty a ++ " " ++ prettyArgs as
end

end MeTTaIL
