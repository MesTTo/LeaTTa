-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Runtime.Parser
Layer: Runtime
Purpose: A parser for a practical subset of MeTTa s-expressions. The tokenizer is a structural state
  machine that recognises parentheses, the `!` query prefix, `;`-comments, `"`-strings, and
  whitespace-separated symbols. The parser then folds the token stream against a stack of in-progress
  expression frames into a list of top-level atoms. Single tokens parse to variables, booleans, the
  empty expression, strings, integer or float literals, or symbols.
Imports: MettaHyperonFull.Core.Atom
Trusted boundary: none
Main exports: tokenize, parseFloat?, parseAtomToken, parseTokens, parseProgram
Open obligations: float literals are IEEE 64-bit doubles, so values like `0.1` carry the usual binary
  rounding.
-/
import MettaHyperonFull.Core.Atom

namespace Metta.Runtime
open Metta

def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- Tokenizer state: accumulating a symbol (`sym`, chars reversed; `[]` means "between tokens"),
    inside a `"`-string literal (`str`, content chars reversed), or inside a `;`-comment. -/
inductive TokState where
  | sym (acc : List Char)
  | str (acc : List Char) (escaped : Bool)
  | comment

/-- Emit the pending symbol token (its chars are reversed in `acc`) onto `toks`, if non-empty. -/
def flushSym (acc : List Char) (toks : List String) : List String :=
  match acc with
  | [] => toks
  | _ => String.ofList acc.reverse :: toks

/-- Tokenize a character list as a state machine, recursing structurally on the input. It
    recognises parentheses, the `!` prefix, `;`-comments, `"`-strings, and whitespace-separated
    symbols. `toks` accumulates completed tokens in reverse. -/
def tokenizeAux (state : TokState) (toks : List String) : List Char → List String
  | [] =>
      match state with
      | TokState.sym acc => (flushSym acc toks).reverse
      | TokState.str acc _ => (("\"" ++ String.ofList acc.reverse ++ "\"") :: toks).reverse
      | TokState.comment => toks.reverse
  | c :: cs =>
      match state with
      | TokState.comment =>
          tokenizeAux (if c == '\n' then TokState.sym [] else TokState.comment) toks cs
      | TokState.str acc escaped =>
          if escaped then
            tokenizeAux (TokState.str (c :: acc) false) toks cs
          else if c == '\\' then
            tokenizeAux (TokState.str acc true) toks cs
          else if c == '"' then
            tokenizeAux (TokState.sym []) (("\"" ++ String.ofList acc.reverse ++ "\"") :: toks) cs
          else
            tokenizeAux (TokState.str (c :: acc) false) toks cs
      | TokState.sym acc =>
          if isSpace c then tokenizeAux (TokState.sym []) (flushSym acc toks) cs
          else if c == ';' && !(match acc.reverse.head? with | some h => h == '$' | none => false) then
            tokenizeAux TokState.comment (flushSym acc toks) cs
          else if c == '"' && acc.isEmpty then tokenizeAux (TokState.str [] false) (flushSym acc toks) cs
          else if c == '(' || c == ')' then
            tokenizeAux (TokState.sym []) (String.singleton c :: flushSym acc toks) cs
          else if c == '!' && acc.isEmpty && (cs.head?).elim true (fun d => d == '(' || isSpace d) then
            -- a leading `!` before `(`, whitespace, or end-of-input is the query/exec marker; a `!`
            -- inside a symbol (`bind!`, `change-state!`, `!=`, `println!`) is an ordinary symbol char
            tokenizeAux (TokState.sym []) ("!" :: toks) cs
          else tokenizeAux (TokState.sym (c :: acc)) toks cs

/-- Tokenizer for a practical subset of MeTTa s-expressions. -/
def tokenize (s : String) : List String := tokenizeAux (TokState.sym []) [] s.toList

/-- True when the string is non-empty and contains only decimal digits. Lean's own numeric parsers
    accept separators such as `_`, while MeTTa's lexer treats those tokens as symbols. -/
def allDigits (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit

/-- Parse a signed integer with only decimal digits after an optional sign. -/
def parseInt? (s : String) : Option Int :=
  let neg := s.startsWith "-"
  let pos := s.startsWith "+"
  let body := if neg || pos then (s.drop 1).toString else s
  if allDigits body then
    body.toNat?.map fun n => if neg then -Int.ofNat n else Int.ofNat n
  else none

/-- Split a mantissa into `(sign, digits, fractional_digits)`. A decimal mantissa must have at least
    one digit before and after `.`, so `.5` stays a symbol. -/
def parseMantissa? (s : String) : Option (Bool × Nat × Nat) :=
  let neg := s.startsWith "-"
  let pos := s.startsWith "+"
  let body := if neg || pos then (s.drop 1).toString else s
  match body.splitOn "." with
  | [digits] =>
      if allDigits digits then digits.toNat?.map fun n => (neg, n, 0) else none
  | [intPart, fracPart] =>
      if allDigits intPart && allDigits fracPart then
        (intPart ++ fracPart).toNat?.map fun n => (neg, n, fracPart.length)
      else none
  | _ => none

/-- Parse a decimal float literal with optional scientific notation. Accepted forms include
    `1.5`, `-0.25`, `1e2`, and `1.5e3`; leading-dot floats and digit separators remain symbols.
    Known issue: result is IEEE 64-bit double, so values like `0.1` carry binary float rounding. -/
def parseFloat? (s : String) : Option Float :=
  let parts := if s.contains "e" then s.splitOn "e" else s.splitOn "E"
  match parts with
  | [mantissa] =>
      if mantissa.contains "." then
        parseMantissa? mantissa |>.map fun p =>
          let f := Float.ofScientific p.2.1 true p.2.2
          if p.1 then -f else f
      else none
  | [mantissa, exponent] =>
      match parseMantissa? mantissa, parseInt? exponent with
      | some (neg, m, fracDigits), some e =>
          let scale := Int.ofNat fracDigits - e
          let f := if scale >= 0 then
            Float.ofScientific m true scale.toNat
          else
            Float.ofScientific m false (-scale).toNat
          some (if neg then -f else f)
      | _, _ => none
  | _ => none

/-- Parse a single token into an `Atom`: `$x` → variable, `True`/`False` → Bool, `()` → the empty
    expression, `"…"` → string, an integer/float literal → the grounded number, otherwise a symbol.
    The tokenizer splits `(` and `)` into separate tokens, so the `()` case here is only a guard. -/
def parseAtomToken (s : String) : Atom :=
  if s.startsWith "$" then Atom.var (s.drop 1).toString
  else if s == "True" then Atom.gnd (Ground.bool true)
  else if s == "False" then Atom.gnd (Ground.bool false)
  else if s == "()" then Atom.expr []
  else if s.startsWith "\"" then Atom.gnd (Ground.str ((s.drop 1).dropEnd 1).toString)
  else match parseInt? s with
    | some n => Atom.gnd (Ground.int n)
    | none => match parseFloat? s with
      | some f => Atom.gnd (Ground.float f)
      | none => Atom.sym s

/-- Parse a flat token stream against an explicit stack of in-progress expression accumulators
    (each holding its atoms reversed); the bottom frame collects the top-level atoms. `(` pushes a
    frame, `)` pops and wraps it as an `Atom.expr`, any other token is appended to the current
    frame. Structurally recursive on the token list, hence total. -/
def parseTokens : List (List Atom) → List String → Except String (List Atom)
  | [top], [] => Except.ok top.reverse
  | _, [] => Except.error "unterminated expression"
  | stack, "(" :: rest => parseTokens ([] :: stack) rest
  | inner :: outer :: more, ")" :: rest =>
      parseTokens ((Atom.expr inner.reverse :: outer) :: more) rest
  | _, ")" :: _ => Except.error "unexpected )"
  | top :: more, tok :: rest => parseTokens ((parseAtomToken tok :: top) :: more) rest
  | [], _ :: _ => Except.error "unexpected token at top level"

/-- Parse a whole program: a sequence of top-level atoms. -/
def parseProgram (s : String) : Except String (List Atom) := parseTokens [[]] (tokenize s)

end Metta.Runtime
