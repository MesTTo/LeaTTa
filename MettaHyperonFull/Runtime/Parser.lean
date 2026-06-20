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
  | str (acc : List Char)
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
      | TokState.str acc => (("\"" ++ String.ofList acc.reverse ++ "\"") :: toks).reverse
      | TokState.comment => toks.reverse
  | c :: cs =>
      match state with
      | TokState.comment =>
          tokenizeAux (if c == '\n' then TokState.sym [] else TokState.comment) toks cs
      | TokState.str acc =>
          if c == '"' then
            tokenizeAux (TokState.sym []) (("\"" ++ String.ofList acc.reverse ++ "\"") :: toks) cs
          else
            tokenizeAux (TokState.str (c :: acc)) toks cs
      | TokState.sym acc =>
          if isSpace c then tokenizeAux (TokState.sym []) (flushSym acc toks) cs
          else if c == ';' then tokenizeAux TokState.comment (flushSym acc toks) cs
          else if c == '"' then tokenizeAux (TokState.str []) (flushSym acc toks) cs
          else if c == '(' || c == ')' then
            tokenizeAux (TokState.sym []) (String.singleton c :: flushSym acc toks) cs
          else if c == '!' && acc.isEmpty && (cs.head?).elim true (fun d => d == '(' || isSpace d) then
            -- a leading `!` before `(`, whitespace, or end-of-input is the query/exec marker; a `!`
            -- inside a symbol (`bind!`, `change-state!`, `!=`, `println!`) is an ordinary symbol char
            tokenizeAux (TokState.sym []) ("!" :: toks) cs
          else tokenizeAux (TokState.sym (c :: acc)) toks cs

/-- Tokenizer for a practical subset of MeTTa s-expressions. -/
def tokenize (s : String) : List String := tokenizeAux (TokState.sym []) [] s.toList

/-- Parse a decimal float literal `[-]digits.digits` (e.g. `1.5`, `-0.25`, `.5`) via
    `Float.ofScientific`, the same primitive `Lean.Json`'s number parser uses. Integer tokens are
    handled by `String.toInt?` in `parseAtomToken`, so this path runs only when a `.` is present.
    Known issue: result is IEEE 64-bit double, so values like `0.1` are subject to the usual
    binary float rounding. -/
def parseFloat? (s : String) : Option Float :=
  let neg := s.startsWith "-"
  let body := if neg then (s.drop 1).toString else s
  match body.splitOn "." with
  | [intPart, fracPart] =>
      if fracPart.isEmpty then none
      else match (intPart ++ fracPart).toNat? with
        | some m => some (let f := Float.ofScientific m true fracPart.length; if neg then -f else f)
        | none => none
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
  else match s.toInt? with
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
