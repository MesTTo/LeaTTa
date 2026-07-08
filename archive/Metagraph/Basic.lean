-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Core.Atom

namespace Metta

/-- Labels may include type labels and arbitrary enrichments such as vectors/tensors. -/
structure Label where
  symbol : String
  ty : Option Atom := none
  enrichment : Option Atom := none
  deriving Repr, BEq, Inhabited

/-- Directed labelled metagraph edge. `targets` is ordered; unordered hyperedges can be encoded
    by using canonical sorted order or a commutative label. -/
structure MGEdge where
  id : Nat
  label : Label
  targets : List Nat
  deriving Repr, BEq, Inhabited

structure Metagraph where
  edges : List MGEdge
  deriving Repr, BEq, Inhabited

namespace Metagraph

def empty : Metagraph := ⟨[]⟩
def addEdge (g : Metagraph) (e : MGEdge) : Metagraph := ⟨e :: g.edges⟩
def ids (g : Metagraph) : List Nat := g.edges.map (fun e => e.id)
def findEdge? (g : Metagraph) (i : Nat) : Option MGEdge := g.edges.find? (fun e => e.id == i)
def containsId (g : Metagraph) (i : Nat) : Bool := (findEdge? g i).isSome

def wellFormed (g : Metagraph) : Bool :=
  g.edges.all (fun e => e.targets.all (fun t => g.containsId t))

mutual

/-- Encode an atom as a DAG-like metagraph, allocating edge ids from `next` upward and returning
    the next free id together with the generated edges. -/
def encodeAtomFrom (next : Nat) : Atom → Nat × List MGEdge
  | Atom.sym s => (next+1, [⟨next, ⟨"Sym:" ++ s, none, none⟩, []⟩])
  | Atom.var v => (next+1, [⟨next, ⟨"Var:" ++ v, none, none⟩, []⟩])
  | Atom.gnd g => (next+1, [⟨next, ⟨"Ground", none, some (Atom.gnd g)⟩, []⟩])
  | Atom.expr xs =>
      let (n', es) := encodeAtomsFrom (next+1) xs
      let childIds := (List.range xs.length).map (fun i => next + 1 + i) -- approximation for docs/runtime
      (n', ⟨next, ⟨"Expr", none, none⟩, childIds⟩ :: es)

/-- Encode a list of atoms in sequence, threading the next free id through each. -/
def encodeAtomsFrom (next : Nat) : List Atom → Nat × List MGEdge
  | [] => (next, [])
  | a :: as =>
      let (n', es) := encodeAtomFrom next a
      let (n'', es') := encodeAtomsFrom n' as
      (n'', es ++ es')

end

end Metagraph

end Metta
