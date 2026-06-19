/-
The BNFCRenderer monomorphization pass: replace higher-order categories (arrows and products) by
named first-order sorts, and append the constructor rules that give those sorts their syntax.
Mirrors the Scala `BNFCRenderer.monomorphizeArrowsAndProducts`.

For an arrow `s -> t`, the sort is `ArrowCC<s>_<t>DD` with an application `α{ f (x) }`, a variable
`Ident`, and a lambda `λ{ (x) => body }`, plus a variable rule for the domain sort. For a product,
a `Make...` constructor. Lists are not yet handled (none occur in the modules tested).
-/
import MeTTaIL.Theory.Ops

namespace MeTTaIL

mutual
  /-- The first-order sort name a category mangles to. `CC`/`_`/`DD` encode the brackets and the
      separator, matching the Scala renderer (`ArrowCCName_ProcDD`, `ProdCCA_BDD`, ...). -/
  def Cat.mangleName : Cat → String
    | .idCat n   => n
    | .arrow s t => "ArrowCC" ++ Cat.mangleName s ++ "_" ++ Cat.mangleName t ++ "DD"
    | .prod cs   => "ProdCC" ++ Cat.mangleNameList cs ++ "DD"
    | .listOf a  => "ListCC" ++ Cat.mangleName a ++ "DD"
  /-- Mangle a list of categories, joined by `_`. -/
  def Cat.mangleNameList : List Cat → String
    | []      => ""
    | [c]     => Cat.mangleName c
    | c :: cs => Cat.mangleName c ++ "_" ++ Cat.mangleNameList cs
end

/-- Replace higher-order categories (arrow, product) by their mangled first-order sort. A top-level
    list stays a list with its element monomorphized. -/
def Cat.mono : Cat → Cat
  | .idCat n   => .idCat n
  | .arrow s t => .idCat (Cat.mangleName (.arrow s t))
  | .prod cs   => .idCat (Cat.mangleName (.prod cs))
  | .listOf a  => .listOf (Cat.mono a)

/-- Monomorphize the categories in an item. -/
def Item.mono : Item → Item
  | .terminal s        => .terminal s
  | .nterminal c       => .nterminal (Cat.mono c)
  | .absNTerminal x it => .absNTerminal x (Item.mono it)
  | .bindNTerminal x c => .bindNTerminal x (Cat.mono c)

/-- Monomorphize the categories in a rule. -/
def Rule.mono (r : Rule) : Rule := { r with cat := Cat.mono r.cat, items := r.items.map Item.mono }

mutual
  /-- The higher-order subcategories (arrows and products) occurring in a category, innermost first.
      -/
  def Cat.collectHO : Cat → List Cat
    | .idCat _   => []
    | .arrow s t => Cat.collectHO s ++ Cat.collectHO t ++ [.arrow s t]
    | .prod cs   => Cat.collectHOList cs ++ [.prod cs]
    | .listOf a  => Cat.collectHO a
  /-- The higher-order subcategories occurring in a list of categories. -/
  def Cat.collectHOList : List Cat → List Cat
    | []      => []
    | c :: cs => Cat.collectHO c ++ Cat.collectHOList cs
end

/-- The higher-order categories occurring in an item. -/
def Item.collectHO : Item → List Cat
  | .terminal _        => []
  | .nterminal c       => Cat.collectHO c
  | .absNTerminal _ it => Item.collectHO it
  | .bindNTerminal _ c => Cat.collectHO c

/-- The higher-order categories a rule mentions. -/
def Rule.collectHO (r : Rule) : List Cat :=
  Cat.collectHO r.cat ++ r.items.flatMap Item.collectHO

/-- The constructor rules generated for one higher-order category. For an arrow `s -> t`:
    application, a variable, a lambda, and a variable rule for the domain. For a product: a `Make`
    constructor. -/
def Cat.ctors : Cat → List Rule
  | .arrow s t =>
      let ms := Cat.mangleName s
      let mt := Cat.mangleName t
      let arr : Cat := .idCat ("ArrowCC" ++ ms ++ "_" ++ mt ++ "DD")
      [ { label := .id ("AppCC" ++ ms ++ "_" ++ mt ++ "DD"), cat := Cat.mono t
          items := [.terminal "α", .terminal "{", .nterminal arr, .terminal "(", .nterminal (Cat.mono s),
                    .terminal ")", .terminal "}"] },
        { label := .id ("IdentCC" ++ ms ++ "_" ++ mt ++ "DD"), cat := arr,
          items := [.nterminal (.idCat "Ident")] },
        { label := .id ("LamCC" ++ ms ++ "_" ++ mt ++ "DD"), cat := arr,
          items := [.terminal "λ", .terminal "{", .terminal "(", .nterminal (.idCat "Ident"), .terminal ")",
                    .terminal "=>", .nterminal (Cat.mono t), .terminal "}"] },
        { label := .id ("IdentCC" ++ ms ++ "DD"), cat := Cat.mono s,
          items := [.nterminal (.idCat "Ident")] } ]
  | .prod cs =>
      let pm := Cat.mangleName (.prod cs)
      [ { label := .id ("Make" ++ pm), cat := .idCat pm,
          items := .terminal "∏" :: .terminal "{" :: cs.map (fun c => .nterminal (Cat.mono c)) ++ [.terminal "}"] } ]
  | _ => []

/-- The monomorphization pass: replace higher-order categories by named sorts and append their
    constructor rules. Equations and rewrites are carried through unchanged. -/
def monomorphize (p : Presentation) : Presentation :=
  let hoCats := distinct (p.terms.flatMap Rule.collectHO)
  let ctors := distinct (hoCats.flatMap Cat.ctors)
  .mk p.exports (p.terms.map Rule.mono ++ ctors) p.equations p.rewrites p.references

end MeTTaIL
