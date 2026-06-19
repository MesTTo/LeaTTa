/-
Colored, text-measured commutative diagrams for the LeaTTa book.

This is a small adaptation of Illuminate's `commDiag` DSL (Apache 2.0, Lean FRO). The stock DSL sizes
every grid cell to a fixed width and draws everything black, so long labels overlap and nothing has
colour. This version measures each label with `estimateTextWidth` so columns are wide enough, and lets
every node and arrow carry a colour.
-/
import Illuminate

namespace Docs
open Illuminate

/-- A node: a label and the colour to draw it in. -/
structure CDNode where
  name : Lean.Name
  label : String
  color : Color := Color.black

/-- An arrow between two nodes, with an optional coloured label. -/
structure CDArrow where
  src : Lean.Name
  tgt : Lean.Name
  label : Option String := none
  side : LabelSide := .above
  color : Color := Color.black

/-- Builder state. -/
structure CDState where
  nextId : Nat := 0
  nodes : Array CDNode := #[]
  arrows : Array CDArrow := #[]
  gridSpec : Option (Array (Array (Option Lean.Name))) := none

/-- The diagram builder monad. -/
abbrev CDM := StateM CDState

/-- Registers a node and returns its handle. -/
def CDM.node (label : String) (color : Color := Color.black) : CDM Lean.Name := do
  let st ← get
  let nm := Lean.Name.mkSimple s!"n{st.nextId}"
  let n : CDNode := { name := nm, label := label, color := color }
  set { st with nextId := st.nextId + 1, nodes := st.nodes.push n }
  return nm

/-- Lays the nodes out in a grid. -/
def CDM.grid (rows : Array (Array (Option Lean.Name))) : CDM Unit :=
  modify fun st => { st with gridSpec := some rows }

/-- Adds an arrow, optionally with a coloured label on a given side. -/
def CDM.arrow (src tgt : Lean.Name) (label : Option String := none)
    (color : Color := Color.black) (side : LabelSide := .above) : CDM Unit := do
  let a : CDArrow := { src := src, tgt := tgt, label := label, color := color, side := side }
  modify fun st => { st with arrows := st.arrows.push a }

namespace CD
variable {β : Type} [Backend β]

/-- Node label size. -/
def nodeFontSize : Float := 15
/-- Arrow label size. -/
def arrowFontSize : Float := 12
/-- Slack added around each grid cell. Generous, so adjacent arrow labels do not collide. -/
def cellGap : Float := 30
/-- Padding inside a node box. -/
def nodePad : Float := 6

/-- Half the drawn width of a node label. -/
def halfWidth (label : String) : Float := estimateTextWidth nodeFontSize label / 2 + nodePad
/-- Half the drawn height of a node label. -/
def halfHeight : Float := nodeFontSize / 2 + nodePad

/-- Lays out the node labels, each in a cell sized to its own width. -/
def buildNodeLayer (st : CDState) : Diagram β :=
  match st.gridSpec with
  | none =>
    Diagram.hcat (st.nodes.toList.map fun n =>
      Diagram.named n.name
        (Diagram.pad nodePad (Diagram.text n.label { fontSize := nodeFontSize, color := n.color })))
  | some rows =>
    let gridRows := rows.map fun row => row.map fun cell =>
      match cell with
      | none => none
      | some nm =>
        match st.nodes.find? (fun n => n.name == nm) with
        | none => none
        | some n =>
          let lbl := Diagram.text n.label { fontSize := nodeFontSize, color := n.color }
          let env := Envelope.ofRect (halfWidth n.label + cellGap) (halfHeight + cellGap)
          some (Diagram.named n.name (Diagram.withEnvelope env (Diagram.pad nodePad lbl)))
    Diagram.grid gridRows

/-- Draws one arrow, shortened so the shaft clears each node's label box. -/
def buildArrow (st : CDState) (base : Diagram β) (m : CDArrow) : Diagram β :=
  let srcPos := (base.find m.src).origin.toVec2
  let tgtPos := (base.find m.tgt).origin.toVec2
  let dir := Vec2.sub tgtPos srcPos
  let dirNorm := dir.normalize
  let stroke : Stroke := { color := m.color, width := 1.6 }
  let widthOf := fun nm => (st.nodes.find? (fun n => n.name == nm)).elim (12.0 : Float)
    (fun n => halfWidth n.label)
  let horiz := dir.x.abs ≥ dir.y.abs
  let srcShrink := if horiz then widthOf m.src + 4 else halfHeight + 6
  let tgtShrink := if horiz then widthOf m.tgt + 4 else halfHeight + 6
  let a := Vec2.add srcPos (srcShrink • dirNorm)
  let b := Vec2.sub tgtPos (tgtShrink • dirNorm)
  let shaft := Diagram.fromStroke (PathData.line a b) stroke
  let (head, _) := ArrowDraw.drawArrowhead {} b (Vec2.sub b a) stroke
  let arrow := Diagram.atop head shaft
  match m.label with
  | none => arrow
  | some lbl =>
    let mid : Vec2 := ⟨(a.x + b.x) / 2, (a.y + b.y) / 2⟩
    let perp : Vec2 := ⟨-dirNorm.y, dirNorm.x⟩
    let off : Vec2 := match m.side with
      | .above => (13.0 : Float) • perp
      | .below => (-13.0 : Float) • perp
      | .left  => ⟨-(estimateTextWidth arrowFontSize lbl / 2 + 6), 0⟩
      | .right => ⟨estimateTextWidth arrowFontSize lbl / 2 + 6, 0⟩
    let lp := Vec2.add mid off
    let lblDiag := Diagram.transform (Matrix.translate lp.x lp.y)
      (Diagram.text lbl { fontSize := arrowFontSize, color := m.color })
    Diagram.atop lblDiag arrow

/-- Compiles the builder to a diagram. -/
def compile (m : CDM Unit) : Diagram β :=
  let (_, st) := StateT.run m ({} : CDState)
  let nodeLayer := buildNodeLayer st
  let arrowLayer := st.arrows.foldl (init := Diagram.empty) fun acc ar =>
    Diagram.atop (buildArrow st nodeLayer ar) acc
  Diagram.atop arrowLayer nodeLayer

end CD

/-- Builds a coloured, text-measured commutative diagram. -/
def cd {β : Type} [Backend β] (m : CDM Unit) : Diagram β := CD.compile m

/-- Common palette for the book's diagrams, tuned to be legible on the dark background. -/
def cdInk    : Color := Color.rgb 201 209 217  -- #c9d1d9 light grey
def cdBlue   : Color := Color.rgb 121 192 255  -- #79c0ff
def cdGreen  : Color := Color.rgb 63 185 80    -- #3fb950
def cdRed    : Color := Color.rgb 255 123 114  -- #ff7b72
def cdPurple : Color := Color.rgb 210 168 255  -- #d2a8ff
