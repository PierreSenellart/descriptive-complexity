/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.Tiling
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.RegChannel
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.WellFormed
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMBlank WMDst WMInp WMRead WMRight WMSrc WMStart WMTr WMWrite)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The tiles a computation table is drawn with

The drawing behind `DescriptiveComplexity.WideTiling`'s hardness, written as
plain predicates before any formula: the tile system whose square is the
*computation table* of a clocked wide machine – a column is a tape address, a
row is a time step.

## What a tile carries

A tile is a tagged triple of elements of the machine's instance
(`DescriptiveComplexity.TileTag`):

* `dig` – not a tile at all, but a **digit**: the diagonal triples are the
  elements the grid's coordinates are subsets of, so the square is `2ⁿ × 2ⁿ`
  with `n` the size of the machine's instance;
* `sym a` – a cell holding the symbol `a`, with no head;
* `head a q τ` – the head is here, in the state `q`, reading `a` and firing the
  transition `τ`;
* `halt a q` – the head is here, in the state `q`, and fires nothing;
* `arrL a q` / `arrR a q` – no head yet, and one is about to arrive from the
  left (right) in the state `q`.

The head component carries the *transition*, not merely the state, because the
two local rules would otherwise each be free to choose their own: the vertical
one fixes the symbol written, the horizontal one the direction taken, and a tile
system whose two rules disagree describes no run at all.

## Why an arrival is a tile of its own

A vertical rule sees one column, so it cannot know that the neighboring head is
about to step into it; a horizontal rule sees one row, so it cannot know what the
next row holds. The arrival tile is the handshake between them: the horizontal
rule *justifies* it against the neighboring head, and the vertical rule *turns
it into* the head of the next row. That is what keeps a row to exactly one head
with rules that never see more than two cells.
-/

namespace Lax822549Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The tags -/

/-- The tags of the tiles a computation table is drawn with: the digits the
grid's coordinates are made of, and the five kinds of cell. -/
inductive TileTag where
  /-- A digit of a coordinate – not a tile. -/
  | dig
  /-- A cell with no head, holding a symbol. -/
  | sym
  /-- The head, firing a transition. -/
  | head
  /-- The head, firing nothing. -/
  | halt
  /-- A head arriving from the left. -/
  | arrL
  /-- A head arriving from the right. -/
  | arrR
  deriving DecidableEq

instance : Fintype TileTag :=
  ⟨{TileTag.dig, TileTag.sym, TileTag.head, TileTag.halt, TileTag.arrL, TileTag.arrR},
    by intro x; cases x <;> simp⟩

instance : Nonempty TileTag := ⟨TileTag.dig⟩

/-! ### The universe of the emitted instance -/

section Tiles

variable {A : Type} [Lax822549.WideMachines.wide.Structure A]

/-- **A point of the emitted instance**: a tag and three elements of the
machine's. -/
abbrev TilePt (A : Type) : Type := TileTag × (Fin 3 → A)

/-- The symbol a tile holds: its first coordinate. -/
def tpSym (p : TilePt A) : A := p.2 0

/-- The state a head or an arrival carries: its second coordinate. -/
def tpState (p : TilePt A) : A := p.2 1

/-- The transition a head fires: its third coordinate. -/
def tpTr (p : TilePt A) : A := p.2 2

/-- **Being a digit**: the tag says so and the triple is diagonal, so the digits
are one per element of the machine's instance. -/
def TPDig (p : TilePt A) : Prop :=
  p.1 = TileTag.dig ∧ p.2 0 = p.2 1 ∧ p.2 1 = p.2 2

/-- The digit of an element. -/
def tpDig (x : A) : TilePt A := (TileTag.dig, fun _ => x)

omit [Lax822549.WideMachines.wide.Structure A] in
@[simp]
theorem tpDig_isDig (x : A) : TPDig (tpDig (A := A) x) := ⟨rfl, rfl, rfl⟩

omit [Lax822549.WideMachines.wide.Structure A] in
theorem tpDig_injective : Function.Injective (tpDig (A := A)) := by
  intro x y h
  exact congrFun (congrArg Prod.snd h) 0

/-- **Being a tile**: one of the five kinds of cell, and – at a head – a
transition the machine may fire on the state and the symbol the tile carries. A
digit is not a tile. -/
def TPTile (p : TilePt A) : Prop :=
  match p.1 with
  | TileTag.dig => False
  | TileTag.sym => True
  | TileTag.head => Lax822549.WideMachines.WMTr (tpTr p) ∧ Lax822549.WideMachines.WMSrc (tpTr p) (tpState p) ∧ Lax822549.WideMachines.WMRead (tpTr p) (tpSym p)
  | TileTag.halt => True
  | TileTag.arrL => True
  | TileTag.arrR => True

/-- **Being an accepting tile**: the head is here, in an accepting state. -/
def TPAcc (p : TilePt A) : Prop :=
  (p.1 = TileTag.head ∨ p.1 = TileTag.halt) ∧ Lax822549.WideMachines.WMAcc (tpState p)

/-- **A cell with no head**: it holds a symbol, and it may be expecting one –
the bottom row's description allows an arrival, since the machine's first step
announces itself in a neighbor of the corner. -/
def TPNoHead (p : TilePt A) : Prop :=
  p.1 = TileTag.sym ∨ p.1 = TileTag.arrL ∨ p.1 = TileTag.arrR

/-- **A base tile**: what a column the description says nothing about carries in
the bottom row – a cell holding the blank. -/
def TPBase (p : TilePt A) : Prop := TPNoHead p ∧ Lax822549.WideMachines.WMBlank (tpSym p)

/-- **A start tile**: what the corner carries – the head, in a start state, on
the blank cell the machine begins on.

It is also where the machine's own well-formedness is folded in: a machine whose
order is not linear, whose input is not functional or which has no single blank
has no start tile at all, so its drawing has no tiling – which is what a no-instance
must give. The order's linearity is folded in twice over, since the emitted order
is linear only when the machine's is. -/
def TPStart (p : TilePt A) : Prop :=
  WideWF A ∧
    ((p.1 = TileTag.head ∧ Lax822549.WideMachines.WMTr (tpTr p) ∧ Lax822549.WideMachines.WMSrc (tpTr p) (tpState p) ∧
        Lax822549.WideMachines.WMRead (tpTr p) (tpSym p)) ∨ p.1 = TileTag.halt) ∧
      Lax822549.WideMachines.WMStart (tpState p) ∧ Lax822549.WideMachines.WMBlank (tpSym p)

/-- **A tile the leftmost column may carry**: anything but a head arriving from
the left, there being nothing to the left of that column to send one. This is
the border condition that keeps a head from appearing out of nowhere at the edge
of the square. -/
def TPEdgeL (p : TilePt A) : Prop := p.1 ≠ TileTag.arrL

/-- **A tile the rightmost column may carry**: anything but a head arriving from
the right. -/
def TPEdgeR (p : TilePt A) : Prop := p.1 ≠ TileTag.arrR

/-- **The bottom row's description**: at the cell of an element carrying input,
that input symbol, with no head. -/
def TPFirst (x p : TilePt A) : Prop :=
  ∃ a, TPDig x ∧ TPNoHead p ∧ Lax822549.WideMachines.WMInp (x.2 0) a ∧ tpSym p = a

/-- **The bottom row's description at the ruler**: the cell of an element holds
that element's input symbol, and the blank where the element carries none. This
is what a *space-bounded* wide machine's tape says, its cells being the initial
segments of the whole instance rather than of a file, which is why the drawing
carries the bottom row as a parameter. -/
def TPFirstR (x p : TilePt A) : Prop :=
  TPDig x ∧ TPNoHead p ∧
    (Lax822549.WideMachines.WMInp (x.2 0) (tpSym p) ∨ ((∀ a, ¬Lax822549.WideMachines.WMInp (x.2 0) a) ∧ Lax822549.WideMachines.WMBlank (tpSym p)))

/-! ### The two compatibilities -/

/-- **What a cell becomes in the next row**: the symbol is the written one under
a head and unchanged elsewhere, and the head of the next row is exactly what this
row's arrival announces. A halted head stays where it is, and a cell that neither
holds nor expects a head simply copies itself. -/
def TPVert (p q : TilePt A) : Prop :=
  match p.1 with
  | TileTag.dig => False
  | TileTag.sym => TPNoHead q ∧ tpSym q = tpSym p
  | TileTag.head => TPNoHead q ∧ Lax822549.WideMachines.WMWrite (tpTr p) (tpSym q)
  | TileTag.halt => q.1 = TileTag.halt ∧ tpSym q = tpSym p ∧ tpState q = tpState p
  | TileTag.arrL =>
    ((q.1 = TileTag.head ∨ q.1 = TileTag.halt) ∧ tpSym q = tpSym p ∧
      tpState q = tpState p)
  | TileTag.arrR =>
    ((q.1 = TileTag.head ∨ q.1 = TileTag.halt) ∧ tpSym q = tpSym p ∧
      tpState q = tpState p)

/-- **What may stand immediately to the right of a cell**: a head that moves
right announces itself in the right neighbor's arrival and nowhere else, and a
head that moves left in the left neighbor's – so an arrival is *justified* by a
neighboring head, which is what keeps a row to one head. -/
def TPHoriz (p q : TilePt A) : Prop :=
  -- neither is a digit
  TPTile p ∧ TPTile q ∧
    -- a head at the left that moves right hands the state to the right cell
    (p.1 = TileTag.head → Lax822549.WideMachines.WMRight (tpTr p) →
      q.1 = TileTag.arrL ∧ Lax822549.WideMachines.WMDst (tpTr p) (tpState q)) ∧
    -- a head at the right that moves left hands the state to the left cell
    (q.1 = TileTag.head → ¬Lax822549.WideMachines.WMRight (tpTr q) →
      p.1 = TileTag.arrR ∧ Lax822549.WideMachines.WMDst (tpTr q) (tpState p)) ∧
    -- an arrival from the left is the left neighbor's head, moving right
    (q.1 = TileTag.arrL →
      p.1 = TileTag.head ∧ Lax822549.WideMachines.WMRight (tpTr p) ∧ Lax822549.WideMachines.WMDst (tpTr p) (tpState q)) ∧
    -- an arrival from the right is the right neighbor's head, moving left
    (p.1 = TileTag.arrR →
      q.1 = TileTag.head ∧ ¬Lax822549.WideMachines.WMRight (tpTr q) ∧ Lax822549.WideMachines.WMDst (tpTr q) (tpState p)) ∧
    -- two heads never stand side by side
    ¬((p.1 = TileTag.head ∨ p.1 = TileTag.halt) ∧
      (q.1 = TileTag.head ∨ q.1 = TileTag.halt))

end Tiles

end Lax822549Proofs.DescriptiveComplexity


