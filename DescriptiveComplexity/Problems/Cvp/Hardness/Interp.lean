/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Defs
import DescriptiveComplexity.Problems.HornSat
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OrderWalk

/-!
# HORN-SAT to CVP: the circuit that runs unit propagation

The interpretation built here draws, inside a `Language.sat`-instance, the
monotone circuit that evaluates unit propagation and reports **failure** of
Horn satisfiability. Reducing from the *complement* is what keeps the circuit
monotone – a circuit that reports satisfiability would have to negate the
propagation – and costs nothing, since polynomial time is closed under
complement (`DescriptiveComplexity.piP_zero_eq`), so hardness for `HORNSAT`ᶜ is
hardness for `HORNSAT`; that step is taken in
`DescriptiveComplexity.Problems.Cvp.Hardness`.

## The layout

Unit propagation is a fixed point, and a circuit is acyclic, so the stages are
*unrolled*: the third coordinate of a gate is an element of the universe read
as a stage number through its rank in the order
(`DescriptiveComplexity.orank`), and `Nat.card A` stages suffice
(`DescriptiveComplexity.forced_forcedIn_card`). Two more chains turn the two
unbounded quantifiers of one propagation round into fan-in two, each walking
the order one cover at a time:

* `bd c y s` – a conjunction chain: *every* negative literal `y' ≤ y` of the
  clause `c` is forced within `orank s` rounds. Its right input is the gate
  `hd y' ⊤ (pred s)` when `y` is a negative literal of `c`, and the constant
  `1` when it is not: the *wiring* tests `negIn`, which is what an
  interpretation may do and a fixed circuit may not;
* `hd x c s` – a disjunction chain: *some* clause `c' ≤ c` has `x` as its
  positive literal and all its negative literals forced within `orank s`
  rounds. At `c = ⊤` this is one propagation round, so `hd x ⊤ s` is
  “`x` is forced within `orank s + 1` rounds”;
* `bdTop c y` – the same conjunction chain read at the *last* stage, needed
  because `bd c y s` reads the forced set one stage below `s` and the goal
  clause has to be tested against the fixed point itself;
* `gl c` – a disjunction chain over the goal clauses: some clause `c' ≤ c` has
  no positive literal and all its negative literals forced. Its base carries
  the Horn condition: at `c = ⊥` the chain starts from the constant `1` when
  the instance is *not* Horn, so a non-Horn instance is a yes-instance
  outright, and from the constant `0` when it is. The output gate is `gl ⊤`.

Junk is disposed of in the usual way: the coordinates a tag does not use are
pinned to the minimum, and the copies with other coordinates carry no mark and
no wire, so they derive nothing and are wired to nothing.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The tags -/

/-- The tags of the interpretation: the two constants, the two conjunction
chains, the propagation chain and the goal chain. -/
inductive CvpTag
  /-- The constant `1` gate. -/
  | tt
  /-- The constant `0` gate. -/
  | ff
  /-- `bd c y s`: all negative literals of `c` up to `y` are forced within
  `orank s` rounds. -/
  | bd
  /-- `bdTop c y`: the same, read at the last stage. -/
  | bdTop
  /-- `hd x c s`: some clause up to `c` forces `x` within `orank s + 1`
  rounds. -/
  | hd
  /-- `gl c`: some clause up to `c` is a falsified goal clause. -/
  | gl
  deriving DecidableEq

instance : Fintype CvpTag :=
  ⟨{.tt, .ff, .bd, .bdTop, .hd, .gl}, fun t => by cases t <;> simp⟩

instance : Nonempty CvpTag := ⟨.tt⟩

namespace CvpInterp

open SatOcc

/-! ### The formula builders

The occurrence builders of `DescriptiveComplexity.SatOcc` supply `clF`, `posF`,
`negF` and `eqF` over the ordered expansion; only three builders are new. All
are parameterized by the variables they speak about, so that the same builder
serves the unary marks (variables `(0, j)`) and the binary wires (variables
`(0, j)` for the gate and `(1, j)` for its input). -/

variable {α : Type}

/-- “`c` is a clause with no positive literal”, i.e., a goal clause: the shape
that makes an instance unsatisfiable once its negative literals are forced. -/
noncomputable def noPosClF (c : α) : satOrd.Formula α :=
  clF c ⊓ ∼((posF (Sum.inl c) (Sum.inr ()) : satOrd.Formula (α ⊕ Unit)).iExs Unit)

/-- The Horn condition, as a formula in any variable context: no clause has two
distinct positive literals. -/
noncomputable def hornCondF : satOrd.Formula α :=
  ((clF (Sum.inr 0) ⊓ posF (Sum.inr 0) (Sum.inr 1) ⊓
      posF (Sum.inr 0) (Sum.inr 2) : satOrd.Formula (α ⊕ Fin 3)).imp
    (eqF (Sum.inr 1) (Sum.inr 2))).iAlls (Fin 3)

/-- All three coordinates of the `i`-th argument are the minimum: the canonical
padding of a tag that does not use them. -/
noncomputable def allMinF {n : ℕ} (i : Fin n) : satOrd.Formula (Fin n × Fin 3) :=
  minF (L := Language.sat) (i, 0) ⊓ minF (L := Language.sat) (i, 1) ⊓
    minF (L := Language.sat) (i, 2)

end CvpInterp

/-! ### The interpretation -/

open CvpInterp SatOcc in
/-- **The unit-propagation circuit**, drawn inside a `Language.sat`-instance
over the ordered expansion. -/
noncomputable def cvpInterp : FOInterpretation satOrd Language.circuit CvpTag 3 where
  relFormula {n} R :=
    match n, R with
    | _, .isTrue => fun t =>
        match t 0 with
        | .tt => allMinF 0
        | _ => ⊥
    | _, .isFalse => fun t =>
        match t 0 with
        | .ff => allMinF 0
        | _ => ⊥
    | _, .isAnd => fun t =>
        match t 0 with
        | .bd => ⊤
        | .bdTop => minF (L := Language.sat) (0, 2)
        | _ => ⊥
    | _, .isOr => fun t =>
        match t 0 with
        | .hd => ⊤
        | .gl => minF (L := Language.sat) (0, 1) ⊓ minF (L := Language.sat) (0, 2)
        | _ => ⊥
    | _, .isNot => fun _ => ⊥
    | _, .out => fun t =>
        match t 0 with
        | .gl => maxF (L := Language.sat) (0, 0) ⊓ minF (L := Language.sat) (0, 1) ⊓
            minF (L := Language.sat) (0, 2)
        | _ => ⊥
    | _, .left => fun t =>
        match t 0, t 1 with
        | .bd, .tt => minF (L := Language.sat) (0, 1) ⊓ allMinF 1
        | .bd, .bd =>
            succF (L := Language.sat) (1, 1) (0, 1) ⊓ eqF (1, 0) (0, 0) ⊓ eqF (1, 2) (0, 2)
        | .bdTop, .tt =>
            minF (L := Language.sat) (0, 1) ⊓ minF (L := Language.sat) (0, 2) ⊓ allMinF 1
        | .bdTop, .bdTop =>
            succF (L := Language.sat) (1, 1) (0, 1) ⊓ eqF (1, 0) (0, 0) ⊓
              minF (L := Language.sat) (0, 2) ⊓ minF (L := Language.sat) (1, 2)
        | .hd, .ff => minF (L := Language.sat) (0, 1) ⊓ allMinF 1
        | .hd, .hd =>
            succF (L := Language.sat) (1, 1) (0, 1) ⊓ eqF (1, 0) (0, 0) ⊓ eqF (1, 2) (0, 2)
        | .gl, .ff =>
            minF (L := Language.sat) (0, 0) ⊓ minF (L := Language.sat) (0, 1) ⊓
              minF (L := Language.sat) (0, 2) ⊓ hornCondF ⊓ allMinF 1
        | .gl, .tt =>
            minF (L := Language.sat) (0, 0) ⊓ minF (L := Language.sat) (0, 1) ⊓
              minF (L := Language.sat) (0, 2) ⊓ ∼hornCondF ⊓ allMinF 1
        | .gl, .gl =>
            succF (L := Language.sat) (1, 0) (0, 0) ⊓ minF (L := Language.sat) (0, 1) ⊓
              minF (L := Language.sat) (0, 2) ⊓ minF (L := Language.sat) (1, 1) ⊓
              minF (L := Language.sat) (1, 2)
        | _, _ => ⊥
    | _, .right => fun t =>
        match t 0, t 1 with
        | .bd, .tt => ∼(negF (0, 0) (0, 1)) ⊓ allMinF 1
        | .bd, .ff => negF (0, 0) (0, 1) ⊓ minF (L := Language.sat) (0, 2) ⊓ allMinF 1
        | .bd, .hd =>
            negF (0, 0) (0, 1) ⊓ eqF (1, 0) (0, 1) ⊓ maxF (L := Language.sat) (1, 1) ⊓
              succF (L := Language.sat) (1, 2) (0, 2)
        | .bdTop, .tt =>
            ∼(negF (0, 0) (0, 1)) ⊓ minF (L := Language.sat) (0, 2) ⊓ allMinF 1
        | .bdTop, .hd =>
            negF (0, 0) (0, 1) ⊓ minF (L := Language.sat) (0, 2) ⊓ eqF (1, 0) (0, 1) ⊓
              maxF (L := Language.sat) (1, 1) ⊓ maxF (L := Language.sat) (1, 2)
        | .hd, .bd =>
            clF (0, 1) ⊓ posF (0, 1) (0, 0) ⊓ eqF (1, 0) (0, 1) ⊓
              maxF (L := Language.sat) (1, 1) ⊓ eqF (1, 2) (0, 2)
        | .hd, .ff => ∼(clF (0, 1) ⊓ posF (0, 1) (0, 0)) ⊓ allMinF 1
        | .gl, .bdTop =>
            noPosClF (0, 0) ⊓ minF (L := Language.sat) (0, 1) ⊓ minF (L := Language.sat) (0, 2) ⊓
              eqF (1, 0) (0, 0) ⊓ maxF (L := Language.sat) (1, 1) ⊓
              minF (L := Language.sat) (1, 2)
        | .gl, .ff =>
            ∼(noPosClF (0, 0)) ⊓ minF (L := Language.sat) (0, 1) ⊓ minF (L := Language.sat) (0, 2) ⊓
              allMinF 1
        | _, _ => ⊥

namespace CvpInterp

/-! ### Realization of the two new builders -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

open SatOcc

/-- A goal clause is a clause with no positive literal. -/
theorem realize_noPosClF (c : α) :
    (noPosClF c).Realize v ↔ IsCl (v c) ∧ ∀ x : A, ¬PosIn (v c) x := by
  simp only [noPosClF, Formula.realize_inf, realize_clF, Formula.realize_not,
    Formula.realize_iExs, realize_posF, Sum.elim_inl, Sum.elim_inr, not_exists]
  exact and_congr Iff.rfl ⟨fun h x hx => h (fun _ => x) hx, fun h i => h (i ())⟩

/-- The Horn condition says what it should. -/
theorem realize_hornCondF : (hornCondF (α := α)).Realize v ↔ AtMostOnePositive A := by
  simp only [hornCondF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    realize_clF, realize_posF, realize_eqF, Sum.elim_inr, AtMostOnePositive, IsCl, PosIn]
  exact ⟨fun h c x y hc hx hy => h ![c, x, y] ⟨⟨hc, hx⟩, hy⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1.1 hi.1.2 hi.2⟩

end Realize

end CvpInterp

end DescriptiveComplexity
