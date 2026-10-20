/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Problems.Machine.DetRun
import DescriptiveComplexity.FixedPointOrderTransfer
import DescriptiveComplexity.Counting
import DescriptiveComplexity.Vocabulary
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The number written by a machine: definition

The function counterpart of deterministic machine acceptance
(`DescriptiveComplexity.DTMAccept`): the machine is data in the instance, and
the problem is to compute the number it leaves on its tape.

* The vocabulary is the one of machine instances
  (`FirstOrder.Language.turing`) with two more symbols
  (`FirstOrder.Language.tapeOut`): `out` marks the **output cells** and `one`
  marks the symbols read as the digit `1`.
* The machine **halts** (`DescriptiveComplexity.TMData.Halts`) in a
  configuration reached from the initial one within the clock – fewer steps
  than there are positions, as for acceptance – from which no step is
  possible. A deterministic machine halts in at most one configuration
  (`DescriptiveComplexity.TMData.halts_unique`).
* `DescriptiveComplexity.machineNumber`: an output cell holding, when the
  machine halts in an accepting state, a symbol marked `one` contributes
  `2 ^ r`, where `r` is the number of output cells strictly before it on the
  tape: the digits are read **in tape order**, the lowest cell holding the
  least significant one. A machine that does not halt within its clock, or
  halts without accepting, writes `0`, and so does an instance that is not a
  well-formed deterministic machine.
-/

namespace FirstOrder

namespace Language

/-- The symbols reading a number off the tape of a machine. -/
fo_language tapeOut with tp where
  /-- `out p`: the cell `p` is an output cell, holding one digit. -/
  out : 1
  /-- `one a`: the symbol `a` is read as the digit `1`. -/
  one : 1

/-- The relational language of machines writing a number. -/
abbrev turingOut : Language.{0, 0} := Language.turing.sum Language.tapeOut

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Halting -/

namespace TMData

variable {A : Type} (M : TMData A)

/-- **The machine halts in the configuration `c`**: `c` is reached from an
initial configuration within the clock, and no step is possible from it. -/
def Halts (c : Config A) : Prop :=
  ∃ (c₀ : Config A) (n : ℕ), M.IsInit c₀ ∧ n < Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ ∀ e, ¬M.Step c e

variable {M}

/-- **A deterministic machine halts in at most one configuration.** -/
theorem halts_unique [Finite A] (hwf : M.WellFormed) (hdet : M.Deterministic) {c d : Config A}
    (hc : M.Halts c) (hd : M.Halts d) : c = d := by
  obtain ⟨c₀, n, hi, -, hrun, hstuck⟩ := hc
  obtain ⟨d₀, m, hi', -, hrun', hstuck'⟩ := hd
  obtain rfl := isInit_unique hwf hdet.1 hi hi'
  rcases reach_total hwf.1 hdet (reflTransGen_of_stepsIn hrun) (reflTransGen_of_stepsIn hrun')
    with h | h
  · exact eq_of_reach_stuck hstuck h
  · exact (eq_of_reach_stuck hstuck' h).symm

open Classical in
/-- **A step is possible** exactly when some transition applies in the
current state to the symbol under the head, and can fire: it has a
destination, a written symbol, and a neighbor in its direction. -/
theorem exists_step_iff (c : Config A) :
    (∃ e, M.Step c e) ↔ ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
      (∃ q, M.Dst τ q) ∧ (∃ a, M.Write τ a) ∧
        ((M.Right τ ∧ ∃ p, SuccPos M.Le M.Posn c.head p) ∨
          (¬M.Right τ ∧ ∃ p, SuccPos M.Le M.Posn p c.head)) := by
  constructor
  · rintro ⟨e, τ, hτ, hsrc, hread, hdst, hwrite, -, hmove⟩
    exact ⟨τ, hτ, hsrc, hread, ⟨_, hdst⟩, ⟨_, hwrite⟩,
      hmove.imp (fun h => ⟨h.1, _, h.2⟩) fun h => ⟨h.1, _, h.2⟩⟩
  · rintro ⟨τ, hτ, hsrc, hread, ⟨q, hq⟩, ⟨a, ha⟩, hmove⟩
    have key : ∀ p : A, ((M.Right τ ∧ SuccPos M.Le M.Posn c.head p) ∨
        (¬M.Right τ ∧ SuccPos M.Le M.Posn p c.head)) →
        M.Step c ⟨q, p, Function.update c.tape c.head a⟩ := fun p hp =>
      ⟨τ, hτ, hsrc, hread, hq,
        (show M.Write τ (Function.update c.tape c.head a c.head) by
          rw [Function.update_self]; exact ha),
        fun p' hp' => Function.update_of_ne hp' _ _, hp⟩
    rcases hmove with ⟨hr, p, hp⟩ | ⟨hr, p, hp⟩
    · exact ⟨_, key p (Or.inl ⟨hr, hp⟩)⟩
    · exact ⟨_, key p (Or.inr ⟨hr, hp⟩)⟩

/-- Halting transports along an equivalence. -/
theorem Agree.halts {B : Type} {u : B ≃ A} {N : TMData B} (h : Agree u N M) (c : Config B) :
    N.Halts c ↔ M.Halts (c.map u) := by
  have hcard : Nat.card {b : B // N.Posn b} = Nat.card {a : A // M.Posn a} :=
    Nat.card_congr (u.subtypeEquiv fun b => h.posn b)
  constructor
  · rintro ⟨c₀, n, hi, hn, hrun, hstuck⟩
    refine ⟨c₀.map u, n, h.isInit.mp hi, hcard ▸ hn, (h.stepsIn n c₀ c).mp hrun, fun e he => ?_⟩
    obtain ⟨e₀, rfl⟩ := Config.map_surjective u e
    exact hstuck e₀ (h.step.mpr he)
  · rintro ⟨c₀, n, hi, hn, hrun, hstuck⟩
    obtain ⟨d₀, rfl⟩ := Config.map_surjective u c₀
    exact ⟨d₀, n, h.isInit.mpr hi, hcard ▸ hn, (h.stepsIn n d₀ c).mpr hrun,
      fun e he => hstuck (e.map u) (h.step.mp he)⟩

/-- Agreements compose. -/
theorem Agree.trans {B C : Type} {u : B ≃ A} {v : C ≃ B} {N : TMData B} {K : TMData C}
    (h₁ : Agree v K N) (h₂ : Agree u N M) : Agree (v.trans u) K M where
  posn b := (h₁.posn b).trans (h₂.posn _)
  le b b' := (h₁.le b b').trans (h₂.le _ _)
  tr b := (h₁.tr b).trans (h₂.tr _)
  start b := (h₁.start b).trans (h₂.start _)
  acc b := (h₁.acc b).trans (h₂.acc _)
  blank b := (h₁.blank b).trans (h₂.blank _)
  right b := (h₁.right b).trans (h₂.right _)
  src b b' := (h₁.src b b').trans (h₂.src _ _)
  read b b' := (h₁.read b b').trans (h₂.read _ _)
  dst b b' := (h₁.dst b b').trans (h₂.dst _ _)
  write b b' := (h₁.write b b').trans (h₂.write _ _)
  inp b b' := (h₁.inp b b').trans (h₂.inp _ _)

end TMData

/-! ### The number -/

/-- “Is an output cell”, in the vocabulary of machines writing a number. -/
abbrev mnOut : Language.turingOut.Relations 1 := Sum.inr tpOut

/-- “Is read as the digit `1`”, in the vocabulary of machines writing a
number. -/
abbrev mnOne : Language.turingOut.Relations 1 := Sum.inr tpOne

/-- The order of the tape, in the vocabulary of machines writing a number. -/
abbrev mnLe : Language.turingOut.Relations 2 := Sum.inl tmLe

/-- A machine writing a number is a machine. -/
instance turingOutStructure (A : Type) [Language.turingOut.Structure A] :
    Language.turing.Structure A :=
  (LHom.sumInl : Language.turing →ᴸ Language.turingOut).reduct A

section Semantics

variable {A : Type} [Language.turingOut.Structure A]

/-- The output cell `p` holds the digit `1` when the machine halts, in an
accepting state. -/
def OutDigit (p : A) : Prop :=
  RelMap mnOut ![p] ∧ ∃ c : Config A, (tmData A).Halts c ∧ (tmData A).Acc c.state ∧
    RelMap mnOne ![c.tape p]

/-- `q` is an output cell strictly before `p` on the tape. -/
def LowerCell (p q : A) : Prop :=
  RelMap mnOut ![q] ∧ q ≠ p ∧ RelMap mnLe ![q, p]

/-- The rank of a cell among the output cells: the number of output cells
strictly before it on the tape. -/
noncomputable def cellRank (p : A) : ℕ :=
  Nat.card {q : A // LowerCell p q}

variable (A) in
open Classical in
/-- **The number written by a machine**: each output cell holding the digit
`1` when the machine halts and accepts contributes two to the power of its
rank among the output cells. Instances that are not well-formed deterministic
machines write `0`. -/
noncomputable def machineNumber : ℕ :=
  if (tmData A).WellFormed ∧ (tmData A).Deterministic then
    ∑ᶠ p : A, if OutDigit p then 2 ^ cellRank p else 0
  else 0

end Semantics

/-! ### Isomorphism-invariance and the bundled problem -/

section Iso

variable {A B : Type} [Language.turingOut.Structure A] [Language.turingOut.Structure B]

theorem outDigit_equiv (e : A ≃[Language.turingOut] B) (p : A) : OutDigit (e p) ↔ OutDigit p := by
  have hag := agree_of_equiv (reductSumInlEquiv e)
  have hone : ∀ (c : Config B), (RelMap mnOne ![c.tape (e p)] : Prop) ↔
      RelMap mnOne ![(c.map (reductSumInlEquiv e).symm.toEquiv).tape p] := by
    intro c
    have h := relMap_equiv₁ e mnOne (e.symm (c.tape (e p)))
    rw [show (e (e.symm (c.tape (e p))) : B) = c.tape (e p) from
      e.toEquiv.apply_symm_apply _] at h
    exact h.symm
  refine and_congr (relMap_equiv₁ e mnOut p).symm ⟨?_, ?_⟩
  · rintro ⟨c, hc, ha, h1⟩
    exact ⟨_, (hag.halts c).mp hc, (hag.acc _).mp ha, (hone c).mp h1⟩
  · rintro ⟨c, hc, ha, h1⟩
    obtain ⟨d, rfl⟩ := Config.map_surjective (reductSumInlEquiv e).symm.toEquiv c
    exact ⟨d, (hag.halts d).mpr hc, (hag.acc _).mpr ha, (hone d).mpr h1⟩

theorem lowerCell_equiv (e : A ≃[Language.turingOut] B) (p q : A) :
    LowerCell (e p) (e q) ↔ LowerCell p q :=
  and_congr (relMap_equiv₁ e mnOut q).symm
    (and_congr e.toEquiv.injective.ne_iff (relMap_equiv₂ e mnLe q p).symm)

theorem cellRank_equiv (e : A ≃[Language.turingOut] B) (p : A) :
    cellRank (e p) = cellRank p :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv fun q => (lowerCell_equiv e p q).symm)).symm

/-- The number written is isomorphism-invariant. -/
theorem machineNumber_iso (e : A ≃[Language.turingOut] B) :
    machineNumber A = machineNumber B := by
  classical
  have hag := agree_of_equiv (reductSumInlEquiv e)
  have hsum : (∑ᶠ p : A, if OutDigit p then 2 ^ cellRank p else 0) =
      ∑ᶠ p : B, if OutDigit p then 2 ^ cellRank p else 0 := by
    rw [← finsum_comp_equiv e.toEquiv]
    refine finsum_congr fun p => ?_
    change _ = if OutDigit (e p) then 2 ^ cellRank (e p) else 0
    rw [cellRank_equiv e p, if_congr (outDigit_equiv e p) rfl rfl]
  rw [machineNumber, machineNumber, hsum]
  exact if_congr (and_congr hag.wellFormed hag.deterministic).symm rfl rfl

end Iso

/-- **The number written by a deterministic machine**, as a counting problem
on `Language.turingOut`-structures: the function counterpart of
`DescriptiveComplexity.DTMAccept`. -/
noncomputable def DTMNumber : CountingProblem Language.turingOut where
  Count := fun A inst => @machineNumber A inst
  iso_invariant := fun e => machineNumber_iso e

end DescriptiveComplexity
