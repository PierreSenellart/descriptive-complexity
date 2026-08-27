/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointStratify
import DescriptiveComplexity.FixedPointPartial

/-!
# An induction, then a partial iteration: one partial iteration

`DescriptiveComplexity.StepDef.stratify` composes two *inflationary*
inductions. This file composes an inflationary induction with a **partial**
one (`DescriptiveComplexity.StepDef.stratifyPFP`): the value of the second
iteration, run over the structure expanded by the first one's limit, is the
value of a single partial iteration
(`DescriptiveComplexity.StepDef.pfpHolds_stratifyPFP`).

That is what closes `DescriptiveComplexity.PSPACE` under FO(LFP) reductions
(`DescriptiveComplexity.FixedPointReductionSpace`): a reduction's induction has
to be absorbed into the membership witness, and PSPACE's witness is a partial
iteration.

## Why a partial second stratum still works

The received reason to expect trouble is that a partial iteration is not
monotone, so “run the second stratum once the first has converged” cannot be
arranged by inflation, as `DescriptiveComplexity.StepDef.stratify` arranges it.
What makes it work anyway is that only the *gating* needs monotonicity, and the
gate is a bit of the state, not of the second stratum:

* the first stratum's variables accumulate – its step formula is written with
  the accumulation spelled out, since the composite iteration replaces rather
  than accumulates;
* the gate is an arity-`0` variable, set once the first stratum's step formulas
  add nothing (`DescriptiveComplexity.stratGateF`) and never unset;
* the second stratum's step is *conjoined* with the gate, so its variables stay
  empty until the gate fires and then iterate partially, from the empty
  assignment, over the frozen first stratum.

The stage count then shifts by the gate's index and nothing else: the composite
is at stage `G + 1 + m` exactly what the second stratum is at stage `m`
(`DescriptiveComplexity.StepDef.strat2Assign_partStage_add`). Fixed points can
only occur after the gate has fired – before it, either the first stratum still
moves or the gate itself does – so the composite converges exactly when the
second stratum does, and reads the same output there.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### The atom of a first-stratum variable -/

section Atoms

variable {B₁ B₂ : SOBlock} {A : Type} [L.Structure A]

/-- A first-stratum variable, as a formula over the combined block: the
composite iteration replaces rather than accumulates, so the accumulation has
to be written out. -/
noncomputable def strat1AtomF (L : Language.{0, 0}) (B₁ B₂ : SOBlock) (i : B₁.ι) :
    (L.sum (stratBlock B₁ B₂).lang).Formula (Fin (B₁.arity i)) :=
  Relations.formula (strat1Sym L B₁ B₂ i) fun j => Term.var j

theorem realize_strat1AtomF (σ : (stratBlock B₁ B₂).Assignment A) (i : B₁.ι)
    (x : Fin (B₁.arity i) → A) :
    (@Formula.Realize _ A ((stratBlock B₁ B₂).structure₁ (L := L) σ) _
      (strat1AtomF L B₁ B₂ i) x) ↔ strat1Assign σ i x := by
  let := (stratBlock B₁ B₂).structure₁ (L := L) σ
  rw [strat1AtomF, Formula.realize_rel]
  exact Iff.rfl

end Atoms

/-! ### The composite -/

namespace StepDef

variable (d₁ : StepDef L) (d₂ : StepDef (L.sum d₁.B.lang))

/-- **An inflationary stratum followed by a partial one**: the first stratum's
variables accumulate, the gate fires when they stop moving, and the second
stratum's variables iterate partially behind the gate, over the frozen first
stratum.

Reducible, so that the block of the composite *is* the combined block: the
stage lemmas below rewrite with assignment-level equalities, which instance
search must see through. -/
@[reducible]
noncomputable def stratifyPFP : StepDef L where
  B := stratBlock d₁.B d₂.B
  step := fun i =>
    match i with
    | .inl (.inl i) =>
        strat1AtomF L d₁.B d₂.B i ⊔ (strat1LHom L d₁.B d₂.B).onFormula (d₁.step i)
    | .inl (.inr _) =>
        Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊔ stratGateF d₁ d₂.B
    | .inr j =>
        Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊓
          (strat2LHom L d₁.B d₂.B).onFormula (d₂.step j)
  out := (strat2LHom L d₁.B d₂.B).onSentence d₂.out

variable {A : Type} [L.Structure A]

/-- One step of the first stratum: its own inflationary step, the
accumulation being written out. -/
theorem next_stratifyPFP_inl (σ : (stratBlock d₁.B d₂.B).Assignment A) (i : d₁.B.ι)
    (x : Fin (d₁.B.arity i) → A) :
    (d₁.stratifyPFP d₂).next σ (.inl (.inl i)) x ↔
      (strat1Assign σ i x ∨
        @StepDef.next L d₁ A _ (strat1Assign σ) i x) := by
  have h0 : (@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
      (strat1AtomF L d₁.B d₂.B i ⊔ (strat1LHom L d₁.B d₂.B).onFormula (d₁.step i)) x) ↔
      ((@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          (strat1AtomF L d₁.B d₂.B i) x) ∨
        @Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          ((strat1LHom L d₁.B d₂.B).onFormula (d₁.step i)) x) :=
    letI := (stratBlock d₁.B d₂.B).structure₁ (L := L) σ
    Formula.realize_sup
  exact h0.trans (or_congr (realize_strat1AtomF σ i x) (realize_strat1Formula σ (d₁.step i) x))

/-- One step of the gate: set once the first stratum's steps add nothing, and
never unset. -/
theorem next_stratifyPFP_gate (σ : (stratBlock d₁.B d₂.B).Assignment A) :
    (d₁.stratifyPFP d₂).next σ (.inl (.inr ())) Fin.elim0 ↔
      (StratGate σ ∨ ∀ (i : d₁.B.ι) (x : Fin (d₁.B.arity i) → A),
        @StepDef.next L d₁ A _ (strat1Assign σ) i x → strat1Assign σ i x) := by
  have h0 : (@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
      (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊔ stratGateF d₁ d₂.B)
      Fin.elim0) ↔
      ((@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0) Fin.elim0) ∨
        @Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          (stratGateF d₁ d₂.B) Fin.elim0) :=
    letI := (stratBlock d₁.B d₂.B).structure₁ (L := L) σ
    Formula.realize_sup
  exact h0.trans (or_congr (realize_gateAtom σ Fin.elim0)
    (realize_stratGateF d₁ σ Fin.elim0))

/-- One step of the second stratum: empty until the gate fires, one partial
step over the frozen first stratum afterwards. -/
theorem next_stratifyPFP_inr (σ : (stratBlock d₁.B d₂.B).Assignment A) (j : d₂.B.ι)
    (x : Fin (d₂.B.arity j) → A) :
    (d₁.stratifyPFP d₂).next σ (.inr j) x ↔
      (StratGate σ ∧
        @Formula.Realize _ A (@SOBlock.structure₁ (L.sum d₁.B.lang) d₂.B A
          (d₁.B.structure₁ (L := L) (strat1Assign σ)) (strat2Assign σ)) _
          (d₂.step j) x) := by
  have h0 : (@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
      (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊓
        (strat2LHom L d₁.B d₂.B).onFormula (d₂.step j)) x) ↔
      ((@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0) x) ∧
        @Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          ((strat2LHom L d₁.B d₂.B).onFormula (d₂.step j)) x) :=
    letI := (stratBlock d₁.B d₂.B).structure₁ (L := L) σ
    Formula.realize_inf
  exact h0.trans (and_congr (realize_gateAtom σ x) (realize_strat2Formula σ (d₂.step j) x))

/-! ### The three parts of one step -/

/-- The first stratum of one step is its own inflationary step. -/
theorem strat1Assign_next_stratifyPFP (σ : (stratBlock d₁.B d₂.B).Assignment A) :
    strat1Assign ((d₁.stratifyPFP d₂).next σ) = d₁.inflStep (strat1Assign σ) := by
  funext i x
  exact propext (d₁.next_stratifyPFP_inl d₂ σ i x)

/-- The gate of one step. -/
theorem stratGate_next_stratifyPFP (σ : (stratBlock d₁.B d₂.B).Assignment A) :
    StratGate ((d₁.stratifyPFP d₂).next σ) ↔
      (StratGate σ ∨ IsFixedPt d₁.inflStep (strat1Assign σ)) :=
  (d₁.next_stratifyPFP_gate d₂ σ).trans
    (or_congr Iff.rfl (d₁.isFixedPt_inflStep_iff (strat1Assign σ)).symm)

/-- The second stratum of one step. -/
theorem strat2Assign_next_stratifyPFP (σ : (stratBlock d₁.B d₂.B).Assignment A) :
    strat2Assign ((d₁.stratifyPFP d₂).next σ) =
      fun j x => StratGate σ ∧
        @StepDef.next (L.sum d₁.B.lang) d₂ A (d₁.B.structure₁ (L := L) (strat1Assign σ))
          (strat2Assign σ) j x := by
  funext j x
  exact propext (d₁.next_stratifyPFP_inr d₂ σ j x)

/-! ### The stages of the composite -/

/-- The first stratum of the composite stages is its own inflationary
stages. -/
theorem strat1Assign_partStage_stratifyPFP (n : ℕ) :
    strat1Assign ((d₁.stratifyPFP d₂).partStage A n) = d₁.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [StepDef.partStage_succ, strat1Assign_next_stratifyPFP, ih, ← d₁.inflStage_succ]

/-- The gate of the composite stages: it turns on when the first stratum stops
moving, and never off. -/
theorem stratGate_partStage_succ (n : ℕ) :
    StratGate ((d₁.stratifyPFP d₂).partStage A (n + 1)) ↔
      (StratGate ((d₁.stratifyPFP d₂).partStage A n) ∨
        IsFixedPt d₁.inflStep (d₁.inflStage A n)) := by
  rw [StepDef.partStage_succ]
  refine (d₁.stratGate_next_stratifyPFP d₂ _).trans (or_congr Iff.rfl ?_)
  rw [strat1Assign_partStage_stratifyPFP]

/-- The gate is off at the start. -/
theorem not_stratGate_partStage_zero :
    ¬StratGate ((d₁.stratifyPFP d₂).partStage A 0) :=
  fun h => h

/-- The gate stays on. -/
theorem stratGate_partStage_mono {m n : ℕ} (hmn : m ≤ n)
    (h : StratGate ((d₁.stratifyPFP d₂).partStage A m)) :
    StratGate ((d₁.stratifyPFP d₂).partStage A n) := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact (d₁.stratGate_partStage_succ d₂ n).mpr (Or.inl (ih (Nat.lt_succ_iff.mp hlt)))
    · rwa [heq] at h

/-- While the gate is off, the second stratum stays empty. -/
theorem strat2Assign_partStage_succ_of_not_gate {n : ℕ}
    (h : ¬StratGate ((d₁.stratifyPFP d₂).partStage A n)) :
    strat2Assign ((d₁.stratifyPFP d₂).partStage A (n + 1)) = d₂.B.botAssign A := by
  rw [StepDef.partStage_succ, strat2Assign_next_stratifyPFP]
  funext j x
  exact propext ⟨fun hh => absurd hh.1 h, False.elim⟩

/-- **Once the gate is on and the first stratum frozen, the second stratum
replays its own partial stages.** -/
theorem strat2Assign_partStage_add {G : ℕ} {ρ₁ : d₁.B.Assignment A}
    (hG : StratGate ((d₁.stratifyPFP d₂).partStage A G))
    (hbot : strat2Assign ((d₁.stratifyPFP d₂).partStage A G) = d₂.B.botAssign A)
    (hfr : ∀ n, G ≤ n → strat1Assign ((d₁.stratifyPFP d₂).partStage A n) = ρ₁) (m : ℕ) :
    strat2Assign ((d₁.stratifyPFP d₂).partStage A (G + m)) =
      @StepDef.partStage (L.sum d₁.B.lang) d₂ A (d₁.B.structure₁ (L := L) ρ₁) m := by
  induction m with
  | zero => exact hbot
  | succ m ih =>
    have hgate : StratGate ((d₁.stratifyPFP d₂).partStage A (G + m)) :=
      d₁.stratGate_partStage_mono d₂ (Nat.le_add_right G m) hG
    have hstrat1 := hfr (G + m) (Nat.le_add_right G m)
    rw [show G + (m + 1) = (G + m) + 1 from rfl, StepDef.partStage_succ,
      strat2Assign_next_stratifyPFP, ih, hstrat1,
      @StepDef.partStage_succ (L.sum d₁.B.lang) d₂ A (d₁.B.structure₁ (L := L) ρ₁) m]
    funext j x
    exact propext ⟨fun hh => hh.2, fun hh => ⟨hgate, hh⟩⟩

/-! ### The value of the composite -/

/-- An inflationary limit is reached at any stage that stops moving. -/
theorem inflLimit_eq_inflStage_of_isFixedPt {k : ℕ}
    (h : IsFixedPt d₁.inflStep (d₁.inflStage A k)) : d₁.inflLimit A = d₁.inflStage A k := by
  funext i x
  refine propext ⟨?_, fun hx => ⟨k, hx⟩⟩
  rintro ⟨n, hn⟩
  rcases le_total n k with hle | hle
  · exact d₁.inflStage_le_of_le hle i x hn
  · have hst : d₁.inflStage A n = d₁.inflStage A k := iterate_eq_of_isFixedPt h hle
    rwa [hst] at hn

/-- An assignment of the combined block is its three parts. -/
theorem stratBlock_ext {B₁ B₂ : SOBlock} {σ τ : (stratBlock B₁ B₂).Assignment A}
    (h1 : strat1Assign σ = strat1Assign τ) (hg : StratGate σ ↔ StratGate τ)
    (h2 : strat2Assign σ = strat2Assign τ) : σ = τ := by
  funext i x
  match i with
  | .inl (.inl i) => exact congrFun (congrFun h1 i) x
  | .inl (.inr u) =>
    have hx : x = Fin.elim0 := funext fun i => i.elim0
    rw [hx]
    exact propext hg
  | .inr j => exact congrFun (congrFun h2 j) x

/-- **The composite computes the second iteration over the first one's
limit.** An inflationary induction followed by a partial iteration is one
partial iteration: the composite converges exactly when the second stratum
does, over the structure expanded by the first stratum's limit, and reads the
same output there. -/
theorem pfpHolds_stratifyPFP [Finite A] :
    (d₁.stratifyPFP d₂).PFPHolds A ↔
      @StepDef.PFPHolds (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) := by
  classical
  -- the gate fires, and there is a first stage at which it has
  have hex : ∃ n, StratGate ((d₁.stratifyPFP d₂).partStage A n) :=
    ⟨Nat.card (BAtom d₁.B A) + 1,
      (d₁.stratGate_partStage_succ d₂ _).mpr (Or.inr (d₁.isFixedPt_inflStep_card A))⟩
  obtain ⟨G, hG, hGmin⟩ : ∃ G, StratGate ((d₁.stratifyPFP d₂).partStage A G) ∧
      ∀ m, m < G → ¬StratGate ((d₁.stratifyPFP d₂).partStage A m) :=
    ⟨sInf _, Nat.sInf_mem hex, fun m hm hmem => absurd (Nat.sInf_le hmem) (Nat.not_le_of_lt hm)⟩
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := by
    cases G with
    | zero => exact absurd hG (d₁.not_stratGate_partStage_zero d₂)
    | succ G' => exact ⟨G', rfl⟩
  -- the first stratum has converged when the gate fires, and stays there
  have hstable : IsFixedPt d₁.inflStep (d₁.inflStage A G') := by
    rcases (d₁.stratGate_partStage_succ d₂ G').mp hG with h | h
    · exact absurd h (hGmin G' (Nat.lt_succ_self G'))
    · exact h
  have hlimeq : d₁.inflLimit A = d₁.inflStage A G' :=
    d₁.inflLimit_eq_inflStage_of_isFixedPt hstable
  have hfr : ∀ n, G' + 1 ≤ n →
      strat1Assign ((d₁.stratifyPFP d₂).partStage A n) = d₁.inflLimit A := by
    intro n hn
    rw [strat1Assign_partStage_stratifyPFP, hlimeq]
    exact iterate_eq_of_isFixedPt hstable (by omega)
  -- and the second stratum then replays its own stages
  have hbot : strat2Assign ((d₁.stratifyPFP d₂).partStage A (G' + 1)) = d₂.B.botAssign A :=
    d₁.strat2Assign_partStage_succ_of_not_gate d₂ (hGmin G' (Nat.lt_succ_self G'))
  have hstage : ∀ m, strat2Assign ((d₁.stratifyPFP d₂).partStage A (G' + 1 + m)) =
      @StepDef.partStage (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m :=
    fun m => d₁.strat2Assign_partStage_add d₂ hG hbot hfr m
  have hout : ∀ σ : (stratBlock d₁.B d₂.B).Assignment A,
      (@Sentence.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ)
        ((strat2LHom L d₁.B d₂.B).onSentence d₂.out)) ↔
        @Sentence.Realize _ A (@SOBlock.structure₁ (L.sum d₁.B.lang) d₂.B A
          (d₁.B.structure₁ (L := L) (strat1Assign σ)) (strat2Assign σ)) d₂.out :=
    fun σ => realize_strat2Formula σ d₂.out default
  constructor
  · rintro ⟨n, hfix, houtn⟩
    have hsucc : (d₁.stratifyPFP d₂).partStage A (n + 1) =
        (d₁.stratifyPFP d₂).partStage A n := by
      rw [StepDef.partStage_succ]; exact hfix
    -- the first stratum has stopped, so the gate is on
    have hst : IsFixedPt d₁.inflStep (d₁.inflStage A n) := by
      have h1 := congrArg strat1Assign hsucc
      rw [strat1Assign_partStage_stratifyPFP, strat1Assign_partStage_stratifyPFP,
        d₁.inflStage_succ] at h1
      exact h1
    have hgaten : StratGate ((d₁.stratifyPFP d₂).partStage A n) := by
      have h2 : StratGate ((d₁.stratifyPFP d₂).partStage A (n + 1)) :=
        (d₁.stratGate_partStage_succ d₂ n).mpr (Or.inr hst)
      rwa [hsucc] at h2
    -- so the stage is past the gate
    have hle : G' + 1 ≤ n := by
      by_contra hlt
      exact hGmin n (by omega) hgaten
    obtain ⟨m, rfl⟩ : ∃ m, n = G' + 1 + m := ⟨n - (G' + 1), by omega⟩
    refine ⟨m, ?_, ?_⟩
    · have h3 := congrArg strat2Assign hsucc
      rw [StepDef.partStage_succ, strat2Assign_next_stratifyPFP, hstage m, hfr _ hle] at h3
      have h4 : ∀ (j : d₂.B.ι) (x : Fin (d₂.B.arity j) → A),
          (@StepDef.next (L.sum d₁.B.lang) d₂ A (d₁.B.structure₁ (L := L) (d₁.inflLimit A))
            (@StepDef.partStage (L.sum d₁.B.lang) d₂ A
              (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m) j x) ↔
            (@StepDef.partStage (L.sum d₁.B.lang) d₂ A
              (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m) j x := by
        intro j x
        have := congrFun (congrFun h3 j) x
        rw [← this]
        exact ⟨fun hh => ⟨hgaten, hh⟩, fun hh => hh.2⟩
      funext j x
      exact propext (h4 j x)
    · have h5 := (hout _).mp houtn
      rwa [hfr _ hle, hstage m] at h5
  · rintro ⟨m, hfix₂, hout₂⟩
    have hgate : StratGate ((d₁.stratifyPFP d₂).partStage A (G' + 1 + m)) :=
      d₁.stratGate_partStage_mono d₂ (Nat.le_add_right _ m) hG
    have hstrat1 : strat1Assign ((d₁.stratifyPFP d₂).partStage A (G' + 1 + m)) =
        d₁.inflLimit A := hfr _ (Nat.le_add_right _ m)
    refine ⟨G' + 1 + m, ?_, ?_⟩
    · refine stratBlock_ext ?_ ?_ ?_
      · rw [strat1Assign_next_stratifyPFP, hstrat1]
        exact d₁.isFixedPt_inflStep_inflLimit A
      · exact ⟨fun _ => hgate, fun _ => (d₁.stratGate_next_stratifyPFP d₂ _).mpr (Or.inl hgate)⟩
      · rw [strat2Assign_next_stratifyPFP, hstage m, hstrat1]
        funext j x
        refine propext ⟨fun hh => ?_, fun hh => ⟨hgate, ?_⟩⟩
        · exact congrFun (congrFun hfix₂ j) x ▸ hh.2
        · exact congrFun (congrFun hfix₂ j) x ▸ hh
    · refine (hout _).mpr ?_
      rw [hstrat1, hstage m]
      exact hout₂

end StepDef

end DescriptiveComplexity
