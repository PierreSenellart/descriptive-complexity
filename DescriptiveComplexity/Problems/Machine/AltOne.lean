/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Machine.AltDefs
import DescriptiveComplexity.Problems.Machine

/-!
# The alternating bridge at one block: `ATMAccept 1 true` is NP-complete

The base case of the machine bridge for the polynomial hierarchy, and the
sanity check on the alternating model: at `k = 1` the only block is `0`, its
polarity is the starting one, so for `start = true` no state is universal and
`DescriptiveComplexity.ATMData.AltAccepts` is
`DescriptiveComplexity.TMData.Accepts`
(`DescriptiveComplexity.ATMData.altAccepts_true_iff_accepts`). The alternating
problem is therefore the same problem as `DescriptiveComplexity.NTMAccept`, up
to the mark – and *up to the mark* is exactly what a reduction is for.

Both directions are identity interpretations – one dimension, one tag – in the
style of `DescriptiveComplexity.DetToNondet.detInterp`:

* `DescriptiveComplexity.MarkOne.markInterp` copies a machine and marks *every*
  element as a state of block `0`, so the promise
  `DescriptiveComplexity.ATMData.BlocksWellFormed` holds in the image by
  construction;
* `DescriptiveComplexity.ForgetOne.forgetInterp` copies an alternating machine
  and forgets the mark, keeping the accepting states only when the promise
  holds in the source – the guard trick again, so that an instance failing the
  promise becomes a no-instance rather than a machine that might accept.

Together they make `ATMAccept 1 true` NP-complete: membership travels backwards
along `forgetInterp`, hardness forwards along `markInterp`. Nothing here is
specific to one block except the two `k = 1` facts of
`DescriptiveComplexity.Problems.Machine.AltDefs`; the general bridge replaces
them by the collapse lemmas of `DescriptiveComplexity.MachinesAltPlay`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Marking a machine: `NTMAccept ≤ᶠᵒ ATMAccept 1 true` -/

namespace MarkOne

/-- **The identity interpretation that marks every element.** Every symbol of
the machine vocabulary is copied, and the single block mark holds of
everything, so the interpreted instance carries a well-formed block
structure. -/
noncomputable def markInterp : FOInterpretation Language.turing (Language.turingAlt 1) Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .base .posn => fo%⟨u⟩ tmPosn(u)
    | _, .base .tr => fo%⟨u⟩ tmTr(u)
    | _, .base .start => fo%⟨u⟩ tmStart(u)
    | _, .base .acc => fo%⟨u⟩ tmAcc(u)
    | _, .base .blank => fo%⟨u⟩ tmBlank(u)
    | _, .base .right => fo%⟨u⟩ tmRight(u)
    | _, .base .le => fo%⟨u, v⟩ tmLe(u, v)
    | _, .base .tsrc => fo%⟨u, v⟩ tmSrc(u, v)
    | _, .base .tread => fo%⟨u, v⟩ tmRead(u, v)
    | _, .base .tdst => fo%⟨u, v⟩ tmDst(u, v)
    | _, .base .twrite => fo%⟨u, v⟩ tmWrite(u, v)
    | _, .base .inp => fo%⟨u, v⟩ tmInp(u, v)
    | _, .blk _ => ⊤

section Reading

variable {A : Type} [Language.turing.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : markInterp.Map A) : A := markInterp.mapEquivSelf A x

/-- A copied unary symbol is read as its source. -/
private theorem rel₁_map (R : (Language.turingAlt 1).Relations 1)
    (R₀ : Language.turing.Relations 1)
    (h : ∀ t, markInterp.relFormula R t = Relations.formula₁ R₀ (Term.var (0, 0)))
    (x : markInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R₀ ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map markInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- A copied binary symbol is read as its source. -/
private theorem rel₂_map (R : (Language.turingAlt 1).Relations 2)
    (R₀ : Language.turing.Relations 2)
    (h : ∀ t, markInterp.relFormula R t =
      Relations.formula₂ R₀ (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : markInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R₀ ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map markInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

/-- **Every element of the image is a state of block `0`.** -/
theorem blk_map (x : markInterp.Map A) : ATMBlk (k := 1) 0 x := by
  refine ⟨by omega, ?_⟩
  refine (FOInterpretation.relMap_map markInterp A (atmBlk (0 : Fin 1)) ![x]).mpr ?_
  simp [markInterp]

/-- **A marked machine is the machine it was built from.** -/
theorem agree (A : Type) [Language.turing.Structure A] :
    (atmData 1 (markInterp.Map A)).toTMData.Agree (markInterp.mapEquivSelf A) (tmData A) where
  posn := rel₁_map atmPosn tmPosn (fun _ => rfl)
  le := rel₂_map atmLe tmLe (fun _ => rfl)
  tr := rel₁_map atmTr tmTr (fun _ => rfl)
  start := rel₁_map atmStart tmStart (fun _ => rfl)
  acc := rel₁_map atmAcc tmAcc (fun _ => rfl)
  blank := rel₁_map atmBlank tmBlank (fun _ => rfl)
  right := rel₁_map atmRight tmRight (fun _ => rfl)
  src := rel₂_map atmSrc tmSrc (fun _ => rfl)
  read := rel₂_map atmRead tmRead (fun _ => rfl)
  dst := rel₂_map atmDst tmDst (fun _ => rfl)
  write := rel₂_map atmWrite tmWrite (fun _ => rfl)
  inp := rel₂_map atmInp tmInp (fun _ => rfl)

end Reading

/-- **The reduction is correct**: marking every element changes nothing, since
at one existential block the alternating semantics is the nondeterministic
one. -/
theorem correct (A : Type) [Language.turing.Structure A] [Finite A] [Nonempty A] :
    NTMAccept A ↔ ATMAccept 1 true (markInterp.Map A) := by
  have : Finite (markInterp.Map A) := markInterp.map_finite A
  have h := agree A
  have hbwf : (atmData 1 (markInterp.Map A)).BlocksWellFormed 1 :=
    blocksWellFormed_one_iff.mpr blk_map
  constructor
  · rintro ⟨hwf, hacc⟩
    have hwf' := h.wellFormed.mpr hwf
    exact ⟨hwf', hbwf,
      (ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mpr (h.accepts.mpr hacc)⟩
  · rintro ⟨hwf', -, halt⟩
    exact ⟨h.wellFormed.mp hwf',
      h.accepts.mp ((ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mp halt)⟩

end MarkOne

/-- **Machine acceptance reduces to alternating acceptance at one block**: mark
every element as a state of the single block. -/
noncomputable def ntmAccept_fo_reduction_atmAccept_one :
    NTMAccept ≤ᶠᵒ ATMAccept 1 true where
  Tag := Unit
  dim := 1
  toInterpretation := MarkOne.markInterp
  correct := MarkOne.correct

/-! ### Forgetting the mark: `ATMAccept 1 true ≤ᶠᵒ NTMAccept` -/

namespace ForgetOne

/-- The promise of `DescriptiveComplexity.ATMAccept` at one block – every
element is marked – as a first-order formula whose free variables are unused:
the guard the image puts on its accepting states. -/
noncomputable def markedG (γ : Type) : (Language.turingAlt 1).Formula γ :=
  fo% ∀ q, (atmBlk (0 : Fin 1))(q)

/-- **The identity interpretation that forgets the mark, with a guarded
accepting predicate.** -/
noncomputable def forgetInterp :
    FOInterpretation (Language.turingAlt 1) Language.turing Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .posn => fo%⟨u⟩ atmPosn(u)
    | _, .tr => fo%⟨u⟩ atmTr(u)
    | _, .start => fo%⟨u⟩ atmStart(u)
    | _, .acc => fo%⟨u⟩ !(markedG _) ∧ atmAcc(u)
    | _, .blank => fo%⟨u⟩ atmBlank(u)
    | _, .right => fo%⟨u⟩ atmRight(u)
    | _, .le => fo%⟨u, v⟩ atmLe(u, v)
    | _, .tsrc => fo%⟨u, v⟩ atmSrc(u, v)
    | _, .tread => fo%⟨u, v⟩ atmRead(u, v)
    | _, .tdst => fo%⟨u, v⟩ atmDst(u, v)
    | _, .twrite => fo%⟨u, v⟩ atmWrite(u, v)
    | _, .inp => fo%⟨u, v⟩ atmInp(u, v)

section Reading

variable {A : Type} [(Language.turingAlt 1).Structure A] {γ : Type}

@[simp]
theorem markedG_realize (v : γ → A) :
    (markedG γ).Realize v ↔ ∀ q : A, ATMBlk (k := 1) 0 q := by
  rw [markedG]
  simp only [Formula.realize_iAlls, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  constructor
  · intro h q
    exact ⟨by omega, h fun _ => q⟩
  · intro h i
    exact (h (i 0)).2

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : forgetInterp.Map A) : A := forgetInterp.mapEquivSelf A x

/-- A copied unary symbol is read as its source. -/
private theorem rel₁_map (R : Language.turing.Relations 1)
    (R₀ : (Language.turingAlt 1).Relations 1)
    (h : ∀ t, forgetInterp.relFormula R t = Relations.formula₁ R₀ (Term.var (0, 0)))
    (x : forgetInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R₀ ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- A copied binary symbol is read as its source. -/
private theorem rel₂_map (R : Language.turing.Relations 2)
    (R₀ : (Language.turingAlt 1).Relations 2)
    (h : ∀ t, forgetInterp.relFormula R t =
      Relations.formula₂ R₀ (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : forgetInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R₀ ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source carries its promise and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : forgetInterp.Map A) :
    TMAcc x ↔ ((∀ q : A, ATMBlk (k := 1) 0 q) ∧ ATMAcc (k := 1) (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map forgetInterp A tmAcc ![x]) ?_
  simp only [forgetInterp, Formula.realize_inf, markedG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **An instance carrying its promise is copied verbatim.** -/
theorem agree_of_marked (hm : ∀ q : A, ATMBlk (k := 1) 0 q) :
    (tmData (forgetInterp.Map A)).Agree (forgetInterp.mapEquivSelf A)
      (atmData 1 A).toTMData where
  posn := rel₁_map tmPosn atmPosn (fun _ => rfl)
  le := rel₂_map tmLe atmLe (fun _ => rfl)
  tr := rel₁_map tmTr atmTr (fun _ => rfl)
  start := rel₁_map tmStart atmStart (fun _ => rfl)
  acc x := (acc_map x).trans (and_iff_right hm)
  blank := rel₁_map tmBlank atmBlank (fun _ => rfl)
  right := rel₁_map tmRight atmRight (fun _ => rfl)
  src := rel₂_map tmSrc atmSrc (fun _ => rfl)
  read := rel₂_map tmRead atmRead (fun _ => rfl)
  dst := rel₂_map tmDst atmDst (fun _ => rfl)
  write := rel₂_map tmWrite atmWrite (fun _ => rfl)
  inp := rel₂_map tmInp atmInp (fun _ => rfl)

/-- **An instance failing its promise has no accepting state in the image.** -/
theorem not_accepts_of_not_marked (hm : ¬∀ q : A, ATMBlk (k := 1) 0 q) :
    ¬(tmData (forgetInterp.Map A)).Accepts := by
  rintro ⟨-, c, -, -, -, -, hacc⟩
  exact hm ((acc_map c.state).mp hacc).1

end Reading

/-- **The reduction is correct**: forgetting the mark is harmless on instances
that carry the promise, and the guard turns the others into no-instances. -/
theorem correct (A : Type) [(Language.turingAlt 1).Structure A] [Finite A] [Nonempty A] :
    ATMAccept 1 true A ↔ NTMAccept (forgetInterp.Map A) := by
  have : Finite (forgetInterp.Map A) := forgetInterp.map_finite A
  by_cases hm : ∀ q : A, ATMBlk (k := 1) 0 q
  · have h := agree_of_marked hm
    have hbwf : (atmData 1 A).BlocksWellFormed 1 := blocksWellFormed_one_iff.mpr hm
    constructor
    · rintro ⟨hwf, -, halt⟩
      exact ⟨h.wellFormed.mpr hwf,
        h.accepts.mpr ((ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf.2.1).mp halt)⟩
    · rintro ⟨hwf, hacc⟩
      have hwf' := h.wellFormed.mp hwf
      exact ⟨hwf', hbwf,
        (ATMData.altAccepts_true_iff_accepts not_isUniv_one hwf'.2.1).mpr (h.accepts.mp hacc)⟩
  · constructor
    · rintro ⟨-, hbwf, -⟩
      exact absurd (blocksWellFormed_one_iff.mp hbwf) hm
    · rintro ⟨-, hacc⟩
      exact absurd hacc (not_accepts_of_not_marked hm)

end ForgetOne

/-- **Alternating acceptance at one block reduces to machine acceptance**:
forget the mark, keeping the accepting states only when the promise holds. -/
noncomputable def atmAccept_one_fo_reduction_ntmAccept :
    ATMAccept 1 true ≤ᶠᵒ NTMAccept where
  Tag := Unit
  dim := 1
  toInterpretation := ForgetOne.forgetInterp
  correct := ForgetOne.correct

/-! ### The bridge at one block -/

/-- **Alternating acceptance at one existential block is in NP.** -/
theorem atmAccept_one_mem_NP : ATMAccept 1 true ∈ NP :=
  NP.mem_of_foReduction atmAccept_one_fo_reduction_ntmAccept ntmAccept_mem_NP

/-- **Alternating acceptance at one existential block is NP-hard.** -/
theorem atmAccept_one_NP_hard : NP.Hard (ATMAccept 1 true) :=
  NP.hard_of_foReduction ntmAccept_fo_reduction_atmAccept_one ntmAccept_NP_hard

/-- **The bridge at one block**: `ATMAccept 1 true` is NP-complete, the level-1
case of the machine bridge for the polynomial hierarchy. -/
theorem atmAccept_one_NP_complete : NP.Complete (ATMAccept 1 true) :=
  ⟨atmAccept_one_mem_NP, atmAccept_one_NP_hard⟩

end DescriptiveComplexity
