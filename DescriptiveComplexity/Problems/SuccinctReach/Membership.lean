/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SuccinctReach.Defs

/-!
# SUCCINCT-REACH is in PSPACE

The membership half: reachability in a propositionally described transition
system is SO(TC) definable, hence in `DescriptiveComplexity.PSPACE`.

This is the cheapest membership proof in the library, and the reason is
structural: SUCCINCT-REACH *is* the syntactic image of SO(TC), so the
specification is a transcription rather than a construction. The walk carries
four monadic relation variables:

* `X`, the state being walked – the only component that matters;
* `V`, the valuation witnessing the transition that *entered* the current
  state (a transition needs an existential over all variables, auxiliary ones
  included, and a walk has no existential of its own, so the witness is stored
  in the state it leads to);
* `W₁` and `W₂`, the valuations witnessing the source and the target
  conditions. Two are needed rather than one because a walk of length zero must
  satisfy both conditions at the same state, with possibly different witnesses.

`V`, `W₁` and `W₂` are unconstrained wherever they are not used, so the walk on
the four variables projects onto the walk on states, which is what
`DescriptiveComplexity.succinctReachable_iff_accepts` says.

## Building the sentences

The three sentences share three generic shapes, stated over an arbitrary
vocabulary so that the same builder and the same realization lemma serve the
current copy of the block and the next one:

* `DescriptiveComplexity.clausesHoldS` – “every clause of this group contains a true
  literal”, the kernel of `DescriptiveComplexity.satKernel` with its symbols abstracted;
* `DescriptiveComplexity.agreeOnS` – “on every marked element these two unary relations
  agree”;
* `DescriptiveComplexity.writesS` – “on the next-state copy of every marked element, this
  unary relation holds the value the other gives to the element itself”.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Three generic sentence shapes -/

section Shapes

variable {L : Language.{0, 0}} {M : Type} [L.Structure M]

/-- “Every clause of the group `grp` contains a literal that `nu` makes
true.” -/
noncomputable def clausesHoldS (grp : L.Relations 1) (pos neg : L.Relations 2)
    (nu : L.Relations 1) : L.Sentence :=
  ((Relations.formula₁ grp (Term.var (Sum.inr 0))).imp
    (((Relations.formula₂ pos (Term.var (Sum.inl (Sum.inr 0))) (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ nu (Term.var (Sum.inr ()))) ⊔
      (Relations.formula₂ neg (Term.var (Sum.inl (Sum.inr 0))) (Term.var (Sum.inr ())) ⊓
        ∼(Relations.formula₁ nu (Term.var (Sum.inr ()))))).iExs Unit)).iAlls (Fin 1)

/-- “On every element marked by `mark`, the unary relations `nu` and `st`
agree.” -/
noncomputable def agreeOnS (mark nu st : L.Relations 1) : L.Sentence :=
  ((Relations.formula₁ mark (Term.var (Sum.inr 0))).imp
    ((Relations.formula₁ nu (Term.var (Sum.inr 0))).iff
      (Relations.formula₁ st (Term.var (Sum.inr 0))))).iAlls (Fin 1)

/-- “Whenever `y` is the `nxt`-successor of an element `x` marked by `mark`,
`nu` holds of `y` exactly when `st` holds of `x`.” -/
noncomputable def writesS (mark : L.Relations 1) (nxt : L.Relations 2)
    (nu st : L.Relations 1) : L.Sentence :=
  ((Relations.formula₁ mark (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ nxt (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
      ((Relations.formula₁ nu (Term.var (Sum.inr 1))).iff
        (Relations.formula₁ st (Term.var (Sum.inr 0)))))).iAlls (Fin 2)

theorem realize_clausesHoldS (grp : L.Relations 1) (pos neg : L.Relations 2)
    (nu : L.Relations 1) :
    M ⊨ clausesHoldS grp pos neg nu ↔
      ∀ c : M, RelMap grp ![c] → ∃ x : M,
        (RelMap pos ![c, x] ∧ RelMap nu ![x]) ∨ (RelMap neg ![c, x] ∧ ¬RelMap nu ![x]) := by
  rw [clausesHoldS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (fun _ => c) hc
    exact ⟨x (), hx⟩
  · intro h i hc
    obtain ⟨x, hx⟩ := h (i 0) hc
    exact ⟨fun _ => x, hx⟩

theorem realize_agreeOnS (mark nu st : L.Relations 1) :
    M ⊨ agreeOnS mark nu st ↔
      ∀ x : M, RelMap mark ![x] → (RelMap nu ![x] ↔ RelMap st ![x]) := by
  rw [agreeOnS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩

theorem realize_writesS (mark : L.Relations 1) (nxt : L.Relations 2)
    (nu st : L.Relations 1) :
    M ⊨ writesS mark nxt nu st ↔
      ∀ x y : M, RelMap mark ![x] → RelMap nxt ![x, y] →
        (RelMap nu ![y] ↔ RelMap st ![x]) := by
  rw [writesS]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun h x y hx hxy => h ![x, y] (by simpa using hx) (by simpa using hxy),
    fun h i hi hii => h (i 0) (i 1) hi hii⟩

end Shapes

/-! ### The block and the vocabularies -/

section Spec

open SOBlock

/-- The block of the SO(TC) specification of SUCCINCT-REACH: four unary
relation variables – the state, the transition witness, and the two endpoint
witnesses. -/
def srBlock : SOBlock where
  ι := Bool × Bool
  arity := fun _ => 1

/-- The relation variable holding the current state. -/
abbrev srX : Bool × Bool := (false, false)

/-- The relation variable holding the valuation witnessing the transition that
entered the current state. -/
abbrev srV : Bool × Bool := (false, true)

/-- The relation variable holding the valuation witnessing the source
condition. -/
abbrev srW₁ : Bool × Bool := (true, false)

/-- The relation variable holding the valuation witnessing the target
condition. -/
abbrev srW₂ : Bool × Bool := (true, true)

/-- The symbol of the relation variable `i` of the block. -/
def srSym (i : Bool × Bool) : srBlock.lang.Relations 1 := ⟨i, rfl⟩

/-- The input vocabulary together with the order, over which the sentences of
an SO(TC) specification live. -/
abbrev srBase : Language := Language.transSys.sum Language.order

/-- The vocabulary of the endpoint sentences: one copy of the block. -/
abbrev srLang₁ : Language := srBase.sum srBlock.lang

/-- The vocabulary of the transition sentence: two copies of the block. -/
abbrev srLang₂ : Language := srLang₁.sum srBlock.lang

/-- An input symbol, in the endpoint vocabulary. -/
abbrev srIn₁ {n : ℕ} (r : Language.transSys.Relations n) : srLang₁.Relations n :=
  Sum.inl (Sum.inl r)

/-- A relation variable of the block, in the endpoint vocabulary. -/
abbrev srVar₁ (i : Bool × Bool) : srLang₁.Relations 1 := Sum.inr (srSym i)

/-- An input symbol, in the transition vocabulary. -/
abbrev srIn₂ {n : ℕ} (r : Language.transSys.Relations n) : srLang₂.Relations n :=
  Sum.inl (Sum.inl (Sum.inl r))

/-- A relation variable of the *current* copy of the block, in the transition
vocabulary. -/
abbrev srCur₂ (i : Bool × Bool) : srLang₂.Relations 1 := Sum.inl (Sum.inr (srSym i))

/-- A relation variable of the *next* copy of the block, in the transition
vocabulary. -/
abbrev srNext₂ (i : Bool × Bool) : srLang₂.Relations 1 := Sum.inr (srSym i)

/-- **The SO(TC) specification of SUCCINCT-REACH.** A transition holds when the
next state's transition witness satisfies every transition clause, reads the
current state on the state variables and writes the next state on their
next-state copies; the endpoint conditions are the two clause groups checked
against their own witnesses. -/
noncomputable def srSpec : SOTCSpec Language.transSys where
  B := srBlock
  step :=
    clausesHoldS (srIn₂ tsStepCl) (srIn₂ tsPosIn) (srIn₂ tsNegIn) (srNext₂ srV) ⊓
      (agreeOnS (srIn₂ tsStateVar) (srNext₂ srV) (srCur₂ srX) ⊓
        writesS (srIn₂ tsStateVar) (srIn₂ tsNext) (srNext₂ srV) (srNext₂ srX))
  src :=
    clausesHoldS (srIn₁ tsSrcCl) (srIn₁ tsPosIn) (srIn₁ tsNegIn) (srVar₁ srW₁) ⊓
      agreeOnS (srIn₁ tsStateVar) (srVar₁ srW₁) (srVar₁ srX)
  tgt :=
    clausesHoldS (srIn₁ tsTgtCl) (srIn₁ tsPosIn) (srIn₁ tsNegIn) (srVar₁ srW₂) ⊓
      agreeOnS (srIn₁ tsStateVar) (srVar₁ srW₂) (srVar₁ srX)

end Spec

/-! ### Reading the specification back -/

section Reading

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The predicate held by the relation variable `i` in the assignment `ρ`. -/
def srPred (ρ : srBlock.Assignment A) (i : Bool × Bool) : A → Prop :=
  fun a => ρ i fun _ => a

/-- The assignment holding the given four predicates. -/
def srAssign (f : Bool × Bool → A → Prop) : srBlock.Assignment A :=
  fun i v => f i (v ⟨0, Nat.zero_lt_one⟩)

omit [Language.transSys.Structure A] [LinearOrder A] in
@[simp]
theorem srPred_srAssign (f : Bool × Bool → A → Prop) (i : Bool × Bool) :
    srPred (srAssign f) i = f i :=
  rfl

/-- Splitting a conjunction of endpoint sentences, with the block expansion
supplied explicitly: instance search does not see through the specification's
block field. -/
theorem srRealize_inf₁ (ρ : srBlock.Assignment A) (φ ψ : srLang₁.Sentence) :
    letI := srBlock.structure₁ (L := srBase) ρ
    ((A ⊨ (φ ⊓ ψ)) ↔ (A ⊨ φ) ∧ (A ⊨ ψ)) :=
  letI := srBlock.structure₁ (L := srBase) ρ
  Formula.realize_inf

/-- The same splitting for the transition sentence. -/
theorem srRealize_inf₂ (ρ σ : srBlock.Assignment A) (φ ψ : srLang₂.Sentence) :
    letI := srBlock.structure₂ (L := srBase) ρ σ
    ((A ⊨ (φ ⊓ ψ)) ↔ (A ⊨ φ) ∧ (A ⊨ ψ)) :=
  letI := srBlock.structure₂ (L := srBase) ρ σ
  Formula.realize_inf

theorem relMap_srVar₁ (ρ : srBlock.Assignment A) (i : Bool × Bool) (w : Fin 1 → A) :
    @RelMap srLang₁ A (srBlock.structure₁ (L := srBase) ρ) 1 (srVar₁ i) w ↔
      srPred ρ i (w 0) := by
  change ρ i _ ↔ ρ i _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_srIn₁ {n : ℕ} (ρ : srBlock.Assignment A)
    (r : Language.transSys.Relations n) (w : Fin n → A) :
    @RelMap srLang₁ A (srBlock.structure₁ (L := srBase) ρ) n (srIn₁ r) w ↔ RelMap r w :=
  Iff.rfl

theorem relMap_srCur₂ (ρ σ : srBlock.Assignment A) (i : Bool × Bool) (w : Fin 1 → A) :
    @RelMap srLang₂ A (srBlock.structure₂ (L := srBase) ρ σ) 1 (srCur₂ i) w ↔
      srPred ρ i (w 0) := by
  change ρ i _ ↔ ρ i _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_srNext₂ (ρ σ : srBlock.Assignment A) (i : Bool × Bool) (w : Fin 1 → A) :
    @RelMap srLang₂ A (srBlock.structure₂ (L := srBase) ρ σ) 1 (srNext₂ i) w ↔
      srPred σ i (w 0) := by
  change σ i _ ↔ σ i _
  exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))

theorem relMap_srIn₂ {n : ℕ} (ρ σ : srBlock.Assignment A)
    (r : Language.transSys.Relations n) (w : Fin n → A) :
    @RelMap srLang₂ A (srBlock.structure₂ (L := srBase) ρ σ) n (srIn₂ r) w ↔ RelMap r w :=
  Iff.rfl

/-- A starting state of the specification is a state whose `W₁` component
witnesses the source condition. -/
theorem srSpec_isSrc_iff (ρ : srBlock.Assignment A) :
    srSpec.IsSrc ρ ↔
      ClausesHold A (srPred ρ srW₁) tsSrcCl ∧ ReadsCur A (srPred ρ srW₁) (srPred ρ srX) := by
  letI := srBlock.structure₁ (L := srBase) ρ
  have h : srSpec.IsSrc ρ ↔
      ((A ⊨ clausesHoldS (srIn₁ tsSrcCl) (srIn₁ tsPosIn) (srIn₁ tsNegIn) (srVar₁ srW₁)) ∧
        (A ⊨ agreeOnS (srIn₁ tsStateVar) (srVar₁ srW₁) (srVar₁ srX))) :=
    srRealize_inf₁ _ _ _
  rw [h, realize_clausesHoldS, realize_agreeOnS]
  simp only [relMap_srIn₁, relMap_srVar₁, Matrix.cons_val_zero]
  exact Iff.rfl

/-- An accepting state of the specification is a state whose `W₂` component
witnesses the target condition. -/
theorem srSpec_isTgt_iff (ρ : srBlock.Assignment A) :
    srSpec.IsTgt ρ ↔
      ClausesHold A (srPred ρ srW₂) tsTgtCl ∧ ReadsCur A (srPred ρ srW₂) (srPred ρ srX) := by
  letI := srBlock.structure₁ (L := srBase) ρ
  have h : srSpec.IsTgt ρ ↔
      ((A ⊨ clausesHoldS (srIn₁ tsTgtCl) (srIn₁ tsPosIn) (srIn₁ tsNegIn) (srVar₁ srW₂)) ∧
        (A ⊨ agreeOnS (srIn₁ tsStateVar) (srVar₁ srW₂) (srVar₁ srX))) :=
    srRealize_inf₁ _ _ _
  rw [h, realize_clausesHoldS, realize_agreeOnS]
  simp only [relMap_srIn₁, relMap_srVar₁, Matrix.cons_val_zero]
  exact Iff.rfl

/-- A transition of the specification is a transition of the system, witnessed
by the `V` component of the state it enters. -/
theorem srSpec_step_iff (ρ σ : srBlock.Assignment A) :
    srSpec.Step ρ σ ↔
      (ClausesHold A (srPred σ srV) tsStepCl ∧ ReadsCur A (srPred σ srV) (srPred ρ srX) ∧
        WritesNext A (srPred σ srV) (srPred σ srX)) := by
  letI := srBlock.structure₂ (L := srBase) ρ σ
  have h : srSpec.Step ρ σ ↔
      ((A ⊨ clausesHoldS (srIn₂ tsStepCl) (srIn₂ tsPosIn) (srIn₂ tsNegIn) (srNext₂ srV)) ∧
        ((A ⊨ agreeOnS (srIn₂ tsStateVar) (srNext₂ srV) (srCur₂ srX)) ∧
          (A ⊨ writesS (srIn₂ tsStateVar) (srIn₂ tsNext) (srNext₂ srV) (srNext₂ srX)))) :=
    Iff.trans (srRealize_inf₂ ρ σ _ _) (and_congr Iff.rfl (srRealize_inf₂ ρ σ _ _))
  rw [h, realize_clausesHoldS, realize_agreeOnS, realize_writesS]
  simp only [relMap_srIn₂, relMap_srNext₂, relMap_srCur₂, Matrix.cons_val_zero]
  exact Iff.rfl

end Reading

/-! ### Correctness of the specification -/

section Correctness

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The state of the walk holding a given state, transition witness and pair of
endpoint witnesses. -/
private def srLift (S v w₁ w₂ : A → Prop) : srBlock.Assignment A :=
  srAssign fun i => if i = srX then S else if i = srV then v else if i = srW₁ then w₁ else w₂

omit [Language.transSys.Structure A] [LinearOrder A] in
private theorem srLift_x (S v w₁ w₂ : A → Prop) : srPred (srLift S v w₁ w₂) srX = S := rfl

omit [Language.transSys.Structure A] [LinearOrder A] in
private theorem srLift_v (S v w₁ w₂ : A → Prop) : srPred (srLift S v w₁ w₂) srV = v := rfl

omit [Language.transSys.Structure A] [LinearOrder A] in
private theorem srLift_w₁ (S v w₁ w₂ : A → Prop) : srPred (srLift S v w₁ w₂) srW₁ = w₁ := rfl

omit [Language.transSys.Structure A] [LinearOrder A] in
private theorem srLift_w₂ (S v w₁ w₂ : A → Prop) : srPred (srLift S v w₁ w₂) srW₂ = w₂ := rfl

/-- A walk of the system lifts to a walk of the specification, along which the
two endpoint witnesses are carried unchanged. -/
private theorem srReach_lift {S S' : A → Prop}
    (h : Relation.ReflTransGen (StepRel A) S S') (v w₁ w₂ : A → Prop) :
    ∃ v' : A → Prop, srSpec.Reach (srLift S v w₁ w₂) (srLift S' v' w₁ w₂) := by
  induction h with
  | refl => exact ⟨v, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨v', hv'⟩ := ih
    obtain ⟨ν, hcl, hr, hw⟩ := hcd
    exact ⟨ν, hv'.tail ((srSpec_step_iff _ _).mpr ⟨hcl, hr, hw⟩)⟩

/-- A walk of the specification projects to a walk of the system. -/
private theorem srReach_proj {ρ σ : srBlock.Assignment A} (h : srSpec.Reach ρ σ) :
    Relation.ReflTransGen (StepRel A) (srPred ρ srX) (srPred σ srX) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    obtain ⟨hcl, hr, hw⟩ := (srSpec_step_iff c d).mp hcd
    exact ih.tail ⟨srPred d srV, hcl, hr, hw⟩

/-- **The specification is correct**: it accepts a transition system exactly
when some target state is reachable from some source state. -/
theorem succinctReachable_iff_accepts :
    SuccinctReachable A ↔ srSpec.Accepts A := by
  constructor
  · rintro ⟨S, S', ⟨ν₁, hcl₁, hr₁⟩, ⟨ν₂, hcl₂, hr₂⟩, hreach⟩
    obtain ⟨v', hv'⟩ := srReach_lift hreach ν₁ ν₁ ν₂
    refine ⟨srLift S ν₁ ν₁ ν₂, srLift S' v' ν₁ ν₂, ?_, ?_, hv'⟩
    · exact (srSpec_isSrc_iff _).mpr ⟨hcl₁, hr₁⟩
    · exact (srSpec_isTgt_iff _).mpr ⟨hcl₂, hr₂⟩
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    obtain ⟨hcl₁, hr₁⟩ := (srSpec_isSrc_iff ρ).mp hsrc
    obtain ⟨hcl₂, hr₂⟩ := (srSpec_isTgt_iff σ).mp htgt
    exact ⟨srPred ρ srX, srPred σ srX, ⟨srPred ρ srW₁, hcl₁, hr₁⟩,
      ⟨srPred σ srW₂, hcl₂, hr₂⟩, srReach_proj hreach⟩

end Correctness

/-- **SUCCINCT-REACH is SO(TC) definable**: the walk on states is the walk of
the specification, its extra components carrying the existential witnesses a
transitive closure cannot quantify on its own. -/
theorem succinctReach_sotcDefinable : SOTCDefinable SUCCINCTREACH :=
  ⟨srSpec, fun _ _ _ _ _ => succinctReachable_iff_accepts⟩

/-- **SUCCINCT-REACH is in PSPACE.** -/
theorem succinctReach_mem_PSPACE : SUCCINCTREACH ∈ PSPACE :=
  succinctReach_sotcDefinable

end DescriptiveComplexity
