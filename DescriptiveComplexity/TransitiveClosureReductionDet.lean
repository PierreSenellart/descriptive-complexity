/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureReduction
import DescriptiveComplexity.TransitiveClosureDet

/-!
# FO(DTC) reductions: the logarithmic-space reduction of the textbooks

`DescriptiveComplexity.TCReduction` lets a reduction's formulas consult
*nondeterministic* walks. The classical many-one reduction for the classes at
this level is the **deterministic logarithmic-space** one, and this file is it:
`DescriptiveComplexity.DTCReduction`, notation `P ≤ᵈᵗᶜ Q`, where every walk is
read through its determinization – it may follow a step only when that step is
the only one available.

## Determinism as a formula

The packaging is the library's own, from
`DescriptiveComplexity.TransitiveClosureDet`: rather than carrying a proof that
a walk is functional – which is not first-order data, and would have to be
re-established after every pullback – the walk is *read* through

```
detStep(x̄, ȳ, z̄) := step(x̄, ȳ, z̄) ∧ ∀ w̄. step(x̄, w̄, z̄) → w̄ = ȳ
```

(`DescriptiveComplexity.ParamTCSpec.det`), which is again first-order. Every
specification then denotes a legitimate deterministic walk
(`DescriptiveComplexity.ParamTCSpec.det_functional`) and nothing has to be
assumed; on a walk that is already functional the two readings agree
(`DescriptiveComplexity.ParamTCSpec.detStepAt_of_functional`), which is how an
existing walk – the parity walk, say – is reused at this notion.

## Where it sits

`≤ᶠᵒ[≤]` ⊆ `≤ᵈᵗᶜ` ⊆ `≤ᵗᶜ` ⊆ `≤ˡᶠᵖ`: a determinized walk is a walk, so
everything `DescriptiveComplexity.TransitiveClosureReduction` proves transfers,
and PTIME, NP and coNP are closed under `≤ᵈᵗᶜ` as well.

`DescriptiveComplexity.LOGSPACE` is closed under it
(`DescriptiveComplexity.mem_LOGSPACE_of_dtcReduction`, in
`DescriptiveComplexity.TransitiveClosureReductionClosure`), by the same normal
form as NL under `≤ᵗᶜ` with one difference at the atoms: flattening a walk
that consults walks needs non-reachability at the negative occurrences, and a
deterministic walk is witnessed not to arrive by a step budget
(`DescriptiveComplexity.ParamTCSpec.detReachDecider`), where a
nondeterministic one needs inductive counting. Transitivity is
`DescriptiveComplexity.DTCReduction.trans`, the composite of
`DescriptiveComplexity.TransitiveClosureReductionTrans` read through its
determinization.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Determinizing a parameterized walk -/

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L)

/-- The renaming used by the uniqueness clause: the step formula is re-read
with its first tuple still the current one, its second tuple the freshly
quantified `w̄`, and its parameters unchanged. -/
def detVar : ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) → (((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) ⊕ Fin s.k)
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr i) => Sum.inr i
  | Sum.inr j => Sum.inl (Sum.inr j)

open Classical in
/-- **The determinized step formula** at a pair of modes: this step, and no
other step out of the current node. As in
`DescriptiveComplexity.TCSpec.detStep`, the competing successor's mode is
compared statically, so the uniqueness clause has one conjunct per mode. -/
noncomputable def detStep (m n : s.Mode) : L.Formula ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) :=
  s.step m n ⊓
    Formula.iInf fun m' : s.Mode =>
      Formula.iAlls (Fin s.k)
        (((s.step m m').relabel s.detVar).imp
          (if m' = n then
            Formula.iInf fun i : Fin s.k =>
              Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (Sum.inl (Sum.inr i))))
          else ⊥))

/-- **The deterministic reading of a walk**: the same modes, arity and
parameters, with the step formula replaced by its determinization.

Reducible, so that the modes, the arity and the parameter count of `s.det` are
those of `s` transparently – a node of the deterministic reading *is* a node,
and the block of a determinized family *is* the block of the family. -/
@[reducible]
noncomputable def det : ParamTCSpec L where
  Mode := s.Mode
  k := s.k
  par := s.par
  step := s.detStep

variable {A : Type} [L.Structure A]

theorem realize_detStep (m n : s.Mode) (x y : Fin s.k → A) (z : Fin s.par → A) :
    (s.detStep m n).Realize (Sum.elim (Sum.elim x y) z) ↔
      (s.step m n).Realize (Sum.elim (Sum.elim x y) z) ∧
        ∀ (m' : s.Mode) (w : Fin s.k → A),
          (s.step m m').Realize (Sum.elim (Sum.elim x w) z) → m' = n ∧ w = y := by
  classical
  rw [detStep, Formula.realize_inf, Formula.realize_iInf]
  have hrel : ∀ w : Fin s.k → A,
      (Sum.elim (Sum.elim (Sum.elim x y) z) w) ∘ s.detVar = Sum.elim (Sum.elim x w) z := by
    intro w
    funext i
    rcases i with (i | i) | i <;> rfl
  refine and_congr Iff.rfl ⟨fun h m' w hw => ?_, fun h m' => ?_⟩
  · have hm := (Formula.realize_iAlls).mp (h m') w
    rw [Formula.realize_imp, Formula.realize_relabel, hrel w] at hm
    have hc := hm hw
    by_cases hmn : m' = n
    · refine ⟨hmn, ?_⟩
      rw [if_pos hmn, Formula.realize_iInf] at hc
      funext i
      have hi := hc i
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var] at hi
      exact hi
    · rw [if_neg hmn, Formula.realize_bot] at hc
      exact hc.elim
  · refine Formula.realize_iAlls.mpr fun w => ?_
    rw [Formula.realize_imp, Formula.realize_relabel, hrel w]
    intro hw
    obtain ⟨hmn, hwy⟩ := h m' w hw
    rw [if_pos hmn, Formula.realize_iInf]
    intro i
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun hwy i

/-- **A determinized step is a step with no competitor.** -/
theorem detStepAt_iff (z : Fin s.par → A) (a b : s.Node A) :
    s.det.StepAt z a b ↔ s.StepAt z a b ∧ ∀ c : s.Node A, s.StepAt z a c → c = b := by
  refine Iff.trans (s.realize_detStep a.1 b.1 a.2 b.2 z) (and_congr Iff.rfl ?_)
  exact ⟨fun h c hc => Prod.ext_iff.mpr (h c.1 c.2 hc),
    fun h m' w hw => ⟨congrArg Prod.fst (h (m', w) hw), congrArg Prod.snd (h (m', w) hw)⟩⟩

variable (A) in
/-- A walk is *functional* at a structure when no node has two successors. -/
def Functional : Prop :=
  ∀ (z : Fin s.par → A) (a b c : s.Node A), s.StepAt z a b → s.StepAt z a c → b = c

variable {s}

/-- **The deterministic reading is functional**, whatever walk it comes from:
this is what makes determinization the right packaging, there being nothing
left to assume. -/
theorem det_functional : s.det.Functional A := by
  intro z a b c hb hc
  exact ((s.detStepAt_iff z a c).mp hc).2 b ((s.detStepAt_iff z a b).mp hb).1

/-- On a walk that is already functional, the deterministic reading is the
original one. -/
theorem detStepAt_of_functional (h : s.Functional A) (z : Fin s.par → A) (a b : s.Node A) :
    s.det.StepAt z a b ↔ s.StepAt z a b := by
  rw [s.detStepAt_iff z a b]
  exact ⟨And.left, fun hab => ⟨hab, fun c hc => h z a c b hc hab⟩⟩

/-- Reachability is unchanged by determinizing a functional walk. -/
theorem reachAt_det_of_functional (h : s.Functional A) (z : Fin s.par → A) (a b : s.Node A) :
    s.det.ReachAt z a b ↔ s.ReachAt z a b := by
  constructor
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((detStepAt_of_functional h z c d).mp hcd)
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((detStepAt_of_functional h z c d).mpr hcd)

end ParamTCSpec

/-! ### Determinizing a family -/

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

/-- The deterministic reading of a family: every walk read through its
determinization. Reducible, so that `F.det.block` *is* `F.block`. -/
@[reducible]
noncomputable def det : TCFamily L where
  Ix := F.Ix
  spec := fun i => (F.spec i).det

variable {F} {A : Type} [L.Structure A]

variable (F A) in
/-- A family is functional when each of its walks is. -/
def Functional : Prop :=
  ∀ i : F.Ix, (F.spec i).Functional A

/-- **A functional family is unchanged by determinization**: its relation
variables hold the same relations either way. -/
theorem reachAssign_det_of_functional (h : F.Functional A) :
    F.det.reachAssign A = F.reachAssign A := by
  funext q w
  exact propext (ParamTCSpec.reachAt_det_of_functional (h q.1) _ _ _)

end TCFamily

/-! ### An FO(TC) sentence read deterministically -/

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : TCSpec L₀) {A : Type} [L₀.Structure A] [LinearOrder A]

/-- **A functional walk may be read deterministically at no cost**: its
walk-as-an-atom formula (`DescriptiveComplexity.TCSpec.acceptsF`) still says
acceptance when the relation variables hold the *determinized* reachability
relations. This is what lets an existing walk of the catalog be reused at the
deterministic notion. -/
theorem realize_acceptsF_det (h : (spec.toFamily).Functional A) :
    (@Sentence.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        ((spec.toFamily).det.reachAssign A)) spec.acceptsF) ↔ spec.Accepts A := by
  rw [TCFamily.reachAssign_det_of_functional h]
  exact spec.realize_acceptsF

end TCSpec

/-! ### FO(DTC) reductions -/

variable {L L' : Language.{0, 0}}

/-- An **FO(DTC) reduction** from `P` to `Q` – a deterministic
logarithmic-space reduction, in the logical form of
[Immerman 1987][immerman1987languages]: an interpretation over the ordered
expansion whose formulas may read the reachability relations of a family of
walks, each read through its determinization. -/
structure DTCReduction [L.IsRelational] [L'.IsRelational] (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The walks the formulas may read – *before* determinization, which is how
  they are read. -/
  fam : TCFamily (L.sum Language.order)
  /-- The interpretation, over the base expanded by the walks' relation
  variables. -/
  toRel : RelFOInterpretation ((L.sum Language.order).sum fam.block.lang) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (TCInterpretation.Map ⟨fam.det, toRel⟩ A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (TCInterpretation.Map ⟨fam.det, toRel⟩ A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᵈᵗᶜ " Q:51 => DTCReduction P Q

section ToTC

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **An FO(DTC) reduction is an FO(TC) reduction**: a determinized walk is a
walk. Every closure property of `≤ᵗᶜ` – hence of `≤ˡᶠᵖ` – transfers along
this. -/
noncomputable def DTCReduction.toTC (f : P ≤ᵈᵗᶜ Q) : P ≤ᵗᶜ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := ⟨f.fam.det, f.toRel⟩
    map_nonempty := f.map_nonempty
    correct := f.correct }

/-- **A relativized ordered FO reduction is an FO(DTC) reduction**, consulting
no walk. -/
noncomputable def RelOrderedFOReduction.toDTC (f : P ≤ʳᶠᵒ[≤] Q) : P ≤ᵈᵗᶜ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    fam := TCFamily.empty (L.sum Language.order)
    toRel := f.toRelInterpretation.liftSource LHom.sumInl
    map_nonempty := fun A _ _ _ _ =>
      (f.mapRel_nonempty A).map
        (f.toRelInterpretation.toTCFamLEquiv (TCFamily.empty _).det A).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans (Q.iso_invariant
        (f.toRelInterpretation.toTCFamLEquiv (TCFamily.empty _).det A)).symm }

/-- **An ordered FO reduction is an FO(DTC) reduction.** -/
noncomputable def OrderedFOReduction.toDTC (f : P ≤ᶠᵒ[≤] Q) : P ≤ᵈᵗᶜ Q :=
  f.toRel.toDTC

/-- **An FO reduction is an FO(DTC) reduction.** -/
noncomputable def FOReduction.toDTC (f : P ≤ᶠᵒ Q) : P ≤ᵈᵗᶜ Q :=
  f.toOrdered.toRel.toDTC

/-- **PTIME is closed under FO(DTC) reductions.** -/
theorem mem_PTIME_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  mem_PTIME_of_tcReduction f.toTC h

/-- **NP is closed under FO(DTC) reductions.** -/
theorem mem_NP_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ NP) : P ∈ NP :=
  mem_NP_of_tcReduction f.toTC h

/-- **coNP is closed under FO(DTC) reductions.** -/
theorem mem_coNP_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ coNP) : P ∈ coNP :=
  mem_coNP_of_tcReduction f.toTC h

end ToTC

end DescriptiveComplexity
