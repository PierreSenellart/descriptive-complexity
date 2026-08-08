/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.FreeCopy
import DescriptiveComplexity.Exponential.Classes
import DescriptiveComplexity.FixedPointParam
import DescriptiveComplexity.FixedPointStepRel

/-!
# The copy a point names, and EXPTIME without the order

`DescriptiveComplexity.Exponential.FreeSpace` reads the inner problem inside one
of the copies of an order-guessing expansion and keeps it in `PSPACE`, the copy
being **guessed** as a relation. A deterministic class cannot guess, so
`DescriptiveComplexity.PTIME` needs the copy to be named by something a fixed
point can carry: **one element**. A copy *is* the class of any one of its
points, so “some copy answers yes” is
`DescriptiveComplexity.ExpExpansion.somePtCls`, an existential over points, and
`DescriptiveComplexity.mem_PTIME_exElement` – every relation variable of the
induction carrying the point as a further argument – is what keeps it in
`PTIME`.

Two steps, then:

* the inner problem read in the class of a **marked** point is a *relativized*
  ordered reduction to it (`DescriptiveComplexity.ExpExpansion.ptReduction`), so
  membership carries over
  (`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`);
* the mark is then existentially quantified away
  (`DescriptiveComplexity.ExpExpansion.mem_PTIME_somePtCls`).

The conclusion is `DescriptiveComplexity.mem_EXPTIME_iff_solfpDefinableFree`:
`EXPTIME` is SO(LFP) with no order in the statement, as `EXPSPACE` is SO(PFP).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-! ### The copy a point names -/

section PointCls

variable {N : Type} [X.orderFree.E.Structure N]

/-- **The copy a point names**: the points carrying its guessed order – or the
whole structure when it carries none, so that the part is never empty. -/
def ptClsSet (c : N) : Set N :=
  {y | RelMap X.sameSym ![c, y] ∨ ∀ w : N, ¬RelMap X.sameSym ![c, w]}

variable {X}

theorem ptClsSet_nonempty [Nonempty N] (c : N) : (X.ptClsSet c).Nonempty := by
  by_cases h : ∃ y : N, RelMap X.sameSym ![c, y]
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, Or.inl hy⟩
  · obtain ⟨y⟩ := ‹Nonempty N›
    exact ⟨y, Or.inr fun w hw => h ⟨w, hw⟩⟩

/-- At a point that carries an order – every point of an order-guessing
expansion does – the copy it names is its class. -/
theorem ptClsSet_eq_of_refl {c : N} (h : RelMap X.sameSym ![c, c]) :
    X.ptClsSet c = {y | RelMap X.sameSym ![c, y]} := by
  ext y
  exact ⟨fun hy => hy.elim id fun hy' => (hy' c h).elim, Or.inl⟩

end PointCls

/-! ### Some copy answers yes, the copy being named by a point -/

section SomePt

variable {N N' : Type} [X.orderFree.E.Structure N] [X.orderFree.E.Structure N']

theorem image_ptClsSet (e : N ≃[X.orderFree.E] N') (c : N) :
    e '' X.ptClsSet c = X.ptClsSet (e c) := by
  have hsame : ∀ x y : N, RelMap X.sameSym ![x, y] ↔ RelMap X.sameSym ![e x, e y] :=
    fun x y => relMap_equiv₂ e X.sameSym x y
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine hy.elim (fun h => Or.inl ((hsame c y).mp h)) fun h => Or.inr fun w hw => ?_
    refine h (e.symm w) ((hsame c (e.symm w)).mpr ?_)
    rwa [e.apply_symm_apply]
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    refine hz.elim (fun h => Or.inl ((hsame c (e.symm z)).mpr ?_)) fun h => Or.inr fun w hw => ?_
    · rwa [e.apply_symm_apply]
    · exact h (e w) ((hsame c w).mp hw)

end SomePt

/-- **Some copy answers yes**, the copy being named by one of its points: the
problem that replaces the inner one when the inner class cannot guess. -/
def somePtCls (Q : DecisionProblem X.E) : DecisionProblem X.orderFree.E where
  Holds N _ := ∃ c : N, Q (X.clsPart (X.ptClsSet c))
  iso_invariant := by
    intro N N' _ _ e
    constructor
    · rintro ⟨c, hQ⟩
      refine ⟨e c, ?_⟩
      have h := (Q.iso_invariant (clsPartEquiv X e (X.ptClsSet c))).mp hQ
      exact image_ptClsSet X e c ▸ h
    · rintro ⟨c, hQ⟩
      refine ⟨e.symm c, ?_⟩
      have h := (Q.iso_invariant (clsPartEquiv X e.symm (X.ptClsSet c))).mp hQ
      exact image_ptClsSet X e.symm c ▸ h

/-! ### The copy of a marked point, as a definable part -/

section Marked

/-- The vocabulary the inner problem is read over: the order-guessing one, plus
a mark for the point that names the copy. -/
noncomputable abbrev ptLangOf : Language.{0, 0} := newLang X.orderFree.E

/-- The order-guessing structure underlying a structure that also carries a
marked point. -/
@[instance_reducible]
noncomputable def ptReduct (X : ExpExpansion L) (M : Type) [X.ptLangOf.Structure M] :
    X.orderFree.E.Structure M :=
  (LHom.sumInl : X.orderFree.E →ᴸ X.ptLangOf).reduct M

/-- The part the reduction reads: the copy the marked point names – or the whole
structure when nothing marked names anything, so that the part is never
empty. -/
def markPtSet (X : ExpExpansion L) (M : Type) [X.ptLangOf.Structure M] : Set M :=
  {y | (∃ m : M, @RelMap X.ptLangOf M ‹_› 1 (Sum.inr Language.oldSym) ![m] ∧
        @RelMap X.orderFree.E M (X.ptReduct M) 2 X.sameSym ![m, y]) ∨
    ∀ m w : M, ¬(@RelMap X.ptLangOf M ‹_› 1 (Sum.inr Language.oldSym) ![m] ∧
      @RelMap X.orderFree.E M (X.ptReduct M) 2 X.sameSym ![m, w])}

variable {X}

theorem markPtSet_nonempty {M : Type} [X.ptLangOf.Structure M] [Nonempty M] :
    (X.markPtSet M).Nonempty := by
  by_cases h : ∃ m y : M, @RelMap X.ptLangOf M ‹_› 1 (Sum.inr Language.oldSym) ![m] ∧
      @RelMap X.orderFree.E M (X.ptReduct M) 2 X.sameSym ![m, y]
  · obtain ⟨m, y, hy⟩ := h
    exact ⟨y, Or.inl ⟨m, hy⟩⟩
  · obtain ⟨y⟩ := ‹Nonempty M›
    exact ⟨y, Or.inr fun m w hw => h ⟨m, w, hw⟩⟩

/-- **The marked point names the copy the point names**: at the structure whose
mark is a single point, the part the reduction reads is the copy of that
point. -/
theorem markPtSet_markOne {N : Type} [inst : X.orderFree.E.Structure N] (c : N) :
    @markPtSet L X N (markOne X.orderFree.E c) = X.ptClsSet c := by
  have hold : ∀ m : N, (@RelMap X.ptLangOf N (markOne X.orderFree.E c) 1
      (Sum.inr Language.oldSym) ![m] ↔ m = c) := fun _ => Iff.rfl
  have hsame : ∀ m y : N, (@RelMap X.orderFree.E N
      (@ptReduct L X N (markOne X.orderFree.E c)) 2 X.sameSym ![m, y] ↔
    @RelMap X.orderFree.E N inst 2 X.sameSym ![m, y]) := fun _ _ => Iff.rfl
  ext y
  constructor
  · rintro (⟨m, hm, hmy⟩ | h)
    · have hmc : m = c := (hold m).mp hm
      subst hmc
      exact Or.inl ((hsame m y).mp hmy)
    · exact Or.inr fun w hw => h c w ⟨(hold c).mpr rfl, (hsame c w).mpr hw⟩
  · rintro (h | h)
    · exact Or.inl ⟨c, (hold c).mpr rfl, (hsame c y).mpr h⟩
    · refine Or.inr fun m w hw => h w ?_
      have hmc : m = c := (hold m).mp hw.1
      subst hmc
      exact (hsame m w).mp hw.2

variable (X)

/-- **The inner problem read in the copy the marked point names.** -/
def ptProblem (Q : DecisionProblem X.E) : DecisionProblem X.ptLangOf where
  Holds M _ :=
    letI := X.ptReduct M
    Q (X.clsPart (X.markPtSet M))
  iso_invariant := by
    intro M M' _ _ e
    letI := X.ptReduct M
    letI := X.ptReduct M'
    letI e' := reductEquiv (LHom.sumInl : X.orderFree.E →ᴸ X.ptLangOf) e
    have hold : ∀ x : M, RelMap (L := X.ptLangOf) (Sum.inr Language.oldSym) ![x] ↔
        RelMap (L := X.ptLangOf) (Sum.inr Language.oldSym) ![e x] :=
      fun x => relMap_equiv₁ e (Sum.inr Language.oldSym) x
    have hsame : ∀ x y : M, RelMap X.sameSym ![x, y] ↔ RelMap X.sameSym ![e x, e y] :=
      fun x y => relMap_equiv₂ e' X.sameSym x y
    have himg : (⇑e' '' X.markPtSet M) = X.markPtSet M' := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine hy.elim (fun hy' => ?_) fun h => Or.inr fun m w hw => ?_
        · obtain ⟨m, hm, hmy⟩ := hy'
          exact Or.inl ⟨e m, (hold m).mp hm, (hsame m y).mp hmy⟩
        · refine h (e.symm m) (e.symm w) ⟨?_, ?_⟩
          · refine (hold (e.symm m)).mpr ?_
            rw [e.apply_symm_apply]
            exact hw.1
          · refine (hsame (e.symm m) (e.symm w)).mpr ?_
            rw [e.apply_symm_apply, e.apply_symm_apply]
            exact hw.2
      · intro hz
        refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
        refine hz.elim (fun hz' => ?_) fun h => Or.inr fun m w hw =>
          h (e m) (e w) ⟨(hold m).mp hw.1, (hsame m w).mp hw.2⟩
        obtain ⟨m, hm, hmz⟩ := hz'
        refine Or.inl ⟨e.symm m, ?_, ?_⟩
        · refine (hold (e.symm m)).mpr ?_
          rw [e.apply_symm_apply]
          exact hm
        · refine (hsame (e.symm m) (e.symm z)).mpr ?_
          rw [e.apply_symm_apply, e.apply_symm_apply]
          exact hmz
    refine Iff.trans (Q.iso_invariant (clsPartEquiv X e' (X.markPtSet M))) ?_
    exact himg ▸ Iff.rfl

/-! ### The reduction reading the copy of the marked point -/


/-- The mark, as a symbol of the source vocabulary of the reduction. -/
noncomputable abbrev oldSymO : (X.ptLangOf.sum Language.order).Relations 1 :=
  Sum.inl (Sum.inr Language.oldSym)

/-- A relation of the original vocabulary, as a symbol of the source vocabulary
of the reduction. -/
noncomputable abbrev origSymP {n : ℕ} (r : X.E.Relations n) :
    (X.ptLangOf.sum Language.order).Relations n :=
  Sum.inl (Sum.inl (X.origSym r))

/-- The unary shift of a nullary symbol, as a symbol of the source vocabulary of
the reduction. -/
noncomputable abbrev nullSymP (s : X.E.Relations 0) :
    (X.ptLangOf.sum Language.order).Relations 1 :=
  Sum.inl (Sum.inl (X.nullSym s))

/-- The same-order symbol, in the source vocabulary of the reduction. -/
noncomputable abbrev sameSymP : (X.ptLangOf.sum Language.order).Relations 2 :=
  Sum.inl (Sum.inl X.sameSym)

/-- Nothing marked names anything. -/
noncomputable def noPtF {α : Type} : (X.ptLangOf.sum Language.order).Formula α :=
  Formula.iAlls (Fin 2)
    (∼(Relations.formula₁ X.oldSymO (Term.var (Sum.inr 0)) ⊓
      Relations.formula₂ X.sameSymP (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))

/-- The domain of the reduction: the copy the marked point names, or everything
when nothing is marked. -/
noncomputable def ptF {α : Type} (x : α) : (X.ptLangOf.sum Language.order).Formula α :=
  Formula.iExs (Fin 1)
      (Relations.formula₁ X.oldSymO (Term.var (Sum.inr 0)) ⊓
        Relations.formula₂ X.sameSymP (Term.var (Sum.inr 0)) (Term.var (Sum.inl x))) ⊔
    X.noPtF

variable {X} {M : Type} [X.ptLangOf.Structure M] [LinearOrder M]

theorem realize_noPtF {α : Type} (v : α → M) :
    (X.noPtF (α := α)).Realize v ↔
      ∀ m w : M, ¬(@RelMap X.ptLangOf M ‹_› 1 (Sum.inr Language.oldSym) ![m] ∧
        @RelMap X.orderFree.E M (X.ptReduct M) 2 X.sameSym ![m, w]) := by
  simp only [noPtF, Formula.realize_iAlls, Formula.realize_not, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h m w => h ![m, w], fun h i hi => h (i 0) (i 1) hi⟩

theorem realize_ptF {α : Type} (v : α → M) (x : α) :
    (X.ptF x).Realize v ↔ v x ∈ X.markPtSet M := by
  refine Iff.trans Formula.realize_sup (or_congr ?_ (realize_noPtF v))
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨m, hm⟩ => ⟨fun _ => m, hm⟩⟩

variable (X)

/-- **The interpretation reading the original vocabulary inside the copy the
marked point names.** -/
noncomputable def ptInterp :
    RelFOInterpretation (X.ptLangOf.sum Language.order) X.E Unit 1 where
  relFormula {n} r _ :=
    match n, r with
    | 0, r => Formula.iExs (Fin 1)
        (X.ptF (Sum.inr 0) ⊓ Relations.formula₁ (X.nullSymP r) (Term.var (Sum.inr 0)))
    | (_ + 1), r => Relations.formula (X.origSymP r) fun i => Term.var (i, 0)
  domFormula _ := X.ptF (0 : Fin 1)

variable {X} {M : Type} [X.ptLangOf.Structure M] [LinearOrder M]

theorem mem_ptInterp_dom (t : Unit) (w : Fin 1 → M) :
    ((X.ptInterp).domFormula t).Realize w ↔ w 0 ∈ X.markPtSet M :=
  realize_ptF w 0

/-- **The interpreted universe is the copy the marked point names.** -/
noncomputable def ptInterpEquiv :
    letI := X.ptReduct M
    X.clsPart (X.markPtSet M) ≃[X.E] (X.ptInterp).MapRel M :=
  letI := X.ptReduct M
  { toFun := fun y => ⟨((), fun _ => y.1), (mem_ptInterp_dom () _).mpr y.2⟩
    invFun := fun z => ⟨z.1.2 0, (mem_ptInterp_dom () _).mp z.2⟩
    left_inv := fun _ => rfl
    right_inv := fun z => Subtype.ext (Prod.ext rfl (funext fun i => by
      fin_cases i
      rfl))
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} r x => by
      match n, r with
      | 0, r =>
        refine Iff.trans ?_ (relMap_clsPart_zero r x).symm
        refine Iff.trans (RelFOInterpretation.relMap_mapRel _ _ _ _) ?_
        refine Iff.trans Formula.realize_iExs ?_
        constructor
        · rintro ⟨i, hi⟩
          refine ⟨i 0, ?_, ?_⟩
          · exact (realize_ptF (Sum.elim _ i) (Sum.inr 0)).mp (Formula.realize_inf.mp hi).1
          · have h' : RelMap (X.nullSymP r) ![i 0] :=
              Formula.realize_rel₁.mp (Formula.realize_inf.mp hi).2
            rw [vec_one_eq] at h'
            exact h'
        · rintro ⟨y, hy, hyr⟩
          refine ⟨fun _ => y, Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
          · exact (realize_ptF (Sum.elim _ fun _ => y) (Sum.inr 0)).mpr hy
          · refine Formula.realize_rel₁.mpr ?_
            simp only [Term.realize_var, Sum.elim_inr]
            rw [vec_one_eq]
            exact hyr
      | (m + 1), r =>
        refine Iff.trans ?_ (relMap_clsPart_succ r x).symm
        refine Iff.trans (RelFOInterpretation.relMap_mapRel _ _ _ _) ?_
        exact Formula.realize_rel }

variable (X)

/-- **Reading the inner problem in the copy of the marked point is a relativized
ordered reduction to it.** -/
noncomputable def ptReduction (Q : DecisionProblem X.E) : X.ptProblem Q ≤ʳᶠᵒ[≤] Q where
  Tag := Unit
  dim := 1
  toRelInterpretation := X.ptInterp
  dom_nonempty := by
    intro A _ _ _ _
    obtain ⟨x, hx⟩ := markPtSet_nonempty (X := X) (M := A)
    exact ⟨(), fun _ => x, (mem_ptInterp_dom () _).mpr hx⟩
  correct := by
    intro A _ _ _ _
    exact Q.iso_invariant (ptInterpEquiv (X := X) (M := A))

/-- **The inner problem read in the copy of the marked point stays in polynomial
time.** -/
theorem mem_PTIME_ptProblem {Q : DecisionProblem X.E} (hQ : Q ∈ PTIME) :
    X.ptProblem Q ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME _).mp
    (IFPDefinable.of_relOrderedReduction (X.ptReduction Q)
      ((ifpDefinable_iff_mem_PTIME Q).mpr hQ))

end Marked

/-! ### Quantifying the point away -/

/-- **“Some copy answers yes” stays in polynomial time**: the point naming the
copy is carried by every relation variable of the induction. -/
theorem mem_PTIME_somePtCls {Q : DecisionProblem X.E} (hQ : Q ∈ PTIME) :
    X.somePtCls Q ∈ PTIME := by
  refine mem_PTIME_exElement (X.mem_PTIME_ptProblem hQ) fun N _ _ _ => ?_
  refine exists_congr fun c => ?_
  exact (iff_of_eq (congrArg (fun S => Q (X.clsPart S)) (markPtSet_markOne (X := X) c))).symm

/-! ### The correctness of “some copy answers yes” -/

section Correct

variable {X} {Q : DecisionProblem X.E} {A : Type} [L.Structure A]

/-- **The copy a point of an order-guessing expansion names is a copy**: the
points carrying its guessed order. -/
theorem isCls_ptClsSet (c : X.orderFree.Map A) : IsCls X (X.ptClsSet c) := by
  have hrefl : RelMap X.sameSym ![c, c] := (relMap_sameSym ![c, c]).mpr fun _ => Iff.rfl
  have heq := ptClsSet_eq_of_refl (X := X) hrefl
  refine ⟨⟨c, heq ▸ hrefl⟩, fun x hx y => ?_⟩
  rw [heq] at hx ⊢
  have hcx := (relMap_sameSym ![c, x]).mp hx
  refine Iff.trans (relMap_sameSym ![c, y]) (Iff.trans ?_ (relMap_sameSym ![x, y]).symm)
  exact ⟨fun h w => (hcx w).symm.trans (h w), fun h w => (hcx w).trans (h w)⟩

variable [Finite A] [Nonempty A]

/-- **Some copy answers yes exactly when the inner problem does, at some linear
order of the instance** – the same statement as
`DescriptiveComplexity.ExpExpansion.someCls_map_iff`, with the copy named by a
point rather than guessed as a set. -/
theorem somePtCls_map_iff :
    (X.somePtCls Q) (X.orderFree.Map A) ↔
      ∃ lo : LinearOrder A, letI := lo; Q (X.Map A) := by
  constructor
  · rintro ⟨c, hQ⟩
    letI lo := guessedLinearOrder c
    refine ⟨lo, ?_⟩
    have hrefl : RelMap X.sameSym ![c, c] := (relMap_sameSym ![c, c]).mpr fun _ => Iff.rfl
    have hord : ∀ w : Fin 2 → A, pointOrd c w ↔ loRel (A := A) w :=
      fun w => (le_guessedLinearOrder c w).symm
    have hmem : c ∈ X.ptClsSet c := (ptClsSet_eq_of_refl (X := X) hrefl) ▸ hrefl
    exact (Q.iso_invariant
      (clsEquiv (eq_range_copyIn (isCls_ptClsSet c) hmem hord))).mpr hQ
  · rintro ⟨lo, hQ⟩
    letI := lo
    obtain ⟨u⟩ := (inferInstance : Nonempty (X.Map A))
    refine ⟨copyIn u, ?_⟩
    have hrange : X.ptClsSet (copyIn u) = Set.range (copyIn (X := X) (A := A)) := by
      have hrefl : RelMap X.sameSym ![copyIn u, copyIn u] :=
        (relMap_sameSym ![copyIn u, copyIn u]).mpr fun _ => Iff.rfl
      refine eq_range_copyIn (isCls_ptClsSet (copyIn u)) ?_ (pointOrd_copyIn u)
      exact (ptClsSet_eq_of_refl (X := X) hrefl) ▸ hrefl
    exact (Q.iso_invariant (clsEquiv hrange)).mp hQ

end Correct

end ExpExpansion

/-! ### EXPTIME needs no order -/

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **PTIME over an expanded universe needs no order.** The order is guessed
into the block of the expansion, and the inner problem is replaced by “some copy
answers yes” – the copy being *named by a point*, since a deterministic class
cannot guess one. -/
theorem expDefinable_PTIME_iff_free (P : DecisionProblem L) :
    ExpDefinable PTIME P ↔ ExpDefinableFree PTIME P := by
  constructor
  · rintro ⟨X, Q, hQ, hX⟩
    refine ⟨X.orderFree, X.somePtCls Q, X.mem_PTIME_somePtCls hQ, ?_⟩
    intro A _ _ _
    rw [ExpExpansion.somePtCls_map_iff]
    constructor
    · intro hP
      letI lo := finiteLinearOrder A
      exact ⟨lo, (hX A).mp hP⟩
    · rintro ⟨lo, h⟩
      letI := lo
      exact (hX A).mpr h
  · exact fun h => h.expDefinable

/-- **SO(LFP) without the order**: a least fixed point over a second-order
universe *defined without an order*, the equivalence being asked of structures
carrying none. -/
def SOLFPDefinableFree (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansionFree L) (Q : DecisionProblem X.E), LFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

theorem solfpDefinableFree_iff_expDefinableFree (P : DecisionProblem L) :
    SOLFPDefinableFree P ↔ ExpDefinableFree PTIME P :=
  exists_congr fun _X => exists_congr fun Q =>
    and_congr_left' (lfpDefinable_iff_mem_PTIME Q)

/-- **SO(≤, LFP) = SO(LFP)**: the order of the expansion can be guessed. -/
theorem solfpDefinable_iff_free (P : DecisionProblem L) :
    SOLFPDefinable P ↔ SOLFPDefinableFree P :=
  (solfpDefinable_iff_expDefinable P).trans
    ((expDefinable_PTIME_iff_free P).trans (solfpDefinableFree_iff_expDefinableFree P).symm)

/-- **EXPTIME is SO(LFP), no order needed.** -/
theorem mem_EXPTIME_iff_solfpDefinableFree (P : DecisionProblem L) :
    P ∈ EXPTIME ↔ SOLFPDefinableFree P :=
  (mem_EXPTIME_iff P).trans (solfpDefinable_iff_free P)

end DescriptiveComplexity
