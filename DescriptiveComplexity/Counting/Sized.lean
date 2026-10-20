/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.SharpP
import DescriptiveComplexity.SecondOrderOrdered
import DescriptiveComplexity.Numbers.MonotoneBijection

/-!
# Counting the solutions of exactly the threshold size

A threshold problem in the unary representation asks for a set at least, or at
most, as large as a marked set, and its counting version counts the solutions
of *exactly* that size. Such a count is `#P`-definable as soon as the property
of the set is first-order, and this file says so once for all of them
(`DescriptiveComplexity.sharpPDefinable_of_sized`, and
`DescriptiveComplexity.sharpPDefinable_of_sized_set` when the set is the whole
certificate).

The input is a kernel `φ₀` over a block `B`, one of whose unary variables `i₀`
is the set being sized, and the symbol `mk` of the marked set. The kernel may
read the order (`DescriptiveComplexity.sharpPDefinable_of_sized_ordered`, for a
certificate walking the order, as the reachability clock of Steiner Tree does)
or not (`DescriptiveComplexity.sharpPDefinable_of_sized`).
The counting kernel (`DescriptiveComplexity.sizedKernel`) adds one binary variable and
asks it to be the graph of the *monotone* bijection from the marked set onto
the set (`DescriptiveComplexity.MonoBij`): a bijection certifies the size, and the
monotone one is the only certificate, so the witnesses of the kernel are the
assignments of `B` satisfying `φ₀` whose set has the size of the marked one
(`DescriptiveComplexity.witnessCount_sizedKernel`), whatever the linear order.

The extra variable is that of `DescriptiveComplexity.SOBlock.withOrder`, reused for
its assignment bookkeeping: there it is an order being re-quantified, here a
bijection.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Sized

variable (L : Language.{0, 0}) (B : SOBlock)

/-- The inclusion of the vocabulary of a kernel into that of the sized kernel:
the bijection variable is added to the block. -/
def sizedLHom :
    (L.sum Language.order).sum B.lang →ᴸ (L.sum Language.order).sum B.withOrder.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl g => Sum.inl g
    | Sum.inr g => nomatch g
  onRelation {n} r :=
    match n, r with
    | _, Sum.inl s => Sum.inl s
    | _, Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

variable {A : Type}

/-- The structure of the sized kernel expands that of the kernel. -/
theorem sizedLHom_isExpansionOn (instA : L.Structure A) (lo : LinearOrder A)
    (ρ : B.withOrder.Assignment A) :
    @LHom.IsExpansionOn _ _ (sizedLHom L B) A
      (@sumStructure (L.sum Language.order) B.lang A
        (letI := instA; letI := lo; sumOrderStructure L A)
        (B.structure (B.restPart ρ)))
      (@sumStructure (L.sum Language.order) B.withOrder.lang A
        (letI := instA; letI := lo; sumOrderStructure L A)
        (B.withOrder.structure ρ)) := by
  let := instA
  let := lo
  let := B.structure (B.restPart ρ)
  let := B.withOrder.structure ρ
  exact
    { map_onFunction := fun {n} f x => by
        match f with
        | Sum.inl g => rfl
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {n} r x => by
        match n, r with
        | _, Sum.inl s => rfl
        | _, Sum.inr s => rfl }

variable (mk : L.Relations 1) (i₀ : B.ι) (h₀ : B.arity i₀ = 1)

/-- The mark symbol over the vocabulary of the sized kernel. -/
abbrev szMkSym : ((L.sum Language.order).sum B.withOrder.lang).Relations 1 :=
  Sum.inl (Sum.inl mk)

/-- The sized set, as a symbol of the sized kernel. -/
abbrev szSelSym : ((L.sum Language.order).sum B.withOrder.lang).Relations 1 :=
  Sum.inr ⟨Sum.inr i₀, h₀⟩

/-- The bijection variable, as a symbol of the sized kernel. -/
abbrev szBijSym : ((L.sum Language.order).sum B.withOrder.lang).Relations 2 :=
  Sum.inr B.orderSym

/-- The order symbol over the vocabulary of the sized kernel. -/
abbrev szLeSym : ((L.sum Language.order).sum B.withOrder.lang).Relations 2 :=
  Sum.inl (Sum.inr leSymb)

/-- `x` is marked, as a formula of the sized kernel. -/
private def szMk {α : Type} (x : α) :
    ((L.sum Language.order).sum B.withOrder.lang).Formula α :=
  Relations.formula₁ (szMkSym L B mk) (Term.var x)

/-- `x` belongs to the sized set, as a formula. -/
private def szSel {α : Type} (x : α) :
    ((L.sum Language.order).sum B.withOrder.lang).Formula α :=
  Relations.formula₁ (szSelSym L B i₀ h₀) (Term.var x)

/-- The bijection relates `x` to `y`, as a formula. -/
private def szBij {α : Type} (x y : α) :
    ((L.sum Language.order).sum B.withOrder.lang).Formula α :=
  Relations.formula₂ (szBijSym L B) (Term.var x) (Term.var y)

/-- `x ≤ y`, as a formula of the sized kernel. -/
private def szLe {α : Type} (x y : α) :
    ((L.sum Language.order).sum B.withOrder.lang).Formula α :=
  Relations.formula₂ (szLeSym L B) (Term.var x) (Term.var y)

/-- The extra variable is the graph of a monotone bijection from the marked set
onto the sized set: `DescriptiveComplexity.MonoBij`, as a sentence. -/
noncomputable def monoBijS : ((L.sum Language.order).sum B.withOrder.lang).Sentence :=
  Formula.iAlls (Fin 2)
      (szBij L B (Sum.inr 0) (Sum.inr 1) ⟹
        szMk L B mk (Sum.inr 0) ⊓ szSel L B i₀ h₀ (Sum.inr 1)) ⊓
    (Formula.iAlls (Fin 1)
        (szMk L B mk (Sum.inr 0) ⟹
          (szBij L B (Sum.inl (Sum.inr 0)) (Sum.inr ())).iExs Unit) ⊓
      (Formula.iAlls (Fin 1)
          (szSel L B i₀ h₀ (Sum.inr 0) ⟹
            (szBij L B (Sum.inr ()) (Sum.inl (Sum.inr 0))).iExs Unit) ⊓
        Formula.iAlls (Fin 4)
          (szBij L B (Sum.inr 0) (Sum.inr 2) ⊓ szBij L B (Sum.inr 1) (Sum.inr 3) ⟹
            (szLe L B (Sum.inr 0) (Sum.inr 1)).iff (szLe L B (Sum.inr 2) (Sum.inr 3)))))

/-- Realization of the monotone-bijection sentence. -/
theorem realize_monoBijS (instA : L.Structure A) [LinearOrder A]
    (ρ : B.withOrder.Assignment A) :
    @Sentence.Realize _ A
        (@sumStructure (L.sum Language.order) B.withOrder.lang A _
          (B.withOrder.structure ρ))
        (monoBijS L B mk i₀ h₀) ↔
      MonoBij (fun a : A => RelMap mk ![a]) (fun a => ρ (Sum.inr i₀) fun _ => a)
        fun a b => ρ (Sum.inl ()) ![a, b] := by
  let := B.withOrder.structure ρ
  have hMk : ∀ (w : Fin 1 → A),
      RelMap (L := (L.sum Language.order).sum B.withOrder.lang) (M := A)
        (szMkSym L B mk) w ↔ RelMap mk w := fun _ => Iff.rfl
  have hSel : ∀ (w : Fin 1 → A),
      RelMap (L := (L.sum Language.order).sum B.withOrder.lang) (M := A)
        (szSelSym L B i₀ h₀) w ↔ ρ (Sum.inr i₀) fun _ => w 0 := by
    intro w
    change ρ (Sum.inr i₀) _ ↔ ρ (Sum.inr i₀) _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  have hBij : ∀ (w : Fin 2 → A),
      RelMap (L := (L.sum Language.order).sum B.withOrder.lang) (M := A)
        (szBijSym L B) w ↔ ρ (Sum.inl ()) w := fun _ => Iff.rfl
  have hLe : ∀ (w : Fin 2 → A),
      RelMap (L := (L.sum Language.order).sum B.withOrder.lang) (M := A)
        (szLeSym L B) w ↔ w 0 ≤ w 1 := fun _ => Iff.rfl
  simp only [MonoBij, monoBijS, szMk, szSel, szBij, szLe, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs, Formula.realize_iff,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    hMk, hSel, hBij, hLe, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine and_congr ⟨fun h a b hab => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h a ha => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h b hb => ?_, fun h i hi => ?_⟩
        ⟨fun h a a' b b' hab hab' => ?_, fun h i hi => ?_⟩))
  · exact h ![a, b] hab
  · exact h (i 0) (i 1) hi
  · obtain ⟨b, hb⟩ := h (fun _ => a) ha
    exact ⟨b (), hb⟩
  · obtain ⟨b, hb⟩ := h (i 0) hi
    exact ⟨fun _ => b, hb⟩
  · obtain ⟨a, ha⟩ := h (fun _ => b) hb
    exact ⟨a (), ha⟩
  · obtain ⟨a, ha⟩ := h (i 0) hi
    exact ⟨fun _ => a, ha⟩
  · exact h ![a, a', b, b'] ⟨hab, hab'⟩
  · exact h (i 0) (i 1) (i 2) (i 3) hi.1 hi.2

variable (φ₀ : ((L.sum Language.order).sum B.lang).Sentence)

/-- **The sized kernel**: the kernel `φ₀`, which may read the order, and the
extra variable is the monotone bijection from the marked set onto the set
`i₀`. -/
noncomputable def sizedKernel : ((L.sum Language.order).sum B.withOrder.lang).Sentence :=
  (sizedLHom L B).onSentence φ₀ ⊓ monoBijS L B mk i₀ h₀

/-- Realization of the sized kernel. -/
theorem realize_sizedKernel (instA : L.Structure A) [LinearOrder A]
    (ρ : B.withOrder.Assignment A) :
    @Sentence.Realize _ A
        (@sumStructure (L.sum Language.order) B.withOrder.lang A _
          (B.withOrder.structure ρ))
        (sizedKernel L B mk i₀ h₀ φ₀) ↔
      @Sentence.Realize ((L.sum Language.order).sum B.lang) A
          (@sumStructure (L.sum Language.order) B.lang A _ (B.structure (B.restPart ρ))) φ₀ ∧
        MonoBij (fun a : A => RelMap mk ![a]) (fun a => ρ (Sum.inr i₀) fun _ => a)
          fun a b => ρ (Sum.inl ()) ![a, b] := by
  have hmono := realize_monoBijS L B mk i₀ h₀ instA ρ
  have hexp := sizedLHom_isExpansionOn L B instA inferInstance ρ
  let := B.structure (B.restPart ρ)
  let := B.withOrder.structure ρ
  rw [sizedKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr (LHom.realize_onSentence A (sizedLHom L B) φ₀) hmono

/-- **The witnesses of the sized kernel** are the assignments of the block
satisfying the kernel whose set has exactly the size of the marked set,
bijectively. -/
theorem witnessCount_sizedKernel [instA : L.Structure A] [LinearOrder A] [Finite A] :
    witnessCount B.withOrder (sizedKernel L B mk i₀ h₀ φ₀) A =
      Nat.card {ρ₀ : B.Assignment A //
        @Sentence.Realize ((L.sum Language.order).sum B.lang) A
            (@sumStructure (L.sum Language.order) B.lang A _ (B.structure ρ₀)) φ₀ ∧
          {a | ρ₀ i₀ fun _ => a}.ncard = {a : A | RelMap mk ![a]}.ncard} := by
  refine Nat.card_congr
    { toFun := fun ρ => ⟨B.restPart ρ.1,
        ((realize_sizedKernel L B mk i₀ h₀ φ₀ instA ρ.1).mp ρ.2).1,
        ((realize_sizedKernel L B mk i₀ h₀ φ₀ instA ρ.1).mp ρ.2).2.ncard_eq⟩
      invFun := fun ρ₀ =>
        ⟨B.joinOrder (fun w => (exists_monoBij ρ₀.2.2).choose (w 0) (w 1)) ρ₀.1,
          (realize_sizedKernel L B mk i₀ h₀ φ₀ instA _).mpr
            ⟨ρ₀.2.1, (exists_monoBij ρ₀.2.2).choose_spec⟩⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  rintro ⟨ρ, hρ⟩
  have hr := (realize_sizedKernel L B mk i₀ h₀ φ₀ instA ρ).mp hρ
  have hF := (exists_monoBij hr.2.ncard_eq).choose_spec.ext hr.2
  refine Subtype.ext (funext fun p => ?_)
  cases p with
  | inl u =>
    refine funext fun (w : Fin 2 → A) => ?_
    exact (congrFun (congrFun hF (w 0)) (w 1)).trans
      (congrArg (ρ (Sum.inl ())) (funext fun k => by fin_cases k <;> rfl))
  | inr i => rfl

end Sized

/-- **A count of the solutions of exactly the threshold size is
`#P`-definable**, when the property of the solution is first-order over the
ordered expansion: the size is certified by the monotone bijection with the
marked set, the one certificate a linear order offers. The kernel may read the
order, and then has to define the same count whatever the order. -/
theorem sharpPDefinable_of_sized_ordered {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) (B : SOBlock) (mk : L.Relations 1) (i₀ : B.ι)
    (h₀ : B.arity i₀ = 1) (φ₀ : ((L.sum Language.order).sum B.lang).Sentence)
    (hC : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A],
      C A = Nat.card {ρ₀ : B.Assignment A //
        @Sentence.Realize ((L.sum Language.order).sum B.lang) A
            (@sumStructure (L.sum Language.order) B.lang A _ (B.structure ρ₀)) φ₀ ∧
          {a | ρ₀ i₀ fun _ => a}.ncard = {a : A | RelMap mk ![a]}.ncard}) :
    SharpPDefinable C :=
  ⟨B.withOrder, sizedKernel L B mk i₀ h₀ φ₀, fun A _ _ _ _ =>
    (hC A).trans (witnessCount_sizedKernel L B mk i₀ h₀ φ₀).symm⟩

/-- An order-free kernel, lifted to the ordered expansion, holds exactly when
it did. -/
theorem realize_orderFreeKernel {L : Language.{0, 0}} (B : SOBlock)
    (φ₀ : (L.sum B.lang).Sentence) {A : Type} [instA : L.Structure A] [LinearOrder A]
    (ρ₀ : B.Assignment A) :
    @Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure (L.sum Language.order) B.lang A _ (B.structure ρ₀))
        (orderFreeKernel B φ₀) ↔
      @Sentence.Realize (L.sum B.lang) A
        (@sumStructure L B.lang A instA (B.structure ρ₀)) φ₀ := by
  let := B.structure ρ₀
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
      (LHom.id B.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  exact LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
    (LHom.id B.lang)) φ₀

/-- **A count of the solutions of exactly the threshold size is
`#P`-definable**, when the property of the solution is first-order: the case of
`DescriptiveComplexity.sharpPDefinable_of_sized_ordered` where the kernel does not read
the order. -/
theorem sharpPDefinable_of_sized {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) (B : SOBlock) (mk : L.Relations 1) (i₀ : B.ι)
    (h₀ : B.arity i₀ = 1) (φ₀ : (L.sum B.lang).Sentence)
    (hC : ∀ (A : Type) [instA : L.Structure A] [Finite A],
      C A = Nat.card {ρ₀ : B.Assignment A //
        @Sentence.Realize (L.sum B.lang) A
            (@sumStructure L B.lang A instA (B.structure ρ₀)) φ₀ ∧
          {a | ρ₀ i₀ fun _ => a}.ncard = {a : A | RelMap mk ![a]}.ncard}) :
    SharpPDefinable C :=
  sharpPDefinable_of_sized_ordered C B mk i₀ h₀ (orderFreeKernel B φ₀) fun A _ _ _ =>
    (hC A).trans (Nat.card_congr (Equiv.subtypeEquivRight fun ρ₀ =>
      and_congr (realize_orderFreeKernel B φ₀ ρ₀).symm Iff.rfl))

/-- A set no larger than a number no larger than the universe extends to a set
of exactly that size: what makes the support of an exact-size count of
*upward closed* solutions the “at most” decision problem. -/
theorem exists_superset_ncard_eq {A : Type} [Finite A] {s : Set A} {k : ℕ}
    (hs : s.ncard ≤ k) (hk : k ≤ Nat.card A) : ∃ t : Set A, s ⊆ t ∧ t.ncard = k := by
  have hcompl := Set.ncard_add_ncard_compl s
  obtain ⟨T, hT, hTcard⟩ := Set.exists_subset_card_eq (s := sᶜ) (n := k - s.ncard) (by omega)
  refine ⟨s ∪ T, Set.subset_union_left, ?_⟩
  rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun v hv hvT => hT hvT hv), hTcard]
  omega

/-- Sets, as the assignments of a block whose only variable is unary. -/
def unaryAssignEquiv (B : SOBlock) [Subsingleton B.ι] (i₀ : B.ι) (h₀ : B.arity i₀ = 1)
    (A : Type) : (A → Prop) ≃ B.Assignment A where
  toFun S := fun i w => S (w ⟨0, by rw [Subsingleton.elim i i₀, h₀]; exact Nat.one_pos⟩)
  invFun ρ := fun a => ρ i₀ fun _ => a
  left_inv _ := rfl
  right_inv ρ := by
    funext i w
    obtain rfl := Subsingleton.elim i₀ i
    exact congrArg (ρ i₀) (funext fun j => congrArg w (Fin.ext (by omega)))

/-- `DescriptiveComplexity.sharpPDefinable_of_sized` for a block with a single
variable, the solution itself: a count of the sets with a first-order property
and exactly the size of the marked set is `#P`-definable. -/
theorem sharpPDefinable_of_sized_set {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) (B : SOBlock) [Subsingleton B.ι] (mk : L.Relations 1)
    (i₀ : B.ι) (h₀ : B.arity i₀ = 1) (φ₀ : (L.sum B.lang).Sentence)
    (P : ∀ (A : Type) [L.Structure A], (A → Prop) → Prop)
    (hφ : ∀ (A : Type) [instA : L.Structure A] (ρ₀ : B.Assignment A),
      @Sentence.Realize (L.sum B.lang) A
          (@sumStructure L B.lang A instA (B.structure ρ₀)) φ₀ ↔
        P A fun a => ρ₀ i₀ fun _ => a)
    (hC : ∀ (A : Type) [L.Structure A] [Finite A],
      C A = Nat.card {S : A → Prop //
        P A S ∧ {a | S a}.ncard = {a : A | RelMap mk ![a]}.ncard}) :
    SharpPDefinable C :=
  sharpPDefinable_of_sized C B mk i₀ h₀ φ₀ fun A _ _ =>
    (hC A).trans (Nat.card_congr (Equiv.subtypeEquiv (unaryAssignEquiv B i₀ h₀ A)
      fun S => and_congr (hφ A (unaryAssignEquiv B i₀ h₀ A S)).symm Iff.rfl))

end DescriptiveComplexity
