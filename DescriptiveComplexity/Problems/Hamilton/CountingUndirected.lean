/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.CircuitPerm

/-!
# #Hamilton Circuit: counting the circuits of an undirected graph

The counting version of `DescriptiveComplexity.HamCircuit`: the number of Hamilton
circuits of a graph, a circuit being its **set of edges**
(`DescriptiveComplexity.IsUCircuit`) – the symmetric relation “`x` and `y` are
consecutive” – and not one of its two orientations.

## Membership

The certificate is still a linear order, and a circuit has `2n` of them: `n`
places to cut it and two directions to read it. The counting kernel
(`DescriptiveComplexity.sharpHamKernel`) fixes both: the order starts at the least
element of the instance, as for the directed problem, and of the two
neighbours of that element on the circuit it goes first to the smaller one
(`DescriptiveComplexity.Oriented`). Every circuit has exactly one such order: one
exists because reversing an order reverses its cyclic successor
(`DescriptiveComplexity.cycSucc_reverse`), and two of them with the same edges agree
at the root by the orientation rule, hence everywhere, by induction along the
circuit (`DescriptiveComplexity.cycSucc_of_sym`). Hence
`DescriptiveComplexity.sharpHamCircuit_mem_sharpP`.

Parsimonious hardness is in
`DescriptiveComplexity.Problems.Hamilton.CountingUndirectedHardness`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section UCircuit

variable {A : Type}

/-- The relation `E` is the edge set of a Hamilton circuit of `R`: the
symmetric closure of a circuit of `R`. -/
def IsUCircuit (R : A → A → Prop) (E : A → A → Prop) : Prop :=
  ∃ Nxt : A → A → Prop, IsCircuit R Nxt ∧ ∀ x y, E x y ↔ (Nxt x y ∨ Nxt y x)

/-- A relation has a tour iff it has an undirected circuit. -/
theorem tourOn_iff_exists_ucircuit {R : A → A → Prop} :
    TourOn R ↔ ∃ E, IsUCircuit R E := by
  rw [tourOn_iff_exists_circuit]
  exact ⟨fun ⟨Nxt, h⟩ => ⟨_, Nxt, h, fun _ _ => Iff.rfl⟩, fun ⟨_, Nxt, h, _⟩ => ⟨Nxt, h⟩⟩

variable {B : Type}

/-- Undirected circuits transport along an equivalence commuting with the
relations. -/
theorem IsUCircuit.of_equiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) {E : A → A → Prop} (h : IsUCircuit RA E) :
    IsUCircuit RB fun b b' => E (u.symm b) (u.symm b') := by
  obtain ⟨Nxt, hN, hE⟩ := h
  exact ⟨_, hN.of_equiv u hR, fun b b' => hE _ _⟩

/-- The undirected circuits of two relations an equivalence exchanges are in
bijection. -/
def ucircuitEquiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) :
    {E : A → A → Prop // Finite A ∧ IsUCircuit RA E} ≃
      {E : B → B → Prop // Finite B ∧ IsUCircuit RB E} where
  toFun N := ⟨fun b b' => N.1 (u.symm b) (u.symm b'), u.finite_iff.mp N.2.1,
    N.2.2.of_equiv u hR⟩
  invFun T := ⟨fun a a' => T.1 (u a) (u a'), u.finite_iff.mpr T.2.1, by
    have h := T.2.2.of_equiv u.symm (RB := RA) fun b b' => by
      rw [hR]
      simp
    simpa using h⟩
  left_inv N := Subtype.ext (funext fun a => funext fun a' => by simp)
  right_inv T := Subtype.ext (funext fun b => funext fun b' => by simp)

/-! ### One order per undirected circuit -/

/-- The orientation rule: from the least element, the circuit goes first to the
smaller of its two neighbours. -/
def Oriented [LE A] (C : A → A → Prop) : Prop :=
  ∀ x y z, IsBot x → C x y → C z x → y ≤ z

variable [LinearOrder A] [Finite A]

/-- **Two oriented cuts with the same edges have the same cyclic successor.** -/
theorem cycSucc_of_sym {Le Le' : A → A → Prop} (h : IsLinOrd Le) (h' : IsLinOrd Le') {a₀ : A}
    (ha₀ : IsBot a₀)
    (hsym : ∀ x y, (CycSucc Le x y ∨ CycSucc Le y x) ↔ (CycSucc Le' x y ∨ CycSucc Le' y x))
    (ho : Oriented (CycSucc Le)) (ho' : Oriented (CycSucc Le')) :
    ∀ x y, CycSucc Le x y → CycSucc Le' x y := by
  have hc : IsCircuit (fun _ _ : A => True) (CycSucc Le) :=
    ⟨Le, h, fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
  have hc' : IsCircuit (fun _ _ : A => True) (CycSucc Le') :=
    ⟨Le', h', fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
  obtain ⟨-, hfun, -, hinj, -, -⟩ := hc.local
  obtain ⟨htot', -, -, hinj', -, -⟩ := hc'.local
  refine hc.induction (P := fun x => ∀ y, CycSucc Le x y → CycSucc Le' x y) a₀ ?_ ?_
  · intro w hw
    rcases (hsym a₀ w).mp (Or.inl hw) with h₁ | h₁
    · exact h₁
    · obtain ⟨z', hz'⟩ := htot' a₀
      rcases (hsym a₀ z').mpr (Or.inl hz') with h₂ | h₂
      · rw [hfun _ _ _ hw h₂]
        exact hz'
      · rw [le_antisymm (ho a₀ w z' ha₀ hw h₂) (ho' a₀ z' w ha₀ hz' h₁)]
        exact hz'
  · intro x y hxy hP w hw
    have hxy' := hP y hxy
    rcases (hsym y w).mp (Or.inl hw) with h₁ | h₁
    · exact h₁
    · have hwx : w = x := hinj' _ _ _ h₁ hxy'
      subst hwx
      obtain ⟨w', hw'⟩ := htot' y
      rcases (hsym y w').mpr (Or.inl hw') with h₂ | h₂
      · rw [hfun _ _ _ hw h₂]
        exact hw'
      · rw [← hinj _ _ _ h₂ hxy]
        exact hw'

/-- **Undirected circuits are the oriented orders that start at the least
element**, bijectively. -/
theorem card_orientedTour_eq [Nonempty A] (R : A → A → Prop) (hRsym : ∀ x y, R x y → R y x) :
    Nat.card {Le : A → A → Prop // IsLinOrd Le ∧ (∀ x y, SuccOf Le x y → R x y) ∧
        (∀ x y, (∀ z, Le x z) → (∀ z, Le z y) → R y x) ∧
        (∀ x : A, IsBot x → ∀ y, Le x y) ∧ Oriented (CycSucc Le)} =
      Nat.card {E : A → A → Prop // IsUCircuit R E} := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have hbot : ∀ x : A, IsBot x → x = a₀ := fun x hx => le_antisymm (hx a₀) (ha₀ x)
  refine Nat.card_congr (Equiv.ofBijective
    (fun Le => ⟨fun x y => CycSucc Le.1 x y ∨ CycSucc Le.1 y x, CycSucc Le.1,
      ⟨Le.1, Le.2.1, fun _ _ => Iff.rfl,
        fun x y h => h.elim (Le.2.2.1 x y) fun ⟨hmax, hmin⟩ => Le.2.2.2.1 y x hmin hmax⟩,
      fun _ _ => Iff.rfl⟩)
    ⟨?_, ?_⟩)
  · intro L L' hval
    have hrel : ∀ x y, (CycSucc L.1 x y ∨ CycSucc L.1 y x) ↔
        (CycSucc L'.1 x y ∨ CycSucc L'.1 y x) := fun x y =>
      iff_of_eq (congrFun (congrFun (congrArg Subtype.val hval) x) y)
    exact Subtype.ext (linOrd_eq_of_cycSucc L.2.1 L'.2.1 (L.2.2.2.2.1 a₀ ha₀)
      (L'.2.2.2.2.1 a₀ ha₀) fun x y =>
        ⟨cycSucc_of_sym L.2.1 L'.2.1 ha₀ hrel L.2.2.2.2.2 L'.2.2.2.2.2 x y,
          cycSucc_of_sym L'.2.1 L.2.1 ha₀ (fun x y => (hrel x y).symm) L'.2.2.2.2.2
            L.2.2.2.2.2 x y⟩)
  · rintro ⟨E, Nxt, ⟨Le₀, h₀, hiff, hR⟩, hE⟩
    obtain ⟨Le₁, hlin₁, hmin₁, hcyc₁⟩ := exists_rooted_order h₀ a₀
    have hC₁ : ∀ x y, CycSucc Le₁ x y ↔ Nxt x y := fun x y =>
      (hcyc₁ x y).trans (hiff x y).symm
    by_cases hor : Oriented (CycSucc Le₁)
    · refine ⟨⟨Le₁, hlin₁, fun x y h => hR _ _ ((hC₁ _ _).mp (Or.inl h)),
        fun x y hx hy => hR _ _ ((hC₁ _ _).mp (Or.inr ⟨hy, hx⟩)),
        fun x hx y => hbot x hx ▸ hmin₁ y, hor⟩, Subtype.ext (funext fun x => funext fun y =>
          propext ((or_congr (hC₁ x y) (hC₁ y x)).trans (hE x y).symm))⟩
    · obtain ⟨Le₂, hlin₂, hmin₂, hcyc₂⟩ := exists_rooted_order hlin₁.reverse a₀
      have hC₂ : ∀ x y, CycSucc Le₂ x y ↔ Nxt y x := fun x y =>
        (hcyc₂ x y).trans (cycSucc_reverse.trans (hC₁ y x))
      have hc₁ : IsCircuit (fun _ _ : A => True) (CycSucc Le₁) :=
        ⟨Le₁, hlin₁, fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
      obtain ⟨-, hfun, -, hinj, -, -⟩ := hc₁.local
      have hor₂ : Oriented (CycSucc Le₂) := by
        unfold Oriented at hor
        push Not at hor
        obtain ⟨x, y, z, hx, hxy, hzx, hnot⟩ := hor
        intro x' y' z' hx' h₁ h₂
        rw [hbot x' hx'] at h₁ h₂
        rw [hbot x hx] at hxy hzx
        have e₁ : y' = z := hinj _ _ _ ((hC₁ _ _).mpr ((hC₂ _ _).mp h₁)) hzx
        have e₂ : z' = y := hfun _ _ _ ((hC₁ _ _).mpr ((hC₂ _ _).mp h₂)) hxy
        rw [e₁, e₂]
        exact le_of_lt hnot
      refine ⟨⟨Le₂, hlin₂, fun x y h => hRsym _ _ (hR _ _ ((hC₂ _ _).mp (Or.inl h))),
        fun x y hx hy => hRsym _ _ (hR _ _ ((hC₂ _ _).mp (Or.inr ⟨hy, hx⟩))),
        fun x hx y => hbot x hx ▸ hmin₂ y, hor₂⟩, Subtype.ext (funext fun x => funext fun y =>
          propext (((or_congr (hC₂ x y) (hC₂ y x)).trans or_comm).trans (hE x y).symm))⟩

end UCircuit

/-! ### The counting problem -/

section Problem

variable (A : Type) [Language.digraph.Structure A]

/-- The relation `E` is the edge set of a Hamilton circuit of a finite
graph. -/
def UCircuit (E : A → A → Prop) : Prop :=
  Finite A ∧ IsUCircuit (fun x y : A => DGEdge x y) E

end Problem

/-- **#Hamilton Circuit**: the number of Hamilton circuits of a graph, a
circuit being its set of edges. -/
noncomputable def SharpHamCircuit : CountingProblem Language.digraph where
  Count := fun A inst => Nat.card {E : A → A → Prop // @UCircuit A inst E}
  iso_invariant := fun e => Nat.card_congr
    (ucircuitEquiv e.toEquiv fun a a' =>
      or_congr (relMap_equiv₂ e dgArc a a') (relMap_equiv₂ e dgArc a' a))

theorem sharpHamCircuit_apply (A : Type) [Language.digraph.Structure A] :
    SharpHamCircuit A = Nat.card {E : A → A → Prop // UCircuit A E} :=
  rfl

/-- **The support of #Hamilton Circuit is Hamilton Circuit.** -/
theorem sharpHamCircuit_support_iff (A : Type) [Language.digraph.Structure A] [Finite A] :
    SharpHamCircuit.support A ↔ HamCircuit A := by
  rw [CountingProblem.support_iff, sharpHamCircuit_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨E, hfin, hE⟩, -⟩
    exact ⟨hfin, tourOn_iff_exists_ucircuit.mpr ⟨E, hE⟩⟩
  · rintro ⟨hfin, h⟩
    obtain ⟨E, hE⟩ := tourOn_iff_exists_ucircuit.mp h
    exact ⟨⟨⟨E, hfin, hE⟩⟩, inferInstance⟩

/-! ### Membership -/

/-- The cyclic successor of the guessed order, as a formula. -/
noncomputable def cycF {α : Type} (x y : α) : dhcLang.Formula α :=
  fo%[x, y] ((dhcVarSym(x, y) ∧ ¬ x ≐ y) ∧
      (∀ w, dhcVarSym(x, w) ∧ dhcVarSym(w, y) → w ≐ x ∨ w ≐ y)) ∨
    ((∀ w, dhcVarSym(w, x)) ∧ (∀ w, dhcVarSym(y, w)))

/-- Kernel conjunct: the guessed order is oriented. -/
noncomputable def hamOrientClause : dhcLang.Sentence :=
  fo% ∀ x y z, ((∀ w, dhcOrdSym(x, w)) ∧ cycF⟨x, y⟩) ∧ cycF⟨z, x⟩ → dhcOrdSym(y, z)

/-- The first-order kernel of #Hamilton Circuit: the guessed relation is a
linear order carrying a tour of the edges, it starts at the least element of
the instance, and it is oriented. -/
noncomputable def sharpHamKernel : dhcLang.Sentence :=
  rootedHamKernel false ⊓ hamOrientClause

section Kernel

variable {A : Type} [Language.digraph.Structure A] [LinearOrder A]

theorem realize_cycF (ρ : hamGuessBlock.Assignment A) {α : Type} (v : α → A) (x y : α) :
    (@Formula.Realize dhcLang A (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) _
        (cycF x y) v) ↔ CycSucc (fun a b : A => ρ .le ![a, b]) (v x) (v y) := by
  let := hamGuessBlock.structure ρ
  have hVar : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcVarSym w ↔ ρ .le w :=
    fun _ => Iff.rfl
  simp only [cycF, CycSucc, SuccOf, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_not, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_equal,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr, hVar]
  exact or_congr
    ⟨fun h => ⟨h.1.1, h.1.2, fun z h₁ h₂ => h.2 (fun _ => z) ⟨h₁, h₂⟩⟩,
      fun h => ⟨⟨h.1, h.2.1⟩, fun i hi => h.2.2 (i 0) hi.1 hi.2⟩⟩
    (and_congr ⟨fun h z => h fun _ => z, fun h i => h (i 0)⟩
      ⟨fun h z => h fun _ => z, fun h i => h (i 0)⟩)

/-- Realization of the kernel of #Hamilton Circuit. -/
theorem realize_sharpHamKernel (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize dhcLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) sharpHamKernel) ↔
      IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, SuccOf (fun x y : A => ρ .le ![x, y]) x y → DGEdge x y) ∧
        (∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) → DGEdge y x) ∧
        (∀ x : A, IsBot x → ∀ y, ρ .le ![x, y]) ∧
        Oriented (CycSucc fun x y : A => ρ .le ![x, y]) := by
  have hroot := realize_rootedHamKernel false ρ
  simp only [Bool.false_eq_true, ↓reduceIte] at hroot
  let := hamGuessBlock.structure ρ
  have hOrd : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcOrdSym w ↔ w 0 ≤ w 1 :=
    fun _ => Iff.rfl
  have horient : (@Sentence.Realize dhcLang A _ hamOrientClause) ↔
      Oriented (CycSucc fun x y : A => ρ .le ![x, y]) := by
    simp only [hamOrientClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_inf, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
      hOrd, realize_cycF ρ, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h x y z hx h₁ h₂ => h ![x, y, z] ⟨⟨fun w => hx (w 0), h₁⟩, h₂⟩,
      fun h i hi => h (i 0) (i 1) (i 2) (fun z => hi.1.1 fun _ => z) hi.1.2 hi.2⟩
  rw [sharpHamKernel, Sentence.Realize, Formula.realize_inf]
  rw [← and_assoc, ← and_assoc, ← and_assoc]
  refine and_congr (hroot.trans ?_) horient
  rw [and_assoc, and_assoc]

end Kernel

/-- **#Hamilton Circuit is in `#P`**: a circuit has exactly one oriented cut at
the least element of the instance. -/
theorem sharpHamCircuit_mem_sharpP : SharpHamCircuit ∈ SharpP := by
  refine ⟨hamGuessBlock, sharpHamKernel, fun A _ _ hfin _ => ?_⟩
  rw [sharpHamCircuit_apply]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)).trans
    ((card_orientedTour_eq (fun x y : A => DGEdge x y) fun x y h => h.symm).symm.trans
      (Nat.card_congr (Equiv.subtypeEquiv (hamAssignEquiv A)
        fun ρ => (realize_sharpHamKernel ρ))).symm)

end DescriptiveComplexity
