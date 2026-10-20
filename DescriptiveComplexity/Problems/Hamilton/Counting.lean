/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Cycle
import DescriptiveComplexity.Problems.Hamilton.Membership
import DescriptiveComplexity.Counting.Class

/-!
# #Directed Hamilton Circuit: counting the circuits

The counting version of `DescriptiveComplexity.DirHamCircuit`: the number of
Hamilton circuits of a digraph.

## What is counted

The decision problem reads a circuit as a linear order of the universe
(`DescriptiveComplexity.TourOn`), the circuit cut open at one place. A count of those
orders is not a count of circuits: a circuit through `n` vertices can be cut at
`n` places. What is counted here is the circuit itself, as the relation
“`y` comes next after `x`” (`DescriptiveComplexity.IsCircuit`): the cyclic successor
relation of some linear order (`DescriptiveComplexity.CycSucc`), following the arcs.
Its support is the decision problem
(`DescriptiveComplexity.sharpDirHamCircuit_support_iff`).

## Membership

A circuit has no first-order certificate of its own, so the counting kernel
(`DescriptiveComplexity.sharpDirHamKernel`) still guesses an order – but the one that
starts at the least element of the instance: every circuit has exactly one
(`DescriptiveComplexity.exists_rooted_order`, `DescriptiveComplexity.linOrd_eq_of_cycSucc`).
Hence `DescriptiveComplexity.sharpDirHamCircuit_mem_sharpP`. Parsimonious hardness is
in `DescriptiveComplexity.Problems.Hamilton.CountingHardness`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Circuits -/

section Circuit

variable {A : Type}

/-- `y` comes next after `x` on the circuit a linear order is a cut of: it is
the immediate successor of `x`, or `x` is the last element and `y` the
first. -/
def CycSucc (Le : A → A → Prop) (x y : A) : Prop :=
  SuccOf Le x y ∨ ((∀ z, Le z x) ∧ ∀ z, Le y z)

/-- The cyclic successor along an increasing enumeration is the next index. -/
theorem cycSucc_iff {Le : A → A → Prop} {n : ℕ} (f : Fin n ≃ A)
    (hmono : ∀ j k : Fin n, Le (f j) (f k) ↔ j ≤ k) (x y : A) :
    CycSucc Le x y ↔ y = f (nextIdx (f.symm x)) := by
  constructor
  · intro h
    have hLe : Le = fun x y => f.symm x ≤ f.symm y := by
      funext a b
      have h' := hmono (f.symm a) (f.symm b)
      simp only [Equiv.apply_symm_apply] at h'
      exact propext h'
    subst hLe
    have ht := tour_of_enum (R := fun a b => b = f (nextIdx (f.symm a))) f (fun i => by simp)
    rcases h with h | ⟨hmax, hmin⟩
    · exact ht.2.1 x y h
    · exact ht.2.2 y x hmin hmax
  · rintro rfl
    have h := enum_of_mono (R := CycSucc Le) f hmono (fun _ _ h => Or.inl h)
      (fun a b ha hb => Or.inr ⟨hb, ha⟩) (f.symm x)
    simpa using h

/-- The relation `Nxt` is a Hamilton circuit of `R`: the cyclic successor
relation of a linear order of the universe, included in `R`. -/
def IsCircuit (R : A → A → Prop) (Nxt : A → A → Prop) : Prop :=
  ∃ Le : A → A → Prop, IsLinOrd Le ∧ (∀ x y, Nxt x y ↔ CycSucc Le x y) ∧
    ∀ x y, Nxt x y → R x y

/-- A relation has a tour iff it has a circuit. -/
theorem tourOn_iff_exists_circuit {R : A → A → Prop} :
    TourOn R ↔ ∃ Nxt, IsCircuit R Nxt := by
  constructor
  · rintro ⟨Le, hlin, hs, hw⟩
    exact ⟨CycSucc Le, Le, hlin, fun _ _ => Iff.rfl,
      fun x y h => h.elim (hs x y) fun ⟨hmax, hmin⟩ => hw y x hmin hmax⟩
  · rintro ⟨Nxt, Le, hlin, hiff, hR⟩
    exact ⟨Le, hlin, fun x y h => hR x y ((hiff x y).mpr (Or.inl h)),
      fun x y hx hy => hR y x ((hiff y x).mpr (Or.inr ⟨hy, hx⟩))⟩

variable {B : Type}

/-- Circuits transport along an equivalence commuting with the relations. -/
theorem IsCircuit.of_equiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) {Nxt : A → A → Prop} (h : IsCircuit RA Nxt) :
    IsCircuit RB fun b b' => Nxt (u.symm b) (u.symm b') := by
  obtain ⟨Le, hlin, hiff, hNR⟩ := h
  refine ⟨fun b b' => Le (u.symm b) (u.symm b'),
    IsLinOrd.of_equiv u (fun a a' => by simp) hlin, fun b b' => ?_, fun b b' hb => ?_⟩
  · refine (hiff _ _).trans (or_congr ?_ (and_congr ?_ ?_))
    · have h' := succOf_equiv u (Le := Le) (x := u.symm b) (y := u.symm b')
      simp only [Equiv.apply_symm_apply] at h'
      exact h'.symm
    · exact ⟨fun h z => h _, fun h z => by simpa using h (u z)⟩
    · exact ⟨fun h z => h _, fun h z => by simpa using h (u z)⟩
  · have h' := (hR _ _).mp (hNR _ _ hb)
    simpa using h'

/-- The circuits of two relations an equivalence exchanges are in bijection. -/
def circuitEquiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) :
    {Nxt : A → A → Prop // Finite A ∧ IsCircuit RA Nxt} ≃
      {Nxt : B → B → Prop // Finite B ∧ IsCircuit RB Nxt} where
  toFun N := ⟨fun b b' => N.1 (u.symm b) (u.symm b'), u.finite_iff.mp N.2.1,
    N.2.2.of_equiv u hR⟩
  invFun T := ⟨fun a a' => T.1 (u a) (u a'), u.finite_iff.mpr T.2.1, by
    have h := T.2.2.of_equiv u.symm (RB := RA) fun b b' => by
      rw [hR]
      simp
    simpa using h⟩
  left_inv N := Subtype.ext (funext fun a => funext fun a' => by simp)
  right_inv T := Subtype.ext (funext fun b => funext fun b' => by simp)

/-! ### One order per circuit -/

variable [Finite A]

/-- **Two cuts of the same circuit at the same place are the same order.** -/
theorem linOrd_eq_of_cycSucc {Le Le' : A → A → Prop} (h : IsLinOrd Le) (h' : IsLinOrd Le')
    {a₀ : A} (hmin : ∀ y, Le a₀ y) (hmin' : ∀ y, Le' a₀ y)
    (hc : ∀ x y, CycSucc Le x y ↔ CycSucc Le' x y) : Le = Le' := by
  obtain ⟨f, hf⟩ := exists_mono_enum h
  obtain ⟨g, hg⟩ := exists_mono_enum h'
  have hzero : ∀ {Le : A → A → Prop} (_ : IsLinOrd Le) (_ : ∀ y, Le a₀ y)
      (f : Fin (Nat.card A) ≃ A) (_ : ∀ j k : Fin (Nat.card A), Le (f j) (f k) ↔ j ≤ k)
      (hk : 0 < Nat.card A), f ⟨0, hk⟩ = a₀ := by
    intro Le hlin hmin f hf hk
    have h₁ : Le (f ⟨0, hk⟩) a₀ := by
      have h₂ := (hf ⟨0, hk⟩ (f.symm a₀)).mpr (Fin.mk_le_of_le_val (Nat.zero_le _))
      simpa using h₂
    exact hlin.2.2.1 _ _ h₁ (hmin _)
  have key : ∀ (k : ℕ) (hk : k < Nat.card A), f ⟨k, hk⟩ = g ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => exact fun hk => (hzero h hmin f hf hk).trans (hzero h' hmin' g hg hk).symm
    | succ k ih =>
      intro hk
      have hk' : k < Nat.card A := by omega
      have e := ih hk'
      have hnext : nextIdx (⟨k, hk'⟩ : Fin (Nat.card A)) = ⟨k + 1, hk⟩ :=
        Fin.ext (nextIdx_of_lt (i := ⟨k, hk'⟩) hk)
      have c₁ := (cycSucc_iff f hf (f ⟨k, hk'⟩) (f (nextIdx ⟨k, hk'⟩))).mpr (by simp)
      have c₂ := (cycSucc_iff g hg _ _).mp ((hc _ _).mp c₁)
      rw [e, Equiv.symm_apply_apply, hnext] at c₂
      exact c₂
  have hfg : f = g := Equiv.ext fun i => key i.1 i.2
  funext x y
  apply propext
  have a := hf (f.symm x) (f.symm y)
  have b := hg (g.symm x) (g.symm y)
  simp only [Equiv.apply_symm_apply] at a b
  rw [a, b, hfg]

/-- **A circuit can be cut anywhere**: every order has a rotation starting at a
given element, with the same cyclic successor. -/
theorem exists_rooted_order {Le₀ : A → A → Prop} (h₀ : IsLinOrd Le₀) (a₀ : A) :
    ∃ Le : A → A → Prop, IsLinOrd Le ∧ (∀ y, Le a₀ y) ∧
      ∀ x y, CycSucc Le x y ↔ CycSucc Le₀ x y := by
  obtain ⟨g, hg⟩ := exists_mono_enum h₀
  have hn : 0 < Nat.card A := (g.symm a₀).pos
  let ν : A → A := fun x => g (nextIdx (g.symm x))
  have hiter : ∀ (i : ℕ) (x : A),
      ((g.symm (ν^[i] x) : Fin (Nat.card A)) : ℕ) = ((g.symm x : ℕ) + i) % Nat.card A := by
    intro i
    induction i with
    | zero =>
      intro x
      simp [Nat.mod_eq_of_lt (g.symm x).isLt]
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply']
      have hν : g.symm (ν (ν^[i] x)) = nextIdx (g.symm (ν^[i] x)) := by simp [ν]
      rw [hν]
      change ((g.symm (ν^[i] x) : ℕ) + 1) % Nat.card A = _
      rw [ih x, Nat.mod_add_mod, Nat.add_assoc]
  let F : Fin (Nat.card A) → A := fun i => ν^[i] a₀
  have hinj : Function.Injective F := by
    intro i j hij
    have h₁ := hiter i a₀
    have h₂ := hiter j a₀
    have hij' : ν^[(i : ℕ)] a₀ = ν^[(j : ℕ)] a₀ := hij
    rw [hij'] at h₁
    have hmod : ((g.symm a₀ : ℕ) + i) % Nat.card A = ((g.symm a₀ : ℕ) + j) % Nat.card A :=
      h₁.symm.trans h₂
    have hmod' : (i : ℕ) % Nat.card A = (j : ℕ) % Nat.card A :=
      Nat.ModEq.add_left_cancel' _ hmod
    rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod'
    exact Fin.ext hmod'
  have hbij : Function.Bijective F := hinj.bijective_of_nat_card_le (by simp)
  let f : Fin (Nat.card A) ≃ A := Equiv.ofBijective F hbij
  have hf : ∀ i : Fin (Nat.card A), f i = ν^[(i : ℕ)] a₀ := fun _ => rfl
  have hstep : ∀ i : Fin (Nat.card A), f (nextIdx i) = ν (f i) := by
    intro i
    rw [hf, hf, ← Function.iterate_succ_apply' ν]
    by_cases hlt : (i : ℕ) + 1 < Nat.card A
    · rw [nextIdx_of_lt hlt]
    · have hcard : (i : ℕ) + 1 = Nat.card A := by
        have := i.isLt
        omega
      rw [nextIdx_of_last hcard]
      change ν^[0] a₀ = ν^[(i : ℕ) + 1] a₀
      rw [hcard]
      refine g.symm.injective (Fin.ext ?_)
      rw [hiter, hiter]
      simp
  have hmono : ∀ j k : Fin (Nat.card A),
      (fun x y => f.symm x ≤ f.symm y) (f j) (f k) ↔ j ≤ k := fun j k => by simp
  refine ⟨fun x y => f.symm x ≤ f.symm y,
    (tour_of_enum (R := fun _ _ => True) f fun _ => trivial).1, fun y => ?_, fun x y => ?_⟩
  · have h0 : f.symm a₀ = ⟨0, hn⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    change f.symm a₀ ≤ f.symm y
    rw [h0]
    exact Fin.mk_le_of_le_val (Nat.zero_le _)
  · rw [cycSucc_iff f hmono, cycSucc_iff g hg, hstep, Equiv.apply_symm_apply]

/-- **Circuits are the orders that start at a given element**, bijectively:
the tours of a relation whose least element is the least element of a linear
order of the universe are as many as its circuits. -/
theorem card_rootedTour_eq [LinearOrder A] [Nonempty A] (R : A → A → Prop) :
    Nat.card {Le : A → A → Prop // IsLinOrd Le ∧ (∀ x y, SuccOf Le x y → R x y) ∧
        (∀ x y, (∀ z, Le x z) → (∀ z, Le z y) → R y x) ∧
        ∀ x : A, IsBot x → ∀ y, Le x y} =
      Nat.card {Nxt : A → A → Prop // IsCircuit R Nxt} := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  refine Nat.card_congr (Equiv.ofBijective
    (fun Le => ⟨CycSucc Le.1, Le.1, Le.2.1, fun _ _ => Iff.rfl,
      fun x y h => h.elim (Le.2.2.1 x y) fun ⟨hmax, hmin⟩ => Le.2.2.2.1 y x hmin hmax⟩)
    ⟨?_, ?_⟩)
  · intro L L' hval
    have hc : CycSucc L.1 = CycSucc L'.1 := congrArg Subtype.val hval
    exact Subtype.ext (linOrd_eq_of_cycSucc L.2.1 L'.2.1 (L.2.2.2.2 a₀ ha₀)
      (L'.2.2.2.2 a₀ ha₀) fun x y => iff_of_eq (congrFun (congrFun hc x) y))
  · rintro ⟨Nxt, Le₀, h₀, hiff, hR⟩
    obtain ⟨Le, hlin, hmin, hcyc⟩ := exists_rooted_order h₀ a₀
    refine ⟨⟨Le, hlin, fun x y h => hR _ _ ((hiff _ _).mpr ((hcyc _ _).mp (Or.inl h))),
      fun x y hx hy => hR _ _ ((hiff _ _).mpr ((hcyc _ _).mp (Or.inr ⟨hy, hx⟩))),
      fun x hx y => ?_⟩, Subtype.ext (funext fun x => funext fun y =>
        propext ((hcyc x y).trans (hiff x y).symm))⟩
    rw [le_antisymm (hx a₀) (ha₀ x)]
    exact hmin y

end Circuit

/-! ### The counting problem -/

section Problem

variable (A : Type) [Language.digraph.Structure A]

/-- The relation `Nxt` is a Hamilton circuit of a finite digraph. -/
def DirCircuit (Nxt : A → A → Prop) : Prop :=
  Finite A ∧ IsCircuit (fun x y : A => DGArc x y) Nxt

end Problem

/-- **#Directed Hamilton Circuit**: the number of Hamilton circuits of a
digraph, a circuit being its “comes next” relation. -/
noncomputable def SharpDirHamCircuit : CountingProblem Language.digraph where
  Count := fun A inst => Nat.card {Nxt : A → A → Prop // @DirCircuit A inst Nxt}
  iso_invariant := fun e => Nat.card_congr
    (circuitEquiv e.toEquiv fun a a' => relMap_equiv₂ e dgArc a a')

theorem sharpDirHamCircuit_apply (A : Type) [Language.digraph.Structure A] :
    SharpDirHamCircuit A = Nat.card {Nxt : A → A → Prop // DirCircuit A Nxt} :=
  rfl

/-- **The support of #Directed Hamilton Circuit is Directed Hamilton
Circuit.**
Registered in the Lax archive as
[`Lax280166.DirHamCircuitComplete.sharpDirHamCircuit_support_iff`](https://laxarchive.org/lax-280166/Lax280166.DirHamCircuitComplete.html#s-Lax280166.DirHamCircuitComplete.sharpDirHamCircuit_support_iff). -/
theorem sharpDirHamCircuit_support_iff (A : Type) [Language.digraph.Structure A]
    [Finite A] : SharpDirHamCircuit.support A ↔ DirHamCircuit A := by
  rw [CountingProblem.support_iff, sharpDirHamCircuit_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨Nxt, hfin, hN⟩, -⟩
    exact ⟨hfin, tourOn_iff_exists_circuit.mpr ⟨Nxt, hN⟩⟩
  · rintro ⟨hfin, h⟩
    obtain ⟨Nxt, hN⟩ := tourOn_iff_exists_circuit.mp h
    exact ⟨⟨⟨Nxt, hfin, hN⟩⟩, inferInstance⟩

/-! ### Membership -/

/-- The vocabulary of the counting kernel: the ordered digraph, expanded by the
guessed order. -/
abbrev dhcLang : Language :=
  (Language.digraph.sum Language.order).sum hamGuessBlock.lang

/-- The guessed order, over the vocabulary of the counting kernel. -/
abbrev dhcVarSym : dhcLang.Relations 2 := Sum.inr hLeRel

/-- The order of the instance, over the vocabulary of the counting kernel. -/
abbrev dhcOrdSym : dhcLang.Relations 2 := Sum.inl (Sum.inr leSymb)

/-- Kernel conjunct: the guessed order starts where the order of the instance
does. -/
noncomputable def dhcRootClause : dhcLang.Sentence :=
  fo% ∀ x, (∀ z, dhcOrdSym(x, z)) → ∀ y, dhcVarSym(x, y)

/-- The guessed relation is a linear order carrying a tour – of the arcs when
`dir` is true, of the edges otherwise – and it starts at the least element of
the instance. -/
noncomputable def rootedHamKernel (dir : Bool) : dhcLang.Sentence :=
  orderFreeKernel hamGuessBlock (hamKernel dir) ⊓ dhcRootClause

/-- The first-order kernel of #Directed Hamilton Circuit: the guessed relation
is a linear order carrying a tour, and it starts at the least element of the
instance. -/
noncomputable def sharpDirHamKernel : dhcLang.Sentence :=
  rootedHamKernel true

section Kernel

variable {A : Type} [Language.digraph.Structure A] [LinearOrder A]

/-- Realization of the rooted tour kernel. -/
theorem realize_rootedHamKernel (dir : Bool) (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize dhcLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) (rootedHamKernel dir)) ↔
      IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, SuccOf (fun x y : A => ρ .le ![x, y]) x y →
          (if dir then DGArc x y else DGEdge x y)) ∧
        (∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) →
          (if dir then DGArc y x else DGEdge y x)) ∧
        ∀ x : A, IsBot x → ∀ y, ρ .le ![x, y] := by
  have hk := realize_hamKernel dir ρ
  let := hamGuessBlock.structure ρ
  have hexp : (LHom.sumMap (LHom.sumInl : Language.digraph →ᴸ
      Language.digraph.sum Language.order) (LHom.id hamGuessBlock.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  have hfree := LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : Language.digraph →ᴸ
    Language.digraph.sum Language.order) (LHom.id hamGuessBlock.lang)) (hamKernel dir)
  have hVar : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcVarSym w ↔ ρ .le w :=
    fun _ => Iff.rfl
  have hOrd : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcOrdSym w ↔ w 0 ≤ w 1 :=
    fun _ => Iff.rfl
  have hroot : (@Sentence.Realize dhcLang A _ dhcRootClause) ↔
      ∀ x : A, IsBot x → ∀ y, ρ .le ![x, y] := by
    simp only [dhcRootClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hVar, hOrd,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h x hx y => h (fun _ => x) (fun z => hx (z 0)) fun _ => y,
      fun h i hi y => h (i 0) (fun z => hi fun _ => z) (y 0)⟩
  rw [rootedHamKernel, Sentence.Realize, Formula.realize_inf]
  rw [← and_assoc, ← and_assoc]
  refine and_congr (hfree.trans (hk.trans ?_)) hroot
  rw [and_assoc]

/-- Realization of the kernel of #Directed Hamilton Circuit. -/
theorem realize_sharpDirHamKernel (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize dhcLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) sharpDirHamKernel) ↔
      IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, SuccOf (fun x y : A => ρ .le ![x, y]) x y → DGArc x y) ∧
        (∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) → DGArc y x) ∧
        ∀ x : A, IsBot x → ∀ y, ρ .le ![x, y] := by
  have h := realize_rootedHamKernel true ρ
  simp only [↓reduceIte] at h
  exact h

/-- A binary relation, as an assignment of the block guessing the order. -/
def hamAssignEquiv (A : Type) : hamGuessBlock.Assignment A ≃ (A → A → Prop) where
  toFun ρ := fun x y => ρ .le ![x, y]
  invFun Le := fun i => match i with
    | .le => fun w : Fin 2 → A => Le (w 0) (w 1)
  left_inv ρ := by
    funext i
    cases i
    refine funext fun (w : Fin 2 → A) => ?_
    exact congrArg (ρ .le) (funext fun k => by fin_cases k <;> rfl)
  right_inv _ := rfl

end Kernel

/-- **#Directed Hamilton Circuit is in `#P`**: a circuit has exactly one cut
at the least element of the instance. -/
theorem sharpDirHamCircuit_mem_sharpP : SharpDirHamCircuit ∈ SharpP := by
  refine ⟨hamGuessBlock, sharpDirHamKernel, fun A _ _ hfin _ => ?_⟩
  rw [sharpDirHamCircuit_apply]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)).trans
    ((card_rootedTour_eq (fun x y : A => DGArc x y)).symm.trans (Nat.card_congr
      (Equiv.subtypeEquiv (hamAssignEquiv A) fun ρ => (realize_sharpDirHamKernel ρ))).symm)

end DescriptiveComplexity
