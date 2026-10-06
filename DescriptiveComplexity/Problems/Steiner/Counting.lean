/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Steiner.Reductions
import DescriptiveComplexity.Arithmetic
import DescriptiveComplexity.Counting.Sized
import DescriptiveComplexity.Counting.Class

/-!
# #Steiner Tree: counting the Steiner sets of the threshold size

The counting version of `DescriptiveComplexity.SteinerTree`, the node-weighted problem:
the number of connected sets of vertices containing every terminal and using
*exactly* as many non-terminals as the marked set has elements
(`DescriptiveComplexity.SteinerOfSize`).

## The certificate of connectivity

Connectivity is not first-order. The `Σ₁` definition of the decision problem
certifies it by a root and a strict order in which every other chosen vertex
has a chosen neighbour below it (`DescriptiveComplexity.connectedOn_iff_exists_root`),
and there are many such orders. The counting kernel uses the order of the
*instance* as a clock: a binary relation `R x t`, “`x` is reached from the
least chosen vertex in at most as many steps as `t` has predecessors”, which is
determined step by step along the order
(`DescriptiveComplexity.IsReachClock`, `DescriptiveComplexity.IsReachClock.eq_clockOf`) – it is
`DescriptiveComplexity.reachIn` at the rank of `t`. The set is connected iff every
chosen vertex is reached by the last tick
(`DescriptiveComplexity.clockOf_top_iff_connectedOn`), a path needing fewer steps than
there are vertices (`DescriptiveComplexity.reachIn_card`).

This kernel reads the order, and defines the same count whatever the order:
the clock changes with it, the set of solutions does not. Hence
`DescriptiveComplexity.sharpSteinerTree_mem_sharpP`, by
`DescriptiveComplexity.sharpPDefinable_of_sized_ordered`.

As for Set Cover, the support is “some Steiner set uses exactly the threshold
number of non-terminals”, not the decision problem: a Steiner set can only be
extended by a neighbour.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Reachability in a bounded number of steps -/

section Reach

variable {A : Type}

theorem reachIn_le {R : A → A → Prop} {n m : ℕ} (hnm : n ≤ m) {x y : A}
    (h : reachIn R n x y) : reachIn R m x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => exact h
  | succ k ih => exact Or.inl (ih (Nat.le_add_right n k))

/-- **A path needs fewer steps than there are vertices.** -/
theorem reachIn_card [Finite A] {R : A → A → Prop} {r x : A}
    (h : Relation.ReflTransGen R r x) : reachIn R (Nat.card A - 1) r x := by
  classical
  have hex := (reflTransGen_iff_exists_reachIn R r x).mp h
  have hd : reachIn R (Nat.find hex) r x := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → ¬reachIn R j r x := fun j hj => Nat.find_min hex hj
  -- once the reached set stops growing, it never grows again
  have hstab : ∀ i, (∀ y, reachIn R (i + 1) r y → reachIn R i r y) →
      ∀ k y, reachIn R (i + k) r y → reachIn R i r y := by
    intro i hi k
    induction k with
    | zero => exact fun y hy => hy
    | succ k ih =>
      intro y hy
      rcases hy with hy | ⟨z, hz, hzy⟩
      · exact ih y hy
      · exact hi y (Or.inr ⟨z, ih z hz, hzy⟩)
  have hstrict : ∀ j, j < Nat.find hex → ∃ y, reachIn R (j + 1) r y ∧ ¬reachIn R j r y := by
    intro j hj
    by_contra hcon
    have hi : ∀ y, reachIn R (j + 1) r y → reachIn R j r y := fun y hy =>
      by_contra fun hny => hcon ⟨y, hy, hny⟩
    have hx : reachIn R (j + (Nat.find hex - j)) r x := by
      rw [Nat.add_sub_cancel' hj.le]
      exact hd
    exact hmin j hj (hstab j hi _ x hx)
  have hgrow : ∀ i, i ≤ Nat.find hex → i + 1 ≤ {y | reachIn R i r y}.ncard := by
    intro i
    induction i with
    | zero =>
      intro _
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨r, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨y, hy, hny⟩ := hstrict i hi
      have hlt : {y | reachIn R i r y}.ncard < {y | reachIn R (i + 1) r y}.ncard :=
        Set.ncard_lt_ncard ⟨fun z hz => Or.inl hz, fun hsub => hny (hsub hy)⟩
      have := ih (Nat.le_of_succ_le hi)
      omega
  have h₁ := hgrow _ le_rfl
  have h₂ := Set.ncard_le_card {y | reachIn R (Nat.find hex) r y}
  exact reachIn_le (by omega) hd

end Reach

/-! ### The clock -/

section Clock

variable {A : Type}

/-- The relation `R x t` is a reachability clock for the links `Lk` inside `S`:
at the first tick it holds of the least element of `S`, and at each later tick
of what the previous tick reached, and of its `Lk`-successors. -/
def IsReachClock [LE A] (Lk : A → A → Prop) (S : A → Prop) (R : A → A → Prop) : Prop :=
  (∀ x t, (∀ z, t ≤ z) → (R x t ↔ S x ∧ ∀ y, S y → x ≤ y)) ∧
    ∀ x t u, ((t ≤ u ∧ t ≠ u) ∧ ∀ z, ¬((t ≤ z ∧ t ≠ z) ∧ (z ≤ u ∧ z ≠ u))) →
      (R x u ↔ R x t ∨ ∃ y, R y t ∧ Lk y x)

variable [LinearOrder A] [Finite A]

/-- The clock: reachability from the least element of `S`, in as many steps as
the tick has predecessors. -/
def clockOf (Lk : A → A → Prop) (S : A → Prop) (x t : A) : Prop :=
  ∃ r, (S r ∧ ∀ y, S y → r ≤ y) ∧ reachIn Lk (orank t) r x

omit [Finite A] in
theorem clockOf_iff {Lk : A → A → Prop} {S : A → Prop} {x t : A} {k : ℕ} (hk : orank t = k) :
    clockOf Lk S x t ↔ ∃ r, (S r ∧ ∀ y, S y → r ≤ y) ∧ reachIn Lk k r x := by
  rw [clockOf, hk]

theorem isReachClock_clockOf (Lk : A → A → Prop) (S : A → Prop) :
    IsReachClock Lk S (clockOf Lk S) := by
  refine ⟨fun x t ht => ?_, fun x t u htu => ?_⟩
  · rw [clockOf_iff (orank_eq_zero ht)]
    exact ⟨fun ⟨r, hr, he⟩ => (show r = x from he) ▸ hr, fun h => ⟨x, h, rfl⟩⟩
  · have hcov : t ⋖ u := ⟨lt_of_le_of_ne htu.1.1 htu.1.2,
      fun c htc hcu => htu.2 c ⟨⟨htc.le, htc.ne⟩, ⟨hcu.le, hcu.ne⟩⟩⟩
    rw [clockOf_iff (orank_covBy hcov), clockOf_iff rfl]
    constructor
    · rintro ⟨r, hr, h | ⟨z, hz, hl⟩⟩
      · exact Or.inl ⟨r, hr, h⟩
      · exact Or.inr ⟨z, (clockOf_iff rfl).mpr ⟨r, hr, hz⟩, hl⟩
    · rintro (⟨r, hr, h⟩ | ⟨y, hy, hl⟩)
      · exact ⟨r, hr, Or.inl h⟩
      · obtain ⟨r, hr, h⟩ := (clockOf_iff rfl).mp hy
        exact ⟨r, hr, Or.inr ⟨y, h, hl⟩⟩

/-- **The clock is unique**: it is determined tick by tick. -/
theorem IsReachClock.eq_clockOf {Lk : A → A → Prop} {S : A → Prop} {R : A → A → Prop}
    (h : IsReachClock Lk S R) : R = clockOf Lk S := by
  have key : ∀ (k : ℕ) (t : A), orank t = k → ∀ x, R x t ↔ clockOf Lk S x t := by
    intro k
    induction k with
    | zero =>
      intro t hk x
      have hbot : ∀ z, t ≤ z := fun z => orank_le_iff.mp (by omega)
      exact (h.1 x t hbot).trans ((isReachClock_clockOf Lk S).1 x t hbot).symm
    | succ k ih =>
      intro t hk x
      obtain ⟨z', hz', hlt, hno⟩ := exists_pred_of_orank_succ hk
      have hcond : (z' ≤ t ∧ z' ≠ t) ∧ ∀ z, ¬((z' ≤ z ∧ z' ≠ z) ∧ (z ≤ t ∧ z ≠ t)) :=
        ⟨⟨hlt.le, hlt.ne⟩, fun z hz =>
          hno z ⟨lt_of_le_of_ne hz.1.1 hz.1.2, lt_of_le_of_ne hz.2.1 hz.2.2⟩⟩
      rw [h.2 x z' t hcond, (isReachClock_clockOf Lk S).2 x z' t hcond, ih z' hz' x]
      exact or_congr Iff.rfl (exists_congr fun y => and_congr (ih z' hz' y) Iff.rfl)
  funext x t
  exact propext (key _ t rfl x)

/-- **The set is connected iff the clock reaches all of it by the last
tick.** -/
theorem clockOf_top_iff_connectedOn (Adjp : A → A → Prop) (S : A → Prop) :
    (∀ x t, (∀ z, z ≤ t) → S x → clockOf (Link Adjp S) S x t) ↔ ConnectedOn Adjp S := by
  constructor
  · intro h x y hx hy
    have : Nonempty A := ⟨x⟩
    obtain ⟨t, ht⟩ := Finite.exists_max (id : A → A)
    obtain ⟨r, hr, hrx⟩ := h x t ht hx
    obtain ⟨r', hr', hry⟩ := h y t ht hy
    have hrr : r' = r := le_antisymm (hr'.2 r hr.1) (hr.2 r' hr'.1)
    rw [hrr] at hry
    exact (reflTransGen_symm (fun _ _ hab => link_symm hab)
      ((reflTransGen_iff_exists_reachIn _ r x).mpr ⟨_, hrx⟩)).trans
      ((reflTransGen_iff_exists_reachIn _ r y).mpr ⟨_, hry⟩)
  · intro hconn x t ht hx
    obtain ⟨r, hr, hmin⟩ := Set.exists_min_image {y | S y} id (Set.toFinite _) ⟨x, hx⟩
    refine ⟨r, ⟨hr, fun y hy => hmin y hy⟩, ?_⟩
    rw [orank_isTop ht]
    exact reachIn_card (hconn r x hr hx)

end Clock

/-! ### The counting problem -/

section Generic

variable {A B : Type}

/-- The set `S` contains every terminal, is connected, and has exactly as many
non-terminals as the `Kp`-marked set has elements. -/
def SteinerOfSizeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard = {x | Kp x}.ncard

/-- The Steiner sets of the threshold size transport along an equivalence
commuting with the three predicates. -/
def steinerOfSizeEquiv (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) :
    {S : B → Prop // Finite B ∧ SteinerOfSizeOn AdjB TermB KB S} ≃
      {S : A → Prop // Finite A ∧ SteinerOfSizeOn AdjA TermA KA S} where
  toFun S := ⟨fun a => S.1 (u.symm a), u.finite_iff.mp S.2.1,
    fun x hx => S.2.2.1 _ ((hterm _).mpr (by simpa using hx)),
    ConnectedOn.of_equiv u hadj (fun b => by simp) S.2.2.2.1,
    (ncard_setOf_equiv (KB := fun b => S.1 b ∧ ¬TermB b)
      (KA := fun a => S.1 (u.symm a) ∧ ¬TermA a) u (fun b => by
        rw [hterm b]
        simp)).symm.trans (S.2.2.2.2.trans (ncard_setOf_equiv u hK))⟩
  invFun T := ⟨fun b => T.1 (u b), u.finite_iff.mpr T.2.1,
    fun x hx => T.2.2.1 _ ((hterm x).mp hx),
    ConnectedOn.of_equiv u.symm (fun a a' => by
      rw [hadj]
      simp) (fun a => by simp) T.2.2.2.1,
    ((ncard_setOf_equiv (KB := fun b => T.1 (u b) ∧ ¬TermB b)
      (KA := fun a => T.1 a ∧ ¬TermA a) u (fun b => by rw [hterm b])).trans
      T.2.2.2.2).trans (ncard_setOf_equiv u hK).symm⟩
  left_inv S := Subtype.ext (funext fun b => by simp)
  right_inv T := Subtype.ext (funext fun a => by simp)

end Generic

section Problem

variable (A : Type) [Language.steinerGraph.Structure A]

/-- The set `S` is a connected set containing every terminal and using exactly
as many non-terminals as the marked set has elements, in a finite graph. -/
def SteinerOfSize (S : A → Prop) : Prop :=
  Finite A ∧ SteinerOfSizeOn (fun a b : A => STAdj a b) (fun a => STTerminal a)
    (fun a => STMarked a) S

end Problem

/-- **#Steiner Tree**: the number of connected sets containing every terminal
and using exactly as many non-terminals as the marked set has elements. -/
noncomputable def SharpSteinerTree : CountingProblem Language.steinerGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @SteinerOfSize A inst S}
  iso_invariant := fun e => Nat.card_congr
    (steinerOfSizeEquiv e.toEquiv (fun a a' => relMap_equiv₂ e stAdj a a')
      (fun a => relMap_equiv₁ e stTerminal a) fun a => relMap_equiv₁ e stMarked a)

theorem sharpSteinerTree_apply (A : Type) [Language.steinerGraph.Structure A] :
    SharpSteinerTree A = Nat.card {S : A → Prop // SteinerOfSize A S} :=
  rfl

/-- The support of #Steiner Tree: some Steiner set uses exactly the threshold
number of non-terminals. -/
theorem sharpSteinerTree_support_iff (A : Type) [Language.steinerGraph.Structure A]
    [Finite A] : SharpSteinerTree.support A ↔ ∃ S : A → Prop, SteinerOfSize A S := by
  rw [CountingProblem.support_iff, sharpSteinerTree_apply, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨S⟩, _⟩ => ⟨S.1, S.2⟩, fun ⟨S, hS⟩ => ⟨⟨⟨S, hS⟩⟩, inferInstance⟩⟩

/-- The support of #Steiner Tree implies Steiner Tree. -/
theorem steinerTree_of_sharpSteinerTree_support (A : Type)
    [Language.steinerGraph.Structure A] [Finite A] (h : SharpSteinerTree.support A) :
    SteinerTree A := by
  obtain ⟨S, hfin, hterm, hconn, hcard⟩ := (sharpSteinerTree_support_iff A).mp h
  exact ⟨hfin, S, hterm, hconn, hcard.le⟩

/-! ### Membership -/

/-- The block of the counting definition of Steiner Tree: the chosen set, its
non-terminals, and the reachability clock. -/
fo_block steinerCountBlock over Language.steinerGraph st into steinerCountLang with sc where
  /-- The chosen set. -/
  sel : 1
  /-- The non-terminals of the chosen set: the set whose size is the budget. -/
  non : 1
  /-- The reachability clock. -/
  reach : 2

/-- The vocabulary of the counting kernel: the *ordered* graph with terminals,
expanded by the block. -/
abbrev stoLang : Language :=
  (Language.steinerGraph.sum Language.order).sum steinerCountBlock.lang

/-- The `adj` symbol over the ordered sum. -/
abbrev stoAdjSym : stoLang.Relations 2 := Sum.inl (Sum.inl stAdj)

/-- The `terminal` symbol over the ordered sum. -/
abbrev stoTermSym : stoLang.Relations 1 := Sum.inl (Sum.inl stTerminal)

/-- The order symbol over the ordered sum. -/
abbrev stoLeSym : stoLang.Relations 2 := Sum.inl (Sum.inr leSymb)

/-- The `sel` symbol over the ordered sum. -/
abbrev stoSelSym : stoLang.Relations 1 := Sum.inr scSelRel

/-- The `non` symbol over the ordered sum. -/
abbrev stoNonSym : stoLang.Relations 1 := Sum.inr scNonRel

/-- The `reach` symbol over the ordered sum. -/
abbrev stoReachSym : stoLang.Relations 2 := Sum.inr scReachRel

/-- The first-order kernel of #Steiner Tree, over the ordered expansion: the
chosen set contains the terminals, the second set is its non-terminals, the
binary relation is the reachability clock, and the clock reaches the whole set
by the last tick. -/
noncomputable def steinerCountKernel : stoLang.Sentence :=
  fo% (∀ x, stoTermSym(x) → stoSelSym(x)) ∧
    (∀ x, stoNonSym(x) ↔ (stoSelSym(x) ∧ ¬ stoTermSym(x))) ∧
    (∀ x t, (∀ z, stoLeSym(t, z)) →
      (stoReachSym(x, t) ↔ (stoSelSym(x) ∧ ∀ y, stoSelSym(y) → stoLeSym(x, y)))) ∧
    (∀ x t u, ((stoLeSym(t, u) ∧ ¬ t ≐ u) ∧
        ∀ z, ¬ ((stoLeSym(t, z) ∧ ¬ t ≐ z) ∧ (stoLeSym(z, u) ∧ ¬ z ≐ u))) →
      (stoReachSym(x, u) ↔ (stoReachSym(x, t) ∨ ∃ y, stoReachSym(y, t) ∧
        (stoSelSym(y) ∧ stoSelSym(x) ∧ (stoAdjSym(y, x) ∨ stoAdjSym(x, y)))))) ∧
    (∀ x t, ((∀ z, stoLeSym(z, t)) ∧ stoSelSym(x)) → stoReachSym(x, t))

section Kernel

variable {A : Type} [Language.steinerGraph.Structure A] [LinearOrder A]

/-- Realization of the kernel of #Steiner Tree. -/
theorem realize_steinerCountKernel (ρ : steinerCountBlock.Assignment A) :
    (@Sentence.Realize stoLang A
        (@sumStructure _ _ A _ (steinerCountBlock.structure ρ)) steinerCountKernel) ↔
      (∀ x : A, STTerminal x → ρ .sel fun _ => x) ∧
        (∀ x : A, (ρ .non fun _ => x) ↔ (ρ .sel fun _ => x) ∧ ¬STTerminal x) ∧
        IsReachClock (Link (fun a b : A => STAdj a b) fun a => ρ .sel fun _ => a)
          (fun a => ρ .sel fun _ => a) (fun a b => ρ .reach ![a, b]) ∧
        ∀ x t : A, (∀ z, z ≤ t) → (ρ .sel fun _ => x) → ρ .reach ![x, t] := by
  let := steinerCountBlock.structure ρ
  have hsel : ∀ (w : Fin 1 → A),
      RelMap (L := stoLang) (M := A) stoSelSym w ↔ ρ .sel fun _ => w 0 := by
    intro w
    change ρ .sel _ ↔ ρ .sel _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  have hnon : ∀ (w : Fin 1 → A),
      RelMap (L := stoLang) (M := A) stoNonSym w ↔ ρ .non fun _ => w 0 := by
    intro w
    change ρ .non _ ↔ ρ .non _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  have hreach : ∀ (w : Fin 2 → A), RelMap (L := stoLang) (M := A) stoReachSym w ↔ ρ .reach w :=
    fun _ => Iff.rfl
  have hadj : ∀ (w : Fin 2 → A),
      RelMap (L := stoLang) (M := A) stoAdjSym w ↔ RelMap stAdj w := fun _ => Iff.rfl
  have hterm : ∀ (w : Fin 1 → A),
      RelMap (L := stoLang) (M := A) stoTermSym w ↔ RelMap stTerminal w := fun _ => Iff.rfl
  have hle : ∀ (w : Fin 2 → A), RelMap (L := stoLang) (M := A) stoLeSym w ↔ w 0 ≤ w 1 :=
    fun _ => Iff.rfl
  rw [steinerCountKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_sup, Formula.realize_iExs, Formula.realize_not, Formula.realize_iff,
    Formula.realize_equal, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl, hsel, hnon, hreach, hadj, hterm, hle, Matrix.cons_val_zero,
    Matrix.cons_val_one, IsReachClock, Link]
  refine and_congr ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩
    (and_congr ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩ ?_)
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h x t ht => (h ![x, t] fun z => ht (z 0)).trans
        (and_congr Iff.rfl ⟨fun h' y hy => h' (fun _ => y) hy, fun h' y hy => h' (y 0) hy⟩),
      fun h i hi => (h (i 0) (i 1) fun z => hi fun _ => z).trans
        (and_congr Iff.rfl ⟨fun h' y hy => h' (y 0) hy, fun h' y hy => h' (fun _ => y) hy⟩)⟩
  · exact ⟨fun h x t u htu => (h ![x, t, u] ⟨htu.1, fun z => htu.2 (z 0)⟩).trans
        (or_congr Iff.rfl ⟨fun ⟨y, hy⟩ => ⟨y 0, hy⟩, fun ⟨y, hy⟩ => ⟨fun _ => y, hy⟩⟩),
      fun h i hi => (h (i 0) (i 1) (i 2) ⟨hi.1, fun z => hi.2 fun _ => z⟩).trans
        (or_congr Iff.rfl ⟨fun ⟨y, hy⟩ => ⟨fun _ => y, hy⟩, fun ⟨y, hy⟩ => ⟨y 0, hy⟩⟩)⟩
  · exact ⟨fun h x t ht hx => h ![x, t] ⟨fun z => ht (z 0), hx⟩,
      fun h i hi => h (i 0) (i 1) (fun z => hi.1 fun _ => z) hi.2⟩

/-- The certificate of a set: the set, its non-terminals, and its clock. -/
def steinerCertOf (S : A → Prop) : steinerCountBlock.Assignment A :=
  fun i => match i with
    | .sel => fun w : Fin 1 → A => S (w 0)
    | .non => fun w : Fin 1 → A => S (w 0) ∧ ¬STTerminal (w 0)
    | .reach => fun w : Fin 2 → A =>
        clockOf (Link (fun a b : A => STAdj a b) S) S (w 0) (w 1)

variable (A) [Finite A]

/-- **The Steiner sets of the threshold size are the witnesses of the kernel of
that size**, bijectively: the non-terminals and the clock are determined. -/
noncomputable def steinerEquiv :
    {ρ : steinerCountBlock.Assignment A //
        (@Sentence.Realize stoLang A
          (@sumStructure _ _ A _ (steinerCountBlock.structure ρ)) steinerCountKernel) ∧
        {a | ρ .non fun _ => a}.ncard = {a : A | RelMap stMarked ![a]}.ncard} ≃
      {S : A → Prop // SteinerOfSize A S} where
  toFun ρ := ⟨fun a => ρ.1 .sel fun _ => a, ‹Finite A›,
    ((realize_steinerCountKernel ρ.1).mp ρ.2.1).1,
    (clockOf_top_iff_connectedOn _ _).mp fun x t ht hx => by
      have h := (realize_steinerCountKernel ρ.1).mp ρ.2.1
      have heq := h.2.2.1.eq_clockOf
      exact (iff_of_eq (congrFun (congrFun heq x) t)).mp (h.2.2.2 x t ht hx),
    (congrArg Set.ncard (Set.ext fun x =>
      (((realize_steinerCountKernel ρ.1).mp ρ.2.1).2.1 x).symm)).trans ρ.2.2⟩
  invFun S := ⟨steinerCertOf S.1,
    (realize_steinerCountKernel _).mpr ⟨S.2.2.1, fun _ => Iff.rfl, isReachClock_clockOf _ _,
      (clockOf_top_iff_connectedOn _ _).mpr S.2.2.2.1⟩, S.2.2.2.2⟩
  left_inv := by
    rintro ⟨ρ, hρ, hcard⟩
    have h := (realize_steinerCountKernel ρ).mp hρ
    have heq := h.2.2.1.eq_clockOf
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | sel =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .sel) (funext fun (j : Fin 1) => congrArg w (Subsingleton.elim 0 j))
    | non =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact (propext (h.2.1 (w 0)).symm).trans
        (congrArg (ρ .non) (funext fun (j : Fin 1) => congrArg w (Subsingleton.elim 0 j)))
    | reach =>
      refine funext fun (w : Fin 2 → A) => ?_
      exact (congrFun (congrFun heq (w 0)) (w 1)).symm.trans
        (congrArg (ρ .reach) (funext fun k => by fin_cases k <;> rfl))
  right_inv := fun _ => rfl

end Kernel

/-- **#Steiner Tree is in `#P`**: the budget is certified by the monotone
bijection with the marked set, and connectivity by the reachability clock. -/
theorem sharpSteinerTree_mem_sharpP : SharpSteinerTree ∈ SharpP :=
  sharpPDefinable_of_sized_ordered SharpSteinerTree steinerCountBlock stMarked .non rfl
    steinerCountKernel fun A _ _ _ => (Nat.card_congr (steinerEquiv A)).symm

end DescriptiveComplexity
