/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNew

/-!
# Relativization of a formula to a unary predicate

Restricting every quantifier of a first-order formula to the elements
satisfying a unary relation symbol (`DescriptiveComplexity.relativizeTo`), so
that the formula, read in a structure `M`, says exactly what it says in the
part of `M` that the symbol marks
(`DescriptiveComplexity.realize_relativizeTo`).

The part must be closed under the function symbols of the language, so that it
carries a structure at all; the statement therefore takes the marked part as a
`FirstOrder.Language.Substructure` whose carrier the symbol defines. Marking
by a *symbol* rather than by an arbitrary formula is what the users below
need, and keeps the guard a one-line atom.

## Where this is used

Value invention (`DescriptiveComplexity.SecondOrderNew`) puts the instance `A`
and `m` invented values in one universe `A ⊕ Fin m`. A formula about `A` – in
particular a defining formula of an interpretation being pulled back – must
then be read with its quantifiers restricted to the original elements, which
is exactly relativization to the predicate `old`. The specialization
`DescriptiveComplexity.relOld` and its correctness
`DescriptiveComplexity.realize_relOld` package that instance: the old part of
`A ⊕ Fin m` is a substructure (function symbols return original elements by
`DescriptiveComplexity.extBase`) isomorphic to `A`
(`DescriptiveComplexity.oldSubEquiv`).

The same machinery is what a relativized *membership* pullback
(`ROADMAP.md`, the domain-formula item) would want.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Relativization to a unary relation symbol -/

section Relativize

variable {L : Language.{0, 0}} {α : Type}

/-- The guard “the last bound variable satisfies `R`”. -/
def lastGuard (R : L.Relations 1) (n : ℕ) : L.BoundedFormula α (n + 1) :=
  R.boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))

/-- **Relativization**: the formula obtained by restricting every quantifier
to the elements satisfying the unary relation symbol `R`. Atoms are left
untouched, so this is a purely syntactic guard insertion. -/
def relativizeTo (R : L.Relations 1) :
    ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel r ts => .rel r ts
  | _, .imp φ ψ => .imp (relativizeTo R φ) (relativizeTo R ψ)
  | n, .all φ => .all ((lastGuard R n).imp (relativizeTo R φ))

variable {M : Type} [L.Structure M] {R : L.Relations 1}

theorem realize_lastGuard {n : ℕ} (v : α → M) (xs : Fin (n + 1) → M) :
    (lastGuard R n).Realize v xs ↔ RelMap R ![xs (Fin.last n)] := by
  rw [lastGuard, BoundedFormula.realize_rel₁]
  rfl

/-- **Relativization is correct**: the relativized formula, read in `M` at
arguments taken from the substructure the symbol `R` defines, says what the
original formula says in that substructure. -/
theorem realize_relativizeTo (S : L.Substructure M) (hS : ∀ x : M, x ∈ S ↔ RelMap R ![x]) :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → S) (xs : Fin n → S),
      (relativizeTo R φ).Realize (fun a => ((v a : M))) (fun i => ((xs i : M))) ↔
        φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    have hcomp : Sum.elim (fun a => ((v a : M))) (fun i => ((xs i : M))) =
        (S.subtype : S → M) ∘ Sum.elim v xs :=
      (Sum.comp_elim (S.subtype : S → M) v xs).symm
    change (Term.realize _ t₁ = Term.realize _ t₂) ↔ _
    rw [hcomp, HomClass.realize_term, HomClass.realize_term]
    exact ⟨fun h => S.subtype.injective h, fun h => congrArg _ h⟩
  | rel r ts =>
    intro v xs
    have hcomp : Sum.elim (fun a => ((v a : M))) (fun i => ((xs i : M))) =
        (S.subtype : S → M) ∘ Sum.elim v xs :=
      (Sum.comp_elim (S.subtype : S → M) v xs).symm
    change RelMap r (fun i => Term.realize _ (ts i)) ↔ _
    rw [hcomp]
    simp only [HomClass.realize_term]
    exact S.subtype.map_rel' r _
  | imp φ ψ ihφ ihψ =>
    intro v xs
    change ((relativizeTo R φ).Realize _ _ → (relativizeTo R ψ).Realize _ _) ↔ _
    rw [ihφ v xs, ihψ v xs]
    exact Iff.rfl
  | all φ ih =>
    intro v xs
    rw [relativizeTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h b
      have hguard : RelMap R ![((b : M))] := (hS _).mp b.2
      have hb := h (b : M) ((realize_lastGuard _ _).mpr (by simpa using hguard))
      rw [show Fin.snoc (fun i => ((xs i : M))) ((b : M)) =
          fun i => (((Fin.snoc xs b : Fin _ → S) i : M)) by
        funext i
        exact congrFun (Fin.comp_snoc (S.subtype : S → M) xs b).symm i] at hb
      exact (ih v (Fin.snoc xs b)).mp hb
    · intro h a hguard
      have ha : a ∈ S := (hS a).mpr (by simpa using (realize_lastGuard _ _).mp hguard)
      have hb := (ih v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)
      rw [show (fun i => (((Fin.snoc xs (⟨a, ha⟩ : S) : Fin _ → S) i : M))) =
          Fin.snoc (fun i => ((xs i : M))) a by
        funext i
        exact congrFun (Fin.comp_snoc (S.subtype : S → M) xs ⟨a, ha⟩) i] at hb
      exact hb

end Relativize

/-! ### Relativization to the original elements of an extended universe -/

section Old

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [Nonempty A] (m : ℕ)

/-- The original elements of the extended universe form a substructure: by
`DescriptiveComplexity.extBase`, function symbols take their values among the
original elements. -/
def oldSub : (newLang L).Substructure (A ⊕ Fin m) where
  carrier := {x | IsOld x}
  fun_mem := fun {_n} f x _ => by
    cases f with
    | inl f => exact trivial
    | inr f => exact isEmptyElim f

theorem mem_oldSub_iff (x : A ⊕ Fin m) : x ∈ oldSub L A m ↔ IsOld x := Iff.rfl

/-- The substructure of original elements is the instance itself, over the
extended vocabulary (where every element is marked as original). -/
noncomputable def oldSubEquiv :
    @Language.Equiv (newLang L) (oldSub L A m) A Substructure.inducedStructure
      (allOldStructure L A) :=
  letI := allOldStructure L A
  { toEquiv :=
      { toFun := fun x => oldPart A m (x : A ⊕ Fin m)
        invFun := fun a => ⟨Sum.inl a, isOld_inl (m := m) a⟩
        left_inv := fun x => Subtype.ext (by
          obtain ⟨a, ha⟩ := isOld_iff.mp (x.2 : IsOld (x : A ⊕ Fin m))
          change Sum.inl (oldPart A m (x : A ⊕ Fin m)) = (x : A ⊕ Fin m)
          rw [ha]
          rfl)
        right_inv := fun _ => rfl }
    map_fun' := fun {_n} f x => by
      cases f with
      | inl f =>
        change oldPart A m (funMap (L := newLang L) (Sum.inl f) fun i => ((x i : A ⊕ Fin m))) = _
        rfl
      | inr f => exact isEmptyElim f
    map_rel' := fun {_n} r x => by
      cases r with
      | inl s =>
        change RelMap (L := newLang L) (M := A) (Sum.inl s)
            (fun i => oldPart A m ((x i : A ⊕ Fin m))) ↔
          RelMap (L := newLang L) (M := A ⊕ Fin m) (Sum.inl s)
            (fun i => ((x i : A ⊕ Fin m)))
        have hcoe : ∀ i, ((x i : A ⊕ Fin m)) = Sum.inl (oldPart A m ((x i : A ⊕ Fin m))) := by
          intro i
          obtain ⟨a, ha⟩ := isOld_iff.mp (x i).2
          rw [ha]
          rfl
        rw [relMap_ext_iff]
        refine ⟨fun h => ⟨_, hcoe, h⟩, fun h => ?_⟩
        obtain ⟨y, hy, h⟩ := h
        have hyy : (fun i => oldPart A m ((x i : A ⊕ Fin m))) = y := by
          funext i
          exact Sum.inl_injective ((hcoe i).symm.trans (hy i))
        rw [hyy]
        exact h
      | inr s =>
        cases s with
        | old => exact iff_of_true trivial (x 0).2 }

variable {L A m}

/-- The relativization of an `L`-formula to the original elements of an
extended universe: an `L`-formula becomes a formula over the extended
vocabulary, with every quantifier restricted to the elements marked `old`. -/
def relOld {γ : Type} (φ : L.Formula γ) : (newLang L).Formula γ :=
  relativizeTo (Sum.inr Language.oldSym) (LHom.sumInl.onFormula φ)

/-- **Relativizing to the original elements is correct**: read in the extended
universe at original arguments, the relativized formula says what the original
formula says in the instance. -/
theorem realize_relOld {γ : Type} (φ : L.Formula γ) (v : γ → A) :
    (relOld φ).Realize (M := A ⊕ Fin m) (fun g => Sum.inl (v g)) ↔ φ.Realize v := by
  letI := allOldStructure L A
  let w : γ → oldSub L A m := fun g => ⟨Sum.inl (v g), isOld_inl (m := m) (v g)⟩
  have hsub : ∀ x : A ⊕ Fin m, x ∈ oldSub L A m ↔
      RelMap (L := newLang L) (Sum.inr Language.oldSym) ![x] := fun _ => Iff.rfl
  have h1 := realize_relativizeTo (R := (Sum.inr Language.oldSym : (newLang L).Relations 1))
    (oldSub L A m) hsub (LHom.sumInl.onFormula φ) w (default : Fin 0 → oldSub L A m)
  have h2 := StrongHomClass.realize_formula (L := newLang L) (oldSubEquiv L A m)
    (LHom.sumInl.onFormula φ) (v := w)
  have h3 := LHom.realize_onFormula (M := A) (LHom.sumInl : L →ᴸ newLang L) φ (v := v)
  refine Iff.trans ?_ (h1.trans (h2.symm.trans h3))
  exact iff_of_eq (congrArg
    (fun xs => BoundedFormula.Realize (M := A ⊕ Fin m) (relOld φ) (fun g => Sum.inl (v g)) xs)
    (Subsingleton.elim _ _))

end Old

end DescriptiveComplexity
