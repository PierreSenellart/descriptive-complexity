/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TwoCopies
import DescriptiveComplexity.Relativize

/-!
# Doubling a gadget: one construction, run on each side

A reduction between two problems of the GI degree applies one construction to
the pattern side of its input and the same construction to the host side. This
file makes that a *theorem about a single gadget*: given an interpretation `F`
of `L₁` in `L₀` – a construction taking one `L₀`-structure to one
`L₁`-structure – it builds `DescriptiveComplexity.FOInterpretation.double`,
mapping `FirstOrder.Language.twoCopies L₀`-instances to
`FirstOrder.Language.twoCopies L₁`-instances by running `F` on each marked
side, and identifies the sides of the result: the pattern side of `F.double`
applied to `A` is `F` applied to the pattern side of `A`
(`DescriptiveComplexity.patSide_double_equiv`).

Each side's defining formulas are those of `F` with every atom renamed to its
copy for that side (`DescriptiveComplexity.patLHom`) and every quantifier
restricted to that side's mark
(`DescriptiveComplexity.relativizeTo`). The correctness of the two operations
is proved *together*, by one induction
(`DescriptiveComplexity.realize_patRelativize`): separately, the rename would
have to cross a language reduct and the restriction a `Substructure` coercion,
and the two identifications would then have to be composed with the subtype the
side structures are actually stated on.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Renaming a base symbol to its copy -/

section Hom

variable (L₀ : Language.{0, 0}) [L₀.IsRelational]

/-- The base vocabulary, mapped onto its pattern copy. -/
def patLHom : L₀ →ᴸ Language.twoCopies L₀ where
  onFunction {_} f := isEmptyElim f
  onRelation {_} r := tcPat r

/-- The base vocabulary, mapped onto its host copy. -/
def hostLHom : L₀ →ᴸ Language.twoCopies L₀ where
  onFunction {_} f := isEmptyElim f
  onRelation {_} r := tcHost r

end Hom

/-! ### Reading a renamed, relativized formula on a side -/

section Realize

variable {L₀ : Language.{0, 0}} [L₀.IsRelational] {A : Type}
variable [(Language.twoCopies L₀).Structure A] {α : Type}

/-- A term of a relational vocabulary is a variable. -/
private theorem term_eq_var (t : L₀.Term α) : ∃ a, t = Term.var a := by
  cases t with
  | var a => exact ⟨a, rfl⟩
  | func f _ => exact isEmptyElim f

/-- **The pattern side reads what the gadget wrote**: a formula of the base
vocabulary, renamed to the pattern copy and relativized to the pattern mark,
holds in the ambient structure at arguments taken from the pattern side exactly
when the original formula holds on that side. -/
theorem realize_patRelativize :
    ∀ {n : ℕ} (φ : L₀.BoundedFormula α n) (v : α → {x : A // TCPatMark (L₁ := L₀) x})
      (xs : Fin n → {x : A // TCPatMark (L₁ := L₀) x}),
      (relativizeTo (tcPatMark L₀) ((patLHom L₀).onBoundedFormula φ)).Realize
          (fun a => (v a).1) (fun i => (xs i).1) ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    obtain ⟨a, rfl⟩ := term_eq_var t₁
    obtain ⟨b, rfl⟩ := term_eq_var t₂
    have hcomp : Sum.elim (fun a => ((v a : A))) (fun i => ((xs i : A))) =
        (Subtype.val : {x : A // TCPatMark (L₁ := L₀) x} → A) ∘ Sum.elim v xs :=
      (Sum.comp_elim _ v xs).symm
    change (Term.realize _ (Term.var a) = Term.realize _ (Term.var b)) ↔ _
    rw [hcomp]
    exact ⟨fun h => Subtype.val_injective h,
      fun h => congrArg Subtype.val (h : Sum.elim v xs a = Sum.elim v xs b)⟩
  | rel r ts =>
    intro v xs
    have hts : ∀ i, ∃ a, ts i = Term.var a := fun i => term_eq_var (ts i)
    choose a ha using hts
    have hrw : ts = fun i => Term.var (a i) := funext ha
    subst hrw
    have hcomp : Sum.elim (fun a => ((v a : A))) (fun i => ((xs i : A))) =
        (Subtype.val : {x : A // TCPatMark (L₁ := L₀) x} → A) ∘ Sum.elim v xs :=
      (Sum.comp_elim _ v xs).symm
    change RelMap (tcPat r) (fun i => Term.realize _ (Term.var (a i))) ↔ _
    rw [hcomp]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    change ((relativizeTo _ _).Realize _ _ → (relativizeTo _ _).Realize _ _) ↔ _
    rw [ihφ v xs, ihψ v xs]
    exact Iff.rfl
  | all φ ih =>
    intro v xs
    rw [LHom.onBoundedFormula, relativizeTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h b
      have hb := h b.1 ((realize_lastGuard _ _).mpr (by simpa [TCPatMark] using b.2))
      rw [show Fin.snoc (fun i => ((xs i : A))) (b : A) =
          fun i => (((Fin.snoc xs b : Fin _ → {x : A // TCPatMark (L₁ := L₀) x}) i : A)) by
        funext i
        exact congrFun (Fin.comp_snoc (Subtype.val : _ → A) xs b).symm i] at hb
      exact (ih v (Fin.snoc xs b)).mp hb
    · intro h y hguard
      have hy : TCPatMark (L₁ := L₀) y := by
        simpa [TCPatMark] using (realize_lastGuard _ _).mp hguard
      have hb := (ih v (Fin.snoc xs ⟨y, hy⟩)).mpr (h ⟨y, hy⟩)
      rw [show (fun i =>
            (((Fin.snoc xs (⟨y, hy⟩ : {x : A // TCPatMark (L₁ := L₀) x}) : Fin _ → _) i : A))) =
          Fin.snoc (fun i => ((xs i : A))) y by
        funext i
        exact congrFun (Fin.comp_snoc (Subtype.val : _ → A) xs ⟨y, hy⟩) i] at hb
      exact hb

/-- **The host side reads what the gadget wrote**: a formula of the base
vocabulary, renamed to the host copy and relativized to the host mark,
holds in the ambient structure at arguments taken from the host side exactly
when the original formula holds on that side. -/
theorem realize_hostRelativize :
    ∀ {n : ℕ} (φ : L₀.BoundedFormula α n) (v : α → {x : A // TCHostMark (L₁ := L₀) x})
      (xs : Fin n → {x : A // TCHostMark (L₁ := L₀) x}),
      (relativizeTo (tcHostMark L₀) ((hostLHom L₀).onBoundedFormula φ)).Realize
          (fun a => (v a).1) (fun i => (xs i).1) ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    obtain ⟨a, rfl⟩ := term_eq_var t₁
    obtain ⟨b, rfl⟩ := term_eq_var t₂
    have hcomp : Sum.elim (fun a => ((v a : A))) (fun i => ((xs i : A))) =
        (Subtype.val : {x : A // TCHostMark (L₁ := L₀) x} → A) ∘ Sum.elim v xs :=
      (Sum.comp_elim _ v xs).symm
    change (Term.realize _ (Term.var a) = Term.realize _ (Term.var b)) ↔ _
    rw [hcomp]
    exact ⟨fun h => Subtype.val_injective h,
      fun h => congrArg Subtype.val (h : Sum.elim v xs a = Sum.elim v xs b)⟩
  | rel r ts =>
    intro v xs
    have hts : ∀ i, ∃ a, ts i = Term.var a := fun i => term_eq_var (ts i)
    choose a ha using hts
    have hrw : ts = fun i => Term.var (a i) := funext ha
    subst hrw
    have hcomp : Sum.elim (fun a => ((v a : A))) (fun i => ((xs i : A))) =
        (Subtype.val : {x : A // TCHostMark (L₁ := L₀) x} → A) ∘ Sum.elim v xs :=
      (Sum.comp_elim _ v xs).symm
    change RelMap (tcHost r) (fun i => Term.realize _ (Term.var (a i))) ↔ _
    rw [hcomp]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    change ((relativizeTo _ _).Realize _ _ → (relativizeTo _ _).Realize _ _) ↔ _
    rw [ihφ v xs, ihψ v xs]
    exact Iff.rfl
  | all φ ih =>
    intro v xs
    rw [LHom.onBoundedFormula, relativizeTo]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h b
      have hb := h b.1 ((realize_lastGuard _ _).mpr (by simpa [TCHostMark] using b.2))
      rw [show Fin.snoc (fun i => ((xs i : A))) (b : A) =
          fun i => (((Fin.snoc xs b : Fin _ → {x : A // TCHostMark (L₁ := L₀) x}) i : A)) by
        funext i
        exact congrFun (Fin.comp_snoc (Subtype.val : _ → A) xs b).symm i] at hb
      exact (ih v (Fin.snoc xs b)).mp hb
    · intro h y hguard
      have hy : TCHostMark (L₁ := L₀) y := by
        simpa [TCHostMark] using (realize_lastGuard _ _).mp hguard
      have hb := (ih v (Fin.snoc xs ⟨y, hy⟩)).mpr (h ⟨y, hy⟩)
      rw [show (fun i =>
            (((Fin.snoc xs (⟨y, hy⟩ : {x : A // TCHostMark (L₁ := L₀) x}) : Fin _ → _) i : A))) =
          Fin.snoc (fun i => ((xs i : A))) y by
        funext i
        exact congrFun (Fin.comp_snoc (Subtype.val : _ → A) xs ⟨y, hy⟩) i] at hb
      exact hb

end Realize

/-! ### The doubled interpretation -/

section Double

variable {L₀ L₁ : Language.{0, 0}} [L₀.IsRelational] [L₁.IsRelational]
variable {Tag : Type} {d : ℕ}

/-- **A gadget, run on both sides.** The pattern copy of a relation symbol is
defined by the gadget's own formula, its atoms renamed to the pattern copies
and its quantifiers restricted to the pattern mark; the host copy likewise. A
point belongs to a side exactly when all `d` of its coordinates do. -/
noncomputable def FOInterpretation.double (F : FOInterpretation L₀ L₁ Tag d) :
    FOInterpretation (Language.twoCopies L₀) (Language.twoCopies L₁) Tag d where
  relFormula {n} R :=
    match n, R with
    | _, .patMark => fun _ =>
        Formula.iInf fun j : Fin d => Relations.formula₁ (tcPatMark L₀) (Term.var (0, j))
    | _, .hostMark => fun _ =>
        Formula.iInf fun j : Fin d => Relations.formula₁ (tcHostMark L₀) (Term.var (0, j))
    | _, .pat r => fun t =>
        relativizeTo (tcPatMark L₀) ((patLHom L₀).onFormula (F.relFormula r t))
    | _, .host r => fun t =>
        relativizeTo (tcHostMark L₀) ((hostLHom L₀).onFormula (F.relFormula r t))

variable (F : FOInterpretation L₀ L₁ Tag d) {A : Type} [(Language.twoCopies L₀).Structure A]

omit [L₁.IsRelational] in
/-- **A point of the doubled construction is on the pattern side exactly when
all its coordinates are.** -/
theorem tcPatMark_double (p : F.double.Map A) :
    TCPatMark (L₁ := L₁) p ↔ ∀ j, TCPatMark (L₁ := L₀) (p.2 j) := by
  rw [TCPatMark, FOInterpretation.relMap_map]
  simp only [FOInterpretation.double, Formula.realize_iInf, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

omit [L₁.IsRelational] in
/-- The same, on the host side. -/
theorem tcHostMark_double (p : F.double.Map A) :
    TCHostMark (L₁ := L₁) p ↔ ∀ j, TCHostMark (L₁ := L₀) (p.2 j) := by
  rw [TCHostMark, FOInterpretation.relMap_map]
  simp only [FOInterpretation.double, Formula.realize_iInf, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-! ### The sides of the doubled construction -/

/-- **The pattern side of the doubled gadget is the gadget on the pattern
side.** This is what makes a reduction between isomorphism problems a statement
about a construction on *single* structures: the two sides of the constructed
instance are `F` applied to the two sides of the input, so an isomorphism of
the former is one of the latter's images. -/
noncomputable def patSideDoubleEquiv :
    {p : F.double.Map A // TCPatMark (L₁ := L₁) p} ≃[L₁]
      F.Map {x : A // TCPatMark (L₁ := L₀) x} where
  toFun p := (p.1.1, fun j => ⟨p.1.2 j, (tcPatMark_double F p.1).mp p.2 j⟩)
  invFun q := ⟨(q.1, fun j => (q.2 j).1), (tcPatMark_double F _).mpr fun j => (q.2 j).2⟩
  left_inv p := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun _ => rfl⟩)
  right_inv q := Prod.ext_iff.mpr ⟨rfl, funext fun _ => Subtype.ext rfl⟩
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have hRHS : RelMap (L := L₁) r x ↔
        RelMap (L := Language.twoCopies L₁) (tcPat r) fun i => ((x i).1 : F.double.Map A) :=
      Iff.rfl
    rw [hRHS, FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    simp only [FOInterpretation.double]
    have h := realize_patRelativize (F.relFormula r fun i => ((x i).1).1)
      (fun p => ⟨((x p.1).1).2 p.2, (tcPatMark_double F (x p.1).1).mp (x p.1).2 p.2⟩)
      (default : Fin 0 → {x : A // TCPatMark (L₁ := L₀) x})
    rw [show (fun i => ((default : Fin 0 → {x : A // TCPatMark (L₁ := L₀) x}) i).1)
        = (default : Fin 0 → A) from funext fun i => i.elim0] at h
    exact h.symm

/-- The same identification on the host side. -/
noncomputable def hostSideDoubleEquiv :
    {p : F.double.Map A // TCHostMark (L₁ := L₁) p} ≃[L₁]
      F.Map {x : A // TCHostMark (L₁ := L₀) x} where
  toFun p := (p.1.1, fun j => ⟨p.1.2 j, (tcHostMark_double F p.1).mp p.2 j⟩)
  invFun q := ⟨(q.1, fun j => (q.2 j).1), (tcHostMark_double F _).mpr fun j => (q.2 j).2⟩
  left_inv p := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun _ => rfl⟩)
  right_inv q := Prod.ext_iff.mpr ⟨rfl, funext fun _ => Subtype.ext rfl⟩
  map_fun' f := isEmptyElim f
  map_rel' {n} r x := by
    have hRHS : RelMap (L := L₁) r x ↔
        RelMap (L := Language.twoCopies L₁) (tcHost r) fun i => ((x i).1 : F.double.Map A) :=
      Iff.rfl
    rw [hRHS, FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    simp only [FOInterpretation.double]
    have h := realize_hostRelativize (F.relFormula r fun i => ((x i).1).1)
      (fun p => ⟨((x p.1).1).2 p.2, (tcHostMark_double F (x p.1).1).mp (x p.1).2 p.2⟩)
      (default : Fin 0 → {x : A // TCHostMark (L₁ := L₀) x})
    rw [show (fun i => ((default : Fin 0 → {x : A // TCHostMark (L₁ := L₀) x}) i).1)
        = (default : Fin 0 → A) from funext fun i => i.elim0] at h
    exact h.symm

/-! ### What a gadget has to satisfy -/

/-- The two sides of the doubled construction are isomorphic exactly when the
gadget's values on the two sides of the input are. -/
theorem nonempty_double_sides_iff :
    Nonempty (TCSideEquiv (L₁ := L₁) (F.double.Map A)) ↔
      Nonempty (F.Map {x : A // TCPatMark (L₁ := L₀) x} ≃[L₁]
        F.Map {x : A // TCHostMark (L₁ := L₀) x}) :=
  ⟨fun ⟨i⟩ => ⟨((hostSideDoubleEquiv F).comp i).comp (patSideDoubleEquiv F).symm⟩,
    fun ⟨i⟩ => ⟨((hostSideDoubleEquiv F).symm.comp i).comp (patSideDoubleEquiv F)⟩⟩

/-- A gadget **reflects isomorphism** when isomorphic values come from
isomorphic arguments. The converse holds for free, an interpretation being
functorial (`DescriptiveComplexity.FOInterpretation.mapLEquiv`), so this is the
whole content a client has to supply – and it speaks about single structures,
with no pattern/host distinction anywhere. -/
def IsoReflecting (F : FOInterpretation L₀ L₁ Tag d) : Prop :=
  ∀ (G H : Type) [L₀.Structure G] [L₀.Structure H] [Finite G] [Finite H],
    Nonempty (F.Map G ≃[L₁] F.Map H) → Nonempty (G ≃[L₀] H)

/-- **Correctness of a doubled gadget**: the two sides of the input are
isomorphic exactly when the two sides of its image are. -/
theorem twoCopiesIso_double_iff [Finite Tag] (hrefl : IsoReflecting F) (hA : Finite A) :
    (TwoCopiesIso L₀).Holds A ↔ (TwoCopiesIso L₁).Holds (F.double.Map A) := by
  have := hA
  have : Finite {x : A // TCPatMark (L₁ := L₀) x} := Subtype.finite
  have : Finite {x : A // TCHostMark (L₁ := L₀) x} := Subtype.finite
  constructor
  · rintro ⟨-, ⟨i⟩⟩
    exact ⟨F.double.map_finite A, (nonempty_double_sides_iff F).mpr ⟨F.mapLEquiv i⟩⟩
  · rintro ⟨-, ⟨i⟩⟩
    exact ⟨hA, hrefl _ _ ((nonempty_double_sides_iff F).mp ⟨i⟩)⟩

/-- **A gadget that reflects isomorphism is a reduction**: run it on both
sides. Order-free, as a reduction between isomorphism problems must be. -/
noncomputable def isoReflecting_fo_reduction [Finite Tag] [Nonempty Tag]
    (hrefl : IsoReflecting F) : TwoCopiesIso L₀ ≤ᶠᵒ TwoCopiesIso L₁ where
  Tag := Tag
  dim := d
  toInterpretation := F.double
  correct A _ _ _ := twoCopiesIso_double_iff F hrefl ‹Finite A›

end Double

end DescriptiveComplexity
