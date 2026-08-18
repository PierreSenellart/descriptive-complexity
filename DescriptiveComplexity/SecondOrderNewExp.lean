/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewBdd
import DescriptiveComplexity.Exponential.Free
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.Relativize

/-!
# The expansion a bounded invention lives in

`DescriptiveComplexity.SigmaSONewExpDefinable` guesses an extension `A ⊕ Fin m`
with `m ≤ 2 ^ Nat.card (Fin d → A)` – as many invented values as the instance
has `d`-ary relations. To read such a definition as one over an *exponential
expansion*, the expansion has to be big enough to hold them, and it has to carry
the instance too, since an expansion is all a sentence over it can see.

This file builds that expansion. It has two tags:

* an **original** point is an assignment whose unary variable is a singleton and
  whose `d`-ary one is empty – so those points are the elements of the instance;
* a **new** point is an assignment whose unary variable is empty – so those
  points are the `d`-ary relations of the instance, `2 ^ nᵈ` of them.

Its vocabulary is `DescriptiveComplexity.newLang L`: the relations of the
instance, holding of original points exactly where they hold of the elements
they name, and the marker `old`. What the expanded structure is, then, is the
extended structure `A ⊕ Fin (2 ^ nᵈ)` with *every* invented value present; a
sentence that wants fewer of them marks the ones it uses, which is a guess and
so stays inside `Σ₁`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The block -/

/-- The block whose assignments are the points of the expansion: one `d`-ary
variable carrying an invented value and one unary variable carrying an original
element. -/
abbrev powBlock (c d : ℕ) : SOBlock where
  ι := Option (Fin c)
  arity := fun i => i.elim 1 fun _ => d

/-- The `i`-th `d`-ary variable: one coordinate of an invented value. -/
def powValSym (c d : ℕ) (i : Fin c) : (powBlock c d).lang.Relations d :=
  ⟨some i, rfl⟩

/-- The unary variable: an original element. -/
def powEltSym (c d : ℕ) : (powBlock c d).lang.Relations 1 :=
  ⟨none, rfl⟩

/-- The unary variable of the `k`-th copy. -/
def powEltSymAt (c d : ℕ) {n : ℕ} (k : Fin n) :
    ((powBlock c d).replicate n).lang.Relations 1 :=
  (powBlock c d).replicateSym k (powEltSym c d)

/-! ### The sentences -/

section Sentences

variable (L : Language.{0, 0}) (c d : ℕ)

/-- The atom `elt x`, over the vocabulary of the block. -/
noncomputable def eltAtom {α : Type} (x : α) : (L.sum (powBlock c d).lang).Formula α :=
  Relations.formula (Sum.inr (powEltSym c d) : (L.sum (powBlock c d).lang).Relations 1)
    fun _ => Term.var x

/-- The atom `eltₖ x`, over the vocabulary of `n` copies of the block. -/
noncomputable def eltAtomAt {n : ℕ} (k : Fin n) {α : Type} (x : α) :
    (L.sum ((powBlock c d).replicate n).lang).Formula α :=
  Relations.formula
    (Sum.inr (powEltSymAt c d k) : (L.sum ((powBlock c d).replicate n).lang).Relations 1)
    fun _ => Term.var x

/-- The atom `valᵢ w`, over the vocabulary of the block. -/
noncomputable def valAtom (i : Fin c) {α : Type} (w : Fin d → α) :
    (L.sum (powBlock c d).lang).Formula α :=
  Relations.formula (Sum.inr (powValSym c d i) : (L.sum (powBlock c d).lang).Relations d)
    fun j => Term.var (w j)

/-- `elt` holds of exactly one element. -/
noncomputable def eltUnique : (L.sum (powBlock c d).lang).Sentence :=
  Formula.iExsUnique (Fin 1) (eltAtom L c d (Sum.inr 0))

/-- `elt` holds of nothing. -/
noncomputable def eltEmpty : (L.sum (powBlock c d).lang).Sentence :=
  Formula.iAlls (Fin 1) (∼(eltAtom L c d (Sum.inr 0)))

/-- No coordinate of the invented value holds of anything. -/
noncomputable def valEmpty : (L.sum (powBlock c d).lang).Sentence :=
  Formula.iInf fun i : Fin c => Formula.iAlls (Fin d) (∼(valAtom L c d i fun j => Sum.inr j))

/-- **The domain sentence of each tag**: an original point names one element and
invents nothing; a new point names no element. -/
noncomputable def powDom : Bool → (L.sum (powBlock c d).lang).Sentence
  | false => eltUnique L c d ⊓ valEmpty L c d
  | true => eltEmpty L c d

open Classical in
/-- **The defining sentence of each symbol**: a relation of the instance holds of
original points exactly when it holds of the elements they name, and never of a
new point; `old` marks the original points. -/
noncomputable def powRelSentence :
    ∀ {n : ℕ}, (newLang L).Relations n → (Fin n → Bool) →
      (L.sum ((powBlock c d).replicate n).lang).Sentence
  | n, Sum.inl R, τ =>
      if ∀ i : Fin n, τ i = false then
        (((Formula.iInf fun i : Fin n => eltAtomAt L c d i (Sum.inr i)) ⊓
            Relations.formula
              (Sum.inl R : (L.sum ((powBlock c d).replicate n).lang).Relations n)
              fun i => Term.var (Sum.inr i)).iExs (Fin n))
      else ⊥
  | _, Sum.inr r, τ =>
      match r with
      | .old => if τ 0 = false then ⊤ else ⊥

end Sentences

/-! ### The sentences, realized -/

section Realize

variable {L : Language.{0, 0}} {c d : ℕ} {A : Type} [L.Structure A]
variable (ρ : (powBlock c d).Assignment A)

/-- The unary variable, read off the assignment. -/
def eltOf : A → Prop := fun x => ρ none fun _ => x

/-- The `d`-ary variables, read off the assignment. -/
def valOf : Fin c → (Fin d → A) → Prop := fun i w => ρ (some i) w

theorem realize_eltAtom {α : Type} (x : α) (v : α → A) :
    letI := (powBlock c d).structure₁ (L := L) ρ
    (eltAtom L c d x).Realize v ↔ eltOf ρ (v x) := by
  letI := (powBlock c d).structure₁ (L := L) ρ
  exact Iff.rfl

theorem realize_valAtom (i : Fin c) {α : Type} (w : Fin d → α) (v : α → A) :
    letI := (powBlock c d).structure₁ (L := L) ρ
    (valAtom L c d i w).Realize v ↔ valOf ρ i (fun j => v (w j)) := by
  letI := (powBlock c d).structure₁ (L := L) ρ
  exact Iff.rfl

theorem realize_eltEmpty :
    letI := (powBlock c d).structure₁ (L := L) ρ
    A ⊨ (eltEmpty L c d) ↔
      ∀ x : A, ¬eltOf ρ x := by
  letI := (powBlock c d).structure₁ (L := L) ρ
  rw [eltEmpty, Sentence.Realize, Formula.realize_iAlls]
  constructor
  · intro h x
    exact fun hc => (h fun _ => x) ((realize_eltAtom ρ (Sum.inr 0) _).mpr hc)
  · intro h i hc
    exact h (i 0) ((realize_eltAtom ρ (Sum.inr 0) _).mp hc)

theorem realize_valEmpty :
    letI := (powBlock c d).structure₁ (L := L) ρ
    A ⊨ (valEmpty L c d) ↔
      ∀ (i : Fin c) (w : Fin d → A), ¬valOf ρ i w := by
  letI := (powBlock c d).structure₁ (L := L) ρ
  rw [valEmpty, Sentence.Realize, Formula.realize_iInf]
  refine forall_congr' fun i => ?_
  rw [Formula.realize_iAlls]
  constructor
  · intro h w
    exact fun hc => (h w) ((realize_valAtom ρ i (fun j => Sum.inr j) _).mpr hc)
  · intro h u hc
    exact h u ((realize_valAtom ρ i (fun j => Sum.inr j) _).mp hc)

theorem realize_eltUnique :
    letI := (powBlock c d).structure₁ (L := L) ρ
    A ⊨ (eltUnique L c d) ↔
      ∃! x : A, eltOf ρ x := by
  letI := (powBlock c d).structure₁ (L := L) ρ
  rw [eltUnique, Sentence.Realize, Formula.realize_iExsUnique]
  constructor
  · rintro ⟨i, hi, huniq⟩
    refine ⟨i 0, (realize_eltAtom ρ (Sum.inr 0) _).mp hi, fun x hx => ?_⟩
    have := huniq (fun _ => x) ((realize_eltAtom ρ (Sum.inr 0) _).mpr hx)
    exact congrFun this 0
  · rintro ⟨x, hx, huniq⟩
    refine ⟨fun _ => x, (realize_eltAtom ρ (Sum.inr 0) _).mpr hx, fun i hi => ?_⟩
    funext j
    have := huniq (i 0) ((realize_eltAtom ρ (Sum.inr 0) _).mp hi)
    rw [Subsingleton.elim j 0]
    exact this

end Realize


/-! ### The expansion -/

section Expansion

variable (L : Language.{0, 0}) [L.IsRelational] (c d : ℕ)

/-- **The expansion**: two tags, the instance's elements and its `d`-ary
relations, over the extended vocabulary.

Reducible: its block and its vocabulary have to reduce for instance search, or
the structure a domain sentence is read in is not the one the realization lemmas
are stated at. -/
@[reducible] noncomputable def powExpFree : ExpExpansionFree L where
  Tag := Bool
  B := powBlock c d
  E := newLang L
  dom := powDom L c d
  relSentence := powRelSentence L c d
  dom_nonempty := by
    intro A _ _ _
    exact ⟨true, fun _ _ => False, (realize_eltEmpty (L := L) _).mpr fun _ hc => hc⟩

end Expansion


/-! ### The points of the expansion -/

section Points

variable {L : Language.{0, 0}} [L.IsRelational] {c d : ℕ} {A : Type} [L.Structure A]

instance : Nonempty (Fin ((powBlock c d).arity none)) :=
  ⟨⟨0, Nat.zero_lt_one⟩⟩

theorem domHolds_false (ρ : (powBlock c d).Assignment A) :
    ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, ρ) ↔
      (∃! x : A, eltOf ρ x) ∧ ∀ (i : Fin c) (w : Fin d → A), ¬valOf ρ i w := by
  refine Iff.trans ?_ (and_congr (realize_eltUnique (L := L) ρ) (realize_valEmpty (L := L) ρ))
  letI := (powBlock c d).structure₁ (L := L) ρ
  exact Sentence.realize_inf A

theorem domHolds_true (ρ : (powBlock c d).Assignment A) :
    ExpExpansionFree.DomHolds (X := powExpFree L c d) (true, ρ) ↔ ∀ x : A, ¬eltOf ρ x :=
  realize_eltEmpty (L := L) ρ

/-- The assignment naming an original element: its unary variable holds of that
element alone, and it invents nothing. -/
def eltAssign (x : A) : (powBlock c d).Assignment A
  | none, u => ∀ j, u j = x
  | some _, _ => False

/-- The assignment naming an invented value: its unary variable holds of nothing,
and its `d`-ary ones are the value's coordinates. -/
def valAssign (S : Fin c → (Fin d → A) → Prop) : (powBlock c d).Assignment A
  | none, _ => False
  | some i, w => S i w

@[simp]
theorem eltOf_eltAssign (x y : A) : eltOf (c := c) (d := d) (eltAssign x) y ↔ y = x :=
  ⟨fun h => h (Classical.arbitrary _), fun h _ => h⟩

@[simp]
theorem valOf_eltAssign (x : A) (i : Fin c) (w : Fin d → A) :
    ¬valOf (eltAssign (c := c) (d := d) x) i w :=
  id

@[simp]
theorem eltOf_valAssign (S : Fin c → (Fin d → A) → Prop) (y : A) :
    ¬eltOf (c := c) (d := d) (valAssign S) y :=
  id

@[simp]
theorem valOf_valAssign (S : Fin c → (Fin d → A) → Prop) (i : Fin c) (w : Fin d → A) :
    valOf (valAssign S) i w ↔ S i w :=
  Iff.rfl

theorem domHolds_eltAssign (x : A) :
    ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, eltAssign x) :=
  (domHolds_false _).mpr ⟨⟨x, (eltOf_eltAssign x x).mpr rfl,
    fun y hy => (eltOf_eltAssign x y).mp hy⟩, fun i w => valOf_eltAssign x i w⟩

theorem domHolds_valAssign (S : Fin c → (Fin d → A) → Prop) :
    ExpExpansionFree.DomHolds (X := powExpFree L c d) (true, valAssign S) :=
  (domHolds_true _).mpr fun y => eltOf_valAssign S y

end Points


/-! ### The points, counted -/

section Count

variable {L : Language.{0, 0}} [L.IsRelational] {c d : ℕ} {A : Type} [L.Structure A]

instance : Subsingleton (Fin ((powBlock c d).arity none)) :=
  ⟨fun i j => Subsingleton.elim (α := Fin 1) i j⟩

/-- A unary variable is determined by what it holds of: its argument tuples are
constant. -/
theorem assign_false_ext {ρ σ : (powBlock c d).Assignment A}
    (h : ∀ x : A, eltOf ρ x ↔ eltOf σ x) : ρ none = σ none := by
  funext u
  have hu : u = fun _ => u (Classical.arbitrary _) :=
    funext fun j => congrArg u (Subsingleton.elim j _)
  rw [hu]
  exact propext (h _)

/-- The element an original point names. -/
noncomputable def pointElt {ρ : (powBlock c d).Assignment A}
    (h : ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, ρ)) : A :=
  (((domHolds_false (L := L) ρ).mp h).1).choose

theorem eltOf_pointElt {ρ : (powBlock c d).Assignment A}
    (h : ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, ρ)) :
    eltOf ρ (pointElt h) :=
  (((domHolds_false (L := L) ρ).mp h).1).choose_spec.1

theorem eq_pointElt {ρ : (powBlock c d).Assignment A}
    (h : ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, ρ)) {y : A}
    (hy : eltOf ρ y) : y = pointElt h :=
  (((domHolds_false (L := L) ρ).mp h).1).choose_spec.2 y hy

/-- An original point *is* the assignment naming its element. -/
theorem assign_eq_eltAssign {ρ : (powBlock c d).Assignment A}
    (h : ExpExpansionFree.DomHolds (X := powExpFree L c d) (false, ρ)) :
    ρ = eltAssign (pointElt h) := by
  funext b
  cases b with
  | none =>
    exact assign_false_ext fun x =>
      ⟨fun hx => (eltOf_eltAssign _ x).mpr (eq_pointElt h hx),
        fun hx => (eq_pointElt h (eltOf_pointElt h) ▸ (eltOf_eltAssign _ x).mp hx) ▸
          eltOf_pointElt h⟩
  | some i =>
    funext w
    exact propext (iff_of_false (((domHolds_false (L := L) ρ).mp h).2 i w) id)

/-- A new point *is* the assignment naming its value. -/
theorem assign_eq_valAssign {ρ : (powBlock c d).Assignment A}
    (h : ExpExpansionFree.DomHolds (X := powExpFree L c d) (true, ρ)) :
    ρ = valAssign (valOf ρ) := by
  funext b
  cases b with
  | none =>
    exact assign_false_ext fun x =>
      iff_of_false ((domHolds_true (L := L) ρ).mp h x) (eltOf_valAssign _ x)
  | some i => rfl

/-- The point of the expansion carried by an element or by a tuple of `d`-ary
relations. -/
def powPoint : A ⊕ (Fin c → (Fin d → A) → Prop) → (powExpFree L c d).Map A
  | Sum.inl x => ⟨(false, eltAssign x), domHolds_eltAssign x⟩
  | Sum.inr S => ⟨(true, valAssign S), domHolds_valAssign S⟩

theorem powPoint_injective :
    Function.Injective (powPoint (L := L) (c := c) (d := d) (A := A)) := by
  rintro (x | S) (y | T) h
  · refine congrArg Sum.inl ?_
    have hb : eltAssign (c := c) (d := d) x none = eltAssign (c := c) (d := d) y none :=
      congrArg (fun p => p.1.2 none) h
    have hx : eltOf (c := c) (d := d) (eltAssign y) x :=
      Eq.mp (congrFun hb fun _ => x) ((eltOf_eltAssign (c := c) (d := d) x x).mpr rfl)
    exact (eltOf_eltAssign (c := c) (d := d) y x).mp hx
  · exact absurd (congrArg (fun p => p.1.1) h : (false : Bool) = true) Bool.noConfusion
  · exact absurd (congrArg (fun p => p.1.1) h : (true : Bool) = false) Bool.noConfusion
  · refine congrArg Sum.inr (funext fun i => ?_)
    exact (congrArg (fun p => p.1.2 (some i)) h : S i = T i)

theorem powPoint_surjective :
    Function.Surjective (powPoint (L := L) (c := c) (d := d) (A := A)) := by
  rintro ⟨⟨t, ρ⟩, h⟩
  cases t with
  | false =>
    refine ⟨Sum.inl (pointElt h), Subtype.ext (Prod.ext rfl ?_)⟩
    exact (assign_eq_eltAssign h).symm
  | true =>
    refine ⟨Sum.inr (valOf ρ), Subtype.ext (Prod.ext rfl ?_)⟩
    exact (assign_eq_valAssign h).symm

/-- **The points of the expansion are the instance's elements and its `d`-ary
relations**, so there are `n + 2 ^ nᵈ` of them: enough to hold any extension the
bound of `DescriptiveComplexity.SigmaSONewExpDefinable` allows. -/
noncomputable def powPointEquiv :
    A ⊕ (Fin c → (Fin d → A) → Prop) ≃ (powExpFree L c d).Map A :=
  Equiv.ofBijective _ ⟨powPoint_injective, powPoint_surjective⟩


end Count


/-! ### The defining sentences, realized -/

section RelRealize

variable {L : Language.{0, 0}} [L.IsRelational] {c d n : ℕ} {A : Type} [L.Structure A]
variable (ρs : Fin n → (powBlock c d).Assignment A)

omit [L.IsRelational] in
theorem realize_eltAtomAt (k : Fin n) {α : Type} (x : α) (v : α → A) :
    letI := ((powBlock c d).replicate n).structure₁ (L := L)
      ((powBlock c d).replicateAssign ρs)
    (eltAtomAt L c d k x).Realize v ↔ eltOf (ρs k) (v x) := by
  letI := ((powBlock c d).replicate n).structure₁ (L := L) ((powBlock c d).replicateAssign ρs)
  exact Iff.rfl

omit [L.IsRelational] in
open Classical in
/-- **A relation of the instance, at original points**: it holds exactly when it
holds of the elements they name. -/
theorem realize_powRelSentence_base (R : L.Relations n) (τ : Fin n → Bool)
    (hτ : ∀ i, τ i = false) :
    letI := ((powBlock c d).replicate n).structure₁ (L := L)
      ((powBlock c d).replicateAssign ρs)
    A ⊨ powRelSentence L c d (Sum.inl R) τ ↔
      ∃ x : Fin n → A, (∀ i, eltOf (ρs i) (x i)) ∧ RelMap R x := by
  letI := ((powBlock c d).replicate n).structure₁ (L := L) ((powBlock c d).replicateAssign ρs)
  rw [powRelSentence, if_pos hτ, Sentence.Realize, Formula.realize_iExs]
  refine exists_congr fun x => ?_
  rw [Formula.realize_inf, Formula.realize_iInf]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  exact realize_eltAtomAt ρs i (Sum.inr i) _

omit [L.IsRelational] in
open Classical in
/-- **A relation of the instance never holds of an invented point.** -/
theorem powRelSentence_base_eq_bot (R : L.Relations n) (τ : Fin n → Bool)
    (hτ : ¬∀ i, τ i = false) : powRelSentence L c d (Sum.inl R) τ = ⊥ := by
  rw [powRelSentence, if_neg hτ]

omit [L.IsRelational] in
open Classical in
/-- **The marker `old` holds exactly of the original points.** -/
theorem realize_powRelSentence_old (σs : Fin 1 → (powBlock c d).Assignment A)
    (τ : Fin 1 → Bool) :
    letI := ((powBlock c d).replicate 1).structure₁ (L := L)
      ((powBlock c d).replicateAssign σs)
    A ⊨ powRelSentence L c d (Sum.inr Language.oldSym) τ ↔ τ 0 = false := by
  letI := ((powBlock c d).replicate 1).structure₁ (L := L) ((powBlock c d).replicateAssign σs)
  rw [powRelSentence]
  by_cases h : τ 0 = false
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

end RelRealize


/-! ### The expanded structure is the extended structure -/

section Iso

variable {L : Language.{0, 0}} [L.IsRelational] {c d : ℕ} {A : Type} [L.Structure A]

/-- **The extended structure over an arbitrary set of invented values**: the
relations of the instance hold of original elements only, and `old` marks them.
`DescriptiveComplexity.extStructure` is the case `N = Fin m`. -/
@[instance_reducible]
def extOn (L : Language.{0, 0}) [L.IsRelational] (A N : Type) [L.Structure A] :
    (newLang L).Structure (A ⊕ N) :=
  @sumStructure L Language.oldMark (A ⊕ N)
    { funMap := fun f => isEmptyElim f
      RelMap := fun {_k} r x => ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y }
    { RelMap := fun | .old => fun x => IsOld (x 0) }

theorem relMap_extOn_base {N : Type} {k : ℕ} (R : L.Relations k) (x : Fin k → A ⊕ N) :
    letI := extOn L A N
    RelMap (L := newLang L) (Sum.inl R) x ↔
      ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap R y :=
  Iff.rfl

theorem relMap_extOn_old {N : Type} (x : Fin 1 → A ⊕ N) :
    letI := extOn L A N
    RelMap (L := newLang L) (Sum.inr Language.oldSym) x ↔ IsOld (x 0) :=
  Iff.rfl

/-- **The expanded structure is the extended one**: the map sending an element
to its original point and a `d`-ary relation to its new point is an isomorphism
over `DescriptiveComplexity.newLang`. -/
noncomputable def powExtEquiv :
    letI := extOn L A (Fin c → (Fin d → A) → Prop)
    letI := ExpExpansionFree.mapStructure (X := powExpFree L c d) A
    @Language.Equiv (newLang L) (A ⊕ (Fin c → (Fin d → A) → Prop))
      ((powExpFree L c d).Map A) _ _ :=
  letI := extOn L A (Fin c → (Fin d → A) → Prop)
  letI := ExpExpansionFree.mapStructure (X := powExpFree L c d) A
  { toEquiv := powPointEquiv
    map_fun' := fun f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      refine Iff.trans (ExpExpansionFree.relMap_map (X := powExpFree L c d) R _) ?_
      change @Sentence.Realize _ A
          (((powBlock c d).replicate k).structure₁ (L := L)
            ((powBlock c d).replicateAssign fun i => (powPoint (L := L) (x i)).1.2))
          (powRelSentence L c d R fun i => (powPoint (L := L) (x i)).1.1) ↔ RelMap R x
      cases R with
      | inl R =>
        by_cases hall : ∀ i, ∃ a : A, x i = Sum.inl a
        · choose a ha using hall
          have hτ : ∀ i, (powPoint (L := L) (x i)).1.1 = false := fun i => by rw [ha i]; rfl
          rw [realize_powRelSentence_base _ R _ hτ]
          refine Iff.trans ?_ (relMap_extOn_base (L := L) R x).symm
          constructor
          · rintro ⟨z, hz, hR⟩
            refine ⟨z, fun i => ?_, hR⟩
            have := hz i
            rw [ha i] at this ⊢
            exact congrArg Sum.inl ((eltOf_eltAssign (d := d) (a i) (z i)).mp this).symm
          · rintro ⟨y, hy, hR⟩
            refine ⟨y, fun i => ?_, hR⟩
            have hai : a i = y i := Sum.inl_injective ((ha i).symm.trans (hy i))
            rw [ha i]
            exact (eltOf_eltAssign (d := d) (a i) (y i)).mpr hai.symm
        · obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
          have hne : ¬∀ i, (powPoint (L := L) (x i)).1.1 = false := by
            intro ht
            cases hx : x i₀ with
            | inl a => exact hi₀ ⟨a, hx⟩
            | inr S =>
              have := ht i₀
              rw [hx] at this
              exact Bool.noConfusion this
          rw [powRelSentence_base_eq_bot (L := L) (d := d) R _ hne]
          refine Iff.trans ?_ (relMap_extOn_base (L := L) R x).symm
          simp only [Sentence.Realize, Formula.realize_bot, false_iff]
          rintro ⟨y, hy, -⟩
          exact hi₀ ⟨y i₀, hy i₀⟩
      | inr R =>
        cases R with
        | old =>
          rw [realize_powRelSentence_old (L := L) _ _]
          refine Iff.trans ?_ (relMap_extOn_old (L := L) x).symm
          cases hx : x 0 with
          | inl a => exact ⟨fun _ => trivial, fun _ => rfl⟩
          | inr S => exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩ }

end Iso


/-! ### The marked part of an extended universe -/

section Used

variable {L : Language.{0, 0}} [L.IsRelational] {A N : Type} [L.Structure A]

/-- **The original elements together with the marked invented values**: a
substructure, there being nothing to be closed under in a relational
vocabulary. -/
def usedSub (U : N → Prop) :
    letI := extOn L A N
    (newLang L).Substructure (A ⊕ N) :=
  letI := extOn L A N
  { carrier := {x | Sum.elim (fun _ => True) U x}
    fun_mem := fun {_n} f _ _ => isEmptyElim f }

theorem mem_usedSub_iff (U : N → Prop) (x : A ⊕ N) :
    letI := extOn L A N
    x ∈ usedSub (L := L) (A := A) U ↔ Sum.elim (fun _ => True) U x :=
  Iff.rfl

/-- The inclusion of the extension by the marked values into the whole one. -/
def usedPoint (U : N → Prop) : A ⊕ {y : N // U y} → A ⊕ N :=
  Sum.map id Subtype.val

theorem usedPoint_mem (U : N → Prop) (x : A ⊕ {y : N // U y}) :
    letI := extOn L A N
    usedPoint U x ∈ usedSub (L := L) (A := A) U := by
  cases x with
  | inl a => exact trivial
  | inr y => exact y.2

theorem usedPoint_isOld (U : N → Prop) (x : A ⊕ {y : N // U y}) :
    IsOld (usedPoint U x) ↔ IsOld x := by
  cases x <;> exact Iff.rfl

theorem usedPoint_eq_inl (U : N → Prop) (x : A ⊕ {y : N // U y}) (a : A) :
    usedPoint U x = Sum.inl a ↔ x = Sum.inl a := by
  cases x with
  | inl b => exact ⟨fun h => congrArg Sum.inl (Sum.inl_injective h), fun h => congrArg _ h⟩
  | inr y =>
    refine iff_of_false (fun h => ?_) (fun h => ?_)
    · exact Sum.inr_ne_inl (show (Sum.inr y.val : A ⊕ N) = Sum.inl a from h)
    · exact Sum.inr_ne_inl h

/-- **The marked part is the extended universe over the marked values**: the
invented values a sentence uses are the ones it marks, and what it says of them
it says of the extension by those alone. -/
def usedSubEquiv (U : N → Prop) :
    letI := extOn L A {y : N // U y}
    letI := extOn L A N
    @Language.Equiv (newLang L) (A ⊕ {y : N // U y}) (usedSub (L := L) (A := A) U) _
      Substructure.inducedStructure :=
  letI := extOn L A {y : N // U y}
  letI := extOn L A N
  { toEquiv :=
      { toFun := fun x => ⟨usedPoint U x, usedPoint_mem (L := L) U x⟩
        invFun := fun x => match x with
          | ⟨Sum.inl a, _⟩ => Sum.inl a
          | ⟨Sum.inr y, hy⟩ => Sum.inr ⟨y, hy⟩
        left_inv := fun x => match x with
          | Sum.inl _ => rfl
          | Sum.inr _ => rfl
        right_inv := fun x => match x with
          | ⟨Sum.inl _, _⟩ => rfl
          | ⟨Sum.inr _, _⟩ => rfl }
    map_fun' := fun {_n} f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      cases R with
      | inl R =>
        exact exists_congr fun z =>
          and_congr (forall_congr' fun i => usedPoint_eq_inl U (x i) (z i)) Iff.rfl
      | inr R =>
        cases R with
        | old =>
          exact usedPoint_isOld U (x 0) }

end Used


/-! ### The sentence read over the expansion -/

section Sentence

variable (L : Language.{0, 0}) [L.IsRelational] (B : SOBlock)

/-- The unary marker a sentence over the expansion guesses: which invented
values it uses. -/
abbrev markerBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The block guessed over the expansion: the kernel's own variables together
with the marker. -/
abbrev usedBlock : SOBlock := SOBlock.cons B markerBlock

/-- The marker, as a symbol of the guessed vocabulary. -/
abbrev markerSym : (usedBlock B).lang.Relations 1 :=
  ⟨Sum.inr (), rfl⟩

/-- The marker, as a symbol over the extended vocabulary. -/
abbrev markerHostSym : ((newLang L).sum (usedBlock B).lang).Relations 1 :=
  Sum.inr (markerSym B)

/-- `old`, as a symbol over the same vocabulary. -/
abbrev oldUsedSym : ((newLang L).sum (usedBlock B).lang).Relations 1 :=
  Sum.inl (Sum.inr Language.oldSym)

/-- **Every original element is marked**: the guess adds invented values to the
instance, it does not take elements away. -/
noncomputable def oldMarked : ((newLang L).sum (usedBlock B).lang).Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula (oldUsedSym L B) fun _ => Term.var (Sum.inr 0)) ⟹
      Relations.formula (markerHostSym L B) fun _ => Term.var (Sum.inr 0))

/-- The kernel, transported into the merged block. -/
noncomputable def usedKernelHom :
    ((newLang L).sum B.lang) →ᴸ ((newLang L).sum (usedBlock B).lang) :=
  (mergeStep (newLang L) B markerBlock).comp LHom.sumInl

/-- **The sentence read over the expansion**: mark the invented values it uses,
mark every original element, and read the kernel among the marked ones. -/
noncomputable def usedSentence (φ : ((newLang L).sum B.lang).Sentence) :
    ((newLang L).sum (usedBlock B).lang).Sentence :=
  oldMarked L B ⊓ relativizeTo (markerHostSym L B) ((usedKernelHom L B).onSentence φ)

end Sentence


/-! ### The marked part, with the kernel's block -/

section UsedB

variable {L : Language.{0, 0}} [L.IsRelational] {A N : Type} [L.Structure A] {B : SOBlock}

/-- The extended structure together with an assignment of the kernel's block. -/
@[instance_reducible]
def extOnB (ρ : B.Assignment (A ⊕ N)) : ((newLang L).sum B.lang).Structure (A ⊕ N) :=
  @sumStructure (newLang L) B.lang (A ⊕ N) (extOn L A N) (B.structure ρ)

/-- The assignment of the kernel's block on the extension by the marked values,
read off one on the whole extension. -/
def usedRestrict (U : N → Prop) (ρ : B.Assignment (A ⊕ N)) :
    B.Assignment (A ⊕ {y : N // U y}) :=
  fun i x => ρ i fun j => usedPoint U (x j)

/-- The marked part, as a substructure over the vocabulary the kernel is written
in. -/
def usedSubB (U : N → Prop) (ρ : B.Assignment (A ⊕ N)) :
    letI := extOnB (L := L) ρ
    ((newLang L).sum B.lang).Substructure (A ⊕ N) :=
  letI := extOnB (L := L) ρ
  { carrier := {x | Sum.elim (fun _ => True) U x}
    fun_mem := fun {_n} f _ _ => isEmptyElim f }

theorem mem_usedSubB_iff (U : N → Prop) (ρ : B.Assignment (A ⊕ N)) (x : A ⊕ N) :
    letI := extOnB (L := L) ρ
    x ∈ usedSubB (L := L) U ρ ↔ Sum.elim (fun _ => True) U x :=
  Iff.rfl

/-- **The marked part is the extension by the marked values**, over the
vocabulary the kernel is written in: the same identification as
`DescriptiveComplexity.usedSubEquiv`, with the kernel's block riding along by
restriction. -/
def usedSubEquivB (U : N → Prop) (ρ : B.Assignment (A ⊕ N)) :
    letI := extOnB (L := L) (usedRestrict U ρ)
    letI := extOnB (L := L) ρ
    @Language.Equiv ((newLang L).sum B.lang) (A ⊕ {y : N // U y})
      (usedSubB (L := L) U ρ) _ Substructure.inducedStructure :=
  letI := extOnB (L := L) (usedRestrict U ρ)
  letI := extOnB (L := L) ρ
  { toEquiv :=
      { toFun := fun x => ⟨usedPoint U x, usedPoint_mem (L := L) U x⟩
        invFun := fun x => match x with
          | ⟨Sum.inl a, _⟩ => Sum.inl a
          | ⟨Sum.inr y, hy⟩ => Sum.inr ⟨y, hy⟩
        left_inv := fun x => match x with
          | Sum.inl _ => rfl
          | Sum.inr _ => rfl
        right_inv := fun x => match x with
          | ⟨Sum.inl _, _⟩ => rfl
          | ⟨Sum.inr _, _⟩ => rfl }
    map_fun' := fun {_n} f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      cases R with
      | inl R =>
        cases R with
        | inl R =>
          exact exists_congr fun z =>
            and_congr (forall_congr' fun i => usedPoint_eq_inl U (x i) (z i)) Iff.rfl
        | inr R =>
          cases R with
          | old => exact usedPoint_isOld U (x 0)
      | inr R => exact Iff.rfl }

end UsedB


/-! ### The sentence over the expansion, realized -/

section RealizeUsed

variable {L : Language.{0, 0}} [L.IsRelational] {A N : Type} [L.Structure A] {B : SOBlock}

theorem usedPoint_injective (U : N → Prop) :
    Function.Injective (usedPoint (A := A) U) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩

/-- The assignment on the whole extension reproducing one on the extension by
the marked values: a tuple is related exactly when it is the image of a related
tuple. -/
def usedExtend (U : N → Prop) (ρ : B.Assignment (A ⊕ {y : N // U y})) :
    B.Assignment (A ⊕ N) :=
  fun i x => ∃ z, (∀ j, usedPoint U (z j) = x j) ∧ ρ i z

theorem usedRestrict_usedExtend (U : N → Prop) (ρ : B.Assignment (A ⊕ {y : N // U y})) :
    usedRestrict U (usedExtend U ρ) = ρ := by
  funext i x
  refine propext ⟨fun h => ?_, fun h => ⟨x, fun _ => rfl, h⟩⟩
  obtain ⟨z, hz, hρ⟩ := h
  have : z = x := funext fun j => usedPoint_injective U (hz j)
  exact this ▸ hρ

/-- The marker, read off a guessed assignment. -/
def markerOf (ρ' : (usedBlock B).Assignment (A ⊕ N)) : A ⊕ N → Prop :=
  fun x => ρ' (Sum.inr ()) fun _ => x

instance : Subsingleton (Fin ((usedBlock B).arity (Sum.inr ()))) :=
  ⟨fun i j => Subsingleton.elim (α := Fin 1) i j⟩

/-- The marker, as the relativization's guard reads it. -/
theorem markerOf_iff (ρ' : (usedBlock B).Assignment (A ⊕ N)) (z : A ⊕ N) :
    letI := extOnB (L := L) ρ'
    RelMap (markerHostSym L B) ![z] ↔ markerOf ρ' z := by
  letI := extOnB (L := L) ρ'
  refine iff_of_eq (congrArg (ρ' (Sum.inr ())) (funext fun j => ?_))
  rw [Subsingleton.elim j ⟨0, Nat.zero_lt_one⟩]
  rfl

/-- The atom `mark x`, realized. -/
theorem realize_markerAtom (ρ' : (usedBlock B).Assignment (A ⊕ N)) {α : Type} (x : α)
    (v : α → A ⊕ N) :
    letI := extOnB (L := L) ρ'
    ((Relations.formula (markerHostSym L B) fun _ => Term.var x).Realize v) ↔
      markerOf ρ' (v x) :=
  Iff.rfl

/-- The atom `old x`, realized. -/
theorem realize_oldUsedAtom (ρ' : (usedBlock B).Assignment (A ⊕ N)) {α : Type} (x : α)
    (v : α → A ⊕ N) :
    letI := extOnB (L := L) ρ'
    ((Relations.formula (oldUsedSym L B) fun _ => Term.var x).Realize v) ↔
      IsOld (v x) :=
  Iff.rfl

/-- The kernel's part of a guessed assignment. -/
def kernelOf (ρ' : (usedBlock B).Assignment (A ⊕ N)) : B.Assignment (A ⊕ N) :=
  fun i => ρ' (Sum.inl i)

/-- A guessed assignment, from its two parts. -/
def usedJoin (U : N → Prop) (ρ : B.Assignment (A ⊕ {y : N // U y})) :
    (usedBlock B).Assignment (A ⊕ N)
  | Sum.inl i, x => usedExtend U ρ i x
  | Sum.inr _, x => Sum.elim (fun _ => True) U (x ⟨0, Nat.zero_lt_one⟩)

@[simp]
theorem markOf_usedJoin (U : N → Prop) (ρ : B.Assignment (A ⊕ {y : N // U y}))
    (x : A ⊕ N) : markerOf (usedJoin U ρ) x ↔ Sum.elim (fun _ => True) U x :=
  Iff.rfl

@[simp]
theorem blockOf_usedJoin (U : N → Prop) (ρ : B.Assignment (A ⊕ {y : N // U y})) :
    kernelOf (usedJoin U ρ) = usedExtend U ρ :=
  rfl

/-- **The transported kernel says what the kernel says**: the merged block is
the kernel's own variables together with the marker, and the kernel reads only
the former. -/
theorem realize_usedKernelHom {N' : Type} (σ : (usedBlock B).Assignment (A ⊕ N'))
    (φ : ((newLang L).sum B.lang).Sentence) :
    letI := extOnB (L := L) σ
    ((A ⊕ N') ⊨ (usedKernelHom L B).onSentence φ) ↔
      letI := extOnB (L := L) (fun i => σ (Sum.inl i))
      ((A ⊕ N') ⊨ φ) := by
  letI M := A ⊕ N'
  letI instM := extOn L A N'
  letI instB := extOnB (L := L) (fun i => σ (Sum.inl i))
  letI instM' := markerBlock.structure fun i => σ (Sum.inr i)
  letI instBig := @sumStructure ((newLang L).sum B.lang) markerBlock.lang M instB instM'
  letI instU := extOnB (L := L) σ
  have hσ : consAssign (fun i => σ (Sum.inl i)) (fun i => σ (Sum.inr i)) = σ := by
    funext i
    cases i with
    | inl _ => rfl
    | inr _ => rfl
  haveI hexp : @LHom.IsExpansionOn _ _ (mergeStep (newLang L) B markerBlock) M instBig instU := by
    have := mergeStep_isExpansionOn (newLang L) instM B markerBlock
      (fun i => σ (Sum.inl i)) (fun i => σ (Sum.inr i))
    rwa [hσ] at this
  have h1 : (M ⊨ (mergeStep (newLang L) B markerBlock).onSentence
      ((LHom.sumInl : ((newLang L).sum B.lang) →ᴸ
        ((newLang L).sum B.lang).sum markerBlock.lang).onSentence φ)) ↔
      (M ⊨ (LHom.sumInl : ((newLang L).sum B.lang) →ᴸ
        ((newLang L).sum B.lang).sum markerBlock.lang).onSentence φ) :=
    LHom.realize_onSentence (M := M) _ _
  refine Iff.trans ?_ (h1.trans (LHom.realize_onSentence (M := M) _ _))
  rw [usedKernelHom, LHom.onSentence, LHom.onFormula, LHom.comp_onBoundedFormula]
  exact Iff.rfl


/-- **The relativized kernel says what the kernel says on the marked part.** -/
theorem realize_relativized (U : N → Prop) (ρ' : (usedBlock B).Assignment (A ⊕ N))
    (hU : ∀ x : A ⊕ N, Sum.elim (fun _ => True) U x ↔ markerOf ρ' x)
    (φ : ((newLang L).sum B.lang).Sentence) :
    letI := extOnB (L := L) ρ'
    ((A ⊕ N) ⊨ relativizeTo (markerHostSym L B) ((usedKernelHom L B).onSentence φ)) ↔
      letI := extOnB (L := L) (usedRestrict U ρ')
      ((A ⊕ {y : N // U y}) ⊨ (usedKernelHom L B).onSentence φ) := by
  letI := extOnB (L := L) ρ'
  letI := extOnB (L := L) (usedRestrict U ρ')
  have hS : ∀ x : A ⊕ N, x ∈ usedSubB (L := L) (B := usedBlock B) U ρ' ↔
      RelMap (markerHostSym L B) ![x] := fun x => (hU x).trans (markerOf_iff ρ' x).symm
  have h1 := realize_relativizeTo (R := markerHostSym L B)
    (usedSubB (L := L) (B := usedBlock B) U ρ') hS
    ((usedKernelHom L B).onSentence φ) (default : Empty → _) (default : Fin 0 → _)
  have h2 := StrongHomClass.realize_sentence
    (usedSubEquivB (L := L) (B := usedBlock B) U ρ') ((usedKernelHom L B).onSentence φ)
  refine Iff.trans ?_ h2.symm
  refine Iff.trans ?_ h1
  exact iff_of_eq (congrArg₂ (fun a b => BoundedFormula.Realize
    (M := A ⊕ N) (relativizeTo (markerHostSym L B) ((usedKernelHom L B).onSentence φ)) a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))


theorem realize_oldMarked (ρ' : (usedBlock B).Assignment (A ⊕ N)) :
    letI := extOnB (L := L) ρ'
    ((A ⊕ N) ⊨ oldMarked L B) ↔ ∀ a : A, markerOf ρ' (Sum.inl a) := by
  letI := extOnB (L := L) ρ'
  rw [oldMarked, Sentence.Realize, Formula.realize_iAlls]
  constructor
  · intro h a
    exact (realize_markerAtom (L := L) ρ' _ _).mp
      (h (fun _ => Sum.inl a) ((realize_oldUsedAtom (L := L) ρ' _ _).mpr trivial))
  · intro h i hold
    refine (realize_markerAtom (L := L) ρ' (Sum.inr 0) _).mpr ?_
    have hleft : IsOld (i 0) := (realize_oldUsedAtom (L := L) ρ' (Sum.inr 0) _).mp hold
    change markerOf ρ' (i 0)
    match hx : i 0 with
    | Sum.inl a => exact hx ▸ h a
    | Sum.inr y =>
      rw [hx] at hleft
      exact hleft.elim

/-- **The sentence over the expansion, realized**: it holds exactly when the
kernel holds over the extension by *some* set of invented values – the ones the
marker names. -/
theorem sorealize_usedSentence (φ : ((newLang L).sum B.lang).Sentence) :
    letI := extOn L A N
    SORealize (newLang L) (A ⊕ N) [usedBlock B] (usedSentence L B φ) true ↔
      ∃ U : N → Prop,
        letI := extOn L A {y : N // U y}
        SORealize (newLang L) (A ⊕ {y : N // U y}) [B] φ true := by
  letI := extOn L A N
  constructor
  · rintro ⟨ρ', hρ'⟩
    letI := extOnB (L := L) ρ'
    obtain ⟨hguard, hrel⟩ := (Sentence.realize_inf (A ⊕ N)).mp hρ'
    have hg := (realize_oldMarked (L := L) ρ').mp hguard
    letI := extOn L A {y : N // markerOf ρ' (Sum.inr y)}
    refine ⟨fun y => markerOf ρ' (Sum.inr y),
      usedRestrict (fun y => markerOf ρ' (Sum.inr y)) (kernelOf ρ'), ?_⟩
    have hU : ∀ x : A ⊕ N,
        Sum.elim (fun _ => True) (fun y => markerOf ρ' (Sum.inr y)) x ↔ markerOf ρ' x := by
      rintro (a | y)
      · exact ⟨fun _ => hg a, fun _ => trivial⟩
      · exact Iff.rfl
    have h1 := (realize_relativized (L := L) _ ρ' hU φ).mp hrel
    exact (realize_usedKernelHom _ φ).mp h1
  · rintro ⟨U, ρ, hρ⟩
    letI := extOn L A {y : N // U y}
    refine ⟨usedJoin U ρ, ?_⟩
    letI := extOnB (L := L) (usedJoin U ρ)
    have hU : ∀ x : A ⊕ N,
        Sum.elim (fun _ => True) U x ↔ markerOf (usedJoin U ρ) x := fun _ => Iff.rfl
    refine (Sentence.realize_inf (A ⊕ N)).mpr ⟨?_, ?_⟩
    · exact (realize_oldMarked (L := L) (usedJoin U ρ)).mpr fun _ => trivial
    · refine (realize_relativized (L := L) U (usedJoin U ρ) hU φ).mpr ?_
      have hres : (fun i => usedRestrict U (usedJoin U ρ) (Sum.inl i)) = ρ :=
        usedRestrict_usedExtend U ρ
      have hρ2 : letI := extOnB (L := L) ρ
          (A ⊕ {y : N // U y}) ⊨ φ := hρ
      refine (realize_usedKernelHom (usedRestrict U (usedJoin U ρ)) φ).mpr ?_
      rw [hres]
      exact hρ2


end RealizeUsed


/-! ### Bounded invention is definability over the expansion -/

section Final

variable {L : Language.{0, 0}} [L.IsRelational] {c d : ℕ} [NeZero d] {B : SOBlock}

theorem sumCongr_eq_inl {A N N' : Type} (e : N ≃ N') (x : A ⊕ N) (a : A) :
    (Equiv.sumCongr (Equiv.refl A) e) x = Sum.inl a ↔ x = Sum.inl a := by
  cases x with
  | inl b => exact ⟨fun h => congrArg Sum.inl (Sum.inl_injective h), fun h => congrArg _ h⟩
  | inr y =>
    refine iff_of_false (fun h => ?_) (fun h => ?_)
    · exact Sum.inr_ne_inl (show (Sum.inr (e y) : A ⊕ N') = Sum.inl a from h)
    · exact Sum.inr_ne_inl h

theorem sumCongr_isOld {A N N' : Type} (e : N ≃ N') (x : A ⊕ N) :
    IsOld ((Equiv.sumCongr (Equiv.refl A) e) x) ↔ IsOld x := by
  cases x <;> exact Iff.rfl

/-- **Renaming the invented values**: the extended structure depends on them
only through their number. -/
def extOnCongr {A N N' : Type} [L.Structure A] (e : N ≃ N') :
    letI := extOn L A N
    letI := extOn L A N'
    @Language.Equiv (newLang L) (A ⊕ N) (A ⊕ N') _ _ :=
  letI := extOn L A N
  letI := extOn L A N'
  { toEquiv := Equiv.sumCongr (Equiv.refl A) e
    map_fun' := fun f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      cases R with
      | inl R =>
        exact exists_congr fun z =>
          and_congr (forall_congr' fun i => sumCongr_eq_inl e (x i) (z i)) Iff.rfl
      | inr R =>
        cases R with
        | old => exact sumCongr_isOld e (x 0) }

theorem extOn_fin (A : Type) [L.Structure A] (m : ℕ) :
    extOn L A (Fin m) = extStructure L A m := rfl

theorem card_pow {c : ℕ} (α : Type) [Finite α] :
    Nat.card (Fin c → α → Prop) = 2 ^ (c * Nat.card α) := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_prop, Fintype.card_fin, mul_comm c, pow_mul]

/-- **The problem the expansion decides**: the kernel, read over the extension
by the invented values a guess marks. -/
def usedProblem (φ : ((newLang L).sum B.lang).Sentence) : DecisionProblem (newLang L) where
  Holds M _ := SORealize (newLang L) M [usedBlock B] (usedSentence L B φ) true
  iso_invariant e := sorealize_iso e [usedBlock B] _ true

theorem usedProblem_mem_NP (φ : ((newLang L).sum B.lang).Sentence) :
    NP.Mem (usedProblem (L := L) (B := B) φ) :=
  ⟨[usedBlock B], rfl, usedSentence L B φ, fun _ _ _ _ => Iff.rfl⟩

omit [NeZero d] in
/-- **Bounded invention is definability over the expansion**: an
`∃SO[new, exp c d]` definition is an `∃SO` definition over
`DescriptiveComplexity.powExpFree`, which is `∃SO[new, exp c d] ⊆ NEXPTIME`. -/
theorem SigmaSONewExpDefinable.toExpDefinable {P : DecisionProblem L}
    (h : SigmaSONewExpDefinable c d P) : ExpDefinable NP P := by
  classical
  obtain ⟨B, φ, hφ⟩ := h
  refine ExpDefinableFree.expDefinable
    ⟨powExpFree L c d, usedProblem φ, usedProblem_mem_NP φ, ?_⟩
  intro A _ _ _
  letI : Fintype (Fin c → (Fin d → A) → Prop) := Fintype.ofFinite _
  letI := extOn L A (Fin c → (Fin d → A) → Prop)
  letI := ExpExpansionFree.mapStructure (X := powExpFree L c d) A
  have hiso : SORealize (newLang L) (A ⊕ (Fin c → (Fin d → A) → Prop)) [usedBlock B]
        (usedSentence L B φ) true ↔
      usedProblem (L := L) (B := B) φ ((powExpFree L c d).Map A) :=
    sorealize_iso (powExtEquiv (L := L) (c := c) (d := d) (A := A)) [usedBlock B] _ true
  refine ((hφ A).trans ?_).trans hiso
  refine Iff.trans ?_
    (sorealize_usedSentence (L := L) (N := Fin c → (Fin d → A) → Prop) φ).symm
  constructor
  · rintro ⟨m, hm, hρ⟩
    obtain ⟨e⟩ : Nonempty (Fin m ↪ (Fin c → (Fin d → A) → Prop)) := by
      refine Function.Embedding.nonempty_of_card_le ?_
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_pow]
      exact hm
    letI := extOn L A {S : Fin c → (Fin d → A) → Prop // ∃ i, e i = S}
    refine ⟨fun S => ∃ i, e i = S, ?_⟩
    have hq : Fin m ≃ {S : Fin c → (Fin d → A) → Prop // ∃ i, e i = S} :=
      Equiv.ofBijective (fun i => ⟨e i, ⟨i, rfl⟩⟩)
        ⟨fun i j h => e.injective (congrArg Subtype.val h),
          fun z => by obtain ⟨i, hi⟩ := z.2; exact ⟨i, Subtype.ext hi⟩⟩
    exact (sorealize_iso (extOnCongr (L := L) (A := A) hq) [B] φ true).mp hρ
  · rintro ⟨U, hU⟩
    letI : Fintype {S : Fin c → (Fin d → A) → Prop // U S} := Fintype.ofFinite _
    letI := extOn L A {S : Fin c → (Fin d → A) → Prop // U S}
    refine ⟨Fintype.card {S : Fin c → (Fin d → A) → Prop // U S}, ?_, ?_⟩
    · rw [← card_pow (c := c) (Fin d → A), Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective _ Subtype.val_injective
    · exact (sorealize_iso
        (extOnCongr (L := L) (A := A) (Fintype.equivFin _)) [B] φ true).mp hU


end Final


end DescriptiveComplexity
