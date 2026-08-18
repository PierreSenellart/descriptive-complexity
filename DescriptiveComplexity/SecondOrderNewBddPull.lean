/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewBdd
import DescriptiveComplexity.SecondOrderNewPull

/-!
# A bounded extension lives inside the instance's own tuples

`DescriptiveComplexity.SigmaSONewBddDefinable` guesses an extension
`A ⊕ Fin m` with `m ≤ Nat.card (Fin d → A)`. That bound is exactly what it takes
for the extension to be **definable inside `A`**: there are as many invented
values as `d`-tuples, so the invented values can be *taken* to be `d`-tuples,
guessed as one `d`-ary relation.

This file builds the interpretation that says so, in the shape
`DescriptiveComplexity.SecondOrderNewPull` established for the other direction:

* two tags, `false` for the original elements and `true` for the invented ones,
  and dimension `d`;
* an original element is a **diagonal** tuple – so that each one is a single
  point, which is why the dimension has to be positive;
* an invented value is a tuple the guessed relation `N` holds of – so their
  number is `Nat.card {v // N v}`, which is at most `Nat.card (Fin d → A)`
  whatever `N` is, and reaches every value below it for a suitable `N`.

The defining formulas say the rest: a relation of the base vocabulary holds of
interpreted points when they are all original and it holds of the elements on
their diagonals; `old` marks the `false`-tagged points; and a relation variable
of the guessed block is read off the pulled variable selected by the tags, as in
`DescriptiveComplexity.SOBlock.pull`.

What comes out is `DescriptiveComplexity.sorealize_bddPull` – the kernel holds
over some bounded extension exactly when its pullback holds over the instance –
and from it `DescriptiveComplexity.sigmaSONewBddDefinable_iff_sigmaSODefinable`:
**`∃SO[new, d] = NP`**. Read beside `DescriptiveComplexity.SecondOrderNewPull`,
which pulls the *unbounded* logic through an interpretation without ever
eliminating the invention, this is where the bound earns its keep: an
interpretation cannot invent, so the values have to come from the instance, and
the bound is exactly the promise that they can.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The guessed block -/

section Block

variable (d : ℕ) (B : SOBlock)

/-- The block guessed on the instance: the set of invented values, as a `d`-ary
relation, together with the pullback of the kernel's block through the two-tag
interpretation. -/
abbrev bddBlock : SOBlock where
  ι := Unit ⊕ (B.pull Bool d).ι
  arity := Sum.elim (fun _ => d) (B.pull Bool d).arity

/-- The invented-values variable of the guessed block. -/
def newSetSym : (bddBlock d B).lang.Relations d :=
  ⟨Sum.inl (), rfl⟩

/-- The pulled relation variable selected by a tuple of tags. -/
def bddPullSym {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Bool) :
    (bddBlock d B).lang.Relations (B.arity r.1 * d) :=
  ⟨Sum.inr ⟨r.1, fun j => τ (Fin.cast r.2 j)⟩, rfl⟩

end Block

/-! ### The two vocabularies -/

/-- The vocabulary the pulled-back kernel is written in: the instance's own,
together with the guessed relation variables. -/
abbrev bddHost (L : Language.{0, 0}) (d : ℕ) (B : SOBlock) : Language :=
  L.sum (bddBlock d B).lang

/-- The vocabulary the kernel is written in: the extended vocabulary together
with the block's relation variables. -/
abbrev bddTarget (L : Language.{0, 0}) (B : SOBlock) : Language :=
  (newLang L).sum B.lang

/-! ### The interpretation -/

section Interp

variable (L : Language.{0, 0}) (d : ℕ) [NeZero d] (B : SOBlock)

/-- The invented-values variable, as a symbol of the host vocabulary. -/
abbrev newSetHostSym : (bddHost L d B).Relations d :=
  Sum.inr (newSetSym d B)

/-- A pulled relation variable, as a symbol of the host vocabulary. -/
abbrev bddBlockHostSym {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Bool) :
    (bddHost L d B).Relations (B.arity r.1 * d) :=
  Sum.inr (bddPullSym d B r τ)

/-- **The domain formula**: an original point is a diagonal tuple, so that each
element of the instance is one point; an invented point is a tuple the guessed
relation holds of. -/
noncomputable def bddDom : Bool → (bddHost L d B).Formula (Fin d)
  | false => Formula.iInf fun j : Fin d => Term.equal (Term.var j) (Term.var 0)
  | true => Relations.formula (newSetHostSym L d B) fun j => Term.var j

open Classical in
/-- **The defining formulas**: a symbol of the instance's vocabulary holds of
interpreted points exactly when they are all original and it holds of the
elements their diagonals carry, and never of an invented point; `old` marks the
original points; a relation variable of the block is read off the pulled
variable selected by the tags. -/
noncomputable def bddRelF :
    ∀ {k : ℕ}, (bddTarget L B).Relations k → (Fin k → Bool) →
      (bddHost L d B).Formula (Fin k × Fin d)
  | k, Sum.inl (Sum.inl R), τ =>
      if ∀ i : Fin k, τ i = false then
        LHom.sumInl.onFormula (Relations.formula R fun i => Term.var (i, (0 : Fin d)))
      else ⊥
  | _, Sum.inl (Sum.inr r), _τ =>
      match r with
      | .old => if _τ 0 = false then ⊤ else ⊥
  | _, Sum.inr r, τ =>
      Relations.formula (bddBlockHostSym L d B r τ) fun mm =>
        Term.var (Fin.cast r.2 (finProdFinEquiv.symm mm).1, (finProdFinEquiv.symm mm).2)

/-- **The extended universe, interpreted in the instance**: two tags and
dimension `d`, the original elements on the diagonal and the invented values
wherever the guessed relation puts them. -/
noncomputable def bddInterp :
    RelFOInterpretation (bddHost L d B) (bddTarget L B) Bool d where
  relFormula := bddRelF L d B
  domFormula := bddDom L d B

end Interp

/-! ### Realization in the host structure -/

section Realize

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}

/-- **The invented values, as the instance's own tuples**: the `d`-tuples the
guessed variable holds of. Their number is what the bound of
`DescriptiveComplexity.SigmaSONewBddDefinable` allows. -/
def newSet {A : Type} {d : ℕ} {B : SOBlock} (ρ : (bddBlock d B).Assignment A) :
    (Fin d → A) → Prop := fun v => ρ (Sum.inl ()) v

variable (A : Type) [L.Structure A] (ρ : (bddBlock d B).Assignment A)

/-- The host structure: the instance, expanded by the guessed relation
variables. -/
@[instance_reducible]
noncomputable def bddHostStruc : (bddHost L d B).Structure A :=
  @sumStructure L (bddBlock d B).lang A inferInstance ((bddBlock d B).structure ρ)

variable {A ρ}

omit [L.IsRelational] in
theorem realize_bddDom_false (w : Fin d → A) :
    letI := bddHostStruc (L := L) A ρ
    (bddDom L d B false).Realize w ↔ ∀ j : Fin d, w j = w 0 := by
  letI := bddHostStruc (L := L) A ρ
  rw [bddDom, Formula.realize_iInf]
  exact forall_congr' fun j => by rw [Formula.realize_equal]; exact Iff.rfl

omit [L.IsRelational] in
theorem realize_bddDom_true (w : Fin d → A) :
    letI := bddHostStruc (L := L) A ρ
    (bddDom L d B true).Realize w ↔ newSet ρ w := by
  letI := bddHostStruc (L := L) A ρ
  rw [bddDom, Formula.realize_rel]
  exact Iff.rfl

end Realize

/-! ### The extended universe as tagged tuples -/

section Point

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}
variable {A : Type} [L.Structure A] {m : ℕ}

/-- **The tagged tuple representing a point of the extended universe**: an
original element on its diagonal, an invented value where the embedding puts
it. -/
def bddPoint (e : Fin m → Fin d → A) : A ⊕ Fin m → Bool × (Fin d → A)
  | Sum.inl a => (false, fun _ => a)
  | Sum.inr i => (true, e i)

omit [L.IsRelational] [NeZero d] [L.Structure A] in
@[simp]
theorem bddPoint_inl (e : Fin m → Fin d → A) (a : A) :
    bddPoint e (Sum.inl a) = (false, fun _ => a) := rfl

omit [L.IsRelational] [NeZero d] [L.Structure A] in
@[simp]
theorem bddPoint_inr (e : Fin m → Fin d → A) (i : Fin m) :
    bddPoint e (Sum.inr i) = (true, e i) := rfl

omit [L.IsRelational] [L.Structure A] in
theorem bddPoint_injective {e : Fin m → Fin d → A} (he : Function.Injective e) :
    Function.Injective (bddPoint e) := by
  rintro (a | i) (b | j) h
  · exact congrArg Sum.inl (congrFun (congrArg Prod.snd h) 0)
  · exact absurd (congrArg Prod.fst h) (by simp)
  · exact absurd (congrArg Prod.fst h) (by simp)
  · exact congrArg Sum.inr (he (congrArg Prod.snd h))

variable (ρ : (bddBlock d B).Assignment A)

omit [L.IsRelational] in
theorem bddPoint_mem_dom {e : Fin m → Fin d → A}
    (he : ∀ i, newSet ρ (e i)) (x : A ⊕ Fin m) :
    letI := bddHostStruc (L := L) A ρ
    (bddDom L d B (bddPoint e x).1).Realize (bddPoint e x).2 := by
  letI := bddHostStruc (L := L) A ρ
  cases x with
  | inl a => exact (realize_bddDom_false (B := B) _).mpr fun _ => rfl
  | inr i => exact (realize_bddDom_true (B := B) _).mpr (he i)

omit [L.IsRelational] in
theorem bddPoint_surjective {e : Fin m → Fin d → A}
    (hN : ∀ v : Fin d → A, newSet ρ v ↔ ∃ i, e i = v)
    (t : Bool) (w : Fin d → A) :
    letI := bddHostStruc (L := L) A ρ
    (bddDom L d B t).Realize w → ∃ x : A ⊕ Fin m, bddPoint e x = (t, w) := by
  letI := bddHostStruc (L := L) A ρ
  cases t with
  | false =>
    intro hw
    refine ⟨Sum.inl (w 0), Prod.ext rfl ?_⟩
    exact (funext fun j => ((realize_bddDom_false (B := B) w).mp hw j).symm)
  | true =>
    intro hw
    obtain ⟨i, hi⟩ := (hN w).mp ((realize_bddDom_true (B := B) w).mp hw)
    exact ⟨Sum.inr i, Prod.ext rfl hi⟩

/-- **The assignment of the kernel's block on the extended universe**, read off
a guessed assignment on the instance: the pulled variable selected by the tags
of the arguments, at their coordinates. -/
def bddTargetAssign (e : Fin m → Fin d → A) (ρ : (bddBlock d B).Assignment A) :
    B.Assignment (A ⊕ Fin m) :=
  fun i y => ρ (Sum.inr ⟨i, fun k => (bddPoint e (y k)).1⟩)
    fun mm => (bddPoint e (y (finProdFinEquiv.symm mm).1)).2 (finProdFinEquiv.symm mm).2

end Point


/-! ### The defining formulas, realized -/

section RelRealize

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}
variable {A : Type} [L.Structure A] (ρ : (bddBlock d B).Assignment A)

omit [L.IsRelational] in
/-- **A base symbol at original points**: the relation of the instance, at the
elements the diagonals carry. -/
theorem realize_bddRelF_base {k : ℕ} (R : L.Relations k) (a : Fin k → A)
    (w : Fin k × Fin d → A) (hw : ∀ (i : Fin k) (j : Fin d), w (i, j) = a i) :
    letI := bddHostStruc (L := L) A ρ
    (bddRelF L d B (Sum.inl (Sum.inl R)) (fun _ => false)).Realize w ↔ RelMap R a := by
  letI := bddHostStruc (L := L) A ρ
  rw [bddRelF, if_pos (fun _ => rfl), LHom.realize_onFormula, Formula.realize_rel]
  exact iff_of_eq (congrArg _ (funext fun i => hw i 0))

omit [L.IsRelational] [L.Structure A] in
/-- **A base symbol never holds of an invented point.** -/
theorem bddRelF_base_eq_bot {k : ℕ} (R : L.Relations k) (τ : Fin k → Bool)
    (h : ¬∀ i, τ i = false) : bddRelF L d B (Sum.inl (Sum.inl R)) τ = ⊥ := by
  rw [bddRelF, if_neg h]

omit [L.IsRelational] in
/-- **The marker `old` holds exactly of the original points.** -/
theorem realize_bddRelF_old (τ : Fin 1 → Bool) (w : Fin 1 × Fin d → A) :
    letI := bddHostStruc (L := L) A ρ
    (bddRelF L d B (Sum.inl (Sum.inr .old)) τ).Realize w ↔ τ 0 = false := by
  letI := bddHostStruc (L := L) A ρ
  rw [bddRelF]
  by_cases h : τ 0 = false
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

omit [L.IsRelational] in
/-- **A relation variable of the block** is read off the pulled variable
selected by the tags. -/
theorem realize_bddRelF_block {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Bool)
    (w : Fin k × Fin d → A) :
    letI := bddHostStruc (L := L) A ρ
    (bddRelF L d B (Sum.inr r) τ).Realize w ↔
      ρ (Sum.inr ⟨r.1, fun j => τ (Fin.cast r.2 j)⟩)
        (fun mm => w (Fin.cast r.2 (finProdFinEquiv.symm mm).1,
          (finProdFinEquiv.symm mm).2)) := by
  letI := bddHostStruc (L := L) A ρ
  rw [bddRelF, Formula.realize_rel]
  exact Iff.rfl

end RelRealize


/-! ### The interpreted universe *is* the extended universe -/

section Universe

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}
variable {A : Type} [L.Structure A] {m : ℕ}

/-- **The interpreted structure is the extended structure**: the map sending a
point of `A ⊕ Fin m` to its tagged tuple is an isomorphism over the extended
vocabulary, the block being interpreted by
`DescriptiveComplexity.bddTargetAssign`. -/
noncomputable def bddTargetEquiv (e : Fin m → Fin d → A) (he : Function.Injective e)
    (ρ : (bddBlock d B).Assignment A)
    (hN : ∀ v : Fin d → A, newSet ρ v ↔ ∃ i, e i = v) :
    letI := bddHostStruc (L := L) A ρ
    letI := extStructure L A m
    letI := B.structure (bddTargetAssign e ρ)
    @Language.Equiv (bddTarget L B) (A ⊕ Fin m) ((bddInterp L d B).MapRel A) _ _ :=
  letI := bddHostStruc (L := L) A ρ
  letI := extStructure L A m
  letI := B.structure (bddTargetAssign e ρ)
  { toEquiv := Equiv.ofBijective
      (fun x => (⟨bddPoint e x, bddPoint_mem_dom ρ (fun i => (hN (e i)).mpr ⟨i, rfl⟩) x⟩ :
        (bddInterp L d B).MapRel A))
      ⟨fun x y h => bddPoint_injective he (congrArg Subtype.val h),
        fun z => by
          obtain ⟨x, hx⟩ := bddPoint_surjective ρ hN z.1.1 z.1.2 z.2
          exact ⟨x, Subtype.ext hx⟩⟩
    map_fun' := fun f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      rw [RelFOInterpretation.relMap_mapRel]
      cases R with
      | inl R' =>
        cases R' with
        | inl R =>
          by_cases hall : ∀ i, ∃ a : A, x i = Sum.inl a
          · choose a ha using hall
            have hτ : (fun i => (bddPoint e (x i)).1) = fun _ => false :=
              funext fun i => by rw [ha i]; rfl
            change (bddRelF L d B (Sum.inl (Sum.inl R))
              (fun i => (bddPoint e (x i)).1)).Realize
                (fun p => (bddPoint e (x p.1)).2 p.2) ↔ _
            rw [hτ, realize_bddRelF_base ρ R a _ (fun i j => by rw [ha i]; rfl)]
            refine Iff.trans ?_ (relMap_ext_iff (L := L) (A := A) (m := m) R x).symm
            refine ⟨fun h => ⟨a, ha, h⟩, fun h => ?_⟩
            obtain ⟨y, hy, hR⟩ := h
            have hya : y = a := funext fun i => Sum.inl_injective ((hy i).symm.trans (ha i))
            exact hya ▸ hR
          · obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
            have hne : ¬∀ i, (bddPoint e (x i)).1 = false := by
              intro ht
              cases hx : x i₀ with
              | inl a => exact hi₀ ⟨a, hx⟩
              | inr i =>
                have := ht i₀
                rw [hx] at this
                simp at this
            change (bddRelF L d B (Sum.inl (Sum.inl R))
              (fun i => (bddPoint e (x i)).1)).Realize
                (fun p => (bddPoint e (x p.1)).2 p.2) ↔ _
            rw [bddRelF_base_eq_bot (L := L) (d := d) (B := B) R _ hne]
            refine Iff.trans ?_ (relMap_ext_iff (L := L) (A := A) (m := m) R x).symm
            simp only [Formula.realize_bot, false_iff]
            rintro ⟨y, hy, -⟩
            exact hi₀ ⟨y i₀, hy i₀⟩
        | inr R =>
          cases R with
          | old =>
            change (bddRelF L d B (Sum.inl (Sum.inr Language.oldSym))
              (fun i => (bddPoint e (x i)).1)).Realize
                (fun p => (bddPoint e (x p.1)).2 p.2) ↔ _
            rw [realize_bddRelF_old ρ]
            refine Iff.trans ?_ (relMap_ext_old (L := L) (A := A) (m := m) x).symm
            cases hx : x 0 with
            | inl a => exact ⟨fun _ => trivial, fun _ => rfl⟩
            | inr i => exact ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩
      | inr r =>
        change (bddRelF L d B (Sum.inr r) (fun i => (bddPoint e (x i)).1)).Realize
            (fun p => (bddPoint e (x p.1)).2 p.2) ↔ _
        rw [realize_bddRelF_block ρ]
        exact Iff.rfl }

end Universe


/-! ### The guess, read back -/

section Source

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}
variable {A : Type} {m : ℕ}

open Classical in
/-- **The point a tag and a tuple name**: an original element on a diagonal, the
invented value the embedding puts there. Off the embedding's image the value is
junk, which no formula reaches – the domain formula rules those tuples out. -/
noncomputable def bddBack (e : Fin m → Fin d → A) : Bool → (Fin d → A) → A ⊕ Fin m
  | false, v => Sum.inl (v 0)
  | true, v => if h : ∃ i, e i = v then Sum.inr h.choose else Sum.inl (v 0)

theorem bddBack_bddPoint {e : Fin m → Fin d → A} (he : Function.Injective e)
    (x : A ⊕ Fin m) : bddBack e (bddPoint e x).1 (bddPoint e x).2 = x := by
  classical
  cases x with
  | inl a => rfl
  | inr i =>
    have hex : ∃ j, e j = e i := ⟨i, rfl⟩
    change (if h : ∃ j, e j = e i then Sum.inr h.choose else Sum.inl ((e i) 0)) = Sum.inr i
    rw [dif_pos hex]
    exact congrArg Sum.inr (he hex.choose_spec)

open Classical in
/-- **The guessed assignment on the instance**, read off an assignment on the
extended universe: the invented values are the embedding's image, and a pulled
variable holds where the original one holds of the points its tags and
coordinates name. -/
noncomputable def bddSourceAssign (e : Fin m → Fin d → A) (σ : B.Assignment (A ⊕ Fin m)) :
    (bddBlock d B).Assignment A
  | Sum.inl _, v => ∃ i, e i = v
  | Sum.inr p, x => σ p.1 fun k => bddBack e (p.2 k) fun j => x (finProdFinEquiv (k, j))

theorem newSet_bddSourceAssign (e : Fin m → Fin d → A) (σ : B.Assignment (A ⊕ Fin m))
    (v : Fin d → A) : newSet (d := d) (B := B) (bddSourceAssign e σ) v ↔ ∃ i, e i = v :=
  Iff.rfl

/-- **The two assignment transfers are inverse**, in the direction an
existential block needs: what the instance guesses is read back as what was
guessed on the extended universe. -/
theorem bddTargetAssign_bddSourceAssign {e : Fin m → Fin d → A}
    (he : Function.Injective e) (σ : B.Assignment (A ⊕ Fin m)) :
    bddTargetAssign e (bddSourceAssign e σ) = σ := by
  classical
  funext i y
  change σ i (fun k => bddBack e (bddPoint e (y k)).1
    (fun j => (bddPoint e (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).2
      (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2)) = σ i y
  refine congrArg (σ i) (funext fun k => ?_)
  have hco : (fun j => (bddPoint e (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).2
      (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2) = (bddPoint e (y k)).2 :=
    funext fun j => by rw [Equiv.symm_apply_apply]
  rw [hco]
  exact bddBack_bddPoint he (y k)

end Source


/-! ### The kernel, pulled onto the instance -/

section Pull

variable {L : Language.{0, 0}} [L.IsRelational] {d : ℕ} [NeZero d] {B : SOBlock}
variable {A : Type} [L.Structure A] {m : ℕ}

/-- **Sentence transfer**: what the kernel says in the extended universe, it says
in the interpreted one. -/
theorem realize_bddTransfer {e : Fin m → Fin d → A} (he : Function.Injective e)
    (ρ : (bddBlock d B).Assignment A) (hN : ∀ v : Fin d → A, newSet ρ v ↔ ∃ i, e i = v)
    (σ : B.Assignment (A ⊕ Fin m)) (hσ : bddTargetAssign e ρ = σ)
    (φ : (bddTarget L B).Sentence) :
    letI := bddHostStruc (L := L) A ρ
    (@Sentence.Realize (bddTarget L B) (A ⊕ Fin m)
        (@sumStructure (newLang L) B.lang (A ⊕ Fin m) (extStructure L A m)
          (B.structure σ)) φ) ↔ ((bddInterp L d B).MapRel A ⊨ φ) := by
  letI := bddHostStruc (L := L) A ρ
  subst hσ
  letI := extStructure L A m
  letI := B.structure (bddTargetAssign e ρ)
  exact StrongHomClass.realize_sentence (bddTargetEquiv e he ρ hN) φ

/-- **A bounded extension is a guess on the instance**: the kernel holds in
`A ⊕ Fin m` for some `m` below the number of `d`-tuples exactly when its
pullback through `DescriptiveComplexity.bddInterp` holds in `A` itself. The
bound is what makes the forward direction possible – there have to be enough
tuples to embed the invented values in – and the guessed relation is what makes
the backward one, every `d`-ary relation cutting out at most that many. -/
theorem sorealize_bddPull (φ : (bddTarget L B).Sentence) (A : Type) [L.Structure A]
    [Finite A] :
    (∃ m ≤ Nat.card (Fin d → A), SORealize (newLang L) (A ⊕ Fin m) [B] φ true) ↔
      SORealize L A [bddBlock d B] ((bddInterp L d B).pullRelSentence φ) true := by
  classical
  letI : Fintype (Fin d → A) := Fintype.ofFinite _
  constructor
  · rintro ⟨m, hm, σ, hσ⟩
    obtain ⟨e⟩ : Nonempty (Fin m ↪ (Fin d → A)) := by
      refine Function.Embedding.nonempty_of_card_le ?_
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
      exact hm
    refine ⟨bddSourceAssign e σ, ?_⟩
    letI := bddHostStruc (L := L) A (bddSourceAssign e σ)
    refine ((bddInterp L d B).realize_pullRelSentence φ A).mpr ?_
    exact (realize_bddTransfer e.injective (bddSourceAssign e σ)
      (newSet_bddSourceAssign e σ) σ (bddTargetAssign_bddSourceAssign e.injective σ) φ).mp hσ
  · rintro ⟨ρ, hρ⟩
    letI := bddHostStruc (L := L) A ρ
    letI : Fintype {v : Fin d → A // newSet ρ v} := Fintype.ofFinite _
    set S := {v : Fin d → A // newSet ρ v} with hS
    set eq := Fintype.equivFin S with heq
    refine ⟨Fintype.card S, ?_, bddTargetAssign (fun i => (eq.symm i).val) ρ, ?_⟩
    · calc Fintype.card S ≤ Fintype.card (Fin d → A) :=
            Fintype.card_le_of_injective _ Subtype.val_injective
        _ = Nat.card (Fin d → A) := (Nat.card_eq_fintype_card).symm
    · have he : Function.Injective (fun i : Fin (Fintype.card S) => (eq.symm i).val) :=
        fun i j h => eq.symm.injective (Subtype.ext h)
      have hN : ∀ v : Fin d → A, newSet ρ v ↔
          ∃ i : Fin (Fintype.card S), (eq.symm i).val = v := by
        intro v
        constructor
        · intro hv
          exact ⟨eq ⟨v, hv⟩, congrArg Subtype.val (Equiv.symm_apply_apply eq ⟨v, hv⟩)⟩
        · rintro ⟨i, rfl⟩
          exact (eq.symm i).2
      exact (realize_bddTransfer he ρ hN _ rfl φ).mpr
        (((bddInterp L d B).realize_pullRelSentence φ A).mp hρ)

variable {P : DecisionProblem L}

/-- **`∃SO[new, d] ⊆ Σ₁`**: bounded value invention is existential second-order
logic over the instance itself. The invented values are taken to be `d`-tuples,
guessed as one more relation variable, and the kernel is pulled back through the
two-tag interpretation. With
`DescriptiveComplexity.SigmaSODefinable.toNewBdd` this is `∃SO[new, d] = NP`. -/
theorem SigmaSONewBddDefinable.toSigmaSO (h : SigmaSONewBddDefinable d P) :
    SigmaSODefinable 1 P := by
  obtain ⟨B, φ, hφ⟩ := h
  refine ⟨[bddBlock d B], rfl, (bddInterp L d B).pullRelSentence φ, ?_⟩
  intro A _ _ _
  exact (hφ A).trans (sorealize_bddPull φ A)

/-- **`∃SO[new, d] = NP`**, for a positive dimension: bounding the invented
values by the instance's `d`-tuples hands the search space back to the instance,
which is what the parameter was for. -/
theorem sigmaSONewBddDefinable_iff_sigmaSODefinable :
    SigmaSONewBddDefinable d P ↔ SigmaSODefinable 1 P :=
  ⟨SigmaSONewBddDefinable.toSigmaSO, SigmaSODefinable.toNewBdd⟩


end Pull


end DescriptiveComplexity
