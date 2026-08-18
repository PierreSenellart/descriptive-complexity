/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Structure

/-!
# The canonical order is inflationary-definable

The first-order definition of the ordered pebble refinement
(`DescriptiveComplexity.Invariant.OrderedPebble`): a simultaneous induction
`DescriptiveComplexity.ordStepDef` over the base vocabulary, with one
relation variable of arity `k + k` holding the current strict order on
`k`-tuples, whose inflationary stages are exactly the stages of the ordered
refinement (`DescriptiveComplexity.inflStage_ordStepDef`), so whose limit is
the canonical order `DescriptiveComplexity.OrdK` on the `≡ᵏ`-classes.

The initial coloring is the *atomic bit vector* relative to a finite
agreement family `S` (`DescriptiveComplexity.atomColor`): one bit per
coordinate equality and one per relation of `S` at each selection of
coordinates, ordered lexicographically along an arbitrary enumeration of the
bits. Its agreement is atomic agreement
(`DescriptiveComplexity.colorAgree_atomColor`), which plugs the definable
order into the invariant structure's linear order
(`DescriptiveComplexity.invLinearOrder`).

Every piece of one refinement round is written as a first-order formula over
the expanded vocabulary – the bit comparisons as finite lexicographic
disjunctions, membership in a move set with one quantifier, move-set
comparison with a quantified separating tuple and a quantified minimality
check – and each formula builder comes with its realization lemma, so the
step formula realizes one round of `DescriptiveComplexity.ordRefine`
(`DescriptiveComplexity.realize_ordStepF`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {k : ℕ}

/-! ### The order block and its symbol -/

/-- The block of the definable refinement: one relation variable of arity
`k + k`, the current strict order on `k`-tuples. -/
@[reducible]
def ordBlock (k : ℕ) : SOBlock where
  ι := Unit
  arity := fun _ => k + k

/-- The order variable's relation symbol. -/
abbrev ordVSym (L : Language.{0, 0}) (k : ℕ) :
    (L.sum (ordBlock k).lang).Relations (k + k) :=
  Sum.inr ⟨(), rfl⟩

/-- A base relation symbol, in the vocabulary expanded by the order block. -/
abbrev ordBaseSym (L : Language.{0, 0}) (k : ℕ) {l : ℕ} (R : L.Relations l) :
    (L.sum (ordBlock k).lang).Relations l :=
  Sum.inl R

/-- The strict order on `k`-tuples held by an assignment of the order
block. -/
def toPebble {A : Type} (σ : (ordBlock k).Assignment A) : PebbleRel A k :=
  fun u v => σ () (Fin.addCases u v)

/-- Reading a `k + k`-tuple as two `k`-tuples. -/
theorem addCases_comp {A γ : Type} (w : γ → A) (f g : Fin k → γ) :
    (Fin.addCases (fun i => w (f i)) fun i => w (g i)) =
      fun p : Fin (k + k) => w (Fin.addCases f g p) := by
  funext p
  induction p using Fin.addCases with
  | left i => rw [Fin.addCases_left, Fin.addCases_left]
  | right i => rw [Fin.addCases_right, Fin.addCases_right]

/-! ### Formula builders

Each builder takes the tuples it speaks about as *selections of variables*
`Fin k → γ` in an arbitrary context `γ`, so that the builders compose under
the quantifiers `Formula.iExs`/`Formula.iAlls`. -/

section Builders

variable (L k)

/-- The `≺`-atom between two `k`-tuples of variables. -/
noncomputable def ordPrecF {γ : Type} (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  Relations.formula (ordVSym L k) fun p => Term.var (Fin.addCases f g p)

/-- Incomparability of two `k`-tuples of variables. -/
noncomputable def incompF {γ : Type} (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  ∼(ordPrecF L k f g) ⊓ ∼(ordPrecF L k g f)

/-- Membership of the class of `x` in the move set of `f` at pebble `j`:
some value of pebble `j` moves `f` into the class of `x`. -/
noncomputable def inMovesF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f x : Fin k → γ) : (L.sum (ordBlock k).lang).Formula γ :=
  Formula.iExs (Fin 1)
    (incompF L k (fun p => if p = j then Sum.inr 0 else Sum.inl (f p))
      fun p => Sum.inl (x p))

/-- The class of `x` separates the move sets of `f` and `g` at pebble `j`. -/
noncomputable def movesDiffF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g x : Fin k → γ) : (L.sum (ordBlock k).lang).Formula γ :=
  ∼((inMovesF L k j f x).iff (inMovesF L k j g x))

/-- Move-set comparison at pebble `j`: some separating class in the move set
of `f` and not of `g` is minimal among the separating classes. -/
noncomputable def setLessF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g : Fin k → γ) : (L.sum (ordBlock k).lang).Formula γ :=
  Formula.iExs (Fin k)
    (inMovesF L k j (fun p => Sum.inl (f p)) (fun p => Sum.inr p) ⊓
      ∼(inMovesF L k j (fun p => Sum.inl (g p)) fun p => Sum.inr p) ⊓
      Formula.iAlls (Fin k)
        (movesDiffF L k j (fun p => Sum.inl (Sum.inl (f p)))
            (fun p => Sum.inl (Sum.inl (g p))) (fun p => Sum.inr p) ⟹
          ∼(ordPrecF L k (fun p => Sum.inr p) fun p => Sum.inl (Sum.inr p))))

/-- Move-set equality at pebble `j`. -/
noncomputable def movesEqF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g : Fin k → γ) : (L.sum (ordBlock k).lang).Formula γ :=
  Formula.iAlls (Fin k)
    ((inMovesF L k j (fun p => Sum.inl (f p)) fun p => Sum.inr p).iff
      (inMovesF L k j (fun p => Sum.inl (g p)) fun p => Sum.inr p))

/-- Lexicographic move-set comparison over the pebbles. -/
noncomputable def movesLessF {γ : Type} [DecidableEq γ] (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  Formula.iSup fun j : Fin k =>
    (Formula.iInf fun j' : {j' : Fin k // j' < j} =>
      movesEqF L k j'.1 f g) ⊓ setLessF L k j f g

end Builders

/-! ### Realization of the builders -/

section RealizeBuilders

variable {A : Type} [L.Structure A] {σ : (ordBlock k).Assignment A}

theorem realize_ordPrecF {γ : Type} (f g : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (ordPrecF L k f g) w) ↔
      toPebble σ (fun i => w (f i)) fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [ordPrecF, Formula.realize_rel]
  rw [toPebble, addCases_comp]
  exact Iff.rfl

theorem realize_incompF {γ : Type} (f g : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (incompF L k f g) w) ↔
      IncompRel (toPebble σ) (fun i => w (f i)) fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [incompF, Formula.realize_inf, Formula.realize_not, Formula.realize_not,
    realize_ordPrecF, realize_ordPrecF]
  exact Iff.rfl

theorem realize_inMovesF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f x : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (inMovesF L k j f x) w) ↔
      InMoves (toPebble σ) j (fun i => w (f i)) fun i => w (x i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [inMovesF, Formula.realize_iExs]
  constructor
  · rintro ⟨c, hc⟩
    rw [realize_incompF] at hc
    refine ⟨c 0, ?_⟩
    have h1 : (fun i => Sum.elim w c
        ((fun p => if p = j then Sum.inr 0 else Sum.inl (f p)) i)) =
        Function.update (fun i => w (f i)) j (c 0) := by
      funext p
      by_cases hp : p = j
      · subst hp
        simp
      · simp [hp]
    have h2 : (fun i => Sum.elim w c (Sum.inl (x i))) = fun i => w (x i) :=
      rfl
    rw [h1, h2] at hc
    exact hc
  · rintro ⟨a, ha⟩
    refine ⟨fun _ => a, ?_⟩
    rw [realize_incompF]
    have h1 : (fun i => Sum.elim w (fun _ : Fin 1 => a)
        ((fun p => if p = j then Sum.inr 0 else Sum.inl (f p)) i)) =
        Function.update (fun i => w (f i)) j a := by
      funext p
      by_cases hp : p = j
      · subst hp
        simp
      · simp [hp]
    rw [h1]
    exact ha

theorem realize_movesDiffF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g x : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (movesDiffF L k j f g x) w) ↔
      MovesDiff (toPebble σ) j (fun i => w (f i)) (fun i => w (g i))
        fun i => w (x i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [movesDiffF, Formula.realize_not, Formula.realize_iff,
    realize_inMovesF, realize_inMovesF]
  exact Iff.rfl

theorem realize_setLessF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (setLessF L k j f g) w) ↔
      SetLess (toPebble σ) j (fun i => w (f i)) fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [setLessF, Formula.realize_iExs]
  refine exists_congr fun c => ?_
  rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_not,
    realize_inMovesF, realize_inMovesF, Formula.realize_iAlls]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun y hy => ?_⟩
    have h4 := h3 y
    rw [Formula.realize_imp, realize_movesDiffF, Formula.realize_not,
      realize_ordPrecF] at h4
    exact h4 hy
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun y => ?_⟩
    rw [Formula.realize_imp, realize_movesDiffF, Formula.realize_not,
      realize_ordPrecF]
    exact h3 y

theorem realize_movesEqF {γ : Type} [DecidableEq γ] (j : Fin k)
    (f g : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (movesEqF L k j f g) w) ↔
      MovesEq (toPebble σ) j (fun i => w (f i)) fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [movesEqF, Formula.realize_iAlls]
  refine forall_congr' fun c => ?_
  rw [Formula.realize_iff, realize_inMovesF, realize_inMovesF]
  exact Iff.rfl

theorem realize_movesLessF {γ : Type} [DecidableEq γ] (f g : Fin k → γ)
    (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (movesLessF L k f g) w) ↔
      MovesLess (toPebble σ) (fun i => w (f i)) fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [movesLessF, Formula.realize_iSup]
  refine exists_congr fun j => ?_
  rw [Formula.realize_inf, Formula.realize_iInf, realize_setLessF]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h j' hj'
    have := h ⟨j', hj'⟩
    rwa [realize_movesEqF] at this
  · intro h j'
    rw [realize_movesEqF]
    exact h j'.1 j'.2

end RealizeBuilders

/-! ### The atomic bit coloring -/

section Bits

variable (L k) (S : Set (Σ n, L.Relations n))

/-- The bit positions of the atomic coloring: one per coordinate equality,
one per relation of the family at each selection of coordinates. -/
@[reducible]
def BitIdx : Type :=
  (Fin k × Fin k) ⊕ (Σ R : S, Fin R.1.1 → Fin k)

open Classical in
/-- The atomic bit vector of a `k`-tuple. -/
noncomputable def atomBits {A : Type} [L.Structure A] (w : Fin k → A) :
    BitIdx L k S → Bool := fun b =>
  match b with
  | .inl (i, j) => decide (w i = w j)
  | .inr ⟨R, gsel⟩ => decide (RelMap R.1.2 fun p => w (gsel p))

/-- The atomic coloring: the bit vector, compared lexicographically. -/
noncomputable def atomColor {A : Type} [L.Structure A] (w : Fin k → A) :
    Lex (BitIdx L k S → Bool) :=
  toLex (atomBits L k S w)

/-- An arbitrary enumeration order on the bit positions (finitely many, for a
finite family). -/
@[instance_reducible]
noncomputable def bitIdxLinearOrder (hS : S.Finite) :
    LinearOrder (BitIdx L k S) :=
  letI := hS.to_subtype
  finiteLinearOrder _

/-- The lexicographic order on bit vectors. -/
@[instance_reducible]
noncomputable def bitVecLinearOrder (hS : S.Finite) :
    LinearOrder (Lex (BitIdx L k S → Bool)) :=
  letI := hS.to_subtype
  letI := bitIdxLinearOrder L k S hS
  inferInstance

/-- The agreement of the atomic coloring is atomic agreement. -/
theorem colorAgree_atomColor {A : Type} [L.Structure A] :
    colorAgree (atomColor L k S (A := A)) = atomicAgreeOn S A k := by
  classical
  funext u v
  refine propext ?_
  have hcolor : colorAgree (atomColor L k S (A := A)) u v ↔
      ∀ b, atomBits L k S u b = atomBits L k S v b := by
    rw [colorAgree, atomColor, atomColor]
    exact ⟨fun h b => congrFun (toLex.injective h) b,
      fun h => congrArg toLex (funext h)⟩
  rw [hcolor]
  constructor
  · intro h
    constructor
    · intro i j
      have := h (.inl (i, j))
      simpa [atomBits] using this
    · intro l R hR g
      have := h (.inr ⟨⟨⟨l, R⟩, hR⟩, g⟩)
      simpa [atomBits] using this
  · intro h b
    rcases b with ⟨i, j⟩ | ⟨R, gsel⟩
    · simpa [atomBits] using h.1 i j
    · simpa [atomBits] using h.2 R.1.2 R.2 gsel

end Bits

/-! ### The bit comparison formulas -/

section BitFormulas

variable (L k) (S : Set (Σ n, L.Relations n))

/-- The formula of one atomic bit at a selection of variables. -/
noncomputable def atomBitF {γ : Type} (b : BitIdx L k S) (f : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  match b with
  | .inl (i, j) => Term.equal (Term.var (f i)) (Term.var (f j))
  | .inr ⟨R, gsel⟩ =>
      Relations.formula (ordBaseSym L k R.1.2) fun p => Term.var (f (gsel p))

/-- Bit agreement at two selections of variables. -/
noncomputable def atomBitEqF {γ : Type} (b : BitIdx L k S) (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  (atomBitF L k S b f).iff (atomBitF L k S b g)

/-- Lexicographic bit-vector comparison: agree before some bit, `0 < 1` at
it. -/
noncomputable def atomLessF (hS : S.Finite) {γ : Type} (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  letI := hS.to_subtype
  letI := bitIdxLinearOrder L k S hS
  Formula.iSup fun b : BitIdx L k S =>
    (Formula.iInf fun b' : {b' : BitIdx L k S // b' < b} =>
      atomBitEqF L k S b'.1 f g) ⊓
      (∼(atomBitF L k S b f) ⊓ atomBitF L k S b g)

/-- Bit-vector equality. -/
noncomputable def atomEqF (hS : S.Finite) {γ : Type} (f g : Fin k → γ) :
    (L.sum (ordBlock k).lang).Formula γ :=
  letI := hS.to_subtype
  Formula.iInf fun b : BitIdx L k S => atomBitEqF L k S b f g

variable {A : Type} [L.Structure A] {σ : (ordBlock k).Assignment A}

theorem realize_atomBitF {γ : Type} (b : BitIdx L k S) (f : Fin k → γ) (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (atomBitF L k S b f) w) ↔
      atomBits L k S (fun i => w (f i)) b = true := by
  classical
  let := (ordBlock k).structure₁ (L := L) σ
  rcases b with ⟨i, j⟩ | ⟨R, gsel⟩
  · simp only [atomBits, decide_eq_true_eq]
    exact Formula.realize_equal
  · simp only [atomBits, decide_eq_true_eq]
    have h : ∀ (l : ℕ) (Rr : L.Relations l) (sel : Fin l → Fin k),
        ((@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
          (Relations.formula (ordBaseSym L k Rr)
            fun p => Term.var (f (sel p))) w) ↔
          RelMap Rr fun p => w (f (sel p))) := by
      intro l Rr sel
      rw [Formula.realize_rel]
      exact Iff.rfl
    exact h R.1.1 R.1.2 gsel

theorem realize_atomBitEqF {γ : Type} (b : BitIdx L k S) (f g : Fin k → γ)
    (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (atomBitEqF L k S b f g) w) ↔
      atomBits L k S (fun i => w (f i)) b =
        atomBits L k S (fun i => w (g i)) b := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [atomBitEqF, Formula.realize_iff, realize_atomBitF, realize_atomBitF]
  exact Bool.eq_iff_iff.symm

theorem realize_atomLessF (hS : S.Finite) {γ : Type} (f g : Fin k → γ)
    (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (atomLessF L k S hS f g) w) ↔
      (letI := bitVecLinearOrder L k S hS;
        atomColor L k S (fun i => w (f i)) <
          atomColor L k S fun i => w (g i)) := by
  let := (ordBlock k).structure₁ (L := L) σ
  let := hS.to_subtype
  let := bitIdxLinearOrder L k S hS
  rw [atomLessF, Formula.realize_iSup]
  refine exists_congr fun b => ?_
  rw [Formula.realize_inf, Formula.realize_iInf, Formula.realize_inf,
    Formula.realize_not, realize_atomBitF, realize_atomBitF]
  constructor
  · rintro ⟨hpre, hb, hb'⟩
    refine ⟨fun b' hb'' => ?_, ?_⟩
    · have := hpre ⟨b', hb''⟩
      rwa [realize_atomBitEqF] at this
    · rcases Bool.eq_false_or_eq_true (atomBits L k S (fun i => w (f i)) b)
        with hx | hx
      · exact absurd hx hb
      · exact Bool.lt_iff.mpr ⟨hx, hb'⟩
  · rintro ⟨hpre, hlt⟩
    have hlt' := Bool.lt_iff.mp hlt
    refine ⟨fun b' => ?_, fun hx => ?_, hlt'.2⟩
    · rw [realize_atomBitEqF]
      exact hpre b'.1 b'.2
    · have hfalse : atomBits L k S (fun i => w (f i)) b = false := hlt'.1
      rw [hfalse] at hx
      exact Bool.false_ne_true hx

theorem realize_atomEqF (hS : S.Finite) {γ : Type} (f g : Fin k → γ)
    (w : γ → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (atomEqF L k S hS f g) w) ↔
      atomColor L k S (fun i => w (f i)) =
        atomColor L k S fun i => w (g i) := by
  let := (ordBlock k).structure₁ (L := L) σ
  let := hS.to_subtype
  rw [atomEqF, Formula.realize_iInf]
  constructor
  · intro h
    refine congrArg toLex (funext fun b => ?_)
    have := h b
    rwa [realize_atomBitEqF] at this
  · intro h b
    rw [realize_atomBitEqF]
    exact congrFun (toLex.injective h) b

end BitFormulas

/-! ### The step formula and the induction -/

section OrdStepDef

variable (L k) (S : Set (Σ n, L.Relations n))

/-- The step formula of the definable refinement: one round of
`DescriptiveComplexity.ordRefine`, over the current order variable. -/
noncomputable def ordStepF (hS : S.Finite) :
    (L.sum (ordBlock k).lang).Formula (Fin (k + k)) :=
  incompF L k (Fin.castAdd k) (Fin.natAdd k) ⊓
    (atomLessF L k S hS (Fin.castAdd k) (Fin.natAdd k) ⊔
      (atomEqF L k S hS (Fin.castAdd k) (Fin.natAdd k) ⊓
        movesLessF L k (Fin.castAdd k) (Fin.natAdd k)))

/-- **The definable refinement**: the simultaneous induction computing the
canonical order on `k`-tuples, inflationarily. (The output sentence is
irrelevant: the induction is consumed as the first stratum of a
stratification.) -/
noncomputable def ordStepDef (hS : S.Finite) : StepDef L where
  B := ordBlock k
  step := fun _ => ordStepF L k S hS
  out := ⊥

variable {A : Type} [L.Structure A]

theorem realize_ordStepF (hS : S.Finite) {σ : (ordBlock k).Assignment A}
    (w : Fin (k + k) → A) :
    (@Formula.Realize _ A ((ordBlock k).structure₁ (L := L) σ) _
      (ordStepF L k S hS) w) ↔
      (IncompRel (toPebble σ) (fun i => w (Fin.castAdd k i))
          (fun i => w (Fin.natAdd k i)) ∧
        (letI := bitVecLinearOrder L k S hS;
          (atomColor L k S (fun i => w (Fin.castAdd k i)) <
            atomColor L k S fun i => w (Fin.natAdd k i)) ∨
          (atomColor L k S (fun i => w (Fin.castAdd k i)) =
              atomColor L k S (fun i => w (Fin.natAdd k i)) ∧
            MovesLess (toPebble σ) (fun i => w (Fin.castAdd k i))
              fun i => w (Fin.natAdd k i)))) := by
  let := (ordBlock k).structure₁ (L := L) σ
  rw [ordStepF, Formula.realize_inf, Formula.realize_sup, Formula.realize_inf,
    realize_incompF, realize_atomLessF, realize_atomEqF, realize_movesLessF]

/-- **The stages of the definable refinement are the stages of the ordered
pebble refinement.** -/
theorem inflStage_ordStepDef (hS : S.Finite) (n : ℕ) :
    (ordStepDef L k S hS).inflStage A n = fun _ w =>
      (letI := bitVecLinearOrder L k S hS;
        ordStage (atomColor L k S (A := A)) n
          (fun i => w (Fin.castAdd k i)) fun i => w (Fin.natAdd k i)) := by
  let := bitVecLinearOrder L k S hS
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i w
    rw [(ordStepDef L k S hS).inflStage_succ]
    have htp : toPebble ((ordStepDef L k S hS).inflStage A n) =
        ordStage (atomColor L k S (A := A)) n := by
      funext u v
      have h1 : toPebble ((ordStepDef L k S hS).inflStage A n) u v =
          (ordStepDef L k S hS).inflStage A n () (Fin.addCases u v) := rfl
      rw [h1, ih]
      have e1 : (fun i => Fin.addCases (motive := fun _ => A) u v
          (Fin.castAdd k i)) = u := funext fun i => Fin.addCases_left i
      have e2 : (fun i => Fin.addCases (motive := fun _ => A) u v
          (Fin.natAdd k i)) = v := funext fun i => Fin.addCases_right i
      beta_reduce
      rw [e1, e2]
    have hnext : (ordStepDef L k S hS).next
        ((ordStepDef L k S hS).inflStage A n) i w ↔
        (IncompRel (ordStage (atomColor L k S (A := A)) n)
            (fun p => w (Fin.castAdd k p)) (fun p => w (Fin.natAdd k p)) ∧
          ((atomColor L k S (fun p => w (Fin.castAdd k p)) <
              atomColor L k S fun p => w (Fin.natAdd k p)) ∨
            (atomColor L k S (fun p => w (Fin.castAdd k p)) =
                atomColor L k S (fun p => w (Fin.natAdd k p)) ∧
              MovesLess (ordStage (atomColor L k S (A := A)) n)
                (fun p => w (Fin.castAdd k p))
                fun p => w (Fin.natAdd k p)))) := by
      have h0 := realize_ordStepF L k S hS (σ :=
        (ordStepDef L k S hS).inflStage A n) w
      rw [htp] at h0
      exact h0
    refine propext (or_congr (iff_of_eq (congrFun (congrFun ih i) w)) hnext)

/-- **The value of the definable refinement is the canonical order.** -/
theorem toPebble_inflLimit_ordStepDef (hS : S.Finite) :
    toPebble ((ordStepDef L k S hS).inflLimit A) =
      (letI := bitVecLinearOrder L k S hS;
        OrdK (atomColor L k S (A := A))) := by
  let := bitVecLinearOrder L k S hS
  funext u v
  have h1 : toPebble ((ordStepDef L k S hS).inflLimit A) u v ↔
      ∃ n, (ordStepDef L k S hS).inflStage A n () (Fin.addCases u v) :=
    Iff.rfl
  refine propext (h1.trans (exists_congr fun n => ?_))
  rw [congrFun (congrFun (inflStage_ordStepDef L k S hS (A := A) n) ())
    (Fin.addCases u v)]
  have e1 : (fun i => Fin.addCases (motive := fun _ => A) u v
      (Fin.castAdd k i)) = u := funext fun i => Fin.addCases_left i
  have e2 : (fun i => Fin.addCases (motive := fun _ => A) u v
      (Fin.natAdd k i)) = v := funext fun i => Fin.addCases_right i
  beta_reduce
  rw [e1, e2]

end OrdStepDef

end DescriptiveComplexity
