/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import DescriptiveComplexity.FixedPointInflationary
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.SecondOrderBlockHom
import DescriptiveComplexity.Strings.Lax.LeastFixedPoints
import DescriptiveComplexity.Strings.FirstOrder
import DescriptiveComplexity.FixedPointStep

/-!
# Inflationary programs with free variables

A `DescriptiveComplexity.Strings.Prog` is a simultaneous inflationary induction whose
output is a formula with free variables rather than a sentence. Such programs are
closed under the first-order connectives
(`DescriptiveComplexity.Strings.Prog.neg`, `DescriptiveComplexity.Strings.Prog.conj`,
`DescriptiveComplexity.Strings.Prog.ex`, `DescriptiveComplexity.Strings.Prog.rename`)
and under one more operation, which is the point of this file: *iterating* a program
in a relation it reads.

## Iteration

Let `p` be a program over a vocabulary expanded by a relation `X`, whose output has
the arity of `X`. It defines an operator `G` on relations, arbitrary and in particular
not monotone. `DescriptiveComplexity.Strings.Prog.iter` is a program over the vocabulary
without `X` computing `G`, iterated from the empty relation, once per tuple of a given
arity over the universe (`DescriptiveComplexity.Strings.Prog.val_iter`).

The construction runs one copy of `p` per tuple `t`, which plays the part of a round
number: the relation `X` and the block of `p` receive `t` as additional coordinates, so
that a round starts from empty relations. The tuples are walked in lexicographic order
by a *gate* variable. The gate of a tuple opens once the round before it has converged,
a first-order condition since the step formulas of `p` are formulas; at that point the
value of `X` for the new round is written in one step, the output of `p` at the previous
round, and the block of the new round starts running.

The correctness is an invariant of the stages, which says nothing of when things
happen: a round whose gate is open holds the right `X`; a round whose gate is closed
holds nothing; and the block of a round is always one of the stages of `p` at the
right `X`. At the limit, the fixed-point property alone opens every gate, by induction
along the order of the tuples.
-/

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure
open Lax.LeastFixedPoints

/-- An inflationary program whose output has `m` free variables, over the ordered
expansion of `K`. -/
structure Prog (K : Language.{0, 0}) (m : ℕ) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable. -/
  step : ∀ i : B.ι, ((K.sum Language.order).sum B.lang).Formula (Fin (B.arity i))
  /-- The output, read at the limit of the iteration. -/
  out : ((K.sum Language.order).sum B.lang).Formula (Fin m)

namespace Prog

variable {K : Language.{0, 0}} {m : ℕ}

/-- The induction underlying a program; its output sentence is not used. -/
@[reducible] def sd (p : Prog K m) : StepDef (K.sum Language.order) :=
  ⟨p.B, p.step, ⊥⟩

section Val

variable (p : Prog K m) (M : Type) [K.Structure M] [LinearOrder M]

/-- The value of a program on a tuple. -/
def Val (w : Fin m → M) : Prop :=
  @Formula.Realize _ M (p.B.structure₁ (L := K.sum Language.order) (p.sd.inflLimit M)) _ p.out w

end Val

/-! ### The first-order connectives -/

/-- A formula, as a program with an empty block. -/
def ofFormula (φ : (K.sum Language.order).Formula (Fin m)) : Prog K m where
  B := ⟨Empty, Empty.elim⟩
  step := fun i => i.elim
  out := LHom.sumInl.onFormula φ

theorem val_ofFormula (φ : (K.sum Language.order).Formula (Fin m)) (M : Type) [K.Structure M]
    [LinearOrder M] (w : Fin m → M) : (ofFormula φ).Val M w ↔ φ.Realize w := by
  let := (ofFormula φ : Prog K m).B.structure ((ofFormula φ).sd.inflLimit M)
  exact LHom.realize_onFormula (M := M) (φ := LHom.sumInl) φ

/-- The negation of a program. -/
def neg (p : Prog K m) : Prog K m := { p with out := ∼p.out }

theorem val_neg (p : Prog K m) (M : Type) [K.Structure M] [LinearOrder M] (w : Fin m → M) :
    p.neg.Val M w ↔ ¬ p.Val M w :=
  Iff.rfl

/-- A program, its free variables renamed. -/
def rename {m' : ℕ} (p : Prog K m) (f : Fin m → Fin m') : Prog K m' :=
  { p with out := p.out.relabel f }

theorem val_rename {m' : ℕ} (p : Prog K m) (f : Fin m → Fin m') (M : Type) [K.Structure M]
    [LinearOrder M] (w : Fin m' → M) : (p.rename f).Val M w ↔ p.Val M (w ∘ f) := by
  let := p.B.structure₁ (L := K.sum Language.order) (p.sd.inflLimit M)
  change (p.out.relabel f).Realize w ↔ p.out.Realize (w ∘ f)
  exact Formula.realize_relabel

/-- The position of the variables under `DescriptiveComplexity.Strings.Prog.ex`. -/
def exSplit {m : ℕ} : Fin (m + 1) → Fin m ⊕ Unit :=
  Fin.cases (.inr ()) .inl

/-- The existential quantification of variable zero of a program. -/
noncomputable def ex (p : Prog K (m + 1)) : Prog K m :=
  { p with out := Formula.iExs Unit (p.out.relabel exSplit) }

theorem val_ex (p : Prog K (m + 1)) (M : Type) [K.Structure M] [LinearOrder M] (w : Fin m → M) :
    p.ex.Val M w ↔ ∃ a : M, p.Val M (Fin.cons a w) := by
  let := p.B.structure₁ (L := K.sum Language.order) (p.sd.inflLimit M)
  have hc : ∀ i : Unit → M, Sum.elim w i ∘ exSplit = Fin.cons (i ()) w := by
    intro i
    funext x
    refine Fin.cases rfl (fun j => rfl) x
  change (Formula.iExs Unit (p.out.relabel exSplit)).Realize w ↔ ∃ a : M, p.out.Realize _
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Formula.realize_iExs.mp h
    refine ⟨i (), ?_⟩
    have := Formula.realize_relabel.mp hi
    rwa [hc] at this
  · rintro ⟨a, ha⟩
    refine Formula.realize_iExs.mpr ⟨fun _ => a, Formula.realize_relabel.mpr ?_⟩
    rw [hc]
    exact ha

/-! ### Two programs side by side -/

section Par

variable (p q : Prog K m)

/-- The block of two programs side by side. -/
@[reducible] def parB : SOBlock where
  ι := p.B.ι ⊕ q.B.ι
  arity := Sum.elim p.B.arity q.B.arity

/-- The inclusion of the left program. -/
abbrev parL : (K.sum Language.order).sum p.B.lang →ᴸ (K.sum Language.order).sum (parB p q).lang :=
  LHom.sumMap (LHom.id _)
    (SOBlock.homLHom (B := p.B) (B' := parB p q) Sum.inl fun _ => rfl)

/-- The inclusion of the right program. -/
abbrev parR : (K.sum Language.order).sum q.B.lang →ᴸ (K.sum Language.order).sum (parB p q).lang :=
  LHom.sumMap (LHom.id _)
    (SOBlock.homLHom (B := q.B) (B' := parB p q) Sum.inr fun _ => rfl)

/-- The conjunction of two programs: their inductions do not interact. -/
noncomputable def conj : Prog K m where
  B := parB p q
  step
    | .inl i => (parL p q).onFormula (p.step i)
    | .inr i => (parR p q).onFormula (q.step i)
  out := (parL p q).onFormula p.out ⊓ (parR p q).onFormula q.out

variable (M : Type) [K.Structure M] [LinearOrder M]

/-- The left part of an assignment of the two programs. -/
abbrev leftOf (τ : (parB p q).Assignment M) : p.B.Assignment M :=
  SOBlock.homAssign (B := p.B) (B' := parB p q) Sum.inl (fun _ => rfl) τ

/-- The right part of an assignment of the two programs. -/
abbrev rightOf (τ : (parB p q).Assignment M) : q.B.Assignment M :=
  SOBlock.homAssign (B := q.B) (B' := parB p q) Sum.inr (fun _ => rfl) τ

private theorem conj_stage (n : ℕ) :
    leftOf p q M ((conj p q).sd.inflStage M n) = p.sd.inflStage M n ∧
      rightOf p q M ((conj p q).sd.inflStage M n) = q.sd.inflStage M n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [StepDef.inflStage_succ, StepDef.inflStage_succ, StepDef.inflStage_succ]
    constructor
    · rw [← ih.1]
      funext i x
      refine propext (or_congr Iff.rfl ?_)
      exact SOBlock.realize_homFormula (B := p.B) (B' := parB p q) Sum.inl (fun _ => rfl)
        (L := K.sum Language.order) _ (p.step i) _
    · rw [← ih.2]
      funext i x
      refine propext (or_congr Iff.rfl ?_)
      exact SOBlock.realize_homFormula (B := q.B) (B' := parB p q) Sum.inr (fun _ => rfl)
        (L := K.sum Language.order) _ (q.step i) _

private theorem conj_limit :
    leftOf p q M ((conj p q).sd.inflLimit M) = p.sd.inflLimit M ∧
      rightOf p q M ((conj p q).sd.inflLimit M) = q.sd.inflLimit M := by
  constructor
  · funext i x
    refine propext (exists_congr fun n => ?_)
    exact iff_of_eq (congrFun (congrFun (conj_stage p q M n).1 i) x)
  · funext i x
    refine propext (exists_congr fun n => ?_)
    exact iff_of_eq (congrFun (congrFun (conj_stage p q M n).2 i) x)

theorem val_conj (w : Fin m → M) : (conj p q).Val M w ↔ p.Val M w ∧ q.Val M w := by
  let := (parB p q).structure₁ (L := K.sum Language.order) ((conj p q).sd.inflLimit M)
  refine (BoundedFormula.realize_inf (φ := (parL p q).onFormula p.out)).trans (and_congr ?_ ?_)
  · have h := SOBlock.realize_homFormula (B := p.B) (B' := parB p q) Sum.inl (fun _ => rfl)
      (L := K.sum Language.order) ((conj p q).sd.inflLimit M) p.out w
    have e : SOBlock.homAssign (B := p.B) (B' := parB p q) Sum.inl (fun _ => rfl)
        ((conj p q).sd.inflLimit M) = p.sd.inflLimit M := (conj_limit p q M).1
    rw [e] at h
    exact h
  · have h := SOBlock.realize_homFormula (B := q.B) (B' := parB p q) Sum.inr (fun _ => rfl)
      (L := K.sum Language.order) ((conj p q).sd.inflLimit M) q.out w
    have e : SOBlock.homAssign (B := q.B) (B' := parB p q) Sum.inr (fun _ => rfl)
        ((conj p q).sd.inflLimit M) = q.sd.inflLimit M := (conj_limit p q M).2
    rw [e] at h
    exact h

end Par

/-! ### Iteration: the syntax -/

section Iter

variable {K : Language.{0, 0}} [K.IsRelational] {a : ℕ}

/-- A block of one relation variable. -/
@[reducible] def xBlock (a : ℕ) : SOBlock := ⟨Unit, fun _ => a⟩

/-- A vocabulary expanded by one relation symbol. -/
abbrev KX (K : Language.{0, 0}) (a : ℕ) : Language.{0, 0} := K.sum (xBlock a).lang

/-- The new symbol of `KX`. -/
abbrev xSym (K : Language.{0, 0}) (a : ℕ) : (KX K a).Relations a := Sum.inr ⟨(), rfl⟩

variable (p : Prog (KX K a) a) (D : ℕ)

/-- The variables of the iteration: the gate of a round, the value of `X` at a round,
and the block of `p` at a round. -/
@[reducible] def iterB : SOBlock where
  ι := Unit ⊕ Unit ⊕ p.B.ι
  arity
    | .inl _ => D
    | .inr (.inl _) => D + a
    | .inr (.inr i) => D + p.B.arity i

/-- The vocabulary of the formulas of the iteration. -/
abbrev TL : Language.{0, 0} := (K.sum Language.order).sum (iterB p D).lang

/-- The vocabulary of the formulas of `p`. -/
abbrev SL : Language.{0, 0} := ((KX K a).sum Language.order).sum p.B.lang

/-- The value of a round number and a tuple, as terms in a formula with the round
number as free variables. -/
def pinTerms {n mm : ℕ} (args : Fin n → Fin mm) (j : Fin (D + n)) :
    (TL p D).Term (Fin D ⊕ Fin mm) :=
  Fin.addCases (motive := fun _ => (TL p D).Term (Fin D ⊕ Fin mm))
    (fun q => Term.var (.inl q)) (fun i => Term.var (.inr (args i))) j

/-- An atom of `p`, at a round given by the free variables. -/
def pinAtom {mm n : ℕ} : (SL p).Relations n → (Fin n → Fin mm) →
    (TL p D).BoundedFormula (Fin D) mm
  | .inl (.inl (.inl R)), args =>
      BoundedFormula.rel (Sum.inl (Sum.inl R)) fun i => Term.var (.inr (args i))
  | .inl (.inl (.inr Q)), args =>
      BoundedFormula.rel (l := D + n) (Sum.inr ⟨.inr (.inl ()), congrArg (D + ·) Q.2⟩)
        (pinTerms p D args)
  | .inl (.inr R), args =>
      BoundedFormula.rel (Sum.inl (Sum.inr R)) fun i => Term.var (.inr (args i))
  | .inr Q, args =>
      BoundedFormula.rel (l := D + n) (Sum.inr ⟨.inr (.inr Q.1), congrArg (D + ·) Q.2⟩)
        (pinTerms p D args)

/-- The formulas with the round as free variables receive the formulas of `p`. -/
def pinAlg : FOAlg (SL p) where
  T mm := (TL p D).BoundedFormula (Fin D) mm
  truth := ⊤
  equal x y := (Term.var (.inr x)).bdEqual (Term.var (.inr y))
  atom := pinAtom p D
  neg φ := ∼φ
  conj φ ψ := φ ⊓ ψ
  ex φ := φ.ex
  new m := Fin.last m
  shift _ := Fin.castSucc

/-- A formula of `p`, at the round given by the first group of variables. -/
noncomputable def pinF {b : ℕ} (φ : (SL p).Formula (Fin b)) : (TL p D).Formula (Fin D ⊕ Fin b) :=
  ((pinAlg p D).tr φ (Sum.elim id Fin.elim0 : Fin b ⊕ Fin 0 → Fin b)).toFormula

variable {p D}

section Sem

variable {M : Type} [K.Structure M] [LinearOrder M]

/-- The value of `X` at a round. -/
def xAt (τ : (iterB p D).Assignment M) (t : Fin D → M) : (xBlock a).Assignment M :=
  fun _ u => τ (.inr (.inl ())) (Fin.append t u)

/-- The block of `p` at a round. -/
def sAt (τ : (iterB p D).Assignment M) (t : Fin D → M) : p.B.Assignment M :=
  fun i u => τ (.inr (.inr i)) (Fin.append t u)

/-- The structure `p` runs on, for an interpretation of `X`. -/
@[instance_reducible]
def xStr (W : (xBlock a).Assignment M) : (KX K a).Structure M :=
  @sumStructure K (xBlock a).lang M _ ((xBlock a).structure W)

/-- The expansion of that structure by the order. -/
@[instance_reducible]
def xOrd (W : (xBlock a).Assignment M) : ((KX K a).sum Language.order).Structure M :=
  @sumOrderStructure (KX K a) M (xStr W) _

/-- The structure the formulas of `p` read. -/
@[instance_reducible]
def srcStr (W : (xBlock a).Assignment M) (ρ : p.B.Assignment M) : (SL p).Structure M :=
  @SOBlock.structure₁ ((KX K a).sum Language.order) p.B M (xOrd W) ρ

/-- The structure the formulas of the iteration read. -/
@[instance_reducible]
def tgtStr (τ : (iterB p D).Assignment M) : (TL p D).Structure M :=
  (iterB p D).structure₁ (L := K.sum Language.order) τ

private theorem pinTerms_realize (t : Fin D → M) {n mm : ℕ} (args : Fin n → Fin mm) (w : Fin mm → M)
    (τ : (iterB p D).Assignment M) :
    letI := tgtStr τ
    (fun j => (pinTerms p D args j).realize (Sum.elim t w)) = Fin.append t (w ∘ args) := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun i => ?_) j
  · simp [pinTerms]
  · simp [pinTerms]

/-- The semantics of `pinAlg`, at a round. -/
private theorem pinSem (τ : (iterB p D).Assignment M) (t : Fin D → M) :
    letI := srcStr (xAt τ t) (sAt τ t)
    FOAlg.Sem (pinAlg p D) M
      (fun φ w => @BoundedFormula.Realize _ M (tgtStr τ) _ _ φ t w) := by
  let := srcStr (xAt τ t) (sAt τ t)
  let := tgtStr τ
  refine { truth := fun _ => BoundedFormula.realize_top.mpr trivial, equal := ?_, atom := ?_,
           neg := fun _ _ => BoundedFormula.realize_not, conj := fun _ _ _ =>
            BoundedFormula.realize_inf, ex := ?_, ext := ?_ }
  · intro m x y w
    exact BoundedFormula.realize_bdEqual _ _
  · rintro m n ((((R | Q)) | R) | Q) args w
    · exact Iff.rfl
    · obtain ⟨⟨⟩, rfl⟩ := Q
      refine iff_of_eq (congrArg (τ (.inr (.inl ()))) ?_)
      refine (pinTerms_realize t args w τ).trans ?_
      rfl
    · exact Iff.rfl
    · obtain ⟨i, rfl⟩ := Q
      refine iff_of_eq (congrArg (τ (.inr (.inr i))) ?_)
      refine (pinTerms_realize t args w τ).trans ?_
      rfl
  · intro m φ w
    refine BoundedFormula.realize_ex.trans ?_
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨Fin.snoc w x, funext fun i => Fin.snoc_castSucc (α := fun _ => M) x w i, hx⟩
    · rintro ⟨w', rfl, hx⟩
      refine ⟨w' (Fin.last m), ?_⟩
      have h : (Fin.snoc (w' ∘ Fin.castSucc) (w' (Fin.last m)) : Fin (m + 1) → M) = w' :=
        Fin.snoc_init_self w'
      exact (congrArg (fun z => BoundedFormula.Realize φ t z) h).mpr hx
  · intro m x w
    exact ⟨Fin.snoc w x, funext fun i => Fin.snoc_castSucc (α := fun _ => M) x w i,
      Fin.snoc_last (α := fun _ => M) x w⟩

/-- **A formula of `p` read at a round.** -/
private theorem realize_pinF (τ : (iterB p D).Assignment M) (t : Fin D → M) {b : ℕ}
    (φ : (SL p).Formula (Fin b)) (u : Fin b → M) :
    @Formula.Realize _ M (tgtStr τ) _ (pinF p D φ) (Sum.elim t u) ↔
      @Formula.Realize _ M (srcStr (xAt τ t) (sAt τ t)) _ φ u := by
  let := srcStr (xAt τ t) (sAt τ t)
  let := tgtStr τ
  refine (BoundedFormula.realize_toFormula _ _).trans ?_
  refine ((pinSem τ t).eval_tr φ (Sum.elim id Fin.elim0) u).trans ?_
  exact iff_of_eq (congrArg₂ _ rfl (Subsingleton.elim _ _))

/-! ### Iteration: the program -/

variable (p D)

/-- The relation symbol of the gate. -/
abbrev gateSym : (TL p D).Relations D := Sum.inr ⟨.inl (), rfl⟩

/-- A variable of the block at a round, as a formula on the round and the tuple. -/
noncomputable def sAtomF (i : p.B.ι) : (TL p D).Formula (Fin D ⊕ Fin (p.B.arity i)) :=
  Relations.formula (n := D + p.B.arity i) (Sum.inr ⟨.inr (.inr i), rfl⟩)
    (Fin.addCases (motive := fun _ => (TL p D).Term (Fin D ⊕ Fin (p.B.arity i)))
      (fun q => Term.var (.inl q)) (fun j => Term.var (.inr j)))

/-- The gate of the tuple held by `sel`. -/
noncomputable def gateF {γ : Type} (sel : Fin D → γ) : (TL p D).Formula γ :=
  Relations.formula (gateSym p D) fun q => Term.var (sel q)

/-- The round is converged: the step formulas of `p` add nothing to it. -/
noncomputable def convF : (TL p D).Formula (Fin D) :=
  Formula.iInf fun i : p.B.ι =>
    Formula.iAlls (Fin (p.B.arity i))
      (((pinF p D (p.step i)).imp (sAtomF p D i)) : (TL p D).Formula (Fin D ⊕ Fin (p.B.arity i)))

/-- The tuples in `Fin D` are the successor of a round whose gate is open and which has
converged, and `ψ` holds of that round. -/
noncomputable def firedF {γ : Type} (ψ : (TL p D).Formula (Fin D ⊕ γ)) :
    (TL p D).Formula (Fin D ⊕ γ) :=
  Formula.iExs (Fin D)
    (LHom.sumInl.onFormula (succTupF (L := K) (fun q => .inr q) (fun q => .inl (.inl q))) ⊓
      gateF p D (fun q => .inr q) ⊓
      (convF p D).relabel (fun q => .inr q) ⊓
      ψ.relabel (Sum.elim (fun q => .inr q) (fun g => .inl (.inr g))))

/-- The splitting of the variables of a formula with a round. -/
def roundSplit {b : ℕ} : Fin D ⊕ Fin b → Fin (D + b) :=
  Sum.elim (Fin.castAdd b) (Fin.natAdd D)

/-- **The iteration**, whose rounds are the tuples of arity `D`. -/
noncomputable def iter : Prog K a where
  B := iterB p D
  step
    | .inl _ =>
        LHom.sumInl.onFormula (minTupF (L := K) (id : Fin D → Fin D)) ⊔
          (firedF p D (γ := Empty) ⊤).relabel (Sum.elim id Empty.elim)
    | .inr (.inl _) => (firedF p D (pinF p D p.out)).relabel (roundSplit D)
    | .inr (.inr i) =>
        (gateF p D (fun q => .inl q) ⊓ pinF p D (p.step i)).relabel (roundSplit D)
  out :=
    Formula.iExs (Fin D)
      (LHom.sumInl.onFormula (maxTupF (L := K) (fun q => .inr q)) ⊓
        (pinF p D p.out).relabel (Sum.elim (fun q => .inr q) .inl))

variable {p D}

/-! ### Iteration: what the formulas say -/

section Reads

variable (τ : (iterB p D).Assignment M)

omit [K.IsRelational] in
theorem realize_lift {γ : Type} (φ : (K.sum Language.order).Formula γ) (v : γ → M) :
    @Formula.Realize _ M (tgtStr τ) _ (LHom.sumInl.onFormula φ) v ↔ φ.Realize v := by
  let := (iterB p D).structure τ
  exact LHom.realize_onFormula (M := M) (φ := LHom.sumInl) φ

omit [K.IsRelational] in
theorem realize_gateF {γ : Type} (sel : Fin D → γ) (v : γ → M) :
    @Formula.Realize _ M (tgtStr τ) _ (gateF p D sel) v ↔ τ (.inl ()) (v ∘ sel) :=
  Iff.rfl

/-- A round has converged, as a statement about the assignment. -/
private def Conv (t : Fin D → M) : Prop :=
  ∀ (i : p.B.ι) (u : Fin (p.B.arity i) → M),
    @Formula.Realize _ M (srcStr (xAt τ t) (sAt τ t)) _ (p.step i) u → sAt τ t i u

private theorem realize_sAtomF (t : Fin D → M) (i : p.B.ι) (u : Fin (p.B.arity i) → M) :
    @Formula.Realize _ M (tgtStr τ) _ (sAtomF p D i) (Sum.elim t u) ↔ sAt τ t i u := by
  let := tgtStr τ
  refine iff_of_eq (congrArg (τ (.inr (.inr i))) ?_)
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j <;> simp

private theorem realize_convF (t : Fin D → M) :
    @Formula.Realize _ M (tgtStr τ) _ (convF p D) t ↔ Conv τ t := by
  let := tgtStr τ
  refine BoundedFormula.realize_iInf.trans (forall_congr' fun i => ?_)
  refine Formula.realize_iAlls.trans (forall_congr' fun u => ?_)
  refine BoundedFormula.realize_imp.trans ?_
  exact imp_congr (realize_pinF τ t (p.step i) u) (realize_sAtomF τ t i u)

private theorem realize_firedF {γ : Type} (ψ : (TL p D).Formula (Fin D ⊕ γ)) (t : Fin D → M) (g :
    γ → M) :
    @Formula.Realize _ M (tgtStr τ) _ (firedF p D ψ) (Sum.elim t g) ↔
      ∃ t' : Fin D → M, TupSucc t' t ∧ τ (.inl ()) t' ∧ Conv τ t' ∧
        @Formula.Realize _ M (tgtStr τ) _ ψ (Sum.elim t' g) := by
  let := tgtStr τ
  refine Formula.realize_iExs.trans (exists_congr fun t' => ?_)
  have hsucc := (realize_lift (p := p) (D := D) τ
    (succTupF (L := K) (fun q => (Sum.inr q : (Fin D ⊕ γ) ⊕ Fin D)) (fun q => .inl (.inl q)))
    (Sum.elim (Sum.elim t g) t')).trans (realize_succTupF _ _)
  have hconv : ((convF p D).relabel (fun q => (Sum.inr q : (Fin D ⊕ γ) ⊕ Fin D))).Realize
      (Sum.elim (Sum.elim t g) t') ↔ Conv τ t' :=
    Formula.realize_relabel.trans (realize_convF τ t')
  have hψ : (ψ.relabel (Sum.elim (fun q => (Sum.inr q : (Fin D ⊕ γ) ⊕ Fin D))
      (fun g => .inl (.inr g)))).Realize (Sum.elim (Sum.elim t g) t') ↔
      ψ.Realize (Sum.elim t' g) := by
    refine Formula.realize_relabel.trans (iff_of_eq (congrArg _ ?_))
    funext x
    cases x <;> rfl
  refine (BoundedFormula.realize_inf).trans ?_
  refine (and_congr (BoundedFormula.realize_inf.trans (and_congr
    (BoundedFormula.realize_inf.trans (and_congr hsucc Iff.rfl)) hconv)) hψ).trans ?_
  tauto

end Reads

omit [LinearOrder M] in
/-- The value of `roundSplit` on a tuple. -/
theorem elim_roundSplit {b : ℕ} (x : Fin (D + b) → M) :
    x ∘ roundSplit (b := b) D = Sum.elim (x ∘ Fin.castAdd b) (x ∘ Fin.natAdd D) := by
  funext y
  cases y <;> rfl

/-! ### Iteration: one step of the program -/

section Next

variable (τ : (iterB p D).Assignment M)

/-- The gate of a round opens at the successor of a converged round whose gate is open. -/
private def Fire (t : Fin D → M) : Prop :=
  ∃ t' : Fin D → M, TupSucc t' t ∧ τ (.inl ()) t' ∧ Conv τ t'

omit [K.IsRelational] in
theorem realize_relabel' {α β : Type} (φ : (TL p D).Formula α) (g : α → β) (v : β → M) :
    @Formula.Realize _ M (tgtStr τ) _ (φ.relabel g) v ↔
      @Formula.Realize _ M (tgtStr τ) _ φ (v ∘ g) := by
  let := tgtStr τ
  exact Formula.realize_relabel

private theorem next_gate (t : Fin D → M) :
    (iter p D).sd.next τ (.inl ()) t ↔ (∀ (q : Fin D) (a : M), t q ≤ a) ∨ Fire τ t := by
  let := tgtStr τ
  change @Formula.Realize _ M (tgtStr τ) _
    (LHom.sumInl.onFormula (minTupF (L := K) (id : Fin D → Fin D)) ⊔
      (firedF p D (γ := Empty) ⊤).relabel (Sum.elim id Empty.elim)) t ↔ _
  refine BoundedFormula.realize_sup.trans (or_congr ?_ ?_)
  · exact (realize_lift τ (minTupF (L := K) (id : Fin D → Fin D)) t).trans (realize_minTupF _)
  · have hc : t ∘ Sum.elim (id : Fin D → Fin D) (Empty.elim : Empty → Fin D) =
        Sum.elim t Empty.elim := by
      funext x; cases x with
      | inl _ => rfl
      | inr e => exact e.elim
    refine (realize_relabel' τ _ _ t).trans ?_
    rw [hc]
    refine (realize_firedF τ ⊤ t _).trans ?_
    refine exists_congr fun t' => ?_
    have : (⊤ : (TL p D).Formula (Fin D ⊕ Empty)).Realize (Sum.elim t' Empty.elim) :=
      BoundedFormula.realize_top.mpr trivial
    tauto

private theorem next_x (x : Fin (D + a) → M) :
    (iter p D).sd.next τ (.inr (.inl ())) x ↔
      ∃ t' : Fin D → M, TupSucc t' (x ∘ Fin.castAdd a) ∧ τ (.inl ()) t' ∧ Conv τ t' ∧
        @Formula.Realize _ M (srcStr (xAt τ t') (sAt τ t')) _ p.out (x ∘ Fin.natAdd D) := by
  let := tgtStr τ
  change @Formula.Realize _ M (tgtStr τ) _
    ((firedF p D (pinF p D p.out)).relabel (roundSplit D)) x ↔ _
  refine (realize_relabel' τ _ _ x).trans ?_
  rw [elim_roundSplit]
  refine (realize_firedF τ _ _ _).trans (exists_congr fun t' => ?_)
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  exact realize_pinF τ t' p.out _

private theorem next_s (i : p.B.ι) (x : Fin (D + p.B.arity i) → M) :
    (iter p D).sd.next τ (.inr (.inr i)) x ↔
      τ (.inl ()) (x ∘ Fin.castAdd _) ∧
        @Formula.Realize _ M (srcStr (xAt τ (x ∘ Fin.castAdd _)) (sAt τ (x ∘ Fin.castAdd _))) _
          (p.step i) (x ∘ Fin.natAdd D) := by
  let := tgtStr τ
  change @Formula.Realize _ M (tgtStr τ) _
    ((gateF p D (fun q => .inl q) ⊓ pinF p D (p.step i)).relabel (roundSplit D)) x ↔ _
  refine (realize_relabel' τ _ _ x).trans ?_
  rw [elim_roundSplit]
  refine BoundedFormula.realize_inf.trans (and_congr ?_ ?_)
  · exact realize_gateF τ _ _
  · exact realize_pinF τ _ (p.step i) _

end Next

/-! ### Iteration: the invariant -/

variable [Finite M]

variable (p) in
/-- The operator a program defines on the relation it reads. -/
def gOp (W : Set (Fin a → M)) : Set (Fin a → M) :=
  {u | @Prog.Val _ _ p M (xStr fun _ => W) _ u}

variable (p) in
/-- A stage of a program, at a value of the relation it reads. -/
private def pStage (W : Set (Fin a → M)) (j : ℕ) : p.B.Assignment M :=
  @StepDef.inflStage _ p.sd M (xOrd fun _ => W) j

variable (p) in
/-- The limit of a program, at a value of the relation it reads. -/
private def pLim (W : Set (Fin a → M)) : p.B.Assignment M :=
  @StepDef.inflLimit _ p.sd M (xOrd fun _ => W)

/-- The value of `X` at a round, as a set. -/
def xSet (τ : (iterB p D).Assignment M) (t : Fin D → M) : Set (Fin a → M) :=
  {u | τ (.inr (.inl ())) (Fin.append t u)}

omit [K.IsRelational] [K.Structure M] [LinearOrder M] [Finite M] in
theorem xAt_eq (τ : (iterB p D).Assignment M) (t : Fin D → M) :
    xAt τ t = fun _ => xSet τ t := rfl

/-- The rank of a round. -/
noncomputable def rd (t : Fin D → M) : ℕ := orank (toLex t)

variable (p) in
/-- The invariant of the stages of the iteration. -/
private def Inv (τ : (iterB p D).Assignment M) : Prop :=
  ∀ t : Fin D → M,
    (τ (.inl ()) t → xSet τ t = stage (gOp p) (rd t)) ∧
    (¬ τ (.inl ()) t → xSet τ t = ∅) ∧
    ∃ j, sAt τ t = pStage p (stage (gOp p) (rd t)) j

set_option linter.unusedSectionVars false in
/-- A converged round holds the limit of `p`, and the output of `p` read there is the next
stage of the operator. -/
private theorem read_out_of_conv {τ : (iterB p D).Assignment M} (hI : Inv p τ) {t : Fin D → M}
    (hg : τ (.inl ()) t) (hc : Conv τ t) :
    sAt τ t = pLim p (stage (gOp p) (rd t)) ∧
      ∀ u, @Formula.Realize _ M (srcStr (xAt τ t) (sAt τ t)) _ p.out u ↔
        u ∈ stage (gOp p) (rd t + 1) := by
  obtain ⟨hx, -, j, hj⟩ := hI t
  have hxt := hx hg
  have hlim : sAt τ t = pLim p (stage (gOp p) (rd t)) := by
    let := xOrd (K := K) (M := M) (a := a) fun _ => stage (gOp p) (rd t)
    have hfix : Function.IsFixedPt p.sd.inflStep (p.sd.inflStage M j) := by
      funext i y
      refine propext ⟨?_, Or.inl⟩
      rintro (h | h)
      · exact h
      · have := hc i y
        rw [hj, xAt_eq, hxt] at this
        exact this h
    rw [hj]
    funext i y
    refine propext ⟨fun h => ⟨j, h⟩, ?_⟩
    rintro ⟨n, hn⟩
    rcases le_total n j with hle | hle
    · exact p.sd.inflStage_le_of_le hle i y hn
    · have := iterate_eq_of_isFixedPt hfix hle
      exact (congrFun (congrFun this i) y).mp hn
  refine ⟨hlim, fun u => ?_⟩
  rw [xAt_eq, hxt, hlim]
  exact Iff.rfl

omit [Finite M] in
/-- Two predecessors of a round are equal. -/
theorem tupSucc_unique {t₁ t₂ t : Fin D → M} (h₁ : TupSucc t₁ t) (h₂ : TupSucc t₂ t) : t₁ = t₂ :=
  toLex.injective ((tupSucc_iff_covBy.mp h₁).unique_left (tupSucc_iff_covBy.mp h₂))

/-- The rank goes up by one along a successor. -/
theorem rd_succ {t₁ t : Fin D → M} (h : TupSucc t₁ t) : rd t = rd t₁ + 1 :=
  orank_covBy (tupSucc_iff_covBy.mp h)

set_option linter.unusedSectionVars false in
private theorem rd_min {t : Fin D → M} (h : ∀ (q : Fin D) (a : M), t q ≤ a) : rd t = 0 :=
  orank_eq_zero (tup_isBot_iff.mpr h)

/-- **The invariant is preserved by a step of the iteration.** -/
private theorem inv_step {τ : (iterB p D).Assignment M} (hI : Inv p τ) :
    Inv p ((iter p D).sd.inflStep τ) := by
  intro t
  set τ' := (iter p D).sd.inflStep τ with hτ'
  have hgate : τ' (.inl ()) t ↔ τ (.inl ()) t ∨ (∀ (q : Fin D) (a : M), t q ≤ a) ∨ Fire τ t :=
    or_congr Iff.rfl (next_gate τ t)
  have hxmem : ∀ u, u ∈ xSet τ' t ↔ u ∈ xSet τ t ∨ (Fire τ t ∧ u ∈ stage (gOp p) (rd t)) := by
    intro u
    refine or_congr Iff.rfl ((next_x τ _).trans ?_)
    have h₁ : Fin.append t u ∘ Fin.castAdd a = t := funext fun q => Fin.append_left t u q
    have h₂ : Fin.append t u ∘ Fin.natAdd D = u := funext fun q => Fin.append_right t u q
    rw [h₁, h₂]
    constructor
    · rintro ⟨t', hs, hg, hc, hr⟩
      refine ⟨⟨t', hs, hg, hc⟩, ?_⟩
      rw [rd_succ hs]
      exact ((read_out_of_conv hI hg hc).2 u).mp hr
    · rintro ⟨⟨t', hs, hg, hc⟩, hu⟩
      refine ⟨t', hs, hg, hc, ((read_out_of_conv hI hg hc).2 u).mpr ?_⟩
      rw [← rd_succ hs]
      exact hu
  obtain ⟨hx, hn, j, hj⟩ := hI t
  refine ⟨fun hg' => ?_, fun hg' => ?_, ?_⟩
  · ext u
    rw [hxmem]
    by_cases hF : Fire τ t
    · by_cases hg : τ (.inl ()) t
      · rw [hx hg]; tauto
      · rw [hn hg]
        simp [hF]
    · have hu : u ∈ xSet τ t ↔ u ∈ stage (gOp p) (rd t) := by
        by_cases hg : τ (.inl ()) t
        · rw [hx hg]
        · have hmin : ∀ (q : Fin D) (a : M), t q ≤ a := by
            rcases hgate.mp hg' with h | h | h
            · exact (hg h).elim
            · exact h
            · exact (hF h).elim
          rw [hn hg, rd_min hmin]
          exact Iff.rfl
      tauto
  · have hng : ¬ τ (.inl ()) t := fun h => hg' (hgate.mpr (Or.inl h))
    have hnF : ¬ Fire τ t := fun h => hg' (hgate.mpr (Or.inr (Or.inr h)))
    ext u
    rw [hxmem, hn hng]
    simp [hnF]
  · have hs : ∀ (i : p.B.ι) (u : Fin (p.B.arity i) → M),
        sAt τ' t i u ↔ sAt τ t i u ∨
          (τ (.inl ()) t ∧ @Formula.Realize _ M (srcStr (xAt τ t) (sAt τ t)) _ (p.step i) u) := by
      intro i u
      refine or_congr Iff.rfl ((next_s τ i _).trans ?_)
      have h₁ : Fin.append t u ∘ Fin.castAdd (p.B.arity i) = t :=
        funext fun q => Fin.append_left t u q
      have h₂ : Fin.append t u ∘ Fin.natAdd D = u := funext fun q => Fin.append_right t u q
      rw [h₁, h₂]
    by_cases hg : τ (.inl ()) t
    · refine ⟨j + 1, ?_⟩
      funext i u
      refine propext ((hs i u).trans ?_)
      have hxt := hx hg
      rw [xAt_eq, hxt, hj]
      let := xOrd (K := K) (M := M) (a := a) fun _ => stage (gOp p) (rd t)
      have hst : pStage (M := M) p (stage (gOp p) (rd t)) (j + 1) =
          p.sd.inflStep (pStage (M := M) p (stage (gOp p) (rd t)) j) :=
        p.sd.inflStage_succ j
      rw [hst]
      refine or_congr Iff.rfl ?_
      exact and_iff_right hg
    · refine ⟨j, ?_⟩
      rw [← hj]
      funext i u
      refine propext ((hs i u).trans ?_)
      simp [hg]

/-- The invariant holds of every stage of the iteration. -/
private theorem inv_stage (n : ℕ) : Inv p ((iter p D).sd.inflStage M n) := by
  induction n with
  | zero =>
    intro t
    refine ⟨fun h => h.elim, fun _ => rfl, 0, rfl⟩
  | succ n ih =>
    rw [StepDef.inflStage_succ]
    exact inv_step ih

/-- The invariant holds of the limit of the iteration. -/
private theorem inv_limit : Inv p ((iter p D).sd.inflLimit M) := by
  rw [(iter p D).sd.inflLimit_eq_stage_card M]
  exact inv_stage _

/-- At the limit, every round is converged as soon as its gate is open. -/
private theorem conv_limit {t : Fin D → M} (hg : (iter p D).sd.inflLimit M (.inl ()) t) :
    Conv ((iter p D).sd.inflLimit M) t := by
  intro i u hr
  have hfix := (iter p D).sd.isFixedPt_inflStep_inflLimit M
  have : (iter p D).sd.inflStep ((iter p D).sd.inflLimit M) (.inr (.inr i)) (Fin.append t u) := by
    refine Or.inr ((next_s _ i _).mpr ?_)
    have h₁ : Fin.append t u ∘ Fin.castAdd (p.B.arity i) = t :=
      funext fun q => Fin.append_left t u q
    have h₂ : Fin.append t u ∘ Fin.natAdd D = u := funext fun q => Fin.append_right t u q
    rw [h₁, h₂]
    exact ⟨hg, hr⟩
  rw [hfix] at this
  exact this

/-- **At the limit, every gate is open**, by induction along the order of the rounds. -/
private theorem iterLimit_gate (t : Fin D → M) : (iter p D).sd.inflLimit M (.inl ()) t := by
  have hfix := (iter p D).sd.isFixedPt_inflStep_inflLimit M
  have hnext : ∀ t, (iter p D).sd.next ((iter p D).sd.inflLimit M) (.inl ()) t →
      (iter p D).sd.inflLimit M (.inl ()) t := by
    intro t h
    have : (iter p D).sd.inflStep ((iter p D).sd.inflLimit M) (.inl ()) t := Or.inr h
    rw [hfix] at this
    exact this
  have key : ∀ z : Lex (Fin D → M), (iter p D).sd.inflLimit M (.inl ()) (ofLex z) := by
    refine order_induction ?_ ?_
    · intro z hz
      exact hnext _ ((next_gate _ _).mpr (Or.inl (tup_isBot_iff.mp hz)))
    · intro w z hwz hnb hw
      refine hnext _ ((next_gate _ _).mpr (Or.inr ⟨ofLex w, ?_, hw, conv_limit hw⟩))
      exact tupSucc_iff_covBy.mpr ⟨hwz, fun a h₁ h₂ => hnb a ⟨h₁, h₂⟩⟩
  exact key (toLex t)

/-- **The value of the iteration**: the operator of `p`, iterated once per round from the
empty relation. -/
theorem val_iter [Nonempty M] (u : Fin a → M) :
    (iter p D).Val M u ↔ u ∈ stage (gOp p) (Nat.card (Fin D → M)) := by
  let τ := (iter p D).sd.inflLimit M
  let := tgtStr τ
  have hread : ∀ t, @Formula.Realize _ M (tgtStr τ) _ (pinF p D p.out) (Sum.elim t u) ↔
      u ∈ stage (gOp p) (rd t + 1) := by
    intro t
    refine (realize_pinF τ t p.out u).trans ?_
    have hg := iterLimit_gate (p := p) (D := D) (M := M) t
    exact (read_out_of_conv inv_limit hg (conv_limit hg)).2 u
  have hout : (iter p D).Val M u ↔ ∃ t : Fin D → M, (∀ (q : Fin D) (a : M), a ≤ t q) ∧
      u ∈ stage (gOp p) (rd t + 1) := by
    change @Formula.Realize _ M (tgtStr τ) _
      (Formula.iExs (Fin D)
        (LHom.sumInl.onFormula (maxTupF (L := K) (fun q => .inr q)) ⊓
          (pinF p D p.out).relabel (Sum.elim (fun q => .inr q) .inl))) u ↔ _
    refine Formula.realize_iExs.trans (exists_congr fun t => ?_)
    refine BoundedFormula.realize_inf.trans (and_congr ?_ ?_)
    · exact (realize_lift τ (maxTupF (L := K) (fun q => (Sum.inr q : Fin a ⊕ Fin D)))
        (Sum.elim u t)).trans (realize_maxTupF _)
    · refine (realize_relabel' τ _ _ _).trans ?_
      have : Sum.elim u t ∘ Sum.elim (fun q => (Sum.inr q : Fin a ⊕ Fin D)) Sum.inl =
          Sum.elim t u := by
        funext x; cases x <;> rfl
      rw [this]
      exact hread t
  have hcard : ∀ t : Fin D → M, (∀ (q : Fin D) (a : M), a ≤ t q) →
      rd t + 1 = Nat.card (Fin D → M) := by
    intro t ht
    have h₁ := orank_isTop (tup_isTop_iff.mpr ht)
    have h₂ : Nat.card (Lex (Fin D → M)) = Nat.card (Fin D → M) :=
      Nat.card_congr toLex.symm
    have h₃ : 0 < Nat.card (Fin D → M) := Nat.card_pos
    change orank (toLex t) + 1 = _
    omega
  rw [hout]
  constructor
  · rintro ⟨t, ht, hu⟩
    rwa [hcard t ht] at hu
  · intro hu
    obtain ⟨m₀, hm₀⟩ := Finite.exists_max (id : M → M)
    refine ⟨fun _ => m₀, fun _ a => hm₀ a, ?_⟩
    rwa [hcard (fun _ => m₀) fun _ a => hm₀ a]

end Sem

end Iter

end Prog

end DescriptiveComplexity.Strings
