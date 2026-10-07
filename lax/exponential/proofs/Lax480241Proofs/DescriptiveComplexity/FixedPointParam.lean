/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.FixedPointInflationaryLFP
import Lax480241Proofs.DescriptiveComplexity.SecondOrderNew
import Lax480241Proofs.DescriptiveComplexity.SecondOrderParam
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.IFPDefinable
end Lax480241Proofs.DescriptiveComplexity.IFPDefinable

namespace Lax480241Proofs.DescriptiveComplexity.SOBlock
end Lax480241Proofs.DescriptiveComplexity.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity.StepDef
end Lax480241Proofs.DescriptiveComplexity.StepDef

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Interpretations (sumOrderStructure)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (IFPDefinable StepDef)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (botAssign)
end Lax904597.SecondOrder.SOBlock

/-!
# An element, quantified in front of a fixed point

**The theorem**: FO(≤, IFP) definability – hence membership in
`DescriptiveComplexity.PTIME` – is closed under **existential quantification
over one element** (`DescriptiveComplexity.IFPDefinable.exElement`,
`DescriptiveComplexity.mem_PTIME_exElement`). If a problem `R` over the
vocabulary extended by a mark (`DescriptiveComplexity.newLang`, one unary
symbol) is definable, then so is “**some** element, marked, makes `R` hold”.

Semantically there is nothing to it – trying every element multiplies the work
by the size of the instance – but a fixed point cannot be *restarted* once per
element, so the construction runs all of them at once: every relation variable
gains one argument, the **parameter**, and every stage of the iteration then
holds the stages of all the instances side by side
(`DescriptiveComplexity.StepDef.inflStage_param`). The mark is not a symbol of
the new vocabulary any more, so the atom `old t` becomes the equation
`t = parameter`; nothing else changes, since the universe does not.

This is the deterministic counterpart of
`DescriptiveComplexity.SOTCDefinable.exBlock`, which prefixes a walk with a
guessed *relation* – a walk may guess, a fixed point may not, and one element
is what a fixed point can afford instead.

## Where it is used

`DescriptiveComplexity.Exponential.FreeTime`: the order-free reading of
`DescriptiveComplexity.EXPTIME` has to say “some copy of the order-guessing
expansion answers yes”, and a copy is named by any one of its points.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### A structure with one marked element -/

/-- The mark of a single element, as a structure over the marking
vocabulary. -/
@[instance_reducible]
def oneMark {N : Type} (c : N) : Lax480241Proofs.Foreign.FirstOrder.Language.oldMark.Structure N where
  RelMap := fun {_} r => match r with
    | .old => fun x => x 0 = c

/-- **The instance with one element marked**, over
`DescriptiveComplexity.newLang`. -/
@[instance_reducible]
def markOne (L : Language.{0, 0}) {N : Type} [inst : L.Structure N] (c : N) :
    (newLang L).Structure N :=
  @sumStructure L Lax480241Proofs.Foreign.FirstOrder.Language.oldMark N inst (oneMark c)

/-! ### The block, with a parameter argument

`DescriptiveComplexity.SOBlock.withParam` and its reading at a parameter are
`SecondOrderParam.lean`'s; what is here is the one statement that mentions the
empty assignment. -/

variable {N : Type}

theorem SOBlock.atParam_bot (B : Lax904597.SecondOrder.SOBlock) (c : N) :
    B.atParam (B.withParam.botAssign N) c = B.botAssign N :=
  rfl

end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock

export Lax480241Proofs.DescriptiveComplexity.SOBlock (atParam_bot)

end Lax904597.SecondOrder.SOBlock

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

/-! ### The parameter substitution -/

section Lift

variable (B : Lax904597.SecondOrder.SOBlock) {α : Type} (p : α)

/-- A term of the marked vocabulary, read in the parameterized one: over
relational vocabularies a term is a variable, so there is nothing to do. -/
def paramTerm {β : Type} :
    (((newLang L).sum Language.order).sum B.lang).Term β →
      ((L.sum Language.order).sum B.withParam.lang).Term β
  | .var x => .var x
  | .func f _ => isEmptyElim f

/-- **The parameter substitution**: the mark becomes “equal to the parameter”,
every fixed-point variable takes the parameter as a further argument, and
everything else is left alone – in particular the quantifiers, the universe
being unchanged. -/
def paramLift :
    ∀ {n : ℕ}, (((newLang L).sum Language.order).sum B.lang).BoundedFormula α n →
      ((L.sum Language.order).sum B.withParam.lang).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (paramTerm B t₁) (paramTerm B t₂)
  | _, .rel r ts =>
    match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => .rel (Sum.inl (Sum.inl s)) fun i => paramTerm B (ts i)
    | Sum.inl (Sum.inl (Sum.inr .old)) =>
        .equal (paramTerm B (ts 0)) (Term.var (Sum.inl p))
    | Sum.inl (Sum.inr .le) => .rel (Sum.inl (Sum.inr .le)) fun i => paramTerm B (ts i)
    | Sum.inr b =>
        .rel (Sum.inr (B.paramSym b))
          (Fin.cons (Term.var (Sum.inl p)) fun i => paramTerm B (ts i))
  | _, .imp φ ψ => .imp (paramLift φ) (paramLift ψ)
  | _, .all φ => .all (paramLift φ)

variable {B p}

variable [L.Structure N] [LinearOrder N]

theorem realize_paramTerm {β : Type} (ρ : B.withParam.Assignment N) (c : N)
    (v : β → N) (t : (((newLang L).sum Language.order).sum B.lang).Term β) :
    letI := (B.withParam.structure₁ (L := L.sum Language.order) ρ)
    letI := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) B N
      (@Lax904597.Interpretations.sumOrderStructure (newLang L) N (markOne L c) _) (B.atParam ρ c)
    (paramTerm B t).realize v = t.realize v := by
  match t with
  | .var _ => rfl
  | .func f _ => exact isEmptyElim f

/-- **The parameter substitution is correct**: read at an assignment of the
extended block, the substituted formula says what the original said in the
instance whose mark is the parameter, at that assignment read at the
parameter. -/
theorem realize_paramLift (ρ : B.withParam.Assignment N) (v : α → N) :
    ∀ {n : ℕ} (φ : (((newLang L).sum Language.order).sum B.lang).BoundedFormula α n)
      (xs : Fin n → N),
      letI := (B.withParam.structure₁ (L := L.sum Language.order) ρ)
      letI := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) B N
        (@Lax904597.Interpretations.sumOrderStructure (newLang L) N (markOne L (v p)) _) (B.atParam ρ (v p))
      ((paramLift B p φ).Realize v xs ↔ φ.Realize v xs) := by
  let := (B.withParam.structure₁ (L := L.sum Language.order) ρ)
  let := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) B N
    (@Lax904597.Interpretations.sumOrderStructure (newLang L) N (markOne L (v p)) _) (B.atParam ρ (v p))
  intro n φ
  induction φ with
  | falsum => exact fun _ => Iff.rfl
  | equal t₁ t₂ =>
    intro xs
    change ((paramTerm B t₁).realize _ = (paramTerm B t₂).realize _) ↔ _
    rw [realize_paramTerm ρ (v p) _ t₁, realize_paramTerm ρ (v p) _ t₂]
    exact Iff.rfl
  | @rel _ l r ts =>
    intro xs
    have hts : ∀ i, (paramTerm B (ts i)).realize (Sum.elim v xs) =
        (ts i).realize (Sum.elim v xs) := fun i => realize_paramTerm ρ (v p) _ (ts i)
    match l, r with
    | _, Sum.inl (Sum.inl (Sum.inl s)) =>
      change (@RelMap ((L.sum Language.order).sum B.withParam.lang) N _ _
        (Sum.inl (Sum.inl s)) fun i => (paramTerm B (ts i)).realize (Sum.elim v xs)) ↔ _
      rw [funext hts]
      exact Iff.rfl
    | _, Sum.inl (Sum.inl (Sum.inr .old)) =>
      change ((paramTerm B (ts 0)).realize (Sum.elim v xs) =
        (Term.var (Sum.inl p) : ((L.sum Language.order).sum
          B.withParam.lang).Term _).realize (Sum.elim v xs)) ↔ _
      rw [hts 0]
      exact Iff.rfl
    | _, Sum.inl (Sum.inr .le) =>
      change (@RelMap ((L.sum Language.order).sum B.withParam.lang) N _ _
        (Sum.inl (Sum.inr Language.orderRel.le))
        fun i => (paramTerm B (ts i)).realize (Sum.elim v xs)) ↔ _
      rw [funext hts]
      exact Iff.rfl
    | _, Sum.inr b =>
      set w : Fin _ → N := fun j =>
        ((Fin.cons (Term.var (Sum.inl p)) fun i => paramTerm B (ts i) : Fin _ →
          ((L.sum Language.order).sum B.withParam.lang).Term _) j).realize
            (Sum.elim v xs) with hwdef
      have hw0 : w 0 = v p := by
        rw [hwdef]
        simp only [Fin.cons_zero, Term.realize_var, Sum.elim_inl]
      have hwsucc : ∀ i, w i.succ = (ts i).realize (Sum.elim v xs) := by
        intro i
        rw [hwdef]
        simp only [Fin.cons_succ]
        exact hts i
      change (@RelMap ((L.sum Language.order).sum B.withParam.lang) N _ _
          (Sum.inr (B.paramSym b)) w) ↔
        (@RelMap (((newLang L).sum Language.order).sum B.lang) N _ _ (Sum.inr b)
          fun i => (ts i).realize (Sum.elim v xs))
      rw [← funext hwsucc]
      exact SOBlock.relMap_paramSym B ρ (v p) b w hw0
  | imp φ ψ ihφ ihψ =>
    intro xs
    exact Iff.trans BoundedFormula.realize_imp
      (Iff.trans (imp_congr (ihφ xs) (ihψ xs)) BoundedFormula.realize_imp.symm)
  | all φ ih =>
    intro xs
    refine Iff.trans BoundedFormula.realize_all (Iff.trans ?_ BoundedFormula.realize_all.symm)
    exact forall_congr' fun x => ih (Fin.snoc xs x)

end Lift

/-- **The instance with one element marked**, ordered. -/
@[instance_reducible]
def markOneOrd (L : Language.{0, 0}) {N : Type} [L.Structure N] [LinearOrder N] (c : N) :
    ((newLang L).sum Language.order).Structure N :=
  @Lax904597.Interpretations.sumOrderStructure (newLang L) N (markOne L c) _

/-! ### The definition, run at every parameter at once -/

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

/-- **Every instance at once**: the same simultaneous induction, every relation
variable carrying the parameter as a further argument, and the output
existentially quantified over it. -/
noncomputable def param : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order) where
  B := d.B.withParam
  step i := paramLift d.B (0 : Fin (d.B.arity i + 1)) ((d.step i).relabel Fin.succ)
  out := Formula.iExs (Fin 1) (paramLift d.B (Sum.inr 0) (d.out.relabel Sum.inl))

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- One step of the parameterized definition, read at a parameter, is one step
of the original in the instance that parameter marks. -/
theorem next_param (ρ : d.param.B.Assignment N) (c : N) :
    d.B.atParam (d.param.next ρ) c = @Lax535992.InflationaryFixedPoint.StepDef.next _ d N (markOneOrd L c) (d.B.atParam ρ c) := by
  funext i x
  let := markOneOrd L c
  let := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L c)
    (d.B.atParam ρ c)
  let := d.param.B.structure₁ (L := L.sum Language.order) ρ
  have hcomp : ((Fin.cons c x : Fin (d.B.arity i + 1) → N) ∘ Fin.succ) = x := by
    funext j
    simp
  have h := realize_paramLift (B := d.B) (p := (0 : Fin (d.B.arity i + 1))) ρ (Fin.cons c x)
    ((d.step i).relabel Fin.succ) (default : Fin 0 → N)
  refine propext (Iff.trans h ?_)
  refine Iff.trans Formula.realize_relabel ?_
  rw [hcomp]
  exact Iff.rfl

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (next_param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- The inflationary step of the parameterized definition, read at a
parameter. -/
theorem inflStep_param (ρ : d.param.B.Assignment N) (c : N) :
    d.B.atParam (d.param.inflStep ρ) c =
      @Lax535992.InflationaryFixedPoint.StepDef.inflStep _ d N (markOneOrd L c) (d.B.atParam ρ c) := by
  funext i x
  exact congrArg (Or (d.B.atParam ρ c i x)) (congrFun (congrFun (next_param (d := d) ρ c) i) x)

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (inflStep_param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- **Every stage of the parameterized iteration holds the stages of all the
instances side by side.** -/
theorem inflStage_param (c : N) :
    ∀ k : ℕ, d.B.atParam (d.param.inflStage N k) c =
      @Lax535992.InflationaryFixedPoint.StepDef.inflStage _ d N (markOneOrd L c) k := by
  intro k
  induction k with
  | zero => exact d.B.atParam_bot c
  | succ k ih =>
    have hstep : d.param.inflStage N (k + 1) = d.param.inflStep (d.param.inflStage N k) :=
      d.param.inflStage_succ k
    have hstepd : @Lax535992.InflationaryFixedPoint.StepDef.inflStage _ d N (markOneOrd L c) (k + 1) =
        @Lax535992.InflationaryFixedPoint.StepDef.inflStep _ d N (markOneOrd L c) (@Lax535992.InflationaryFixedPoint.StepDef.inflStage _ d N (markOneOrd L c) k) :=
      @StepDef.inflStage_succ _ d N (markOneOrd L c) k
    rw [hstep, hstepd, ← ih]
    exact inflStep_param (d := d) (d.param.inflStage N k) c

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (inflStage_param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- The value of the parameterized iteration, read at a parameter. -/
theorem inflLimit_param (c : N) :
    d.B.atParam (d.param.inflLimit N) c = @Lax535992.InflationaryFixedPoint.StepDef.inflLimit _ d N (markOneOrd L c) := by
  funext i x
  exact propext (exists_congr fun k =>
    iff_of_eq (congrFun (congrFun (inflStage_param (d := d) c k) i) x))

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (inflLimit_param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- **What the parameterized definition defines**: the original one, at some
element of the instance. -/
theorem ifpHolds_param :
    d.param.IFPHolds N ↔ ∃ c : N, @Lax535992.InflationaryFixedPoint.StepDef.IFPHolds _ d N (markOneOrd L c) := by
  let := d.param.B.structure₁ (L := L.sum Language.order) (d.param.inflLimit N)
  have hcongr : ∀ (c : N) (σ τ : d.B.Assignment N), σ = τ →
      (@Sentence.Realize _ N (@Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) d.B N
          (markOneOrd L c) σ) d.out ↔
        @Sentence.Realize _ N (@Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) d.B N
          (markOneOrd L c) τ) d.out) := by
    rintro c σ τ rfl
    exact Iff.rfl
  refine Iff.trans Formula.realize_iExs ?_
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w 0, ?_⟩
    let := markOneOrd L (w 0)
    let := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L (w 0))
      (d.B.atParam (d.param.inflLimit N) (w 0))
    have h := (realize_paramLift (B := d.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (d.param.inflLimit N) (Sum.elim default w) (d.out.relabel Sum.inl)
      (default : Fin 0 → N)).mp hw
    have h2 := Formula.realize_relabel.mp h
    exact (hcongr (w 0) _ _ (inflLimit_param (d := d) (w 0))).mp h2
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_⟩
    let := markOneOrd L c
    let := @Lax480241.Expansions.SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L c)
      (d.B.atParam (d.param.inflLimit N) c)
    refine (realize_paramLift (B := d.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (d.param.inflLimit N) (Sum.elim default fun _ => c) (d.out.relabel Sum.inl)
      (default : Fin 0 → N)).mpr ?_
    refine Formula.realize_relabel.mpr ?_
    exact (hcongr c _ _ (inflLimit_param (d := d) c)).mpr hc

end StepDef

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.StepDef

export Lax480241Proofs.DescriptiveComplexity.StepDef (ifpHolds_param)

end Lax535992.InflationaryFixedPoint.StepDef

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

namespace StepDef

variable (d : Lax535992.InflationaryFixedPoint.StepDef ((newLang L).sum Language.order))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

end StepDef

/-! ### The closure theorems -/

variable {R : Lax904597.Problems.DecisionProblem (newLang L)} {P : Lax904597.Problems.DecisionProblem L}

/-- **FO(≤, IFP) definability is closed under existential quantification over an
element**: the parameter is carried by every relation variable of the
induction. -/
theorem IFPDefinable.exElement (hR : Lax535992.InflationaryFixedPoint.IFPDefinable R)
    (h : ∀ (N : Type) [L.Structure N] [Finite N] [Nonempty N],
      P N ↔ ∃ c : N, @Lax904597.Problems.DecisionProblem.Holds (newLang L) _ R N (markOne L c)) :
    Lax535992.InflationaryFixedPoint.IFPDefinable P := by
  obtain ⟨d, hd⟩ := hR
  refine ⟨d.param, fun N _ _ _ _ => ?_⟩
  rw [h N, StepDef.ifpHolds_param]
  exact exists_congr fun c => @hd N (markOne L c) _ _ _

end Lax480241Proofs.DescriptiveComplexity

namespace Lax535992.InflationaryFixedPoint.IFPDefinable

export Lax480241Proofs.DescriptiveComplexity.IFPDefinable (exElement)

end Lax535992.InflationaryFixedPoint.IFPDefinable

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

variable {N : Type}

variable {R : Lax904597.Problems.DecisionProblem (newLang L)} {P : Lax904597.Problems.DecisionProblem L}

/-- **PTIME is closed under existential quantification over an element.** -/
theorem mem_PTIME_exElement (hR : R ∈ PTIME)
    (h : ∀ (N : Type) [L.Structure N] [Finite N] [Nonempty N],
      P N ↔ ∃ c : N, @Lax904597.Problems.DecisionProblem.Holds (newLang L) _ R N (markOne L c)) :
    P ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME P).mp
    (IFPDefinable.exElement ((ifpDefinable_iff_mem_PTIME R).mpr hR) h)

end Lax480241Proofs.DescriptiveComplexity


