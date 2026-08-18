/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointInflationaryLFP
import DescriptiveComplexity.SecondOrderNew
import DescriptiveComplexity.SecondOrderParam

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

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### A structure with one marked element -/

/-- The mark of a single element, as a structure over the marking
vocabulary. -/
@[instance_reducible]
def oneMark {N : Type} (c : N) : Language.oldMark.Structure N where
  RelMap := fun {_} r => match r with
    | .old => fun x => x 0 = c

/-- **The instance with one element marked**, over
`DescriptiveComplexity.newLang`. -/
@[instance_reducible]
def markOne (L : Language.{0, 0}) {N : Type} [inst : L.Structure N] (c : N) :
    (newLang L).Structure N :=
  @sumStructure L Language.oldMark N inst (oneMark c)

/-! ### The block, with a parameter argument

`DescriptiveComplexity.SOBlock.withParam` and its reading at a parameter are
`SecondOrderParam.lean`'s; what is here is the one statement that mentions the
empty assignment. -/

variable {N : Type}

theorem SOBlock.atParam_bot (B : SOBlock) (c : N) :
    B.atParam (B.withParam.botAssign N) c = B.botAssign N :=
  rfl

/-! ### The parameter substitution -/

section Lift

variable (B : SOBlock) {α : Type} (p : α)

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
    letI := @SOBlock.structure₁ ((newLang L).sum Language.order) B N
      (@sumOrderStructure (newLang L) N (markOne L c) _) (B.atParam ρ c)
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
      letI := @SOBlock.structure₁ ((newLang L).sum Language.order) B N
        (@sumOrderStructure (newLang L) N (markOne L (v p)) _) (B.atParam ρ (v p))
      ((paramLift B p φ).Realize v xs ↔ φ.Realize v xs) := by
  let := (B.withParam.structure₁ (L := L.sum Language.order) ρ)
  let := @SOBlock.structure₁ ((newLang L).sum Language.order) B N
    (@sumOrderStructure (newLang L) N (markOne L (v p)) _) (B.atParam ρ (v p))
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
  @sumOrderStructure (newLang L) N (markOne L c) _

/-! ### The definition, run at every parameter at once -/

namespace StepDef

variable (d : StepDef ((newLang L).sum Language.order))

/-- **Every instance at once**: the same simultaneous induction, every relation
variable carrying the parameter as a further argument, and the output
existentially quantified over it. -/
noncomputable def param : StepDef (L.sum Language.order) where
  B := d.B.withParam
  step i := paramLift d.B (0 : Fin (d.B.arity i + 1)) ((d.step i).relabel Fin.succ)
  out := Formula.iExs (Fin 1) (paramLift d.B (Sum.inr 0) (d.out.relabel Sum.inl))

variable {d} {N : Type} [L.Structure N] [LinearOrder N]

/-- One step of the parameterized definition, read at a parameter, is one step
of the original in the instance that parameter marks. -/
theorem next_param (ρ : d.param.B.Assignment N) (c : N) :
    d.B.atParam (d.param.next ρ) c = @StepDef.next _ d N (markOneOrd L c) (d.B.atParam ρ c) := by
  funext i x
  let := markOneOrd L c
  let := @SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L c)
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

/-- The inflationary step of the parameterized definition, read at a
parameter. -/
theorem inflStep_param (ρ : d.param.B.Assignment N) (c : N) :
    d.B.atParam (d.param.inflStep ρ) c =
      @StepDef.inflStep _ d N (markOneOrd L c) (d.B.atParam ρ c) := by
  funext i x
  exact congrArg (Or (d.B.atParam ρ c i x)) (congrFun (congrFun (next_param (d := d) ρ c) i) x)

/-- **Every stage of the parameterized iteration holds the stages of all the
instances side by side.** -/
theorem inflStage_param (c : N) :
    ∀ k : ℕ, d.B.atParam (d.param.inflStage N k) c =
      @StepDef.inflStage _ d N (markOneOrd L c) k := by
  intro k
  induction k with
  | zero => exact d.B.atParam_bot c
  | succ k ih =>
    have hstep : d.param.inflStage N (k + 1) = d.param.inflStep (d.param.inflStage N k) :=
      d.param.inflStage_succ k
    have hstepd : @StepDef.inflStage _ d N (markOneOrd L c) (k + 1) =
        @StepDef.inflStep _ d N (markOneOrd L c) (@StepDef.inflStage _ d N (markOneOrd L c) k) :=
      @StepDef.inflStage_succ _ d N (markOneOrd L c) k
    rw [hstep, hstepd, ← ih]
    exact inflStep_param (d := d) (d.param.inflStage N k) c

/-- The value of the parameterized iteration, read at a parameter. -/
theorem inflLimit_param (c : N) :
    d.B.atParam (d.param.inflLimit N) c = @StepDef.inflLimit _ d N (markOneOrd L c) := by
  funext i x
  exact propext (exists_congr fun k =>
    iff_of_eq (congrFun (congrFun (inflStage_param (d := d) c k) i) x))

/-- **What the parameterized definition defines**: the original one, at some
element of the instance. -/
theorem ifpHolds_param :
    d.param.IFPHolds N ↔ ∃ c : N, @StepDef.IFPHolds _ d N (markOneOrd L c) := by
  let := d.param.B.structure₁ (L := L.sum Language.order) (d.param.inflLimit N)
  have hcongr : ∀ (c : N) (σ τ : d.B.Assignment N), σ = τ →
      (@Sentence.Realize _ N (@SOBlock.structure₁ ((newLang L).sum Language.order) d.B N
          (markOneOrd L c) σ) d.out ↔
        @Sentence.Realize _ N (@SOBlock.structure₁ ((newLang L).sum Language.order) d.B N
          (markOneOrd L c) τ) d.out) := by
    rintro c σ τ rfl
    exact Iff.rfl
  refine Iff.trans Formula.realize_iExs ?_
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w 0, ?_⟩
    let := markOneOrd L (w 0)
    let := @SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L (w 0))
      (d.B.atParam (d.param.inflLimit N) (w 0))
    have h := (realize_paramLift (B := d.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (d.param.inflLimit N) (Sum.elim default w) (d.out.relabel Sum.inl)
      (default : Fin 0 → N)).mp hw
    have h2 := Formula.realize_relabel.mp h
    exact (hcongr (w 0) _ _ (inflLimit_param (d := d) (w 0))).mp h2
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_⟩
    let := markOneOrd L c
    let := @SOBlock.structure₁ ((newLang L).sum Language.order) d.B N (markOneOrd L c)
      (d.B.atParam (d.param.inflLimit N) c)
    refine (realize_paramLift (B := d.B) (p := (Sum.inr 0 : Empty ⊕ Fin 1))
      (d.param.inflLimit N) (Sum.elim default fun _ => c) (d.out.relabel Sum.inl)
      (default : Fin 0 → N)).mpr ?_
    refine Formula.realize_relabel.mpr ?_
    exact (hcongr c _ _ (inflLimit_param (d := d) c)).mpr hc

end StepDef

/-! ### The closure theorems -/

variable {R : DecisionProblem (newLang L)} {P : DecisionProblem L}

/-- **FO(≤, IFP) definability is closed under existential quantification over an
element**: the parameter is carried by every relation variable of the
induction. -/
theorem IFPDefinable.exElement (hR : IFPDefinable R)
    (h : ∀ (N : Type) [L.Structure N] [Finite N] [Nonempty N],
      P N ↔ ∃ c : N, @DecisionProblem.Holds (newLang L) _ R N (markOne L c)) :
    IFPDefinable P := by
  obtain ⟨d, hd⟩ := hR
  refine ⟨d.param, fun N _ _ _ _ => ?_⟩
  rw [h N, StepDef.ifpHolds_param]
  exact exists_congr fun c => @hd N (markOne L c) _ _ _

/-- **PTIME is closed under existential quantification over an element.** -/
theorem mem_PTIME_exElement (hR : R ∈ PTIME)
    (h : ∀ (N : Type) [L.Structure N] [Finite N] [Nonempty N],
      P N ↔ ∃ c : N, @DecisionProblem.Holds (newLang L) _ R N (markOne L c)) :
    P ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME P).mp
    (IFPDefinable.exElement ((ifpDefinable_iff_mem_PTIME R).mpr hR) h)

end DescriptiveComplexity
