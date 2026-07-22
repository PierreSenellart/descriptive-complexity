/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Hierarchy

/-!
# QBF: quantified Boolean formulas with bounded alternation

The problems `QBF k` – quantified Boolean formulas with `k` alternating
blocks of propositional quantifiers – as decision problems on first-order
structures. The vocabulary `FirstOrder.Language.qbf k` is that of SAT
(`FirstOrder.Language.sat`: clauses, positive and negative occurrences)
together with `k` unary *block marks* `qbfBlock i` splitting the
propositional variables into the `k` quantifier blocks.

The semantics is the alternating quantification `DescriptiveComplexity.altQuant`: block
`0` is quantified outermost, block `k - 1` innermost, and the polarities
alternate starting from `start`. Each quantifier picks a truth assignment for
its own block; the combined truth value of a variable
(`DescriptiveComplexity.qbfVal`) is given by the assignment of a block that marks it.

The innermost quantifier-free *matrix* comes in two shapes, selected by a
Boolean parameter:

* `DescriptiveComplexity.CnfSat` – conjunctive: every clause contains a true literal;
* `DescriptiveComplexity.DnfSat` – disjunctive: some term has all its literals true.

Both shapes are needed. The hardness proof
(`DescriptiveComplexity.Problems.Qbf.Hardness`) encodes the first-order kernel of a
second-order definition by a Tseitin translation
([Tseitin 1968][tseitin1968complexity]), which introduces auxiliary *gate*
variables; these are functionally determined by the block variables, so they
can be absorbed into the innermost quantifier only when that quantifier is
existential. For a prefix starting existentially the innermost quantifier is
existential exactly when `k` is odd, which is why
`DescriptiveComplexity.QBF` takes a conjunctive matrix for odd `k` and a disjunctive one
for even `k` – the standard form of the `Σₖᵖ`-complete quantified Boolean
formula problems ([Stockmeyer 1976][stockmeyer1976polynomial]; [Wrathall
1976][wrathall1976complete]).
-/

/- The language of quantified CNF instances lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` and `Language.sat`
– a project-local `Language` namespace would shadow Mathlib's under
`open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of quantified Boolean formulas with `k`
quantifier blocks. -/
inductive qbfRel (k : ℕ) : ℕ → Type
  /-- `isClause c`: the element `c` is a clause (a term, for a disjunctive
  matrix). -/
  | isClause : qbfRel k 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qbfRel k 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qbfRel k 2
  /-- `block i x`: the variable `x` belongs to the `i`-th quantifier block. -/
  | block : Fin k → qbfRel k 1
  deriving DecidableEq

/-- The relational vocabulary of quantified Boolean formulas with `k`
quantifier blocks: that of CNF instances, together with `k` unary predicates
marking the variables of each quantifier block. -/
protected def qbf (k : ℕ) : Language :=
  ⟨fun _ => Empty, qbfRel k⟩

instance (k : ℕ) : IsRelational (Language.qbf k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

variable {k : ℕ}

/-- The symbol for “is a clause”. -/
abbrev qbfIsClause : (Language.qbf k).Relations 1 := .isClause

/-- The symbol for “occurs positively in”. -/
abbrev qbfPosIn : (Language.qbf k).Relations 2 := .posIn

/-- The symbol for “occurs negatively in”. -/
abbrev qbfNegIn : (Language.qbf k).Relations 2 := .negIn

/-- The symbol marking the variables of the `i`-th quantifier block. -/
abbrev qbfBlock (i : Fin k) : (Language.qbf k).Relations 1 := .block i

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Alternating quantification over truth assignments -/

/-- Alternating quantification over `k` truth assignments on `A`: the
assignment of index `0` is quantified outermost, existentially if `pol` is
`true`, and the polarities alternate inwards. -/
def altQuant (A : Type) : ∀ (k : ℕ), ((Fin k → A → Prop) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true => ∃ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) false
  | k + 1, P, false => ∀ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) true

/-- Alternating quantification only depends on the quantified predicate up to
pointwise equivalence. -/
theorem altQuant_congr {A : Type} :
    ∀ (k : ℕ) (P Q : (Fin k → A → Prop) → Prop), (∀ νs, P νs ↔ Q νs) →
      ∀ pol : Bool, altQuant A k P pol ↔ altQuant A k Q pol := by
  intro k
  induction k with
  | zero => intro P Q h pol; exact h _
  | succ k ih =>
    intro P Q h pol
    cases pol with
    | true => exact exists_congr fun ν => ih _ _ (fun νs => h _) false
    | false => exact forall_congr' fun ν => ih _ _ (fun νs => h _) true

/-- Transport of alternating quantification along an equivalence of
universes: quantifying over assignments on `B` and reading them back through
`e` is quantifying over assignments on `A`. -/
theorem altQuant_equiv {A B : Type} (e : A ≃ B) :
    ∀ (k : ℕ) (P : (Fin k → A → Prop) → Prop) (pol : Bool),
      altQuant B k (fun νs => P fun i a => νs i (e a)) pol ↔ altQuant A k P pol := by
  intro k
  induction k with
  | zero =>
    intro P pol
    exact iff_of_eq (congrArg P (funext fun i => i.elim0))
  | succ k ih =>
    intro P pol
    have key : ∀ (ν : B → Prop) (νs : Fin k → B → Prop),
        (fun (i : Fin (k + 1)) (a : A) => (Fin.cons ν νs : Fin (k + 1) → B → Prop) i (e a)) =
          Fin.cons (fun a => ν (e a)) fun i a => νs i (e a) := by
      intro ν νs
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    have key' : ∀ (ν : A → Prop) (νs : Fin k → B → Prop),
        (fun (i : Fin (k + 1)) (a : A) =>
            (Fin.cons (fun b => ν (e.symm b)) νs : Fin (k + 1) → B → Prop) i (e a)) =
          Fin.cons ν fun i a => νs i (e a) := by
      intro ν νs
      refine (key _ νs).trans (congrArg₂ Fin.cons (funext fun a => ?_) rfl)
      exact congrArg ν (e.symm_apply_apply a)
    cases pol with
    | true =>
      constructor
      · rintro ⟨ν, hν⟩
        refine ⟨fun a => ν (e a), (ih (fun νs => P (Fin.cons (fun a => ν (e a)) νs)) false).mp ?_⟩
        refine (altQuant_congr k _ _ (fun νs => ?_) false).mp hν
        exact iff_of_eq (congrArg P (key ν νs))
      · rintro ⟨ν, hν⟩
        refine ⟨fun b => ν (e.symm b), ?_⟩
        refine (altQuant_congr k _ _ (fun νs => ?_) false).mpr
          ((ih (fun νs => P (Fin.cons ν νs)) false).mpr hν)
        exact iff_of_eq (congrArg P (key' ν νs))
    | false =>
      constructor
      · intro h ν
        refine (ih (fun νs => P (Fin.cons ν νs)) true).mp ?_
        refine (altQuant_congr k _ _ (fun νs => ?_) true).mp (h fun b => ν (e.symm b))
        exact iff_of_eq (congrArg P (key' ν νs))
      · intro h ν
        refine (altQuant_congr k _ _ (fun νs => ?_) true).mpr
          ((ih (fun νs => P (Fin.cons (fun a => ν (e a)) νs)) true).mpr (h _))
        exact iff_of_eq (congrArg P (key ν νs))

/-! ### The matrix of a quantified Boolean formula -/

section Matrix

variable {k : ℕ} {A : Type} [(Language.qbf k).Structure A]

/-- The truth value of the variable `x` under a tuple of block assignments:
`x` is true when some block marking it assigns it the value true. (In a
well-formed instance the block marks partition the variables, so exactly one
assignment is consulted.) -/
def qbfVal (νs : Fin k → A → Prop) (x : A) : Prop :=
  ∃ i : Fin k, RelMap (qbfBlock i) ![x] ∧ νs i x

/-- Conjunctive satisfaction, with the sign of every literal flipped when
`swap` is `true`: every clause then has to contain a literal that the block
assignments make *false*. -/
def CnfSatWith (swap : Bool) (νs : Fin k → A → Prop) : Prop :=
  ∀ c : A, RelMap (qbfIsClause (k := k)) ![c] →
    ∃ x : A,
      (RelMap (if swap then qbfNegIn (k := k) else qbfPosIn (k := k)) ![c, x] ∧ qbfVal νs x) ∨
      (RelMap (if swap then qbfPosIn (k := k) else qbfNegIn (k := k)) ![c, x] ∧ ¬qbfVal νs x)

/-- The conjunctive matrix: every clause contains a literal made true by the
block assignments. -/
abbrev CnfSat (νs : Fin k → A → Prop) : Prop := CnfSatWith false νs

/-- The disjunctive matrix: some term has all of its literals made true by the
block assignments. -/
def DnfSat (νs : Fin k → A → Prop) : Prop :=
  ∃ c : A, RelMap (qbfIsClause (k := k)) ![c] ∧
    ∀ x : A, (RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x) ∧
      (RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x)

/-- The matrix of a quantified Boolean formula: conjunctive when `cnf` is
`true`, disjunctive when it is `false`. -/
def QbfMatrix (cnf : Bool) (νs : Fin k → A → Prop) : Prop :=
  match cnf with
  | true => CnfSat νs
  | false => DnfSat νs

/-- **Propositional duality**: the disjunctive matrix is the negation of the
conjunctive one with the sign of every literal swapped. This is what lets a
single Tseitin translation serve both parities of `k`: at even `k` the
innermost quantifier is universal, and it absorbs the gate variables through
this negation. -/
theorem dnfSat_iff_not_cnfSatWith_true (νs : Fin k → A → Prop) :
    DnfSat νs ↔ ¬CnfSatWith true νs := by
  constructor
  · rintro ⟨c, hc, h⟩ hcnf
    obtain ⟨x, hx⟩ := hcnf c hc
    rcases hx with ⟨hneg, hval⟩ | ⟨hpos, hval⟩
    · exact (h x).2 hneg hval
    · exact hval ((h x).1 hpos)
  · intro h
    by_contra hd
    refine h fun c hc => ?_
    have hnc : ¬∀ x : A, (RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x) ∧
        (RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x) := fun hall => hd ⟨c, hc, hall⟩
    obtain ⟨x, hx⟩ := not_forall.mp hnc
    rcases Classical.em (RelMap (qbfPosIn (k := k)) ![c, x] ∧ ¬qbfVal νs x) with hp | hp
    · exact ⟨x, Or.inr hp⟩
    · have h1 : RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x := fun hpos =>
        Classical.byContradiction fun hv => hp ⟨hpos, hv⟩
      have h2 : ¬(RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x) := fun h2' => hx ⟨h1, h2'⟩
      rcases Classical.em (RelMap (qbfNegIn (k := k)) ![c, x]) with hn | hn
      · exact ⟨x, Or.inl ⟨hn, Classical.byContradiction fun hv => h2 fun _ => hv⟩⟩
      · exact absurd (fun hn' => absurd hn' hn) h2

/-- Optional negation, indexed by a Boolean. -/
def xorP (b : Bool) (P : Prop) : Prop :=
  match b with
  | true => ¬P
  | false => P

theorem xorP_congr (b : Bool) {P Q : Prop} (h : P ↔ Q) : xorP b P ↔ xorP b Q := by
  cases b
  · exact h
  · exact not_congr h

/-- **The two matrix shapes, uniformly**: whichever matrix `QBF` uses at a
given parity is the conjunctive one with the corresponding sign swap, negated
exactly when the swap happens. This is what lets the hardness proof treat both
parities at once. -/
theorem qbfMatrix_eq_xorP (sw : Bool) (νs : Fin k → A → Prop) :
    QbfMatrix (!sw) νs ↔ xorP sw (CnfSatWith sw νs) := by
  cases sw
  · exact Iff.rfl
  · exact dnfSat_iff_not_cnfSatWith_true νs

end Matrix

/-! ### Isomorphism-invariance -/

section Iso

variable {k : ℕ} {A B : Type} [(Language.qbf k).Structure A] [(Language.qbf k).Structure B]

/-- The truth value of a variable transports along an isomorphism. -/
private theorem qbfVal_equiv (e : A ≃[Language.qbf k] B) (νs : Fin k → B → Prop) (x : A) :
    qbfVal (fun i a => νs i (e a)) x ↔ qbfVal νs (e x) :=
  exists_congr fun i => and_congr_left' (relMap_equiv₁ e (qbfBlock i) x)

private theorem cnfSatWith_equiv (swap : Bool) (e : A ≃[Language.qbf k] B)
    (νs : Fin k → B → Prop) :
    CnfSatWith swap (fun i a => νs i (e a)) ↔ CnfSatWith swap νs := by
  unfold CnfSatWith
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (e.symm c) ((relMap_equiv₁ e.symm (qbfIsClause (k := k)) c).mp hc)
    refine ⟨e x, ?_⟩
    rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · refine Or.inl ⟨?_, (qbfVal_equiv e νs x).mp hv⟩
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hp
    · refine Or.inr ⟨?_, fun hv' => hv ((qbfVal_equiv e νs x).mpr hv')⟩
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hn
  · intro h c hc
    obtain ⟨x, hx⟩ := h (e c) ((relMap_equiv₁ e (qbfIsClause (k := k)) c).mp hc)
    refine ⟨e.symm x, ?_⟩
    rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · refine Or.inl ⟨(relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hp), ?_⟩
      exact (qbfVal_equiv e νs (e.symm x)).mpr (by simpa using hv)
    · refine Or.inr ⟨(relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hn), ?_⟩
      exact fun hv' => hv (by simpa using (qbfVal_equiv e νs (e.symm x)).mp hv')

private theorem dnfSat_equiv (e : A ≃[Language.qbf k] B) (νs : Fin k → B → Prop) :
    DnfSat (fun i a => νs i (e a)) ↔ DnfSat νs := by
  unfold DnfSat
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨e c, (relMap_equiv₁ e (qbfIsClause (k := k)) c).mp hc, fun x => ?_⟩
    refine ⟨fun hp => ?_, fun hn hv => ?_⟩
    · have := (h (e.symm x)).1 ((relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hp))
      simpa using (qbfVal_equiv e νs (e.symm x)).mp this
    · refine (h (e.symm x)).2 ((relMap_equiv₂ e _ c (e.symm x)).mpr (by simpa using hn)) ?_
      exact (qbfVal_equiv e νs (e.symm x)).mpr (by simpa using hv)
  · rintro ⟨c, hc, h⟩
    refine ⟨e.symm c, (relMap_equiv₁ e.symm (qbfIsClause (k := k)) c).mp hc, fun x => ?_⟩
    refine ⟨fun hp => ?_, fun hn hv => ?_⟩
    · refine (qbfVal_equiv e νs x).mpr ((h (e x)).1 ?_)
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hp
    · refine (h (e x)).2 ?_ ((qbfVal_equiv e νs x).mp hv)
      simpa using (relMap_equiv₂ e _ (e.symm c) x).mp hn

private theorem qbfMatrix_equiv (cnf : Bool) (e : A ≃[Language.qbf k] B)
    (νs : Fin k → B → Prop) :
    QbfMatrix cnf (fun i a => νs i (e a)) ↔ QbfMatrix cnf νs := by
  cases cnf
  · exact dnfSat_equiv e νs
  · exact cnfSatWith_equiv false e νs

end Iso

/-! ### The decision problems -/

/-- Quantified Boolean formulas with `k` alternating quantifier blocks: the
prefix starts with an existential block when `start` is `true`, and the matrix
is conjunctive when `cnf` is `true`. -/
def QbfProblem (k : ℕ) (start cnf : Bool) : DecisionProblem (Language.qbf k) where
  Holds := fun A inst => altQuant A k (fun νs => @QbfMatrix k A inst cnf νs) start
  iso_invariant := fun {_A _B} _ _ e =>
    ((altQuant_congr k _ _ (fun νs => (qbfMatrix_equiv cnf e νs).symm) start).trans
      (altQuant_equiv e.toEquiv k _ start)).symm

/-- **QBF with `k` alternating blocks**, the canonical `Σₖᵖ`-complete problem:
an existential outermost block, and a matrix whose shape follows the parity of
`k` – conjunctive when the innermost quantifier is existential (`k` odd),
disjunctive when it is universal (`k` even). See
`DescriptiveComplexity.Problems.Qbf` for the completeness theorem. -/
def QBF (k : ℕ) : DecisionProblem (Language.qbf k) :=
  QbfProblem k true (k % 2 == 1)

/-- The dual family, with a universal outermost block: the canonical
`Πₖᵖ`-complete problem. -/
def QBFPi (k : ℕ) : DecisionProblem (Language.qbf k) :=
  QbfProblem k false (k % 2 == 0)

end DescriptiveComplexity
