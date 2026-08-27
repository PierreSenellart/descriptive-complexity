/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureDecideReachDet

/-!
# Flattening a walk whose steps are decided: the suspension

The nested case of the normal form for FO(TC): a walk over an *expansion* –
whose step formulas read the reachability relations of other walks – becomes
a walk over the base vocabulary
(`DescriptiveComplexity.ParamTCSpec.flat`), given a
`DescriptiveComplexity.Decider` for each of its step formulas. The outer walk
is **suspended** at a node, the decider of the step to a candidate successor
is run, and where it exits `yes` the outer walk resumes at that successor.

## Two ways to pick the candidate

* **Guessing** (`det := false`): the candidate is chosen nondeterministically.
  Reachability in the flat walk is then reachability in the outer one
  (`DescriptiveComplexity.ParamTCSpec.reachAt_flat_iff`), for any outer walk.
* **Searching** (`det := true`): the candidates are tried in the mode-major
  lexicographic order of nodes, the next one after a `no`. The flat walk is
  then **functional** when the deciders are
  (`DescriptiveComplexity.ParamTCSpec.functional_flat`), and it simulates the
  outer walk provided that one is functional
  (`DescriptiveComplexity.ParamTCSpec.reachAt_flat_iff_of_functional`) – as
  the deterministic reading of a walk is.

A node of the outer walk is encoded with the candidate and every decider's
coordinates at the minimum (`DescriptiveComplexity.ParamTCSpec.flatEnc`), which
is where the walk resumes after a `yes`; this is what makes the encoding a
bijection onto the outer nodes the flat walk can stand on.

The flat walk carries its coordinates as a type rather than an arity
(`DescriptiveComplexity.CoordWalk`), the coordinates of the deciders being a
dependent sum over the pairs of modes; `DescriptiveComplexity.CoordWalk.toParam`
enumerates them for the `DescriptiveComplexity.ParamTCSpec` the rest of the
development consumes.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Walks with a type of coordinates -/

/-- A parameterized walk whose coordinates are an arbitrary finite type. -/
structure CoordWalk (L : Language.{0, 0}) : Type 1 where
  /-- The modes. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The coordinates. -/
  Coord : Type
  /-- Tuples are finite. -/
  [coordFinite : Finite Coord]
  /-- The number of parameters. -/
  par : ℕ
  /-- The step formula, one per pair of modes. -/
  step : Mode → Mode → L.Formula ((Coord ⊕ Coord) ⊕ Fin par)

attribute [instance] CoordWalk.modeFinite CoordWalk.coordFinite

namespace CoordWalk

variable {L : Language.{0, 0}} (C : CoordWalk L) {A : Type} [L.Structure A]

variable (A) in
/-- A node: a mode and a tuple. -/
abbrev Node : Type := C.Mode × (C.Coord → A)

/-- One step, at a valuation of the parameters. -/
def StepAt (z : Fin C.par → A) (a b : C.Node A) : Prop :=
  (C.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) z)

/-- Reachability, at a valuation of the parameters. -/
abbrev ReachAt (z : Fin C.par → A) : C.Node A → C.Node A → Prop :=
  Relation.ReflTransGen (C.StepAt z)

variable (A) in
/-- The walk is functional when no node has two successors. -/
def Functional : Prop :=
  ∀ (z : Fin C.par → A) (a b c : C.Node A), C.StepAt z a b → C.StepAt z a c → b = c

/-- The coordinates, enumerated. -/
noncomputable def coordEquiv : C.Coord ≃ Fin (Nat.card C.Coord) :=
  letI := Fintype.ofFinite C.Coord
  (Fintype.equivFin C.Coord).trans (finCongr Fintype.card_eq_nat_card)

/-- **The walk with its coordinates enumerated**, as a
`DescriptiveComplexity.ParamTCSpec`. Reducible, so that its modes and
parameters are those of the walk transparently. -/
@[reducible]
noncomputable def toParam : ParamTCSpec L where
  Mode := C.Mode
  k := Nat.card C.Coord
  par := C.par
  step m n := (C.step m n).relabel (Sum.map (Sum.map C.coordEquiv C.coordEquiv) id)

theorem stepAt_toParam (z : Fin C.par → A) (a b : C.toParam.Node A) :
    C.toParam.StepAt z a b ↔ C.StepAt z (a.1, a.2 ∘ C.coordEquiv) (b.1, b.2 ∘ C.coordEquiv) := by
  change ((C.step a.1 b.1).relabel _).Realize (Sum.elim (Sum.elim a.2 b.2) z) ↔ _
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (Formula.Realize (M := A) (C.step a.1 b.1)) (funext fun i => ?_))
  rcases i with (i | i) | i <;> rfl

theorem reachAt_toParam (z : Fin C.par → A) (a b : C.toParam.Node A) :
    C.toParam.ReachAt z a b ↔ C.ReachAt z (a.1, a.2 ∘ C.coordEquiv) (b.1, b.2 ∘ C.coordEquiv) := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((C.stepAt_toParam z c d).mp hcd)
  · intro h
    have key : ∀ c d : C.Node A, C.ReachAt z c d →
        C.toParam.ReachAt z (c.1, c.2 ∘ C.coordEquiv.symm) (d.1, d.2 ∘ C.coordEquiv.symm) := by
      intro c d hcd
      refine Relation.ReflTransGen.lift (fun e : C.Node A => (e.1, e.2 ∘ C.coordEquiv.symm))
        (fun e e' hee' => ?_) _ _ hcd
      refine (C.stepAt_toParam z _ _).mpr ?_
      simpa [Function.comp_def] using hee'
    have := key _ _ h
    simpa [Function.comp_def] using this

theorem functional_toParam (h : C.Functional A) : C.toParam.Functional A := by
  intro z a b c hb hc
  have := h z _ _ _ ((C.stepAt_toParam z a b).mp hb) ((C.stepAt_toParam z a c).mp hc)
  refine Prod.ext (Prod.mk.inj this).1 (funext fun i => ?_)
  have := congrFun (Prod.mk.inj this).2 (C.coordEquiv.symm i)
  simpa using this

end CoordWalk

/-! ### The flat walk -/

namespace ParamTCSpec

variable {L : Language.{0, 0}} {B : SOBlock}
variable (S : ParamTCSpec ((L.sum Language.order).sum B.lang))
variable (D : S.Mode → S.Mode → Decider L ((Fin S.k ⊕ Fin S.k) ⊕ Fin S.par))

/-- An arbitrary linear order on the modes of the outer walk, for the
search. -/
@[instance_reducible]
noncomputable def outerModeOrder : LinearOrder S.Mode := finiteLinearOrder S.Mode

/-- The coordinates of the flat walk: the current tuple and the candidate,
then the coordinates of every decider. -/
abbrev FlatCoord : Type := (Fin S.k ⊕ Fin S.k) ⊕ (Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord)

/-- The modes of the flat walk: a mode of the outer walk, or a pair of modes
with a mode of their decider. -/
abbrev FlatMode : Type := S.Mode ⊕ (Σ p : S.Mode × S.Mode, (D p.1 p.2).Mode)

/-- A coordinate belongs to the slice of a pair of modes. -/
def InSlice (p : S.Mode × S.Mode) (c : S.FlatCoord D) : Prop := ∃ d, c = Sum.inr ⟨p, d⟩

/-! #### The formulas -/

section Formulas

/-- The variables of a decider's step, in the flat walk's. -/
def flatRunVar (p : S.Mode × S.Mode) :
    (((D p.1 p.2).Coord ⊕ (D p.1 p.2).Coord) ⊕ ((Fin S.k ⊕ Fin S.k) ⊕ Fin S.par)) →
      (S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par
  | Sum.inl (Sum.inl c) => Sum.inl (Sum.inl (Sum.inr ⟨p, c⟩))
  | Sum.inl (Sum.inr c) => Sum.inl (Sum.inr (Sum.inr ⟨p, c⟩))
  | Sum.inr (Sum.inl q) => Sum.inl (Sum.inl (Sum.inl q))
  | Sum.inr (Sum.inr j) => Sum.inr j

/-- The variables of a decider's exit, in the flat walk's step (read on the
current tuple). -/
def flatExitVar (p : S.Mode × S.Mode) :
    ((D p.1 p.2).Coord ⊕ ((Fin S.k ⊕ Fin S.k) ⊕ Fin S.par)) →
      (S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par
  | Sum.inl c => Sum.inl (Sum.inl (Sum.inr ⟨p, c⟩))
  | Sum.inr (Sum.inl q) => Sum.inl (Sum.inl (Sum.inl q))
  | Sum.inr (Sum.inr j) => Sum.inr j

/-- The current tuple's coordinate, as a step variable. -/
abbrev fcur (c : S.FlatCoord D) : (S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par :=
  Sum.inl (Sum.inl c)

/-- The next tuple's coordinate, as a step variable. -/
abbrev fnext (c : S.FlatCoord D) : (S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par :=
  Sum.inl (Sum.inr c)

open Classical in
/-- Every coordinate outside a slice is copied. -/
noncomputable def copyExceptF (p : S.Mode × S.Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  Formula.iInf fun c : S.FlatCoord D =>
    if S.InSlice D p c then ⊤ else Term.equal (Term.var (S.fcur D c)) (Term.var (S.fnext D c))

/-- Every decider coordinate of the next tuple is at the minimum. -/
noncomputable def minSlicesF :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  Formula.iInf fun c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord => minF (S.fnext D (Sum.inr c))

/-- The next tuple is the candidate, with everything else at the minimum. -/
noncomputable def resetF :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  Formula.iInf fun c : S.FlatCoord D =>
    match c with
    | Sum.inl (Sum.inl i) =>
        Term.equal (Term.var (S.fnext D (Sum.inl (Sum.inl i))))
          (Term.var (S.fcur D (Sum.inl (Sum.inr i))))
    | c => minF (S.fnext D c)

/-- The current tuple is copied. -/
noncomputable def copyCurF :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  copyF (fun i : Fin S.k => S.fcur D (Sum.inl (Sum.inl i))) fun i => S.fnext D (Sum.inl (Sum.inl i))

open Classical in
/-- **The candidate advances**: same mode and the successor tuple, or the
next mode with the tuple from the maximum to the minimum. -/
noncomputable def candSuccF (c c' : S.Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  letI := S.outerModeOrder
  if c' = c then
    succTupF (fun i => S.fcur D (Sum.inl (Sum.inr i))) fun i => S.fnext D (Sum.inl (Sum.inr i))
  else if c ⋖ c' then
    maxTupF (fun i => S.fcur D (Sum.inl (Sum.inr i))) ⊓
      minTupF fun i => S.fnext D (Sum.inl (Sum.inr i))
  else ⊥

open Classical in
/-- **Entering a decider**: the current tuple is copied and the decider's
coordinates are reset; when searching, the candidate is the least node. -/
noncomputable def initF (det : Bool) (p : S.Mode × S.Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  letI := S.outerModeOrder
  (if det then
    (if ∀ c' : S.Mode, p.2 ≤ c' then minTupF fun i => S.fnext D (Sum.inl (Sum.inr i)) else ⊥)
  else ⊤) ⊓ S.copyCurF D ⊓ S.minSlicesF D

/-- **Running a decider**: its step on its slice, everything else copied. -/
noncomputable def runF (p : S.Mode × S.Mode) (d d' : (D p.1 p.2).Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  ((D p.1 p.2).step d d').relabel (S.flatRunVar D p) ⊓ S.copyExceptF D p

/-- **Resuming the outer walk**: the decider exits `yes`, and the walk stands
on the candidate. -/
noncomputable def retF (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  ((D p.1 p.2).exit d true).relabel (S.flatExitVar D p) ⊓ S.resetF D

open Classical in
/-- **Trying the next candidate**: the decider exits `no`, the candidate
advances, and the decider's coordinates are reset. -/
noncomputable def advF (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (p' : S.Mode × S.Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  if p'.1 = p.1 then
    ((D p.1 p.2).exit d false).relabel (S.flatExitVar D p) ⊓ S.candSuccF D p.2 p'.2 ⊓
      S.copyCurF D ⊓ S.minSlicesF D
  else ⊥

open Classical in
/-- The step between two decider nodes: the run, or (when searching) an
advance to the start of the next candidate's decider. -/
noncomputable def innerF (det : Bool) (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode)
    (p' : S.Mode × S.Mode) (d' : (D p'.1 p'.2).Mode) :
    (L.sum Language.order).Formula ((S.FlatCoord D ⊕ S.FlatCoord D) ⊕ Fin S.par) :=
  (if h : p = p' then
    S.runF D p d (cast (congrArg (fun q : S.Mode × S.Mode => (D q.1 q.2).Mode) h.symm) d')
  else ⊥) ⊔
    (if det ∧ d' = (D p'.1 p'.2).start then S.advF D p d p' else ⊥)

open Classical in
/-- **The flat walk**: the outer walk with each step decided in place.
Guessing (`det = false`) or searching (`det = true`) the candidate. -/
@[reducible]
noncomputable def flat (det : Bool) : CoordWalk (L.sum Language.order) where
  Mode := S.FlatMode D
  Coord := S.FlatCoord D
  par := S.par
  step m n :=
    match m, n with
    | Sum.inl m, Sum.inr ⟨p, d⟩ =>
        if p.1 = m ∧ d = (D p.1 p.2).start then S.initF D det p else ⊥
    | Sum.inr ⟨p, d⟩, Sum.inr ⟨p', d'⟩ => S.innerF D det p d p' d'
    | Sum.inr ⟨p, d⟩, Sum.inl n => if p.2 = n then S.retF D p d else ⊥
    | Sum.inl _, Sum.inl _ => ⊥

end Formulas

/-! #### Tuples of the flat walk -/

section Tuples

variable {S D} {A : Type}

/-- The current tuple. -/
abbrev tx (t : S.FlatCoord D → A) : Fin S.k → A := fun i => t (Sum.inl (Sum.inl i))

/-- The candidate. -/
abbrev ty (t : S.FlatCoord D → A) : Fin S.k → A := fun i => t (Sum.inl (Sum.inr i))

/-- The slice of a pair of modes. -/
abbrev tsl (t : S.FlatCoord D → A) (p : S.Mode × S.Mode) : (D p.1 p.2).Coord → A :=
  fun c => t (Sum.inr ⟨p, c⟩)

/-- The valuation of a decider's parameters: the current tuple, the candidate
and the outer parameters. -/
abbrev dpar (t : S.FlatCoord D → A) (z : Fin S.par → A) : (Fin S.k ⊕ Fin S.k) ⊕ Fin S.par → A :=
  Sum.elim (t ∘ Sum.inl) z

open Classical in
/-- A tuple with one slice replaced. -/
noncomputable def setSlice (t : S.FlatCoord D → A) (p : S.Mode × S.Mode)
    (u : (D p.1 p.2).Coord → A) : S.FlatCoord D → A
  | Sum.inl q => t (Sum.inl q)
  | Sum.inr ⟨q, c⟩ =>
      if h : q = p then u (cast (congrArg (fun r : S.Mode × S.Mode => (D r.1 r.2).Coord) h) c)
      else t (Sum.inr ⟨q, c⟩)

theorem setSlice_inl (t : S.FlatCoord D → A) (p : S.Mode × S.Mode) (u : (D p.1 p.2).Coord → A)
    (q : Fin S.k ⊕ Fin S.k) : setSlice t p u (Sum.inl q) = t (Sum.inl q) := rfl

theorem setSlice_comp_inl (t : S.FlatCoord D → A) (p : S.Mode × S.Mode)
    (u : (D p.1 p.2).Coord → A) : setSlice t p u ∘ Sum.inl = t ∘ Sum.inl := rfl

theorem tsl_setSlice_self (t : S.FlatCoord D → A) (p : S.Mode × S.Mode)
    (u : (D p.1 p.2).Coord → A) : tsl (setSlice t p u) p = u := by
  funext c
  simp [tsl, setSlice]

theorem setSlice_of_not_inSlice (t : S.FlatCoord D → A) (p : S.Mode × S.Mode)
    (u : (D p.1 p.2).Coord → A) (c : S.FlatCoord D) (hc : ¬S.InSlice D p c) :
    setSlice t p u c = t c := by
  rcases c with q | ⟨q, c⟩
  · rfl
  · have hq : q ≠ p := fun h => hc ⟨h ▸ c, by subst h; rfl⟩
    simp [setSlice, hq]

theorem dpar_setSlice (t : S.FlatCoord D → A) (p : S.Mode × S.Mode) (u : (D p.1 p.2).Coord → A)
    (z : Fin S.par → A) : dpar (setSlice t p u) z = dpar t z := rfl

theorem setSlice_tsl (t : S.FlatCoord D → A) (p : S.Mode × S.Mode) :
    setSlice t p (tsl t p) = t := by
  funext c
  by_cases hc : S.InSlice D p c
  · obtain ⟨d, rfl⟩ := hc
    exact congrFun (tsl_setSlice_self t p (tsl t p)) d
  · exact setSlice_of_not_inSlice t p _ c hc

end Tuples

/-- The encoding of a node of the outer walk, at a bottom element `a₀`. -/
def flatEnc {A : Type} (det : Bool) (a₀ : A) (a : S.Node A) : (S.flat D det).Node A :=
  (Sum.inl a.1, Sum.elim (Sum.elim a.2 fun _ => a₀) fun _ => a₀)

/-! #### Semantics of the formulas -/

section Semantics

variable {det : Bool} {A : Type} [L.Structure A] [LinearOrder A] (z : Fin S.par → A)

theorem realize_copyExceptF (p : S.Mode × S.Mode) (t t' : S.FlatCoord D → A) :
    (S.copyExceptF D p).Realize (Sum.elim (Sum.elim t t') z) ↔
      ∀ c, ¬S.InSlice D p c → t' c = t c := by
  classical
  rw [copyExceptF, Formula.realize_iInf]
  refine forall_congr' fun c => ?_
  split_ifs with h
  · simp [h]
  · simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h' _ => h'.symm, fun h' => (h' h).symm⟩

theorem realize_minSlicesF (t t' : S.FlatCoord D → A) :
    (S.minSlicesF D).Realize (Sum.elim (Sum.elim t t') z) ↔
      ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  rw [minSlicesF, Formula.realize_iInf]
  exact forall_congr' fun c => realize_minF _

theorem realize_resetF (t t' : S.FlatCoord D → A) :
    (S.resetF D).Realize (Sum.elim (Sum.elim t t') z) ↔
      tx t' = ty t ∧ (∀ (i : Fin S.k) (a : A), t' (Sum.inl (Sum.inr i)) ≤ a) ∧
        ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  rw [resetF, Formula.realize_iInf]
  constructor
  · intro h
    refine ⟨funext fun i => ?_, fun i => ?_, fun c => ?_⟩
    · have := h (Sum.inl (Sum.inl i))
      simpa using this
    · have := h (Sum.inl (Sum.inr i))
      simpa using this
    · have := h (Sum.inr c)
      simpa using this
  · rintro ⟨h1, h2, h3⟩ c
    rcases c with (i | i) | c
    · simpa using congrFun h1 i
    · simpa using h2 i
    · simpa using h3 c

theorem realize_copyCurF (t t' : S.FlatCoord D → A) :
    (S.copyCurF D).Realize (Sum.elim (Sum.elim t t') z) ↔ tx t' = tx t := by
  rw [copyCurF, realize_copyF]
  exact ⟨fun h => funext fun i => congrFun h i, fun h => funext fun i => congrFun h i⟩

variable [Nonempty A]

theorem realize_candSuccF (c c' : S.Mode) (t t' : S.FlatCoord D → A) :
    (S.candSuccF D c c').Realize (Sum.elim (Sum.elim t t') z) ↔
      (letI := S.outerModeOrder; toLex (c, toLex (ty t)) ⋖ toLex (c', toLex (ty t'))) := by
  classical
  let := S.outerModeOrder
  rw [candSuccF, prodLex_covBy_iff]
  split_ifs with h1 h2
  · subst h1
    rw [realize_succTupF, tupSucc_iff_covBy]
    constructor
    · intro h
      exact Or.inl ⟨rfl, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd rfl h.ne
  · rw [Formula.realize_inf, realize_maxTupF, realize_minTupF]
    constructor
    · rintro ⟨hmax, hmin⟩
      exact Or.inr ⟨h2, tup_isTop_iff.mpr hmax, tup_isBot_iff.mpr hmin⟩
    · rintro (⟨h, -⟩ | ⟨-, hmax, hmin⟩)
      · exact absurd h.symm h1
      · exact ⟨tup_isTop_iff.mp hmax, tup_isBot_iff.mp hmin⟩
  · simp only [Formula.realize_bot, false_iff, not_or, not_and]
    exact ⟨fun h => absurd h.symm h1, fun h => absurd h h2⟩

omit [Nonempty A] in
theorem realize_initF (p : S.Mode × S.Mode) (t t' : S.FlatCoord D → A) :
    (S.initF D det p).Realize (Sum.elim (Sum.elim t t') z) ↔
      (det = true → (letI := S.outerModeOrder; ∀ c' : S.Mode, p.2 ≤ c') ∧
          ∀ (i : Fin S.k) (a : A), t' (Sum.inl (Sum.inr i)) ≤ a) ∧
        tx t' = tx t ∧
        ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  classical
  let := S.outerModeOrder
  rw [initF, Formula.realize_inf, Formula.realize_inf, S.realize_copyCurF, S.realize_minSlicesF,
    and_assoc]
  refine and_congr ?_ Iff.rfl
  cases det
  · simp
  · simp only [↓reduceIte, forall_const]
    split_ifs with h
    · rw [realize_minTupF]
      exact ⟨fun h' => ⟨h, h'⟩, And.right⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun h' => absurd h' h

omit [Nonempty A] in
theorem realize_runF (p : S.Mode × S.Mode) (d d' : (D p.1 p.2).Mode)
    (t t' : S.FlatCoord D → A) :
    (S.runF D p d d').Realize (Sum.elim (Sum.elim t t') z) ↔
      (D p.1 p.2).StepAt (dpar t z) (d, tsl t p) (d', tsl t' p) ∧
        ∀ c, ¬S.InSlice D p c → t' c = t c := by
  rw [runF, Formula.realize_inf, Formula.realize_relabel, S.realize_copyExceptF]
  refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) ((D p.1 p.2).step d d'))
    (funext fun i => ?_))) Iff.rfl
  rcases i with (i | i) | (i | i) <;> rfl

omit [Nonempty A] in
theorem realize_exit_relabel (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (o : Bool)
    (t t' : S.FlatCoord D → A) :
    (((D p.1 p.2).exit d o).relabel (S.flatExitVar D p)).Realize (Sum.elim (Sum.elim t t') z) ↔
      (D p.1 p.2).ExitAt (dpar t z) (d, tsl t p) o := by
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (Formula.Realize (M := A) ((D p.1 p.2).exit d o))
    (funext fun i => ?_))
  rcases i with i | (i | i) <;> rfl

omit [Nonempty A] in
theorem realize_retF (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (t t' : S.FlatCoord D → A) :
    (S.retF D p d).Realize (Sum.elim (Sum.elim t t') z) ↔
      (D p.1 p.2).ExitAt (dpar t z) (d, tsl t p) true ∧
        tx t' = ty t ∧ (∀ (i : Fin S.k) (a : A), t' (Sum.inl (Sum.inr i)) ≤ a) ∧
          ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  rw [retF, Formula.realize_inf, S.realize_exit_relabel, S.realize_resetF]

/-- The advance, as a relation between the two nodes. -/
def Adv (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (p' : S.Mode × S.Mode)
    (t t' : S.FlatCoord D → A) : Prop :=
  p'.1 = p.1 ∧ (D p.1 p.2).ExitAt (dpar t z) (d, tsl t p) false ∧
    (letI := S.outerModeOrder; toLex (p.2, toLex (ty t)) ⋖ toLex (p'.2, toLex (ty t'))) ∧
    tx t' = tx t ∧
    ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a

theorem realize_advF (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (p' : S.Mode × S.Mode)
    (t t' : S.FlatCoord D → A) :
    (S.advF D p d p').Realize (Sum.elim (Sum.elim t t') z) ↔ S.Adv D z p d p' t t' := by
  classical
  rw [advF, Adv]
  split_ifs with h
  · rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, S.realize_exit_relabel,
      S.realize_candSuccF, S.realize_copyCurF, S.realize_minSlicesF, and_iff_right h, and_assoc,
      and_assoc]
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

/-! #### Steps of the flat walk -/

omit [Nonempty A] in
theorem flat_stepAt_inl_inr (m : S.Mode) (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode)
    (t t' : S.FlatCoord D → A) :
    (S.flat D det).StepAt z (Sum.inl m, t) (Sum.inr ⟨p, d⟩, t') ↔
      p.1 = m ∧ d = (D p.1 p.2).start ∧
        (det = true → (letI := S.outerModeOrder; ∀ c' : S.Mode, p.2 ≤ c') ∧
          ∀ (i : Fin S.k) (a : A), t' (Sum.inl (Sum.inr i)) ≤ a) ∧
        tx t' = tx t ∧
        ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  classical
  have hstep : (S.flat D det).step (Sum.inl m) (Sum.inr ⟨p, d⟩) =
      if p.1 = m ∧ d = (D p.1 p.2).start then S.initF D det p else ⊥ := rfl
  unfold CoordWalk.StepAt
  rw [hstep]
  split_ifs with h
  · rw [S.realize_initF, and_iff_right h.1, and_iff_right h.2]
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h1 h2 => absurd ⟨h1, h2⟩ h

omit [Nonempty A] in
theorem flat_not_stepAt_inl_inl (m n : S.Mode) (t t' : S.FlatCoord D → A) :
    ¬(S.flat D det).StepAt z (Sum.inl m, t) (Sum.inl n, t') :=
  fun h => h

omit [Nonempty A] in
theorem flat_stepAt_inr_inl (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (n : S.Mode)
    (t t' : S.FlatCoord D → A) :
    (S.flat D det).StepAt z (Sum.inr ⟨p, d⟩, t) (Sum.inl n, t') ↔
      p.2 = n ∧ (D p.1 p.2).ExitAt (dpar t z) (d, tsl t p) true ∧
        tx t' = ty t ∧ (∀ (i : Fin S.k) (a : A), t' (Sum.inl (Sum.inr i)) ≤ a) ∧
          ∀ (c : Σ p : S.Mode × S.Mode, (D p.1 p.2).Coord) (a : A), t' (Sum.inr c) ≤ a := by
  classical
  have hstep : (S.flat D det).step (Sum.inr ⟨p, d⟩) (Sum.inl n) =
      if p.2 = n then S.retF D p d else ⊥ := rfl
  unfold CoordWalk.StepAt
  rw [hstep]
  split_ifs with h
  · rw [S.realize_retF, and_iff_right h]
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

/-- A step between decider nodes of the *same* pair of modes: the run, or an
advance. -/
theorem flat_stepAt_inr_inr_same (p : S.Mode × S.Mode) (d d' : (D p.1 p.2).Mode)
    (t t' : S.FlatCoord D → A) :
    (S.flat D det).StepAt z (Sum.inr ⟨p, d⟩, t) (Sum.inr ⟨p, d'⟩, t') ↔
      ((D p.1 p.2).StepAt (dpar t z) (d, tsl t p) (d', tsl t' p) ∧
          ∀ c, ¬S.InSlice D p c → t' c = t c) ∨
        (det = true ∧ d' = (D p.1 p.2).start ∧ S.Adv D z p d p t t') := by
  classical
  have hstep : (S.flat D det).step (Sum.inr ⟨p, d⟩) (Sum.inr ⟨p, d'⟩) =
      S.innerF D det p d p d' := rfl
  unfold CoordWalk.StepAt
  rw [hstep, innerF, dif_pos rfl, Formula.realize_sup, S.realize_runF]
  refine or_congr Iff.rfl ?_
  split_ifs with h
  · rw [S.realize_advF]
    exact ⟨fun h' => ⟨h.1, h.2, h'⟩, fun h' => h'.2.2⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h1 h2 => absurd ⟨h1, h2⟩ h

/-- A step between decider nodes of *different* pairs of modes: an advance
only. -/
theorem flat_stepAt_inr_inr_ne {p p' : S.Mode × S.Mode} (hne : p ≠ p') (d : (D p.1 p.2).Mode)
    (d' : (D p'.1 p'.2).Mode) (t t' : S.FlatCoord D → A) :
    (S.flat D det).StepAt z (Sum.inr ⟨p, d⟩, t) (Sum.inr ⟨p', d'⟩, t') ↔
      det = true ∧ d' = (D p'.1 p'.2).start ∧ S.Adv D z p d p' t t' := by
  classical
  have hstep : (S.flat D det).step (Sum.inr ⟨p, d⟩) (Sum.inr ⟨p', d'⟩) =
      S.innerF D det p d p' d' := rfl
  unfold CoordWalk.StepAt
  rw [hstep, innerF, dif_neg hne, Formula.realize_sup]
  simp only [Formula.realize_bot, false_or]
  split_ifs with h
  · rw [S.realize_advF]
    exact ⟨fun h' => ⟨h.1, h.2, h'⟩, fun h' => h'.2.2⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h1 h2 => absurd ⟨h1, h2⟩ h

end Semantics

/-! #### Correctness -/

section Correctness

variable {det : Bool} {A : Type} [L.Structure A] [LinearOrder A]
  [instE : ((L.sum Language.order).sum B.lang).Structure A] (z : Fin S.par → A)

omit [L.Structure A] [LinearOrder A] instE in
theorem dpar_eq (t : S.FlatCoord D → A) : Sum.elim (Sum.elim (tx t) (ty t)) z = dpar t z := by
  funext i
  rcases i with (i | i) | i <;> rfl

omit [L.Structure A] [LinearOrder A] instE in
theorem tuple_ext {t t' : S.FlatCoord D → A} (hx : tx t' = tx t) (hy : ty t' = ty t)
    (hs : ∀ p, tsl t' p = tsl t p) : t' = t := by
  funext c
  rcases c with (i | i) | ⟨p, c⟩
  · exact congrFun hx i
  · exact congrFun hy i
  · exact congrFun (hs p) c

omit [L.Structure A] [LinearOrder A] instE in
theorem tx_flatEnc (a₀ : A) (a : S.Node A) : tx (S.flatEnc D det a₀ a).2 = a.2 := rfl

omit [L.Structure A] [LinearOrder A] instE in
theorem ty_flatEnc (a₀ : A) (a : S.Node A) : ty (S.flatEnc D det a₀ a).2 = fun _ => a₀ := rfl

omit [L.Structure A] instE in
/-- Coordinates at the minimum are equal. -/
theorem bot_unique {u u' : A} (h : ∀ a, u ≤ a) (h' : ∀ a, u' ≤ a) : u = u' :=
  le_antisymm (h u') (h' u)

/-- The step deciders decide the steps of the outer walk. -/
def DecidesSteps : Prop :=
  ∀ (p : S.Mode × S.Mode) (x y : Fin S.k → A),
    (D p.1 p.2).Decides (Sum.elim (Sum.elim x y) z) (S.StepAt z (p.1, x) (p.2, y))

/-- What the flat walk may have reached from the encoding of `a`: an outer
node reached from `a`, or a decider node whose outer node is reached from
`a` and whose decider has run from its start. -/
def FlatInv (a : S.Node A) (c : (S.flat D det).Node A) : Prop :=
  (∃ (m : S.Mode) (t' : S.FlatCoord D → A), c = (Sum.inl m, t') ∧ S.ReachAt z a (m, tx t')) ∨
    (∃ (p : S.Mode × S.Mode) (d : (D p.1 p.2).Mode) (t' : S.FlatCoord D → A),
      c = (Sum.inr ⟨p, d⟩, t') ∧ S.ReachAt z a (p.1, tx t') ∧
        ∃ u₀, (D p.1 p.2).ReachAt (dpar t' z) ((D p.1 p.2).start, u₀) (d, tsl t' p))

variable {z} [Nonempty A]

theorem flatInv_of_reachAt (hD : S.DecidesSteps D z) (a₀ : A) (a : S.Node A)
    {c : (S.flat D det).Node A} (h : (S.flat D det).ReachAt z (S.flatEnc D det a₀ a) c) :
    S.FlatInv D z (det := det) a c := by
  refine reach_invariant (P := S.FlatInv D z (det := det) a) (fun c b hc hcb => ?_) h
    (Or.inl ⟨a.1, _, rfl, Relation.ReflTransGen.refl⟩)
  obtain ⟨mb, tb⟩ := b
  rcases hc with ⟨m, t', rfl, hr⟩ | ⟨p, d, t', rfl, hr, u₀, hd⟩
  · rcases mb with n | ⟨p, d⟩
    · exact absurd hcb (S.flat_not_stepAt_inl_inl D z m n t' tb)
    · obtain ⟨hp, rfl, -, hx, -⟩ := (S.flat_stepAt_inl_inr D z m p d t' tb).mp hcb
      refine Or.inr ⟨p, _, tb, rfl, ?_, _, Relation.ReflTransGen.refl⟩
      have h' := hr
      rw [← hp, ← hx] at h'
      exact h'
  · rcases mb with n | ⟨p', d'⟩
    · obtain ⟨hp, he, hx, -, -⟩ := (S.flat_stepAt_inr_inl D z p d n t' tb).mp hcb
      refine Or.inl ⟨n, tb, rfl, hr.tail ?_⟩
      have hd' := hd
      have he' := he
      rw [← S.dpar_eq D z t'] at hd' he'
      have := ((hD p (tx t') (ty t') _).1).mp ⟨_, hd', he'⟩
      rw [hp, ← hx] at this
      exact this
    · by_cases hpp : p = p'
      · subst hpp
        rcases (S.flat_stepAt_inr_inr_same D z p d d' t' tb).mp hcb with
          ⟨hs, hcopy⟩ | ⟨-, rfl, -, -, -, hx, -⟩
        · have hpar : dpar tb z = dpar t' z := by
            refine congrArg (fun f => Sum.elim f z) (funext fun q => hcopy (Sum.inl q) ?_)
            rintro ⟨d, h⟩
            exact absurd h Sum.inl_ne_inr
          have hx : tx tb = tx t' :=
            funext fun i => hcopy _ (by rintro ⟨d, h⟩; exact absurd h Sum.inl_ne_inr)
          refine Or.inr ⟨p, d', tb, rfl, hx ▸ hr, u₀, ?_⟩
          rw [hpar]
          exact hd.tail hs
        · exact Or.inr ⟨p, _, tb, rfl, hx ▸ hr, _, Relation.ReflTransGen.refl⟩
      · obtain ⟨-, rfl, hp1, -, -, hx, -⟩ := (S.flat_stepAt_inr_inr_ne D z hpp d d' t' tb).mp hcb
        refine Or.inr ⟨p', _, tb, rfl, ?_, _, Relation.ReflTransGen.refl⟩
        have h' := hr
        rw [← hp1, ← hx] at h'
        exact h'

/-- **The flat walk reaches only what the outer walk reaches.** -/
theorem reachAt_of_flat_reachAt (hD : S.DecidesSteps D z) (a₀ : A) (a b : S.Node A)
    (h : (S.flat D det).ReachAt z (S.flatEnc D det a₀ a) (S.flatEnc D det a₀ b)) :
    S.ReachAt z a b := by
  rcases S.flatInv_of_reachAt D hD a₀ a h with ⟨m, t', he, hr⟩ | ⟨p, d, t', he, -⟩
  · obtain ⟨hm, ht⟩ := Prod.mk.inj he
    rw [← Sum.inl.inj hm, ← ht] at hr
    exact hr
  · exact absurd (congrArg Prod.fst he) Sum.inl_ne_inr

omit instE in
/-- A run of a decider lifts to the flat walk, on its slice. -/
theorem flat_reachAt_of_decider (p : S.Mode × S.Mode) (t : S.FlatCoord D → A)
    {e e' : (D p.1 p.2).Node A} (h : (D p.1 p.2).ReachAt (dpar t z) e e') :
    (S.flat D det).ReachAt z (Sum.inr ⟨p, e.1⟩, setSlice t p e.2)
      (Sum.inr ⟨p, e'.1⟩, setSlice t p e'.2) := by
  refine Relation.ReflTransGen.lift
    (fun f : (D p.1 p.2).Node A => ((Sum.inr ⟨p, f.1⟩ : S.FlatMode D), setSlice t p f.2))
    (fun f f' hff' => ?_) _ _ h
  refine (S.flat_stepAt_inr_inr_same D z p f.1 f'.1 _ _).mpr (Or.inl ⟨?_, fun c hc => ?_⟩)
  · rw [tsl_setSlice_self, tsl_setSlice_self]
    change (D p.1 p.2).StepAt (Sum.elim (setSlice t p f.2 ∘ Sum.inl) z) f f'
    rw [setSlice_comp_inl]
    exact hff'
  · rw [setSlice_of_not_inSlice _ _ _ _ hc, setSlice_of_not_inSlice _ _ _ _ hc]

/-- **Finishing a step**: from the start of the decider of a step that holds,
the flat walk reaches the encoding of the step's target. -/
theorem flat_finish (hD : S.DecidesSteps D z) {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (m n : S.Mode) (x y : Fin S.k → A) (h : S.StepAt z (m, x) (n, y)) :
    (S.flat D det).ReachAt z
      (Sum.inr ⟨(m, n), (D m n).start⟩, Sum.elim (Sum.elim x y) fun _ => a₀)
      (S.flatEnc D det a₀ (n, y)) := by
  set T : S.FlatCoord D → A := Sum.elim (Sum.elim x y) fun _ => a₀ with hT
  have hpar : Sum.elim (Sum.elim x y) z = dpar T z := by
    funext i
    rcases i with (i | i) | i <;> rfl
  obtain ⟨e, he, hex⟩ := ((hD (m, n) x y _).1).mpr h
  rw [hpar] at he hex
  have hlift := S.flat_reachAt_of_decider D (det := det) (m, n) T he
  rw [setSlice_tsl] at hlift
  refine hlift.tail ((S.flat_stepAt_inr_inl D z (m, n) e.1 n (setSlice T (m, n) e.2)
    (S.flatEnc D det a₀ (n, y)).2).mpr ?_)
  refine ⟨rfl, ?_, rfl, fun _ a => hbot a, fun _ a => hbot a⟩
  rw [tsl_setSlice_self, dpar_setSlice]
  exact hex

/-- **Guessing: the flat walk reaches what the outer walk reaches.** -/
theorem flat_reachAt_of_reachAt (hD : S.DecidesSteps D z) {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    {a b : S.Node A} (h : S.ReachAt z a b) :
    (S.flat D false).ReachAt z (S.flatEnc D false a₀ a) (S.flatEnc D false a₀ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    refine ih.trans (Relation.ReflTransGen.head ?_ (S.flat_finish D hD hbot c.1 d.1 c.2 d.2 hcd))
    refine (S.flat_stepAt_inl_inr D z c.1 (c.1, d.1) (D c.1 d.1).start _ _).mpr
      ⟨rfl, rfl, fun h => Bool.noConfusion h, rfl, fun _ a => hbot a⟩

/-- The candidates, ordered. -/
abbrev Cand (A : Type) [LinearOrder A] : Type := Lex (S.Mode × Lex (Fin S.k → A))

/-- **Searching: from a candidate at or before the successor, the flat walk
reaches the encoding of the successor**, the outer walk being functional. -/
theorem flat_search [Finite A] (hD : S.DecidesSteps D z) {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (hS : ∀ a b c : S.Node A, S.StepAt z a b → S.StepAt z a c → b = c)
    (m n : S.Mode) (x y : Fin S.k → A) (h : S.StepAt z (m, x) (n, y)) (κ : S.Cand A) :
    letI := S.outerModeOrder
    ∀ (n' : S.Mode) (y' : Fin S.k → A), toLex (n', toLex y') = κ → κ ≤ toLex (n, toLex y) →
      (S.flat D true).ReachAt z
        (Sum.inr ⟨(m, n'), (D m n').start⟩, Sum.elim (Sum.elim x y') fun _ => a₀)
        (S.flatEnc D true a₀ (n, y)) := by
  let := S.outerModeOrder
  have key : ∀ (n' : S.Mode) (y' : Fin S.k → A), toLex (n', toLex y') < toLex (n, toLex y) →
      ∀ (n₂ : S.Mode) (y₂ : Fin S.k → A), toLex (n', toLex y') ⋖ toLex (n₂, toLex y₂) →
      (S.flat D true).ReachAt z
        (Sum.inr ⟨(m, n₂), (D m n₂).start⟩, Sum.elim (Sum.elim x y₂) fun _ => a₀)
        (S.flatEnc D true a₀ (n, y)) →
      (S.flat D true).ReachAt z
        (Sum.inr ⟨(m, n'), (D m n').start⟩, Sum.elim (Sum.elim x y') fun _ => a₀)
        (S.flatEnc D true a₀ (n, y)) := by
    intro n' y' hlt n₂ y₂ hcov ih
    set T : S.FlatCoord D → A := Sum.elim (Sum.elim x y') fun _ => a₀ with hT
    have hpar : Sum.elim (Sum.elim x y') z = dpar T z := by
      funext i
      rcases i with (i | i) | i <;> rfl
    have hne : ¬S.StepAt z (m, x) (n', y') := by
      intro hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hS _ _ _ hs h)
      exact lt_irrefl _ hlt
    obtain ⟨e, he, hex⟩ := ((hD (m, n') x y' _).2).mpr hne
    rw [hpar] at he hex
    have hlift := S.flat_reachAt_of_decider D (det := true) (m, n') T he
    rw [setSlice_tsl] at hlift
    have hadv : S.Adv D z (m, n') e.1 (m, n₂) (setSlice T (m, n') e.2)
        (Sum.elim (Sum.elim x y₂) fun _ => a₀) := by
      refine ⟨rfl, ?_, ?_, rfl, fun _ a => hbot a⟩
      · rw [tsl_setSlice_self, dpar_setSlice]
        exact hex
      · exact hcov
    refine hlift.trans (Relation.ReflTransGen.head ?_ ih)
    by_cases hnn : n' = n₂
    · subst hnn
      exact (S.flat_stepAt_inr_inr_same D z (m, n') e.1 _ _ _).mpr (Or.inr ⟨rfl, rfl, hadv⟩)
    · have hp : ((m, n') : S.Mode × S.Mode) ≠ (m, n₂) := fun h => hnn (congrArg Prod.snd h)
      exact (S.flat_stepAt_inr_inr_ne D z hp e.1 _ _ _).mpr ⟨rfl, rfl, hadv⟩
  induction κ using order_induction_down with
  | hmax κ hκ =>
    intro n' y' hκ' hle
    have heq : toLex (n, toLex y) = toLex (n', toLex y') := (hκ' ▸ le_antisymm hle (hκ _)).symm
    obtain ⟨hn, hy⟩ := Prod.mk.inj (toLex.injective heq)
    obtain rfl := hn
    obtain rfl := toLex.injective hy
    exact S.flat_finish D hD hbot m n x y h
  | hstep κ κ' hlt hnb ih =>
    intro n' y' hκ' hle
    obtain ⟨n₂, y₂, rfl⟩ : ∃ (n₂ : S.Mode) (y₂ : Fin S.k → A), toLex (n₂, toLex y₂) = κ' :=
      ⟨(ofLex κ').1, ofLex (ofLex κ').2, rfl⟩
    rcases lt_or_eq_of_le hle with hlt' | heq
    · subst hκ'
      have hcov : toLex (n', toLex y') ⋖ toLex (n₂, toLex y₂) :=
        ⟨hlt, fun a h1 h2 => hnb a ⟨h1, h2⟩⟩
      exact key n' y' hlt' n₂ y₂ hcov (ih n₂ y₂ rfl (hcov.ge_of_gt hlt'))
    · subst hκ'
      obtain ⟨hn, hy⟩ := Prod.mk.inj (toLex.injective heq.symm)
      obtain rfl := hn
      obtain rfl := toLex.injective hy
      exact S.flat_finish D hD hbot m n x y h

/-- **Searching: the flat walk reaches what a functional outer walk
reaches.** -/
theorem flat_reachAt_of_reachAt_det [Finite A] (hD : S.DecidesSteps D z) {a₀ : A}
    (hbot : ∀ a : A, a₀ ≤ a)
    (hS : ∀ a b c : S.Node A, S.StepAt z a b → S.StepAt z a c → b = c) {a b : S.Node A}
    (h : S.ReachAt z a b) :
    (S.flat D true).ReachAt z (S.flatEnc D true a₀ a) (S.flatEnc D true a₀ b) := by
  let := S.outerModeOrder
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    obtain ⟨cmin, -, hcmin⟩ := (Finite.to_wellFoundedLT (α := S.Mode)).wf.has_min Set.univ
      ⟨c.1, Set.mem_univ _⟩
    have hcmin' : ∀ c' : S.Mode, cmin ≤ c' := fun c' => not_lt.mp (hcmin c' (Set.mem_univ c'))
    refine ih.trans (Relation.ReflTransGen.head ?_
      (S.flat_search D hD hbot hS c.1 d.1 c.2 d.2 hcd (toLex (cmin, toLex fun _ => a₀))
        cmin (fun _ => a₀) rfl ?_))
    · refine (S.flat_stepAt_inl_inr D z c.1 (c.1, cmin) (D c.1 cmin).start _ _).mpr
        ⟨rfl, rfl, fun _ => ⟨hcmin', fun _ a => hbot a⟩, rfl, fun _ a => hbot a⟩
    · exact prodLex_isBot_iff.mpr ⟨hcmin', tup_isBot_iff.mpr fun _ a => hbot a⟩ _

/-- **Guessing simulates the outer walk**, at the encodings. -/
theorem reachAt_flat_iff (hD : S.DecidesSteps D z) {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a)
    (a b : S.Node A) :
    (S.flat D false).ReachAt z (S.flatEnc D false a₀ a) (S.flatEnc D false a₀ b) ↔
      S.ReachAt z a b :=
  ⟨S.reachAt_of_flat_reachAt D hD a₀ a b, S.flat_reachAt_of_reachAt D hD hbot⟩

/-- **Searching simulates a functional outer walk**, at the encodings. -/
theorem reachAt_flat_iff_of_functional [Finite A] (hD : S.DecidesSteps D z) {a₀ : A}
    (hbot : ∀ a : A, a₀ ≤ a) (hS : ∀ a b c : S.Node A, S.StepAt z a b → S.StepAt z a c → b = c)
    (a b : S.Node A) :
    (S.flat D true).ReachAt z (S.flatEnc D true a₀ a) (S.flatEnc D true a₀ b) ↔
      S.ReachAt z a b :=
  ⟨S.reachAt_of_flat_reachAt D hD a₀ a b, S.flat_reachAt_of_reachAt_det D hD hbot hS⟩

/-! #### Functionality of the searching flat walk -/

omit instE [Nonempty A] in
/-- Two advances from the same node go to the same node. -/
theorem adv_unique {p p₁ p₂ : S.Mode × S.Mode} {d : (D p.1 p.2).Mode} {t t₁ t₂ : S.FlatCoord D → A}
    (h₁ : S.Adv D z p d p₁ t t₁) (h₂ : S.Adv D z p d p₂ t t₂) : p₁ = p₂ ∧ t₁ = t₂ := by
  let := S.outerModeOrder
  obtain ⟨hp₁, -, hc₁, hx₁, hs₁⟩ := h₁
  obtain ⟨hp₂, -, hc₂, hx₂, hs₂⟩ := h₂
  have hκ := covBy_right_unique hc₁ hc₂
  obtain ⟨hn, hy⟩ := Prod.mk.inj (toLex.injective hκ)
  refine ⟨Prod.ext (hp₁.trans hp₂.symm) hn, S.tuple_ext D (hx₁.trans hx₂.symm) (toLex.injective hy)
    fun q => funext fun c => bot_unique (hs₁ ⟨q, c⟩) (hs₂ ⟨q, c⟩)⟩

omit instE in
/-- **The searching flat walk is functional** when the deciders are. -/
theorem functional_flat (hDf : ∀ p : S.Mode × S.Mode, (D p.1 p.2).Functional A) :
    (S.flat D true).Functional A := by
  let := S.outerModeOrder
  rintro z ⟨m, t⟩ ⟨m₁, t₁⟩ ⟨m₂, t₂⟩ h₁ h₂
  rcases m with m | ⟨p, d⟩
  · rcases m₁ with n₁ | ⟨p₁, d₁⟩
    · exact absurd h₁ (S.flat_not_stepAt_inl_inl D z m n₁ t t₁)
    rcases m₂ with n₂ | ⟨p₂, d₂⟩
    · exact absurd h₂ (S.flat_not_stepAt_inl_inl D z m n₂ t t₂)
    obtain ⟨hp₁, hd₁, hdet₁, hx₁, hs₁⟩ := (S.flat_stepAt_inl_inr D z m p₁ d₁ t t₁).mp h₁
    obtain ⟨hp₂, hd₂, hdet₂, hx₂, hs₂⟩ := (S.flat_stepAt_inl_inr D z m p₂ d₂ t t₂).mp h₂
    obtain ⟨hmin₁, hy₁⟩ := hdet₁ rfl
    obtain ⟨hmin₂, hy₂⟩ := hdet₂ rfl
    have hp : p₁ = p₂ := Prod.ext (hp₁.trans hp₂.symm) (le_antisymm (hmin₁ _) (hmin₂ _))
    subst hp
    rw [hd₁, hd₂, S.tuple_ext D (hx₁.trans hx₂.symm) (funext fun i => bot_unique (hy₁ i) (hy₂ i))
      fun q => funext fun c => bot_unique (hs₁ ⟨q, c⟩) (hs₂ ⟨q, c⟩)]
  · have hsame : ∀ {p' : S.Mode × S.Mode} {d' : (D p'.1 p'.2).Mode} {t' : S.FlatCoord D → A},
        (S.flat D true).StepAt z (Sum.inr ⟨p, d⟩, t) (Sum.inr ⟨p', d'⟩, t') →
        (∃ h : p = p', (D p.1 p.2).StepAt (dpar t z) (d, tsl t p)
            (cast (congrArg (fun q : S.Mode × S.Mode => (D q.1 q.2).Mode) h.symm) d', tsl t' p) ∧
          ∀ c, ¬S.InSlice D p c → t' c = t c) ∨
        (d' = (D p'.1 p'.2).start ∧ S.Adv D z p d p' t t') := by
      intro p' d' t' h
      by_cases hp : p = p'
      · subst hp
        rcases (S.flat_stepAt_inr_inr_same D z p d d' t t').mp h with ⟨hs, hc⟩ | ⟨-, hd, ha⟩
        · exact Or.inl ⟨rfl, hs, hc⟩
        · exact Or.inr ⟨hd, ha⟩
      · obtain ⟨-, hd, ha⟩ := (S.flat_stepAt_inr_inr_ne D z hp d d' t t').mp h
        exact Or.inr ⟨hd, ha⟩
    rcases m₁ with n₁ | ⟨p₁, d₁⟩ <;> rcases m₂ with n₂ | ⟨p₂, d₂⟩
    · obtain ⟨hn₁, he₁, hx₁, hy₁, hs₁⟩ := (S.flat_stepAt_inr_inl D z p d n₁ t t₁).mp h₁
      obtain ⟨hn₂, he₂, hx₂, hy₂, hs₂⟩ := (S.flat_stepAt_inr_inl D z p d n₂ t t₂).mp h₂
      rw [← hn₁, ← hn₂, S.tuple_ext D (hx₁.trans hx₂.symm)
        (funext fun i => bot_unique (hy₁ i) (hy₂ i))
        fun q => funext fun c => bot_unique (hs₁ ⟨q, c⟩) (hs₂ ⟨q, c⟩)]
    · obtain ⟨-, he₁, -⟩ := (S.flat_stepAt_inr_inl D z p d n₁ t t₁).mp h₁
      rcases hsame h₂ with ⟨hp', hs, -⟩ | ⟨-, -, he₂, -⟩
      · exact absurd he₁ ((hDf p).not_exit_of_step hs)
      · exact absurd ((hDf p).exit_unique he₁ he₂) Bool.noConfusion
    · obtain ⟨-, he₂, -⟩ := (S.flat_stepAt_inr_inl D z p d n₂ t t₂).mp h₂
      rcases hsame h₁ with ⟨hp', hs, -⟩ | ⟨-, -, he₁, -⟩
      · exact absurd he₂ ((hDf p).not_exit_of_step hs)
      · exact absurd ((hDf p).exit_unique he₂ he₁) Bool.noConfusion
    · rcases hsame h₁ with ⟨hp₁, hs₁, hc₁⟩ | ⟨hd₁, ha₁⟩ <;>
        rcases hsame h₂ with ⟨hp₂, hs₂, hc₂⟩ | ⟨hd₂, ha₂⟩
      · subst hp₁
        subst hp₂
        have hn := (hDf p).step_unique hs₁ hs₂
        obtain ⟨hd, hsl⟩ := Prod.mk.inj hn
        have ht : t₁ = t₂ := by
          funext c
          by_cases hc : S.InSlice D p c
          · obtain ⟨e, rfl⟩ := hc
            exact congrFun hsl e
          · rw [hc₁ c hc, hc₂ c hc]
        rw [ht]
        exact congrArg (fun d => ((Sum.inr ⟨p, d⟩ : S.FlatMode D), t₂)) hd
      · subst hp₁
        exact absurd ha₂.2.1 ((hDf p).not_exit_of_step hs₁)
      · subst hp₂
        exact absurd ha₁.2.1 ((hDf p).not_exit_of_step hs₂)
      · obtain ⟨hp, ht⟩ := S.adv_unique D ha₁ ha₂
        subst hp
        rw [hd₁, hd₂, ht]

end Correctness

end ParamTCSpec

end DescriptiveComplexity
