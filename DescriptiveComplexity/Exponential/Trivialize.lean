/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Increment
import DescriptiveComplexity.TransitiveClosure

/-!
# Trading an expansion's domain for a mark

An expansion carves its universe out of the tagged assignments by a **domain
sentence**, and that is what makes walking it hard over the base: the immediate
successor of a point is the least *point* above it, and skipping the tagged
assignments that fail the domain sentence is not a first-order condition — "no
point in between" quantifies over block assignments.

This file removes the difficulty at the source. `X.trivialize` is the same
expansion with the same tags and the same block, its domain sentence replaced
by `⊤` and the old domain kept as a new **unary symbol** of the expanded
vocabulary. Its universe is therefore *every* tagged assignment, where the
successor is the plain binary increment
(`DescriptiveComplexity.SOBlock.succAssignF`), and the old universe is the part
the mark selects.

What has to move along is the problem: a walk over the old universe becomes a
walk over the new one whose formulas are **relativized** to the mark
(`DescriptiveComplexity.ExpExpansion.relSpec`), which is the standard guard
insertion of `DescriptiveComplexity.relativizeTo` together with the renaming of
the vocabulary. The two are done by one recursion here
(`DescriptiveComplexity.ExpExpansion.relLift`) rather than composed, so that its
correctness is a single induction stated directly at the inclusion of the old
universe into the new — which is what the walk correspondence consumes.

The inclusion is *definitional*: the trivialized expansion has the same tags and
the same block, so its points are the same pairs, its order is the same order,
and its relations are given by the same sentences. Nothing but the domain
condition changes, and that is a proof field of the subtype.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The marking vocabulary -/

/-- Relation symbols of the marking vocabulary: one unary symbol. -/
inductive markRel : ℕ → Type
  /-- `real x`: the point `x` was in the domain of the original expansion. -/
  | real : markRel 1
  deriving DecidableEq

/-- The vocabulary of a single unary relation, marking the points an expansion's
domain sentence admits. -/
def markLang : Language.{0, 0} := ⟨fun _ => Empty, markRel⟩
  deriving IsRelational

namespace ExpExpansion

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-! ### The trivialized expansion -/

/-- Reading a sentence over one copy of the block inside the one-fold
replication, which is the shape a defining sentence of a unary symbol has. -/
def rep1LHom :
    ((L.sum Language.order).sum X.B.lang) →ᴸ
      ((L.sum Language.order).sum (X.B.replicate 1).lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (fun i => ((0 : Fin 1), i)) fun _ => rfl)

variable {X} {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_rep1LHom (ρs : Fin 1 → X.B.Assignment A)
    (φ : ((L.sum Language.order).sum X.B.lang).Sentence) :
    (@Sentence.Realize _ A
        ((X.B.replicate 1).structure₁ (L := L.sum Language.order) (X.B.replicateAssign ρs))
        (X.rep1LHom.onSentence φ) ↔
      @Sentence.Realize _ A (X.B.structure₁ (L := L.sum Language.order) (ρs 0)) φ) :=
  SOBlock.realize_homSentence (B := X.B) (B' := X.B.replicate 1) _ _ _ φ

variable (X)

open Classical in
/-- **The expansion with a trivial domain**: the same tags and the same block,
so the same candidate points, but every one of them admitted, the old domain
sentence surviving as the defining sentence of a new unary symbol. -/
noncomputable def trivialize : ExpExpansion L where
  Tag := X.Tag
  B := X.B
  E := X.E.sum markLang
  dom _ := ⊤
  relSentence {n} r τ :=
    match n, r with
    | _, Sum.inl s => X.relSentence s τ
    | _, Sum.inr .real => X.rep1LHom.onSentence (X.dom (τ 0))
  dom_nonempty := fun A _ _ _ _ => by
    obtain ⟨t, ρ, -⟩ := X.dom_nonempty A
    letI := X.B.structure₁ (L := L.sum Language.order) ρ
    exact ⟨t, ρ, Formula.realize_top.mpr trivial⟩

/-- The marking symbol of the trivialized vocabulary. -/
abbrev realSym : X.trivialize.E.Relations 1 := Sum.inr .real

variable {X}

/-- **Every candidate point is a point** of the trivialized expansion. -/
theorem trivialize_domHolds (p : X.trivialize.Point A) : DomHolds (X := X.trivialize) p := by
  letI := X.trivialize.B.structure₁ (L := L.sum Language.order) p.2
  exact Formula.realize_top.mpr trivial

/-- A point of the trivialized expansion, from a candidate point. -/
def trivPt (p : X.Point A) : X.trivialize.Map A :=
  ⟨p, trivialize_domHolds p⟩

/-- The inclusion of the original universe into the trivialized one. -/
def trivIncl (p : X.Map A) : X.trivialize.Map A :=
  trivPt p.1

theorem trivIncl_injective : Function.Injective (trivIncl (X := X) (A := A)) := by
  intro p q h
  have h1 : (trivIncl p).val = (trivIncl q).val := congrArg Subtype.val h
  exact Subtype.ext h1

/-- **The mark holds exactly of the old points.** -/
theorem relMap_realSym (q : X.trivialize.Map A) :
    (@RelMap X.trivialize.E (X.trivialize.Map A) (X.trivialize.mapStructure A) 1
        X.realSym ![q] ↔ DomHolds (X := X) q.1) := by
  rw [relMap_map]
  exact realize_rep1LHom _ (X.dom q.1.1)

/-- **The relations are unchanged**: a relation of the original vocabulary holds
of included points exactly when it held of them. -/
theorem relMap_trivIncl {n : ℕ} (r : X.E.Relations n) (xs : Fin n → X.Map A) :
    (@RelMap X.trivialize.E (X.trivialize.Map A) (X.trivialize.mapStructure A) n
        (Sum.inl r) (fun i => trivIncl (xs i)) ↔
      @RelMap X.E (X.Map A) (X.mapStructure A) n r xs) :=
  Iff.rfl

/-- **The included points are exactly the marked ones.** -/
theorem exists_trivIncl_iff (q : X.trivialize.Map A) :
    (∃ p : X.Map A, trivIncl p = q) ↔
      @RelMap X.trivialize.E (X.trivialize.Map A) (X.trivialize.mapStructure A) 1
        X.realSym ![q] := by
  rw [relMap_realSym]
  exact ⟨fun ⟨p, hp⟩ => hp ▸ p.2, fun h => ⟨⟨q.1, h⟩, rfl⟩⟩

variable [Finite A] [Nonempty A]

/-- **The order is unchanged**: the trivialized expansion orders its points by
the same key, tag first and then the assignment as a binary number. -/
theorem trivIncl_le_iff (p q : X.Map A) :
    ((X.trivialize.mapLinearOrder A).le (trivIncl p) (trivIncl q) ↔
      (X.mapLinearOrder A).le p q) :=
  Iff.rfl

/-! ### Relativizing a formula to the mark -/

variable (X)

/-- A term of the original vocabulary, read in the marked one: over relational
vocabularies a term is a variable, so there is nothing to do. -/
def termLift {β : Type} :
    (X.E.sum Language.order).Term β → (X.trivialize.E.sum Language.order).Term β
  | .var x => .var x
  | .func f _ => isEmptyElim f

/-- A relation symbol of the original vocabulary, in the marked one. -/
noncomputable def symLift {n : ℕ} :
    (X.E.sum Language.order).Relations n → (X.trivialize.E.sum Language.order).Relations n
  | Sum.inl s => Sum.inl (Sum.inl s)
  | Sum.inr o => Sum.inr o

/-- The guard “the last bound variable is marked”. -/
noncomputable def markGuard {β : Type} (n : ℕ) :
    (X.trivialize.E.sum Language.order).BoundedFormula β (n + 1) :=
  Relations.boundedFormula₁ (Sum.inl X.realSym) (Term.var (Sum.inr (Fin.last n)))

/-- The mark, as a formula of one variable. -/
noncomputable def markF {β : Type} (x : β) :
    (X.trivialize.E.sum Language.order).Formula β :=
  Relations.boundedFormula₁ (Sum.inl X.realSym) (Term.var (Sum.inl x))

/-- **Lifting and relativizing at once**: the formula read in the trivialized
expansion, with every quantifier restricted to the marked points. Composing
`FirstOrder.Language.LHom.onBoundedFormula` with
`DescriptiveComplexity.relativizeTo` would do the same, but this way its
correctness is one induction, stated directly at the inclusion of the old
universe into the new. -/
noncomputable def relLift {β : Type} :
    ∀ {n : ℕ}, (X.E.sum Language.order).BoundedFormula β n →
      (X.trivialize.E.sum Language.order).BoundedFormula β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (termLift X t₁) (termLift X t₂)
  | _, .rel r ts => .rel (symLift X r) fun i => termLift X (ts i)
  | _, .imp φ ψ => .imp (relLift φ) (relLift ψ)
  | n, .all φ => .all ((markGuard X n).imp (relLift φ))

variable {X}

theorem realize_termLift {β : Type} (v : β → X.Map A) (t : (X.E.sum Language.order).Term β) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((termLift X t).realize fun b => trivIncl (v b)) = trivIncl (t.realize v) := by
  match t with
  | .var _ => rfl
  | .func f _ => exact isEmptyElim f

theorem realize_termLift_elim {β : Type} {n : ℕ} (v : β → X.Map A) (xs : Fin n → X.Map A)
    (t : (X.E.sum Language.order).Term (β ⊕ Fin n)) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((termLift X t).realize (Sum.elim (fun b => trivIncl (v b)) fun i => trivIncl (xs i))) =
      trivIncl (t.realize (Sum.elim v xs)) := by
  have h : (Sum.elim (fun b => trivIncl (v b)) fun i => trivIncl (xs i)) =
      fun x => trivIncl (Sum.elim v xs x) := by
    funext x; cases x <;> rfl
  rw [h]
  exact realize_termLift _ t

theorem realize_markF {β : Type} (v : β → X.trivialize.Map A) (x : β) :
    letI := X.trivialize.mapLinearOrder A
    ((markF X x).Realize v ↔ ∃ p : X.Map A, trivIncl p = v x) := by
  letI := X.trivialize.mapLinearOrder A
  exact Iff.trans BoundedFormula.realize_rel₁ (exists_trivIncl_iff (v x)).symm

/-- **The relativized formula says of the marked points what the original said
of the old ones.** -/
theorem realize_relLift {β : Type} :
    ∀ {n : ℕ} (φ : (X.E.sum Language.order).BoundedFormula β n) (v : β → X.Map A)
      (xs : Fin n → X.Map A),
      letI := X.mapLinearOrder A
      letI := X.trivialize.mapLinearOrder A
      ((relLift X φ).Realize (fun b => trivIncl (v b)) (fun i => trivIncl (xs i)) ↔
        φ.Realize v xs) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  intro n φ
  induction φ with
  | falsum => exact fun _ _ => Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    change ((termLift X t₁).realize _ = (termLift X t₂).realize _) ↔ _
    rw [realize_termLift_elim v xs t₁, realize_termLift_elim v xs t₂]
    exact ⟨fun h => trivIncl_injective h, fun h => congrArg _ h⟩
  | rel r ts =>
    intro v xs
    change (RelMap (symLift X r) fun i => (termLift X (ts i)).realize _) ↔
      RelMap r fun i => (ts i).realize _
    rw [funext fun i => realize_termLift_elim v xs (ts i)]
    cases r with
    | inl s => exact relMap_trivIncl s _
    | inr o => cases o with
      | le => exact trivIncl_le_iff _ _
  | imp φ ψ ihφ ihψ =>
    intro v xs
    rw [relLift, BoundedFormula.realize_imp, BoundedFormula.realize_imp, ihφ v xs, ihψ v xs]
  | @all m φ ih =>
    intro v xs
    have hsnoc : ∀ x : X.Map A,
        (Fin.snoc (fun i => trivIncl (xs i)) (trivIncl x) : Fin (m + 1) → X.trivialize.Map A) =
          fun i => trivIncl ((Fin.snoc xs x : Fin (m + 1) → X.Map A) i) := by
      intro x
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    have hguard : ∀ y : X.trivialize.Map A,
        ((markGuard X m).Realize (fun b => trivIncl (v b))
            (Fin.snoc (fun i => trivIncl (xs i)) y) ↔ ∃ p : X.Map A, trivIncl p = y) := by
      intro y
      refine Iff.trans BoundedFormula.realize_rel₁ ?_
      simp only [Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      exact (exists_trivIncl_iff y).symm
    rw [relLift]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h x
      have h' := h (trivIncl x) ((hguard (trivIncl x)).mpr ⟨x, rfl⟩)
      rw [hsnoc x] at h'
      exact (ih _ (Fin.snoc xs x)).mp h'
    · intro h y hy
      obtain ⟨x, rfl⟩ := (hguard y).mp hy
      rw [hsnoc x]
      exact (ih _ (Fin.snoc xs x)).mpr (h x)

/-- The relativized formula, at no bound variables. -/
theorem realize_relLift_formula {β : Type} (φ : (X.E.sum Language.order).Formula β)
    (v : β → X.Map A) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    (Formula.Realize (relLift X φ) (fun b => trivIncl (v b)) ↔ Formula.Realize φ v) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  refine Iff.trans ?_ (realize_relLift φ v default)
  exact iff_of_eq (congrArg (fun w : Fin 0 → X.trivialize.Map A =>
    BoundedFormula.Realize (relLift X φ) (fun b => trivIncl (v b)) w)
    (Subsingleton.elim _ _))

/-! ### The walk, carried over -/

variable (X)

/-- **The walk of a specification, carried to the trivialized expansion**: every
formula relativized to the mark, and the mark of the tuple required wherever the
walk enters a node — at a source, and at the target of a step. -/
noncomputable def relSpec (spec : TCSpec X.E) : TCSpec X.trivialize.E where
  Mode := spec.Mode
  k := spec.k
  src m := relLift X (spec.src m) ⊓
    listInf ((List.finRange spec.k).map fun i => markF X i)
  tgt m := relLift X (spec.tgt m)
  step m m' := relLift X (spec.step m m') ⊓
    listInf ((List.finRange spec.k).map fun i => markF X (Sum.inr i))

variable {X} {spec : TCSpec X.E}

/-- A node of the carried walk: the same mode, the tuple included. -/
def relNode (a : spec.Node (X.Map A)) : (relSpec X spec).Node (X.trivialize.Map A) :=
  (a.1, fun i => trivIncl (a.2 i))

omit [Finite A] [Nonempty A] in
theorem relNode_injective : Function.Injective (relNode (X := X) (A := A) (spec := spec)) := by
  rintro ⟨m, x⟩ ⟨m', x'⟩ h
  have h1 : m = m' := congrArg Prod.fst h
  have h2 : (fun i => trivIncl (x i)) = fun i => trivIncl (x' i) := congrArg Prod.snd h
  exact Prod.ext h1 (funext fun i => trivIncl_injective (congrFun h2 i))

/-- The conjoined marks hold exactly of a tuple of included points. -/
theorem realize_marks {β : Type} (sel : Fin spec.k → β) (v : β → X.trivialize.Map A) :
    letI := X.trivialize.mapLinearOrder A
    (Formula.Realize (listInf ((List.finRange spec.k).map fun i => markF X (sel i))) v ↔
      ∀ i, ∃ p : X.Map A, trivIncl p = v (sel i)) := by
  letI := X.trivialize.mapLinearOrder A
  rw [realize_listInf]
  constructor
  · intro h i
    exact (realize_markF v (sel i)).mp (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_markF v (sel i)).mpr (h i)

theorem isSrc_relNode (a : spec.Node (X.Map A)) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((relSpec X spec).IsSrc (relNode a) ↔ spec.IsSrc a) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  have hmarks : Formula.Realize
      (listInf ((List.finRange spec.k).map fun i => markF X i))
      (fun i => trivIncl (a.2 i)) :=
    (realize_marks (spec := spec) id _).mpr fun i => ⟨a.2 i, rfl⟩
  change (Formula.Realize (relLift X (spec.src a.1) ⊓
    listInf ((List.finRange spec.k).map fun i => markF X i))
      (fun i => trivIncl (a.2 i)) ↔ _)
  refine Iff.trans Formula.realize_inf (Iff.trans (and_iff_left hmarks) ?_)
  exact realize_relLift_formula (spec.src a.1) a.2

theorem isTgt_relNode (a : spec.Node (X.Map A)) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((relSpec X spec).IsTgt (relNode a) ↔ spec.IsTgt a) :=
  realize_relLift_formula (spec.tgt a.1) a.2

theorem step_relNode (a b : spec.Node (X.Map A)) :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((relSpec X spec).Step (relNode a) (relNode b) ↔ spec.Step a b) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  have hv : (Sum.elim (fun i => trivIncl (a.2 i)) fun i => trivIncl (b.2 i)) =
      fun x => trivIncl (Sum.elim a.2 b.2 x) := by
    funext x; cases x <;> rfl
  have hmarks : Formula.Realize
      (listInf ((List.finRange spec.k).map fun i => markF X (Sum.inr i)))
      (Sum.elim (fun i => trivIncl (a.2 i)) fun i => trivIncl (b.2 i)) :=
    (realize_marks (spec := spec) Sum.inr _).mpr fun i => ⟨b.2 i, rfl⟩
  change (Formula.Realize (relLift X (spec.step a.1 b.1) ⊓
    listInf ((List.finRange spec.k).map fun i => markF X (Sum.inr i)))
      (Sum.elim (fun i => trivIncl (a.2 i)) fun i => trivIncl (b.2 i)) ↔ _)
  refine Iff.trans Formula.realize_inf (Iff.trans (and_iff_left hmarks) ?_)
  rw [hv]
  exact realize_relLift_formula (spec.step a.1 b.1) (Sum.elim a.2 b.2)

omit [Finite A] [Nonempty A] in
/-- A node whose points are all marked is the image of a node of the original
walk. -/
theorem exists_relNode {u : (relSpec X spec).Node (X.trivialize.Map A)}
    (h : ∀ i, ∃ p : X.Map A, trivIncl p = u.2 i) : ∃ a : spec.Node (X.Map A), relNode a = u := by
  choose f hf using h
  exact ⟨(u.1, f), Prod.ext rfl (funext hf)⟩

theorem exists_relNode_of_isSrc {u : (relSpec X spec).Node (X.trivialize.Map A)}
    (h : letI := X.trivialize.mapLinearOrder A; (relSpec X spec).IsSrc u) :
    ∃ a : spec.Node (X.Map A), relNode a = u := by
  letI := X.trivialize.mapLinearOrder A
  exact exists_relNode ((realize_marks (X := X) (spec := spec) id u.2).mp
    (Formula.realize_inf.mp h).2)

theorem exists_relNode_of_step {u v : (relSpec X spec).Node (X.trivialize.Map A)}
    (h : letI := X.mapLinearOrder A; letI := X.trivialize.mapLinearOrder A;
      (relSpec X spec).Step u v) :
    ∃ b : spec.Node (X.Map A), relNode b = v := by
  letI := X.trivialize.mapLinearOrder A
  exact exists_relNode ((realize_marks (X := X) (spec := spec) Sum.inr
    (Sum.elim u.2 v.2)).mp (Formula.realize_inf.mp h).2)

/-- **Reachability is carried over**, in both directions: a walk of the carried
specification that starts at an included node stays included, step by step. -/
theorem reach_relSpec (a : spec.Node (X.Map A))
    {v : (relSpec X spec).Node (X.trivialize.Map A)} :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((relSpec X spec).Reach (relNode a) v →
      ∃ b : spec.Node (X.Map A), relNode b = v ∧ spec.Reach a b) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  intro h
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨b, rfl, hab⟩ := ih
    obtain ⟨b', rfl⟩ := exists_relNode_of_step hcd
    exact ⟨b', rfl, hab.tail ((step_relNode b b').mp hcd)⟩

theorem reach_relNode {a b : spec.Node (X.Map A)} :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    (spec.Reach a b → (relSpec X spec).Reach (relNode a) (relNode b)) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((step_relNode c d).mpr hcd)

/-- **The carried walk accepts exactly what the original one did.** -/
theorem accepts_relSpec :
    letI := X.mapLinearOrder A
    letI := X.trivialize.mapLinearOrder A
    ((relSpec X spec).Accepts (X.trivialize.Map A) ↔ spec.Accepts (X.Map A)) := by
  letI := X.mapLinearOrder A
  letI := X.trivialize.mapLinearOrder A
  constructor
  · rintro ⟨u, w, hu, hw, huw⟩
    obtain ⟨a, rfl⟩ := exists_relNode_of_isSrc hu
    obtain ⟨b, rfl, hab⟩ := reach_relSpec a huw
    exact ⟨a, b, (isSrc_relNode a).mp hu, (isTgt_relNode b).mp hw, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨relNode a, relNode b, (isSrc_relNode a).mpr ha, (isTgt_relNode b).mpr hb,
      reach_relNode hab⟩

end ExpExpansion

end DescriptiveComplexity
