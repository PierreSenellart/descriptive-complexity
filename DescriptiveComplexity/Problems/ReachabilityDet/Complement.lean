/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.ReachabilityDet
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.WalkBudget

/-!
# UNREACHd, and `L = coL`

Deterministic logarithmic space is closed under complement
(`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`), and UNREACHd – *non*-reachability
along forced arcs – is LOGSPACE-complete
(`DescriptiveComplexity.UNREACHd_LOGSPACE_complete`).

Unlike `NL = coNL` this needs no inductive counting, and unlike the clausal
fragments FO(DTC) has no built-in asymmetry between a problem and its
complement: everything reduces to *one* membership statement,
`DescriptiveComplexity.unreachd_dtcDefinable`. Given it, the complement of any
FO(DTC) definable problem is FO(DTC) definable, because a reduction complements
along with the problem (`DescriptiveComplexity.OrderedFOReduction.compl`) and REACHd is
LOGSPACE-hard.

## Complementing a deterministic walk

`REACHdᶜ` says that *no* marked source has a marked target ahead of it. Three
things make that a deterministic walk:

* **The walk is functional**, so from a given vertex there is only one thing to
  do: follow the forced arc (`DescriptiveComplexity.detNext`, the successor map, a dead
  end being its own successor). Reachability along forced arcs is exactly
  iteration of that map (`DescriptiveComplexity.reflTransGen_detEdge_iff_iterate`).
* **A step budget replaces cycle detection.** A walk that has not arrived after
  `|A| - 1` steps never will: taking a *minimal* number of steps to a vertex
  makes the visited vertices distinct, so it is bounded by the size of the
  universe (`DescriptiveComplexity.exists_iterate_lt_card`). The budget is carried as a
  third coordinate holding a vertex, counted through
  `DescriptiveComplexity.orank` – the universe has exactly as many elements as the walk
  may take steps.
* **The sources are scanned in order.** Acceptance quantifies the *start* node
  existentially, while the complement must quantify sources universally, so the
  walk loops over the candidates itself, in the order of the structure, and
  accepts only after exhausting them.

A node is therefore a mode – scanning or done – with a triple
`(s, x, c)`: the source candidate, the current position, the budget. The walk
gets stuck exactly when it finds a marked target ahead of a marked source, so
it reaches its accepting node exactly when there is nothing to find.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The forced-arc successor map -/

section Walk

variable {A : Type} [Language.stGraph.Structure A]

/-- The forced arcs are functional: that is the whole point of
`DescriptiveComplexity.DetEdge`. -/
theorem detEdge_unique {x y z : A} (hy : DetEdge x y) (hz : DetEdge x z) : y = z :=
  hz.2 y hy.1

/-- A vertex is *stuck* when no arc out of it is forced: either it has no
outgoing arc at all, or it has several. -/
def Stuck (x : A) : Prop := ¬∃ y, DetEdge x y

/-- The successor map of the deterministic walk: the endpoint of the forced arc
out of `x`, and `x` itself where the walk is stuck – the walk of the forced arcs
read as an iterated function, `DescriptiveComplexity.stepNext`. Making it total is
what lets reachability be read as iteration. -/
noncomputable def detNext (x : A) : A := stepNext DetEdge x

theorem detEdge_detNext {x : A} (h : ¬Stuck x) : DetEdge x (detNext x) :=
  step_stepNext (not_not.mp h)

theorem detNext_eq_self {x : A} (h : Stuck x) : detNext x = x := stepNext_eq_self h

theorem detNext_eq {x y : A} (h : DetEdge x y) : detNext x = y :=
  stepNext_eq (fun _ _ _ hv hw => detEdge_unique hv hw) h

/-- **Reachability along forced arcs is iteration of the successor map.** -/
theorem reflTransGen_detEdge_iff_iterate (s t : A) :
    Relation.ReflTransGen DetEdge s t ↔ ∃ n, detNext^[n] s = t :=
  reach_iff_iterate (R := DetEdge) (fun _ _ _ hv hw => detEdge_unique hv hw) s t

/-- **The step budget**: a vertex reachable along forced arcs is reachable in
fewer steps than the universe has elements – the machine-free
`DescriptiveComplexity.exists_iterate_lt_card`, read for the forced arcs. -/
theorem exists_iterate_detNext_lt_card [Finite A] {s t : A} (h : ∃ n, detNext^[n] s = t) :
    ∃ n, n < Nat.card A ∧ detNext^[n] s = t :=
  exists_iterate_lt_card (R := DetEdge) h

end Walk

/-! ### The scanning walk

A node is a mode – `false` while scanning, `true` once done – together with a
triple `(s, x, c)`: the source candidate being tested, the current position of
the walk, and the budget, itself a vertex, counted by its rank in the order. -/

namespace UnreachD

section Formulas

variable {γ : Type}

/-- `u` is a marked source, as a formula. -/
noncomputable def srcF (u : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  Relations.formula₁ sgSourceO (Term.var u)

/-- `u` is a marked target, as a formula. -/
noncomputable def tgtF (u : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  Relations.formula₁ sgTargetO (Term.var u)

/-- There is an arc from `u` to `v`, as a formula. -/
noncomputable def edgeF (u v : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  Relations.formula₂ sgEdgeO (Term.var u) (Term.var v)

/-- The arc from `u` to `v` is forced, as a formula: it is an arc, and it is
the only one out of `u`. -/
noncomputable def detEdgeF (u v : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  fo%[u, v] edgeF⟨u, v⟩ ∧ ∀ w, edgeF⟨u, w⟩ → w ≐ v

/-- No arc out of `u` is forced, as a formula. -/
noncomputable def stuckF (u : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  fo%[u] ∀ w, ¬ detEdgeF⟨u, w⟩

/-- Equality of two variables, as a formula. -/
def eqF (u v : γ) : (Language.stGraph.sum Language.order).Formula γ :=
  Term.equal (Term.var u) (Term.var v)

end Formulas

section Realize

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A] {γ : Type} {v : γ → A}

@[simp]
theorem realize_srcF (u : γ) : (srcF u).Realize v ↔ SGSource (v u) := by
  rw [srcF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_tgtF (u : γ) : (tgtF u).Realize v ↔ SGTarget (v u) := by
  rw [tgtF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_edgeF (u w : γ) : (edgeF u w).Realize v ↔ SGEdge (v u) (v w) := by
  rw [edgeF, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_eqF (u w : γ) : (eqF u w).Realize v ↔ v u = v w := by
  rw [eqF, Formula.realize_equal, Term.realize_var, Term.realize_var]

@[simp]
theorem realize_detEdgeF (u w : γ) : (detEdgeF u w).Realize v ↔ DetEdge (v u) (v w) := by
  rw [detEdgeF, Formula.realize_inf, realize_edgeF, Formula.realize_iAlls, DetEdge]
  refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h i => ?_⟩
  · have hi := h fun _ => z
    rw [Formula.realize_imp, realize_edgeF, Formula.realize_equal, Term.realize_var,
      Term.realize_var] at hi
    exact hi hz
  · rw [Formula.realize_imp, realize_edgeF, Formula.realize_equal, Term.realize_var,
      Term.realize_var]
    exact h (i 0)

@[simp]
theorem realize_stuckF (u : γ) : (stuckF u).Realize v ↔ Stuck (v u) := by
  rw [stuckF, Formula.realize_iAlls, Stuck]
  constructor
  · rintro h ⟨y, hy⟩
    have hi := h fun _ => y
    rw [Formula.realize_not, realize_detEdgeF] at hi
    exact hi hy
  · intro h i
    rw [Formula.realize_not, realize_detEdgeF]
    exact fun hd => h ⟨i 0, hd⟩

end Realize

/-! ### The specification -/

section Spec

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A]

/-- The current source candidate. -/
abbrev vS : Fin 3 ⊕ Fin 3 := Sum.inl 0

/-- The current position of the walk. -/
abbrev vX : Fin 3 ⊕ Fin 3 := Sum.inl 1

/-- The current budget. -/
abbrev vC : Fin 3 ⊕ Fin 3 := Sum.inl 2

/-- The next source candidate. -/
abbrev vS' : Fin 3 ⊕ Fin 3 := Sum.inr 0

/-- The next position. -/
abbrev vX' : Fin 3 ⊕ Fin 3 := Sum.inr 1

/-- The next budget. -/
abbrev vC' : Fin 3 ⊕ Fin 3 := Sum.inr 2

/-- The transition of the scanning mode to itself: either follow the forced arc
and spend one unit of budget, or – when the walk is stuck or the budget is
exhausted – move on to the next source candidate. Both are guarded by the
absence of a marked target ahead of a marked source, which is where the walk
stops for good. -/
noncomputable def stepFF : (Language.stGraph.sum Language.order).Formula (Fin 3 ⊕ Fin 3) :=
  ∼(srcF vS ⊓ tgtF vX) ⊓
    ((eqF vS' vS ⊓ detEdgeF vX vX' ⊓ succF vC vC') ⊔
      ((stuckF vX ⊔ maxF vC) ⊓ succF vS vS' ⊓ eqF vX' vS' ⊓ minF vC'))

/-- The transition to the accepting mode: the last candidate has been scanned
through. -/
noncomputable def stepFT : (Language.stGraph.sum Language.order).Formula (Fin 3 ⊕ Fin 3) :=
  ∼(srcF vS ⊓ tgtF vX) ⊓ (stuckF vX ⊔ maxF vC) ⊓ maxF vS ⊓
    (minF vS' ⊓ minF vX' ⊓ minF vC')

/-- The starting nodes: the least candidate, the walk at that candidate, the
full budget. -/
noncomputable def srcFml : (Language.stGraph.sum Language.order).Formula (Fin 3) :=
  minF 0 ⊓ eqF 1 0 ⊓ minF 2

/-- **The specification whose deterministic walk scans for a forced path from a
marked source to a marked target**, accepting when it finds none. -/
noncomputable abbrev unreachdSpec : TCSpec Language.stGraph where
  Mode := Bool
  k := 3
  step m n :=
    match m, n with
    | false, false => stepFF
    | false, true => stepFT
    | true, _ => ⊥
  src m :=
    match m with
    | false => srcFml
    | true => ⊥
  tgt m :=
    match m with
    | false => ⊥
    | true => ⊤

/-! ### Semantics of the walk -/

/-- `a` is a least element of the order. -/
def IsMinA (a : A) : Prop := ∀ b : A, a ≤ b

/-- `a` is a greatest element of the order. -/
def IsMaxA (a : A) : Prop := ∀ b : A, b ≤ a

/-- `z` covers `w`: the budget goes from `w` to `z` in one step. -/
def IsSuccA (w z : A) : Prop := w < z ∧ ∀ a : A, ¬(w < a ∧ a < z)

/-- One step of the scanning walk, in Lean: follow the forced arc while there
is budget, otherwise move to the next candidate, or finish. -/
def UStep (a b : Bool × (Fin 3 → A)) : Prop :=
  a.1 = false ∧ ¬(SGSource (a.2 0) ∧ SGTarget (a.2 1)) ∧
    (match b.1 with
      | true =>
        (Stuck (a.2 1) ∨ IsMaxA (a.2 2)) ∧ IsMaxA (a.2 0) ∧
          IsMinA (b.2 0) ∧ IsMinA (b.2 1) ∧ IsMinA (b.2 2)
      | false =>
        (b.2 0 = a.2 0 ∧ DetEdge (a.2 1) (b.2 1) ∧ IsSuccA (a.2 2) (b.2 2)) ∨
          ((Stuck (a.2 1) ∨ IsMaxA (a.2 2)) ∧ IsSuccA (a.2 0) (b.2 0) ∧
            b.2 1 = b.2 0 ∧ IsMinA (b.2 2)))

theorem realize_stepFF (x y : Fin 3 → A) :
    stepFF.Realize (Sum.elim x y) ↔
      ¬(SGSource (x 0) ∧ SGTarget (x 1)) ∧
        ((y 0 = x 0 ∧ DetEdge (x 1) (y 1) ∧ IsSuccA (x 2) (y 2)) ∨
          ((Stuck (x 1) ∨ IsMaxA (x 2)) ∧ IsSuccA (x 0) (y 0) ∧ y 1 = y 0 ∧ IsMinA (y 2))) := by
  rw [stepFF]
  simp only [Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_srcF,
    realize_tgtF, realize_eqF, realize_detEdgeF, realize_stuckF, realize_succF, realize_maxF,
    realize_minF, Sum.elim_inl, Sum.elim_inr, IsSuccA, IsMinA, IsMaxA]
  tauto

theorem realize_stepFT (x y : Fin 3 → A) :
    stepFT.Realize (Sum.elim x y) ↔
      ¬(SGSource (x 0) ∧ SGTarget (x 1)) ∧ ((Stuck (x 1) ∨ IsMaxA (x 2)) ∧ IsMaxA (x 0) ∧
        IsMinA (y 0) ∧ IsMinA (y 1) ∧ IsMinA (y 2)) := by
  rw [stepFT]
  simp only [Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_srcF,
    realize_tgtF, realize_stuckF, realize_maxF, realize_minF, Sum.elim_inl, Sum.elim_inr,
    IsMinA, IsMaxA]
  tauto

/-- **The walk of the specification is the scanning walk.** -/
theorem step_unreachdSpec (a b : unreachdSpec.Node A) :
    unreachdSpec.Step a b ↔ UStep a b := by
  obtain ⟨m, x⟩ := a
  obtain ⟨n, y⟩ := b
  cases m with
  | true =>
    refine iff_of_false ?_ ?_
    · cases n <;> exact fun h => h
    · rintro ⟨h, -⟩
      exact Bool.noConfusion h
  | false =>
    cases n with
    | false => exact (realize_stepFF x y).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
    | true => exact (realize_stepFT x y).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

/-- The starting nodes of the walk. -/
theorem isSrc_unreachdSpec (a : unreachdSpec.Node A) :
    unreachdSpec.IsSrc a ↔ a.1 = false ∧ IsMinA (a.2 0) ∧ a.2 1 = a.2 0 ∧ IsMinA (a.2 2) := by
  obtain ⟨m, x⟩ := a
  cases m with
  | true => exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h.1)
  | false =>
    refine Iff.trans ?_ ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
    change (srcFml.Realize x) ↔ _
    rw [srcFml]
    simp only [Formula.realize_inf, realize_minF, realize_eqF, IsMinA]
    tauto

/-- The accepting nodes of the walk: those of the finished mode. -/
theorem isTgt_unreachdSpec (a : unreachdSpec.Node A) : unreachdSpec.IsTgt a ↔ a.1 = true := by
  obtain ⟨m, x⟩ := a
  cases m with
  | true => exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  | false => exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h)

end Spec

/-! ### Order arithmetic for the budget -/

section OrderFacts

variable {A : Type} [LinearOrder A]

theorem isMinA_unique {a b : A} (ha : IsMinA a) (hb : IsMinA b) : a = b :=
  le_antisymm (ha b) (hb a)

theorem isSuccA_unique {c b b' : A} (h : IsSuccA c b) (h' : IsSuccA c b') : b = b' := by
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · exact absurd ⟨h.1, hlt⟩ (h'.2 b)
  · exact heq
  · exact absurd ⟨h'.1, hgt⟩ (h.2 b')

theorem not_isSuccA_of_isMaxA {c b : A} (hc : IsMaxA c) (h : IsSuccA c b) : False :=
  absurd (hc b) (not_le.mpr h.1)

theorem lt_or_eq_of_lt_isSuccA {w z a : A} (h : IsSuccA w z) (ha : a < z) : a < w ∨ a = w := by
  rcases lt_trichotomy a w with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr heq
  · exact absurd ⟨hgt, ha⟩ (h.2 a)

variable [Finite A]

theorem exists_isSuccA_of_not_isMaxA {c : A} (h : ¬IsMaxA c) : ∃ c', IsSuccA c c' := by
  classical
  have := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun a : A => c < a).Nonempty := by
    rw [IsMaxA] at h
    push Not at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  refine ⟨(Finset.univ.filter fun a : A => c < a).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · rintro a ⟨hca, hac⟩
    exact absurd (Finset.min'_le _ a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hca⟩))
      (not_le.mpr hac)

omit [Finite A] in
theorem orank_of_isMinA {a : A} (h : IsMinA a) : orank a = 0 := orank_eq_zero h

theorem orank_of_isSuccA {w z : A} (h : IsSuccA w z) : orank z = orank w + 1 :=
  orank_covBy ⟨h.1, fun a hwa haz => h.2 a ⟨hwa, haz⟩⟩

theorem orank_of_isMaxA {z : A} (h : IsMaxA z) : orank z = Nat.card A - 1 := orank_isTop h

end OrderFacts

/-! ### Determinism of the scanning walk -/

section Functional

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A] [Finite A]

omit [Language.stGraph.Structure A] [LinearOrder A] [Finite A] in
private theorem node_ext {b c : Bool × (Fin 3 → A)} (h0 : b.1 = c.1) (h1 : b.2 0 = c.2 0)
    (h2 : b.2 1 = c.2 1) (h3 : b.2 2 = c.2 2) : b = c := by
  refine Prod.ext_iff.mpr ⟨h0, funext fun i => ?_⟩
  fin_cases i
  exacts [h1, h2, h3]

omit [Finite A] in
/-- A walking step and an end-of-loop step exclude each other. -/
private theorem not_walk_of_end {a b : Bool × (Fin 3 → A)}
    (hend : Stuck (a.2 1) ∨ IsMaxA (a.2 2))
    (hwalk : DetEdge (a.2 1) (b.2 1) ∧ IsSuccA (a.2 2) (b.2 2)) : False := by
  rcases hend with hs | hm
  · exact hs ⟨b.2 1, hwalk.1⟩
  · exact not_isSuccA_of_isMaxA hm hwalk.2

omit [Finite A] in
/-- **The scanning walk is deterministic.** -/
theorem functional_unreachdSpec : unreachdSpec.Functional A := by
  intro a b c hb hc
  rw [step_unreachdSpec] at hb hc
  obtain ⟨-, -, hb'⟩ := hb
  obtain ⟨-, -, hc'⟩ := hc
  cases hbm : b.1 <;> cases hcm : c.1 <;> rw [hbm] at hb' <;> rw [hcm] at hc'
  · -- both scanning
    rcases hb' with ⟨hb0, hb1, hb2⟩ | ⟨hbe, hb0, hb1, hb2⟩ <;>
      rcases hc' with ⟨hc0, hc1, hc2⟩ | ⟨hce, hc0, hc1, hc2⟩
    · exact node_ext (hbm.trans hcm.symm) (hb0.trans hc0.symm)
        (detEdge_unique hb1 hc1) (isSuccA_unique hb2 hc2)
    · exact absurd ⟨hb1, hb2⟩ (not_walk_of_end hce)
    · exact absurd ⟨hc1, hc2⟩ (not_walk_of_end hbe)
    · have h00 : b.2 0 = c.2 0 := isSuccA_unique hb0 hc0
      exact node_ext (hbm.trans hcm.symm) h00 (hb1.trans (h00.trans hc1.symm))
        (isMinA_unique hb2 hc2)
  · -- scanning against finishing
    obtain ⟨hce, hcmax, -⟩ := hc'
    rcases hb' with ⟨-, hb1, hb2⟩ | ⟨-, hb0, -, -⟩
    · exact absurd ⟨hb1, hb2⟩ (not_walk_of_end hce)
    · exact absurd hb0 fun h => not_isSuccA_of_isMaxA hcmax h
  · obtain ⟨hbe, hbmax, -⟩ := hb'
    rcases hc' with ⟨-, hc1, hc2⟩ | ⟨-, hc0, -, -⟩
    · exact absurd ⟨hc1, hc2⟩ (not_walk_of_end hbe)
    · exact absurd hc0 fun h => not_isSuccA_of_isMaxA hbmax h
  · -- both finishing
    obtain ⟨-, -, hb0, hb1, hb2⟩ := hb'
    obtain ⟨-, -, hc0, hc1, hc2⟩ := hc'
    exact node_ext (hbm.trans hcm.symm) (isMinA_unique hb0 hc0) (isMinA_unique hb1 hc1)
      (isMinA_unique hb2 hc2)

end Functional

/-! ### Correctness of the scan -/

section Correctness

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- A marked source with a marked target ahead of it: what the scan looks for,
and what its acceptance denies. -/
def Bad (s : A) : Prop :=
  SGSource s ∧ ∃ t : A, SGTarget t ∧ Relation.ReflTransGen DetEdge s t

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem detReachable_iff_exists_bad : DetReachable A ↔ ∃ s : A, Bad s := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    exact ⟨s, hs, t, ht, hp⟩
  · rintro ⟨s, hs, t, ht, hp⟩
    exact ⟨s, t, hs, ht, hp⟩

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem iterate_of_stuck {x : A} (h : Stuck x) (n : ℕ) : detNext^[n] x = x := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, detNext_eq_self h]

/-- **The invariant carried along the scan**: every candidate already passed is
harmless, and if the current one is not, its target is still ahead of the walk
and within the remaining budget. -/
def Inv (a : Bool × (Fin 3 → A)) : Prop :=
  (∀ s' : A, s' < a.2 0 → ¬Bad s') ∧
    (a.1 = false → Bad (a.2 0) →
      ∃ t : A, ∃ n : ℕ, SGTarget t ∧ n + orank (a.2 2) < Nat.card A ∧
        detNext^[n] (a.2 1) = t) ∧
    (a.1 = true → ∀ s : A, ¬Bad s)

/-- At the end of an inner loop – the walk stuck, or the budget spent – the
current candidate is harmless: its target would have to be where the walk
already stands, and the walk has not stopped there. -/
theorem not_bad_of_end {a : Bool × (Fin 3 → A)}
    (hguard : ¬(SGSource (a.2 0) ∧ SGTarget (a.2 1)))
    (hend : Stuck (a.2 1) ∨ IsMaxA (a.2 2))
    (hinv : Bad (a.2 0) → ∃ t : A, ∃ n : ℕ, SGTarget t ∧
      n + orank (a.2 2) < Nat.card A ∧ detNext^[n] (a.2 1) = t) :
    ¬Bad (a.2 0) := by
  intro hb
  obtain ⟨t, n, ht, hn, hit⟩ := hinv hb
  have hzero : detNext^[n] (a.2 1) = a.2 1 := by
    rcases hend with hs | hm
    · exact iterate_of_stuck hs n
    · have hrank : orank (a.2 2) = Nat.card A - 1 := orank_of_isMaxA hm
      have hpos : 0 < Nat.card A := Nat.card_pos
      have hn0 : n = 0 := by omega
      rw [hn0]
      rfl
  have hta : t = a.2 1 := by rw [← hit, hzero]
  exact hguard ⟨hb.1, hta ▸ ht⟩

/-- **The invariant is preserved by every step of the scan.** -/
theorem inv_step {a b : Bool × (Fin 3 → A)} (h : UStep a b) (hinv : Inv a) : Inv b := by
  obtain ⟨ha0, hguard, hcases⟩ := h
  obtain ⟨hinv1, hinv2, -⟩ := hinv
  have hinv2' := hinv2 ha0
  cases hbm : b.1 with
  | true =>
    rw [hbm] at hcases
    obtain ⟨hend, hmax, hmin0, -, -⟩ := hcases
    have hnb := not_bad_of_end hguard hend hinv2'
    refine ⟨fun s' hs' => absurd (hmin0 s') (not_le.mpr hs'), ?_, ?_⟩
    · intro hf
      exact Bool.noConfusion (hbm.symm.trans hf)
    · rintro - s
      rcases lt_or_eq_of_le (hmax s) with hlt | heq
      · exact hinv1 s hlt
      · exact heq ▸ hnb
  | false =>
    rw [hbm] at hcases
    rcases hcases with ⟨hb0, hedge, hsucc⟩ | ⟨hend, hsucc0, hb1, hmin2⟩
    · refine ⟨?_, ?_, fun hf => Bool.noConfusion (hbm.symm.trans hf)⟩
      · rw [hb0]
        exact hinv1
      · rintro - hbad
        obtain ⟨t, n, ht, hn, hit⟩ := hinv2' (hb0 ▸ hbad)
        have hne : n ≠ 0 := by
          rintro rfl
          have h0 : a.2 1 = t := hit
          exact hguard ⟨(hb0 ▸ hbad : Bad (a.2 0)).1, h0 ▸ ht⟩
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
        refine ⟨t, m, ht, ?_, ?_⟩
        · rw [orank_of_isSuccA hsucc]
          omega
        · rw [← hit, Function.iterate_succ_apply, detNext_eq hedge]
    · refine ⟨?_, ?_, fun hf => Bool.noConfusion (hbm.symm.trans hf)⟩
      · intro s' hs'
        rcases lt_or_eq_of_lt_isSuccA hsucc0 hs' with hlt | heq
        · exact hinv1 s' hlt
        · exact heq ▸ not_bad_of_end hguard hend hinv2'
      · rintro - hbad
        obtain ⟨-, t, ht, hp⟩ := hbad
        obtain ⟨n, hn, hit⟩ :=
          exists_iterate_detNext_lt_card ((reflTransGen_detEdge_iff_iterate _ _).mp hp)
        refine ⟨t, n, ht, ?_, ?_⟩
        · rw [orank_of_isMinA hmin2]
          omega
        · rw [hb1]
          exact hit

theorem inv_reach {a b : unreachdSpec.Node A} (h : unreachdSpec.Reach a b) (hinv : Inv a) :
    Inv b := by
  induction h with
  | refl => exact hinv
  | @tail c d _ hcd ih => exact inv_step ((step_unreachdSpec c d).mp hcd) ih

omit [Nonempty A] in
/-- The starting node satisfies the invariant: nothing has been scanned, and the
whole universe is still available as budget. -/
theorem inv_of_isSrc {a : unreachdSpec.Node A} (h : unreachdSpec.IsSrc a) : Inv a := by
  rw [isSrc_unreachdSpec] at h
  obtain ⟨h0, hmin0, h1, hmin2⟩ := h
  refine ⟨fun s' hs' => absurd (hmin0 s') (not_le.mpr hs'), ?_,
    fun hf => Bool.noConfusion (h0.symm.trans hf)⟩
  rintro - hbad
  obtain ⟨-, t, ht, hp⟩ := hbad
  obtain ⟨n, hn, hit⟩ :=
    exists_iterate_detNext_lt_card ((reflTransGen_detEdge_iff_iterate _ _).mp hp)
  refine ⟨t, n, ht, ?_, ?_⟩
  · rw [orank_of_isMinA hmin2]
    omega
  · rw [h1]
    exact hit

/-- **Soundness**: if the scan finishes, there was nothing to find. -/
theorem not_detReachable_of_accepts (h : unreachdSpec.Accepts A) : ¬DetReachable A := by
  obtain ⟨u, v, hu, hv, huv⟩ := h
  have hinvv := inv_reach huv (inv_of_isSrc hu)
  rw [detReachable_iff_exists_bad]
  rintro ⟨s, hs⟩
  exact hinvv.2.2 ((isTgt_unreachdSpec v).mp hv) s hs

/-! #### Completeness of the scan

Nothing to find means nothing stops the walk, so it runs the inner loop to its
end for every candidate and finishes. -/

omit [Nonempty A] in
/-- The inner loop: from any position of the walk on the candidate `s`, with any
budget, the node `z` that ends the loop is reached. -/
theorem reach_of_inner (hnb : ∀ s : A, ¬Bad s) (s : A) (z : Bool × (Fin 3 → A))
    (hz : ∀ x c : A, Relation.ReflTransGen DetEdge s x → (Stuck x ∨ IsMaxA c) →
      UStep (false, ![s, x, c]) z) :
    ∀ (m : ℕ) (c x : A), Nat.card A - orank c ≤ m → Relation.ReflTransGen DetEdge s x →
      unreachdSpec.Reach (false, ![s, x, c]) z := by
  intro m
  induction m with
  | zero =>
    rintro c x hle -
    exact absurd (orank_lt_card c) (by omega)
  | succ m ih =>
    intro c x hle hsx
    have hguard : ¬(SGSource s ∧ SGTarget x) := by
      rintro ⟨h1, h2⟩
      exact hnb s ⟨h1, x, h2, hsx⟩
    by_cases hend : Stuck x ∨ IsMaxA c
    · exact Relation.ReflTransGen.single ((step_unreachdSpec _ _).mpr (hz x c hsx hend))
    · push Not at hend
      obtain ⟨hns, hnm⟩ := hend
      obtain ⟨c', hc'⟩ := exists_isSuccA_of_not_isMaxA hnm
      have hedge : DetEdge x (detNext x) := detEdge_detNext hns
      have hstep : UStep ((false, ![s, x, c]) : Bool × (Fin 3 → A))
          (false, ![s, detNext x, c']) := ⟨rfl, hguard, Or.inl ⟨rfl, hedge, hc'⟩⟩
      refine Relation.ReflTransGen.head ((step_unreachdSpec _ _).mpr hstep) ?_
      refine ih c' (detNext x) ?_ (hsx.tail hedge)
      rw [orank_of_isSuccA hc']
      omega

omit [Nonempty A] in
/-- The outer loop: every candidate is reached, in the order of the
structure. -/
theorem reach_candidate (hnb : ∀ s : A, ¬Bad s) {a₀ : A} (h₀ : IsMinA a₀) (s : A) :
    unreachdSpec.Reach (false, ![a₀, a₀, a₀]) (false, ![s, s, a₀]) := by
  induction s using order_induction with
  | hmin z hz =>
    rw [isMinA_unique hz h₀]
  | hstep w z hwz hcov ih =>
    refine ih.trans ?_
    refine reach_of_inner hnb w (false, ![z, z, a₀]) ?_ (Nat.card A) a₀ w (by omega)
      Relation.ReflTransGen.refl
    intro x c hx hend
    refine ⟨rfl, ?_, Or.inr ⟨hend, ⟨hwz, hcov⟩, rfl, h₀⟩⟩
    rintro ⟨h1, h2⟩
    exact hnb w ⟨h1, x, h2, hx⟩

/-- **Completeness**: if there is nothing to find, the scan finishes. -/
theorem accepts_of_not_detReachable (h : ¬DetReachable A) : unreachdSpec.Accepts A := by
  have hnb : ∀ s : A, ¬Bad s := fun s hs => h (detReachable_iff_exists_bad.mpr ⟨s, hs⟩)
  obtain ⟨a₀, h₀⟩ : ∃ a₀ : A, IsMinA a₀ := Finite.exists_min (id : A → A)
  obtain ⟨aM, hM⟩ : ∃ z : A, IsMaxA z := Finite.exists_max (id : A → A)
  refine ⟨(false, ![a₀, a₀, a₀]), (true, ![a₀, a₀, a₀]),
    (isSrc_unreachdSpec _).mpr ⟨rfl, h₀, rfl, h₀⟩, (isTgt_unreachdSpec _).mpr rfl, ?_⟩
  refine (reach_candidate hnb h₀ aM).trans ?_
  refine reach_of_inner hnb aM (true, ![a₀, a₀, a₀]) ?_ (Nat.card A) a₀ aM (by omega)
    Relation.ReflTransGen.refl
  intro x c hx hend
  refine ⟨rfl, ?_, hend, hM, h₀, h₀, h₀⟩
  rintro ⟨h1, h2⟩
  exact hnb aM ⟨h1, x, h2, hx⟩

/-- **The scan decides non-reachability along forced arcs.** -/
theorem accepts_unreachdSpec_iff : unreachdSpec.Accepts A ↔ ¬DetReachable A :=
  ⟨not_detReachable_of_accepts, accepts_of_not_detReachable⟩

end Correctness

end UnreachD

/-! ### UNREACHd, and the closure of LOGSPACE under complement -/

/-- **The complement of REACHd is FO(DTC) definable**: the scan is
deterministic (`DescriptiveComplexity.UnreachD.functional_unreachdSpec`), so its
determinization is itself, and it accepts exactly the marked graphs in which no
marked target lies ahead of a marked source. -/
theorem unreachd_dtcDefinable : DTCDefinable REACHdᶜ := by
  refine ⟨UnreachD.unreachdSpec, ?_⟩
  intro A _ _ _ _
  rw [TCSpec.det_accepts_iff _ UnreachD.functional_unreachdSpec,
    UnreachD.accepts_unreachdSpec_iff]
  exact Iff.rfl

/-- **FO(DTC) definability is closed under complement.** The complement of `P`
reduces to the complement of REACHd – a reduction complements along with its two
problems – and that complement is FO(DTC) definable. -/
theorem dtcDefinable_compl {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : DTCDefinable P) : DTCDefinable Pᶜ := by
  obtain ⟨f⟩ := reachd_hard_of_dtcDefinable P h
  exact unreachd_dtcDefinable.of_orderedReduction f.compl

/-- Membership in LOGSPACE is closed under complement. -/
theorem mem_LOGSPACE_compl_iff {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    Pᶜ ∈ LOGSPACE ↔ P ∈ LOGSPACE := by
  refine ⟨fun h => ?_, fun h => dtcDefinable_compl h⟩
  have h' := dtcDefinable_compl h
  rwa [DecisionProblem.compl_compl] at h'

/-- coLOGSPACE, the complement class of LOGSPACE. That it *is* LOGSPACE is
`DescriptiveComplexity.LOGSPACE_eq_coLOGSPACE`. -/
noncomputable abbrev coLOGSPACE : ComplexityClass := LOGSPACE.compl

/-- **`L = coL`**: deterministic logarithmic space is closed under complement.
Unlike `NL = coNL` (`DescriptiveComplexity.NL_eq_coNL`, Immerman–Szelepcsényi) this
needs no inductive counting: a deterministic walk has only one thing to do at
each node, so *not* arriving is witnessed by walking until the budget runs
out. -/
theorem LOGSPACE_eq_coLOGSPACE : LOGSPACE = coLOGSPACE := by
  refine ComplexityClass.ext (fun P => (mem_LOGSPACE_compl_iff P).symm) fun P => ?_
  constructor
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((mem_LOGSPACE_compl_iff Q).mp hQ)
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((mem_LOGSPACE_compl_iff Q).mpr hQ)

/-- **UNREACHd**, the complement of REACHd: no marked target is reachable from a
marked source along forced arcs. -/
def UNREACHd : DecisionProblem Language.stGraph := REACHdᶜ

/-- UNREACHd is in LOGSPACE, by the scan. -/
theorem unreachd_mem_LOGSPACE : UNREACHd ∈ LOGSPACE := unreachd_dtcDefinable

/-- **UNREACHd is LOGSPACE-hard**, by complementing the discharge: the
complement of a problem of the class is again in the class, it reduces to
REACHd, and the very same interpretation reduces the problem itself to
UNREACHd. -/
theorem unreachd_LOGSPACE_hard : LOGSPACE.Hard UNREACHd :=
  (hard_LOGSPACE_iff UNREACHd).mpr fun Q hQ => by
    obtain ⟨f⟩ := reachd_hard_of_dtcDefinable Qᶜ (dtcDefinable_compl hQ)
    have h := f.compl
    rw [DecisionProblem.compl_compl] at h
    exact ⟨h.toRel⟩

/-- **UNREACHd is LOGSPACE-complete.** Both halves come from the same side here,
unlike the REACH/UNREACH pair one level up: an operator-based logic defines a
problem and its complement alike, so no analogue of Immerman–Szelepcsényi is
needed to complete the picture. -/
theorem UNREACHd_LOGSPACE_complete : LOGSPACE.Complete UNREACHd :=
  ⟨unreachd_mem_LOGSPACE, unreachd_LOGSPACE_hard⟩

end DescriptiveComplexity
