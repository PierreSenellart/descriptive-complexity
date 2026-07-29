/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Program

/-!
# Runs of a deterministic machine, unbounded in time

The tool that makes the *converse* half of a space-bounded hardness proof free.

A reduction into `DescriptiveComplexity.DTMAcceptSpace` has to show both that a
yes-instance is accepted and that a no-instance is **not**. The second half is
usually a second induction – an invariant strong enough to rule out every run.
For a deterministic machine it is not needed: the configurations reachable from
one starting point are *linearly ordered* by reachability
(`DescriptiveComplexity.TMData.reach_total`, from Mathlib's
`Relation.ReflTransGen.total_of_right_unique` and
`DescriptiveComplexity.TMData.step_functional`), so it is enough to exhibit *one*
run, of the machine's own choosing, that ends badly.

Concretely, `DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` says: if
the initial configuration reaches a configuration that is stuck and not
accepting, and if accepting configurations are themselves stuck, then the
machine does not accept. Both side conditions are properties of the transition
table, so a reduction discharges them by inspection of its own program.

Nothing here is about space: the statements hold for any `TMData` whose runs
are read with `Relation.ReflTransGen`.
-/

namespace DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : TMData A}

omit [Finite A] in
/-- **A budgeted run is a run**: the space-bounded reading of acceptance forgets
the step count, so every lemma stated with `DescriptiveComplexity.TMData.StepsIn` –
the sweep primitives of `DescriptiveComplexity.Problems.Machine.Program`, in
particular – feeds straight into it. -/
theorem reflTransGen_of_stepsIn : ∀ {n : ℕ} {c d : Config A}, M.StepsIn n c d →
    Relation.ReflTransGen M.Step c d := by
  intro n
  induction n with
  | zero => intro c d h; exact (show c = d from h) ▸ Relation.ReflTransGen.refl
  | succ n ih =>
    rintro c d ⟨e, he, hrest⟩
    exact Relation.ReflTransGen.head he (ih hrest)

omit [Finite A] in
/-- **A deterministic machine has one run**: two configurations reachable from
the same starting point are reachable from one another. -/
theorem reach_total (hlin : IsLinOrd M.Le) (hdet : M.Deterministic) {c x y : Config A}
    (hx : Relation.ReflTransGen M.Step c x) (hy : Relation.ReflTransGen M.Step c y) :
    Relation.ReflTransGen M.Step x y ∨ Relation.ReflTransGen M.Step y x :=
  Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ h₁ h₂ => step_functional hlin hdet h₁ h₂) hx hy

omit [Finite A] in
/-- Nothing is reachable from a stuck configuration but itself. -/
theorem eq_of_reach_stuck {c d : Config A} (hstuck : ∀ e, ¬M.Step c e)
    (h : Relation.ReflTransGen M.Step c d) : c = d := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨e, he, -⟩
  · exact heq
  · exact absurd he (hstuck e)

omit [Finite A] in
/-- **A deterministic machine that runs into a dead end does not accept.**

The run exhibited by `hreach` is *the* run, so an accepting configuration would
have to lie on it – before the dead end, and then it would have to be the dead
end itself since an accepting configuration is stuck, or after it, and then it
would be the dead end because nothing follows a dead end. Either way the dead
end is accepting, which it is not. -/
theorem not_acceptsSpace_of_reaches_dead (hwf : M.WellFormed) (hdet : M.Deterministic)
    {c₀ d : Config A} (hinit : M.IsInit c₀) (hreach : Relation.ReflTransGen M.Step c₀ d)
    (hdead : ∀ e, ¬M.Step d e) (hnacc : ¬M.Acc d.state)
    (hsink : ∀ e : Config A, M.Acc e.state → ∀ e', ¬M.Step e e') :
    ¬M.AcceptsSpace := by
  rintro ⟨c₀', c, hinit', hr, hacc⟩
  obtain rfl : c₀' = c₀ := isInit_unique hwf hdet.1 hinit' hinit
  rcases reach_total hwf.1 hdet hreach hr with h | h
  · exact hnacc ((eq_of_reach_stuck hdead h) ▸ hacc)
  · exact hnacc ((eq_of_reach_stuck (hsink c hacc) h) ▸ hacc)

omit [Finite A] in
/-- **The positive half**, for symmetry: a run from the initial configuration
to an accepting one is exactly what acceptance in bounded space asks for. -/
theorem acceptsSpace_of_reaches_acc {c₀ d : Config A} (hinit : M.IsInit c₀)
    (hreach : Relation.ReflTransGen M.Step c₀ d) (hacc : M.Acc d.state) :
    M.AcceptsSpace :=
  ⟨c₀, d, hinit, hreach, hacc⟩

end TMData

end DescriptiveComplexity
