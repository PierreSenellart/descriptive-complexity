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

The hypothesis is not determinism but
`DescriptiveComplexity.TMData.UniqueFrom`: every configuration reachable from a
given one has at most one successor. That is what a program which **guesses in
one phase** and is deterministic after it has, and it is all the read-off lemmas
need – a reduction into a nondeterministic problem has to read its certificate
off an arbitrary accepting run, and this is what makes that a case analysis on
the guess rather than a second induction. Global determinism is the special case
(`DescriptiveComplexity.TMData.uniqueFrom_of_deterministic`).

Nothing here is about space: the statements hold for any `TMData` whose runs
are read with `Relation.ReflTransGen`.
-/

namespace DescriptiveComplexity

namespace TMData

variable {A : Type} [Finite A] {M : TMData A}

variable (M) in
/-- **Determinism where it is used**: every configuration reachable from `c` has
at most one successor.

This is weaker than `DescriptiveComplexity.TMData.Deterministic` in exactly the
way a *guessing* program needs. A reduction into a nondeterministic problem has
to read its certificate off an arbitrary accepting run, and the way to survive
that is to guess in one phase and be deterministic everywhere after it: the
machine is then not deterministic at all, but it is unique from the
configuration the guess ends at, and every read-off below asks for no more. -/
def UniqueFrom (c : Config A) : Prop :=
  ∀ x y z : Config A, Relation.ReflTransGen M.Step c x → M.Step x y → M.Step x z → y = z

omit [Finite A] in
/-- A deterministic machine is unique from anywhere. -/
theorem uniqueFrom_of_deterministic (hlin : IsLinOrd M.Le) (hdet : M.Deterministic)
    (c : Config A) : M.UniqueFrom c :=
  fun _ _ _ _ h₁ h₂ => step_functional hlin hdet h₁ h₂

omit [Finite A] in
/-- **Uniqueness from an invariant**: a property the step relation preserves, and
under which the step is functional, makes the machine unique from any
configuration having it.

This is how a program that guesses in one phase pays for the rest of its run.
The property is "the phase is one the guess is not reachable from"; the step
preserves it because the program's phases only go forward, and at those phases
its rules separate. Global determinism is the case where the property is
`True`. -/
theorem uniqueFrom_of_invariant {Inv : Config A → Prop}
    (hclosed : ∀ x y : Config A, Inv x → M.Step x y → Inv y)
    (hfun : ∀ x y z : Config A, Inv x → M.Step x y → M.Step x z → y = z)
    {c : Config A} (hc : Inv c) : M.UniqueFrom c := by
  intro x y z hcx
  have hx : Inv x := by
    induction hcx with
    | refl => exact hc
    | tail _ hstep ih => exact hclosed _ _ ih hstep
  exact hfun x y z hx

omit [Finite A] in
/-- Uniqueness travels forward along the run. -/
theorem UniqueFrom.mono {c d : Config A} (h : M.UniqueFrom c)
    (hcd : Relation.ReflTransGen M.Step c d) : M.UniqueFrom d :=
  fun x y z hx => h x y z (hcd.trans hx)

omit [Finite A] in
/-- **A machine unique from `c` has one run out of `c`**: two configurations
reachable from it are reachable from one another. -/
theorem reach_total_of_uniqueFrom {c x y : Config A} (huniq : M.UniqueFrom c)
    (hx : Relation.ReflTransGen M.Step c x) (hy : Relation.ReflTransGen M.Step c y) :
    Relation.ReflTransGen M.Step x y ∨ Relation.ReflTransGen M.Step y x := by
  induction hx with
  | refl => exact Or.inl hy
  | @tail x' x hcx' hstep ih =>
    rcases ih with h | h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨e, he, hey⟩
      · exact Or.inr (Relation.ReflTransGen.single hstep)
      · exact Or.inl ((huniq x' e x hcx' he hstep) ▸ hey)
    · exact Or.inr (h.tail hstep)

omit [Finite A] in
/-- **A deterministic machine has one run**: two configurations reachable from
the same starting point are reachable from one another. -/
theorem reach_total (hlin : IsLinOrd M.Le) (hdet : M.Deterministic) {c x y : Config A}
    (hx : Relation.ReflTransGen M.Step c x) (hy : Relation.ReflTransGen M.Step c y) :
    Relation.ReflTransGen M.Step x y ∨ Relation.ReflTransGen M.Step y x :=
  reach_total_of_uniqueFrom (uniqueFrom_of_deterministic hlin hdet c) hx hy

omit [Finite A] in
/-- **Runs of the same length out of a configuration unique from it end at the
same place.** -/
theorem stepsIn_functional_of_uniqueFrom : ∀ {n : ℕ} {c d d' : Config A},
    M.UniqueFrom c → M.StepsIn n c d → M.StepsIn n c d' → d = d' := by
  intro n
  induction n with
  | zero => intro c d d' _ h h'; exact (show c = d from h).symm.trans h'
  | succ n ih =>
    rintro c d d' huniq ⟨e, he, hrest⟩ ⟨e', he', hrest'⟩
    obtain rfl := huniq c e e' Relation.ReflTransGen.refl he he'
    exact ih (huniq.mono (Relation.ReflTransGen.single he)) hrest hrest'

omit [Finite A] in
/-- Nothing is reachable from a stuck configuration but itself. -/
theorem eq_of_reach_stuck {c d : Config A} (hstuck : ∀ e, ¬M.Step c e)
    (h : Relation.ReflTransGen M.Step c d) : c = d := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨e, he, -⟩
  · exact heq
  · exact absurd he (hstuck e)

omit [Finite A] in
/-- **A run into a dead end is not an accepting one**, at a machine unique from
where the run starts. This is the form a guessing program uses: the guess phase
is the only nondeterministic one, so what has to be ruled out is an accepting run
*of the same guess*, and that is a statement about one deterministic remainder.

`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` is this with the
uniqueness supplied by global determinism and the initial configuration matched
up. -/
theorem not_acc_of_reaches_dead_of_uniqueFrom {c₀ d : Config A} (huniq : M.UniqueFrom c₀)
    (hreach : Relation.ReflTransGen M.Step c₀ d)
    (hdead : ∀ e, ¬M.Step d e) (hnacc : ¬M.Acc d.state)
    (hsink : ∀ e : Config A, M.Acc e.state → ∀ e', ¬M.Step e e')
    {c : Config A} (hr : Relation.ReflTransGen M.Step c₀ c) (hacc : M.Acc c.state) :
    False := by
  rcases reach_total_of_uniqueFrom huniq hreach hr with h | h
  · exact hnacc ((eq_of_reach_stuck hdead h) ▸ hacc)
  · exact hnacc ((eq_of_reach_stuck (hsink c hacc) h) ▸ hacc)

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
  exact not_acc_of_reaches_dead_of_uniqueFrom
    (uniqueFrom_of_deterministic hwf.1 hdet _) hreach hdead hnacc hsink hr hacc

/-! ### A machine that never halts

The other way a no-instance is discharged, and the one a machine with no clock
needs: instead of *one* run that ends badly, an unbounded *chain* of runs that
never ends. A halted configuration is reached in a fixed number of steps, so a
chain whose `n`-th link costs at least `n` of them reaches none. -/

omit [Finite A] in
/-- Reachability is a run of some length. -/
theorem exists_stepsIn {c d : Config A}
    (h : Relation.ReflTransGen M.Step c d) : ∃ n, M.StepsIn n c d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih => exact ⟨ih.choose + 1, ih.choose_spec.trans_step hstep⟩

omit [Finite A] in
/-- A *nonempty* reachability is a run of positive length. -/
theorem exists_stepsIn_pos {c d : Config A}
    (h : Relation.TransGen M.Step c d) : ∃ n, 1 ≤ n ∧ M.StepsIn n c d := by
  induction h with
  | single hstep => exact ⟨1, le_rfl, ⟨_, hstep, rfl⟩⟩
  | tail _ hstep ih =>
    exact ⟨ih.choose + 1, Nat.le_succ_of_le ih.choose_spec.1,
      ih.choose_spec.2.trans_step hstep⟩

omit [Finite A] in
/-- **A stuck configuration is reached in one number of steps**: the shorter
run is a prefix of the longer one, and nothing leaves a dead end. -/
theorem stepsIn_eq_of_stuck (hlin : IsLinOrd M.Le) (hdet : M.Deterministic)
    {i j : ℕ} {c d : Config A} (hi : M.StepsIn i c d) (hj : M.StepsIn j c d)
    (hdead : ∀ e, ¬M.Step d e) : i = j := by
  have key : ∀ {a b : ℕ}, a ≤ b → M.StepsIn a c d → M.StepsIn b c d → a = b := by
    intro a b hab ha hb
    obtain ⟨x, hcx, hxd⟩ := stepsIn_split (m := a) (k := b - a)
      (Nat.add_sub_cancel' hab ▸ hb)
    obtain rfl := stepsIn_functional hlin hdet ha hcx
    match hba : b - a with
    | 0 => omega
    | k + 1 =>
      obtain ⟨e, he, -⟩ := hba ▸ hxd
      exact absurd he (hdead e)
  rcases le_total i j with hle | hle
  · exact key hle hi hj
  · exact (key hle hj hi).symm

omit [Finite A] in
/-- **A deterministic machine whose run passes an unbounded chain does not
accept.** Each link of the chain costs at least one step, so the `n`-th is
reached in at least `n`; an accepting configuration is stuck, hence reached in
one fixed number of steps, and lies beyond every link. This is what makes a
*diverging* computation a correct rejection with no clock anywhere. -/
theorem not_acceptsSpace_of_chain (hwf : M.WellFormed) (hdet : M.Deterministic)
    {c₀ : Config A} (hinit : M.IsInit c₀) {c : ℕ → Config A}
    (hc0 : Relation.ReflTransGen M.Step c₀ (c 0))
    (hstep : ∀ n, Relation.TransGen M.Step (c n) (c (n + 1)))
    (hsink : ∀ e : Config A, M.Acc e.state → ∀ e', ¬M.Step e e') :
    ¬M.AcceptsSpace := by
  rintro ⟨c₀', x, hinit', hr, hacc⟩
  rw [isInit_unique hwf hdet.1 hinit' hinit] at hr
  obtain ⟨k₀, hk₀⟩ := exists_stepsIn hc0
  -- the chain's `n`-th link is reached in at least `n` steps
  have hchain : ∀ n, ∃ m, n ≤ m ∧ M.StepsIn m c₀ (c n) := by
    intro n
    induction n with
    | zero => exact ⟨k₀, Nat.zero_le _, hk₀⟩
    | succ n ih =>
      obtain ⟨m, hm, hrun⟩ := ih
      obtain ⟨p, hp, hrun'⟩ := exists_stepsIn_pos (hstep n)
      exact ⟨m + p, by omega, hrun.trans hrun'⟩
  obtain ⟨k, hk⟩ := exists_stepsIn hr
  obtain ⟨m, hm, hrun⟩ := hchain (k + 1)
  -- and the accepting configuration lies beyond it, being stuck
  have hbeyond : Relation.ReflTransGen M.Step (c (k + 1)) x := by
    rcases reach_total hwf.1 hdet (reflTransGen_of_stepsIn hrun) hr with h | h
    · exact h
    · exact (eq_of_reach_stuck (hsink x hacc) h) ▸ Relation.ReflTransGen.refl
  obtain ⟨j, hj⟩ := exists_stepsIn hbeyond
  exact absurd (stepsIn_eq_of_stuck hwf.1 hdet hk (hrun.trans hj)
    (hsink x hacc)) (by omega)

omit [Finite A] in
/-- **The positive half**, for symmetry: a run from the initial configuration
to an accepting one is exactly what acceptance in bounded space asks for. -/
theorem acceptsSpace_of_reaches_acc {c₀ d : Config A} (hinit : M.IsInit c₀)
    (hreach : Relation.ReflTransGen M.Step c₀ d) (hacc : M.Acc d.state) :
    M.AcceptsSpace :=
  ⟨c₀, d, hinit, hreach, hacc⟩

end TMData

end DescriptiveComplexity
