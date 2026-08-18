/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadAutomaton

/-!
# Programs: two-way multi-head automata, written with guarded transitions

`DescriptiveComplexity.HeadAutomaton` is the machine model of the logarithmic-space
level, and it is stated the way a *finished* machine wants to be stated: a fixed
list of tests, and a transition table indexed by every outcome those tests may
have. That presentation is exactly wrong for *building* a machine, where one
wants to write one transition at a time, each carrying its own guard, and to
paste machines together.

This file is the assembly language. A `DescriptiveComplexity.HeadProgram` is the same
model with the transitions presented individually –

* a **guard**, a quantifier-free formula of the head positions;
* a **move** for every head;
* a **target**: another state of the program, or one of two *exits*, `true` and
  `false`

– and two compilations back into the finished form: `toAutomaton`, which enables
every transition whose guard holds, and `toAutomatonPri`, which enables the
*first* one, so that the compiled table has at most one entry per reading and
`DescriptiveComplexity.HeadAutomaton.IsDeterministic` holds outright. Programs whose
guards are mutually exclusive (`DescriptiveComplexity.HeadProgram.Deterministic`) run the
same way under both.

## What a program is proved to do

Two exits rather than one is what makes programs composable: a fragment can be
used as a *test* by another fragment. The specification of a fragment is
`DescriptiveComplexity.HeadProgram.Runs`: a relation `R x b y` describing which exits
`b`, with which head positions `y`, are reachable from the entry at head
positions `x`. It has two halves, and they are not symmetric –

* **soundness**: every reachable exit satisfies `R` – the fragment never lies;
* **completeness**: every `R`-related outcome is reachable *up to the scratch
  heads*, the ones a fragment is allowed to leave dirty.

The scratch heads are the point of the number `m` carried by `Runs`: heads below
`m` are the fragment's *protected* interface, heads from `m` on are workspace.
`DescriptiveComplexity.HeadAgree` and `DescriptiveComplexity.HeadLocal2` say “agrees on the
interface” and “depends only on the interface”.

## Composition

Everything is built from four pieces:

* `DescriptiveComplexity.HeadProgram.exitP` – exit at once;
* `DescriptiveComplexity.HeadProgram.leafP` – test a quantifier-free formula;
* `DescriptiveComplexity.HeadProgram.moveP` – move the heads;
* `DescriptiveComplexity.HeadProgram.wireP` – **the** combinator: a finite family of
  fragments, one per node of a *control graph*, each node saying where to go
  when its fragment exits `true` and where when it exits `false`.

`wireP` subsumes sequencing, branching and looping, and
`DescriptiveComplexity.HeadProgram.runs_wireP` reduces the runs of the assembled program
to a walk in the control graph whose steps are the runs of the fragments. Every
later construction – the formula evaluator, and the drivers that turn a
`DescriptiveComplexity.TCSpec` into a machine – is a control graph over fragments, and
its correctness proof is an argument about that walk, never about states.

The engine room is `DescriptiveComplexity.HeadProgram.Embeds`: a fragment sitting inside
a larger program, with the two lemmas that a run of the fragment is a run of the
program, and – the one that does the work – that a run of the program which
starts inside the fragment either is still inside it or has left it through one
of its exits.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

/-! ### Agreement on an interface -/

/-- Two head assignments **agree on the first `m` heads**: the interface a
fragment must preserve, the rest being scratch. -/
def HeadAgree (m : ℕ) {A : Type} (x y : Fin K → A) : Prop :=
  ∀ j : Fin K, (j : ℕ) < m → x j = y j

namespace HeadAgree

variable {m : ℕ} {A : Type} {x y z : Fin K → A}

@[refl]
theorem refl (x : Fin K → A) : HeadAgree m x x := fun _ _ => rfl

theorem symm (h : HeadAgree m x y) : HeadAgree m y x := fun j hj => (h j hj).symm

theorem trans (h : HeadAgree m x y) (h' : HeadAgree m y z) : HeadAgree m x z :=
  fun j hj => (h j hj).trans (h' j hj)

/-- Agreement on more heads is agreement on fewer. -/
theorem mono {m' : ℕ} (hm : m' ≤ m) (h : HeadAgree m x y) : HeadAgree m' x y :=
  fun j hj => h j (hj.trans_le hm)

end HeadAgree

/-- A property of the heads **depends only on the first `m` of them**. -/
def HeadLocal (m : ℕ) {A : Type} (P : (Fin K → A) → Prop) : Prop :=
  ∀ x y, HeadAgree m x y → (P x ↔ P y)

/-- A relation between two head assignments and an exit **depends only on the
first `m` heads** of each. -/
def HeadLocal2 (m : ℕ) {A : Type} (R : (Fin K → A) → Bool → (Fin K → A) → Prop) : Prop :=
  ∀ x x' y y', HeadAgree m x x' → HeadAgree m y y' → ∀ b, (R x b y ↔ R x' b y')

/-- Depending on fewer heads is depending on more. -/
theorem HeadLocal.mono {m m' : ℕ} {A : Type} {P : (Fin K → A) → Prop} (hm : m' ≤ m)
    (h : HeadLocal m' P) : HeadLocal m P :=
  fun x y hxy => h x y (hxy.mono hm)

/-! ### Guarded transitions -/

/-- **A guarded transition**: a quantifier-free guard on the current head
positions, a move for every head, and where to go – another state, or an
exit. -/
structure HeadTrans (L : Language.{0, 0}) (K : ℕ) (S : Type) where
  /-- The guard: the transition is available only where it holds. -/
  guard : (L.sum Language.order).Formula (Fin K)
  /-- What each head does. -/
  moves : Fin K → HeadMove K
  /-- Where the transition goes: a state, or an exit. -/
  target : S ⊕ Bool

/-- Rewiring a transition, for pasting a fragment into a larger program. -/
def HeadTrans.retarget {S S' : Type} (f : S ⊕ Bool → S' ⊕ Bool) (t : HeadTrans L K S) :
    HeadTrans L K S' where
  guard := t.guard
  moves := t.moves
  target := f t.target

@[simp]
theorem HeadTrans.retarget_guard {S S' : Type} (f : S ⊕ Bool → S' ⊕ Bool) (t : HeadTrans L K S) :
    (t.retarget f).guard = t.guard := rfl

@[simp]
theorem HeadTrans.retarget_moves {S S' : Type} (f : S ⊕ Bool → S' ⊕ Bool) (t : HeadTrans L K S) :
    (t.retarget f).moves = t.moves := rfl

@[simp]
theorem HeadTrans.retarget_target {S S' : Type} (f : S ⊕ Bool → S' ⊕ Bool) (t : HeadTrans L K S) :
    (t.retarget f).target = f t.target := rfl

/-! ### Programs -/

/-- **A program**: a two-way `K`-head automaton with its transitions presented
one at a time, each with its own quantifier-free guard, and with two exits. -/
structure HeadProgram (L : Language.{0, 0}) (K : ℕ) where
  /-- The states. -/
  St : Type
  /-- Finitely many states: that is what makes this a machine. -/
  [stFinite : Finite St]
  /-- Where a run starts. -/
  entry : St
  /-- The transitions available at each state, in order of priority. -/
  tr : St → List (HeadTrans L K St)
  /-- **The guards are quantifier-free**, as the tests of a machine must be. -/
  guard_qf : ∀ s, ∀ t ∈ tr s, t.guard.IsQF

attribute [instance] HeadProgram.stFinite

namespace HeadProgram

variable (F : HeadProgram L K)

/-- Where a run can be: at a state, or at one of the two exits. -/
abbrev Site : Type := F.St ⊕ Bool

/-- A configuration: a site together with the head positions. -/
abbrev Conf (A : Type) : Type := F.Site × (Fin K → A)

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- One step: some transition of the current state whose guard holds, with each
head moving as it prescribes. -/
def Step (c d : F.Conf A) : Prop :=
  ∃ s, c.1 = Sum.inl s ∧ ∃ t ∈ F.tr s, t.guard.Realize c.2 ∧ d.1 = t.target ∧
    ∀ j, (t.moves j).Holds c.2 j (d.2 j)

/-- Reachability: the reflexive-transitive closure of a step. -/
abbrev Reach : F.Conf A → F.Conf A → Prop := Relation.ReflTransGen F.Step

variable {F}

/-- Nothing happens at an exit: it has no transitions. -/
theorem not_step_exit {b : Bool} {y : Fin K → A} {d : F.Conf A} :
    ¬F.Step ((Sum.inr b : F.Site), y) d := by
  rintro ⟨s, hs, -⟩
  simp at hs

/-- A run that has reached an exit stays there. -/
theorem reach_exit {b : Bool} {y : Fin K → A} {d : F.Conf A}
    (h : F.Reach ((Sum.inr b : F.Site), y) d) : d = (Sum.inr b, y) := by
  induction h with
  | refl => rfl
  | @tail c d _ hcd ih => exact absurd (ih ▸ hcd) not_step_exit

/-- The step relation, at a state, spelled out. -/
theorem step_iff {s : F.St} {x : Fin K → A} {d : F.Conf A} :
    F.Step ((Sum.inl s : F.Site), x) d ↔
      ∃ t ∈ F.tr s, t.guard.Realize x ∧ d.1 = t.target ∧ ∀ j, (t.moves j).Holds x j (d.2 j) := by
  constructor
  · rintro ⟨s', hs', t, ht, hg, htar, hmv⟩
    have hss : s' = s := by simpa using hs'.symm
    subst hss
    exact ⟨t, ht, hg, htar, hmv⟩
  · rintro ⟨t, ht, hg, htar, hmv⟩
    exact ⟨s, rfl, t, ht, hg, htar, hmv⟩

/-- Taking a named transition is a step. -/
theorem step_of_mem {s : F.St} {x : Fin K → A} {t : HeadTrans L K F.St} (ht : t ∈ F.tr s)
    (hg : t.guard.Realize x) {d : F.Conf A} (htar : d.1 = t.target)
    (hmv : ∀ j, (t.moves j).Holds x j (d.2 j)) : F.Step ((Sum.inl s : F.Site), x) d :=
  ⟨s, rfl, t, ht, hg, htar, hmv⟩

end Semantics

/-! ### What a fragment does -/

section Runs

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The specification of a fragment**: `R x b y` describes the exits reachable
from the entry at head positions `x`. Soundness is exact – every reachable exit
is `R`-related – while completeness is up to the scratch heads, those from `m`
on. -/
structure Runs (F : HeadProgram L K) (A : Type) [L.Structure A] [LinearOrder A] (m : ℕ)
    (R : (Fin K → A) → Bool → (Fin K → A) → Prop) : Prop where
  /-- Every reachable exit is `R`-related to the entry. -/
  sound : ∀ {x : Fin K → A} {b : Bool} {y : Fin K → A},
    F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr b : F.Site), y) → R x b y
  /-- Every `R`-related outcome is reached, up to the scratch heads. -/
  complete : ∀ {x : Fin K → A} {b : Bool} {y : Fin K → A}, R x b y →
    ∃ y', HeadAgree m y y' ∧
      F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr b : F.Site), y')

/-- Leaving more heads dirty is allowed: a fragment protecting `m` heads
protects any smaller interface. -/
theorem Runs.weaken {F : HeadProgram L K} {m m' : ℕ}
    {R : (Fin K → A) → Bool → (Fin K → A) → Prop} (h : F.Runs A m R) (hle : m' ≤ m) :
    F.Runs A m' R where
  sound := h.sound
  complete hR := by
    obtain ⟨y', hag, hreach⟩ := h.complete hR
    exact ⟨y', hag.mono hle, hreach⟩

/-- **A fragment that decides a property**: it exits `true` exactly where the
property holds, and gives the interface heads back unchanged. -/
def Decides (F : HeadProgram L K) (A : Type) [L.Structure A] [LinearOrder A] (m : ℕ)
    (P : (Fin K → A) → Prop) : Prop :=
  F.Runs A m fun x b y => (b = true ↔ P x) ∧ HeadAgree m x y

theorem Decides.runs {F : HeadProgram L K} {m : ℕ} {P : (Fin K → A) → Prop}
    (h : F.Decides A m P) :
    F.Runs A m fun x b y => (b = true ↔ P x) ∧ HeadAgree m x y := h

omit [LinearOrder A] in
/-- The relation a decider runs is local when the property is. -/
theorem headLocal2_decides {m : ℕ} {P : (Fin K → A) → Prop} (hP : HeadLocal m P) :
    HeadLocal2 m fun x b y => (b = true ↔ P x) ∧ HeadAgree m x y := by
  intro x x' y y' hx hy b
  constructor
  · exact fun ⟨h1, h2⟩ => ⟨h1.trans (hP x x' hx), (hx.symm.trans h2).trans hy⟩
  · exact fun ⟨h1, h2⟩ => ⟨h1.trans (hP x x' hx).symm, (hx.trans h2).trans hy.symm⟩

end Runs

/-! ### Fragments inside programs -/

section Embeds

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- Where a site of the fragment sits in the larger program. -/
def esite {F P : HeadProgram L K} (e : F.St → P.St) (xt : Bool → P.Site) : F.Site → P.Site :=
  Sum.elim (fun s => Sum.inl (e s)) xt

/-- **The fragment `F` sits inside `P`** at `e`, its exits wired to `xt`: the
transitions of `P` at an embedded state are exactly those of `F`, retargeted. -/
def Embeds (F P : HeadProgram L K) (e : F.St → P.St) (xt : Bool → P.Site) : Prop :=
  ∀ s, P.tr (e s) = (F.tr s).map (HeadTrans.retarget (esite e xt))

variable {F P : HeadProgram L K} {e : F.St → P.St} {xt : Bool → P.Site}

/-- A step of the fragment is a step of the program. -/
theorem Embeds.step (h : Embeds F P e xt) {c d : F.Conf A} (hcd : F.Step c d) :
    P.Step (esite e xt c.1, c.2) (esite e xt d.1, d.2) := by
  obtain ⟨s, hs, t, ht, hg, htar, hmv⟩ := hcd
  refine ⟨e s, by rw [hs]; rfl, t.retarget (esite e xt), ?_, hg, ?_, hmv⟩
  · rw [h s]
    exact List.mem_map_of_mem ht
  · rw [HeadTrans.retarget_target, htar]

/-- A run of the fragment is a run of the program. -/
theorem Embeds.reach (h : Embeds F P e xt) {c d : F.Conf A} (hcd : F.Reach c d) :
    P.Reach (esite e xt c.1, c.2) (esite e xt d.1, d.2) := by
  induction hcd with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v _ huv ih => exact ih.tail (h.step huv)

/-- **The decomposition lemma**: a run of the program that starts inside the
fragment either is still inside it, or has left it through one of its exits – in
which case the program's run splits at that exit. -/
theorem Embeds.reach_cases (h : Embeds F P e xt) {s : F.St} {u : Fin K → A} {d : P.Conf A}
    (hd : P.Reach ((Sum.inl (e s) : P.Site), u) d) :
    (∃ s' w, d = ((Sum.inl (e s') : P.Site), w) ∧
        F.Reach ((Sum.inl s : F.Site), u) ((Sum.inl s' : F.Site), w)) ∨
      ∃ b w, F.Reach ((Sum.inl s : F.Site), u) ((Sum.inr b : F.Site), w) ∧ P.Reach (xt b, w) d := by
  induction hd with
  | refl => exact Or.inl ⟨s, u, rfl, Relation.ReflTransGen.refl⟩
  | @tail c d hc hcd ih =>
    rcases ih with ⟨s', w, rfl, hF⟩ | ⟨b, w, hF, hP⟩
    · obtain ⟨s₀, hs₀, t, ht, hg, htar, hmv⟩ := hcd
      have hs₀' : e s' = s₀ := by simpa using hs₀
      rw [← hs₀', h s'] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      have hstep : F.Step ((Sum.inl s' : F.Site), w) (t₀.target, d.2) :=
        step_of_mem ht₀ hg rfl hmv
      rcases hts : t₀.target with s'' | b
      · refine Or.inl ⟨s'', d.2, ?_, hF.tail (hts ▸ hstep)⟩
        rw [← Prod.mk.eta (p := d), htar, HeadTrans.retarget_target, hts]
        rfl
      · refine Or.inr ⟨b, d.2, hF.tail (hts ▸ hstep), ?_⟩
        rw [← Prod.mk.eta (p := d), htar, HeadTrans.retarget_target, hts]
        exact Relation.ReflTransGen.refl
    · exact Or.inr ⟨b, w, hF, hP.tail hcd⟩

end Embeds

/-! ### Determinism -/

section Deterministic

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **A program is deterministic** when the transitions available at a state
never disagree: any two whose guards hold at the same head positions have the
same target and the same moves. -/
def Deterministic (F : HeadProgram L K) (A : Type) [L.Structure A] [LinearOrder A] : Prop :=
  ∀ (s : F.St) (x : Fin K → A) (t t' : HeadTrans L K F.St), t ∈ F.tr s → t' ∈ F.tr s →
    t.guard.Realize x → t'.guard.Realize x → t.target = t'.target ∧ t.moves = t'.moves

/-- A deterministic program has a functional step relation: at most one
successor per configuration. -/
theorem Deterministic.functional {F : HeadProgram L K} (h : F.Deterministic A)
    {c d d' : F.Conf A} (hd : F.Step c d) (hd' : F.Step c d') : d = d' := by
  obtain ⟨s, hs, t, ht, hg, htar, hmv⟩ := hd
  obtain ⟨s', hs', t', ht', hg', htar', hmv'⟩ := hd'
  have hss : s = s' := Sum.inl.inj (hs.symm.trans hs')
  subst hss
  obtain ⟨heq, hmeq⟩ := h s c.2 t t' ht ht' hg hg'
  refine Prod.ext_iff.mpr ⟨htar.trans (heq.trans htar'.symm), funext fun j => ?_⟩
  exact HeadMove.holds_unique (hmv j) (hmeq ▸ hmv' j)

end Deterministic

/-! ### The pieces: exiting, testing, moving -/

/-- **Exit at once**, with the given answer. -/
def exitP (b : Bool) : HeadProgram L K where
  St := Unit
  entry := ()
  tr _ := [⟨⊤, fun _ => .stay, Sum.inr b⟩]
  guard_qf := by
    rintro s t ht
    rw [List.mem_singleton] at ht
    exact ht ▸ BoundedFormula.IsQF.top

/-- **Test a quantifier-free formula**: exit `true` where it holds and `false`
where it does not, without moving a head. -/
def leafP (φ : (L.sum Language.order).Formula (Fin K)) (hφ : φ.IsQF) : HeadProgram L K where
  St := Unit
  entry := ()
  tr _ := [⟨φ, fun _ => .stay, Sum.inr true⟩, ⟨∼φ, fun _ => .stay, Sum.inr false⟩]
  guard_qf := by
    rintro s t ht
    rcases List.mem_pair.mp (by simpa using ht) with rfl | rfl
    · exact hφ
    · exact hφ.not

/-- **Move the heads** and exit `true`. -/
def moveP (mvs : Fin K → HeadMove K) : HeadProgram L K where
  St := Unit
  entry := ()
  tr _ := [⟨⊤, mvs, Sum.inr true⟩]
  guard_qf := by
    rintro s t ht
    rw [List.mem_singleton] at ht
    exact ht ▸ BoundedFormula.IsQF.top

section Pieces

variable {A : Type} [L.Structure A] [LinearOrder A] {m : ℕ}

/-- Weakening what a fragment is known to run: any relation implied by `R` and
whose outcomes `R` already realizes up to the scratch heads. -/
theorem Runs.mono {F : HeadProgram L K} {R R' : (Fin K → A) → Bool → (Fin K → A) → Prop}
    (h : F.Runs A m R) (hsound : ∀ x b y, R x b y → R' x b y)
    (hcomplete : ∀ x b y, R' x b y → ∃ y', HeadAgree m y y' ∧ R x b y') : F.Runs A m R' where
  sound hr := hsound _ _ _ (h.sound hr)
  complete := by
    intro x b y hxy
    obtain ⟨y', hagree, hR⟩ := hcomplete x b y hxy
    obtain ⟨y'', hagree', hreach⟩ := h.complete hR
    exact ⟨y'', hagree.trans hagree', hreach⟩

/-- **A flat fragment** – one whose every transition out of the entry goes
straight to an exit – runs exactly one step. -/
theorem reach_exit_flat {F : HeadProgram L K}
    (hflat : ∀ t ∈ F.tr F.entry, ∃ b, t.target = Sum.inr b) {x : Fin K → A} {b : Bool}
    {y : Fin K → A} :
    F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr b : F.Site), y) ↔
      ∃ t ∈ F.tr F.entry, t.guard.Realize x ∧ t.target = Sum.inr b ∧
        ∀ j, (t.moves j).Holds x j (y j) := by
  constructor
  · intro hr
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨d, hd, hrest⟩
    · exact absurd (congrArg Prod.fst heq) (by simp)
    · obtain ⟨t, ht, hg, htar, hmv⟩ := step_iff.mp hd
      obtain ⟨b', hb'⟩ := hflat t ht
      have hd1 : d.1 = Sum.inr b' := htar.trans hb'
      have hdd : d = ((Sum.inr b' : F.Site), d.2) := Prod.ext_iff.mpr ⟨hd1, rfl⟩
      rw [hdd] at hrest
      have hfin := reach_exit hrest
      have hb : b = b' := by simpa using congrArg Prod.fst hfin
      have hy : y = d.2 := congrArg Prod.snd hfin
      subst hb
      subst hy
      exact ⟨t, ht, hg, hb', hmv⟩
  · rintro ⟨t, ht, hg, htar, hmv⟩
    exact Relation.ReflTransGen.single (step_of_mem ht hg htar.symm hmv)

/-! #### The transition tables of the pieces -/

@[simp]
theorem tr_exitP (b : Bool) (s : (exitP (L := L) (K := K) b).St) :
    (exitP (L := L) (K := K) b).tr s = [⟨⊤, fun _ => .stay, Sum.inr b⟩] := rfl

@[simp]
theorem tr_leafP (φ : (L.sum Language.order).Formula (Fin K)) (hφ : φ.IsQF)
    (s : (leafP φ hφ).St) :
    (leafP φ hφ).tr s =
      [⟨φ, fun _ => .stay, Sum.inr true⟩, ⟨∼φ, fun _ => .stay, Sum.inr false⟩] := rfl

@[simp]
theorem tr_moveP (mvs : Fin K → HeadMove K) (s : (moveP (L := L) mvs).St) :
    (moveP (L := L) mvs).tr s = [⟨⊤, mvs, Sum.inr true⟩] := rfl

theorem runs_exitP (b : Bool) :
    (exitP (L := L) (K := K) b).Runs A m fun x b' y => b' = b ∧ y = x := by
  have hflat : ∀ t ∈ (exitP (L := L) (K := K) b).tr (exitP b).entry,
      ∃ b', t.target = Sum.inr b' := by
    intro t ht
    simp only [tr_exitP, List.mem_singleton] at ht
    exact ⟨b, ht ▸ rfl⟩
  constructor
  · intro x b' y hr
    obtain ⟨t, ht, -, htar, hmv⟩ := (reach_exit_flat hflat).mp hr
    simp only [tr_exitP, List.mem_singleton] at ht
    subst ht
    exact ⟨(Sum.inr.inj htar).symm, funext hmv⟩
  · rintro x b' y ⟨rfl, rfl⟩
    exact ⟨y, HeadAgree.refl y, (reach_exit_flat hflat).mpr
      ⟨⟨⊤, fun _ => .stay, Sum.inr b'⟩, by simp, Formula.realize_top.mpr trivial, rfl,
        fun _ => rfl⟩⟩

theorem decides_leafP (φ : (L.sum Language.order).Formula (Fin K)) (hφ : φ.IsQF) :
    (leafP φ hφ).Decides A m fun x => φ.Realize x := by
  have hflat : ∀ t ∈ (leafP (L := L) (K := K) φ hφ).tr (leafP φ hφ).entry,
      ∃ b', t.target = Sum.inr b' := by
    intro t ht
    simp only [tr_leafP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  constructor
  · intro x b y hr
    obtain ⟨t, ht, hg, htar, hmv⟩ := (reach_exit_flat hflat).mp hr
    simp only [tr_leafP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by simp [← Sum.inr.inj htar, hg], fun j _ => (hmv j).symm⟩
    · refine ⟨?_, fun j _ => (hmv j).symm⟩
      rw [← Sum.inr.inj htar]
      simp only [Bool.false_eq_true, false_iff]
      exact Formula.realize_not.mp hg
  · rintro x b y ⟨hb, hxy⟩
    refine ⟨x, hxy.symm, (reach_exit_flat hflat).mpr ?_⟩
    cases b with
    | true =>
      refine ⟨⟨φ, fun _ => .stay, Sum.inr true⟩, by simp, hb.mp rfl, rfl, fun _ => rfl⟩
    | false =>
      refine ⟨⟨∼φ, fun _ => .stay, Sum.inr false⟩, by simp, ?_, rfl, fun _ => rfl⟩
      exact Formula.realize_not.mpr fun h => by simpa using hb.mpr h

theorem runs_moveP (mvs : Fin K → HeadMove K) :
    (moveP (L := L) mvs).Runs A m fun x b y => b = true ∧ ∀ j, (mvs j).Holds x j (y j) := by
  have hflat : ∀ t ∈ (moveP (L := L) mvs).tr (moveP mvs).entry, ∃ b', t.target = Sum.inr b' := by
    intro t ht
    simp only [tr_moveP, List.mem_singleton] at ht
    exact ⟨true, ht ▸ rfl⟩
  constructor
  · intro x b y hr
    obtain ⟨t, ht, -, htar, hmv⟩ := (reach_exit_flat hflat).mp hr
    simp only [tr_moveP, List.mem_singleton] at ht
    subst ht
    exact ⟨(Sum.inr.inj htar).symm, hmv⟩
  · rintro x b y ⟨rfl, hmv⟩
    exact ⟨y, HeadAgree.refl y, (reach_exit_flat hflat).mpr
      ⟨⟨⊤, mvs, Sum.inr true⟩, by simp, Formula.realize_top.mpr trivial, rfl, hmv⟩⟩

theorem deterministic_exitP (b : Bool) : (exitP (L := L) (K := K) b).Deterministic A := by
  intro s x t t' ht ht' _ _
  simp only [tr_exitP, List.mem_singleton] at ht ht'
  exact ht ▸ ht' ▸ ⟨rfl, rfl⟩

theorem deterministic_moveP (mvs : Fin K → HeadMove K) :
    (moveP (L := L) mvs).Deterministic A := by
  intro s x t t' ht ht' _ _
  simp only [tr_moveP, List.mem_singleton] at ht ht'
  exact ht ▸ ht' ▸ ⟨rfl, rfl⟩

theorem deterministic_leafP (φ : (L.sum Language.order).Formula (Fin K)) (hφ : φ.IsQF) :
    (leafP (L := L) φ hφ).Deterministic A := by
  intro s x t t' ht ht' hg hg'
  simp only [tr_leafP, List.mem_cons, List.not_mem_nil, or_false] at ht ht'
  rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact absurd hg (Formula.realize_not.mp hg')
  · exact absurd hg' (Formula.realize_not.mp hg)
  · exact ⟨rfl, rfl⟩

end Pieces

/-! ### Wiring fragments into a control graph -/

section Wire

variable {C : Type} [Finite C] (Fam : C → HeadProgram L K) (w : C → Bool → C ⊕ Bool)

/-- Where a run goes when the fragment at control node `c` exits with `b`: to
the entry of the fragment at the next control node, or out of the program. -/
def wireTo (c : C) (b : Bool) : (Σ c : C, (Fam c).St) ⊕ Bool :=
  match w c b with
  | Sum.inl c' => Sum.inl ⟨c', (Fam c').entry⟩
  | Sum.inr b' => Sum.inr b'

/-- **The control graph combinator**: run the fragment at the current control
node, and on its exit follow the wiring `w` – to another control node, or out.
Sequencing, branching and looping are all instances. -/
def wireP (c₀ : C) : HeadProgram L K where
  St := Σ c : C, (Fam c).St
  entry := ⟨c₀, (Fam c₀).entry⟩
  tr p := ((Fam p.1).tr p.2).map
    (HeadTrans.retarget (Sum.elim (fun s => Sum.inl ⟨p.1, s⟩) (wireTo Fam w p.1)))
  guard_qf := by
    rintro p t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact (Fam p.1).guard_qf p.2 t₀ ht₀

/-- Each fragment sits in the assembled program at its own control node. -/
theorem embeds_wireP (c₀ c : C) :
    Embeds (Fam c) (wireP Fam w c₀) (fun s => ⟨c, s⟩) (wireTo Fam w c) := fun _ => rfl

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- One step of **the control walk**: the fragment at `u.1` runs from `u.2` to
some exit, which the wiring sends on to the next control node. -/
def wireStep (R : C → (Fin K → A) → Bool → (Fin K → A) → Prop) (w : C → Bool → C ⊕ Bool)
    (u v : C × (Fin K → A)) : Prop :=
  ∃ b, R u.1 u.2 b v.2 ∧ w u.1 b = Sum.inl v.1

/-- How the control walk leaves the program. -/
def wireExit (R : C → (Fin K → A) → Bool → (Fin K → A) → Prop) (w : C → Bool → C ⊕ Bool)
    (u : C × (Fin K → A)) (b' : Bool) (y : Fin K → A) : Prop :=
  ∃ b, R u.1 u.2 b y ∧ w u.1 b = Sum.inr b'

/-- **What an assembled program runs is the control walk**: its exits are those
reached by walking the control graph, each step being a run of the fragment
sitting at that node. This is the lemma every later construction is proved
with. -/
theorem runs_wireP {m : ℕ} {R : C → (Fin K → A) → Bool → (Fin K → A) → Prop}
    (hR : ∀ c, (Fam c).Runs A m (R c)) (hloc : ∀ c, HeadLocal2 m (R c)) (c₀ : C) :
    (wireP Fam w c₀).Runs A m fun x b y =>
      ∃ u : C × (Fin K → A), Relation.ReflTransGen (wireStep R w) (c₀, x) u ∧
        wireExit R w u b y := by
  constructor
  · intro x b y hr
    suffices H : ∀ d : (wireP Fam w c₀).Conf A,
        (wireP Fam w c₀).Reach ((Sum.inl (wireP Fam w c₀).entry : (wireP Fam w c₀).Site), x) d →
        (∃ (c : C) (s : (Fam c).St) (u : Fin K → A), d.1 = Sum.inl ⟨c, s⟩ ∧
            Relation.ReflTransGen (wireStep R w) (c₀, x) (c, u) ∧
            (Fam c).Reach ((Sum.inl (Fam c).entry : (Fam c).Site), u)
              ((Sum.inl s : (Fam c).Site), d.2)) ∨
          ∃ b' : Bool, d.1 = Sum.inr b' ∧ ∃ u : C × (Fin K → A),
            Relation.ReflTransGen (wireStep R w) (c₀, x) u ∧ wireExit R w u b' d.2 by
      rcases H _ hr with ⟨c, s, u, hcontra, -, -⟩ | ⟨b', hb', u, hwalk, hexit⟩
      · exact absurd hcontra (by simp)
      · have hbb : b = b' := by simpa using hb'
        subst hbb
        exact ⟨u, hwalk, hexit⟩
    intro d hd
    induction hd with
    | refl => exact Or.inl ⟨c₀, (Fam c₀).entry, x, rfl, .refl, .refl⟩
    | @tail e d he hed ih =>
      rcases ih with ⟨c, s, u, hes, hwalk, hfrag⟩ | ⟨b', hb', hrest⟩
      · rw [← Prod.mk.eta (p := e), hes] at hed
        obtain ⟨t, ht, hg, htar, hmv⟩ := step_iff.mp hed
        obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
        have hstep : (Fam c).Step ((Sum.inl s : (Fam c).Site), e.2) (t₀.target, d.2) :=
          step_of_mem ht₀ hg rfl hmv
        rcases hts : t₀.target with s' | b₁
        · refine Or.inl ⟨c, s', u, ?_, hwalk, hfrag.tail (hts ▸ hstep)⟩
          rw [htar, HeadTrans.retarget_target, hts]
          rfl
        · have hRc : R c u b₁ d.2 := (hR c).sound (hfrag.tail (hts ▸ hstep))
          have hd1 : d.1 = wireTo Fam w c b₁ := by
            rw [htar, HeadTrans.retarget_target, hts]
            rfl
          rcases hw : w c b₁ with c' | b'
          · refine Or.inl ⟨c', (Fam c').entry, d.2, ?_, hwalk.tail ⟨b₁, hRc, hw⟩, .refl⟩
            rw [hd1]
            simp only [wireTo, hw]
            exact rfl
          · refine Or.inr ⟨b', ?_, (c, u), hwalk, ⟨b₁, hRc, hw⟩⟩
            rw [hd1]
            simp only [wireTo, hw]
            exact rfl
      · rw [← Prod.mk.eta (p := e), hb'] at hed
        exact absurd hed not_step_exit
  · rintro x b y ⟨u, hwalk, b₁, hR₁, hw₁⟩
    have key : ∀ v : C × (Fin K → A), Relation.ReflTransGen (wireStep R w) (c₀, x) v →
        ∃ z, HeadAgree m v.2 z ∧ (wireP Fam w c₀).Reach
          ((Sum.inl (wireP Fam w c₀).entry : (wireP Fam w c₀).Site), x)
          ((Sum.inl ⟨v.1, (Fam v.1).entry⟩ : (wireP Fam w c₀).Site), z) := by
      intro v hv
      induction hv with
      | refl => exact ⟨x, HeadAgree.refl x, .refl⟩
      | @tail p q hp hpq ih =>
        obtain ⟨z, hz, hreach⟩ := ih
        obtain ⟨b₂, hR₂, hw₂⟩ := hpq
        have hR₂' : R p.1 z b₂ q.2 :=
          (hloc p.1 p.2 z q.2 q.2 hz (HeadAgree.refl _) b₂).mp hR₂
        obtain ⟨z', hz', hsub⟩ := (hR p.1).complete hR₂'
        have himg : (wireP Fam w c₀).Reach
            ((Sum.inl ⟨p.1, (Fam p.1).entry⟩ : (wireP Fam w c₀).Site), z)
            (wireTo Fam w p.1 b₂, z') := (embeds_wireP Fam w c₀ p.1).reach hsub
        have hgo : wireTo Fam w p.1 b₂ = Sum.inl ⟨q.1, (Fam q.1).entry⟩ := by
          simp only [wireTo, hw₂]
        rw [hgo] at himg
        exact ⟨z', hz', hreach.trans himg⟩
    obtain ⟨z, hz, hreach⟩ := key u hwalk
    have hR₁' : R u.1 z b₁ y := (hloc u.1 u.2 z y y hz (HeadAgree.refl _) b₁).mp hR₁
    obtain ⟨y', hy', hsub⟩ := (hR u.1).complete hR₁'
    have himg : (wireP Fam w c₀).Reach
        ((Sum.inl ⟨u.1, (Fam u.1).entry⟩ : (wireP Fam w c₀).Site), z)
        (wireTo Fam w u.1 b₁, y') := (embeds_wireP Fam w c₀ u.1).reach hsub
    have hgo : wireTo Fam w u.1 b₁ = (Sum.inr b : (wireP Fam w c₀).Site) := by
      simp only [wireTo, hw₁]
      exact rfl
    rw [hgo] at himg
    exact ⟨y', hy', hreach.trans himg⟩

/-- An assembled program is deterministic as soon as its fragments are. -/
theorem deterministic_wireP (c₀ : C) (h : ∀ c, (Fam c).Deterministic A) :
    (wireP Fam w c₀).Deterministic A := by
  rintro ⟨c, s⟩ x t t' ht ht' hg hg'
  obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
  obtain ⟨t₀', ht₀', rfl⟩ := List.mem_map.mp ht'
  obtain ⟨htar, hmv⟩ := h c s x t₀ t₀' ht₀ ht₀' hg hg'
  exact ⟨by rw [HeadTrans.retarget_target, HeadTrans.retarget_target, htar], hmv⟩

end Wire

/-! ### Compiling a program into an automaton -/

section Compile

variable (F : HeadProgram L K)

/-- The tests a compiled program reads: the guard of each of its transitions. -/
abbrev TestOf : Type := Σ s : F.St, Fin (F.tr s).length

/-- The entry a transition contributes to the compiled transition table. -/
def entryOf (i : F.TestOf) : F.Site × (Fin K → HeadMove K) :=
  (((F.tr i.1).get i.2).target, ((F.tr i.1).get i.2).moves)

/-- The transitions of a state that a reading enables, by index. -/
def enabled (s : F.St) (r : F.TestOf → Bool) : List (Fin (F.tr s).length) :=
  (List.finRange (F.tr s).length).filter fun i => r ⟨s, i⟩

/-- **The compiled automaton**. At `pri := false` every transition whose guard
holds is enabled – the nondeterministic reading of a program. At `pri := true`
only the *first* one is, so that the table has at most one entry per reading and
`DescriptiveComplexity.HeadAutomaton.IsDeterministic` holds whatever the guards are. -/
def compile (pri : Bool) : HeadAutomaton L K where
  State := F.Site
  start := Sum.inl F.entry
  accept s := match s with
    | Sum.inr true => true
    | _ => false
  TestIx := F.TestOf
  test i := ((F.tr i.1).get i.2).guard
  test_qf i := F.guard_qf i.1 _ (List.get_mem _ _)
  trans s r := match s with
    | Sum.inl s' => (if pri then (F.enabled s' r).take 1 else F.enabled s' r).map
        fun i => F.entryOf ⟨s', i⟩
    | Sum.inr _ => []

@[simp]
theorem trans_compile_inl (pri : Bool) (s : F.St) (r : F.TestOf → Bool) :
    (F.compile pri).trans (Sum.inl s) r =
      (if pri then (F.enabled s r).take 1 else F.enabled s r).map fun i => F.entryOf ⟨s, i⟩ :=
  rfl

@[simp]
theorem trans_compile_inr (pri : Bool) (b : Bool) (r : F.TestOf → Bool) :
    (F.compile pri).trans (Sum.inr b) r = [] := rfl

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The step relation of a program, indexed by transitions rather than by
membership: the form the compiled table has. -/
theorem step_iff_index {s : F.St} {x : Fin K → A} {d : F.Conf A} :
    F.Step ((Sum.inl s : F.Site), x) d ↔
      ∃ i : Fin (F.tr s).length, ((F.tr s).get i).guard.Realize x ∧
        d.1 = ((F.tr s).get i).target ∧ ∀ j, (((F.tr s).get i).moves j).Holds x j (d.2 j) := by
  rw [step_iff]
  constructor
  · rintro ⟨t, ht, hrest⟩
    obtain ⟨i, hi⟩ := List.get_of_mem ht
    exact ⟨i, hi ▸ hrest⟩
  · rintro ⟨i, hrest⟩
    exact ⟨_, List.get_mem _ _, hrest⟩

/-- The step relation of a compiled automaton, in terms of the enabled
transitions of the program. -/
theorem step_compile (pri : Bool) {s : F.St} {x : Fin K → A} {d : F.Conf A} :
    (F.compile pri).Step ((Sum.inl s : F.Site), x) d ↔
      ∃ i ∈ (if pri then (F.enabled s ((F.compile pri).reading x)).take 1
          else F.enabled s ((F.compile pri).reading x)),
        d.1 = ((F.tr s).get i).target ∧ ∀ j, (((F.tr s).get i).moves j).Holds x j (d.2 j) := by
  constructor
  · rintro ⟨p, hp, htar, hmv⟩
    have hp' : p ∈ (if pri then (F.enabled s ((F.compile pri).reading x)).take 1
        else F.enabled s ((F.compile pri).reading x)).map fun i => F.entryOf ⟨s, i⟩ := hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp'
    exact ⟨i, hi, htar.symm, hmv⟩
  · rintro ⟨i, hi, htar, hmv⟩
    exact ⟨F.entryOf ⟨s, i⟩, List.mem_map_of_mem hi, htar.symm, hmv⟩

/-- Nothing steps out of an exit of a compiled automaton. -/
theorem not_step_compile_exit (pri : Bool) {b : Bool} {x : Fin K → A} {d : F.Conf A} :
    ¬(F.compile pri).Step ((Sum.inr b : F.Site), x) d := by
  rintro ⟨p, hp, -⟩
  have hp' : p ∈ ([] : List (F.Site × (Fin K → HeadMove K))) := hp
  cases hp'

/-- An index is enabled exactly when its guard holds. -/
theorem mem_enabled_iff (pri : Bool) (s : F.St) (x : Fin K → A) (i : Fin (F.tr s).length) :
    i ∈ F.enabled s ((F.compile pri).reading x) ↔ ((F.tr s).get i).guard.Realize x := by
  simp only [enabled, List.mem_filter]
  exact ⟨fun h => ((F.compile pri).reading_iff x ⟨s, i⟩).mp (by simpa using h.2),
    fun h => ⟨List.mem_finRange i, by simpa using ((F.compile pri).reading_iff x ⟨s, i⟩).mpr h⟩⟩

/-- **The compiled automaton runs the program**, in the nondeterministic
reading. -/
theorem step_compile_false (c d : F.Conf A) : (F.compile false).Step c d ↔ F.Step c d := by
  obtain ⟨site, x⟩ := c
  rcases site with s | b
  · refine Iff.trans (F.step_compile false) (Iff.trans ?_ (Iff.symm F.step_iff_index))
    simp only [Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨i, hi, htar, hmv⟩
      exact ⟨i, (F.mem_enabled_iff false s x i).mp hi, htar, hmv⟩
    · rintro ⟨i, hg, htar, hmv⟩
      exact ⟨i, (F.mem_enabled_iff false s x i).mpr hg, htar, hmv⟩
  · exact ⟨fun h => absurd h (F.not_step_compile_exit false), fun h => absurd h not_step_exit⟩

/-- The deterministic compilation has at most one transition per reading. -/
theorem isDeterministic_compile_true : (F.compile true).IsDeterministic := by
  rintro (s | b) r
  · change ((if true then (F.enabled s r).take 1 else F.enabled s r).map
      fun i => F.entryOf ⟨s, i⟩).length ≤ 1
    rw [if_pos rfl, List.length_map]
    simp [List.length_take]
  · exact Nat.zero_le 1

/-- **A deterministic program runs the same way under the deterministic
compilation**: taking the first enabled transition is taking the only one. -/
theorem step_compile_true (hdet : F.Deterministic A) (c d : F.Conf A) :
    (F.compile true).Step c d ↔ F.Step c d := by
  obtain ⟨site, x⟩ := c
  rcases site with s | b
  · refine Iff.trans (F.step_compile true) (Iff.trans ?_ (Iff.symm F.step_iff_index))
    rw [if_pos rfl]
    constructor
    · rintro ⟨i, hi, htar, hmv⟩
      exact ⟨i, (F.mem_enabled_iff true s x i).mp (List.mem_of_mem_take hi), htar, hmv⟩
    · rintro ⟨i, hg, htar, hmv⟩
      have hne : F.enabled s ((F.compile true).reading x) ≠ [] := by
        intro h
        have hmem : i ∈ ([] : List (Fin (F.tr s).length)) :=
          h ▸ (F.mem_enabled_iff true s x i).mpr hg
        cases hmem
      obtain ⟨i', l, hl⟩ := List.exists_cons_of_ne_nil hne
      have hi' : i' ∈ F.enabled s ((F.compile true).reading x) := by
        rw [hl]
        exact List.mem_cons_self
      obtain ⟨htar', hmv'⟩ := hdet s x _ _ (List.get_mem (F.tr s) i') (List.get_mem (F.tr s) i)
        ((F.mem_enabled_iff true s x i').mp hi') hg
      refine ⟨i', ?_, ?_, ?_⟩
      · rw [hl]
        simp
      · rw [htar, htar']
      · rw [hmv']
        exact hmv
  · exact ⟨fun h => absurd h (F.not_step_compile_exit true), fun h => absurd h not_step_exit⟩

/-- A run of the program is a run of the compiled automaton, and back. -/
theorem reach_compile (pri : Bool)
    (hstep : ∀ c d : F.Conf A, (F.compile pri).Step c d ↔ F.Step c d) {c d : F.Conf A} :
    Relation.ReflTransGen (F.compile pri).Step c d ↔ F.Reach c d := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail u v _ huv ih => exact ih.tail ((hstep u v).mp huv)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail u v _ huv ih => exact ih.tail ((hstep u v).mpr huv)

/-- **A compiled program is accepted exactly when its `true` exit is
reachable** from the entry with every head on the least element. -/
theorem accepts_compile (pri : Bool)
    (hstep : ∀ c d : F.Conf A, (F.compile pri).Step c d ↔ F.Step c d) :
    (F.compile pri).Accepts A ↔ ∃ x y : Fin K → A, (∀ j, ∀ a : A, x j ≤ a) ∧
      F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr true : F.Site), y) := by
  have hacc : ∀ s : F.Site, (F.compile pri).accept s = true ↔ s = (Sum.inr true : F.Site) := by
    rintro (s | b)
    · exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (by simp)⟩
    · cases b
      · exact ⟨fun h => Bool.noConfusion h, fun h => absurd h (by simp)⟩
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
  constructor
  · rintro ⟨⟨s₀, x₀⟩, ⟨s₁, x₁⟩, ⟨hs, hmin⟩, hreach, hac⟩
    refine ⟨x₀, x₁, hmin, ?_⟩
    have hwalk : F.Reach ((s₀ : F.Site), x₀) ((s₁ : F.Site), x₁) :=
      (F.reach_compile pri hstep).mp hreach
    have hs' : (s₀ : F.Site) = (Sum.inl F.entry : F.Site) := hs
    rw [hs', (hacc s₁).mp hac] at hwalk
    exact hwalk
  · rintro ⟨x, y, hmin, hreach⟩
    refine ⟨((Sum.inl F.entry : F.Site), x), ((Sum.inr true : F.Site), y), ⟨rfl, hmin⟩, ?_,
      (hacc _).mpr rfl⟩
    exact (F.reach_compile pri hstep).mpr hreach

/-- **The nondeterministic compilation accepts exactly what the program
reaches.** -/
theorem accepts_compile_false : (F.compile false).Accepts A ↔ ∃ x y : Fin K → A,
    (∀ j, ∀ a : A, x j ≤ a) ∧
      F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr true : F.Site), y) :=
  F.accepts_compile false F.step_compile_false

/-- **The deterministic compilation of a deterministic program accepts exactly
what the program reaches.** -/
theorem accepts_compile_true (hdet : F.Deterministic A) :
    (F.compile true).Accepts A ↔ ∃ x y : Fin K → A, (∀ j, ∀ a : A, x j ≤ a) ∧
      F.Reach ((Sum.inl F.entry : F.Site), x) ((Sum.inr true : F.Site), y) :=
  F.accepts_compile true (F.step_compile_true hdet)

end Compile

end HeadProgram

end DescriptiveComplexity
