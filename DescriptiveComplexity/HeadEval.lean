/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadProgram

/-!
# Evaluating a first-order formula with heads

The half of the capture theorem that has content: **a two-way multi-head
automaton can decide any fixed first-order formula of its head positions**,
spending two extra heads per quantifier.

The guards of a `DescriptiveComplexity.HeadProgram` are quantifier-free by fiat – a
control that could read a quantified fact would be first-order logic in
disguise. This file removes the apparent limitation: quantifiers are not *read*,
they are *walked*. To decide `∀ x, φ(x)` the program parks a head at the
greatest element, sweeps another head from the least element upwards, and
evaluates `φ` at each stop; it answers `false` at the first stop where `φ`
fails, and `true` when the sweep reaches the parked head. Existential
quantification is `∀` with `→ ⊥` around it, which the `imp` case already
handles, so a single sweep serves both.

## The two combinators

* `DescriptiveComplexity.HeadProgram.iteP` – run a fragment, then one of two others
  depending on its answer. This is branching, sequencing and negation at once.
* `DescriptiveComplexity.HeadProgram.scanP` – the sweep just described, on a pair of
  heads: `h` walks, `hm` marks the greatest element. **Why two heads and not
  one**: the sweep must know when to stop, and “this head is at the greatest
  element” is not a quantifier-free fact of one head – while “these two heads are
  equal” is, being an atom. A single parked head buys the test. The step off the
  end is not needed as a guard: `DescriptiveComplexity.HeadMove.succ` is simply
  disabled there.

Both are `DescriptiveComplexity.HeadProgram.wireP` over a four- or three-node control
graph, and both are proved by `DescriptiveComplexity.HeadProgram.runs_wireP`: the
sweep's proof is an induction *downwards* along the order
(`DescriptiveComplexity.order_induction_down`), which is the direction that knows about
the elements a walker has not yet reached.

## The evaluator

`DescriptiveComplexity.HeadProgram.evalP` is defined by structural recursion on a
`BoundedFormula`, with a fixed layout of the heads:

* the free variables live wherever the caller says, through a map `hv` into
  heads *below* the protection level `d`;
* the `i`-th bound variable lives at head `d + 2 * i`-ish – precisely, entering a
  quantifier at level `d` claims heads `d` and `d + 1` and recurses at level
  `d + 2`, so `DescriptiveComplexity.HeadProgram.qdepth` counts two heads per nested
  quantifier;
* everything from the current level up is scratch.

The recursion never inspects a state: each case is a combinator, and its
correctness is the corresponding combinator lemma applied to the inductive
hypothesis. The result, `DescriptiveComplexity.HeadProgram.decides_evalP`, is a
`DescriptiveComplexity.HeadProgram.Decides`, and
`DescriptiveComplexity.HeadProgram.deterministic_evalP` records that the evaluator is
deterministic – a sweep is not a guess – which is what lets the same evaluator
serve the deterministic capture.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

namespace HeadProgram

/-! ### Moving a single head -/

/-- The moves that send head `h` along `mv` and leave every other head where it
is. -/
def setHead (h : Fin K) (mv : HeadMove K) : Fin K → HeadMove K :=
  fun j => if j = h then mv else .stay

@[simp]
theorem setHead_self (h : Fin K) (mv : HeadMove K) : setHead h mv h = mv := by
  simp [setHead]

@[simp]
theorem setHead_of_ne {h j : Fin K} (mv : HeadMove K) (hj : j ≠ h) : setHead h mv j = .stay := by
  simp [setHead, hj]

section Moves

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **Moving, seen from the interface**: a fragment that only moves heads below
`m` runs a relation about those heads alone. -/
theorem runs_moveP_local (mvs : Fin K → HeadMove K) (m : ℕ)
    (hstay : ∀ j : Fin K, m ≤ (j : ℕ) → mvs j = .stay) :
    (moveP (L := L) mvs).Runs A m
      fun x b y => b = true ∧ ∀ j : Fin K, (j : ℕ) < m → (mvs j).Holds x j (y j) := by
  refine (runs_moveP mvs).mono ?_ ?_
  · rintro x b y ⟨rfl, hmv⟩
    exact ⟨rfl, fun j _ => hmv j⟩
  · rintro x b y ⟨rfl, hmv⟩
    refine ⟨fun j => if (j : ℕ) < m then y j else x j, fun j hj => by simp [hj], rfl, fun j => ?_⟩
    by_cases hj : (j : ℕ) < m
    · simpa [hj] using hmv j hj
    · rw [hstay j (not_lt.mp hj)]
      change (if (j : ℕ) < m then y j else x j) = x j
      rw [if_neg hj]

end Moves

/-! ### Branching -/

/-- The control nodes of a branch: the test, and its two continuations. -/
inductive IteNode
  /-- Running the test. -/
  | test : IteNode
  /-- Running the continuation taken when the test says `true`. -/
  | thenB : IteNode
  /-- Running the continuation taken when the test says `false`. -/
  | elseB : IteNode
  deriving DecidableEq

instance : Finite IteNode := by
  refine Finite.of_injective (fun n : IteNode => match n with
    | .test => (0 : Fin 3)
    | .thenB => 1
    | .elseB => 2) ?_
  rintro (_ | _ | _) (_ | _ | _) h <;> first
    | rfl
    | exact absurd h (by decide)

/-- The wiring of a branch: the test hands over to one of the continuations,
which then answer for the whole. -/
def iteWire : IteNode → Bool → IteNode ⊕ Bool
  | .test, true => Sum.inl .thenB
  | .test, false => Sum.inl .elseB
  | _, b => Sum.inr b

/-- The fragments of a branch. -/
def iteFam (F G H : HeadProgram L K) : IteNode → HeadProgram L K
  | .test => F
  | .thenB => G
  | .elseB => H

/-- **Branching**: run `F`; continue with `G` if it says `true` and with `H` if
it says `false`, and answer what the continuation answers. -/
def iteP (F G H : HeadProgram L K) : HeadProgram L K := wireP (iteFam F G H) iteWire .test

section Ite

variable {A : Type} [L.Structure A] [LinearOrder A]

omit [LinearOrder A] in
/-- The walk of a branch: from the test, one either has not moved, or has handed
over to one of the two continuations. -/
theorem iteWalk {R : IteNode → (Fin K → A) → Bool → (Fin K → A) → Prop} {x : Fin K → A}
    {u : IteNode × (Fin K → A)}
    (h : Relation.ReflTransGen (wireStep R iteWire) ((.test : IteNode), x) u) :
    u = ((.test : IteNode), x) ∨ (∃ y, u = ((.thenB : IteNode), y) ∧ R .test x true y) ∨
      ∃ y, u = ((.elseB : IteNode), y) ∧ R .test x false y := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail p q hp hpq ih =>
    obtain ⟨b, hR, hw⟩ := hpq
    rcases ih with rfl | ⟨y, rfl, hy⟩ | ⟨y, rfl, hy⟩
    · cases b
      · have hq1 : q.1 = IteNode.elseB := by simpa [iteWire] using hw.symm
        exact Or.inr (Or.inr ⟨q.2, Prod.ext_iff.mpr ⟨hq1, rfl⟩, hR⟩)
      · have hq1 : q.1 = IteNode.thenB := by simpa [iteWire] using hw.symm
        exact Or.inr (Or.inl ⟨q.2, Prod.ext_iff.mpr ⟨hq1, rfl⟩, hR⟩)
    · exact absurd hw (by cases b <;> simp [iteWire])
    · exact absurd hw (by cases b <;> simp [iteWire])

/-- The relations the fragments of a branch run. -/
def iteRel (R S T : (Fin K → A) → Bool → (Fin K → A) → Prop) :
    IteNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .test => R
  | .thenB => S
  | .elseB => T

/-- **What a branch runs**: the test, followed by whichever continuation its
answer selects. -/
theorem runs_iteP {m : ℕ} {F G H : HeadProgram L K}
    {R S T : (Fin K → A) → Bool → (Fin K → A) → Prop} (hF : F.Runs A m R) (hG : G.Runs A m S)
    (hH : H.Runs A m T) (hRl : HeadLocal2 m R) (hSl : HeadLocal2 m S) (hTl : HeadLocal2 m T) :
    (iteP F G H).Runs A m fun x b z => ∃ y, (R x true y ∧ S y b z) ∨ (R x false y ∧ T y b z) := by
  have hfam : ∀ c : IteNode, (iteFam F G H c).Runs A m (iteRel R S T c) := by
    rintro (_ | _ | _)
    exacts [hF, hG, hH]
  have hloc : ∀ c : IteNode, HeadLocal2 m (iteRel R S T c) := by
    rintro (_ | _ | _)
    exacts [hRl, hSl, hTl]
  refine (runs_wireP (iteFam F G H) iteWire hfam hloc .test).mono ?_ ?_
  · rintro x b y ⟨u, hwalk, b', hR', hw'⟩
    rcases iteWalk hwalk with rfl | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩
    · exact absurd hw' (by cases b' <;> simp [iteWire])
    · have hbb : b' = b := by simpa [iteWire] using hw'
      exact ⟨z, Or.inl ⟨hz, hbb ▸ hR'⟩⟩
    · have hbb : b' = b := by simpa [iteWire] using hw'
      exact ⟨z, Or.inr ⟨hz, hbb ▸ hR'⟩⟩
  · rintro x b z ⟨y, hy | hy⟩
    · exact ⟨z, HeadAgree.refl z, (.thenB, y),
        Relation.ReflTransGen.single ⟨true, hy.1, rfl⟩, b, hy.2, by cases b <;> rfl⟩
    · exact ⟨z, HeadAgree.refl z, (.elseB, y),
        Relation.ReflTransGen.single ⟨false, hy.1, rfl⟩, b, hy.2, by cases b <;> rfl⟩

/-- **What a branch decides**: the test's property, with the continuations'
properties under it. -/
theorem decides_iteP {m : ℕ} {F G H : HeadProgram L K} {P Q₁ Q₂ : (Fin K → A) → Prop}
    (hF : F.Decides A m P) (hG : G.Decides A m Q₁) (hH : H.Decides A m Q₂)
    (hP : HeadLocal m P) (hQ₁ : HeadLocal m Q₁) (hQ₂ : HeadLocal m Q₂) :
    (iteP F G H).Decides A m fun x => (P x ∧ Q₁ x) ∨ (¬P x ∧ Q₂ x) := by
  refine (runs_iteP hF hG hH (headLocal2_decides hP) (headLocal2_decides hQ₁)
    (headLocal2_decides hQ₂)).mono ?_ ?_
  · rintro x b z ⟨y, ⟨⟨hy1, hy2⟩, hz1, hz2⟩ | ⟨⟨hy1, hy2⟩, hz1, hz2⟩⟩
    · refine ⟨⟨fun hb => Or.inl ⟨hy1.mp rfl, (hQ₁ y x hy2.symm).mp (hz1.mp hb)⟩, fun hor => ?_⟩,
        hy2.trans hz2⟩
      rcases hor with ⟨-, hq⟩ | ⟨hnp, -⟩
      · exact hz1.mpr ((hQ₁ y x hy2.symm).mpr hq)
      · exact absurd (hy1.mp rfl) hnp
    · have hnp : ¬P x := fun hp => absurd (hy1.mpr hp) (by simp)
      refine ⟨⟨fun hb => Or.inr ⟨hnp, (hQ₂ y x hy2.symm).mp (hz1.mp hb)⟩, fun hor => ?_⟩,
        hy2.trans hz2⟩
      rcases hor with ⟨hp, -⟩ | ⟨-, hq⟩
      · exact absurd hp hnp
      · exact hz1.mpr ((hQ₂ y x hy2.symm).mpr hq)
  · rintro x b z ⟨hb, hxz⟩
    refine ⟨z, HeadAgree.refl z, x, ?_⟩
    by_cases hp : P x
    · refine Or.inl ⟨⟨by simp [hp], HeadAgree.refl x⟩, ?_, hxz⟩
      rw [hb]
      exact ⟨fun hor => by
          rcases hor with ⟨-, hq⟩ | ⟨hnp, -⟩
          · exact hq
          · exact absurd hp hnp,
        fun hq => Or.inl ⟨hp, hq⟩⟩
    · refine Or.inr ⟨⟨by simp [hp], HeadAgree.refl x⟩, ?_, hxz⟩
      rw [hb]
      exact ⟨fun hor => by
          rcases hor with ⟨hp', -⟩ | ⟨-, hq⟩
          · exact absurd hp' hp
          · exact hq,
        fun hq => Or.inr ⟨hp, hq⟩⟩

/-- A branch is deterministic as soon as its three fragments are. -/
theorem deterministic_iteP {F G H : HeadProgram L K} (hF : F.Deterministic A)
    (hG : G.Deterministic A) (hH : H.Deterministic A) : (iteP F G H).Deterministic A := by
  refine deterministic_wireP (iteFam F G H) iteWire .test ?_
  rintro (_ | _ | _)
  exacts [hF, hG, hH]

end Ite

/-! ### Sweeping a head along the order -/

/-- Which heads a move looks at: the ones a fragment protecting `m` heads may
mention. -/
def MoveLocal (m : ℕ) : HeadMove K → Prop
  | .stay => True
  | .toMin => True
  | .toMax => True
  | .copy i => (i : ℕ) < m
  | .succ i => (i : ℕ) < m
  | .pred i => (i : ℕ) < m

section MoveLocal

variable {A : Type} [LinearOrder A]

/-- A move that looks only at the first `m` heads cannot tell two assignments
agreeing there apart. -/
theorem holds_congr {mv : HeadMove K} {m : ℕ} (hmv : MoveLocal m mv) {x x' : Fin K → A}
    (hx : HeadAgree m x x') {j : Fin K} (hj : (j : ℕ) < m) (v : A) :
    mv.Holds x j v ↔ mv.Holds x' j v := by
  cases mv with
  | stay => rw [HeadMove.Holds, HeadMove.Holds, hx j hj]
  | toMin => exact Iff.rfl
  | toMax => exact Iff.rfl
  | copy i => rw [HeadMove.Holds, HeadMove.Holds, hx i hmv]
  | succ i => rw [HeadMove.Holds, HeadMove.Holds, hx i hmv]
  | pred i => rw [HeadMove.Holds, HeadMove.Holds, hx i hmv]

/-- The relation a move fragment runs is local when its moves are. -/
theorem headLocal2_moveP {mvs : Fin K → HeadMove K} {m : ℕ}
    (hloc : ∀ j : Fin K, (j : ℕ) < m → MoveLocal m (mvs j)) :
    HeadLocal2 m fun (x : Fin K → A) b y => b = true ∧
      ∀ j : Fin K, (j : ℕ) < m → (mvs j).Holds x j (y j) := by
  intro x x' y y' hx hy b
  refine and_congr Iff.rfl (forall_congr' fun j => imp_congr_right fun hj => ?_)
  rw [holds_congr (hloc j hj) hx hj, hy j hj]

end MoveLocal

/-- The control nodes of a sweep. -/
inductive ScanNode
  /-- Putting the walking head at the least element and the marker at the
  greatest. -/
  | reset : ScanNode
  /-- Evaluating the body at the current value of the walking head. -/
  | body : ScanNode
  /-- Asking whether the walking head has reached the marker. -/
  | atMax : ScanNode
  /-- Stepping the walking head to the next element. -/
  | bump : ScanNode
  deriving DecidableEq

instance : Finite ScanNode := by
  refine Finite.of_injective (fun n : ScanNode => match n with
    | .reset => (0 : Fin 4)
    | .body => 1
    | .atMax => 2
    | .bump => 3) ?_
  rintro (_ | _ | _ | _) (_ | _ | _ | _) h <;> first
    | rfl
    | exact absurd h (by decide)

/-- The wiring of a sweep: a body that fails ends it, a body that succeeds asks
whether the sweep is over, and if it is not the walking head steps on. -/
def scanWire : ScanNode → Bool → ScanNode ⊕ Bool
  | .reset, _ => Sum.inl .body
  | .body, true => Sum.inl .atMax
  | .body, false => Sum.inr false
  | .atMax, true => Sum.inr true
  | .atMax, false => Sum.inl .bump
  | .bump, _ => Sum.inl .body

/-- The moves that start a sweep: the walking head to the least element, the
marker to the greatest. -/
def resetMoves (h hm : Fin K) : Fin K → HeadMove K :=
  fun j => if j = h then .toMin else if j = hm then .toMax else .stay

/-- The fragments of a sweep. -/
def scanFam (h hm : Fin K) (F : HeadProgram L K) : ScanNode → HeadProgram L K
  | .reset => moveP (resetMoves h hm)
  | .body => F
  | .atMax => leafP (HeadMove.eqVarF L h hm) ((BoundedFormula.IsAtomic.equal _ _).isQF)
  | .bump => moveP (setHead h (.succ h))

/-- **The sweep**: run `F` at every value of head `h` in turn, from the least
element up to the marker head `hm`; answer `false` at the first value where `F`
does, and `true` if it never does. -/
def scanP (h hm : Fin K) (F : HeadProgram L K) : HeadProgram L K :=
  wireP (scanFam h hm F) scanWire .reset

section Scan

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The relations the fragments of a sweep run. -/
def scanRel (d : ℕ) (h hm : Fin K) (P : (Fin K → A) → Prop) :
    ScanNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .reset => fun x b y => b = true ∧
      ∀ j : Fin K, (j : ℕ) < d + 2 → (resetMoves h hm j).Holds x j (y j)
  | .body => fun x b y => (b = true ↔ P x) ∧ HeadAgree (d + 2) x y
  | .atMax => fun x b y => (b = true ↔ x h = x hm) ∧ HeadAgree (d + 2) x y
  | .bump => fun x b y => b = true ∧
      ∀ j : Fin K, (j : ℕ) < d + 2 → (setHead h (.succ h) j).Holds x j (y j)

/-- Restating what a fragment decides. -/
theorem Decides.congr {F : HeadProgram L K} {m : ℕ} {P P' : (Fin K → A) → Prop}
    (h : F.Decides A m P) (hPP : ∀ x, P x ↔ P' x) : F.Decides A m P' :=
  h.mono (fun x _ _ hxy => ⟨hxy.1.trans (hPP x), hxy.2⟩)
    fun x _ y hxy => ⟨y, HeadAgree.refl y, (hxy.1.trans (hPP x).symm), hxy.2⟩

/-- Reaching a target that is not there is impossible. -/
private theorem eq_of_covBy_of_covBy {a v z : A} (hv : a < v ∧ ∀ e : A, ¬(a < e ∧ e < v))
    (hz : a < z ∧ ∀ e : A, ¬(a < e ∧ e < z)) : v = z := by
  rcases lt_trichotomy v z with hlt | heq | hgt
  · exact absurd ⟨hv.1, hlt⟩ (hz.2 v)
  · exact heq
  · exact absurd ⟨hz.1, hgt⟩ (hv.2 z)

variable [Finite A]

/-- **What a sweep decides**: the body, at every value of the walking head. -/
theorem decides_scanP {d : ℕ} {h hm : Fin K} (hh : (h : ℕ) = d) (hhm : (hm : ℕ) = d + 1)
    {F : HeadProgram L K} {P : (Fin K → A) → Prop}
    (hF : F.Decides A (d + 2) P) (hP : HeadLocal (d + 1) P) :
    (scanP h hm F).Decides A d fun x => ∀ a : A, P (Function.update x h a) := by
  classical
  have hne : h ≠ hm := fun he => by rw [he, hhm] at hh; omega
  have hhd : (h : ℕ) < d + 2 := by omega
  have hhmd : (hm : ℕ) < d + 2 := by omega
  have hjlt : ∀ j : Fin K, (j : ℕ) < d + 1 → j ≠ h → (j : ℕ) < d := by
    intro j hj hjne
    have : (j : ℕ) ≠ (h : ℕ) := fun he => hjne (Fin.ext he)
    omega
  -- the property does not see anything but the heads below `d` and the walking head
  have hupd : ∀ (y y' : Fin K → A) (a : A), (∀ j : Fin K, (j : ℕ) < d → y' j = y j) →
      (P (Function.update y' h a) ↔ P (Function.update y h a)) := by
    intro y y' a hyy
    refine hP _ _ fun j hj => ?_
    rcases eq_or_ne j h with rfl | hjne
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hjne, Function.update_of_ne hjne]
      exact hyy j (hjlt j hj hjne)
  have hself : ∀ y : Fin K → A, P (Function.update y h (y h)) ↔ P y := by
    intro y
    rw [Function.update_eq_self]
  -- what each fragment does
  have hRreset : ∀ (x y : Fin K → A) (b : Bool), scanRel d h hm P .reset x b y →
      b = true ∧ (∀ a : A, y h ≤ a) ∧ (∀ a : A, a ≤ y hm) ∧
        ∀ j : Fin K, (j : ℕ) < d + 2 → j ≠ h → j ≠ hm → y j = x j := by
    rintro x y b ⟨rfl, hmv⟩
    have e1 : resetMoves h hm h = HeadMove.toMin := by simp [resetMoves]
    have e2 : resetMoves h hm hm = HeadMove.toMax := by simp [resetMoves, Ne.symm hne]
    refine ⟨rfl, ?_, ?_, fun j hj hj1 hj2 => ?_⟩
    · have hx := hmv h hhd
      rwa [e1] at hx
    · have hx := hmv hm hhmd
      rwa [e2] at hx
    · have hx := hmv j hj
      have e3 : resetMoves h hm j = HeadMove.stay := by simp [resetMoves, hj1, hj2]
      rwa [e3] at hx
  have hRbump : ∀ (x y : Fin K → A) (b : Bool), scanRel d h hm P .bump x b y →
      b = true ∧ (x h < y h ∧ ∀ e : A, ¬(x h < e ∧ e < y h)) ∧
        ∀ j : Fin K, (j : ℕ) < d + 2 → j ≠ h → y j = x j := by
    rintro x y b ⟨rfl, hmv⟩
    refine ⟨rfl, ?_, fun j hj hj1 => ?_⟩
    · have hx := hmv h hhd
      rwa [setHead_self] at hx
    · have hx := hmv j hj
      rwa [setHead_of_ne _ hj1] at hx
  -- soundness of the sweep proper, by induction downwards along the order
  have main_sound : ∀ c : A, ∀ y : Fin K → A, y h = c → (∀ a : A, a ≤ y hm) →
      ∀ (b : Bool) (z : Fin K → A),
        (∃ u, Relation.ReflTransGen (wireStep (scanRel d h hm P) scanWire)
            ((.body : ScanNode), y) u ∧ wireExit (scanRel d h hm P) scanWire u b z) →
        (b = true ↔ ∀ a : A, c ≤ a → P (Function.update y h a)) ∧
          ∀ j : Fin K, (j : ℕ) < d + 2 → j ≠ h → z j = y j := by
    intro c
    induction c using order_induction_down with
    | hmax c hcmax =>
      rintro y hyc hymax b z ⟨u, hwalk, hexit⟩
      have hhmc : y hm = c := le_antisymm (hcmax (y hm)) (hyc ▸ hymax (y h))
      rcases Relation.ReflTransGen.cases_head hwalk with rfl | ⟨v, hstep1, hrest⟩
      · obtain ⟨b', hRb, hw⟩ := hexit
        cases b' with
        | true => exact absurd hw (by simp [scanWire])
        | false =>
          have hb : b = false := by simpa [scanWire] using hw.symm
          subst hb
          obtain ⟨hiff, hag⟩ : (false = true ↔ P y) ∧ HeadAgree (d + 2) y z := hRb
          refine ⟨⟨fun hcon => absurd hcon (by simp), fun hall => ?_⟩,
            fun j hj _ => (hag j hj).symm⟩
          exact absurd ((hself y).mp (hyc ▸ hall c le_rfl)) (by simpa using hiff)
      · obtain ⟨b₁, hR₁, hw₁⟩ := hstep1
        cases b₁ with
        | false => exact absurd hw₁ (by simp [scanWire])
        | true =>
          have hv1 : v.1 = ScanNode.atMax := by simpa [scanWire] using hw₁.symm
          obtain ⟨hPy, hag₁⟩ : (true = true ↔ P y) ∧ HeadAgree (d + 2) y v.2 := hR₁
          rw [← Prod.mk.eta (p := v), hv1] at hrest
          rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨v', hstep2, hrest2⟩
          · obtain ⟨b', hRb, hw⟩ := hexit
            cases b' with
            | false => exact absurd hw (by simp [scanWire])
            | true =>
              have hb : b = true := by simpa [scanWire] using hw.symm
              subst hb
              obtain ⟨-, hag₂⟩ : (true = true ↔ v.2 h = v.2 hm) ∧ HeadAgree (d + 2) v.2 z := hRb
              refine ⟨⟨fun _ a hca => ?_, fun _ => rfl⟩,
                fun j hj hj1 => (hag₂ j hj).symm.trans (hag₁ j hj).symm⟩
              have hac : a = c := le_antisymm (hcmax a) hca
              rw [hac, ← hyc, hself]
              exact hPy.mp rfl
          · obtain ⟨b₂, hR₂, hw₂⟩ := hstep2
            cases b₂ with
            | true => exact absurd hw₂ (by simp [scanWire])
            | false =>
              obtain ⟨hne', -⟩ : (false = true ↔ v.2 h = v.2 hm) ∧
                HeadAgree (d + 2) v.2 v'.2 := hR₂
              exact absurd ((hag₁ h hhd).symm.trans ((hyc.trans hhmc.symm).trans (hag₁ hm hhmd)))
                (by simpa using hne')
    | hstep w c hwc hnb ih =>
      rintro y hyw hymax b z ⟨u, hwalk, hexit⟩
      have hwhm : w < y hm := lt_of_lt_of_le hwc (hymax c)
      rcases Relation.ReflTransGen.cases_head hwalk with rfl | ⟨v, hstep1, hrest⟩
      · obtain ⟨b', hRb, hw⟩ := hexit
        cases b' with
        | true => exact absurd hw (by simp [scanWire])
        | false =>
          have hb : b = false := by simpa [scanWire] using hw.symm
          subst hb
          obtain ⟨hiff, hag⟩ : (false = true ↔ P y) ∧ HeadAgree (d + 2) y z := hRb
          refine ⟨⟨fun hcon => absurd hcon (by simp), fun hall => ?_⟩,
            fun j hj _ => (hag j hj).symm⟩
          exact absurd ((hself y).mp (hyw ▸ hall w le_rfl)) (by simpa using hiff)
      · obtain ⟨b₁, hR₁, hw₁⟩ := hstep1
        cases b₁ with
        | false => exact absurd hw₁ (by simp [scanWire])
        | true =>
          have hv1 : v.1 = ScanNode.atMax := by simpa [scanWire] using hw₁.symm
          obtain ⟨hPy, hag₁⟩ : (true = true ↔ P y) ∧ HeadAgree (d + 2) y v.2 := hR₁
          rw [← Prod.mk.eta (p := v), hv1] at hrest
          rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨v', hstep2, hrest2⟩
          · obtain ⟨b', hRb, hw⟩ := hexit
            cases b' with
            | false => exact absurd hw (by simp [scanWire])
            | true =>
              obtain ⟨heq, -⟩ : (true = true ↔ v.2 h = v.2 hm) ∧
                HeadAgree (d + 2) v.2 z := hRb
              have : v.2 h = v.2 hm := heq.mp rfl
              rw [← hag₁ h hhd, ← hag₁ hm hhmd, hyw] at this
              exact absurd this (ne_of_lt hwhm)
          · obtain ⟨b₂, hR₂, hw₂⟩ := hstep2
            cases b₂ with
            | true => exact absurd hw₂ (by simp [scanWire])
            | false =>
              have hv'1 : v'.1 = ScanNode.bump := by simpa [scanWire] using hw₂.symm
              obtain ⟨-, hag₂⟩ : (false = true ↔ v.2 h = v.2 hm) ∧
                HeadAgree (d + 2) v.2 v'.2 := hR₂
              rw [← Prod.mk.eta (p := v'), hv'1] at hrest2
              rcases Relation.ReflTransGen.cases_head hrest2 with rfl | ⟨v'', hstep3, hrest3⟩
              · obtain ⟨b', -, hw⟩ := hexit
                exact absurd hw (by cases b' <;> simp [scanWire])
              · obtain ⟨b₃, hR₃, hw₃⟩ := hstep3
                have hv''1 : v''.1 = ScanNode.body := by
                  cases b₃ <;> simpa [scanWire] using hw₃.symm
                obtain ⟨-, hcov, hag₃⟩ := hRbump v'.2 v''.2 b₃ hR₃
                have hvh : v'.2 h = w := by
                  rw [← hag₂ h hhd, ← hag₁ h hhd, hyw]
                have hnext : v''.2 h = c := by
                  refine eq_of_covBy_of_covBy ?_ ⟨hwc, fun e he => hnb e he⟩
                  rw [← hvh]
                  exact hcov
                have hkeep : ∀ j : Fin K, (j : ℕ) < d + 2 → j ≠ h → v''.2 j = y j := by
                  intro j hj hj1
                  rw [hag₃ j hj hj1, ← hag₂ j hj, ← hag₁ j hj]
                rw [← Prod.mk.eta (p := v''), hv''1] at hrest3
                obtain ⟨hiff, hkeep'⟩ := ih v''.2 hnext
                  (by rw [hkeep hm hhmd (Ne.symm hne)]; exact hymax) b z ⟨u, hrest3, hexit⟩
                refine ⟨hiff.trans ⟨fun hall a hwa => ?_, fun hall a hca => ?_⟩,
                  fun j hj hj1 => (hkeep' j hj hj1).trans (hkeep j hj hj1)⟩
                · rcases eq_or_lt_of_le hwa with rfl | hlt
                  · rw [← hyw, hself]
                    exact hPy.mp rfl
                  · refine (hupd y v''.2 a fun j hj => hkeep j (by omega) ?_).mp
                      (hall a (by by_contra hcon; exact hnb a ⟨hlt, not_le.mp hcon⟩))
                    exact fun he => by rw [he, hh] at hj; omega
                · exact (hupd y v''.2 a fun j hj => hkeep j (by omega) fun he => by
                    rw [he, hh] at hj; omega).mpr (hall a (le_trans (le_of_lt hwc) hca))
  -- completeness of the sweep proper, by the same induction
  have main_complete : ∀ c : A, ∀ y : Fin K → A, y h = c → (∀ a : A, a ≤ y hm) →
      ∀ b : Bool, (b = true ↔ ∀ a : A, c ≤ a → P (Function.update y h a)) →
        ∃ z, (∀ j : Fin K, (j : ℕ) < d + 2 → j ≠ h → z j = y j) ∧
          ∃ u, Relation.ReflTransGen (wireStep (scanRel d h hm P) scanWire)
              ((.body : ScanNode), y) u ∧ wireExit (scanRel d h hm P) scanWire u b z := by
    intro c
    induction c using order_induction_down with
    | hmax c hcmax =>
      intro y hyc hymax b hb
      have hhmc : y hm = c := le_antisymm (hcmax (y hm)) (hyc ▸ hymax (y h))
      by_cases hPy : P y
      · have hall : ∀ a : A, c ≤ a → P (Function.update y h a) := by
          intro a hca
          have hac : a = c := le_antisymm (hcmax a) hca
          rw [hac, ← hyc, hself]
          exact hPy
        have hbt : b = true := hb.mpr hall
        subst hbt
        refine ⟨y, fun j _ _ => rfl, ((.atMax : ScanNode), y), Relation.ReflTransGen.single
          ⟨true, ⟨by simp [hPy], HeadAgree.refl y⟩, rfl⟩, true,
          ⟨⟨fun _ => ?_, fun _ => rfl⟩, HeadAgree.refl y⟩, rfl⟩
        change y h = y hm
        rw [hyc, hhmc]
      · have hbf : b = false := by
          cases b with
          | false => rfl
          | true =>
            have hx := hb.mp rfl c le_rfl
            rw [← hyc] at hx
            exact absurd ((hself y).mp hx) hPy
        subst hbf
        exact ⟨y, fun j _ _ => rfl, ((.body : ScanNode), y), Relation.ReflTransGen.refl, false,
          ⟨by simp [hPy], HeadAgree.refl y⟩, rfl⟩
    | hstep w c hwc hnb ih =>
      intro y hyw hymax b hb
      have hwhm : w < y hm := lt_of_lt_of_le hwc (hymax c)
      by_cases hPy : P y
      · have hy'h : (Function.update y h c) h = c := Function.update_self ..
        have hy'j : ∀ j : Fin K, j ≠ h → (Function.update y h c) j = y j :=
          fun j hj => Function.update_of_ne hj ..
        have hb' : b = true ↔ ∀ a : A, c ≤ a → P (Function.update (Function.update y h c) h a) := by
          rw [hb]
          constructor
          · intro hall a hca
            rw [Function.update_idem]
            exact hall a (le_trans (le_of_lt hwc) hca)
          · intro hall a hwa
            rcases eq_or_lt_of_le hwa with rfl | hlt
            · rw [← hyw, hself]
              exact hPy
            · have hca : c ≤ a := by
                by_contra hcon
                exact hnb a ⟨hlt, not_le.mp hcon⟩
              have hx := hall a hca
              rwa [Function.update_idem] at hx
        obtain ⟨z, hkeep, u, hwalk, hexit⟩ :=
          ih (Function.update y h c) hy'h (by rw [hy'j hm (Ne.symm hne)]; exact hymax) b hb'
        refine ⟨z, fun j hj hj1 => (hkeep j hj hj1).trans (hy'j j hj1), u, ?_, hexit⟩
        refine Relation.ReflTransGen.head (b := ((.atMax : ScanNode), y))
          ⟨true, ⟨by simp [hPy], HeadAgree.refl y⟩, rfl⟩ ?_
        refine Relation.ReflTransGen.head (b := ((.bump : ScanNode), y)) ⟨false, ⟨?_, ?_⟩, rfl⟩ ?_
        · change (false = true) ↔ y h = y hm
          simp only [Bool.false_eq_true, false_iff]
          rw [hyw]
          exact ne_of_lt hwhm
        · exact HeadAgree.refl y
        refine Relation.ReflTransGen.head (b := ((.body : ScanNode), Function.update y h c))
          ⟨true, ⟨rfl, fun j hj => ?_⟩, rfl⟩ hwalk
        change (setHead h (HeadMove.succ h) j).Holds y j (Function.update y h c j)
        by_cases hjh : j = h
        · rw [hjh, setHead_self, Function.update_self]
          change y h < c ∧ ∀ e : A, ¬(y h < e ∧ e < c)
          rw [hyw]
          exact ⟨hwc, hnb⟩
        · rw [setHead_of_ne _ hjh]
          exact hy'j j hjh
      · have hbf : b = false := by
          cases b with
          | false => rfl
          | true =>
            have hx := hb.mp rfl w le_rfl
            rw [← hyw] at hx
            exact absurd ((hself y).mp hx) hPy
        subst hbf
        exact ⟨y, fun j _ _ => rfl, ((.body : ScanNode), y), Relation.ReflTransGen.refl, false,
          ⟨by simp [hPy], HeadAgree.refl y⟩, rfl⟩
  -- the fragments run what they are meant to
  have hjne_h : ∀ j : Fin K, (j : ℕ) < d → j ≠ h := fun j hj he => by rw [he, hh] at hj; omega
  have hjne_hm : ∀ j : Fin K, (j : ℕ) < d → j ≠ hm := fun j hj he => by rw [he, hhm] at hj; omega
  have hRfam : ∀ c : ScanNode, (scanFam h hm F c).Runs A (d + 2) (scanRel d h hm P c) := by
    rintro (_ | _ | _ | _)
    · refine runs_moveP_local _ _ fun j hj => ?_
      have h1 : j ≠ h := fun he => by rw [he, hh] at hj; omega
      have h2 : j ≠ hm := fun he => by rw [he, hhm] at hj; omega
      simp [resetMoves, h1, h2]
    · exact hF
    · exact (decides_leafP (HeadMove.eqVarF L h hm)
        ((BoundedFormula.IsAtomic.equal _ _).isQF)).congr fun x => by simp
    · refine runs_moveP_local _ _ fun j hj => ?_
      have h1 : j ≠ h := fun he => by rw [he, hh] at hj; omega
      exact setHead_of_ne _ h1
  have hlocfam : ∀ c : ScanNode, HeadLocal2 (d + 2) (scanRel d h hm P c) := by
    rintro (_ | _ | _ | _)
    · refine headLocal2_moveP fun j hj => ?_
      rcases eq_or_ne j h with rfl | h1
      · simp [resetMoves, MoveLocal]
      · rcases eq_or_ne j hm with rfl | h2
        · simp [resetMoves, h1, MoveLocal]
        · simp [resetMoves, h1, h2, MoveLocal]
    · exact headLocal2_decides (hP.mono (by omega))
    · refine headLocal2_decides fun x x' hxx => ?_
      rw [hxx h hhd, hxx hm hhmd]
    · refine headLocal2_moveP fun j hj => ?_
      rcases eq_or_ne j h with rfl | h1
      · rw [setHead_self]
        exact hhd
      · rw [setHead_of_ne _ h1]
        trivial
  refine ((runs_wireP (scanFam h hm F) scanWire hRfam hlocfam .reset).weaken (by omega)).mono ?_ ?_
  · rintro x b y ⟨u, hwalk, hexit⟩
    rcases Relation.ReflTransGen.cases_head hwalk with rfl | ⟨v, hstep1, hrest⟩
    · obtain ⟨b', -, hw⟩ := hexit
      exact absurd hw (by cases b' <;> simp [scanWire])
    · obtain ⟨b₁, hR₁, hw₁⟩ := hstep1
      have hv1 : v.1 = ScanNode.body := by cases b₁ <;> simpa [scanWire] using hw₁.symm
      obtain ⟨-, hmin, hmax, hkeep0⟩ := hRreset x v.2 b₁ hR₁
      rw [← Prod.mk.eta (p := v), hv1] at hrest
      obtain ⟨hiff, hkeep⟩ := main_sound (v.2 h) v.2 rfl hmax b y ⟨u, hrest, hexit⟩
      refine ⟨hiff.trans ⟨fun hall a => ?_, fun hall a _ => ?_⟩, fun j hj => ?_⟩
      · exact (hupd x v.2 a fun i hi => hkeep0 i (by omega) (hjne_h i hi) (hjne_hm i hi)).mp
          (hall a (hmin a))
      · exact (hupd x v.2 a fun i hi => hkeep0 i (by omega) (hjne_h i hi) (hjne_hm i hi)).mpr
          (hall a)
      · rw [hkeep j (by omega) (hjne_h j hj), hkeep0 j (by omega) (hjne_h j hj) (hjne_hm j hj)]
  · rintro x b y ⟨hb, hxy⟩
    have hfin := Fintype.ofFinite A
    have hune : (Finset.univ : Finset A).Nonempty := ⟨x h, Finset.mem_univ _⟩
    obtain ⟨mn, hmn⟩ : ∃ mn : A, ∀ a : A, mn ≤ a :=
      ⟨Finset.univ.min' hune, fun a => Finset.min'_le _ a (Finset.mem_univ a)⟩
    obtain ⟨mx, hmx⟩ : ∃ mx : A, ∀ a : A, a ≤ mx :=
      ⟨Finset.univ.max' hune, fun a => Finset.le_max' _ a (Finset.mem_univ a)⟩
    have hy₀h : Function.update (Function.update x hm mx) h mn h = mn := Function.update_self ..
    have hy₀hm : Function.update (Function.update x hm mx) h mn hm = mx := by
      rw [Function.update_of_ne (Ne.symm hne), Function.update_self]
    have hy₀j : ∀ j : Fin K, j ≠ h → j ≠ hm →
        Function.update (Function.update x hm mx) h mn j = x j := by
      intro j h1 h2
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
    have hbcond : b = true ↔ ∀ a : A, mn ≤ a →
        P (Function.update (Function.update (Function.update x hm mx) h mn) h a) := by
      rw [hb]
      exact ⟨fun hall a _ => (hupd x _ a fun i hi => hy₀j i (hjne_h i hi) (hjne_hm i hi)).mpr
          (hall a),
        fun hall a => (hupd x _ a fun i hi => hy₀j i (hjne_h i hi) (hjne_hm i hi)).mp
          (hall a (hmn a))⟩
    obtain ⟨z, hkeep, u, hwalk, hexit⟩ :=
      main_complete mn _ hy₀h (by rw [hy₀hm]; exact hmx) b hbcond
    refine ⟨z, fun j hj => ?_, u, ?_, hexit⟩
    · rw [← hxy j hj, ← hy₀j j (hjne_h j hj) (hjne_hm j hj),
        hkeep j (by omega) (hjne_h j hj)]
    · refine Relation.ReflTransGen.head
        (b := ((.body : ScanNode), Function.update (Function.update x hm mx) h mn))
        ⟨true, ⟨rfl, fun j hj => ?_⟩, rfl⟩ hwalk
      change (resetMoves h hm j).Holds x j (Function.update (Function.update x hm mx) h mn j)
      by_cases h1 : j = h
      · have e1 : resetMoves h hm j = HeadMove.toMin := by simp [resetMoves, h1]
        rw [e1, h1, hy₀h]
        exact hmn
      · by_cases h2 : j = hm
        · have e2 : resetMoves h hm j = HeadMove.toMax := by
            simp [resetMoves, h2, Ne.symm hne]
          rw [e2, h2, hy₀hm]
          exact hmx
        · have e3 : resetMoves h hm j = HeadMove.stay := by simp [resetMoves, h1, h2]
          rw [e3]
          exact hy₀j j h1 h2

omit [Finite A] in
/-- A sweep is deterministic as soon as its body is: it walks, it does not
guess. -/
theorem deterministic_scanP {h hm : Fin K} {F : HeadProgram L K} (hF : F.Deterministic A) :
    (scanP h hm F).Deterministic A := by
  refine deterministic_wireP (scanFam h hm F) scanWire .reset ?_
  rintro (_ | _ | _ | _)
  exacts [deterministic_moveP _, hF,
    deterministic_leafP (HeadMove.eqVarF L h hm) ((BoundedFormula.IsAtomic.equal _ _).isQF),
    deterministic_moveP _]

end Scan

/-! ### Atoms as guards -/

variable {α : Type}

/-- An atomic formula, read as a guard on the heads: its variables are sent to
the heads that hold them. -/
def atomGuard {n : ℕ} (hv : α ⊕ Fin n → Fin K)
    (ψ : (L.sum Language.order).BoundedFormula α n) : (L.sum Language.order).Formula (Fin K) :=
  ψ.toFormula.relabel hv

/-- Turning the bound variables into free ones keeps a formula
quantifier-free. -/
theorem isQF_toFormula {n : ℕ} {ψ : (L.sum Language.order).BoundedFormula α n} (hψ : ψ.IsQF) :
    ψ.toFormula.IsQF := by
  induction hψ with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic hat =>
    cases hat with
    | equal t₁ t₂ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- A guard read off a quantifier-free formula is quantifier-free, as a guard
must be. -/
theorem isQF_atomGuard {n : ℕ} (hv : α ⊕ Fin n → Fin K)
    {ψ : (L.sum Language.order).BoundedFormula α n} (hψ : ψ.IsQF) : (atomGuard hv ψ).IsQF :=
  (isQF_toFormula hψ).relabel _

section Realize

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The guard holds exactly where the formula does, its variables read off the
heads. -/
theorem realize_atomGuard {n : ℕ} (hv : α ⊕ Fin n → Fin K)
    (ψ : (L.sum Language.order).BoundedFormula α n) (x : Fin K → A) :
    (atomGuard hv ψ).Realize x ↔
      ψ.Realize (fun a => x (hv (Sum.inl a))) (fun i => x (hv (Sum.inr i))) := by
  rw [atomGuard, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  rfl

/-- What a formula says of the heads depends only on the heads its variables
live in. -/
theorem headLocal_realize {n d : ℕ} (hv : α ⊕ Fin n → Fin K)
    (ψ : (L.sum Language.order).BoundedFormula α n) (hlow : ∀ v, (hv v : ℕ) < d) :
    HeadLocal d fun x : Fin K → A =>
      ψ.Realize (fun a => x (hv (Sum.inl a))) (fun i => x (hv (Sum.inr i))) := by
  intro x y hxy
  have h1 : (fun a => x (hv (Sum.inl a))) = fun a => y (hv (Sum.inl a)) :=
    funext fun a => hxy _ (hlow _)
  have h2 : (fun i => x (hv (Sum.inr i))) = fun i => y (hv (Sum.inr i)) :=
    funext fun i => hxy _ (hlow _)
  change ψ.Realize (fun a => x (hv (Sum.inl a))) (fun i => x (hv (Sum.inr i))) ↔
    ψ.Realize (fun a => y (hv (Sum.inl a))) (fun i => y (hv (Sum.inr i)))
  rw [h1, h2]

/-- Exiting at once decides falsity. -/
theorem decides_exitP_false (m : ℕ) :
    (exitP (L := L) (K := K) false).Decides A m fun _ => False := by
  refine (runs_exitP false).mono
    (fun x b y hxy => ⟨by simp [hxy.1], fun j _ => (congrFun hxy.2 j).symm⟩) ?_
  rintro x b y ⟨hb, hag⟩
  have hbf : b = false := by
    cases b with
    | false => rfl
    | true => exact absurd (hb.mp rfl) id
  exact ⟨x, hag.symm, hbf, rfl⟩

/-- Exiting at once decides truth. -/
theorem decides_exitP_true (m : ℕ) :
    (exitP (L := L) (K := K) true).Decides A m fun _ => True := by
  refine (runs_exitP true).mono
    (fun x b y hxy => ⟨by simp [hxy.1], fun j _ => (congrFun hxy.2 j).symm⟩) ?_
  rintro x b y ⟨hb, hag⟩
  exact ⟨x, hag.symm, hb.mpr trivial, rfl⟩

end Realize

/-! ### The evaluator -/

/-- **How many heads an evaluation needs**: two per nested quantifier, one to
walk and one to mark the greatest element. -/
def qdepth : ∀ {n : ℕ}, (L.sum Language.order).BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ₁ φ₂ => max (qdepth φ₁) (qdepth φ₂)
  | _, .all φ => qdepth φ + 2

/-- **The evaluator**: a program deciding a fixed first-order formula of the
heads. Atoms are guards, implication is a branch, and a quantifier is a sweep
of two fresh heads – `sh d` walking, `sh (d + 1)` marking the greatest
element. -/
def evalP (sh : ℕ → Fin K) : ∀ {n : ℕ}, ℕ → (α ⊕ Fin n → Fin K) →
    (L.sum Language.order).BoundedFormula α n → HeadProgram L K
  | _, _, _, .falsum => exitP false
  | _, _, hv, .equal t₁ t₂ =>
      leafP (atomGuard hv (BoundedFormula.equal t₁ t₂))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.equal t₁ t₂).isQF)
  | _, _, hv, .rel R ts =>
      leafP (atomGuard hv (BoundedFormula.rel R ts))
        (isQF_atomGuard hv (BoundedFormula.IsAtomic.rel R ts).isQF)
  | _, d, hv, .imp φ₁ φ₂ => iteP (evalP sh d hv φ₁) (evalP sh d hv φ₂) (exitP true)
  | _, d, hv, .all φ => scanP (sh d) (sh (d + 1))
      (evalP sh (d + 2)
        (Sum.elim (fun a => hv (Sum.inl a)) (Fin.snoc (fun i => hv (Sum.inr i)) (sh d))) φ)

section Eval

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- **The evaluator is correct**: it decides the formula, reading its variables
off the heads they live in, and gives those heads back untouched. -/
theorem decides_evalP (sh : ℕ → Fin K) (hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i) :
    ∀ {n : ℕ} (ψ : (L.sum Language.order).BoundedFormula α n) (d : ℕ) (hv : α ⊕ Fin n → Fin K),
      (∀ v, (hv v : ℕ) < d) → d + qdepth ψ ≤ K →
      (evalP sh d hv ψ).Decides A d fun x =>
        ψ.Realize (fun a => x (hv (Sum.inl a))) (fun i => x (hv (Sum.inr i))) := by
  intro n ψ
  induction ψ with
  | falsum =>
    intro d hv _ _
    exact (decides_exitP_false d).congr fun _ => Iff.rfl
  | equal t₁ t₂ =>
    intro d hv _ _
    exact (decides_leafP _ _).congr fun x => realize_atomGuard hv _ x
  | rel R ts =>
    intro d hv _ _
    exact (decides_leafP _ _).congr fun x => realize_atomGuard hv _ x
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro d hv hlow hK
    have hKm : d + max (qdepth φ₁) (qdepth φ₂) ≤ K := hK
    have hK₁ : d + qdepth φ₁ ≤ K := le_trans (Nat.add_le_add_left (le_max_left _ _) d) hKm
    have hK₂ : d + qdepth φ₂ ≤ K := le_trans (Nat.add_le_add_left (le_max_right _ _) d) hKm
    refine (decides_iteP (ih₁ d hv hlow hK₁) (ih₂ d hv hlow hK₂) (decides_exitP_true d)
      (headLocal_realize hv φ₁ hlow) (headLocal_realize hv φ₂ hlow)
      (fun _ _ _ => Iff.rfl)).congr fun x => ?_
    rw [BoundedFormula.realize_imp]
    exact ⟨fun hor hp => by
        rcases hor with ⟨-, hq⟩ | ⟨hnp, -⟩
        · exact hq
        · exact absurd hp hnp,
      fun himp => by
        by_cases hp : φ₁.Realize (fun a => x (hv (Sum.inl a))) fun i => x (hv (Sum.inr i))
        · exact Or.inl ⟨hp, himp hp⟩
        · exact Or.inr ⟨hp, trivial⟩⟩
  | @all n φ ih =>
    intro d hv hlow hK
    have hqd : d + (qdepth φ + 2) ≤ K := hK
    have hdK : d < K := by omega
    have hd1K : d + 1 < K := by omega
    have hh : ((sh d : Fin K) : ℕ) = d := hsh d hdK
    have hhm : ((sh (d + 1) : Fin K) : ℕ) = d + 1 := hsh (d + 1) hd1K
    set hv' : α ⊕ Fin (n + 1) → Fin K :=
      Sum.elim (fun a => hv (Sum.inl a)) (Fin.snoc (fun i => hv (Sum.inr i)) (sh d)) with hv'def
    have hbvlast : (Fin.snoc (fun i => hv (Sum.inr i)) (sh d) : Fin (n + 1) → Fin K)
        (Fin.last n) = sh d := Fin.snoc_last ..
    have hbvcast : ∀ j : Fin n, (Fin.snoc (fun i => hv (Sum.inr i)) (sh d) : Fin (n + 1) → Fin K)
        j.castSucc = hv (Sum.inr j) := fun j => Fin.snoc_castSucc ..
    have hlow' : ∀ v, (hv' v : ℕ) < d + 1 := by
      rintro (a | i)
      · exact lt_trans (hlow _) (by omega)
      · refine Fin.lastCases ?_ ?_ i
        · have hx : (hv' (Sum.inr (Fin.last n)) : Fin K) = sh d := hbvlast
          rw [hx, hh]
          omega
        · intro j
          have hx : (hv' (Sum.inr j.castSucc) : Fin K) = hv (Sum.inr j) := hbvcast j
          rw [hx]
          exact lt_trans (hlow _) (by omega)
    have hbody := ih (d + 2) hv' (fun v => lt_trans (hlow' v) (by omega)) (by omega)
    refine (decides_scanP hh hhm hbody (headLocal_realize hv' φ hlow')).congr fun x => ?_
    rw [BoundedFormula.realize_all]
    refine forall_congr' fun a => ?_
    have hnesh : ∀ v : α ⊕ Fin n, hv v ≠ sh d := by
      intro v he
      have hx := hlow v
      rw [he, hh] at hx
      omega
    have hfree : ∀ b : α, Function.update x (sh d) a (hv' (Sum.inl b)) = x (hv (Sum.inl b)) := by
      intro b
      have hx : (hv' (Sum.inl b) : Fin K) = hv (Sum.inl b) := rfl
      rw [hx]
      exact Function.update_of_ne (hnesh _) _ _
    have hbound : ∀ i : Fin (n + 1), Function.update x (sh d) a (hv' (Sum.inr i)) =
        (Fin.snoc (fun i => x (hv (Sum.inr i))) a : Fin (n + 1) → A) i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · have hx : (hv' (Sum.inr (Fin.last n)) : Fin K) = sh d := hbvlast
        rw [hx, Function.update_self, Fin.snoc_last]
      · intro j
        have hx : (hv' (Sum.inr j.castSucc) : Fin K) = hv (Sum.inr j) := hbvcast j
        rw [hx, Function.update_of_ne (hnesh _) _ _, Fin.snoc_castSucc]
    rw [funext hfree, funext hbound]

omit [Finite A] in
/-- **The evaluator is deterministic**: it sweeps, it does not guess. This is
what lets the same programs serve the deterministic capture. -/
theorem deterministic_evalP (sh : ℕ → Fin K) :
    ∀ {n : ℕ} (ψ : (L.sum Language.order).BoundedFormula α n) (d : ℕ) (hv : α ⊕ Fin n → Fin K),
      (evalP sh d hv ψ).Deterministic A := by
  intro n ψ
  induction ψ with
  | falsum => exact fun d hv => deterministic_exitP false
  | equal t₁ t₂ => exact fun d hv => deterministic_leafP _ _
  | rel R ts => exact fun d hv => deterministic_leafP _ _
  | imp φ₁ φ₂ ih₁ ih₂ =>
    exact fun d hv => deterministic_iteP (ih₁ d hv) (ih₂ d hv) (deterministic_exitP true)
  | @all n φ ih => exact fun d hv => deterministic_scanP (ih (d + 2) _)

end Eval

end HeadProgram

end DescriptiveComplexity
