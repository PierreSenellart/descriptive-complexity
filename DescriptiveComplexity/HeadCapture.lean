/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadEval

/-!
# The capture theorem for NL: FO(TC) is what a multi-head automaton recognizes

`DescriptiveComplexity.HeadAutomaton` compiles a machine into a
`DescriptiveComplexity.TCSpec`, which is the easy half. This file is the other half:
**every FO(TC) definable problem is recognized by a two-way multi-head
automaton**, so that the two notions coincide and
`DescriptiveComplexity.NL` is captured by the machine model as well as by the logic.

## The machine

Given a specification with arity `k`, the machine has `2 * k + D + 1` heads:

* the first `k` hold the **current tuple** of the walk;
* the next `k` hold a **candidate** for the next tuple;
* the remaining `D` are the workspace of
  `DescriptiveComplexity.HeadProgram.evalP`, which evaluates the specification's
  formulas – `D` being the largest quantifier budget among them – plus one spare
  head so that the head type is never empty.

The *mode* of the walk is not on a head – it cannot be, a one-element universe
having only one tuple – but in the control, which is what a finite control is
for.

## The loop

Written as a control graph over fragments
(`DescriptiveComplexity.HeadProgram.wireP`), the machine is:

* **pick a source mode**: a chain of free choices
  (`DescriptiveComplexity.HeadProgram.chooseP`) walking the list of modes, so that any
  mode may be selected;
* **try it**: guess the current tuple (`DescriptiveComplexity.HeadProgram.guessP`,
  a head walked up the order by a nondeterministic number of steps) and evaluate
  the source formula; a failure leads nowhere;
* **at a node**: evaluate the target formula – if it holds, accept;
* otherwise **pick a candidate mode**, guess the candidate tuple, evaluate the
  transition formula, and, if it holds, **commit**: copy the candidate onto the
  current tuple and go back to evaluating the target formula.

Guessing is where the nondeterminism lives, and it is the only place: the
evaluator itself is deterministic.

## The proof

`DescriptiveComplexity.HeadProgram.runs_wireP` turns the machine's runs into a walk in
the control graph, and the correctness is then an argument about that walk, in
two directions:

* **soundness** – an invariant carried along the walk: at a node of the control
  graph, the tuple on the first `k` heads is a node of the specification
  reachable from a source. It is preserved by every arc, and at the accepting
  arc it says exactly that the specification accepts;
* **completeness** – by induction along `DescriptiveComplexity.TCSpec.Reach`: every
  step of the specification's walk is imitated by the loop above, unless the
  target formula holds on the way, in which case the machine has already
  accepted.

The result is `DescriptiveComplexity.tcDefinable_iff_automaton`, and with it
`DescriptiveComplexity.mem_NL_iff_automaton`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {K : ℕ}

namespace HeadProgram

/-! ### Free choices and guesses -/

/-- **A free choice**: exit either way, moving no head. It is the only source of
nondeterminism in the machines built here, together with
`DescriptiveComplexity.HeadProgram.guessP`. -/
def chooseP : HeadProgram L K where
  St := Unit
  entry := ()
  tr _ := [⟨⊤, fun _ => .stay, Sum.inr true⟩, ⟨⊤, fun _ => .stay, Sum.inr false⟩]
  guard_qf := by
    rintro s t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact BoundedFormula.IsQF.top

/-- One step of a guess: either walk head `h` to the next element, or stop. -/
def guessStepP (h : Fin K) : HeadProgram L K where
  St := Unit
  entry := ()
  tr _ := [⟨⊤, setHead h (.succ h), Sum.inr true⟩, ⟨⊤, fun _ => .stay, Sum.inr false⟩]
  guard_qf := by
    rintro s t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact BoundedFormula.IsQF.top

@[simp]
theorem tr_chooseP (s : (chooseP (L := L) (K := K)).St) :
    (chooseP (L := L) (K := K)).tr s =
      [⟨⊤, fun _ => .stay, Sum.inr true⟩, ⟨⊤, fun _ => .stay, Sum.inr false⟩] := rfl

@[simp]
theorem tr_guessStepP (h : Fin K) (s : (guessStepP (L := L) h).St) :
    (guessStepP (L := L) h).tr s =
      [⟨⊤, setHead h (.succ h), Sum.inr true⟩, ⟨⊤, fun _ => .stay, Sum.inr false⟩] := rfl

section Choice

variable {A : Type} [L.Structure A] [LinearOrder A] {m : ℕ}

theorem runs_chooseP : (chooseP (L := L) (K := K)).Runs A m fun x _ y => HeadAgree m x y := by
  have hflat : ∀ t ∈ (chooseP (L := L) (K := K)).tr (chooseP (L := L) (K := K)).entry,
      ∃ b', t.target = Sum.inr b' := by
    intro t ht
    simp only [tr_chooseP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [⟨true, rfl⟩, ⟨false, rfl⟩]
  constructor
  · intro x b y hr
    obtain ⟨t, ht, -, -, hmv⟩ := (reach_exit_flat hflat).mp hr
    simp only [tr_chooseP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact fun j _ => (hmv j).symm
  · intro x b y hag
    refine ⟨x, hag.symm, (reach_exit_flat hflat).mpr ?_⟩
    cases b with
    | true =>
      exact ⟨⟨⊤, fun _ => .stay, Sum.inr true⟩, by simp, Formula.realize_top.mpr trivial, rfl,
        fun _ => rfl⟩
    | false =>
      exact ⟨⟨⊤, fun _ => .stay, Sum.inr false⟩, by simp, Formula.realize_top.mpr trivial, rfl,
        fun _ => rfl⟩

theorem runs_guessStepP (h : Fin K) (hh : (h : ℕ) < m) :
    (guessStepP (L := L) h).Runs A m fun x b y =>
      (b = true ∧ (x h < y h ∧ ∀ e : A, ¬(x h < e ∧ e < y h)) ∧
        ∀ j : Fin K, (j : ℕ) < m → j ≠ h → y j = x j) ∨ (b = false ∧ HeadAgree m x y) := by
  have hflat : ∀ t ∈ (guessStepP (L := L) h).tr (guessStepP (L := L) h).entry,
      ∃ b', t.target = Sum.inr b' := by
    intro t ht
    simp only [tr_guessStepP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [⟨true, rfl⟩, ⟨false, rfl⟩]
  constructor
  · intro x b y hr
    obtain ⟨t, ht, -, htar, hmv⟩ := (reach_exit_flat hflat).mp hr
    simp only [tr_guessStepP, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have hxh := hmv h
      simp only [setHead_self] at hxh
      refine Or.inl ⟨(Sum.inr.inj htar).symm, hxh, fun j _ hj => ?_⟩
      have hx := hmv j
      simp only [setHead_of_ne _ hj] at hx
      exact hx
    · exact Or.inr ⟨(Sum.inr.inj htar).symm, fun j _ => (hmv j).symm⟩
  · rintro x b y (⟨rfl, hsucc, hkeep⟩ | ⟨rfl, hag⟩)
    · refine ⟨fun j => if (j : ℕ) < m then y j else if j = h then y j else x j, ?_,
        (reach_exit_flat hflat).mpr ⟨⟨⊤, setHead h (.succ h), Sum.inr true⟩, by simp,
          Formula.realize_top.mpr trivial, rfl, fun j => ?_⟩⟩
      · intro j hj
        simp [hj]
      · change (setHead h (HeadMove.succ h) j).Holds x j
          (if (j : ℕ) < m then y j else if j = h then y j else x j)
        by_cases hj : j = h
        · rw [hj, setHead_self, if_pos hh]
          exact hsucc
        · rw [setHead_of_ne _ hj]
          change (if (j : ℕ) < m then y j else if j = h then y j else x j) = x j
          by_cases hjm : (j : ℕ) < m
          · rw [if_pos hjm]
            exact hkeep j hjm hj
          · rw [if_neg hjm, if_neg hj]
    · refine ⟨x, hag.symm, (reach_exit_flat hflat).mpr ⟨⟨⊤, fun _ => .stay, Sum.inr false⟩,
        by simp, Formula.realize_top.mpr trivial, rfl, fun _ => rfl⟩⟩

end Choice

/-! ### Guessing one head -/

/-- The control nodes of a guess. -/
inductive GuessNode
  /-- Putting the head on the least element. -/
  | reset : GuessNode
  /-- Walking it up, for as long as the machine chooses to. -/
  | loop : GuessNode
  deriving DecidableEq

instance : Finite GuessNode := by
  refine Finite.of_injective (fun n : GuessNode => match n with
    | .reset => (0 : Fin 2)
    | .loop => 1) ?_
  rintro (_ | _) (_ | _) h <;> first
    | rfl
    | exact absurd h (by decide)

/-- The wiring of a guess: walk up, or stop and answer `true`. -/
def guessWire : GuessNode → Bool → GuessNode ⊕ Bool
  | .reset, _ => Sum.inl .loop
  | .loop, true => Sum.inl .loop
  | .loop, false => Sum.inr true

/-- The fragments of a guess. -/
def guessFam (h : Fin K) : GuessNode → HeadProgram L K
  | .reset => moveP (setHead h .toMin)
  | .loop => guessStepP h

/-- **Guessing a head**: put head `h` on the least element and walk it up a
nondeterministic number of steps, so that it may end anywhere. -/
def guessP (h : Fin K) : HeadProgram L K := wireP (guessFam h) guessWire .reset

section Guess

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] {m : ℕ}

/-- The relations the fragments of a guess run. -/
def guessRel (h : Fin K) (m : ℕ) : GuessNode → (Fin K → A) → Bool → (Fin K → A) → Prop
  | .reset => fun x b y => b = true ∧
      ∀ j : Fin K, (j : ℕ) < m → (setHead h (.toMin) j).Holds x j (y j)
  | .loop => fun x b y =>
      (b = true ∧ (x h < y h ∧ ∀ e : A, ¬(x h < e ∧ e < y h)) ∧
        ∀ j : Fin K, (j : ℕ) < m → j ≠ h → y j = x j) ∨ (b = false ∧ HeadAgree m x y)

/-- **What a guess runs**: head `h` may end anywhere, every other head staying
where it was. -/
theorem runs_guessP (h : Fin K) (hh : (h : ℕ) < m) :
    (guessP (L := L) h).Runs A m fun x b y =>
      b = true ∧ ∀ j : Fin K, (j : ℕ) < m → j ≠ h → y j = x j := by
  have hfam : ∀ c, (guessFam (L := L) h c).Runs A m (guessRel h m c) := by
    rintro (_ | _)
    · refine runs_moveP_local _ _ fun j hj => setHead_of_ne _ fun he => ?_
      rw [he] at hj
      omega
    · exact runs_guessStepP h hh
  have hloc : ∀ c, HeadLocal2 m (guessRel (A := A) h m c) := by
    rintro (_ | _)
    · refine headLocal2_moveP fun j hj => ?_
      by_cases hjh : j = h
      · rw [hjh, setHead_self]
        trivial
      · rw [setHead_of_ne _ hjh]
        trivial
    · intro x x' y y' hx hy b
      constructor
      · rintro (⟨rfl, hs, hk⟩ | ⟨rfl, hag⟩)
        · exact Or.inl ⟨rfl, by rw [← hx h hh, ← hy h hh]; exact hs,
            fun j hj hjh => by rw [← hy j hj, ← hx j hj]; exact hk j hj hjh⟩
        · exact Or.inr ⟨rfl, hx.symm.trans (hag.trans hy)⟩
      · rintro (⟨rfl, hs, hk⟩ | ⟨rfl, hag⟩)
        · exact Or.inl ⟨rfl, by rw [hx h hh, hy h hh]; exact hs,
            fun j hj hjh => by rw [hy j hj, hx j hj]; exact hk j hj hjh⟩
        · exact Or.inr ⟨rfl, hx.trans (hag.trans hy.symm)⟩
  -- the walk of a guess: from the loop, the head may be anywhere above where it is
  have hwalk : ∀ (x : Fin K → A) (a : A), x h ≤ a →
      Relation.ReflTransGen (wireStep (guessRel (A := A) h m) guessWire) ((.loop : GuessNode), x)
        ((.loop : GuessNode), Function.update x h a) := by
    intro x a
    induction a using order_induction with
    | hmin z hz =>
      intro hxz
      have : Function.update x h z = x := by
        rw [le_antisymm (hz (x h)) hxz, Function.update_eq_self]
      rw [this]
    | hstep w z hwz hnb ih =>
      intro hxz
      rcases eq_or_lt_of_le hxz with rfl | hlt
      · rw [Function.update_eq_self]
      · have hxw : x h ≤ w := by
          by_contra hcon
          exact hnb (x h) ⟨not_le.mp hcon, hlt⟩
        refine (ih hxw).tail ⟨true, Or.inl ⟨rfl, ?_, fun j hj hjh => ?_⟩, rfl⟩
        · simp only [Function.update_self]
          exact ⟨hwz, fun e he => hnb e he⟩
        · simp only [Function.update_of_ne hjh]
      -- the head walks up one cover at a time
  refine ((runs_wireP (guessFam h) guessWire hfam hloc .reset).mono ?_ ?_)
  · rintro x b y ⟨u, hw, b', hR, hwire⟩
    -- every exit comes from the loop, where the head has only moved
    have hinv : ∀ u : GuessNode × (Fin K → A),
        Relation.ReflTransGen (wireStep (guessRel (A := A) h m) guessWire)
          ((.reset : GuessNode), x) u →
        u = ((.reset : GuessNode), x) ∨ ∀ j : Fin K, (j : ℕ) < m → j ≠ h → u.2 j = x j := by
      intro u hu
      induction hu with
      | refl => exact Or.inl rfl
      | @tail p q hp hpq ih =>
        obtain ⟨b₁, hR₁, hw₁⟩ := hpq
        rcases ih with rfl | hpk
        · obtain ⟨-, hmv⟩ : b₁ = true ∧
              ∀ j : Fin K, (j : ℕ) < m → (setHead h (.toMin) j).Holds x j (q.2 j) := hR₁
          refine Or.inr fun j hj hjh => ?_
          have hx := hmv j hj
          simp only [setHead_of_ne _ hjh] at hx
          exact hx
        · rcases hpr' : p.1 with _ | _
          · rw [hpr'] at hR₁
            obtain ⟨-, hmv⟩ : b₁ = true ∧
                ∀ j : Fin K, (j : ℕ) < m → (setHead h (.toMin) j).Holds p.2 j (q.2 j) := hR₁
            refine Or.inr fun j hj hjh => ?_
            have hx := hmv j hj
            simp only [setHead_of_ne _ hjh] at hx
            exact hx.trans (hpk j hj hjh)
          · rw [hpr'] at hR₁
            rcases hR₁ with ⟨-, -, hk⟩ | ⟨-, hag⟩
            · exact Or.inr fun j hj hjh => (hk j hj hjh).trans (hpk j hj hjh)
            · exact Or.inr fun j hj hjh => (hag j hj).symm.trans (hpk j hj hjh)
    have hb : b = true := by
      rcases hu1 : u.1 with _ | _
      · rw [hu1] at hwire
        exact absurd hwire (by cases b' <;> simp [guessWire])
      · rw [hu1] at hwire
        cases b' with
        | true => exact absurd hwire (by simp [guessWire])
        | false => simpa [guessWire] using hwire.symm
    refine ⟨hb, fun j hj hjh => ?_⟩
    rcases hinv u hw with hu1 | hkeep
    · rw [congrArg Prod.fst hu1] at hwire
      exact absurd hwire (by cases b' <;> simp [guessWire])
    · rcases hu1 : u.1 with _ | _
      · rw [hu1] at hwire
        exact absurd hwire (by cases b' <;> simp [guessWire])
      · rw [hu1] at hR
        rcases hR with ⟨-, -, hk⟩ | ⟨-, hag⟩
        · exact (hk j hj hjh).trans (hkeep j hj hjh)
        · exact (hag j hj).symm.trans (hkeep j hj hjh)
  · rintro x b y ⟨rfl, hkeep⟩
    -- the head can be walked to `y h`, the others staying put
    obtain ⟨mn, hmn⟩ : ∃ mn : A, ∀ a : A, mn ≤ a := by
      have := Fintype.ofFinite A
      have hune : (Finset.univ : Finset A).Nonempty := ⟨x h, Finset.mem_univ _⟩
      exact ⟨Finset.univ.min' hune, fun a => Finset.min'_le _ a (Finset.mem_univ a)⟩
    refine ⟨Function.update x h (y h), fun j hj => ?_, ((.loop : GuessNode),
      Function.update x h (y h)), ?_, false, Or.inr ⟨rfl, HeadAgree.refl _⟩, rfl⟩
    · by_cases hjh : j = h
      · rw [hjh, Function.update_self]
      · rw [Function.update_of_ne hjh]
        exact hkeep j hj hjh
    · refine Relation.ReflTransGen.head (b := ((.loop : GuessNode), Function.update x h mn))
        ⟨true, ⟨rfl, fun j hj => ?_⟩, rfl⟩ ?_
      · by_cases hjh : j = h
        · rw [hjh, setHead_self]
          simp only [Function.update_self]
          exact hmn
        · rw [setHead_of_ne _ hjh]
          change Function.update x h mn j = x j
          rw [Function.update_of_ne hjh]
      · have := hwalk (Function.update x h mn) (y h) (by rw [Function.update_self]; exact hmn _)
        rwa [Function.update_idem] at this

end Guess

/-! ### Guessing a block of heads -/

theorem runs_exitP_local {A : Type} [L.Structure A] [LinearOrder A] (b : Bool) (m : ℕ) :
    (exitP (L := L) (K := K) b).Runs A m fun x b' y => b' = b ∧ HeadAgree m x y :=
  (runs_exitP b).mono (fun x b' y hxy => ⟨hxy.1, fun j _ => by rw [hxy.2]⟩)
    fun x b' y hxy => ⟨x, hxy.2.symm, hxy.1, rfl⟩

theorem headLocal2_exitP {A : Type} (b : Bool) (m : ℕ) :
    HeadLocal2 m fun (x : Fin K → A) b' y => b' = b ∧ HeadAgree m x y := by
  intro x x' y y' hx hy b'
  exact and_congr Iff.rfl ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩

/-- **Guessing several heads**: the heads `hd lo, …, hd (lo + n - 1)`, in turn. -/
def guessManyP (hd : ℕ → Fin K) (lo : ℕ) : ℕ → HeadProgram L K
  | 0 => exitP true
  | n + 1 => iteP (guessP (hd (lo + n))) (guessManyP hd lo n) (exitP false)

section GuessMany

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- **What guessing a block runs**: the heads of the block may end anywhere, and
no other head moves. -/
theorem runs_guessManyP (hd : ℕ → Fin K) (m : ℕ) (hhd : ∀ i : ℕ, i < m → (hd i : ℕ) = i)
    (lo : ℕ) : ∀ n : ℕ, lo + n ≤ m →
      (guessManyP (L := L) hd lo n).Runs A m fun x b y => b = true ∧
        ∀ j : Fin K, (j : ℕ) < m → ((j : ℕ) < lo ∨ lo + n ≤ (j : ℕ)) → y j = x j := by
  intro n
  induction n with
  | zero =>
    intro _
    refine (runs_exitP_local true m).mono
      (fun x b y hxy => ⟨hxy.1, fun j hjm _ => (hxy.2 j hjm).symm⟩) ?_
    rintro x b y ⟨rfl, hk⟩
    exact ⟨y, HeadAgree.refl y, rfl, fun j hj => (hk j hj (by omega)).symm⟩
  | succ n ih =>
    intro hle
    have hlt : lo + n < m := by omega
    have hdlt : (hd (lo + n) : ℕ) < m := by rw [hhd _ hlt]; exact hlt
    refine (runs_iteP (runs_guessP (hd (lo + n)) hdlt) (ih (by omega)) (runs_exitP_local false m)
      ?_ ?_ (headLocal2_exitP false m)).mono ?_ ?_
    · intro x x' y y' hx hy b
      exact and_congr Iff.rfl (forall_congr' fun j => imp_congr_right fun hj =>
        imp_congr_right fun _ => by rw [← hy j hj, ← hx j hj])
    · intro x x' y y' hx hy b
      exact and_congr Iff.rfl (forall_congr' fun j => imp_congr_right fun hj =>
        imp_congr_right fun _ => by rw [← hy j hj, ← hx j hj])
    · rintro x b z ⟨y, ⟨⟨-, hy⟩, hb, hz⟩ | ⟨⟨hcon, -⟩, -⟩⟩
      · refine ⟨hb, fun j hj hjor => ?_⟩
        refine (hz j hj ?_).trans (hy j hj fun hje => ?_)
        · rcases hjor with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by omega)
        · rcases hjor with h1 | h2
          · rw [hje, hhd _ hlt] at h1
            omega
          · rw [hje, hhd _ hlt] at h2
            omega
      · exact absurd hcon (by simp)
    · rintro x b z ⟨rfl, hk⟩
      refine ⟨z, HeadAgree.refl z, fun j => if (j : ℕ) = lo + n then z j else x j, Or.inl ?_⟩
      constructor
      · refine ⟨rfl, fun j hj hjne => ?_⟩
        have hjv : (j : ℕ) ≠ lo + n := fun he => hjne (Fin.ext (by rw [he, hhd _ hlt]))
        change (if (j : ℕ) = lo + n then z j else x j) = x j
        rw [if_neg hjv]
      · refine ⟨rfl, fun j hj hjor => ?_⟩
        change z j = if (j : ℕ) = lo + n then z j else x j
        by_cases hjv : (j : ℕ) = lo + n
        · rw [if_pos hjv]
        · rw [if_neg hjv]
          exact hk j hj (by omega)

end GuessMany

/-! ### The control graph of the machine -/

/-- The control nodes of the machine simulating a specification: which mode the
walk is in, and what it is doing. `r` is the number of modes, and the `Fin
(r + 1)` indices walk the list of modes, one free choice at a time. -/
inductive DrvNode (M : Type) (r : ℕ)
  /-- Choosing which mode to start the walk in. -/
  | pickSrc (i : Fin (r + 1)) : DrvNode M r
  /-- Guessing a starting tuple and testing the source formula. -/
  | trySrc (m : M) : DrvNode M r
  /-- Testing the target formula at the current node. -/
  | target (m : M) : DrvNode M r
  /-- Choosing which mode to step into. -/
  | pickCand (m : M) (i : Fin (r + 1)) : DrvNode M r
  /-- Guessing the next tuple and testing the transition formula. -/
  | tryCand (m m' : M) : DrvNode M r
  /-- Copying the guessed tuple onto the current one. -/
  | commit (m m' : M) : DrvNode M r
  /-- Nothing more to do. -/
  | dead : DrvNode M r

instance {M : Type} [Finite M] {r : ℕ} : Finite (DrvNode M r) := by
  refine Finite.of_injective (fun c : DrvNode M r => match c with
      | .pickSrc i => Sum.inl (Sum.inl i)
      | .trySrc m => Sum.inl (Sum.inr (Sum.inl m))
      | .target m => Sum.inl (Sum.inr (Sum.inr m))
      | .pickCand m i => Sum.inr (Sum.inl (m, i))
      | .tryCand m m' => Sum.inr (Sum.inr (Sum.inl (m, m')))
      | .commit m m' => Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, m'))))
      | .dead => Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) :
    DrvNode M r → (Fin (r + 1) ⊕ M ⊕ M) ⊕ (M × Fin (r + 1)) ⊕ (M × M) ⊕ (M × M) ⊕ Unit) ?_
  rintro (_ | _ | _ | _ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _) h <;> simp_all

/-- Where the machine goes when a fragment exits. -/
def drvWire {M : Type} {r : ℕ} (modeAt : Fin (r + 1) → Option M)
    (nextIx : Fin (r + 1) → Fin (r + 1)) (i₀ : Fin (r + 1)) :
    DrvNode M r → Bool → DrvNode M r ⊕ Bool
  | .pickSrc i, true => Sum.inl ((modeAt i).elim .dead .trySrc)
  | .pickSrc i, false => Sum.inl (.pickSrc (nextIx i))
  | .trySrc m, true => Sum.inl (.target m)
  | .trySrc _, false => Sum.inl .dead
  | .target _, true => Sum.inr true
  | .target m, false => Sum.inl (.pickCand m i₀)
  | .pickCand m i, true => Sum.inl ((modeAt i).elim .dead (.tryCand m))
  | .pickCand m i, false => Sum.inl (.pickCand m (nextIx i))
  | .tryCand m m', true => Sum.inl (.commit m m')
  | .tryCand _ _, false => Sum.inl .dead
  | .commit _ m', _ => Sum.inl (.target m')
  | .dead, _ => Sum.inr false

end HeadProgram

/-! ### The machine of a specification -/

open HeadProgram

section Capture

variable (spec : TCSpec L)

open Classical in
/-- **The quantifier budget of a specification**: the largest number of extra
heads the evaluation of one of its formulas needs. -/
noncomputable def specDepth : ℕ :=
  letI := Fintype.ofFinite spec.Mode
  max (Finset.univ.sup fun p : spec.Mode × spec.Mode => qdepth (spec.step p.1 p.2))
    (max (Finset.univ.sup fun m => qdepth (spec.src m))
      (Finset.univ.sup fun m => qdepth (spec.tgt m)))

/-- **How many heads the machine of a specification has**: two tuples, the
evaluator's workspace, and a spare one so that there is always a head. -/
noncomputable def specHeads : ℕ := 2 * spec.k + specDepth spec + 1

theorem two_k_lt_specHeads : 2 * spec.k < specHeads spec := by
  rw [specHeads]
  omega

/-- The heads holding the current tuple. -/
noncomputable def blk0 (i : Fin spec.k) : Fin (specHeads spec) :=
  ⟨i, lt_of_lt_of_le (lt_of_lt_of_le i.isLt (by omega)) (le_of_lt (two_k_lt_specHeads spec))⟩

/-- The heads holding the candidate tuple. -/
noncomputable def blk1 (i : Fin spec.k) : Fin (specHeads spec) :=
  ⟨spec.k + i, lt_of_lt_of_le (by omega) (le_of_lt (two_k_lt_specHeads spec))⟩

/-- The head at a given index, for the evaluator's workspace. -/
noncomputable def shd (i : ℕ) : Fin (specHeads spec) :=
  if h : i < specHeads spec then ⟨i, h⟩ else ⟨0, lt_of_le_of_lt (Nat.zero_le _)
    (two_k_lt_specHeads spec)⟩

theorem shd_val {i : ℕ} (h : i < specHeads spec) : (shd spec i : ℕ) = i := by
  rw [shd, dif_pos h]

@[simp]
theorem blk0_val (i : Fin spec.k) : (blk0 spec i : ℕ) = i := rfl

@[simp]
theorem blk1_val (i : Fin spec.k) : (blk1 spec i : ℕ) = spec.k + i := rfl

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The node of the specification the machine is at: its mode, and the tuple on
the first block of heads. -/
noncomputable def curNode (x : Fin (specHeads spec) → A) (m : spec.Mode) : spec.Node A :=
  (m, fun i => x (blk0 spec i))

/-- The node the machine is considering stepping into: the tuple on the second
block of heads. -/
noncomputable def candNode (x : Fin (specHeads spec) → A) (m : spec.Mode) : spec.Node A :=
  (m, fun i => x (blk1 spec i))

end Capture

/-! ### The fragments -/

section Fragments

variable (spec : TCSpec L)

open Classical in
theorem qdepth_src_le (m : spec.Mode) : qdepth (spec.src m) ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun m => qdepth (spec.src m)) (Finset.mem_univ m))
    (le_trans (le_max_left _ _) (le_max_right _ _))

open Classical in
theorem qdepth_tgt_le (m : spec.Mode) : qdepth (spec.tgt m) ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun m => qdepth (spec.tgt m)) (Finset.mem_univ m))
    (le_trans (le_max_right _ _) (le_max_right _ _))

open Classical in
theorem qdepth_step_le (m m' : spec.Mode) : qdepth (spec.step m m') ≤ specDepth spec := by
  let := Fintype.ofFinite spec.Mode
  exact le_trans (Finset.le_sup (f := fun p : spec.Mode × spec.Mode => qdepth (spec.step p.1 p.2))
    (Finset.mem_univ (m, m'))) (le_max_left _ _)

/-- The variables of a formula about the current tuple live in the first block
of heads. -/
noncomputable def hv0 : Fin spec.k ⊕ Fin 0 → Fin (specHeads spec) :=
  Sum.elim (blk0 spec) Fin.elim0

/-- The variables of a transition formula live in the two blocks of heads. -/
noncomputable def hv01 : (Fin spec.k ⊕ Fin spec.k) ⊕ Fin 0 → Fin (specHeads spec) :=
  Sum.elim (Sum.elim (blk0 spec) (blk1 spec)) Fin.elim0

theorem hv0_low : ∀ v, ((hv0 spec v : Fin (specHeads spec)) : ℕ) < 2 * spec.k := by
  rintro (i | i)
  · exact lt_of_lt_of_le i.isLt (by omega)
  · exact i.elim0

theorem hv01_low : ∀ v, ((hv01 spec v : Fin (specHeads spec)) : ℕ) < 2 * spec.k := by
  rintro ((i | i) | i)
  · exact lt_of_lt_of_le i.isLt (by omega)
  · have := i.isLt
    simp only [hv01, Sum.elim_inl, Sum.elim_inr, blk1_val]
    omega
  · exact i.elim0

/-- The evaluator for a source formula. -/
noncomputable def evalSrcP (m : spec.Mode) : HeadProgram L (specHeads spec) :=
  evalP (shd spec) (2 * spec.k) (hv0 spec) (spec.src m)

/-- The evaluator for a target formula. -/
noncomputable def evalTgtP (m : spec.Mode) : HeadProgram L (specHeads spec) :=
  evalP (shd spec) (2 * spec.k) (hv0 spec) (spec.tgt m)

/-- The evaluator for a transition formula. -/
noncomputable def evalStepP (m m' : spec.Mode) : HeadProgram L (specHeads spec) :=
  evalP (shd spec) (2 * spec.k) (hv01 spec) (spec.step m m')

/-- The moves that copy the candidate tuple onto the current one. -/
noncomputable def commitMoves : Fin (specHeads spec) → HeadMove (specHeads spec) :=
  fun j => if h : (j : ℕ) < spec.k then .copy (blk1 spec ⟨j, h⟩) else .stay

section Eval

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

theorem hshd : ∀ i : ℕ, i < specHeads spec → ((shd spec i : Fin (specHeads spec)) : ℕ) = i :=
  fun _ h => shd_val spec h

theorem decides_evalSrcP (m : spec.Mode) :
    (evalSrcP spec m).Decides A (2 * spec.k) fun x => spec.IsSrc (curNode spec x m) := by
  refine (decides_evalP (shd spec) (hshd spec) (spec.src m) (2 * spec.k) (hv0 spec)
    (hv0_low spec) ?_).congr fun x => ?_
  · have := qdepth_src_le spec m
    rw [specHeads]
    omega
  · exact iff_of_eq (congrArg (BoundedFormula.Realize (spec.src m)
      fun i => x (blk0 spec i)) (funext fun i => i.elim0))

theorem decides_evalTgtP (m : spec.Mode) :
    (evalTgtP spec m).Decides A (2 * spec.k) fun x => spec.IsTgt (curNode spec x m) := by
  refine (decides_evalP (shd spec) (hshd spec) (spec.tgt m) (2 * spec.k) (hv0 spec)
    (hv0_low spec) ?_).congr fun x => ?_
  · have := qdepth_tgt_le spec m
    rw [specHeads]
    omega
  · exact iff_of_eq (congrArg (BoundedFormula.Realize (spec.tgt m)
      fun i => x (blk0 spec i)) (funext fun i => i.elim0))

theorem decides_evalStepP (m m' : spec.Mode) :
    (evalStepP spec m m').Decides A (2 * spec.k) fun x =>
      spec.Step (curNode spec x m) (candNode spec x m') := by
  refine (decides_evalP (shd spec) (hshd spec) (spec.step m m') (2 * spec.k) (hv01 spec)
    (hv01_low spec) ?_).congr fun x => ?_
  · have := qdepth_step_le spec m m'
    rw [specHeads]
    omega
  · refine iff_of_eq (congrArg₂ (BoundedFormula.Realize (spec.step m m')) ?_
      (funext fun i => i.elim0))
    funext v
    rcases v with i | i <;> rfl

omit [Finite A] in
theorem headLocal_isSrc (m : spec.Mode) :
    HeadLocal (2 * spec.k) fun x : Fin (specHeads spec) → A => spec.IsSrc (curNode spec x m) := by
  intro x y hxy
  refine iff_of_eq (congrArg (fun u => spec.IsSrc (m, u)) (funext fun i => ?_))
  exact hxy _ (lt_of_lt_of_le i.isLt (by omega))

omit [Finite A] in
theorem headLocal_isTgt (m : spec.Mode) :
    HeadLocal (2 * spec.k) fun x : Fin (specHeads spec) → A => spec.IsTgt (curNode spec x m) := by
  intro x y hxy
  refine iff_of_eq (congrArg (fun u => spec.IsTgt (m, u)) (funext fun i => ?_))
  exact hxy _ (lt_of_lt_of_le i.isLt (by omega))

omit [Finite A] in
theorem headLocal_step (m m' : spec.Mode) :
    HeadLocal (2 * spec.k) fun x : Fin (specHeads spec) → A =>
      spec.Step (curNode spec x m) (candNode spec x m') := by
  intro x y hxy
  refine iff_of_eq (congrArg₂ (fun u v => spec.Step (m, u) (m', v)) (funext fun i => ?_)
    (funext fun i => ?_))
  · exact hxy _ (lt_of_lt_of_le i.isLt (by omega))
  · exact hxy _ (by simp only [blk1_val]; omega)

end Eval

end Fragments

/-! ### The machine -/

section Machine

variable (spec : TCSpec L)

/-- The number of modes. -/
noncomputable def modeCard : ℕ := Nat.card spec.Mode

/-- An enumeration of the modes. -/
noncomputable def modeEquiv : spec.Mode ≃ Fin (modeCard spec) := Finite.equivFin spec.Mode

/-- The mode at an index of the enumeration, if any. -/
noncomputable def modeAt (i : Fin (modeCard spec + 1)) : Option spec.Mode :=
  if h : (i : ℕ) < modeCard spec then some ((modeEquiv spec).symm ⟨i, h⟩) else none

/-- The next index of the enumeration; it stops at the last one. -/
noncomputable def nextIx (i : Fin (modeCard spec + 1)) : Fin (modeCard spec + 1) :=
  if h : (i : ℕ) < modeCard spec then ⟨i + 1, by omega⟩ else i

/-- The index the enumeration starts at. -/
noncomputable def ix0 : Fin (modeCard spec + 1) := ⟨0, Nat.succ_pos _⟩

/-- The index of a mode in the enumeration. -/
noncomputable def ixOf (m : spec.Mode) : Fin (modeCard spec + 1) :=
  ⟨modeEquiv spec m, by have := (modeEquiv spec m).isLt; omega⟩

theorem modeAt_ixOf (m : spec.Mode) : modeAt spec (ixOf spec m) = some m := by
  have h : ((ixOf spec m : Fin (modeCard spec + 1)) : ℕ) < modeCard spec := (modeEquiv spec m).isLt
  rw [modeAt, dif_pos h]
  refine congrArg some ?_
  rw [show (⟨((ixOf spec m : Fin (modeCard spec + 1)) : ℕ), h⟩ : Fin (modeCard spec)) =
    modeEquiv spec m from Fin.ext rfl, Equiv.symm_apply_apply]

/-- The fragments of the machine. -/
noncomputable def drvFam : DrvNode spec.Mode (modeCard spec) → HeadProgram L (specHeads spec)
  | .pickSrc _ => chooseP
  | .trySrc m => iteP (guessManyP (shd spec) 0 spec.k) (evalSrcP spec m) (exitP false)
  | .target m => evalTgtP spec m
  | .pickCand _ _ => chooseP
  | .tryCand m m' => iteP (guessManyP (shd spec) spec.k spec.k) (evalStepP spec m m') (exitP false)
  | .commit _ _ => moveP (commitMoves spec)
  | .dead => exitP false

/-- **The machine of a specification**: the loop described in the header, as a
control graph over those fragments. -/
noncomputable def drvP : HeadProgram L (specHeads spec) :=
  wireP (drvFam spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)) (.pickSrc (ix0 spec))

section Runs

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

/-- What the fragments of the machine run. -/
noncomputable def drvRel : DrvNode spec.Mode (modeCard spec) → (Fin (specHeads spec) → A) →
    Bool → (Fin (specHeads spec) → A) → Prop
  | .pickSrc _ => fun x _ y => HeadAgree (2 * spec.k) x y
  | .trySrc m => fun x b y => (b = true ↔ spec.IsSrc (curNode spec y m)) ∧
      ∀ j : Fin (specHeads spec), (j : ℕ) < 2 * spec.k → spec.k ≤ (j : ℕ) → y j = x j
  | .target m => fun x b y => (b = true ↔ spec.IsTgt (curNode spec x m)) ∧
      HeadAgree (2 * spec.k) x y
  | .pickCand _ _ => fun x _ y => HeadAgree (2 * spec.k) x y
  | .tryCand m m' => fun x b y => (b = true ↔ spec.Step (curNode spec y m) (candNode spec y m')) ∧
      ∀ j : Fin (specHeads spec), (j : ℕ) < spec.k → y j = x j
  | .commit _ _ => fun x b y => b = true ∧ (∀ i : Fin spec.k, y (blk0 spec i) = x (blk1 spec i)) ∧
      ∀ j : Fin (specHeads spec), spec.k ≤ (j : ℕ) → (j : ℕ) < 2 * spec.k → y j = x j
  | .dead => fun x b y => b = false ∧ HeadAgree (2 * spec.k) x y

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem curNode_congr {x y : Fin (specHeads spec) → A}
    (h : ∀ j : Fin (specHeads spec), (j : ℕ) < spec.k → y j = x j) (m : spec.Mode) :
    curNode spec y m = curNode spec x m := by
  refine congrArg (fun u => (m, u)) (funext fun i => ?_)
  exact h _ i.isLt

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem candNode_congr {x y : Fin (specHeads spec) → A}
    (h : ∀ j : Fin (specHeads spec), spec.k ≤ (j : ℕ) → (j : ℕ) < 2 * spec.k → y j = x j)
    (m : spec.Mode) : candNode spec y m = candNode spec x m := by
  refine congrArg (fun u => (m, u)) (funext fun i => ?_)
  refine h _ ?_ ?_ <;> (simp only [blk1_val]; have := i.isLt; omega)

theorem hshd' : ∀ i : ℕ, i < 2 * spec.k → ((shd spec i : Fin (specHeads spec)) : ℕ) = i :=
  fun _ hi => shd_val spec (lt_trans hi (two_k_lt_specHeads spec))

/-- **The fragments run what they are meant to.** -/
theorem runs_drvFam (c : DrvNode spec.Mode (modeCard spec)) :
    (drvFam spec c).Runs A (2 * spec.k) (drvRel spec c) := by
  cases c with
  | pickSrc i => exact runs_chooseP
  | trySrc m =>
    refine (runs_iteP (runs_guessManyP (shd spec) (2 * spec.k) (hshd' spec) 0 spec.k (by omega))
      (decides_evalSrcP spec m) (runs_exitP_local false _) ?_
      (headLocal2_decides (headLocal_isSrc spec m)) (headLocal2_exitP false _)).mono ?_ ?_
    · intro x x' y y' hx hy b
      exact and_congr Iff.rfl (forall_congr' fun j => imp_congr_right fun hj =>
        imp_congr_right fun _ => by rw [← hy j hj, ← hx j hj])
    · rintro x b z ⟨y, ⟨⟨-, hy⟩, hz1, hz2⟩ | ⟨⟨hcon, -⟩, -⟩⟩
      · refine ⟨hz1.trans (headLocal_isSrc spec m y z hz2), fun j hj hjk => ?_⟩
        rw [← hz2 j hj]
        exact hy j hj (Or.inr (by omega))
      · exact absurd hcon (by simp)
    · rintro x b z ⟨hb, hkeep⟩
      exact ⟨z, HeadAgree.refl z, z, Or.inl ⟨⟨rfl, fun j hj hor => hkeep j hj (by omega)⟩,
        hb, HeadAgree.refl z⟩⟩
  | target m => exact decides_evalTgtP spec m
  | pickCand m i => exact runs_chooseP
  | tryCand m m' =>
    refine (runs_iteP (runs_guessManyP (shd spec) (2 * spec.k) (hshd' spec) spec.k spec.k
      (by omega)) (decides_evalStepP spec m m') (runs_exitP_local false _) ?_
      (headLocal2_decides (headLocal_step spec m m')) (headLocal2_exitP false _)).mono ?_ ?_
    · intro x x' y y' hx hy b
      exact and_congr Iff.rfl (forall_congr' fun j => imp_congr_right fun hj =>
        imp_congr_right fun _ => by rw [← hy j hj, ← hx j hj])
    · rintro x b z ⟨y, ⟨⟨-, hy⟩, hz1, hz2⟩ | ⟨⟨hcon, -⟩, -⟩⟩
      · refine ⟨hz1.trans (headLocal_step spec m m' y z hz2), fun j hj => ?_⟩
        rw [← hz2 j (by omega)]
        exact hy j (by omega) (Or.inl hj)
      · exact absurd hcon (by simp)
    · rintro x b z ⟨hb, hkeep⟩
      refine ⟨z, HeadAgree.refl z, z, Or.inl ⟨⟨rfl, fun j hj hor => ?_⟩, hb, HeadAgree.refl z⟩⟩
      rcases hor with h1 | h2
      · exact hkeep j h1
      · omega
  | commit m m' =>
    refine (runs_moveP_local (commitMoves spec) (2 * spec.k) fun j hj => ?_).mono ?_ ?_
    · rw [commitMoves, dif_neg (by omega)]
    · rintro x b y ⟨rfl, hmv⟩
      refine ⟨rfl, fun i => ?_, fun j hj1 hj2 => ?_⟩
      · have hx := hmv (blk0 spec i) (lt_of_lt_of_le i.isLt (by omega))
        rw [commitMoves, dif_pos (show ((blk0 spec i : Fin (specHeads spec)) : ℕ) < spec.k from
          i.isLt)] at hx
        rw [hx]
        exact congrArg (fun w => x (blk1 spec w)) (Fin.ext rfl)
      · have hx := hmv j hj2
        rw [commitMoves, dif_neg (by omega)] at hx
        exact hx
    · rintro x b y ⟨rfl, hcopy, hkeep⟩
      refine ⟨y, HeadAgree.refl y, rfl, fun j hj => ?_⟩
      by_cases hjk : (j : ℕ) < spec.k
      · rw [commitMoves, dif_pos hjk]
        have hx := hcopy ⟨j, hjk⟩
        rw [show blk0 spec ⟨j, hjk⟩ = j from Fin.ext rfl] at hx
        exact hx
      · rw [commitMoves, dif_neg hjk]
        exact hkeep j (by omega) hj
  | dead => exact runs_exitP_local false _

omit [Finite A] in
/-- The relations the fragments run see only the two tuples. -/
theorem headLocal2_drvRel (c : DrvNode spec.Mode (modeCard spec)) :
    HeadLocal2 (2 * spec.k) (drvRel (A := A) spec c) := by
  cases c with
  | pickSrc i =>
    exact fun x x' y y' hx hy b =>
      ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩
  | trySrc m =>
    refine fun x x' y y' hx hy b => and_congr ?_ ?_
    · exact iff_congr Iff.rfl (headLocal_isSrc spec m y y' hy)
    · exact forall_congr' fun j => imp_congr_right fun hj => imp_congr_right fun _ =>
        by rw [← hy j hj, ← hx j hj]
  | target m => exact headLocal2_decides (headLocal_isTgt spec m)
  | pickCand m i =>
    exact fun x x' y y' hx hy b =>
      ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩
  | tryCand m m' =>
    refine fun x x' y y' hx hy b => and_congr ?_ ?_
    · exact iff_congr Iff.rfl (headLocal_step spec m m' y y' hy)
    · exact forall_congr' fun j => imp_congr_right fun hj =>
        by rw [← hy j (by omega), ← hx j (by omega)]
  | commit m m' =>
    refine fun x x' y y' hx hy b => and_congr Iff.rfl (and_congr ?_ ?_)
    · exact forall_congr' fun i => by
        rw [← hy _ (lt_of_lt_of_le i.isLt (by omega)),
          ← hx _ (by simp only [blk1_val]; have := i.isLt; omega)]
    · exact forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hj =>
        by rw [← hy j hj, ← hx j hj]
  | dead =>
    exact fun x x' y y' hx hy b => and_congr Iff.rfl
      ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩

/-! ### Soundness: what the machine knows -/

/-- The invariant the machine carries: at a control node, the tuple on the first
block of heads is a node of the specification reachable from a source – and, at
`commit`, the candidate is a step away. -/
def drvInv (u : DrvNode spec.Mode (modeCard spec) × (Fin (specHeads spec) → A)) : Prop :=
  match u.1 with
  | .pickSrc _ => True
  | .trySrc _ => True
  | .target m => ∃ u₀, spec.IsSrc u₀ ∧ spec.Reach u₀ (curNode spec u.2 m)
  | .pickCand m _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.Reach u₀ (curNode spec u.2 m)
  | .tryCand m _ => ∃ u₀, spec.IsSrc u₀ ∧ spec.Reach u₀ (curNode spec u.2 m)
  | .commit m m' => ∃ u₀, spec.IsSrc u₀ ∧ spec.Reach u₀ (curNode spec u.2 m) ∧
      spec.Step (curNode spec u.2 m) (candNode spec u.2 m')
  | .dead => True

/-! The wiring, arc by arc. -/

section Arcs

variable (i : Fin (modeCard spec + 1)) (m m' : spec.Mode) (b : Bool)

@[simp]
theorem drvWire_pickSrc_true : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.pickSrc i) true =
    Sum.inl ((modeAt spec i).elim .dead .trySrc) := rfl

@[simp]
theorem drvWire_pickSrc_false : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.pickSrc i) false =
    Sum.inl (.pickSrc (nextIx spec i)) := rfl

@[simp]
theorem drvWire_trySrc_true : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.trySrc m) true =
    Sum.inl (.target m) := rfl

@[simp]
theorem drvWire_trySrc_false : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.trySrc m) false =
    Sum.inl .dead := rfl

@[simp]
theorem drvWire_target_true : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.target m) true =
    Sum.inr true := rfl

@[simp]
theorem drvWire_target_false : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.target m) false =
    Sum.inl (.pickCand m (ix0 spec)) := rfl

@[simp]
theorem drvWire_pickCand_true :
    drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.pickCand m i) true =
      Sum.inl ((modeAt spec i).elim .dead (.tryCand m)) := rfl

@[simp]
theorem drvWire_pickCand_false :
    drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.pickCand m i) false =
      Sum.inl (.pickCand m (nextIx spec i)) := rfl

@[simp]
theorem drvWire_tryCand_true :
    drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.tryCand m m') true =
      Sum.inl (.commit m m') := rfl

@[simp]
theorem drvWire_tryCand_false :
    drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.tryCand m m') false = Sum.inl .dead := rfl

@[simp]
theorem drvWire_commit : drvWire (modeAt spec) (nextIx spec) (ix0 spec) (.commit m m') b =
    Sum.inl (.target m') := by
  cases b <;> rfl

@[simp]
theorem drvWire_dead : drvWire (modeAt spec) (nextIx spec) (ix0 spec) .dead b = Sum.inr false := by
  cases b <;> rfl

end Arcs

omit [Finite A] in
/-- **The invariant is carried along the machine's walk.** -/
theorem drvInv_of_walk (x₀ : Fin (specHeads spec) → A)
    {u : DrvNode spec.Mode (modeCard spec) × (Fin (specHeads spec) → A)}
    (h : Relation.ReflTransGen
      (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
      ((.pickSrc (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x₀) u) : drvInv spec u := by
  induction h with
  | refl => trivial
  | @tail p q hp hpq ih =>
    obtain ⟨b, hR, hw⟩ := hpq
    cases hp1 : p.1 with
    | pickSrc i =>
      rw [hp1] at hw
      cases b with
      | true =>
        rw [drvWire_pickSrc_true] at hw
        cases hmi : modeAt spec i with
        | none =>
          rw [hmi] at hw
          have : q.1 = DrvNode.dead := (Sum.inl.inj hw).symm
          simp only [drvInv, this]
        | some m =>
          rw [hmi] at hw
          have : q.1 = DrvNode.trySrc m := (Sum.inl.inj hw).symm
          simp only [drvInv, this]
      | false =>
        have : q.1 = DrvNode.pickSrc (nextIx spec i) := (Sum.inl.inj hw).symm
        simp only [drvInv, this]
    | trySrc m =>
      rw [hp1] at hw hR
      cases b with
      | true =>
        have hq : q.1 = DrvNode.target m := (Sum.inl.inj hw).symm
        obtain ⟨hb, -⟩ : (true = true ↔ spec.IsSrc (curNode spec q.2 m)) ∧
          ∀ j : Fin (specHeads spec), (j : ℕ) < 2 * spec.k → spec.k ≤ (j : ℕ) →
            q.2 j = p.2 j := hR
        simp only [drvInv, hq]
        exact ⟨curNode spec q.2 m, hb.mp rfl, Relation.ReflTransGen.refl⟩
      | false =>
        have : q.1 = DrvNode.dead := (Sum.inl.inj hw).symm
        simp only [drvInv, this]
    | target m =>
      rw [hp1] at hw hR
      simp only [drvInv, hp1] at ih
      cases b with
      | true => exact absurd hw (by simp)
      | false =>
        have hq : q.1 = DrvNode.pickCand m (ix0 spec) := (Sum.inl.inj hw).symm
        obtain ⟨-, hag⟩ : (false = true ↔ spec.IsTgt (curNode spec p.2 m)) ∧
          HeadAgree (2 * spec.k) p.2 q.2 := hR
        simp only [drvInv, hq]
        rw [curNode_congr spec (fun j hj => (hag j (by omega)).symm) m]
        exact ih
    | pickCand m i =>
      rw [hp1] at hw hR
      simp only [drvInv, hp1] at ih
      have hag : HeadAgree (2 * spec.k) p.2 q.2 := hR
      have hnode : curNode spec q.2 m = curNode spec p.2 m :=
        curNode_congr spec (fun j hj => (hag j (by omega)).symm) m
      cases b with
      | true =>
        rw [drvWire_pickCand_true] at hw
        cases hmi : modeAt spec i with
        | none =>
          rw [hmi] at hw
          have : q.1 = DrvNode.dead := (Sum.inl.inj hw).symm
          simp only [drvInv, this]
        | some m' =>
          rw [hmi] at hw
          have hq : q.1 = DrvNode.tryCand m m' := (Sum.inl.inj hw).symm
          simp only [drvInv, hq]
          rw [hnode]
          exact ih
      | false =>
        have hq : q.1 = DrvNode.pickCand m (nextIx spec i) := (Sum.inl.inj hw).symm
        simp only [drvInv, hq]
        rw [hnode]
        exact ih
    | tryCand m m' =>
      rw [hp1] at hw hR
      simp only [drvInv, hp1] at ih
      cases b with
      | true =>
        have hq : q.1 = DrvNode.commit m m' := (Sum.inl.inj hw).symm
        obtain ⟨hb, hkeep⟩ : (true = true ↔
            spec.Step (curNode spec q.2 m) (candNode spec q.2 m')) ∧
          ∀ j : Fin (specHeads spec), (j : ℕ) < spec.k → q.2 j = p.2 j := hR
        simp only [drvInv, hq]
        obtain ⟨u₀, hu₀, hreach⟩ := ih
        exact ⟨u₀, hu₀, by rw [curNode_congr spec hkeep m]; exact hreach, hb.mp rfl⟩
      | false =>
        have : q.1 = DrvNode.dead := (Sum.inl.inj hw).symm
        simp only [drvInv, this]
    | commit m m' =>
      rw [hp1] at hw hR
      simp only [drvInv, hp1] at ih
      have hq : q.1 = DrvNode.target m' := (Sum.inl.inj hw).symm
      obtain ⟨-, hcopy, -⟩ : b = true ∧ (∀ i : Fin spec.k, q.2 (blk0 spec i) = p.2 (blk1 spec i)) ∧
        ∀ j : Fin (specHeads spec), spec.k ≤ (j : ℕ) → (j : ℕ) < 2 * spec.k →
          q.2 j = p.2 j := hR
      obtain ⟨u₀, hu₀, hreach, hstep⟩ := ih
      simp only [drvInv, hq]
      refine ⟨u₀, hu₀, ?_⟩
      have hnode : curNode spec q.2 m' = candNode spec p.2 m' :=
        congrArg (fun w => (m', w)) (funext fun i => hcopy i)
      rw [hnode]
      exact hreach.tail hstep
    | dead =>
      rw [hp1] at hw
      exact absurd hw (by cases b <;> simp)

omit [Finite A] in
/-- **Soundness**: if the machine accepts, the specification does. -/
theorem accepts_of_exit (x₀ : Fin (specHeads spec) → A)
    {u : DrvNode spec.Mode (modeCard spec) × (Fin (specHeads spec) → A)}
    {z : Fin (specHeads spec) → A}
    (hwalk : Relation.ReflTransGen
      (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
      ((.pickSrc (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x₀) u)
    (hexit : wireExit (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)) u true z) :
    spec.Accepts A := by
  obtain ⟨b, hR, hw⟩ := hexit
  have hinv := drvInv_of_walk spec x₀ hwalk
  cases hu1 : u.1 with
  | pickSrc i =>
    rw [hu1] at hw
    cases b <;> exact absurd hw (by cases hmi : modeAt spec i <;> simp [hmi])
  | trySrc m =>
    rw [hu1] at hw
    exact absurd hw (by cases b <;> simp)
  | target m =>
    rw [hu1] at hw hR
    simp only [drvInv, hu1] at hinv
    obtain ⟨u₀, hu₀, hreach⟩ := hinv
    cases b with
    | false => exact absurd hw (by simp)
    | true =>
      obtain ⟨hb, -⟩ : (true = true ↔ spec.IsTgt (curNode spec u.2 m)) ∧
        HeadAgree (2 * spec.k) u.2 z := hR
      exact ⟨u₀, curNode spec u.2 m, hu₀, hb.mp rfl, hreach⟩
  | pickCand m i =>
    rw [hu1] at hw
    cases b <;> exact absurd hw (by cases hmi : modeAt spec i <;> simp [hmi])
  | tryCand m m' =>
    rw [hu1] at hw
    exact absurd hw (by cases b <;> simp)
  | commit m m' =>
    rw [hu1] at hw
    exact absurd hw (by cases b <;> simp)
  | dead =>
    rw [hu1] at hw
    exact absurd hw (by cases b <;> simp)

/-! ### Completeness: the machine imitates the walk -/

/-- Putting a tuple on the first block of heads. -/
noncomputable def putBlk0 (x : Fin (specHeads spec) → A) (u : Fin spec.k → A) :
    Fin (specHeads spec) → A :=
  fun j => if h : (j : ℕ) < spec.k then u ⟨j, h⟩ else x j

/-- Putting a tuple on the second block of heads. -/
noncomputable def putBlk1 (x : Fin (specHeads spec) → A) (u : Fin spec.k → A) :
    Fin (specHeads spec) → A :=
  fun j => if h : spec.k ≤ (j : ℕ) ∧ (j : ℕ) < 2 * spec.k then u ⟨(j : ℕ) - spec.k, by omega⟩
    else x j

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem putBlk0_blk0 (x : Fin (specHeads spec) → A) (u : Fin spec.k → A) (i : Fin spec.k) :
    putBlk0 spec x u (blk0 spec i) = u i := by
  rw [putBlk0, dif_pos (show ((blk0 spec i : Fin (specHeads spec)) : ℕ) < spec.k from i.isLt)]
  exact congrArg u (Fin.ext rfl)

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem putBlk0_of_le (x : Fin (specHeads spec) → A) (u : Fin spec.k → A)
    {j : Fin (specHeads spec)} (hj : spec.k ≤ (j : ℕ)) : putBlk0 spec x u j = x j := by
  rw [putBlk0, dif_neg (by omega)]

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem putBlk1_blk1 (x : Fin (specHeads spec) → A) (u : Fin spec.k → A) (i : Fin spec.k) :
    putBlk1 spec x u (blk1 spec i) = u i := by
  rw [putBlk1, dif_pos (show spec.k ≤ ((blk1 spec i : Fin (specHeads spec)) : ℕ) ∧
    ((blk1 spec i : Fin (specHeads spec)) : ℕ) < 2 * spec.k from
      ⟨by simp only [blk1_val]; omega, by simp only [blk1_val]; have := i.isLt; omega⟩)]
  exact congrArg u (Fin.ext (by simp only [blk1_val]; omega))

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem putBlk1_of_lt (x : Fin (specHeads spec) → A) (u : Fin spec.k → A)
    {j : Fin (specHeads spec)} (hj : (j : ℕ) < spec.k) : putBlk1 spec x u j = x j := by
  rw [putBlk1, dif_neg (by omega)]

omit [Finite A] in
/-- The chain of free choices reaches every mode. -/
theorem walk_pickSrc (x : Fin (specHeads spec) → A) :
    ∀ (n : ℕ) (hn : n < modeCard spec + 1), Relation.ReflTransGen
      (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
      ((.pickSrc (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x)
      ((.pickSrc ⟨n, hn⟩ : DrvNode spec.Mode (modeCard spec)), x) := by
  intro n
  induction n with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro hn
    refine (ih (by omega)).tail ⟨false, HeadAgree.refl x, ?_⟩
    rw [drvWire_pickSrc_false]
    refine congrArg Sum.inl (congrArg DrvNode.pickSrc ?_)
    rw [nextIx, dif_pos (show ((⟨n, by omega⟩ : Fin (modeCard spec + 1)) : ℕ) < modeCard spec
      from show n < modeCard spec by omega)]

omit [Finite A] in
/-- The same chain, for the candidate mode. -/
theorem walk_pickCand (x : Fin (specHeads spec) → A) (m : spec.Mode) :
    ∀ (n : ℕ) (hn : n < modeCard spec + 1), Relation.ReflTransGen
      (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
      ((.pickCand m (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x)
      ((.pickCand m ⟨n, hn⟩ : DrvNode spec.Mode (modeCard spec)), x) := by
  intro n
  induction n with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro hn
    refine (ih (by omega)).tail ⟨false, HeadAgree.refl x, ?_⟩
    rw [drvWire_pickCand_false]
    refine congrArg Sum.inl (congrArg (DrvNode.pickCand m) ?_)
    rw [nextIx, dif_pos (show ((⟨n, by omega⟩ : Fin (modeCard spec + 1)) : ℕ) < modeCard spec
      from show n < modeCard spec by omega)]

omit [Finite A] in
/-- **Completeness**: the machine imitates the specification's walk, node by
node, unless it has already accepted on the way. -/
theorem walk_of_reach (x₀ : Fin (specHeads spec) → A) {u₀ : spec.Node A} (hsrc : spec.IsSrc u₀) :
    ∀ w : spec.Node A, spec.Reach u₀ w →
      (∃ (u : DrvNode spec.Mode (modeCard spec) × (Fin (specHeads spec) → A))
          (z : Fin (specHeads spec) → A), Relation.ReflTransGen
            (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
            ((.pickSrc (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x₀) u ∧
          wireExit (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)) u true z) ∨
        ∃ x : Fin (specHeads spec) → A, curNode spec x w.1 = w ∧ Relation.ReflTransGen
          (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
          ((.pickSrc (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x₀)
          ((.target w.1 : DrvNode spec.Mode (modeCard spec)), x) := by
  intro w hw
  induction hw with
  | refl =>
    refine Or.inr ⟨putBlk0 spec x₀ u₀.2, ?_, ?_⟩
    · exact congrArg (fun v => (u₀.1, v)) (funext fun i => putBlk0_blk0 spec x₀ u₀.2 i)
    · have hchain := walk_pickSrc spec x₀ (modeEquiv spec u₀.1) (by
        have := (modeEquiv spec u₀.1).isLt; omega)
      have hcur : curNode spec (putBlk0 spec x₀ u₀.2) u₀.1 = u₀ :=
        congrArg (fun v => (u₀.1, v)) (funext fun i => putBlk0_blk0 spec x₀ u₀.2 i)
      have hstep1 : wireStep (drvRel spec)
          (drvWire (modeAt spec) (nextIx spec) (ix0 spec))
          ((.pickSrc ⟨(modeEquiv spec u₀.1 : ℕ), by
            have := (modeEquiv spec u₀.1).isLt; omega⟩ :
              DrvNode spec.Mode (modeCard spec)), x₀)
          ((.trySrc u₀.1 : DrvNode spec.Mode (modeCard spec)), x₀) := by
        refine ⟨true, HeadAgree.refl x₀, ?_⟩
        rw [drvWire_pickSrc_true]
        refine congrArg Sum.inl ?_
        rw [show (⟨(modeEquiv spec u₀.1 : ℕ), by have := (modeEquiv spec u₀.1).isLt; omega⟩ :
          Fin (modeCard spec + 1)) = ixOf spec u₀.1 from rfl, modeAt_ixOf]
        rfl
      have hstep2 : wireStep (drvRel spec)
          (drvWire (modeAt spec) (nextIx spec) (ix0 spec))
          ((.trySrc u₀.1 : DrvNode spec.Mode (modeCard spec)), x₀)
          ((.target u₀.1 : DrvNode spec.Mode (modeCard spec)), putBlk0 spec x₀ u₀.2) := by
        refine ⟨true, ⟨⟨fun _ => ?_, fun _ => rfl⟩,
          fun j _ hj => putBlk0_of_le spec x₀ u₀.2 hj⟩, ?_⟩
        · rw [hcur]
          exact hsrc
        · rw [drvWire_trySrc_true]
      exact (hchain.tail hstep1).tail hstep2
  | @tail w w' hww hstep ih =>
    rcases ih with hacc | ⟨x, hx, hwalk⟩
    · exact Or.inl hacc
    · by_cases htgt : spec.IsTgt w
      · refine Or.inl ⟨((.target w.1 : DrvNode spec.Mode (modeCard spec)), x), x, hwalk,
          true, ⟨?_, HeadAgree.refl x⟩, ?_⟩
        · exact ⟨fun _ => by rw [hx]; exact htgt, fun _ => rfl⟩
        · rw [drvWire_target_true]
      · refine Or.inr ⟨putBlk0 spec (putBlk1 spec x w'.2) w'.2, ?_, ?_⟩
        · exact congrArg (fun v => (w'.1, v)) (funext fun i =>
            putBlk0_blk0 spec (putBlk1 spec x w'.2) w'.2 i)
        · have hstep1 : Relation.ReflTransGen
              (wireStep (drvRel spec) (drvWire (modeAt spec) (nextIx spec) (ix0 spec)))
              ((.target w.1 : DrvNode spec.Mode (modeCard spec)), x)
              ((.pickCand w.1 (ix0 spec) : DrvNode spec.Mode (modeCard spec)), x) := by
            refine Relation.ReflTransGen.single ⟨false, ⟨?_, HeadAgree.refl x⟩, ?_⟩
            · simp only [Bool.false_eq_true, false_iff]
              rw [hx]
              exact htgt
            · rw [drvWire_target_false]
          have hchain := walk_pickCand spec x w.1 (modeEquiv spec w'.1) (by
            have := (modeEquiv spec w'.1).isLt; omega)
          have hstep2 : wireStep (drvRel spec)
              (drvWire (modeAt spec) (nextIx spec) (ix0 spec))
              ((.pickCand w.1 ⟨(modeEquiv spec w'.1 : ℕ), by
                have := (modeEquiv spec w'.1).isLt; omega⟩ :
                  DrvNode spec.Mode (modeCard spec)), x)
              ((.tryCand w.1 w'.1 : DrvNode spec.Mode (modeCard spec)), x) := by
            refine ⟨true, HeadAgree.refl x, ?_⟩
            rw [drvWire_pickCand_true]
            refine congrArg Sum.inl ?_
            rw [show (⟨(modeEquiv spec w'.1 : ℕ), by have := (modeEquiv spec w'.1).isLt; omega⟩ :
              Fin (modeCard spec + 1)) = ixOf spec w'.1 from rfl, modeAt_ixOf]
            rfl
          have hstep3 : wireStep (drvRel spec)
              (drvWire (modeAt spec) (nextIx spec) (ix0 spec))
              ((.tryCand w.1 w'.1 : DrvNode spec.Mode (modeCard spec)), x)
              ((.commit w.1 w'.1 : DrvNode spec.Mode (modeCard spec)),
                putBlk1 spec x w'.2) := by
            refine ⟨true, ⟨⟨fun _ => ?_, fun _ => rfl⟩,
              fun j hj => putBlk1_of_lt spec x w'.2 hj⟩, ?_⟩
            · have hc : curNode spec (putBlk1 spec x w'.2) w.1 = w := by
                rw [← hx]
                exact congrArg (fun v => (w.1, v)) (funext fun i =>
                  putBlk1_of_lt spec x w'.2 i.isLt)
              have hd : candNode spec (putBlk1 spec x w'.2) w'.1 = w' :=
                congrArg (fun v => (w'.1, v)) (funext fun i => putBlk1_blk1 spec x w'.2 i)
              rw [hc, hd]
              exact hstep
            · rw [drvWire_tryCand_true]
          have hstep4 : wireStep (drvRel spec)
              (drvWire (modeAt spec) (nextIx spec) (ix0 spec))
              ((.commit w.1 w'.1 : DrvNode spec.Mode (modeCard spec)), putBlk1 spec x w'.2)
              ((.target w'.1 : DrvNode spec.Mode (modeCard spec)),
                putBlk0 spec (putBlk1 spec x w'.2) w'.2) := by
            refine ⟨true, ⟨rfl, fun i => ?_, fun j hj1 _ => ?_⟩, ?_⟩
            · simp only [putBlk0_blk0, putBlk1_blk1]
            · exact putBlk0_of_le spec (putBlk1 spec x w'.2) w'.2 hj1
            · rw [drvWire_commit]
          exact ((((hwalk.trans hstep1).trans hchain).tail hstep2).tail hstep3).tail hstep4

/-! ### The capture theorem -/

variable (A)

/-- **The machine of a specification accepts exactly what the specification
does.** -/
theorem accepts_drvP [Nonempty A] :
    ((drvP spec).compile false).Accepts A ↔ spec.Accepts A := by
  have hruns := runs_wireP (C := DrvNode spec.Mode (modeCard spec)) (drvFam spec)
    (drvWire (modeAt spec) (nextIx spec) (ix0 spec)) (runs_drvFam (A := A) spec)
    (headLocal2_drvRel (A := A) spec) (.pickSrc (ix0 spec))
  rw [accepts_compile_false]
  constructor
  · rintro ⟨x, y, -, hreach⟩
    obtain ⟨u, hwalk, hexit⟩ := hruns.sound hreach
    exact accepts_of_exit spec x hwalk hexit
  · rintro ⟨u₀, v, hu₀, hv, hreach⟩
    obtain ⟨mn, hmn⟩ : ∃ mn : A, ∀ a : A, mn ≤ a := by
      have := Fintype.ofFinite A
      have hune : (Finset.univ : Finset A).Nonempty := ⟨Classical.arbitrary A, Finset.mem_univ _⟩
      exact ⟨Finset.univ.min' hune, fun a => Finset.min'_le _ a (Finset.mem_univ a)⟩
    rcases walk_of_reach spec (fun _ => mn) hu₀ v hreach with ⟨u, z, hwalk, hexit⟩ | ⟨x, hx, hwalk⟩
    · obtain ⟨y', -, hy'⟩ := hruns.complete ⟨u, hwalk, hexit⟩
      exact ⟨fun _ => mn, y', fun _ => hmn, hy'⟩
    · refine ⟨fun _ => mn, ?_, fun _ => hmn, ?_⟩
      · exact Classical.choose (hruns.complete (b := true) (y := x)
          ⟨((.target v.1 : DrvNode spec.Mode (modeCard spec)), x), hwalk, true,
            ⟨⟨fun _ => by rw [hx]; exact hv, fun _ => rfl⟩, HeadAgree.refl x⟩,
            by rw [drvWire_target_true]⟩)
      · exact (Classical.choose_spec (hruns.complete (b := true) (y := x)
          ⟨((.target v.1 : DrvNode spec.Mode (modeCard spec)), x), hwalk, true,
            ⟨⟨fun _ => by rw [hx]; exact hv, fun _ => rfl⟩, HeadAgree.refl x⟩,
            by rw [drvWire_target_true]⟩)).2

end Runs

end Machine

/-! ### The capture theorem -/

/-- **The capture theorem for FO(TC)**: a problem is definable by a single
transitive closure exactly when a two-way multi-head automaton recognizes it.
One direction is `DescriptiveComplexity.tcDefinable_of_automaton` – a configuration is
a node of a specification – and the other is the machine built here. -/
theorem tcDefinable_iff_automaton [L.IsRelational] {P : DecisionProblem L} :
    TCDefinable P ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ M.Accepts A := by
  constructor
  · rintro ⟨spec, hspec⟩
    refine ⟨specHeads spec, (drvP spec).compile false, fun A _ _ _ _ => ?_⟩
    rw [hspec A, ← accepts_drvP spec A]
  · rintro ⟨k, M, hM⟩
    exact tcDefinable_of_automaton M hM

/-- **NL is the class of the two-way multi-head automata**: membership in
`DescriptiveComplexity.NL` is recognizability by such a machine. -/
theorem mem_NL_iff_automaton [L.IsRelational] {P : DecisionProblem L} :
    P ∈ NL ↔ ∃ (k : ℕ) (M : HeadAutomaton L k),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        P A ↔ M.Accepts A :=
  (tcDefinable_iff_mem_NL P).symm.trans tcDefinable_iff_automaton

end DescriptiveComplexity
