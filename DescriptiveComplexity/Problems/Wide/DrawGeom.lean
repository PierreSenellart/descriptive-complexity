/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawMatrix

/-!
# Where the states, the symbols and the transitions sit

The instance the reduction emits has universe `Draw.Tag R P K × (Fin dd → A)`, and
its states, symbols and transitions are *elements* of it. This file says which
elements they are.

The layout is the simplest one that works. A state, a symbol and a transition each
carry a **payload** of `c` coordinates – `c` is the program's choice, and `dd` is
at least `c` – and the coordinates beyond the payload hold a designated element.
That padding is not decoration: without it an element would have `n^(dd-c)`
spellings, and the machine's promises are that there is *one* start state, *one*
blank, and at most one transition per state and symbol
(`DescriptiveComplexity.TMData.Deterministic`). A canonical spelling is what makes
those provable.

What distinguishes the three is the **tag**, which is also what carries everything
about a transition except its data: its rule index. So

* a state is `(phase p, pad w)` – the call site in the tag, the pointer in `w`;
* a symbol is `(sym, pad w)` – the tracks in `w` (`DrawTracks`);
* a transition is `(ctrl r, pad w)` – the rule in the tag, its data in `w`.

Two elements with different tags are different, and two with the same tag differ
exactly when their payloads do
(`DescriptiveComplexity.Draw.pad_injective`). Those are the distinctness facts the
well-formedness and determinism obligations are discharged from.
-/

namespace DescriptiveComplexity

namespace Draw

section Geom

variable {A : Type} {c dd : ℕ}

/-! ### Canonical payloads -/

open Classical in
/-- **The canonical tuple carrying a payload**: the payload in the first `c`
coordinates, the designated element in the rest. -/
noncomputable def pad (zero : A) (w : Fin c → A) : Fin dd → A :=
  fun j => if h : (j : ℕ) < c then w ⟨j, h⟩ else zero

/-- **Reading a payload back.** -/
def unpad (hc : c ≤ dd) (v : Fin dd → A) : Fin c → A :=
  fun i => v ⟨i, lt_of_lt_of_le i.isLt hc⟩

/-- **Being canonically padded**: nothing but the designated element beyond the
payload. This is the condition that gives an element one spelling, and so the
machine's promises their uniqueness. -/
def IsPad (c : ℕ) (zero : A) (v : Fin dd → A) : Prop := ∀ j : Fin dd, c ≤ (j : ℕ) → v j = zero

variable {zero : A} {w : Fin c → A} {v : Fin dd → A}

@[simp]
theorem pad_of_lt (j : Fin dd) (h : (j : ℕ) < c) : pad (dd := dd) zero w j = w ⟨j, h⟩ := by
  simp [pad, h]

@[simp]
theorem pad_of_ge (j : Fin dd) (h : c ≤ (j : ℕ)) : pad (dd := dd) zero w j = zero := by
  simp [pad, Nat.not_lt.mpr h]

theorem isPad_pad : IsPad c zero (pad (dd := dd) zero w) := fun j h => pad_of_ge j h

/-- **A payload reads back.** -/
@[simp]
theorem unpad_pad (hc : c ≤ dd) : unpad hc (pad (dd := dd) zero w) = w :=
  funext fun i => by
    rw [unpad, pad_of_lt _ (by exact i.isLt)]

/-- **A canonically padded tuple is the padding of what it carries**, so the two
descriptions of an element – "it is `pad` of something" and "it is padded" – are
the same. -/
theorem pad_unpad (hc : c ≤ dd) (hv : IsPad c zero v) : pad zero (unpad hc v) = v := by
  refine funext fun j => ?_
  by_cases h : (j : ℕ) < c
  · rw [pad_of_lt j h, unpad]
  · rw [pad_of_ge j (Nat.not_lt.mp h), hv j (Nat.not_lt.mp h)]

/-- **Distinct payloads give distinct tuples**, which is where every uniqueness
promise of the emitted machine comes from. -/
theorem pad_injective (hc : c ≤ dd) : Function.Injective (pad (dd := dd) (c := c) zero) := by
  intro w w' h
  have hu := congrArg (unpad hc) h
  rwa [unpad_pad, unpad_pad] at hu

/-! ### The three kinds of element -/

variable {R P K : Type}

/-- **A state**: the call site in the tag, the pointer in the payload. -/
noncomputable def stateElt (zero : A) (p : P) (w : Fin c → A) :
    Tag R P K × (Fin dd → A) :=
  (Tag.phase p, pad zero w)

/-- **A symbol**: the tracks in the payload (`DescriptiveComplexity.Draw.withBit`). -/
noncomputable def symElt (zero : A) (w : Fin c → A) : Tag R P K × (Fin dd → A) :=
  (Tag.sym, pad zero w)

/-- **A transition**: the rule in the tag, the rule's data in the payload. -/
noncomputable def trElt (zero : A) (r : R) (w : Fin c → A) :
    Tag R P K × (Fin dd → A) :=
  (Tag.ctrl r, pad zero w)

/-- **A state is determined by its call site and its pointer.** -/
theorem stateElt_inj (hc : c ≤ dd) {p p' : P} {w w' : Fin c → A}
    (h : stateElt (dd := dd) (R := R) (K := K) zero p w = stateElt zero p' w') :
    p = p' ∧ w = w' := by
  refine ⟨?_, pad_injective hc (congrArg Prod.snd h)⟩
  have h1 : (Tag.phase p : Tag R P K) = Tag.phase p' := congrArg Prod.fst h
  simpa using h1

/-- **A symbol is determined by its tracks.** -/
theorem symElt_inj (hc : c ≤ dd) {w w' : Fin c → A}
    (h : symElt (dd := dd) (R := R) (P := P) (K := K) zero w = symElt zero w') : w = w' :=
  pad_injective hc (congrArg Prod.snd h)

/-- **A transition is determined by its rule and its data.** -/
theorem trElt_inj (hc : c ≤ dd) {r r' : R} {w w' : Fin c → A}
    (h : trElt (dd := dd) (P := P) (K := K) zero r w = trElt zero r' w') :
    r = r' ∧ w = w' := by
  refine ⟨?_, pad_injective hc (congrArg Prod.snd h)⟩
  have h1 : (Tag.ctrl r : Tag R P K) = Tag.ctrl r' := congrArg Prod.fst h
  simpa using h1

/-- **The three kinds are disjoint**, by their tags: no element is both a state
and a symbol. -/
theorem stateElt_ne_symElt (p : P) (w w' : Fin c → A) :
    stateElt (dd := dd) (R := R) (K := K) zero p w ≠ symElt zero w' := by
  intro h
  have h1 : (Tag.phase p : Tag R P K) = Tag.sym := congrArg Prod.fst h
  simp at h1

/-- No element is both a transition and a state. -/
theorem trElt_ne_stateElt (r : R) (p : P) (w w' : Fin c → A) :
    trElt (dd := dd) (K := K) zero r w ≠ stateElt zero p w' := by
  intro h
  have h1 : (Tag.ctrl r : Tag R P K) = Tag.phase p := congrArg Prod.fst h
  simp at h1

/-- No element is both a transition and a symbol. -/
theorem trElt_ne_symElt (r : R) (w w' : Fin c → A) :
    trElt (dd := dd) (P := P) (K := K) zero r w ≠ symElt zero w' := by
  intro h
  have h1 : (Tag.ctrl r : Tag R P K) = Tag.sym := congrArg Prod.fst h
  simp at h1

end Geom

end Draw

end DescriptiveComplexity
