/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax624099Proofs.DescriptiveComplexity.Machines
import Lax624099.ClassRE
import Lax624099.CodeHalting
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.PostCorrespondence
import Lax624099.ValueInvention
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax624099.Halting.TMData
end Lax624099.Halting.TMData

namespace Lax624099Proofs.DescriptiveComplexity.ConfigU
end Lax624099Proofs.DescriptiveComplexity.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity.TMData
end Lax624099Proofs.DescriptiveComplexity.TMData

namespace Lax624099Proofs.DescriptiveComplexity.TMData.Agree
end Lax624099Proofs.DescriptiveComplexity.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity.TMData.StepsInU
end Lax624099Proofs.DescriptiveComplexity.TMData.StepsInU

namespace Lax904597.Machines.TMData
export Lax624099.Halting.TMData (AcceptsU IsInitU StepU StepsInU SuccCell)
end Lax904597.Machines.TMData

/-!
# Turing machines on an unbounded tape

The third acceptance notion of `Lax624099Proofs.DescriptiveComplexity.TMData`, beside
`Lax624099Proofs.DescriptiveComplexity.TMData.Accepts` (a run bounded by the number of
positions, hence NP) and `Lax624099Proofs.DescriptiveComplexity.TMData.AcceptsSpace` (a run of
any length on a tape indexed by the positions, hence PSPACE): a run of any
length on a tape that **leaves the instance**. It is the acceptance notion of
the halting problem, and the one whose certificate no function of the instance
bounds – which is what puts it in RE and nowhere lower.

The machine itself is unchanged: the vocabulary, the record
`Lax624099Proofs.DescriptiveComplexity.TMData`, its well-formedness and the whole `Agree`
transport layer are reused. Only the configuration changes, and it has to:
`Lax624099Proofs.DescriptiveComplexity.Config` has `tape : A → A`, so space-boundedness is
built into the type.

## The cells: an unbounded strip of pages

A cell is a pair `(z, p) : ℤ × A` with `p` a position, ordered
lexicographically – an unbounded strip of *pages*, each page a copy of the
instance's positions, with the input on page `0`:

```
   … ‖ page -1 ‖ page 0 (the input) ‖ page 1 ‖ …
          p₀ … pₙ      p₀ … pₙ           p₀ … pₙ
```

On a finite instance this is an ordinary two-way infinite tape up to renaming
the cells (`ℤ ×ₗ {p // Posn p}` is order-isomorphic to `ℤ`). Naming the cells
by a page and an offset rather than by an integer is what keeps *all*
arithmetic out of the semantics: the head's move
(`Lax624099Proofs.DescriptiveComplexity.TMData.SuccCell`) is one step of
`Lax624099Proofs.DescriptiveComplexity.SuccPos` inside a page, or the step from the last
position of a page to the first position of the next, so the order vocabulary
of `Lax624099Proofs.DescriptiveComplexity.Numbers.BinRel` covers it unchanged. It is also what
places the input with no rank function: the input is page `0`.

Unlike the bounded model, **no move is ever impossible**: there is no “the head
falls off the end and the run stops” case, one branch fewer in every proof
downstream.
-/

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

/-- A run extended by one more step at its end. -/
theorem StepsInU.trans_step : ∀ {n : ℕ} {c d e : Lax624099.Halting.ConfigU A},
    M.StepsInU n c d → M.StepU d e → M.StepsInU (n + 1) c e := by
  intro n
  induction n with
  | zero => intro c d e hcd hde; exact ⟨e, by rw [show c = d from hcd]; exact hde, rfl⟩
  | succ n ih =>
    rintro c d e ⟨m, hstep, hrest⟩ hde
    exact ⟨m, hstep, ih hrest hde⟩

end Steps

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.TMData.StepsInU

export Lax624099Proofs.DescriptiveComplexity.TMData.StepsInU (trans_step)

end Lax624099.Halting.TMData.StepsInU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Steps

variable {M}

end Steps

/-! ### The head stays in a bounded band of pages

A run of `n` steps moves the head by at most one page per step, so the pages it
visits lie within `n` of the page it started on. This is what makes the
certificate of the membership proof finite, and it is the only quantitative
fact the unbounded model needs. -/

section Band

variable {M}

/-- One step moves the head by at most one page, in either direction. -/
theorem page_dist_stepU {c c' : Lax624099.Halting.ConfigU A} (h : M.StepU c c') :
    (c'.head.1 - c.head.1).natAbs ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, hmove⟩ := h
  have hcell : ∀ x y : ℤ × A, M.SuccCell x y → y.1 = x.1 ∨ y.1 = x.1 + 1 := by
    rintro x y (⟨hz, _⟩ | ⟨hz, _, _⟩)
    · exact Or.inl hz
    · exact Or.inr hz
  rcases hmove with ⟨_, hs⟩ | ⟨_, hs⟩
  · rcases hcell _ _ hs with hz | hz <;> omega
  · rcases hcell _ _ hs with hz | hz <;> omega

end Band

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax624099Proofs.DescriptiveComplexity.TMData (page_dist_stepU)

end Lax904597.Machines.TMData

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Band

variable {M}

/-- **The band of a run**: after `n` steps the head is within `n` pages of where
it started. -/
theorem page_dist_stepsInU : ∀ {n : ℕ} {c c' : Lax624099.Halting.ConfigU A},
    M.StepsInU n c c' → (c'.head.1 - c.head.1).natAbs ≤ n := by
  intro n
  induction n with
  | zero => intro c c' h; rw [show c = c' from h]; simp
  | succ n ih =>
    rintro c c' ⟨d, hstep, hrest⟩
    have h1 := page_dist_stepU hstep
    have h2 := ih hrest
    omega

end Band

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData

export Lax624099Proofs.DescriptiveComplexity.TMData (page_dist_stepsInU)

end Lax904597.Machines.TMData

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Band

variable {M}

end Band

/-! ### Transport along an equivalence of universes -/

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Transport of an unbounded configuration along an equivalence: the page of a
cell is untouched, the offset and the contents move along `u`. -/
def _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map (u : B ≃ A) (c : Lax624099.Halting.ConfigU B) : Lax624099.Halting.ConfigU A where
  state := u c.state
  head := (c.head.1, u c.head.2)
  tape := fun x => u (c.tape (x.1, u.symm x.2))

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map_state (u : B ≃ A) (c : Lax624099.Halting.ConfigU B) :
    (c.map u).state = u c.state := rfl

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map_state)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map_head (u : B ≃ A) (c : Lax624099.Halting.ConfigU B) :
    (c.map u).head = (c.head.1, u c.head.2) := rfl

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map_head)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

@[simp] theorem _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map_tape (u : B ≃ A) (c : Lax624099.Halting.ConfigU B)
    (x : ℤ × A) : (c.map u).tape x = u (c.tape (x.1, u.symm x.2)) := rfl

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map_tape)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Every unbounded configuration over `A` is the transport of one over `B`. -/
theorem _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map_surjective (u : B ≃ A) :
    Function.Surjective (ConfigU.map u) := by
  intro c
  refine ⟨⟨u.symm c.state, (c.head.1, u.symm c.head.2), fun x => u.symm (c.tape (x.1, u x.2))⟩, ?_⟩
  refine Lax624099.Halting.ConfigU.ext ?_ ?_ ?_
  · simp [ConfigU.map]
  · simp [ConfigU.map]
  · funext x
    simp [ConfigU.map]

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map_surjective)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem _root_.Lax624099Proofs.DescriptiveComplexity.ConfigU.map_injective (u : B ≃ A) :
    Function.Injective (ConfigU.map u) := by
  rintro ⟨s, hd, t⟩ ⟨s', hd', t'⟩ hc
  simp only [ConfigU.map, Lax624099.Halting.ConfigU.mk.injEq, Prod.mk.injEq] at hc
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hc
  have ht : t = t' := by
    funext x
    have := congrFun h4 (x.1, u x.2)
    simpa using u.injective (by simpa using this)
  have hhd : hd = hd' := Prod.ext h2 (u.injective h3)
  simp [u.injective h1, hhd, ht]

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax624099.Halting.ConfigU

export Lax624099Proofs.DescriptiveComplexity.ConfigU (map_injective)

end Lax624099.Halting.ConfigU

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- Highest positions correspond, the companion of
`Lax624099Proofs.DescriptiveComplexity.TMData.Agree.minPos`: the bounded model never mentions a
highest position, but the page-crossing move does. -/
theorem Agree.maxPos (h : Agree u N M) {b : B} :
    Lax624099.Halting.MaxPos N.Le N.Posn b ↔ Lax624099.Halting.MaxPos M.Le M.Posn (u b) := by
  refine and_congr (h.posn b) ⟨fun hm a ha => ?_, fun hm a ha => ?_⟩
  · have := hm (u.symm a) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
    rwa [(h.le _ _), Equiv.apply_symm_apply] at this
  · exact (h.le _ _).mpr (hm (u a) ((h.posn a).mp ha))

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (maxPos)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.succCell (h : Agree u N M) {c c' : ℤ × B} :
    N.SuccCell c c' ↔ M.SuccCell (c.1, u c.2) (c'.1, u c'.2) := by
  refine or_congr (and_congr Iff.rfl h.succPos) (and_congr Iff.rfl (and_congr ?_ ?_))
  · exact h.maxPos
  · exact h.minPos

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (succCell)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.isInitU (h : Agree u N M) {c : Lax624099.Halting.ConfigU B} :
    N.IsInitU c ↔ M.IsInitU (c.map u) := by
  refine and_congr (h.start _) (and_congr Iff.rfl (and_congr h.minPos ?_))
  constructor
  · intro hi z p hp
    have := hi z (u.symm p) ((h.posn _).mpr (by rwa [Equiv.apply_symm_apply]))
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · have := (h.initTape (u := u)).mp (this.1 hz)
      rwa [Equiv.apply_symm_apply] at this
    · exact (h.blank _).mp (this.2 hz)
  · intro hi z b hb
    have := hi z (u b) ((h.posn b).mp hb)
    refine ⟨fun hz => (h.initTape (u := u)).mpr (by simpa using this.1 hz),
      fun hz => (h.blank _).mpr (by simpa using this.2 hz)⟩

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (isInitU)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.stepU (h : Agree u N M) {c c' : Lax624099.Halting.ConfigU B} :
    N.StepU c c' ↔ M.StepU (c.map u) (c'.map u) := by
  constructor
  · rintro ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    refine ⟨u τ, (h.tr _).mp hτ, (h.src _ _).mp hsrc, ?_, (h.dst _ _).mp hdst, ?_, ?_, ?_⟩
    · simpa [ConfigU.map] using (h.read _ _).mp hread
    · simpa [ConfigU.map] using (h.write _ _).mp hwrite
    · intro x hx
      have hb : (x.1, u.symm x.2) ≠ c.head := by
        intro hcon
        exact hx (by rw [ConfigU.map_head, ← hcon]; simp)
      simpa [ConfigU.map] using congrArg u (hframe (x.1, u.symm x.2) hb)
    · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨(h.right _).mp hr, h.succCell.mp hs⟩
      · exact Or.inr ⟨fun hcon => hr ((h.right _).mpr hcon), h.succCell.mp hs⟩
  · rintro ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
    refine ⟨u.symm τ, (h.tr _).mpr (by rwa [Equiv.apply_symm_apply]),
      (h.src _ _).mpr (by rwa [Equiv.apply_symm_apply]), ?_,
      (h.dst _ _).mpr (by rwa [Equiv.apply_symm_apply]), ?_, ?_, ?_⟩
    · refine (h.read _ _).mpr ?_
      rw [Equiv.apply_symm_apply]
      simpa [ConfigU.map] using hread
    · refine (h.write _ _).mpr ?_
      rw [Equiv.apply_symm_apply]
      simpa [ConfigU.map] using hwrite
    · intro x hx
      have hx' : ((x.1, u x.2) : ℤ × A) ≠ (c.map u).head := by
        intro hcon
        simp only [ConfigU.map_head, Prod.mk.injEq] at hcon
        exact hx (Prod.ext hcon.1 (u.injective hcon.2))
      exact u.injective (by simpa [ConfigU.map] using hframe (x.1, u x.2) hx')
    · rcases hmove with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · exact Or.inl ⟨(h.right _).mpr (by rwa [Equiv.apply_symm_apply]), h.succCell.mpr hs⟩
      · refine Or.inr ⟨fun hcon => hr ?_, h.succCell.mpr hs⟩
        rw [← Equiv.apply_symm_apply u τ]
        exact (h.right _).mp hcon

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (stepU)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

theorem Agree.stepsInU (h : Agree u N M) :
    ∀ (n : ℕ) (c c' : Lax624099.Halting.ConfigU B), N.StepsInU n c c' ↔ M.StepsInU n (c.map u) (c'.map u) := by
  intro n
  induction n with
  | zero =>
    intro c c'
    change c = c' ↔ ConfigU.map u c = ConfigU.map u c'
    exact ⟨congrArg (ConfigU.map u), fun hc => ConfigU.map_injective u hc⟩
  | succ n ih =>
    intro c c'
    constructor
    · rintro ⟨d, hstep, hrest⟩
      exact ⟨d.map u, h.stepU.mp hstep, (ih d c').mp hrest⟩
    · rintro ⟨d, hstep, hrest⟩
      obtain ⟨d₀, rfl⟩ := ConfigU.map_surjective u d
      exact ⟨d₀, h.stepU.mpr hstep, (ih d₀ c').mpr hrest⟩

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (stepsInU)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

/-- **Acceptance on an unbounded tape transports along an equivalence.** -/
theorem Agree.acceptsU (h : Agree u N M) : N.AcceptsU ↔ M.AcceptsU := by
  constructor
  · rintro ⟨c₀, c, n, hinit, hrun, hacc⟩
    exact ⟨c₀.map u, c.map u, n, h.isInitU.mp hinit, (h.stepsInU n c₀ c).mp hrun,
      (h.acc _).mp hacc⟩
  · rintro ⟨c₀, c, n, hinit, hrun, hacc⟩
    obtain ⟨d₀, rfl⟩ := ConfigU.map_surjective u c₀
    obtain ⟨d, rfl⟩ := ConfigU.map_surjective u c
    exact ⟨d₀, d, n, h.isInitU.mpr hinit, (h.stepsInU n d₀ d).mpr hrun, (h.acc _).mpr hacc⟩

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity

namespace Lax904597.Machines.TMData.Agree

export Lax624099Proofs.DescriptiveComplexity.TMData.Agree (acceptsU)

end Lax904597.Machines.TMData.Agree

namespace Lax624099Proofs.DescriptiveComplexity

namespace TMData

variable {A : Type} (M : Lax904597.Machines.TMData A)

section Transport

variable {A B : Type} {M : Lax904597.Machines.TMData A} {u : B ≃ A} {N : Lax904597.Machines.TMData B}

end Transport

end TMData

end Lax624099Proofs.DescriptiveComplexity


