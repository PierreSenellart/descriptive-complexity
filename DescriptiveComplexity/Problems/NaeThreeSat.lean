/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.NaeSat
import DescriptiveComplexity.Problems.ThreeSat.ToSat
import DescriptiveComplexity.Problems.ThreeSat.FromSat

/-!
# NAE-3SAT is NP-complete

NAE-3SAT is the width-three restriction of NAE-SAT: a `FirstOrder.Language.sat`-structure
is a yes-instance (`DescriptiveComplexity.NAEThreeSatisfiable`) when every clause has at
most three literal occurrences – the very same promise
`DescriptiveComplexity.WidthAtMostThree` as 3SAT – *and* some assignment gives every
clause both a true and a false literal.

Its value in the catalog, like NAE-SAT's, is as a reduction *source*: the
classical reduction to Max Cut runs on width-three not-all-equal clauses.

## Both reductions reuse 3SAT's interpretations verbatim

The point of this file is that no new interpretation is built. Both

* `DescriptiveComplexity.nae3Sat_fo_reduction_naeSat` (membership), through
  `DescriptiveComplexity.ThreeSatToSat.threeSatToSat`, the identity-like interpretation
  gated on the first-order width check, and
* `DescriptiveComplexity.naeSat_ordered_fo_reduction_nae3Sat` (hardness), through
  `DescriptiveComplexity.SatToThreeSat.satToThreeSat`, the clause-splitting
  interpretation along the occurrence order

are the interpretations of the SAT/3SAT pair, applied unchanged; only the
notion of satisfaction attached to them differs. In particular the width
promise (`DescriptiveComplexity.SatToThreeSat.widthAtMostThree_map`) is inherited as
proved, since it is a property of the output structure alone.

That the *same* chain of clause pieces
`(ℓ₁ ∨ y₂), (¬y₂ ∨ ℓ₂ ∨ y₃), …, (¬y_k ∨ ℓ_k)`
works for the not-all-equal reading is the substance of the hardness half.
Read as NAE-clauses, the chain forces the linking variables to carry a value
*into* each piece: writing `T_i` for `¬y_i`, the first piece pins `T₂` to the
value of `ℓ₁`, the last one demands `T_k ≠ ℓ_k`, and the middle ones say
`NAE(T_i, ℓ_i, ¬T_{i+1})`, which is the peeling identity
`NAE(a, ℓ, ℓ', …) ↔ ∃ y, NAE(a, ℓ, y) ∧ NAE(¬y, ℓ', …)` applied along the
order. The witnessing assignment (`DescriptiveComplexity.NaeSatToNaeThreeSat.LinkVal`)
is *not* the one 3SAT uses: a linking variable carries the negation of the
value common to all earlier occurrences as long as they do agree
(`DescriptiveComplexity.NaeSatToNaeThreeSat.UniformBefore`), and its own literal's value
once they do not.

The converse half needs nothing new: a not-all-equal assignment of the split
is in particular a satisfying one, so the chain argument of the 3SAT
reduction, isolated as `DescriptiveComplexity.SatToThreeSat.exists_litTrue_of_map`,
applies to it – and, by the flip symmetry of not-all-equal satisfaction
(`DescriptiveComplexity.NAEProper.not`), also to its negation, which is what yields the
false literal.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-! ### The problem -/

section Problem

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is a yes-instance of NAE-3SAT if every clause
has at most three literal occurrences and some assignment gives every clause
both a true and a false literal. -/
def NAEThreeSatisfiable : Prop :=
  WidthAtMostThree A ∧ NAESatisfiable A

end Problem

/-- Not-all-equal 3-satisfiability is isomorphism-invariant. -/
theorem naeThreeSatisfiable_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) :
    NAEThreeSatisfiable A ↔ NAEThreeSatisfiable B :=
  and_congr (widthAtMostThree_iso e) (naeSatisfiable_iso e)

/-- NAE-3SAT, as a problem on `Language.sat`-structures: the same vocabulary
as NAE-SAT, with 3SAT's width bound folded into the yes-instances. -/
def NAE3SAT : DecisionProblem Language.sat where
  Holds := fun A inst => @NAEThreeSatisfiable A inst
  iso_invariant := fun e => naeThreeSatisfiable_iso e

/-! ### NAE-3SAT reduces to NAE-SAT -/

namespace NaeThreeSatToNaeSat

open ThreeSatToSat

/-- Correctness of the reduction: a CNF structure is a yes-instance of
NAE-3SAT iff the interpreted structure – a faithful copy of it if no clause is
wide, a structure made of empty clauses otherwise – is not-all-equal
satisfiable. -/
theorem naeThreeSatisfiable_iff_naeSatisfiable (A : Type) [Language.sat.Structure A] :
    NAEThreeSatisfiable A ↔ NAESatisfiable (threeSatToSat.Map A) := by
  by_cases hw : Wide A
  · -- wide input: both sides fail
    refine iff_of_false (fun h => (wide_iff_not_widthAtMostThree A).mp hw h.1) ?_
    rintro ⟨ν, hν⟩
    have hw' := hw
    obtain ⟨c, -, -, -, -⟩ := hw'
    obtain ⟨⟨⟨⟩, wx⟩, hx⟩ := (hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inr hw))).1
    rcases hx with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · exact ((posIn_iff _ _).mp hpos).2 hw
    · exact ((negIn_iff _ _).mp hneg).2 hw
  · -- non-wide input: faithful copy
    have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hw ((wide_iff_not_widthAtMostThree A).mpr h)
    rw [NAEThreeSatisfiable, and_iff_right hwidth]
    -- transport along `(fun _ => w 0) = w`, at raw product type
    have hsub : ∀ (g : Unit × (Fin 1 → A) → Prop) (w : Fin 1 → A),
        g ((), w) ↔ g ((), fun _ => w 0) := fun g w => by
      have hw : (fun _ => w 0) = w := funext fun i => congrArg w (Subsingleton.elim 0 i)
      rw [hw]
    constructor
    · rintro ⟨ν, hν⟩
      refine ⟨fun p => ν (p.2 0), ?_⟩
      rintro ⟨⟨⟩, w⟩ hcl
      rcases (isClause_iff w).mp hcl with hcl' | hcl'
      · obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ := hν (w 0) hcl'
        constructor
        · rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
          · exact ⟨((), fun _ => z), Or.inl ⟨(posIn_iff _ _).mpr ⟨hp, hw⟩, hT⟩⟩
          · exact ⟨((), fun _ => z), Or.inr ⟨(negIn_iff _ _).mpr ⟨hn, hw⟩, hT⟩⟩
        · rcases hz' with ⟨hp, hT⟩ | ⟨hn, hT⟩
          · exact ⟨((), fun _ => z'), Or.inl ⟨(posIn_iff _ _).mpr ⟨hp, hw⟩, hT⟩⟩
          · exact ⟨((), fun _ => z'), Or.inr ⟨(negIn_iff _ _).mpr ⟨hn, hw⟩, hT⟩⟩
      · exact absurd hcl' hw
    · rintro ⟨ν, hν⟩
      refine ⟨fun a => ν ((), fun _ => a), ?_⟩
      intro c hc
      obtain ⟨⟨⟨⟨⟩, wz⟩, hz⟩, ⟨⟨⟨⟩, wz'⟩, hz'⟩⟩ :=
        hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inl hc))
      constructor
      · rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
        · exact ⟨wz 0, Or.inl ⟨((posIn_iff _ _).mp hp).1, (hsub ν wz).mp hT⟩⟩
        · exact ⟨wz 0, Or.inr ⟨((negIn_iff _ _).mp hn).1, fun h => hT ((hsub ν wz).mpr h)⟩⟩
      · rcases hz' with ⟨hp, hT⟩ | ⟨hn, hT⟩
        · exact ⟨wz' 0, Or.inl ⟨((posIn_iff _ _).mp hp).1, fun h => hT ((hsub ν wz').mpr h)⟩⟩
        · exact ⟨wz' 0, Or.inr ⟨((negIn_iff _ _).mp hn).1, (hsub ν wz').mp hT⟩⟩

end NaeThreeSatToNaeSat

open NaeThreeSatToNaeSat ThreeSatToSat in
/-- **NAE-3SAT FO-reduces to NAE-SAT.** 3SAT's identity-like interpretation
`ThreeSatToSat.threeSatToSat`, gated on the first-order width check, maps a
CNF structure to a not-all-equal satisfiable instance iff it is a yes-instance
of NAE-3SAT. -/
noncomputable def nae3Sat_fo_reduction_naeSat : NAE3SAT ≤ᶠᵒ NAESAT where
  Tag := Unit
  dim := 1
  toInterpretation := threeSatToSat
  correct A _ _ := naeThreeSatisfiable_iff_naeSatisfiable A

/-! ### NAE-SAT reduces to NAE-3SAT -/

namespace NaeSatToNaeThreeSat

open SatToThreeSat

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The occurrences of the clause `c` strictly before `(x, s)` all have the
same truth value under `ν`. -/
def UniformBefore (ν : A → Prop) (c x : A) (s : Bool) : Prop :=
  ∀ z u z' u', OccIn c z u → OccIn c z' u' → occLt z u x s → occLt z' u' x s →
    (LitTrue ν z u ↔ LitTrue ν z' u')

/-- The value carried by the linking variable of the occurrence `(x, s)` of
`c`: the negation of the value common to all earlier occurrences as long as
they do agree, and the value of its own literal once they do not. -/
def LinkVal (ν : A → Prop) (c x : A) (s : Bool) : Prop :=
  (UniformBefore ν c x s ∧ ¬PrefixOrStrict ν c x s) ∨
    (¬UniformBefore ν c x s ∧ LitTrue ν x s)

theorem linkVal_of_uniform {ν : A → Prop} {c x : A} {s : Bool}
    (h : UniformBefore ν c x s) : LinkVal ν c x s ↔ ¬PrefixOrStrict ν c x s := by
  constructor
  · rintro (⟨-, h'⟩ | ⟨h', -⟩)
    · exact h'
    · exact absurd h h'
  · exact fun h' => Or.inl ⟨h, h'⟩

theorem linkVal_of_not_uniform {ν : A → Prop} {c x : A} {s : Bool}
    (h : ¬UniformBefore ν c x s) : LinkVal ν c x s ↔ LitTrue ν x s := by
  constructor
  · rintro (⟨h', -⟩ | ⟨-, h'⟩)
    · exact absurd h' h
    · exact h'
  · exact fun h' => Or.inr ⟨h, h'⟩

/-- The assignment of the split induced by a not-all-equal assignment of the
input: variable copies follow `ν`, and linking variables carry `LinkVal`. -/
def naeSplitAssign (ν : A → Prop) : satToThreeSat.Map A → Prop := fun p =>
  match p.1 with
  | .var => ν (p.2 0)
  | .link s => LinkVal ν (p.2 0) (p.2 1) s
  | _ => False

@[simp]
theorem naeSplitAssign_var (ν : A → Prop) (w : Fin 2 → A) :
    naeSplitAssign ν (SplitTag.var, w) ↔ ν (w 0) := Iff.rfl

@[simp]
theorem naeSplitAssign_link (ν : A → Prop) (s : Bool) (w : Fin 2 → A) :
    naeSplitAssign ν (SplitTag.link s, w) ↔ LinkVal ν (w 0) (w 1) s := Iff.rfl

variable [Finite A]

/-- **The peeling step.** If every occurrence of `c` up to `(x, s)` has the
same value as `(x, s)` while some occurrence differs, then `(x, s)` has an
immediate successor, and the successor's linking variable carries the opposite
value – which is what gives the piece of `(x, s)` a literal of each sign. -/
theorem exists_succ_linkVal {ν : A → Prop} {c x : A} {s : Bool} (hocc : OccIn c x s)
    (hup : ∀ z u, OccIn c z u → ¬occLt x s z u → (LitTrue ν z u ↔ LitTrue ν x s))
    (hdiff : ∃ z u, OccIn c z u ∧ ¬(LitTrue ν z u ↔ LitTrue ν x s)) :
    ∃ y t, SuccOcc c x s y t ∧ (LinkVal ν c y t ↔ ¬LitTrue ν x s) := by
  obtain ⟨z, u, hz, hzne⟩ := hdiff
  have hlt : occLt x s z u := by
    by_contra h
    exact hzne (hup z u hz h)
  obtain ⟨y, t, hsucc⟩ := exists_succOcc_right hocc ⟨z, u, hz, hlt⟩
  refine ⟨y, t, hsucc, ?_⟩
  -- the occurrences strictly before the successor are those up to `(x, s)`
  have hbefore : ∀ z u, OccIn c z u → occLt z u y t → (LitTrue ν z u ↔ LitTrue ν x s) := by
    intro z u hz hlt'
    refine hup z u hz fun hgt => ?_
    rcases (succOcc_occLt_iff hsucc hz).mp hlt' with h | ⟨h₁, h₂⟩
    · exact occLt_asymm hgt h
    · subst h₁
      subst h₂
      exact occLt_irrefl _ _ hgt
  have huni : UniformBefore ν c y t := fun z u z' u' hz hz' hlt₁ hlt₂ =>
    (hbefore z u hz hlt₁).trans (hbefore z' u' hz' hlt₂).symm
  rw [linkVal_of_uniform huni, prefixOrStrict_succ hsucc]
  constructor
  · exact fun h hT => h ⟨x, s, hocc, Or.inr ⟨rfl, rfl⟩, hT⟩
  · rintro hT ⟨w, r, hw, hlt' | ⟨h₁, h₂⟩, hTw⟩
    · exact hT ((hup w r hw fun hgt => occLt_asymm hgt hlt').mp hTw)
    · subst h₁
      subst h₂
      exact hT hTw

/-- Correctness of the reduction, not-all-equal half: an ordered CNF structure
is not-all-equal satisfiable iff its width-three split is. -/
theorem naeSatisfiable_iff_map :
    NAESatisfiable A ↔ NAESatisfiable (satToThreeSat.Map A) := by
  constructor
  · -- a not-all-equal assignment extends to the split
    rintro ⟨ν, hν⟩
    refine ⟨naeSplitAssign ν, naeProper_of_occ ?_⟩
    rintro ⟨tc, wc⟩ hcl
    rw [isClause_iff] at hcl
    rcases hcl with ⟨s0, rfl, hocc⟩ | ⟨rfl, -, hemp⟩
    · -- a clause piece: its own literal, and one more of the opposite value
      have hclP : RelMap (M := satToThreeSat.Map A) satIsClause ![(SplitTag.piece s0, wc)] :=
        (isClause_iff _ _).mpr (Or.inl ⟨s0, rfl, hocc⟩)
      have hownOcc : OccIn (A := satToThreeSat.Map A) (SplitTag.piece s0, wc)
          (SplitTag.var, fun _ => wc 1) s0 := by
        refine ⟨hclP, ?_⟩
        cases s0 with
        | true => exact (posIn_iff _ _ _ _).mpr (Or.inl ⟨rfl, rfl, ⟨rfl, rfl⟩, hocc⟩)
        | false => exact (negIn_iff _ _ _ _).mpr (Or.inl ⟨rfl, rfl, ⟨rfl, rfl⟩, hocc⟩)
      have hval : LitTrue (naeSplitAssign ν)
          ((SplitTag.var, fun _ => wc 1) : satToThreeSat.Map A) s0 ↔
            LitTrue ν (wc 1) s0 := by
        cases s0 <;> exact Iff.rfl
      -- some occurrence of the clause disagrees with the literal of the piece
      have hdiff : ∃ z u, OccIn (wc 0) z u ∧ ¬(LitTrue ν z u ↔ LitTrue ν (wc 1) s0) := by
        obtain ⟨⟨z₁, u₁, h₁, hT₁⟩, ⟨z₂, u₂, h₂, hF₂⟩⟩ := naeProper_occ hν (wc 0) hocc.isCl
        by_cases hv : LitTrue ν (wc 1) s0
        · exact ⟨z₂, u₂, h₂, fun h => hF₂ (h.mpr hv)⟩
        · exact ⟨z₁, u₁, h₁, fun h => hv (h.mp hT₁)⟩
      have hother : ∃ (q : satToThreeSat.Map A) (u : Bool),
          OccIn (A := satToThreeSat.Map A) (SplitTag.piece s0, wc) q u ∧
            (LitTrue (naeSplitAssign ν) q u ↔ ¬LitTrue ν (wc 1) s0) := by
        -- the successor's linking variable, positively, when the values seen
        -- so far agree with the literal of the piece
        have succ_case : (∀ z u, OccIn (wc 0) z u → ¬occLt (wc 1) s0 z u →
              (LitTrue ν z u ↔ LitTrue ν (wc 1) s0)) →
            ∃ (q : satToThreeSat.Map A) (u : Bool),
              OccIn (A := satToThreeSat.Map A) (SplitTag.piece s0, wc) q u ∧
                (LitTrue (naeSplitAssign ν) q u ↔ ¬LitTrue ν (wc 1) s0) := by
          intro hup
          obtain ⟨y, t, hsucc, hlink⟩ := exists_succ_linkVal hocc hup hdiff
          refine ⟨(SplitTag.link t, ![wc 0, y]), true, ⟨hclP, ?_⟩, ?_⟩
          · exact (posIn_iff _ _ _ _).mpr
              (Or.inr ⟨s0, t, rfl, rfl, by simp, by simpa using hsucc⟩)
          · change LinkVal ν (![wc 0, y] 0) (![wc 0, y] 1) t ↔ ¬LitTrue ν (wc 1) s0
            simpa using hlink
        by_cases hch : Chained (wc 0) (wc 1) s0
        · by_cases huni : UniformBefore ν (wc 0) (wc 1) s0
          · by_cases hP : PrefixOrStrict ν (wc 0) (wc 1) s0 ↔ LitTrue ν (wc 1) s0
            · -- the value carried in agrees with the literal of the piece
              refine succ_case fun z u hz hnlt => ?_
              rcases occLt_trichotomy z u (wc 1) s0 with h | ⟨h₁, h₂⟩ | h
              · exact ⟨fun hT => hP.mp ⟨z, u, hz, h, hT⟩, fun hv => by
                  obtain ⟨w, r, hw, hltw, hTw⟩ := hP.mpr hv
                  exact (huni z u w r hz hw h hltw).mpr hTw⟩
              · subst h₁
                subst h₂
                exact Iff.rfl
              · exact absurd h hnlt
            · -- it does not: the piece's own linking variable, negatively
              refine ⟨(SplitTag.link s0, wc), false, ⟨hclP, ?_⟩, ?_⟩
              · exact (negIn_iff _ _ _ _).mpr (Or.inr ⟨s0, rfl, rfl, ⟨rfl, rfl⟩, hch⟩)
              · change ¬naeSplitAssign ν (SplitTag.link s0, wc) ↔ _
                rw [naeSplitAssign_link, linkVal_of_uniform huni]
                tauto
          · -- earlier occurrences already disagree: the linking variable
            -- repeats the literal of the piece, so its negation differs
            refine ⟨(SplitTag.link s0, wc), false, ⟨hclP, ?_⟩, ?_⟩
            · exact (negIn_iff _ _ _ _).mpr (Or.inr ⟨s0, rfl, rfl, ⟨rfl, rfl⟩, hch⟩)
            · change ¬naeSplitAssign ν (SplitTag.link s0, wc) ↔ _
              rw [naeSplitAssign_link]
              exact not_congr (linkVal_of_not_uniform huni)
        · -- the first occurrence of the clause: nothing is carried in
          have hmin : MinOcc (wc 0) (wc 1) s0 := by
            by_contra h
            exact hch ⟨hocc, h⟩
          refine succ_case fun z u hz hnlt => ?_
          rcases occLt_trichotomy z u (wc 1) s0 with h | ⟨h₁, h₂⟩ | h
          · exact absurd h (hmin.2 z u hz)
          · subst h₁
            subst h₂
            exact Iff.rfl
          · exact absurd h hnlt
      obtain ⟨q, u, hq, hqv⟩ := hother
      by_cases hv : LitTrue ν (wc 1) s0
      · exact ⟨⟨_, s0, hownOcc, hval.mpr hv⟩, ⟨q, u, hq, fun h => hqv.mp h hv⟩⟩
      · exact ⟨⟨q, u, hq, hqv.mpr hv⟩, ⟨_, s0, hownOcc, fun h => hv (hval.mp h)⟩⟩
    · -- an empty clause of the input has no literal at all
      obtain ⟨⟨z, u, hz, -⟩, -⟩ := naeProper_occ hν (wc 0) hemp.1
      exact absurd hz (hemp.2 z u)
  · -- a not-all-equal assignment of the split restricts to the input
    rintro ⟨μ, hμ⟩
    refine ⟨fun a => μ (SplitTag.var, fun _ => a), naeProper_of_occ fun c hcl => ⟨?_, ?_⟩⟩
    · -- a not-all-equal assignment is in particular a satisfying one
      exact exists_litTrue_of_map (fun p hp => (hμ p hp).1) hcl
    · -- and so is its flip, by the defining symmetry
      obtain ⟨x, s, hocc, hT⟩ :=
        exists_litTrue_of_map (ν' := fun p => ¬μ p)
          (fun p hp => by
            obtain ⟨q, hq⟩ := (hμ p hp).2
            rcases hq with ⟨hpos, hF⟩ | ⟨hneg, hT⟩
            · exact ⟨q, Or.inl ⟨hpos, hF⟩⟩
            · exact ⟨q, Or.inr ⟨hneg, not_not_intro hT⟩⟩)
          hcl
      exact ⟨x, s, hocc, litTrue_compl.mp hT⟩

/-- Correctness of the reduction: an ordered CNF structure is not-all-equal
satisfiable iff its width-three split is a yes-instance of NAE-3SAT. -/
theorem naeSatisfiable_iff_naeThreeSatisfiable (A : Type) [Language.sat.Structure A]
    [LinearOrder A] [Finite A] :
    NAESatisfiable A ↔ NAEThreeSatisfiable (satToThreeSat.Map A) := by
  rw [NAEThreeSatisfiable, and_iff_right widthAtMostThree_map]
  exact naeSatisfiable_iff_map

end NaeSatToNaeThreeSat

open NaeSatToNaeThreeSat SatToThreeSat in
/-- **NAE-SAT ordered-FO-reduces to NAE-3SAT.** 3SAT's clause-splitting
interpretation `SatToThreeSat.satToThreeSat`, applied unchanged: read as
not-all-equal clauses, the chain of pieces of a clause carries the value of
its first literal forward until an occurrence disagrees. -/
noncomputable def naeSat_ordered_fo_reduction_nae3Sat : NAESAT ≤ᶠᵒ[≤] NAE3SAT where
  Tag := SplitTag
  dim := 2
  toInterpretation := satToThreeSat
  correct A _ _ _ _ := naeSatisfiable_iff_naeThreeSatisfiable A

/-! ### NP-completeness -/

/-- NAE-3SAT is in NP: it FO-reduces to NAE-SAT, which is in NP. -/
theorem nae3Sat_mem_NP : NAE3SAT ∈ NP :=
  NP.mem_of_foReduction nae3Sat_fo_reduction_naeSat naeSat_mem_NP

/-- NAE-3SAT is NP-hard: NAE-SAT, which is NP-hard, reduces to it by an
ordered FO reduction. -/
theorem nae3Sat_NP_hard : NP.Hard NAE3SAT :=
  NP.hard_of_orderedReduction naeSat_ordered_fo_reduction_nae3Sat naeSat_NP_hard

/-- **NAE-3SAT is NP-complete**, derived from the first-order reductions of
this library and the Cook–Levin theorem. -/
theorem nae3Sat_NP_complete : NP.Complete NAE3SAT :=
  ⟨nae3Sat_mem_NP, nae3Sat_NP_hard⟩

end DescriptiveComplexity
