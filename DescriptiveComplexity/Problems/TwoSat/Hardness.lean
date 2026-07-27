/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderKrom
import DescriptiveComplexity.ClauseDischarge
import DescriptiveComplexity.Problems.TwoSat.Defs

/-!
# Hardness of 2SAT: the Krom discharge

Every SO-Krom definable problem admits an ordered first-order reduction to 2SAT
(`DescriptiveComplexity.twoSat_hard_of_sigmaSOKromDefinable`): the machine-free
NL-hardness statement, the Krom analogue of the Horn discharge of
`DescriptiveComplexity.Problems.HornSat.Hardness`.

The construction is the shared one of `DescriptiveComplexity.ClauseDischarge`: inside an
ordered input structure `A`,

* propositional variables: one per relation variable `i` of the block and per
  `B.arity i`-tuple over `A`, canonically padded to the common dimension
  `DescriptiveComplexity.clauseDim`;
* clauses: one per clause `c` of the program and per `k`-tuple over `A`
  satisfying the *guard* of `c` – guards are input-vocabulary formulas, hence
  evaluated in the input structure rather than encoded;
* literals: the two slots of `c`, each at the canonically padded tuple of its
  atom's arguments, occurring positively or negatively according to the slot's
  sign.

Only the last point differs from the Horn discharge, which reads a head and a
body list instead of two signed slots. The consequence is the one that matters:
a clause of the program has at most two literals, and canonical padding makes
the element encoding each of them unique, so every interpreted clause has at
most two literal occurrences
(`DescriptiveComplexity.KromDischarge.krom_widthAtMostTwo`) – the output lands in 2SAT
rather than merely in SAT, exactly as the Horn discharge's output is Horn.

Both directions of correctness
(`DescriptiveComplexity.KromDischarge.krom_satisfiable_iff`) read through the canonical
padding: an assignment `ρ` of the block gives the truth value `ρ i (pref x)` of
the propositional variable `(i, x)`, and conversely a satisfying truth
assignment `ν` gives the assignment `ρ i ā := ν (i, pad ā)`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace KromDischarge

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### Tags and clause access -/

/-- The tags of the Krom interpretation: the generic clausal tags at the
program's number of clauses. -/
abbrev KromTag (prog : KromProgram (L.sum Language.order) B k) : Type :=
  ClauseTag prog.length B

/-- The `c`-th clause of the program. -/
abbrev clauseAt (prog : KromProgram (L.sum Language.order) B k) (c : Fin prog.length) :
    KromClause (L.sum Language.order) B k :=
  prog[(c : ℕ)]'c.isLt

/-- The two literal slots of a clause, as a list – the shape both the defining
formulas and the correctness proof quantify over. -/
def slots (c : KromClause (L.sum Language.order) B k) : List (Option (KromLit B k)) :=
  [c.lit₁, c.lit₂]

theorem mem_slots_lit₁ (c : KromClause (L.sum Language.order) B k) : c.lit₁ ∈ slots c := by
  simp [slots]

theorem mem_slots_lit₂ (c : KromClause (L.sum Language.order) B k) : c.lit₂ ∈ slots c := by
  simp [slots]

theorem slots_cases {c : KromClause (L.sum Language.order) B k}
    {o : Option (KromLit B k)} (h : o ∈ slots c) : o = c.lit₁ ∨ o = c.lit₂ := by
  simpa [slots] using h

/-! ### The defining formulas of the literals -/

section Formulas

variable {γ : Type}

open Classical in
/-- The occurrence formula of one literal slot, at a given sign: the slot's
literal carries that sign, is an atom of the relation variable `i`, and the
coordinates selected by `x` hold the canonically padded tuple of its
arguments. -/
noncomputable def slotOccF (o : Option (KromLit B k)) (pos : Bool) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  o.elim ⊥ fun l => if l.positive = pos ∧ l.atom.idx = i then atomOccF l.atom u x else ⊥

/-- The occurrence formula of a clause at a given sign: either of its two
slots. -/
noncomputable def litOccF (c : KromClause (L.sum Language.order) B k) (pos : Bool) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  slotOccF c.lit₁ pos i u x ⊔ slotOccF c.lit₂ pos i u x

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

theorem realize_slotOccF {o : Option (KromLit B k)} {pos : Bool} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (slotOccF (L := L) o pos i u x).Realize v ↔
      ∃ l ∈ o, l.positive = pos ∧ l.atom.idx = i ∧
        PadTup (atomIdx l.atom) (fun j => v (u j)) fun j => v (x j) := by
  classical
  rw [slotOccF]
  cases ho : o with
  | none =>
    rw [Option.elim_none]
    refine iff_of_false id ?_
    rintro ⟨l, hl, -⟩
    simp at hl
  | some l =>
    rw [Option.elim_some]
    by_cases hc : l.positive = pos ∧ l.atom.idx = i
    · rw [if_pos hc, realize_atomOccF]
      refine ⟨fun h => ⟨l, rfl, hc.1, hc.2, h⟩, ?_⟩
      rintro ⟨l', hl', -, -, h⟩
      have hle := Option.mem_def.mp hl'
      rw [Option.some.injEq] at hle
      subst hle
      exact h
    · rw [if_neg hc]
      refine iff_of_false id ?_
      rintro ⟨l', hl', hpos, hidx, -⟩
      have hle := Option.mem_def.mp hl'
      rw [Option.some.injEq] at hle
      subst hle
      exact hc ⟨hpos, hidx⟩

theorem realize_litOccF {c : KromClause (L.sum Language.order) B k} {pos : Bool} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (litOccF (L := L) c pos i u x).Realize v ↔
      ∃ o ∈ slots c, ∃ l ∈ o, l.positive = pos ∧ l.atom.idx = i ∧
        PadTup (atomIdx l.atom) (fun j => v (u j)) fun j => v (x j) := by
  rw [litOccF, Formula.realize_sup, realize_slotOccF, realize_slotOccF]
  constructor
  · rintro (h | h)
    · exact ⟨c.lit₁, mem_slots_lit₁ c, h⟩
    · exact ⟨c.lit₂, mem_slots_lit₂ c, h⟩
  · rintro ⟨o, ho, h⟩
    rcases slots_cases ho with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

end Formulas

/-! ### The interpretation -/

/-- The Krom interpretation: the CNF instance of the propositional translation
of the program, defined inside the ordered input structure. -/
noncomputable def kromInterp (prog : KromProgram (L.sum Language.order) B k) :
    FOInterpretation (L.sum Language.order) Language.sat (KromTag prog) (clauseDim B k) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        match t 0 with
        | Sum.inl (Sum.inl c) =>
            guardF (clauseAt prog c).guard (fun j => ((0 : Fin 1), j)) ⊓
              canonF k fun j => ((0 : Fin 1), j)
        | _ => ⊥
    | _, .posIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            litOccF (clauseAt prog c) true i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥
    | _, .negIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            litOccF (clauseAt prog c) false i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥

/-! ### Characterization of the interpreted relations

Every statement below is the corresponding realization lemma read through
`DescriptiveComplexity.FOInterpretation.relMap_map`; the tag combinations that are not
listed have `⊥` as defining formula, so the corresponding relation is empty. -/

section Characterizations

variable {A : Type} [L.Structure A] [LinearOrder A]
variable {prog : KromProgram (L.sum Language.order) B k}

/-- **The clause elements**: one per clause of the program and per canonically
padded tuple satisfying that clause's guard. -/
theorem krom_isClause_cl (c : Fin prog.length) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (kromInterp prog).Map A) satIsClause ![(clTag c, w)] ↔
      (clauseAt prog c).guard.Realize (fun j => w (Fin.castLE le_clauseDim j)) ∧ Canon k w := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_inf.trans (and_congr realize_guardF realize_canonF)

/-- Elements carrying a variable tag are not clauses. -/
theorem krom_not_isClause_var (i : B.ι) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (kromInterp prog).Map A) satIsClause ![(varTag i, w)] :=
  id

/-- Elements carrying the junk tag are not clauses. -/
theorem krom_not_isClause_junk (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (kromInterp prog).Map A) satIsClause
      ![((Sum.inr () : KromTag prog), w)] :=
  id

/-- **The positive literals**: a slot of the clause carrying a positive
literal, at the canonically padded tuple of its atom's arguments. -/
theorem krom_posIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (kromInterp prog).Map A) satPosIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ o ∈ slots (clauseAt prog c), ∃ l ∈ o,
        l.positive = true ∧ l.atom.idx = i ∧ PadTup (atomIdx l.atom) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_litOccF

/-- **The negative literals**: a slot of the clause carrying a negated literal,
at the canonically padded tuple of its atom's arguments. -/
theorem krom_negIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (kromInterp prog).Map A) satNegIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ o ∈ slots (clauseAt prog c), ∃ l ∈ o,
        l.positive = false ∧ l.atom.idx = i ∧ PadTup (atomIdx l.atom) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_litOccF

end Characterizations

/-! ### The output is width-two, and correct -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable (prog : KromProgram (L.sum Language.order) B k)

/-- The propositional variable standing for the atom of a literal, at a clause
tuple. -/
noncomputable def slotPt (a₀ : A) (l : KromLit B k) (u : Fin (clauseDim B k) → A) :
    (kromInterp prog).Map A :=
  (varTag l.atom.idx, pad a₀ fun j => u (atomIdx l.atom j))

omit [Finite A] [Nonempty A] in
/-- **Every occurrence of an interpreted clause comes from one of its two
slots**, at the canonical point of that slot's atom and with that slot's
sign. -/
theorem krom_occ_cases {a₀ : A} (ha₀ : IsBot a₀) (c : Fin prog.length)
    (u : Fin (clauseDim B k) → A) (p : (kromInterp prog).Map A) (t : Bool)
    (hocc : OccIn (A := (kromInterp prog).Map A) (clTag c, u) p t) :
    ∃ o ∈ slots (clauseAt prog c), ∃ l ∈ o,
      t = l.positive ∧ p = slotPt prog a₀ l u := by
  obtain ⟨tx, x⟩ := p
  rcases tx with (c' | i') | ⟨⟩
  · cases t with
    | false => exact hocc.2.elim
    | true => exact hocc.2.elim
  · have hocc' :
        ∃ o ∈ slots (clauseAt prog c), ∃ l ∈ o,
          l.positive = t ∧ l.atom.idx = i' ∧ PadTup (atomIdx l.atom) u x := by
      cases t with
      | false => exact (krom_negIn_cl_var c i' u x).mp hocc.2
      | true => exact (krom_posIn_cl_var c i' u x).mp hocc.2
    obtain ⟨o, ho, l, hl, hpos, hidx, hpad⟩ := hocc'
    refine ⟨o, ho, l, hl, hpos.symm, ?_⟩
    rw [slotPt]
    refine Prod.ext_iff.mpr ⟨?_, eq_pad_of_padTup ha₀ hpad⟩
    exact congrArg (fun j => (varTag j : KromTag prog)) hidx.symm
  · cases t with
    | false => exact hocc.2.elim
    | true => exact hocc.2.elim

/-- **The interpretation always lands in 2SAT**: a clause of the program has at
most two literals, and canonical padding makes the element encoding each of them
unique, so every interpreted clause has at most two literal occurrences. -/
theorem krom_widthAtMostTwo : WidthAtMostTwo ((kromInterp prog).Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rintro ⟨tc, u⟩ x s hocc
  rcases tc with (c | i) | ⟨⟩
  · -- each occurrence comes from the first or the second slot
    choose o ho l hl hs hx using fun m : Fin 3 =>
      krom_occ_cases prog ha₀ c u (x m) (s m) (hocc m)
    have hcases : ∀ m : Fin 3, o m = (clauseAt prog c).lit₁ ∨ o m = (clauseAt prog c).lit₂ :=
      fun m => slots_cases (ho m)
    have hslot : ∃ m n : Fin 3, m ≠ n ∧ o m = o n := by
      rcases hcases 0 with h0 | h0 <;> rcases hcases 1 with h1 | h1 <;>
        rcases hcases 2 with h2 | h2
      exacts [⟨0, 1, by decide, h0.trans h1.symm⟩, ⟨0, 1, by decide, h0.trans h1.symm⟩,
        ⟨0, 2, by decide, h0.trans h2.symm⟩, ⟨1, 2, by decide, h1.trans h2.symm⟩,
        ⟨1, 2, by decide, h1.trans h2.symm⟩, ⟨0, 2, by decide, h0.trans h2.symm⟩,
        ⟨0, 1, by decide, h0.trans h1.symm⟩, ⟨0, 1, by decide, h0.trans h1.symm⟩]
    obtain ⟨m, n, hmn, hon⟩ := hslot
    -- two occurrences from the same slot have the same literal, hence coincide
    have hlmn : l m = l n := by
      have h1 := Option.mem_def.mp (hl m)
      have h2 := Option.mem_def.mp (hl n)
      rw [hon, h2, Option.some.injEq] at h1
      exact h1.symm
    refine ⟨m, n, hmn, ?_, ?_⟩
    · rw [hx m, hx n, hlmn]
    · rw [hs m, hs n, hlmn]
  · exact absurd (hocc 0).1 (krom_not_isClause_var i u)
  · exact absurd (hocc 0).1 (krom_not_isClause_junk u)

/-- **Correctness of the Krom discharge**: the program has a satisfying
assignment iff the interpreted CNF is satisfiable. -/
theorem krom_satisfiable_iff :
    (∃ ρ : B.Assignment A, prog.Holds ρ) ↔ Satisfiable ((kromInterp prog).Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun z =>
      match z with
      | (Sum.inl (Sum.inr i), y) => ρ i (pref (arity_le_clauseDim (k := k) i) y)
      | _ => False, ?_⟩
    rintro ⟨tc, u⟩ hc
    rcases tc with (c | i) | ⟨⟩
    · obtain ⟨hguard, -⟩ := (krom_isClause_cl c u).mp hc
      -- the truth value of the propositional variable encoding an atom
      have hval : ∀ a : SOAtom B k,
          ρ a.idx (pref (arity_le_clauseDim (k := k) a.idx) (pad a₀ fun j => u (atomIdx a j))) ↔
            a.Holds ρ fun j => u (Fin.castLE le_clauseDim j) := by
        intro a
        rw [pref_pad]
        exact Iff.rfl
      -- the clause of the program holds at the tuple, so one of its slots does
      have hcl := hρ (fun j => u (Fin.castLE le_clauseDim j)) (clauseAt prog c)
        (List.getElem_mem c.isLt) hguard
      obtain ⟨o, ho, l, hl, hlT⟩ : ∃ o ∈ slots (clauseAt prog c), ∃ l ∈ o,
          l.Holds ρ fun j => u (Fin.castLE le_clauseDim j) := by
        rcases hcl with h | h
        · exact ⟨_, mem_slots_lit₁ _, KromLit.slotHolds_iff.mp h⟩
        · exact ⟨_, mem_slots_lit₂ _, KromLit.slotHolds_iff.mp h⟩
      refine ⟨slotPt prog a₀ l u, ?_⟩
      rw [KromLit.Holds] at hlT
      cases hpos : l.positive with
      | false =>
        simp only [hpos, Bool.false_eq_true, if_false] at hlT
        refine Or.inr ⟨?_, ?_⟩
        · exact (krom_negIn_cl_var c l.atom.idx u _).mpr
            ⟨o, ho, l, hl, hpos, rfl, padTup_pad ha₀ _ u⟩
        · exact fun h => hlT ((hval l.atom).mp h)
      | true =>
        simp only [hpos, if_true] at hlT
        refine Or.inl ⟨?_, ?_⟩
        · exact (krom_posIn_cl_var c l.atom.idx u _).mpr
            ⟨o, ho, l, hl, hpos, rfl, padTup_pad ha₀ _ u⟩
        · exact (hval l.atom).mpr hlT
    · exact absurd hc (krom_not_isClause_var i u)
    · exact absurd hc (krom_not_isClause_junk u)
  · rintro ⟨ν, hν⟩
    refine ⟨fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā), fun v c hc => ?_⟩
    obtain ⟨n, hn, hci⟩ := List.getElem_of_mem hc
    subst hci
    intro hguard
    have hcl : RelMap (M := (kromInterp prog).Map A) satIsClause
        ![((clTag ⟨n, hn⟩ : KromTag prog), pad a₀ v)] := by
      refine (krom_isClause_cl ⟨n, hn⟩ (pad a₀ v)).mpr ⟨?_, canon_pad ha₀ k v⟩
      rw [show (fun j => pad (D := clauseDim B k) a₀ v (Fin.castLE le_clauseDim j)) = v from
        pref_pad a₀ le_clauseDim v]
      exact hguard
    -- the truth value of the point of a slot is the truth value of its atom
    have hpt : ∀ l : KromLit B k,
        ν (slotPt prog a₀ l (pad a₀ v)) ↔
          l.atom.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v := by
      intro l
      have hkey : (fun j => pad (D := clauseDim B k) a₀ v (atomIdx l.atom j)) =
          fun j => v (l.atom.args j) :=
        funext fun j => congrFun (pref_pad a₀ le_clauseDim v) (l.atom.args j)
      change ν ((varTag l.atom.idx : KromTag prog), pad a₀ fun j => pad a₀ v (atomIdx l.atom j)) ↔
        ν ((varTag l.atom.idx : KromTag prog), pad a₀ fun j => v (l.atom.args j))
      rw [hkey]
    -- a literal is true at its point iff it holds under the induced assignment
    have hbridge : ∀ l : KromLit B k,
        l.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v ↔
          LitTrue ν (slotPt prog a₀ l (pad a₀ v)) l.positive := by
      intro l
      cases hpos : l.positive with
      | false =>
        have h1 : l.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v ↔
            ¬l.atom.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v := by
          simp [KromLit.Holds, hpos]
        have h2 : LitTrue ν (slotPt prog a₀ l (pad a₀ v)) false ↔
            ¬ν (slotPt prog a₀ l (pad a₀ v)) := by
          simp [LitTrue]
        rw [h1, h2]
        exact not_congr (hpt l).symm
      | true =>
        have h1 : l.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v ↔
            l.atom.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v := by
          simp [KromLit.Holds, hpos]
        have h2 : LitTrue ν (slotPt prog a₀ l (pad a₀ v)) true ↔
            ν (slotPt prog a₀ l (pad a₀ v)) := by
          simp [LitTrue]
        rw [h1, h2]
        exact (hpt l).symm
    have key : ∀ (t : Bool) (p : (kromInterp prog).Map A),
        OccIn (A := (kromInterp prog).Map A) (clTag ⟨n, hn⟩, pad a₀ v) p t → LitTrue ν p t →
        KromLit.slotHolds (clauseAt prog ⟨n, hn⟩).lit₁
            (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v ∨
          KromLit.slotHolds (clauseAt prog ⟨n, hn⟩).lit₂
            (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v := by
      intro t p hocc hlt
      obtain ⟨o, ho, l, hl, hts, hpp⟩ := krom_occ_cases prog ha₀ ⟨n, hn⟩ (pad a₀ v) p t hocc
      have hlH : l.Holds (fun i ā => ν ((varTag i : KromTag prog), pad a₀ ā)) v := by
        refine (hbridge l).mpr ?_
        rw [← hpp, ← hts]
        exact hlt
      rcases slots_cases ho with rfl | rfl
      · exact Or.inl (KromLit.slotHolds_iff.mpr ⟨l, hl, hlH⟩)
      · exact Or.inr (KromLit.slotHolds_iff.mpr ⟨l, hl, hlH⟩)
    obtain ⟨p, hp⟩ := hν _ hcl
    rcases hp with ⟨hpos, hνp⟩ | ⟨hneg, hνp⟩
    · exact key true p ⟨hcl, hpos⟩ hνp
    · exact key false p ⟨hcl, hneg⟩ hνp

/-- The program has a satisfying assignment iff the interpreted CNF is a
yes-instance of 2SAT. -/
theorem krom_twoSatisfiable_iff :
    (∃ ρ : B.Assignment A, prog.Holds ρ) ↔ TwoSatisfiable ((kromInterp prog).Map A) := by
  rw [TwoSatisfiable, and_iff_right (krom_widthAtMostTwo prog)]
  exact krom_satisfiable_iff prog

end Correctness

/-- **The generic Krom reduction**: an ordered first-order reduction to 2SAT
from any problem defined, on nonempty finite structures, by an existential
second-order sentence with a Krom kernel. -/
noncomputable def kromReduction (prog : KromProgram (L.sum Language.order) B k)
    (Q : DecisionProblem L)
    (hQ : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      Q A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ) : Q ≤ᶠᵒ[≤] TwoSAT where
  Tag := KromTag prog
  dim := clauseDim B k
  toInterpretation := kromInterp prog
  correct A _ _ _ _ := (hQ A).trans (krom_twoSatisfiable_iff prog)

end KromDischarge

open KromDischarge in
/-- **NL-hardness of 2SAT, machine-free**: every SO-Krom definable problem
admits an ordered first-order reduction to 2SAT. This is the Krom analogue of
the Horn discharge `DescriptiveComplexity.hornSat_hard_of_sigmaSOHornDefinable`, and of
the Cook–Levin discharge above it: the clause list of the program is emitted
directly, one 2-clause per clause and per instantiation of its universally
quantified variables satisfying its guard. -/
theorem twoSat_hard_of_sigmaSOKromDefinable :
    ∀ {L : Language.{0, 0}} (Q : DecisionProblem L),
      SigmaSOKromDefinable Q → Nonempty (Q ≤ᶠᵒ[≤] TwoSAT) := by
  rintro L Q ⟨B, k, prog, hprog⟩
  exact ⟨kromReduction prog Q hprog⟩

end DescriptiveComplexity
