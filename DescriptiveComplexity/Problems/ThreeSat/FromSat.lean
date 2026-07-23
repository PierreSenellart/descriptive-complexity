/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.Problems.ThreeSat.Defs

/-!
# SAT reduces to 3SAT by an ordered FO reduction

The classical clause-splitting reduction, as an ordered first-order
reduction – `DescriptiveComplexity.sat_ordered_fo_reduction_threeSat : SAT ≤ᶠᵒ[≤]
ThreeSAT`. Every clause of the input CNF is split along the linear order of
its literal occurrences (`DescriptiveComplexity.OccurrenceOrder`) into a chain of
clauses of width at most three, linked by fresh variables.

Concretely, the interpretation (`DescriptiveComplexity.SatToThreeSat.satToThreeSat`,
tags `SplitTag`, dimension 2) produces, for each occurrence `(x, s)` of a
clause `c`:

* a linking variable `(.link s, (c, x))`, intended to mean “no occurrence of
  `c` strictly before `(x, s)` is true”;
* a clause piece `(.piece s, (c, x))` containing the literal `(x, s)` itself
  (on the variable copy `(.var, (x, x))`), the linking variable of the
  *successor* occurrence positively (if any), and its own linking variable
  negatively (if the occurrence is not the first): at most three literals.

For a clause with occurrences `ℓ₁ < ⋯ < ℓₖ`, this yields the usual chain
`(ℓ₁ ∨ y₂), (¬y₂ ∨ ℓ₂ ∨ y₃), …, (¬yₖ ∨ ℓₖ)`. Empty input clauses are copied
as empty clauses `(.empty, (c, c))`, keeping the output unsatisfiable. All
other tuples are junk: they are neither clauses nor occur in any clause.

The two halves of correctness are `SatToThreeSat.widthAtMostThree_map` (the
output always satisfies the width promise – each piece has at most three
literals, by uniqueness of the successor occurrence) and
`SatToThreeSat.satisfiable_iff_map` (satisfiability is preserved, by the
usual chain argument, threaded along the occurrence order).
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatToThreeSat

open Language Structure SatOcc

/-- Tags for the clause-splitting interpretation of 3SAT instances in ordered
CNF instances. -/
inductive SplitTag : Type
  /-- `(.var, (x, x))` is the copy of the propositional variable `x`. -/
  | var
  /-- `(.link s, (c, x))` is the fresh linking variable of the occurrence
  `(x, s)` of the clause `c`. -/
  | link (s : Bool)
  /-- `(.piece s, (c, x))` is the clause piece of the occurrence `(x, s)` of
  the clause `c`. -/
  | piece (s : Bool)
  /-- `(.empty, (c, c))` is the copy of the empty clause `c`. -/
  | empty
  deriving DecidableEq, Fintype, Nonempty

/-- Defining formula for `satIsClause`: clause pieces sit on occurrences,
empty-clause copies on diagonal pairs carrying an empty clause. -/
noncomputable def isClauseF : SplitTag → satOrd.Formula (Fin 1 × Fin 2)
  | .piece s => occF s (0, 0) (0, 1)
  | .empty => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | _ => ⊥

/-- Defining formula for `satPosIn`: the piece of a positive occurrence
contains its literal positively, and every piece contains the linking
variable of the successor occurrence (if any) positively. -/
noncomputable def posInF : SplitTag → SplitTag → satOrd.Formula (Fin 2 × Fin 2)
  | .piece true, .var => eqF (1, 0) (1, 1) ⊓ eqF (1, 0) (0, 1) ⊓ occF true (0, 0) (0, 1)
  | .piece s, .link t => eqF (0, 0) (1, 0) ⊓ succOccF s t (0, 0) (0, 1) (1, 1)
  | _, _ => ⊥

/-- Defining formula for `satNegIn`: the piece of a negative occurrence
contains its literal negatively, and the piece of a non-first occurrence
contains its own linking variable negatively. -/
noncomputable def negInF : SplitTag → SplitTag → satOrd.Formula (Fin 2 × Fin 2)
  | .piece false, .var => eqF (1, 0) (1, 1) ⊓ eqF (1, 0) (0, 1) ⊓ occF false (0, 0) (0, 1)
  | .piece s, .link t =>
      if t = s then eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1) ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | _, _ => ⊥

/-- The first-order interpretation producing, from an ordered CNF structure,
its width-three split. -/
noncomputable def satToThreeSat : FOInterpretation satOrd Language.sat SplitTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => isClauseF (t 0)
    | _, .posIn => fun t => posInF (t 0) (t 1)
    | _, .negIn => fun t => negInF (t 0) (t 1)

/-! ### Characterizations of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

@[simp]
theorem isClause_iff (t : SplitTag) (w : Fin 2 → A) :
    RelMap (M := satToThreeSat.Map A) satIsClause ![(t, w)] ↔
      (∃ s, t = .piece s ∧ OccIn (w 0) (w 1) s) ∨
        (t = .empty ∧ w 0 = w 1 ∧ EmptyCl (w 0)) := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [satToThreeSat, isClauseF]

@[simp]
theorem posIn_iff (t₁ t₂ : SplitTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := satToThreeSat.Map A) satPosIn ![(t₁, w₁), (t₂, w₂)] ↔
      (t₁ = .piece true ∧ t₂ = .var ∧
        (w₂ 0 = w₂ 1 ∧ w₂ 0 = w₁ 1) ∧ OccIn (w₁ 0) (w₁ 1) true) ∨
      (∃ s t, t₁ = .piece s ∧ t₂ = .link t ∧
        w₁ 0 = w₂ 0 ∧ SuccOcc (w₁ 0) (w₁ 1) s (w₂ 1) t) := by
  rw [FOInterpretation.relMap_map]
  cases t₁ with
  | var => cases t₂ <;> simp [satToThreeSat, posInF]
  | link s => cases t₂ <;> simp [satToThreeSat, posInF]
  | empty => cases t₂ <;> simp [satToThreeSat, posInF]
  | piece s =>
    cases t₂ with
    | var => cases s <;> simp [satToThreeSat, posInF, and_assoc]
    | link t => simp [satToThreeSat, posInF, and_assoc]
    | piece t => simp [satToThreeSat, posInF]
    | empty => simp [satToThreeSat, posInF]

@[simp]
theorem negIn_iff (t₁ t₂ : SplitTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := satToThreeSat.Map A) satNegIn ![(t₁, w₁), (t₂, w₂)] ↔
      (t₁ = .piece false ∧ t₂ = .var ∧
        (w₂ 0 = w₂ 1 ∧ w₂ 0 = w₁ 1) ∧ OccIn (w₁ 0) (w₁ 1) false) ∨
      (∃ s, t₁ = .piece s ∧ t₂ = .link s ∧
        (w₁ 0 = w₂ 0 ∧ w₁ 1 = w₂ 1) ∧ Chained (w₁ 0) (w₁ 1) s) := by
  rw [FOInterpretation.relMap_map]
  cases t₁ with
  | var => cases t₂ <;> simp [satToThreeSat, negInF]
  | link s => cases t₂ <;> simp [satToThreeSat, negInF]
  | empty => cases t₂ <;> simp [satToThreeSat, negInF]
  | piece s =>
    cases t₂ with
    | var => cases s <;> simp [satToThreeSat, negInF, and_assoc]
    | link t =>
      rcases eq_or_ne t s with rfl | h
      · simp [satToThreeSat, negInF, and_assoc]
      · simp [satToThreeSat, negInF, h]
    | piece t => simp [satToThreeSat, negInF]
    | empty => simp [satToThreeSat, negInF]

end Characterizations

/-! ### The width bound -/

section Width

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- Extensionality for pairs over `Fin 2`, stated with `exact`-friendly
components. -/
private theorem ext2 {B : Type} (w w' : Fin 2 → B) (h0 : w 0 = w' 0) (h1 : w 1 = w' 1) :
    w = w' := by
  funext k
  fin_cases k
  · exact h0
  · exact h1

/-- Congruence for pairs, at raw product type. -/
private theorem pair_congr {B C : Type} {t t' : B} {w w' : C} (h1 : t = t') (h2 : w = w') :
    (t, w) = (t', w') := by
  rw [h1, h2]

/-- The interpreted structure always satisfies the width promise of 3SAT:
every clause piece has at most three literal occurrences (its own literal, the
successor's linking variable – unique by `succOcc_right_unique` – and its own
linking variable), and empty-clause copies have none. -/
theorem widthAtMostThree_map : WidthAtMostThree (satToThreeSat.Map A) := by
  rintro ⟨tc, wc⟩ x s hocc
  -- split each occurrence element into its components
  have hx : ∀ i, ∃ t w, x i = (t, w) := fun i => ⟨(x i).1, (x i).2, rfl⟩
  choose tx wx hx using hx
  have hocc' : ∀ i, OccIn (A := satToThreeSat.Map A) (tc, wc) (tx i, wx i) (s i) := by
    intro i
    have h := hocc i
    rwa [hx i] at h
  -- occurrences sit only on clause pieces
  cases tc with
  | var =>
    have h : RelMap (M := satToThreeSat.Map A) satIsClause ![(SplitTag.var, wc)] :=
      (hocc' 0).isCl
    rw [isClause_iff] at h
    simp at h
  | link s' =>
    have h : RelMap (M := satToThreeSat.Map A) satIsClause ![(SplitTag.link s', wc)] :=
      (hocc' 0).isCl
    rw [isClause_iff] at h
    simp at h
  | empty =>
    have h := hocc' 0
    cases hs0 : s 0 with
    | false =>
      rw [hs0] at h
      have hsign : RelMap (M := satToThreeSat.Map A) satNegIn
          ![(SplitTag.empty, wc), (tx 0, wx 0)] := h.2
      rw [negIn_iff] at hsign
      simp at hsign
    | true =>
      rw [hs0] at h
      have hsign : RelMap (M := satToThreeSat.Map A) satPosIn
          ![(SplitTag.empty, wc), (tx 0, wx 0)] := h.2
      rw [posIn_iff] at hsign
      simp at hsign
  | piece s0 =>
    -- classify the occurrences of the piece into three shapes
    have classify : ∀ i,
        (tx i = .var ∧ wx i = (fun _ => wc 1) ∧ s i = s0) ∨
        (∃ t, tx i = .link t ∧ wx i 0 = wc 0 ∧
          SuccOcc (wc 0) (wc 1) s0 (wx i 1) t ∧ s i = true) ∨
        (tx i = .link s0 ∧ wx i = wc ∧ s i = false) := by
      intro i
      have h := hocc' i
      cases hsi : s i with
      | true =>
        rw [hsi] at h
        have hsign : RelMap (M := satToThreeSat.Map A) satPosIn
            ![(SplitTag.piece s0, wc), (tx i, wx i)] := h.2
        rw [posIn_iff] at hsign
        rcases hsign with ⟨hpc, hvar, ⟨hd, he⟩, -⟩ | ⟨s', t', hpc, hlink, hce, hsucc⟩
        · obtain rfl : s0 = true := by simpa using hpc
          exact Or.inl ⟨hvar, ext2 _ _ he (hd.symm.trans he), rfl⟩
        · have heq : s0 = s' := by simpa using hpc
          refine Or.inr (Or.inl ⟨t', hlink, hce.symm, ?_, rfl⟩)
          rw [heq]
          exact hsucc
      | false =>
        rw [hsi] at h
        have hsign : RelMap (M := satToThreeSat.Map A) satNegIn
            ![(SplitTag.piece s0, wc), (tx i, wx i)] := h.2
        rw [negIn_iff] at hsign
        rcases hsign with ⟨hpc, hvar, ⟨hd, he⟩, -⟩ | ⟨s', hpc, hlink, ⟨h0, h1⟩, -⟩
        · obtain rfl : s0 = false := by simpa using hpc
          exact Or.inl ⟨hvar, ext2 _ _ he (hd.symm.trans he), rfl⟩
        · have heq : s0 = s' := by simpa using hpc
          refine Or.inr (Or.inr ⟨?_, ext2 _ _ h0.symm h1.symm, rfl⟩)
          rw [heq]
          exact hlink
    -- pigeonhole: two of the four occurrences have the same shape
    have pigeon : ∀ g : Fin 4 → Fin 3, ∃ i j, i ≠ j ∧ g i = g j := by decide
    obtain ⟨i, j, hij, hg⟩ :=
      pigeon fun i => if tx i = .var then 0 else if s i then 1 else 2
    refine ⟨i, j, hij, ?_⟩
    -- same shape forces the same occurrence; different shapes contradict the
    -- shape collision `hg`
    rcases classify i with ⟨hti, hwi, hsi⟩ | ⟨ti, hti, hw0i, hsucci, hsi⟩ | ⟨hti, hwi, hsi⟩ <;>
        rcases classify j with ⟨htj, hwj, hsj⟩ | ⟨tj, htj, hw0j, hsuccj, hsj⟩ |
          ⟨htj, hwj, hsj⟩ <;>
        simp only [hti, htj, hsi, hsj] at hg
    · -- both on the variable copy
      refine ⟨((hx i).trans ?_).trans (hx j).symm, hsi.trans hsj.symm⟩
      exact pair_congr (hti.trans htj.symm) (hwi.trans hwj.symm)
    · simp at hg
    · simp at hg
    · simp at hg
    · -- both on the successor's linking variable
      obtain ⟨hw1, ht⟩ := succOcc_right_unique hsucci hsuccj
      refine ⟨((hx i).trans ?_).trans (hx j).symm, hsi.trans hsj.symm⟩
      refine pair_congr (hti.trans ((congrArg SplitTag.link ht).trans htj.symm)) ?_
      exact ext2 _ _ (hw0i.trans hw0j.symm) hw1
    · simp at hg
    · simp at hg
    · simp at hg
    · -- both on the own linking variable
      refine ⟨((hx i).trans ?_).trans (hx j).symm, hsi.trans hsj.symm⟩
      exact pair_congr (hti.trans htj.symm) (hwi.trans hwj.symm)

end Width

/-! ### Preservation of satisfiability -/

section Satisfiability

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The assignment of the interpreted structure induced by an assignment of
the input: variable copies follow `ν`, and the linking variable of an
occurrence states that no earlier occurrence of its clause is true. -/
def splitAssign (ν : A → Prop) : SplitTag × (Fin 2 → A) → Prop
  | (.var, w) => ν (w 0)
  | (.link s, w) => ¬PrefixOrStrict ν (w 0) (w 1) s
  | _ => False

variable [Finite A]

/-- The chain argument of the reduction, isolated in the form its
not-all-equal variant reuses (`DescriptiveComplexity.NaeSatToNaeThreeSat`): if an
assignment of the split gives every output clause a true literal, then, read on
the variable copies, it gives every clause of the input a true literal. -/
theorem exists_litTrue_of_map {ν' : satToThreeSat.Map A → Prop}
    (hν' : ∀ c : satToThreeSat.Map A, RelMap satIsClause ![c] → ∃ x : satToThreeSat.Map A,
      (RelMap satPosIn ![c, x] ∧ ν' x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν' x))
    {c : A} (hcl : IsCl c) :
    ∃ x s, OccIn c x s ∧ LitTrue (fun a => ν' (.var, fun _ => a)) x s := by
  by_contra hno
  -- every literal of `c` is false under the restricted assignment
  have Hfalse : ∀ z u, OccIn c z u → ¬LitTrue (fun a => ν' (.var, fun _ => a)) z u :=
    fun z u hz hT => hno ⟨z, u, hz, hT⟩
  -- congruence of the assignment, at raw product type
  have hcongr : ∀ (g : SplitTag × (Fin 2 → A) → Prop)
      (p q : SplitTag × (Fin 2 → A)), p = q → g p → g q :=
    fun g p q h hg => h ▸ hg
  by_cases hocc : ∃ z u, OccIn c z u
  · -- the linking variables of the chained occurrences of `c` are all
    -- forced true, from first to last
    have step : ∀ x s, OccIn c x s → Chained c x s →
        (∀ y t, OccIn c y t → Chained c y t → occLt y t x s →
          ν' (.link t, ![c, y])) →
        ν' (.link s, ![c, x]) := by
      intro x s hxs hch IH
      obtain ⟨z, u, hsucc⟩ := exists_succOcc hch
      have hclz : RelMap (M := satToThreeSat.Map A) satIsClause
          ![(SplitTag.piece u, ![c, z])] := by
        rw [isClause_iff]
        exact Or.inl ⟨u, rfl, by simpa using hsucc.1⟩
      obtain ⟨⟨te, we⟩, hlit⟩ := hν' _ hclz
      rcases hlit with ⟨hpos, hT⟩ | ⟨hneg, hF⟩
      · rw [posIn_iff] at hpos
        rcases hpos with ⟨hpc, rfl, ⟨hd, he⟩, -⟩ | ⟨s', t', hpc, rfl, hce, hsucc'⟩
        · -- the literal of the predecessor would be true
          obtain rfl : u = true := by simpa using hpc
          exfalso
          refine Hfalse z true hsucc.1 ?_
          have hez : we 0 = z := by simpa using he
          have hwe : we = fun _ => z := ext2 _ _ hez (hd.symm.trans hez)
          exact hcongr ν' (SplitTag.var, we) (SplitTag.var, fun _ => z) (by rw [hwe]) hT
        · -- the successor's linking variable is true, and the successor
          -- is `(x, s)`
          have heq : u = s' := by simpa using hpc
          have hsucc'' : SuccOcc c z u (we 1) t' := by
            rw [heq]
            simpa using hsucc'
          obtain ⟨hxeq, hteq⟩ := succOcc_right_unique hsucc'' hsucc
          have hwe : we = ![c, x] :=
            ext2 _ _ (by simpa using hce.symm) (by simpa using hxeq)
          exact hcongr ν' (SplitTag.link t', we) (SplitTag.link s, ![c, x])
            (by rw [hteq, hwe]) hT
      · rw [negIn_iff] at hneg
        rcases hneg with ⟨hpc, rfl, ⟨hd, he⟩, -⟩ | ⟨s', hpc, rfl, ⟨h0, h1⟩, hchz⟩
        · -- the literal of the predecessor would be true
          obtain rfl : u = false := by simpa using hpc
          exfalso
          refine hF ?_
          have hez : we 0 = z := by simpa using he
          have hwe : (fun _ => z : Fin 2 → A) = we := ext2 _ _ hez.symm (hez.symm.trans hd)
          refine hcongr ν' (SplitTag.var, fun _ => z) (SplitTag.var, we) (by rw [hwe]) ?_
          exact not_not.mp (Hfalse z false hsucc.1)
        · -- the predecessor's own linking variable is true by induction
          have heq : u = s' := by simpa using hpc
          exfalso
          refine hF ?_
          have hchz' : Chained c z u := by
            rw [heq]
            simpa using hchz
          have hwe : (![c, z] : Fin 2 → A) = we :=
            ext2 _ _ (by simpa using h0) (by simpa using h1)
          refine hcongr ν' (SplitTag.link u, ![c, z]) (SplitTag.link s', we) ?_
            (IH z u hsucc.1 hchz' hsucc.2.2.1)
          rw [heq, hwe]
    have main : ∀ x : A, ∀ s, OccIn c x s → Chained c x s →
        ν' (.link s, ![c, x]) := by
      intro x
      refine wellFounded_lt.induction
        (C := fun x => ∀ s, OccIn c x s → Chained c x s → ν' (.link s, ![c, x])) x ?_
      intro x IH s hxs hch
      refine step x s hxs hch fun y t hyt hcht hlt => ?_
      rcases hlt with hlt | ⟨heq, hlt⟩
      · exact IH y hlt t hyt hcht
      · rw [Bool.lt_iff] at hlt
        obtain ⟨rfl, rfl⟩ := hlt
        subst heq
        refine step y false hyt hcht fun z u hz hchz hlt' => ?_
        rcases hlt' with hlt' | ⟨heq', hlt'⟩
        · exact IH z hlt' u hz hchz
        · simp [Bool.lt_iff] at hlt'
    -- the piece of the last occurrence cannot be satisfied
    obtain ⟨xm, sm, hmax⟩ := exists_maxOcc hocc
    have hclm : RelMap (M := satToThreeSat.Map A) satIsClause
        ![(SplitTag.piece sm, ![c, xm])] := by
      rw [isClause_iff]
      exact Or.inl ⟨sm, rfl, by simpa using hmax.occIn⟩
    obtain ⟨⟨te, we⟩, hlit⟩ := hν' _ hclm
    rcases hlit with ⟨hpos, hT⟩ | ⟨hneg, hF⟩
    · rw [posIn_iff] at hpos
      rcases hpos with ⟨hpc, rfl, ⟨hd, he⟩, -⟩ | ⟨s', t', hpc, rfl, -, hsucc'⟩
      · -- its literal would be true
        obtain rfl : sm = true := by simpa using hpc
        refine Hfalse xm true hmax.occIn ?_
        have hez : we 0 = xm := by simpa using he
        have hwe : we = fun _ => xm := ext2 _ _ hez (hd.symm.trans hez)
        exact hcongr ν' (SplitTag.var, we) (SplitTag.var, fun _ => xm) (by rw [hwe]) hT
      · -- the last occurrence has no successor
        have heq : sm = s' := by simpa using hpc
        have hsucc'' : SuccOcc c xm sm (we 1) t' := by
          rw [heq]
          simpa using hsucc'
        exact hmax.2 (we 1) t' hsucc''.2.1 hsucc''.2.2.1
    · rw [negIn_iff] at hneg
      rcases hneg with ⟨hpc, rfl, ⟨hd, he⟩, -⟩ | ⟨s', hpc, rfl, ⟨h0, h1⟩, hch⟩
      · -- its literal would be true
        obtain rfl : sm = false := by simpa using hpc
        refine hF ?_
        have hez : we 0 = xm := by simpa using he
        have hwe : (fun _ => xm : Fin 2 → A) = we := ext2 _ _ hez.symm (hez.symm.trans hd)
        refine hcongr ν' (SplitTag.var, fun _ => xm) (SplitTag.var, we) (by rw [hwe]) ?_
        exact not_not.mp (Hfalse xm false hmax.occIn)
      · -- its own linking variable is true, by the chain invariant
        have heq : sm = s' := by simpa using hpc
        refine hF ?_
        have hch' : Chained c xm sm := by
          rw [heq]
          simpa using hch
        have hwe : (![c, xm] : Fin 2 → A) = we :=
          ext2 _ _ (by simpa using h0) (by simpa using h1)
        refine hcongr ν' (SplitTag.link sm, ![c, xm]) (SplitTag.link s', we) ?_
          (main xm sm hmax.occIn hch')
        rw [heq, hwe]
  · -- `c` is an empty clause: its copy is an unsatisfiable output clause
    have hemp : EmptyCl c := ⟨hcl, fun z u hz => hocc ⟨z, u, hz⟩⟩
    have hcle : RelMap (M := satToThreeSat.Map A) satIsClause
        ![(SplitTag.empty, fun _ => c)] := by
      rw [isClause_iff]
      exact Or.inr ⟨rfl, rfl, hemp⟩
    obtain ⟨⟨te, we⟩, hlit⟩ := hν' _ hcle
    rcases hlit with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · rw [posIn_iff] at hpos
      simp at hpos
    · rw [negIn_iff] at hneg
      simp at hneg

/-- Correctness of the reduction, satisfiability half: an ordered CNF
structure is satisfiable iff its width-three split is. -/
theorem satisfiable_iff_map :
    Satisfiable A ↔ Satisfiable (satToThreeSat.Map A) := by
  constructor
  · -- a satisfying assignment extends to the split
    rintro ⟨ν, hν⟩
    have hν' := satClauses_occ hν
    refine ⟨splitAssign ν, ?_⟩
    rintro ⟨tc, wc⟩ hcl
    rw [isClause_iff] at hcl
    rcases hcl with ⟨s0, rfl, hocc⟩ | ⟨rfl, -, hemp⟩
    · -- a clause piece
      by_cases hpre : PrefixOrStrict ν (wc 0) (wc 1) s0
      · -- an earlier occurrence is true: the own linking variable is false
        have hch : Chained (wc 0) (wc 1) s0 := by
          obtain ⟨y, t, hy, hlt, -⟩ := hpre
          exact ⟨hocc, fun hmin => hmin.2 y t hy hlt⟩
        refine ⟨(SplitTag.link s0, wc), Or.inr ⟨?_, ?_⟩⟩
        · rw [negIn_iff]
          exact Or.inr ⟨s0, rfl, rfl, ⟨rfl, rfl⟩, hch⟩
        · change ¬¬PrefixOrStrict ν (wc 0) (wc 1) s0
          exact not_not_intro hpre
      · by_cases hlit : LitTrue ν (wc 1) s0
        · -- the literal itself is true
          refine ⟨(SplitTag.var, fun _ => wc 1), ?_⟩
          cases s0 with
          | true =>
            refine Or.inl ⟨?_, ?_⟩
            · rw [posIn_iff]
              exact Or.inl ⟨rfl, rfl, ⟨rfl, rfl⟩, hocc⟩
            · exact hlit
          | false =>
            refine Or.inr ⟨?_, ?_⟩
            · rw [negIn_iff]
              exact Or.inl ⟨rfl, rfl, ⟨rfl, rfl⟩, hocc⟩
            · exact hlit
        · -- otherwise some later occurrence exists; its linking variable is
          -- true and occurs positively in the piece
          obtain ⟨z, u, hz, hT⟩ := hν' (wc 0) hocc.isCl
          have hlater : ∃ y t, OccIn (wc 0) y t ∧ occLt (wc 1) s0 y t := by
            refine ⟨z, u, hz, ?_⟩
            rcases occLt_trichotomy z u (wc 1) s0 with h | ⟨rfl, rfl⟩ | h
            · exact absurd ⟨z, u, hz, h, hT⟩ hpre
            · exact absurd hT hlit
            · exact h
          obtain ⟨y, t, hsucc⟩ := exists_succOcc_right hocc hlater
          refine ⟨(SplitTag.link t, ![wc 0, y]), Or.inl ⟨?_, ?_⟩⟩
          · rw [posIn_iff]
            exact Or.inr ⟨s0, t, rfl, rfl, by simp, by simpa using hsucc⟩
          · change ¬PrefixOrStrict ν (wc 0) y t
            rw [prefixOrStrict_succ hsucc, prefixOr_iff hocc]
            rintro (h | h)
            exacts [hpre h, hlit h]
    · -- an empty clause has no true literal in the input: contradiction
      obtain ⟨z, u, hz, -⟩ := hν' (wc 0) hemp.1
      exact absurd hz (hemp.2 z u)
  · -- a satisfying assignment of the split restricts to the input
    rintro ⟨ν', hν'⟩
    refine ⟨fun a => ν' (.var, fun _ => a), fun c hcl => ?_⟩
    obtain ⟨x, s, hocc, hT⟩ := exists_litTrue_of_map hν' hcl
    cases s with
    | true => exact ⟨x, Or.inl ⟨hocc.2, hT⟩⟩
    | false => exact ⟨x, Or.inr ⟨hocc.2, hT⟩⟩


end Satisfiability

/-- Correctness of the reduction: an ordered CNF structure is satisfiable iff
its width-three split is a yes-instance of 3SAT. -/
theorem satisfiable_iff_threeSatisfiable (A : Type) [Language.sat.Structure A]
    [LinearOrder A] [Finite A] :
    Satisfiable A ↔ ThreeSatisfiable (satToThreeSat.Map A) := by
  rw [ThreeSatisfiable, and_iff_right widthAtMostThree_map]
  exact satisfiable_iff_map

end SatToThreeSat

open SatToThreeSat in
/-- **SAT FO-reduces to 3SAT on ordered structures.** The clause-splitting
interpretation `SatToThreeSat.satToThreeSat`, over the ordered expansion of
the language of CNF instances, maps a finite CNF structure to a yes-instance
of 3SAT iff it is satisfiable. Together with `threeSat_fo_reduction_sat`, SAT
and 3SAT are FO-interreducible. -/
noncomputable def sat_ordered_fo_reduction_threeSat : SAT ≤ᶠᵒ[≤] ThreeSAT where
  Tag := SplitTag
  dim := 2
  toInterpretation := satToThreeSat
  correct A _ _ _ _ := satisfiable_iff_threeSatisfiable A

end DescriptiveComplexity
