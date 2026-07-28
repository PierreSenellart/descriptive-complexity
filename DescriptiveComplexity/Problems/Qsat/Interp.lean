/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Tags
import DescriptiveComplexity.Problems.Qsat.Defs
import DescriptiveComplexity.Padding

/-!
# The interpretation of the Savitch reduction

The defining formulas of the reduction of SUCCINCT-REACH to QSAT, and the
resulting first-order interpretation `DescriptiveComplexity.qsatInterp`, of
dimension `2` over the ordered expansion of `FirstOrder.Language.transSys`.

Every relation of `FirstOrder.Language.qsat` is defined by a formula that only
depends on the *tags* of its arguments, and each of those formulas is read off
the tables of `DescriptiveComplexity.Problems.Qsat.Tags`:

* `DescriptiveComplexity.varF` and `DescriptiveComplexity.clF` are the marks
  `DescriptiveComplexity.QVarOn` and `DescriptiveComplexity.QClOn`;
* `DescriptiveComplexity.occF` collects, from the fixed literal list
  `DescriptiveComplexity.qLits` of a clause tag, those literals that are on the
  variable tag and sign asked for – so a single generic realization lemma
  (`DescriptiveComplexity.realize_occF`) replaces a case analysis on all pairs of
  tags;
* `DescriptiveComplexity.prefF` is the lexicographic comparison
  `DescriptiveComplexity.KeyLt` of the two keys, built from static numerals and
  two order atoms.

The section “Characterization of the interpreted relations” reads each of them
back through `DescriptiveComplexity.FOInterpretation.relMap_map`; those lemmas are
the only interface the correctness proof uses.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The formula builders of the reduction

They live in their own namespace: short names like `leF` or `occF` are what every
reduction of the library calls its builders, and the umbrella
`DescriptiveComplexity.Problems` imports them all at once. -/

namespace QsatRed

/-- The ordered expansion of the vocabulary of transition systems: the source
vocabulary of the reduction. -/
abbrev transOrd : Language := Language.transSys.sum Language.order

/-- The symbol for “is a state variable”, in the ordered expansion. -/
abbrev svSym : transOrd.Relations 1 := Sum.inl tsStateVar

/-- The symbol for “is a source clause”, in the ordered expansion. -/
abbrev srcSym : transOrd.Relations 1 := Sum.inl tsSrcCl

/-- The symbol for “is a target clause”, in the ordered expansion. -/
abbrev tgtSym : transOrd.Relations 1 := Sum.inl tsTgtCl

/-- The symbol for “is a transition clause”, in the ordered expansion. -/
abbrev stepSym : transOrd.Relations 1 := Sum.inl tsStepCl

/-- The symbol for “is the next-state copy of”, in the ordered expansion. -/
abbrev nxtSym : transOrd.Relations 2 := Sum.inl tsNext

/-- The symbol for “occurs positively in”, in the ordered expansion. -/
abbrev pSym : transOrd.Relations 2 := Sum.inl tsPosIn

/-- The symbol for “occurs negatively in”, in the ordered expansion. -/
abbrev nSym : transOrd.Relations 2 := Sum.inl tsNegIn

/-! ### Atomic formula builders -/

section Atoms

variable {α : Type}

/-- `x` is a state variable, as a formula. -/
def svF (x : α) : transOrd.Formula α := Relations.formula₁ svSym (Term.var x)

/-- `c` is a source clause, as a formula. -/
def srcF (c : α) : transOrd.Formula α := Relations.formula₁ srcSym (Term.var c)

/-- `c` is a target clause, as a formula. -/
def tgtF (c : α) : transOrd.Formula α := Relations.formula₁ tgtSym (Term.var c)

/-- `c` is a transition clause, as a formula. -/
def stepF (c : α) : transOrd.Formula α := Relations.formula₁ stepSym (Term.var c)

/-- `y` is the next-state copy of `x`, as a formula. -/
def nxtF (x y : α) : transOrd.Formula α :=
  Relations.formula₂ nxtSym (Term.var x) (Term.var y)

/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : transOrd.Formula α :=
  Relations.formula₂ pSym (Term.var c) (Term.var x)

/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : transOrd.Formula α :=
  Relations.formula₂ nSym (Term.var c) (Term.var x)

/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : transOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : transOrd.Formula α := Term.equal (Term.var x) (Term.var y)

/-- `x < y`, as a formula. -/
def ltF (x y : α) : transOrd.Formula α := leF x y ⊓ ∼(eqF x y)

/-- `x` is a minimum of the input order, as a formula. -/
noncomputable def isBotF (x : α) : transOrd.Formula α := botF (L := Language.transSys) x

/-- `x` is the first state variable, as a formula. -/
noncomputable def minSVF (x : α) : transOrd.Formula α :=
  svF x ⊓ ∼((svF (Sum.inr ()) ⊓ ltF (Sum.inr ()) (Sum.inl x)).iExs Unit)

/-- `x` is the last state variable, as a formula. -/
noncomputable def maxSVF (x : α) : transOrd.Formula α :=
  svF x ⊓ ∼((svF (Sum.inr ()) ⊓ ltF (Sum.inl x) (Sum.inr ())).iExs Unit)

/-- `x` is the state variable just above the state variable `y`, as a
formula. -/
noncomputable def predSVF (x y : α) : transOrd.Formula α :=
  svF x ⊓ svF y ⊓ ltF x y ⊓
    ∼((svF (Sum.inr ()) ⊓ ltF (Sum.inl x) (Sum.inr ()) ⊓
      ltF (Sum.inr ()) (Sum.inl y)).iExs Unit)

end Atoms

/-! ### Realization of the atomic builders -/

section RealizeAtoms

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] {α : Type} {V : α → A}

@[simp]
theorem realize_svF {x : α} : (svF x).Realize V ↔ IsSV (V x) := by
  rw [svF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_srcF {c : α} : (srcF c).Realize V ↔ RelMap tsSrcCl ![V c] := by
  rw [srcF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_tgtF {c : α} : (tgtF c).Realize V ↔ RelMap tsTgtCl ![V c] := by
  rw [tgtF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_stepF {c : α} : (stepF c).Realize V ↔ RelMap tsStepCl ![V c] := by
  rw [stepF, Formula.realize_rel₁]
  exact Iff.rfl

@[simp]
theorem realize_nxtF {x y : α} : (nxtF x y).Realize V ↔ RelMap tsNext ![V x, V y] := by
  rw [nxtF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize V ↔ RelMap tsPosIn ![V c, V x] := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize V ↔ RelMap tsNegIn ![V c, V x] := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl

@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize V ↔ V x ≤ V y := by
  simp [leF, Formula.realize_rel₂]

@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize V ↔ V x = V y := by
  simp [eqF]

@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize V ↔ V x < V y := by
  simp [ltF, lt_iff_le_and_ne]

@[simp]
theorem realize_isBotF {x : α} : (isBotF x).Realize V ↔ IsBot (V x) :=
  realize_botF

@[simp]
theorem realize_minSVF {x : α} : (minSVF x).Realize V ↔ IsMinSV (V x) := by
  simp only [minSVF, IsMinSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz hlt => h2 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => hh.elim fun i hi => h2 (i ()) hi.1 hi.2⟩

@[simp]
theorem realize_maxSVF {x : α} : (maxSVF x).Realize V ↔ IsMaxSV (V x) := by
  simp only [maxSVF, IsMaxSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz hlt => h2 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => hh.elim fun i hi => h2 (i ()) hi.1 hi.2⟩

@[simp]
theorem realize_predSVF {x y : α} : (predSVF x y).Realize V ↔ IsPredSV (V x) (V y) := by
  simp only [predSVF, IsPredSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun z hz hlt => h4 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun hh => hh.elim fun i hi => h4 (i ()) hi.1 hi.2⟩

end RealizeAtoms

/-! ### The defining formulas -/

section Formulas

variable {α : Type}

/-- The mark of a variable tag, as a formula in its two coordinates. -/
noncomputable def varF : QVarTag → α → α → transOrd.Formula α
  | .sS | .sT | .sB => fun p q => svF p ⊓ isBotF q
  | .sZ | .sU | .sV => fun p q => svF p ⊓ svF q
  | .aS | .aT | .aP => fun _ q => isBotF q
  | .sE => fun p q => isBotF p ⊓ isBotF q

/-- The guard of a clause tag, as a formula in its two coordinates. -/
noncomputable def clF : QClTag → α → α → transOrd.Formula α
  | .cSrc => fun p q => srcF p ⊓ isBotF q
  | .cTgt => fun p q => tgtF p ⊓ isBotF q
  | .cStep => fun p q => stepF p ⊓ isBotF q
  | .lS _ | .lT _ => fun p q => svF p ⊓ isBotF q
  | .lU _ => fun p q => svF p ⊓ isBotF q
  | .lV _ => fun p q => svF p ⊓ nxtF p q
  | .bE _ => fun p q => svF p ⊓ isBotF q
  | .lev _ _ _ => fun p q => svF p ⊓ svF q

/-- The mark of the universally quantified variables: only the bits `b_ℓ`. -/
noncomputable def allF (v : QVarTag) (p q : α) : transOrd.Formula α :=
  if v = .sB then varF v p q else ⊥

/-- A static component of a lexicographic comparison decides by itself, unless
the two values are equal. -/
noncomputable def natLexF (a b : ℕ) (φ : transOrd.Formula α) : transOrd.Formula α :=
  if a < b then ⊤ else if b < a then ⊥ else φ

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] {V : α → A}

theorem realize_varF {v : QVarTag} {p q : α} :
    (varF v p q).Realize V ↔ QVarOn v (V p) (V q) := by
  cases v <;> simp [varF, QVarOn]

theorem realize_allF {v : QVarTag} {p q : α} :
    (allF v p q).Realize V ↔ (v = .sB ∧ QVarOn v (V p) (V q)) := by
  rw [allF]
  split_ifs with h
  · rw [realize_varF]
    simp [h]
  · simp [h]

theorem realize_clF {c : QClTag} {p q : α} :
    (clF c p q).Realize V ↔ QClOn c (V p) (V q) := by
  cases c <;> simp [clF, QClOn]

theorem realize_natLexF {a b : ℕ} {φ : transOrd.Formula α} {P : Prop} (h : φ.Realize V ↔ P) :
    (natLexF a b φ).Realize V ↔ (a < b ∨ (a = b ∧ P)) := by
  rw [natLexF]
  split_ifs with h1 h2
  · simp [h1]
  · refine iff_of_false (by simp) ?_
    rintro (h3 | ⟨h3, -⟩) <;> omega
  · rw [h]
    have hab : a = b := by omega
    simp [hab]

end Formulas

/-! ### The coordinates of a two-argument defining formula -/

/-- The first coordinate of the first argument. -/
abbrev x₀ : Fin 2 × Fin 2 := (0, 0)

/-- The second coordinate of the first argument. -/
abbrev y₀ : Fin 2 × Fin 2 := (0, 1)

/-- The first coordinate of the second argument. -/
abbrev x₁ : Fin 2 × Fin 2 := (1, 0)

/-- The second coordinate of the second argument. -/
abbrev y₁ : Fin 2 × Fin 2 := (1, 1)

/-- Where a literal's variable sits, as a formula in the four coordinates. -/
noncomputable def linkF : QLink → transOrd.Formula (Fin 2 × Fin 2)
  | .atP => eqF x₁ x₀ ⊓ isBotF y₁
  | .atQ => eqF x₁ y₀ ⊓ isBotF y₁
  | .botBoth => isBotF x₁ ⊓ isBotF y₁
  | .maxAtP => maxSVF x₁ ⊓ eqF y₁ x₀
  | .same => eqF x₁ x₀ ⊓ eqF y₁ y₀
  | .minAtQ => minSVF x₀ ⊓ eqF x₁ y₀ ⊓ isBotF y₁
  | .predAtQ => predSVF x₁ x₀ ⊓ eqF y₁ y₀
  | .occPos => posF x₀ x₁ ⊓ isBotF y₁
  | .occNeg => negF x₀ x₁ ⊓ isBotF y₁

theorem realize_linkF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {k : QLink} {V : Fin 2 × Fin 2 → A} :
    (linkF k).Realize V ↔ LinkOn k (V x₀) (V y₀) (V x₁) (V y₁) := by
  cases k <;> simp [linkF, LinkOn, and_assoc]

/-- **The occurrence formula**: the literals of the clause tag `ct` that are on
the variable tag `vt` with the sign `sgn`, gathered into a disjunction. -/
noncomputable def occF (sgn : Bool) (ct : QClTag) (vt : QVarTag) :
    transOrd.Formula (Fin 2 × Fin 2) :=
  listSup ((qLits ct).map fun l =>
    if l.vt = vt ∧ l.sign = sgn then clF ct x₀ y₀ ⊓ varF vt x₁ y₁ ⊓ linkF l.link else ⊥)

theorem realize_occF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {sgn : Bool} {ct : QClTag} {vt : QVarTag} {V : Fin 2 × Fin 2 → A} :
    (occF sgn ct vt).Realize V ↔
      ∃ l ∈ qLits ct, l.vt = vt ∧ l.sign = sgn ∧
        QClOn ct (V x₀) (V y₀) ∧ QVarOn vt (V x₁) (V y₁) ∧
          LinkOn l.link (V x₀) (V y₀) (V x₁) (V y₁) := by
  classical
  rw [occF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hψmem
    by_cases hc : l.vt = vt ∧ l.sign = sgn
    · rw [if_pos hc, Formula.realize_inf, Formula.realize_inf, realize_linkF, realize_clF,
        realize_varF] at hψ
      exact ⟨l, hl, hc.1, hc.2, hψ.1.1, hψ.1.2, hψ.2⟩
    · rw [if_neg hc] at hψ
      exact hψ.elim
  · rintro ⟨l, hl, h1, h2, h3, h4, h5⟩
    refine ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    rw [if_pos ⟨h1, h2⟩, Formula.realize_inf, Formula.realize_inf, realize_linkF, realize_clF,
      realize_varF]
    exact ⟨⟨h3, h4⟩, h5⟩

/-! ### The prefix formula -/

/-- The lexicographic comparison of two keys, spelled out: the static
components decide by themselves, the two dynamic ones by an order atom. -/
def KeyLtRaw {A : Type} [LinearOrder A] (g : ℕ) (l : A) (s : ℕ) (c : A) (o : ℕ)
    (g' : ℕ) (l' : A) (s' : ℕ) (c' : A) (o' : ℕ) : Prop :=
  g < g' ∨ (g = g' ∧ (l < l' ∨ (l = l' ∧
    (s < s' ∨ (s = s' ∧ (c < c' ∨ (c = c' ∧ o < o')))))))

theorem keyLt_iff_raw {A : Type} [LinearOrder A] (v v' : QVarTag) (p q p' q' : A) :
    KeyLt v p q v' p' q' ↔
      KeyLtRaw (keyGrp v) (keyLev v p q) (keySlot v) (keySec v p q) (keyOrd v)
        (keyGrp v') (keyLev v' p' q') (keySlot v') (keySec v' p' q') (keyOrd v') := by
  simp only [KeyLt, KeyLtRaw, TripleLt, keyTriple, Prod.mk.injEq]
  tauto

/-- The body of the prefix comparison, with the four coordinates selected. -/
noncomputable def keyBodyF (v v' : QVarTag) (lv sc lv' sc' : Fin 2 × Fin 2) :
    transOrd.Formula (Fin 2 × Fin 2) :=
  natLexF (keyGrp v) (keyGrp v')
    (ltF lv lv' ⊔ (eqF lv lv' ⊓
      natLexF (keySlot v) (keySlot v')
        (ltF sc sc' ⊔ (eqF sc sc' ⊓ natLexF (keyOrd v) (keyOrd v') ⊥))))

theorem realize_keyBodyF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {v v' : QVarTag} {lv sc lv' sc' : Fin 2 × Fin 2} {V : Fin 2 × Fin 2 → A} :
    (keyBodyF v v' lv sc lv' sc').Realize V ↔
      KeyLtRaw (keyGrp v) (V lv) (keySlot v) (V sc) (keyOrd v)
        (keyGrp v') (V lv') (keySlot v') (V sc') (keyOrd v') := by
  have hord : (natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2))).Realize V ↔
      keyOrd v < keyOrd v' := by
    rw [realize_natLexF (P := False) (by simp)]
    simp
  have hsec : (ltF sc sc' ⊔ (eqF sc sc' ⊓
      natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2)))).Realize V ↔
      (V sc < V sc' ∨ (V sc = V sc' ∧ keyOrd v < keyOrd v')) := by
    rw [Formula.realize_sup, Formula.realize_inf, realize_ltF, realize_eqF, hord]
  have hslot := realize_natLexF (V := V) (a := keySlot v) (b := keySlot v') hsec
  have hlev : (ltF lv lv' ⊔ (eqF lv lv' ⊓ natLexF (keySlot v) (keySlot v')
      (ltF sc sc' ⊔ (eqF sc sc' ⊓
        natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2)))))).Realize V ↔
      (V lv < V lv' ∨ (V lv = V lv' ∧
        (keySlot v < keySlot v' ∨ (keySlot v = keySlot v' ∧
          (V sc < V sc' ∨ (V sc = V sc' ∧ keyOrd v < keyOrd v')))))) := by
    rw [Formula.realize_sup, Formula.realize_inf, realize_ltF, realize_eqF, hslot]
  rw [keyBodyF, realize_natLexF hlev, KeyLtRaw]

/-- **The quantifier prefix**, as a formula: both arguments are variables, and
their keys compare lexicographically. -/
noncomputable def prefF (v v' : QVarTag) : transOrd.Formula (Fin 2 × Fin 2) :=
  varF v x₀ y₀ ⊓ varF v' x₁ y₁ ⊓
    keyBodyF v v' (if levFst v then x₀ else y₀) (if levFst v then y₀ else x₀)
      (if levFst v' then x₁ else y₁) (if levFst v' then y₁ else x₁)

theorem realize_prefF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {v v' : QVarTag} {V : Fin 2 × Fin 2 → A} :
    (prefF v v').Realize V ↔
      QVarOn v (V x₀) (V y₀) ∧ QVarOn v' (V x₁) (V y₁) ∧
        KeyLt v (V x₀) (V y₀) v' (V x₁) (V y₁) := by
  rw [prefF, Formula.realize_inf, Formula.realize_inf, realize_keyBodyF, realize_varF,
    realize_varF, keyLt_iff_raw, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [keyLev, keySec]
  cases levFst v <;> cases levFst v' <;> simp

end QsatRed

open QsatRed

/-! ### The interpretation -/

/-- **The Savitch interpretation**: the QSAT instance whose prefix and matrix
express reachability in the transition system described by the input, by
recursive doubling. -/
noncomputable def qsatInterp : FOInterpretation transOrd Language.qsat QTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isVar => fun t =>
        match t 0 with
        | Sum.inl v => varF v ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (1 : Fin 2))
        | Sum.inr _ => ⊥
    | _, .allVar => fun t =>
        match t 0 with
        | Sum.inl v => allF v ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (1 : Fin 2))
        | Sum.inr _ => ⊥
    | _, .prefixLt => fun t =>
        match t 0, t 1 with
        | Sum.inl v, Sum.inl v' => prefF v v'
        | _, _ => ⊥
    | _, .isClause => fun t =>
        match t 0 with
        | Sum.inr c => clF c ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (1 : Fin 2))
        | Sum.inl _ => ⊥
    | _, .posIn => fun t =>
        match t 0, t 1 with
        | Sum.inr c, Sum.inl v => occF true c v
        | _, _ => ⊥
    | _, .negIn => fun t =>
        match t 0, t 1 with
        | Sum.inr c, Sum.inl v => occF false c v
        | _, _ => ⊥

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The universe of the constructed instance: a tag together with a pair of
elements of the input. -/
abbrev QM (A : Type) [Language.transSys.Structure A] [LinearOrder A] : Type :=
  (qsatInterp).Map A

instance [Finite A] : Finite (QM A) :=
  inferInstanceAs (Finite (QTag × (Fin 2 → A)))

instance [Nonempty A] : Nonempty (QM A) :=
  inferInstanceAs (Nonempty (QTag × (Fin 2 → A)))

/-- **The variables**: the marked tagged pairs. -/
theorem qsat_isVar (v : QVarTag) (w : Fin 2 → A) :
    IsQVar (A := QM A) (Sum.inl v, w) ↔ QVarOn v (w 0) (w 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsIsVar ![(Sum.inl v, w)]) realize_varF

/-- Elements carrying a clause tag are not variables. -/
theorem qsat_not_isVar (c : QClTag) (w : Fin 2 → A) :
    ¬IsQVar (A := QM A) (Sum.inr c, w) :=
  id

/-- **The universal variables**: only the bits `b_ℓ`. -/
theorem qsat_isAll (v : QVarTag) (w : Fin 2 → A) :
    IsQAll (A := QM A) (Sum.inl v, w) ↔ (v = .sB ∧ QVarOn v (w 0) (w 1)) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsAllVar ![(Sum.inl v, w)]) realize_allF

/-- Every variable tag other than `sB` is existential. -/
theorem qsat_not_isAll {v : QVarTag} (hv : v ≠ .sB) (w : Fin 2 → A) :
    ¬IsQAll (A := QM A) (Sum.inl v, w) := fun h => hv ((qsat_isAll v w).mp h).1

/-- Elements carrying a clause tag are not universal. -/
theorem qsat_not_isAll_cl (c : QClTag) (w : Fin 2 → A) :
    ¬IsQAll (A := QM A) (Sum.inr c, w) :=
  id

/-- **The clauses**: the guarded tagged pairs. -/
theorem qsat_isClause (c : QClTag) (w : Fin 2 → A) :
    RelMap (M := QM A) qsIsClause ![(Sum.inr c, w)] ↔ QClOn c (w 0) (w 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsIsClause ![(Sum.inr c, w)]) realize_clF

/-- Elements carrying a variable tag are not clauses. -/
theorem qsat_not_isClause (v : QVarTag) (w : Fin 2 → A) :
    ¬RelMap (M := QM A) qsIsClause ![(Sum.inl v, w)] :=
  id

/-- **The prefix order** relates two variables exactly as their keys compare. -/
theorem qsat_prec (v v' : QVarTag) (w w' : Fin 2 → A) :
    QPrec (A := QM A) (Sum.inl v, w) (Sum.inl v', w') ↔
      QVarOn v (w 0) (w 1) ∧ QVarOn v' (w' 0) (w' 1) ∧
        KeyLt v (w 0) (w 1) v' (w' 0) (w' 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsPrefixLt
    ![(Sum.inl v, w), (Sum.inl v', w')]) realize_prefF

/-- The prefix order does not relate a clause on the left. -/
theorem qsat_not_prec_left (c : QClTag) (x : QM A) (w : Fin 2 → A) :
    ¬QPrec (A := QM A) (Sum.inr c, w) x := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

/-- The prefix order does not relate a clause on the right. -/
theorem qsat_not_prec_right (c : QClTag) (x : QM A) (w : Fin 2 → A) :
    ¬QPrec (A := QM A) x (Sum.inr c, w) := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

/-- **The positive literals** of a clause: the literals of its list that are on
the given variable tag with a positive sign, and whose link pins that variable's
coordinates. -/
theorem qsat_posIn (c : QClTag) (v : QVarTag) (w y : Fin 2 → A) :
    RelMap (M := QM A) qsPosIn ![(Sum.inr c, w), (Sum.inl v, y)] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = true ∧
        QClOn c (w 0) (w 1) ∧ QVarOn v (y 0) (y 1) ∧
          LinkOn l.link (w 0) (w 1) (y 0) (y 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsPosIn
    ![(Sum.inr c, w), (Sum.inl v, y)]) realize_occF

/-- **The negative literals** of a clause. -/
theorem qsat_negIn (c : QClTag) (v : QVarTag) (w y : Fin 2 → A) :
    RelMap (M := QM A) qsNegIn ![(Sum.inr c, w), (Sum.inl v, y)] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = false ∧
        QClOn c (w 0) (w 1) ∧ QVarOn v (y 0) (y 1) ∧
          LinkOn l.link (w 0) (w 1) (y 0) (y 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsNegIn
    ![(Sum.inr c, w), (Sum.inl v, y)]) realize_occF

/-- No literal is on an element carrying a clause tag. -/
theorem qsat_not_posIn_cl (x : QM A) (c : QClTag) (y : Fin 2 → A) :
    ¬RelMap (M := QM A) qsPosIn ![x, (Sum.inr c, y)] := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

/-- No literal is on an element carrying a clause tag, negatively. -/
theorem qsat_not_negIn_cl (x : QM A) (c : QClTag) (y : Fin 2 → A) :
    ¬RelMap (M := QM A) qsNegIn ![x, (Sum.inr c, y)] := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

/-- An element carrying a variable tag has no literals. -/
theorem qsat_not_posIn_var (v : QVarTag) (w : Fin 2 → A) (x : QM A) :
    ¬RelMap (M := QM A) qsPosIn ![(Sum.inl v, w), x] := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

/-- An element carrying a variable tag has no negative literals. -/
theorem qsat_not_negIn_var (v : QVarTag) (w : Fin 2 → A) (x : QM A) :
    ¬RelMap (M := QM A) qsNegIn ![(Sum.inl v, w), x] := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id

end Characterizations

end DescriptiveComplexity
