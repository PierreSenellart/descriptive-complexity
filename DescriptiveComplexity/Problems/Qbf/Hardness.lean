/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qbf.Transfer
import DescriptiveComplexity.Problems.Sat.Hardness

/-!
# Hardness of QBF

The hardness half of the completeness of `DescriptiveComplexity.QBF`: every problem
definable by a second-order sentence with `k + 1` alternating blocks admits an
ordered first-order reduction to `DescriptiveComplexity.QBF (k + 1)`
(`DescriptiveComplexity.qbf_hard_of_sigmaSODefinable`). This is the Cook–Levin discharge
of
`DescriptiveComplexity.Problems.Sat.Hardness` with block marks added.

The quantifier prefix of a second-order definition is merged into a single
block (`DescriptiveComplexity.SecondOrderMerge`), the Tseitin translation
([Tseitin 1968][tseitin1968complexity]) of the resulting first-order kernel is
interpreted inside an ordered input structure exactly as for SAT
(`DescriptiveComplexity.qbfTseitinInterp`), and each propositional variable is marked
with the quantifier block it belongs to: an atom variable with the block its
relation variable comes from, and every *gate* variable with the innermost
block.

Gate variables can only be marked innermost, and only work out when the
innermost quantifier is existential – they are functionally determined by the
atoms, so `∃ gates, CNF ↔ φ`, whereas a universal player could falsify a gate
clause. With an existential outermost block the innermost quantifier is
existential exactly when `k` is odd, which is why the literal signs of the
interpretation are swapped (the parameter `sw`), and the kernel negated, when
`k` is even: the disjunctive matrix of `DescriptiveComplexity.QBF k` at even `k` is, by
`DescriptiveComplexity.dnfSat_iff_not_cnfSatWith_true`, the negation of a conjunctive
matrix with all signs swapped, and that negation turns the innermost universal
quantifier back into an existential one over the gates. The swap is arranged
so that the parity disappears from the correctness proof: whichever of
`posIn`/`negIn` a satisfied clause must make true always carries the *positive*
Tseitin literals (`DescriptiveComplexity.qbfT_lit_pos`).

The key correctness statement is `DescriptiveComplexity.qbfT_clauses_iff`, the
`∃`-free form of `DescriptiveComplexity.tseitin_satisfiable_iff`: with the truth
assignment *given* – as the quantifier prefix of a QBF supplies it, rather
than existentially quantified as for SAT – the clauses of the encoding hold
exactly when the induced valuation satisfies every Tseitin gate and makes the
root variable true.

The discharge itself is `DescriptiveComplexity.qbf_hard_of_sigmaSODefinable`; together
with the membership half of `DescriptiveComplexity.Problems.Qbf.Membership` it gives the
completeness theorem `DescriptiveComplexity.QBF_complete`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure Tseitin

section Interp

variable {L : Language.{0, 0}} (k : ℕ) (sw : Bool) (M : SOBlock)
  (ψ : (L.sum M.lang).Sentence)
  (mark : (M.ι ⊕ Σ m, NodeAt ψ m) → Fin k)

/-- The block of Tseitin gate variables: one relation variable per subformula
position of the kernel, of the interpretation's dimension. Reducible, so that
`(gateBlock M ψ).ι` unfolds to the type of subformula positions. -/
@[reducible]
noncomputable def gateBlock : SOBlock where
  ι := Σ m, NodeAt ψ m
  arity := fun _ => tseitinDim M ψ

/-- The Tseitin interpretation with block marks: the CNF instance of the
encoding of `ψ`, with each propositional variable marked by the quantifier
block it belongs to. The signs of the literals are swapped when `sw` is
`true`, i.e. when the innermost quantifier of the prefix is universal. -/
noncomputable def qbfTseitinInterp :
    FOInterpretation (L.sum Language.order) (Language.qbf k) (TseitinTag M ψ)
      (tseitinDim M ψ) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        (match t 0 with
         | Sum.inl (Sum.inl (σp, c)) =>
             isClauseF ψ (maxCtx_le_tseitinDim M ψ) σp.2 c fun j => ((0 : Fin 1), j)
         | Sum.inl (Sum.inr _) => canonF 0 fun j => ((0 : Fin 1), j)
         | Sum.inr _ => ⊥)
    | _, .posIn => fun t => tseitinLitFml M ψ (!sw) (t 0) (t 1)
    | _, .negIn => fun t => tseitinLitFml M ψ sw (t 0) (t 1)
    | _, .block j => fun t =>
        (match t 0 with
         | Sum.inr vt => if mark vt = j then ⊤ else ⊥
         | Sum.inl _ => ⊥)

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem qbfT_isClause_node (σp : Σ m, NodeAt ψ m) (c : Fin 3)
    (u : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A) (qbfIsClause (k := k))
        ![(Sum.inl (Sum.inl (σp, c)), u)] ↔
      IsClauseSem ψ (maxCtx_le_tseitinDim M ψ) σp.2 c u := by
  rw [FOInterpretation.relMap_map]
  exact realize_isClauseF ψ (maxCtx_le_tseitinDim M ψ) σp.2 c fun j => (0, j)

theorem qbfT_isClause_top (u : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A) (qbfIsClause (k := k))
        ![(Sum.inl (Sum.inr ()), u)] ↔ Canon 0 u := by
  rw [FOInterpretation.relMap_map]
  exact realize_canonF

theorem qbfT_isClause_var (vt : M.ι ⊕ Σ m, NodeAt ψ m) (u : Fin (tseitinDim M ψ) → A) :
    ¬RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A) (qbfIsClause (k := k))
      ![(Sum.inr vt, u)] := by
  rw [FOInterpretation.relMap_map]
  exact id

/-- The literals of the interpretation are those of the Tseitin encoding, with
the signs swapped when `sw` is `true`. -/
theorem qbfT_lit_iff (s : Bool) (tc tx : TseitinTag M ψ)
    (u x : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A)
        (if s then qbfPosIn (k := k) else qbfNegIn (k := k)) ![(tc, u), (tx, x)] ↔
      TseitinLitSem M ψ (xor s sw) tc tx u x := by
  have key : RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A)
        (if s then qbfPosIn (k := k) else qbfNegIn (k := k)) ![(tc, u), (tx, x)] ↔
      RelMap (M := (tseitinInterp M ψ).Map A)
        (if xor s sw then satPosIn else satNegIn) ![(tc, u), (tx, x)] := by
    cases s <;> cases sw <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true] <;>
      rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map] <;> rfl
  rw [key]
  exact tseitin_lit_iff M ψ (xor s sw) tc tx u x

/-- A variable is marked by exactly the block it belongs to; clause elements
are marked by no block at all. -/
theorem qbfT_block_var (j : Fin k) (vt : M.ι ⊕ Σ m, NodeAt ψ m)
    (u : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A) (qbfBlock j)
        ![(Sum.inr vt, u)] ↔ mark vt = j := by
  rw [FOInterpretation.relMap_map]
  change (if mark vt = j then (⊤ : (L.sum Language.order).Formula _) else ⊥).Realize _ ↔ _
  split_ifs with h
  · exact iff_of_true (by simp) h
  · exact iff_of_false (by simp) h

theorem qbfT_block_clause (j : Fin k) (tc : (Σ m, NodeAt ψ m) × Fin 3 ⊕ Unit)
    (u : Fin (tseitinDim M ψ) → A) :
    ¬RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A) (qbfBlock j)
      ![(Sum.inl tc, u)] := by
  rw [FOInterpretation.relMap_map]
  exact id

/-- The literal that a satisfied clause needs to make *true*: whichever of
`posIn`/`negIn` carries the positive Tseitin literals. -/
theorem qbfT_lit_pos (tc tx : TseitinTag M ψ) (u x : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A)
        (if sw then qbfNegIn (k := k) else qbfPosIn (k := k)) ![(tc, u), (tx, x)] ↔
      TseitinLitSem M ψ true tc tx u x := by
  have h : (if sw then qbfNegIn (k := k) else qbfPosIn (k := k)) =
      (if !sw then qbfPosIn (k := k) else qbfNegIn (k := k)) := by cases sw <;> rfl
  rw [h]
  have h2 := qbfT_lit_iff k sw M ψ mark (!sw) tc tx u x
  rwa [show xor (!sw) sw = true by cases sw <;> rfl] at h2

/-- The literal that a satisfied clause needs to make *false*. -/
theorem qbfT_lit_neg (tc tx : TseitinTag M ψ) (u x : Fin (tseitinDim M ψ) → A) :
    RelMap (M := (qbfTseitinInterp k sw M ψ mark).Map A)
        (if sw then qbfPosIn (k := k) else qbfNegIn (k := k)) ![(tc, u), (tx, x)] ↔
      TseitinLitSem M ψ false tc tx u x := by
  have h2 := qbfT_lit_iff k sw M ψ mark sw tc tx u x
  rwa [show xor sw sw = false by cases sw <;> rfl] at h2

/-! ### Correctness at a fixed valuation

The Tseitin correctness proof of `DescriptiveComplexity.Problems.Sat.Hardness` is stated
with the truth assignment existentially quantified. Here the assignment is
*given*, since the quantifier prefix of the QBF supplies it: the clauses of
the encoding hold under `val` exactly when the induced valuation satisfies
every gate and makes the root true. -/

/-- **Correctness of the interpretation at a fixed valuation.** -/
theorem qbfT_clauses_iff {a₀ : A} (ha₀ : IsBot a₀)
    (val : (qbfTseitinInterp k sw M ψ mark).Map A → Prop) :
    (∀ c : (qbfTseitinInterp k sw M ψ mark).Map A, RelMap (qbfIsClause (k := k)) ![c] →
        ∃ x, (RelMap (if sw then qbfNegIn (k := k) else qbfPosIn (k := k)) ![c, x] ∧ val x) ∨
          (RelMap (if sw then qbfPosIn (k := k) else qbfNegIn (k := k)) ![c, x] ∧ ¬val x)) ↔
      (SatCond ψ (maxCtx_le_tseitinDim M ψ) (fun vt x => val (Sum.inr vt, x)) ∧
        val (Sum.inr (Sum.inr ⟨0, rootAt ψ⟩), pad a₀ finZeroElim)) := by
  constructor
  · intro hν
    constructor
    · intro m p c u hcl
      obtain ⟨⟨tx, x⟩, hx⟩ := hν (Sum.inl (Sum.inl (⟨m, p⟩, c)), u)
        ((qbfT_isClause_node k sw M ψ mark ⟨m, p⟩ c u).mpr hcl)
      rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
      · have hls := (qbfT_lit_pos k sw M ψ mark (Sum.inl (Sum.inl (⟨m, p⟩, c))) tx u x).mp hpos
        rcases tx with tcl | vt
        · exact hls.elim
        · exact ⟨vt, x, Or.inl ⟨hls, hval⟩⟩
      · have hls := (qbfT_lit_neg k sw M ψ mark (Sum.inl (Sum.inl (⟨m, p⟩, c))) tx u x).mp hneg
        rcases tx with tcl | vt
        · exact hls.elim
        · exact ⟨vt, x, Or.inr ⟨hls, hval⟩⟩
    · obtain ⟨⟨tx, x⟩, hx⟩ := hν (Sum.inl (Sum.inr ()), fun _ => a₀)
        ((qbfT_isClause_top k sw M ψ mark _).mpr fun j _ => ha₀)
      rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
      · have hls := (qbfT_lit_pos k sw M ψ mark (Sum.inl (Sum.inr ())) tx _ x).mp hpos
        rcases tx with tcl | vt
        · exact hls.elim
        · rcases vt with i | σp'
          · exact hls.elim
          · obtain ⟨-, rfl, -, hcx⟩ := hls
            have hx0 : x = pad a₀ finZeroElim := by
              rw [← pad_pref_of_canon ha₀ (Nat.zero_le _) hcx]
              exact (congrArg (pad a₀) (Subsingleton.elim _ _)).symm
            rw [← hx0]
            exact hval
      · have hls := (qbfT_lit_neg k sw M ψ mark (Sum.inl (Sum.inr ())) tx _ x).mp hneg
        rcases tx with tcl | vt
        · exact hls.elim
        · rcases vt with i | σp'
          · exact hls.elim
          · exact absurd hls.1 (by simp)
  · rintro ⟨hsat, hroot⟩ ⟨tc, u⟩ hcl
    rcases tc with tcl | vt
    swap
    · exact absurd hcl (qbfT_isClause_var k sw M ψ mark vt u)
    rcases tcl with ⟨σp, c⟩ | u'
    · rw [qbfT_isClause_node] at hcl
      obtain ⟨vt, x, hor⟩ := hsat σp.1 σp.2 c u hcl
      rcases hor with ⟨hls, hval⟩ | ⟨hls, hval⟩
      · exact ⟨(Sum.inr vt, x), Or.inl
          ⟨(qbfT_lit_pos k sw M ψ mark (Sum.inl (Sum.inl (σp, c))) (Sum.inr vt) u x).mpr hls,
            hval⟩⟩
      · exact ⟨(Sum.inr vt, x), Or.inr
          ⟨(qbfT_lit_neg k sw M ψ mark (Sum.inl (Sum.inl (σp, c))) (Sum.inr vt) u x).mpr hls,
            hval⟩⟩
    · rw [qbfT_isClause_top] at hcl
      refine ⟨(Sum.inr (Sum.inr ⟨0, rootAt ψ⟩), pad a₀ finZeroElim), Or.inl ⟨?_, hroot⟩⟩
      exact (qbfT_lit_pos k sw M ψ mark (Sum.inl (Sum.inr u'))
        (Sum.inr (Sum.inr ⟨0, rootAt ψ⟩)) u _).mpr ⟨rfl, rfl, hcl, canon_pad ha₀ 0 _⟩

end Characterizations

end Interp

/-! ### The reduction -/

section Reduction

variable {L : Language.{0, 0}}

/-- Padding a tuple that already has the interpretation's dimension does
nothing. -/
theorem pad_full {A : Type} {D : ℕ} (a₀ : A) (w : Fin D → A) : pad a₀ w = w := by
  funext j
  rw [pad, dif_pos j.isLt]

/-- Reindexing an alternating quantification along an equality of lengths. -/
theorem altQuant_cast {A : Type} {m n : ℕ} (h : m = n)
    (P : (Fin n → A → Prop) → Prop) (pol : Bool) :
    altQuant A m (fun νs => P fun j => νs (Fin.cast h.symm j)) pol ↔ altQuant A n P pol := by
  subst h
  exact Iff.rfl

variable (B : SOBlock) (Bs : List SOBlock) (φ : (soLang L (B :: Bs)).Sentence)

/-- Whether the innermost quantifier of an existentially-starting prefix with
`Bs.length + 1` blocks is universal – equivalently, whether `Bs.length + 1` is
even. The Tseitin gates can only be absorbed by an existential quantifier, so
this is the flag that decides both the shape of the matrix and whether the
kernel gets negated. -/
def qbfSwap (Bs : List SOBlock) : Bool := !innerPol Bs.length true

/-- The sentence that is actually Tseitin-encoded: the merged kernel, negated
when the innermost quantifier is universal. -/
noncomputable def qbfEnc : (L.sum (mergeBlocks (B :: Bs)).lang).Sentence :=
  if qbfSwap Bs then ∼((mergeHom (B :: Bs) L).onSentence φ)
  else (mergeHom (B :: Bs) L).onSentence φ

/-- The block of gate variables of the encoding. -/
noncomputable abbrev qbfGt : SOBlock := gateBlock (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)

/-- The block marks of the interpreted instance: a relation variable is marked
by the block it comes from, a gate variable by the innermost block. -/
noncomputable def qbfMk :
    ((mergeBlocks (B :: Bs)).ι ⊕ Σ m, NodeAt (qbfEnc B Bs φ) m) → Fin (Bs.length + 1) :=
  fun vt => Fin.cast (consLast_length (qbfGt B Bs φ) B Bs) (markC (qbfGt B Bs φ) B Bs vt)

/-- The interpretation of the reduction: the Tseitin encoding of the merged
kernel, with block marks. Reducible, so that the characterizations of
`DescriptiveComplexity.qbfTseitinInterp` apply to it directly. -/
@[reducible]
noncomputable def qbfRedInterp :
    FOInterpretation (L.sum Language.order) (Language.qbf (Bs.length + 1))
      (TseitinTag (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ))
      (tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)) :=
  qbfTseitinInterp (Bs.length + 1) (qbfSwap Bs) (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)
    (qbfMk B Bs φ)

/-- The swap flag is the parity of the number of blocks: the matrix of
`DescriptiveComplexity.QBF k` is disjunctive exactly when a swap is needed. -/
theorem qbfSwap_eq (Bs : List SOBlock) : qbfSwap Bs = !((Bs.length + 1) % 2 == 1) := by
  rw [qbfSwap, innerPol_eq]
  rcases Nat.mod_two_eq_zero_or_one Bs.length with h | h
  · have h1 : (Bs.length + 1) % 2 = 1 := by omega
    rw [h, h1]; rfl
  · have h1 : (Bs.length + 1) % 2 = 0 := by omega
    rw [h, h1]; rfl

section Correct

variable {A : Type} [L.Structure A] [LinearOrder A]

omit [LinearOrder A] in
/-- Realization of a sentence in the expansion by an assignment is
`DescriptiveComplexity.Tseitin.RealizeWith`. -/
theorem realize_eq_realizeWith {M : SOBlock} (μ : M.Assignment A)
    (χ : (L.sum M.lang).Sentence) :
    @Sentence.Realize (L.sum M.lang) A (@sumStructure L M.lang A _ (M.structure μ)) χ ↔
      RealizeWith μ χ finZeroElim :=
  iff_of_eq (congrArg₂
    (fun (v : Empty → A) (xs : Fin 0 → A) =>
      @BoundedFormula.Realize _ A (assignStructure L μ) _ _ χ v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

omit [LinearOrder A] in
/-- **The gates are functionally determined**: some gate valuation satisfies
every gate, so quantifying them existentially adds nothing. -/
theorem exists_gates {M : SOBlock} (a₀ : A) (μ : M.Assignment A)
    (χ : (L.sum M.lang).Sentence) :
    (∃ g : (gateBlock M χ).Assignment A,
        Gates μ χ (fun m q w => g ⟨m, q⟩ (pad a₀ w)) ∧ RealizeWith μ χ finZeroElim) ↔
      RealizeWith μ χ finZeroElim := by
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    refine ⟨fun j x => canonVal μ χ j.1 j.2
      (pref ((nodeAt_le_maxCtx χ j.2).trans (maxCtx_le_tseitinDim M χ)) x), ?_, h⟩
    have hg : (fun m (q : NodeAt χ m) w =>
          canonVal μ χ m q
            (pref ((nodeAt_le_maxCtx χ q).trans (maxCtx_le_tseitinDim M χ)) (pad a₀ w))) =
        canonVal μ χ :=
      funext fun m => funext fun q => funext fun w =>
        congrArg (canonVal μ χ m q) (pref_pad a₀ _ w)
    rw [hg]
    exact gates_canonVal μ χ

/-- The reading of the interpreted instance: each propositional variable is
read at its canonically padded tuple. -/
noncomputable def qbfRd (a₀ : A) :
    BlockRead A ((qbfRedInterp B Bs φ).Map A) (consLast (qbfGt B Bs φ) B Bs) :=
  fun i ν a => ν (Sum.inr (splitIdx (qbfGt B Bs φ) B Bs i), pad a₀ a)

omit [LinearOrder A] in
/-- **The innermost quantifier absorbs the gates**: quantifying the gate block
with the innermost polarity, over the Tseitin condition, is exactly the truth
of the merged kernel. When the innermost quantifier is existential this is
`DescriptiveComplexity.exists_gates`; when it is universal it is the same fact under the
negation that the swapped encoding introduces. -/
theorem qbf_inner (a₀ : A) (μ : (mergeBlocks (B :: Bs)).Assignment A) :
    quantB (innerPol Bs.length true)
        (fun g : (qbfGt B Bs φ).Assignment A => xorP (qbfSwap Bs)
          (Gates μ (qbfEnc B Bs φ) (fun m q w => g ⟨m, q⟩ (pad a₀ w)) ∧
            RealizeWith μ (qbfEnc B Bs φ) finZeroElim)) ↔
      RealizeWith μ ((mergeHom (B :: Bs) L).onSentence φ) finZeroElim := by
  have hsw : qbfSwap Bs = !innerPol Bs.length true := rfl
  cases hp : innerPol Bs.length true with
  | false =>
    have hswt : qbfSwap Bs = true := by rw [hsw, hp]; rfl
    have hχ : qbfEnc B Bs φ = ∼((mergeHom (B :: Bs) L).onSentence φ) := by
      rw [qbfEnc, hswt]; rfl
    have hnot : RealizeWith μ (qbfEnc B Bs φ) finZeroElim ↔
        ¬RealizeWith μ ((mergeHom (B :: Bs) L).onSentence φ) finZeroElim := by
      rw [hχ]; exact Iff.rfl
    rw [hswt]
    constructor
    · intro h
      by_contra hc
      obtain ⟨g, hg⟩ := (exists_gates a₀ μ (qbfEnc B Bs φ)).mpr (hnot.mpr hc)
      exact h g hg
    · intro h g hg
      exact hnot.mp hg.2 h
  | true =>
    have hswf : qbfSwap Bs = false := by rw [hsw, hp]; rfl
    have hχ : qbfEnc B Bs φ = (mergeHom (B :: Bs) L).onSentence φ := by
      rw [qbfEnc, hswf]; rfl
    rw [hswf]
    refine (exists_gates a₀ μ (qbfEnc B Bs φ)).trans ?_
    rw [hχ]

/-- **Correctness of the reduction**: the interpreted quantified Boolean
formula is true exactly when the second-order sentence holds. -/
theorem qbfRed_correct [Finite A] [Nonempty A] :
    @DecisionProblem.Holds _ (QbfProblem (Bs.length + 1) true (!qbfSwap Bs))
        ((qbfRedInterp B Bs φ).Map A) _ ↔
      SORealize L A (B :: Bs) φ true := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have hlen := consLast_length (qbfGt B Bs φ) B Bs
  -- reading a propositional variable gives the assignment of its block
  have hcast : ∀ vt, Fin.cast hlen.symm (qbfMk B Bs φ vt) = markC (qbfGt B Bs φ) B Bs vt :=
    fun _ => rfl
  have hval : ∀ (νs : Fin (consLast (qbfGt B Bs φ) B Bs).length →
        (qbfRedInterp B Bs φ).Map A → Prop) vt x,
      qbfVal (fun j => νs (Fin.cast hlen.symm j)) (Sum.inr vt, x) ↔
        νs (markC (qbfGt B Bs φ) B Bs vt) (Sum.inr vt, x) := by
    intro νs vt x
    constructor
    · rintro ⟨j, hj, h⟩
      rw [qbfT_block_var] at hj
      subst hj
      exact h
    · intro h
      exact ⟨qbfMk B Bs φ vt, (qbfT_block_var _ _ _ _ _ _ _ _).mpr rfl, h⟩
  -- the read assignment splits into the block variables and the gates
  have hread : ∀ νs : Fin (consLast (qbfGt B Bs φ) B Bs).length →
        (qbfRedInterp B Bs φ).Map A → Prop,
      readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs =
        combineLast (qbfGt B Bs φ) B Bs
          (fun i' a => νs (markC (qbfGt B Bs φ) B Bs (Sum.inl i'))
            (Sum.inr (Sum.inl i'), pad a₀ a))
          (fun j x => νs (markC (qbfGt B Bs φ) B Bs (Sum.inr j))
            (Sum.inr (Sum.inr j), pad a₀ x)) :=
    fun νs => readAll_consLast (qbfGt B Bs φ) (fun {_} a => pad a₀ a) B Bs
      (fun z u => (Sum.inr z, u)) νs
  -- the QBF matrix is the Tseitin condition at the assignment it encodes
  have hcompat : ∀ νs : Fin (consLast (qbfGt B Bs φ) B Bs).length →
        (qbfRedInterp B Bs φ).Map A → Prop,
      QbfMatrix (!qbfSwap Bs) (fun j => νs (Fin.cast hlen.symm j)) ↔
        xorP (qbfSwap Bs)
          (Gates (atomPart (qbfGt B Bs φ) B Bs
              (readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs))
            (qbfEnc B Bs φ)
            (fun m q w => gatePart (qbfGt B Bs φ) B Bs
              (readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs) ⟨m, q⟩ (pad a₀ w)) ∧
          RealizeWith (atomPart (qbfGt B Bs φ) B Bs
              (readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs))
            (qbfEnc B Bs φ) finZeroElim) := by
    intro νs
    have hatom : atomPart (qbfGt B Bs φ) B Bs
          (readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs) =
        padAssign a₀ (fun vt x =>
          qbfVal (fun j => νs (Fin.cast hlen.symm j)) (Sum.inr vt, x)) := by
      rw [hread νs]
      refine (atomPart_combineLast (qbfGt B Bs φ) B Bs _ _).trans ?_
      exact funext fun i' => funext fun a => propext (hval νs (Sum.inl i') _).symm
    have hgate : (fun m q w => gatePart (qbfGt B Bs φ) B Bs
          (readAll (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) νs) ⟨m, q⟩ (pad a₀ w)) =
        padVal a₀ (fun vt x =>
          qbfVal (fun j => νs (Fin.cast hlen.symm j)) (Sum.inr vt, x)) := by
      rw [hread νs]
      have hg := gatePart_combineLast (qbfGt B Bs φ) B Bs
        (fun i' a => νs (markC (qbfGt B Bs φ) B Bs (Sum.inl i')) (Sum.inr (Sum.inl i'), pad a₀ a))
        (fun j x => νs (markC (qbfGt B Bs φ) B Bs (Sum.inr j)) (Sum.inr (Sum.inr j), pad a₀ x))
      refine funext fun m => funext fun q => funext fun w => ?_
      rw [hg]
      change νs (markC (qbfGt B Bs φ) B Bs (Sum.inr ⟨m, q⟩))
            (Sum.inr (Sum.inr ⟨m, q⟩), pad a₀ (pad a₀ w)) =
          qbfVal (fun j => νs (Fin.cast hlen.symm j)) (Sum.inr (Sum.inr ⟨m, q⟩), pad a₀ w)
      rw [pad_full]
      exact propext (hval νs (Sum.inr ⟨m, q⟩) _).symm
    rw [qbfMatrix_eq_xorP, hatom, hgate]
    refine xorP_congr (qbfSwap Bs) ?_
    refine Iff.trans (qbfT_clauses_iff (Bs.length + 1) (qbfSwap Bs) (mergeBlocks (B :: Bs))
      (qbfEnc B Bs φ) (qbfMk B Bs φ) ha₀ (qbfVal fun j => νs (Fin.cast hlen.symm j))) ?_
    rw [satCond_iff_gates ha₀ (arity_le_tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ))
      (qbfEnc B Bs φ) (maxCtx_le_tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ))]
    exact and_congr_right fun hg => gates_realize _ (qbfEnc B Bs φ) _ hg finZeroElim
  -- the reading is surjective at every block
  have hsurj : ReadSurj (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) :=
    readSurj_consLast (qbfGt B Bs φ) (fun {_} a => pad a₀ a) B Bs (fun z u => (Sum.inr z, u))
      (fun z z' u u' h => by
        simp only [Prod.mk.injEq, Sum.inr.injEq] at h
        exact h)
      (fun i a a' h => by
        have hb : (mergeBlocks (consLast (qbfGt B Bs φ) B Bs)).arity i ≤
            tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ) :=
          arity_consLast_le (qbfGt B Bs φ) (fun _ => le_rfl) B Bs
            (arity_le_tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)) i
        rw [← pref_pad a₀ hb a, ← pref_pad a₀ hb a', h])
  -- the chain
  have h1 := (altQuant_cast (A := (qbfRedInterp B Bs φ).Map A) hlen
    (fun νs => QbfMatrix (!qbfSwap Bs) νs) true).symm
  have h2 := altQuant_iff_altAssign (consLast (qbfGt B Bs φ) B Bs) (qbfRd B Bs φ a₀) hsurj
    (fun νs => QbfMatrix (!qbfSwap Bs) fun j => νs (Fin.cast hlen.symm j))
    (fun μ => xorP (qbfSwap Bs)
      (Gates (atomPart (qbfGt B Bs φ) B Bs μ) (qbfEnc B Bs φ)
          (fun m q w => gatePart (qbfGt B Bs φ) B Bs μ ⟨m, q⟩ (pad a₀ w)) ∧
        RealizeWith (atomPart (qbfGt B Bs φ) B Bs μ) (qbfEnc B Bs φ) finZeroElim))
    hcompat true
  refine h1.trans (h2.trans ?_)
  refine Iff.trans (altAssign_consLast (qbfGt B Bs φ) B Bs _ true) ?_
  refine Iff.trans (altAssign_congr (B :: Bs) _ _ (fun μ => ?_) true)
    (sorealize_iff_altAssign (B :: Bs) L A inferInstance φ true).symm
  refine Iff.trans (iff_of_eq (congrArg (quantB (innerPol Bs.length true))
    (funext fun g => by rw [atomPart_combineLast, gatePart_combineLast]))) ?_
  exact (qbf_inner B Bs φ a₀ μ).trans (realize_eq_realizeWith μ _).symm

/-- **The generic marked Tseitin reduction**: an ordered first-order reduction
to a quantified Boolean formula problem, from any problem defined on nonempty
finite structures by a second-order sentence with a nonempty prefix. -/
noncomputable def qbfReduction (Q : DecisionProblem L)
    (hφ : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      Q A ↔ SORealize L A (B :: Bs) φ true) :
    Q ≤ᶠᵒ[≤] QbfProblem (Bs.length + 1) true (!qbfSwap Bs) where
  Tag := TseitinTag (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)
  dim := tseitinDim (mergeBlocks (B :: Bs)) (qbfEnc B Bs φ)
  toInterpretation := qbfRedInterp B Bs φ
  correct A _ _ _ _ := (hφ A).trans (qbfRed_correct B Bs φ).symm

end Correct

end Reduction

/-! ### Hardness -/

/-- **Hardness of QBF**: every problem definable by a second-order sentence
with `k + 1` alternating blocks starting existentially admits an ordered
first-order reduction to `DescriptiveComplexity.QBF (k + 1)`.

This is the Cook–Levin discharge one level up: the quantifier prefix is merged
into a single block, its first-order kernel is Tseitin-translated into a CNF
instance inside an ordered input structure, and the propositional variables
are marked with the block they belong to – the gate variables with the
innermost one, which is why the matrix and the encoded sentence follow the
parity of `k + 1`. -/
theorem qbf_hard_of_sigmaSODefinable (k : ℕ) :
    ∀ {L : Language.{0, 0}} (Q : DecisionProblem L),
      SigmaSODefinable (k + 1) Q → Nonempty (Q ≤ᶠᵒ[≤] QBF (k + 1)) := by
  rintro L Q ⟨Bs, hlen, φ, hφ⟩
  cases Bs with
  | nil => exact absurd hlen (by simp)
  | cons B Bs' =>
    obtain rfl : Bs'.length = k := by simpa using hlen
    have hm : QBF (Bs'.length + 1) = QbfProblem (Bs'.length + 1) true (!qbfSwap Bs') := by
      rw [QBF, qbfSwap_eq, Bool.not_not]
    rw [hm]
    exact ⟨qbfReduction B Bs' φ Q hφ⟩


end DescriptiveComplexity
