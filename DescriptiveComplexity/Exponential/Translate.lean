/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Peel

/-!
# The translation lemma

**A first-order sentence over an exponential expansion is a second-order
sentence over the base.** This is the type-lowering reading of
[Henkin 1950][henkin1950completeness] made into a theorem, and the honest
statement of the obstruction that keeps an interpretation from being composed
*after* an expansion: a quantifier ranging over the points of `X.Map A` ranges
over block assignments, so it is a second-order quantifier over `A`. The
translation writes that down rather than avoiding it.

The construction is the standard one, with everything it needs already built.

* **Prenex first.** `FirstOrder.Language.BoundedFormula.toPrenex` puts the
  sentence in prenex form, so the quantifiers can be peeled from the outside.
  The recursion runs on the `FirstOrder.Language.BoundedFormula.IsPrenex`
  *proof*, not on the formula: `∃` is encoded as `∼(∼φ).all`, which no
  structural recursion can match, while `IsPrenex` carries `all` and `ex` as
  genuine constructors.
* **One quantifier, two rounds.** `DescriptiveComplexity.SORealize` alternates
  strictly, while a prenex prefix has runs of the same quantifier. Each
  quantifier therefore takes **two** rounds – one `∃`, one `∀` – of which one
  is real and the other vacuous. Every round is guarded to hold a point
  (`DescriptiveComplexity.ExpExpansion.stepF`), so a vacuous round is
  discharged by `DescriptiveComplexity.ExpExpansion.mapNonempty` rather than by
  a syntactic independence argument, and the matrix may read *every* round.
* **The rounds are addressed absolutely.** The matrix mentions the outermost
  quantifiers, so a round is named by its index in the merged block rather than
  relative to the quantifier being peeled. Peeling then instantiates the outer
  rounds one at a time, which is what the `ext` parameter of
  `DescriptiveComplexity.ExpExpansion.exists_transl` tracks: it places the
  rounds that remain at their absolute positions and fills the positions below
  with the points already chosen.

**The sentence is produced existentially**, not by a total recursive
definition. That is what keeps the round arithmetic honest: the inequalities
saying that the rounds a subformula needs exist are in scope exactly where the
`Fin`-indices are built, so no fallback round and no cast is needed anywhere.
The number of rounds is likewise produced by the induction (the `d` of
`DescriptiveComplexity.ExpExpansion.exists_transl`) instead of by a second
recursion counting quantifiers.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : ExpExpansion L}

/-! ### The kernel, read at an arbitrary family of rounds -/

variable (X) in
/-- The structure the kernel of the translation is realized against: the base,
expanded by one copy of the point block per round. It is
`DescriptiveComplexity.ExpExpansion.prefixStructure` with the rounds allowed to
hold assignments not (yet) known to be points. -/
@[instance_reducible]
noncomputable def roundStructure {n : ℕ} {A : Type} [L.Structure A] [LinearOrder A]
    (ρs : Fin n → X.pointBlock.Assignment A) :
    ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Structure A :=
  (repMerged X.pointBlock n).structure₁ (L := L.sum Language.order)
    (repBlockAssign X.pointBlock A n ρs)

/-! ### Freeing the bound variables of the matrix -/

/-- Turning the bound variables of a quantifier-free formula into free ones
keeps it quantifier-free. -/
theorem isQF_toFormula {L' : Language.{0, 0}} {α : Type} {k : ℕ}
    {ψ : L'.BoundedFormula α k} (hψ : ψ.IsQF) : ψ.toFormula.IsQF := by
  induction hψ with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic hat =>
    cases hat with
    | equal t₁ t₂ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

variable (X) in
/-- **The matrix of the prefix**: the quantifier-free matrix of a prenex
sentence, its bound variables freed and each sent to the round holding its
point. -/
noncomputable def matrixF {n j : ℕ} (hv : Fin j → Fin n)
    (ψ : (X.E.sum Language.order).BoundedFormula Empty j) :
    ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence :=
  translQF X n finZeroElim (ψ.toFormula.relabel (Sum.elim Empty.elim hv))

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The matrix says what it should**: read against the rounds, it holds
exactly when the formula holds of the points they carry. -/
theorem realize_matrixF {n j : ℕ} (pts : Fin n → X.Map A) (hv : Fin j → Fin n)
    {ψ : (X.E.sum Language.order).BoundedFormula Empty j} (hqf : ψ.IsQF) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A (roundStructure X (roundAssign pts)) (matrixF X hv ψ) ↔
      ψ.Realize (M := X.Map A) default fun i => pts (hv i)) := by
  let := X.mapLinearOrder A
  refine (realize_translQF pts ((isQF_toFormula hqf).relabel _)).trans ?_
  refine Iff.trans (Formula.realize_relabel (g := Sum.elim Empty.elim hv) (v := pts)) ?_
  refine Iff.trans (BoundedFormula.realize_toFormula ψ _) ?_
  exact iff_of_eq (congrArg (fun v => ψ.Realize v fun i => pts (hv i))
    (funext fun e : Empty => e.elim))

/-! ### One quantifier, two rounds -/

variable (X) in
/-- The kernel contributed by one quantifier: its two rounds, each guarded to
hold a point – the first existentially, as a conjunct, the second universally,
as a hypothesis. -/
noncomputable def stepF {n : ℕ} (i₀ i₁ : Fin n)
    (K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence) :
    ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence :=
  roundPointGuardF X n i₀ ⊓ (roundPointGuardF X n i₁ ⟹ K)

omit [Finite A] [Nonempty A] in
/-- **Peeling a quantifier**: its two rounds become a point chosen
existentially and a point chosen universally, of which the kernel that remains
uses one. -/
theorem altBlockQuant_peel_step {n r : ℕ} (i₀ i₁ : Fin n)
    (K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence)
    (ext : (Fin (r + 2) → X.pointBlock.Assignment A) →
      (Fin n → X.pointBlock.Assignment A))
    (h₀ : ∀ τs, ext τs i₀ = τs 0) (h₁ : ∀ τs, ext τs i₁ = τs (Fin.succ 0)) :
    altBlockQuant A X.pointBlock (r + 2)
        (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) (stepF X i₀ i₁ K)) true ↔
      ∃ p : X.Map A, ∀ q : X.Map A,
        altBlockQuant A X.pointBlock r
          (fun τs => @Sentence.Realize _ A
            (roundStructure X (ext (Fin.cons (pointAssign p) (Fin.cons (pointAssign q) τs))))
            K) true := by
  have hsplit : ∀ τs : Fin (r + 2) → X.pointBlock.Assignment A,
      (@Sentence.Realize _ A (roundStructure X (ext τs)) (stepF X i₀ i₁ K) ↔
        IsPointAssign (X := X) (τs 0) ∧
          (IsPointAssign (X := X) (ext (Fin.cons (τs 0) (Fin.tail τs)) i₁) →
            @Sentence.Realize _ A
              (roundStructure X (ext (Fin.cons (τs 0) (Fin.tail τs)))) K)) := by
    intro τs
    let := roundStructure X (ext τs)
    have hguard : ∀ i : Fin n, (@Sentence.Realize _ A (roundStructure X (ext τs))
        (roundPointGuardF X n i) ↔ IsPointAssign (X := X) (ext τs i)) :=
      fun i => realize_roundPointGuardF (ext τs) i
    refine Iff.trans (Formula.realize_inf.trans (and_congr (hguard i₀)
      (Formula.realize_imp.trans (imp_congr (hguard i₁) Iff.rfl)))) ?_
    rw [h₀ τs, Fin.cons_self_tail]
    exact Iff.rfl
  refine Iff.trans (altBlockQuant_congr _ _ _ hsplit true) ?_
  refine Iff.trans (altBlockQuant_peel_ex (X := X) (fun σ υs =>
    IsPointAssign (X := X) (ext (Fin.cons σ υs) i₁) →
      @Sentence.Realize _ A (roundStructure X (ext (Fin.cons σ υs))) K)) ?_
  refine exists_congr fun p => ?_
  have hsplit' : ∀ υs : Fin (r + 1) → X.pointBlock.Assignment A,
      ((IsPointAssign (X := X) (ext (Fin.cons (pointAssign p) υs) i₁) →
          @Sentence.Realize _ A (roundStructure X (ext (Fin.cons (pointAssign p) υs))) K) ↔
        (IsPointAssign (X := X) (υs 0) →
          @Sentence.Realize _ A
            (roundStructure X (ext (Fin.cons (pointAssign p)
              (Fin.cons (υs 0) (Fin.tail υs))))) K)) := by
    intro υs
    rw [Fin.cons_self_tail, h₁, Fin.cons_succ]
  refine Iff.trans (altBlockQuant_congr _ _ _ hsplit' false) ?_
  exact altBlockQuant_peel_all (X := X) (fun σ ws =>
    @Sentence.Realize _ A
      (roundStructure X (ext (Fin.cons (pointAssign p) (Fin.cons σ ws)))) K)

/-- The bookkeeping shared by the two quantifier cases: once the two rounds of
a quantifier have been peeled into the points `p` and `q`, the induction
hypothesis applies at the round `c + 2`, its variables read at the family of
points updated at those two rounds. -/
theorem transl_step {n j c d : ℕ} (hc0 : c < n) (hc1 : c + 1 < n)
    {hv : Fin j → Fin n} (hlt : ∀ i, (hv i : ℕ) < c) (iv : Fin n)
    {K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence}
    {ψ : (X.E.sum Language.order).BoundedFormula Empty (j + 1)}
    (hK : ∀ (pts : Fin n → X.Map A)
        (ext : (Fin d → X.pointBlock.Assignment A) → (Fin n → X.pointBlock.Assignment A)),
        (∀ τs (k : Fin n), (k : ℕ) < c + 2 → ext τs k = pointAssign (pts k)) →
        (∀ τs (i : Fin d) (k : Fin n), (k : ℕ) = c + 2 + (i : ℕ) → ext τs k = τs i) →
        letI := X.mapLinearOrder A
        (altBlockQuant A X.pointBlock d
            (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) K) true ↔
          ψ.Realize (M := X.Map A) default fun i => pts ((Fin.snoc hv iv : Fin (j + 1) → Fin n) i)))
    (pts : Fin n → X.Map A)
    (ext : (Fin (d + 2) → X.pointBlock.Assignment A) → (Fin n → X.pointBlock.Assignment A))
    (hfix : ∀ τs (k : Fin n), (k : ℕ) < c → ext τs k = pointAssign (pts k))
    (hemb : ∀ τs (i : Fin (d + 2)) (k : Fin n), (k : ℕ) = c + (i : ℕ) → ext τs k = τs i)
    (p q : X.Map A) :
    letI := X.mapLinearOrder A
    (altBlockQuant A X.pointBlock d
        (fun τs => @Sentence.Realize _ A
          (roundStructure X (ext (Fin.cons (pointAssign p) (Fin.cons (pointAssign q) τs))))
          K) true ↔
      ψ.Realize (M := X.Map A) default
        (Fin.snoc (fun i => pts (hv i))
          (Function.update (Function.update pts ⟨c, hc0⟩ p) ⟨c + 1, hc1⟩ q iv))) := by
  let := X.mapLinearOrder A
  have hv0 : ((⟨c, hc0⟩ : Fin n) : ℕ) = c := rfl
  have hv1 : ((⟨c + 1, hc1⟩ : Fin n) : ℕ) = c + 1 := rfl
  set pts' := Function.update (Function.update pts ⟨c, hc0⟩ p) ⟨c + 1, hc1⟩ q with hpts'
  have hne : (⟨c, hc0⟩ : Fin n) ≠ ⟨c + 1, hc1⟩ := by
    intro h; exact absurd (congrArg Fin.val h) (by omega)
  have hpts0 : pts' ⟨c, hc0⟩ = p := by
    rw [hpts', Function.update_of_ne hne, Function.update_self]
  have hpts1 : pts' ⟨c + 1, hc1⟩ = q := by rw [hpts', Function.update_self]
  have hptsold : ∀ k : Fin n, (k : ℕ) < c → pts' k = pts k := by
    intro k hk
    have h0 : k ≠ ⟨c, hc0⟩ := by intro h; rw [h] at hk; omega
    have h1 : k ≠ ⟨c + 1, hc1⟩ := by intro h; rw [h] at hk; omega
    rw [hpts', Function.update_of_ne h1, Function.update_of_ne h0]
  refine Iff.trans (hK pts' (fun τs => ext (Fin.cons (pointAssign p) (Fin.cons (pointAssign q) τs)))
    (fun τs k hk => ?_) (fun τs i k hk => ?_)) ?_
  · rcases Nat.lt_or_ge (k : ℕ) c with hlt' | hge
    · rw [hfix _ k hlt', hptsold k hlt']
    · have hk0 : (k : ℕ) = c ∨ (k : ℕ) = c + 1 := by omega
      rcases hk0 with h | h
      · have hk' : k = ⟨c, hc0⟩ := Fin.ext h
        subst hk'
        rw [hemb _ 0 _ (by simp), Fin.cons_zero, hpts0]
      · have hk' : k = ⟨c + 1, hc1⟩ := Fin.ext h
        subst hk'
        rw [hemb _ (Fin.succ 0) _ (by simp), Fin.cons_succ, Fin.cons_zero, hpts1]
  · rw [hemb _ i.succ.succ _ (by simp [hk]; omega), Fin.cons_succ, Fin.cons_succ]
  · refine iff_of_eq (congrArg _ (funext fun i => ?_))
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hptsold _ (hlt i)

/-! ### The translation -/

/-- **The translation lemma, by induction on the prenex proof.** A prenex
formula with `j` bound variables, each already held by a round below `c`, is
translated into a sentence of the prefix quantified by the `r` rounds that
remain: `d` rounds are needed, two per quantifier. -/
theorem exists_transl {j : ℕ} {ψ : (X.E.sum Language.order).BoundedFormula Empty j}
    (hψ : ψ.IsPrenex) :
    ∃ d : ℕ, ∀ (n c r : ℕ), c + r = n → r = d → ∀ hv : Fin j → Fin n,
      (∀ i, (hv i : ℕ) < c) →
      ∃ K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence,
        ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
          letI := X.mapLinearOrder A
          ∀ (pts : Fin n → X.Map A)
            (ext : (Fin r → X.pointBlock.Assignment A) →
              (Fin n → X.pointBlock.Assignment A)),
            (∀ τs (k : Fin n), (k : ℕ) < c → ext τs k = pointAssign (pts k)) →
            (∀ τs (i : Fin r) (k : Fin n), (k : ℕ) = c + (i : ℕ) → ext τs k = τs i) →
            (altBlockQuant A X.pointBlock r
                (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) K) true ↔
              ψ.Realize (M := X.Map A) default fun i => pts (hv i)) := by
  induction hψ with
  | @of_isQF j ψ hqf =>
    refine ⟨0, fun n c r hcr hr hv _ => ⟨matrixF X hv ψ, ?_⟩⟩
    subst hr
    intro A _ _ _ _ pts ext hfix _
    have hc : c = n := by omega
    subst hc
    have hext : ext Fin.elim0 = roundAssign pts := funext fun k => hfix _ k k.isLt
    change (@Sentence.Realize _ A (roundStructure X (ext Fin.elim0)) _ ↔ _)
    rw [hext]
    exact realize_matrixF pts hv hqf
  | @all j ψ _ ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + 2, fun n c r hcr hr hv hlt => ?_⟩
    subst hr
    have hc0 : c < n := by omega
    have hc1 : c + 1 < n := by omega
    obtain ⟨K, hK⟩ := hd n (c + 2) d (by omega) rfl (Fin.snoc hv ⟨c + 1, hc1⟩)
      (fun i => Fin.lastCases (by rw [Fin.snoc_last]; exact Nat.lt_succ_self _)
        (fun i => by rw [Fin.snoc_castSucc]; exact lt_trans (hlt i) (by omega)) i)
    refine ⟨stepF X ⟨c, hc0⟩ ⟨c + 1, hc1⟩ K, fun A _ _ _ _ pts ext hfix hemb => ?_⟩
    let := X.mapLinearOrder A
    rw [altBlockQuant_peel_step ⟨c, hc0⟩ ⟨c + 1, hc1⟩ K ext
      (fun τs => hemb τs 0 _ (by simp)) (fun τs => hemb τs (Fin.succ 0) _ (by simp)),
      BoundedFormula.realize_all]
    have key : ∀ p q : X.Map A, _ ↔ _ :=
      fun p q => transl_step hc0 hc1 hlt ⟨c + 1, hc1⟩ (hK A) pts ext hfix hemb p q
    constructor
    · rintro ⟨p, hp⟩ a
      have h := (key p a).mp (hp a)
      rwa [Function.update_self] at h
    · intro h
      refine ⟨Classical.arbitrary _, fun q => (key _ q).mpr ?_⟩
      rw [Function.update_self]
      exact h q
  | @ex j ψ _ ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + 2, fun n c r hcr hr hv hlt => ?_⟩
    subst hr
    have hc0 : c < n := by omega
    have hc1 : c + 1 < n := by omega
    obtain ⟨K, hK⟩ := hd n (c + 2) d (by omega) rfl (Fin.snoc hv ⟨c, hc0⟩)
      (fun i => Fin.lastCases (by rw [Fin.snoc_last]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _))
        (fun i => by rw [Fin.snoc_castSucc]; exact lt_trans (hlt i) (by omega)) i)
    refine ⟨stepF X ⟨c, hc0⟩ ⟨c + 1, hc1⟩ K, fun A _ _ _ _ pts ext hfix hemb => ?_⟩
    let := X.mapLinearOrder A
    rw [altBlockQuant_peel_step ⟨c, hc0⟩ ⟨c + 1, hc1⟩ K ext
      (fun τs => hemb τs 0 _ (by simp)) (fun τs => hemb τs (Fin.succ 0) _ (by simp)),
      BoundedFormula.realize_ex]
    have hv0 : ((⟨c, hc0⟩ : Fin n) : ℕ) = c := rfl
    have hv1 : ((⟨c + 1, hc1⟩ : Fin n) : ℕ) = c + 1 := rfl
    have hne : (⟨c, hc0⟩ : Fin n) ≠ ⟨c + 1, hc1⟩ := by
      intro h; exact absurd (congrArg Fin.val h) (by omega)
    have key : ∀ p q : X.Map A, _ ↔ _ :=
      fun p q => transl_step hc0 hc1 hlt ⟨c, hc0⟩ (hK A) pts ext hfix hemb p q
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      have h := (key p (Classical.arbitrary _)).mp (hp _)
      rwa [Function.update_of_ne hne, Function.update_self] at h
    · rintro ⟨a, ha⟩
      refine ⟨a, fun q => (key a q).mpr ?_⟩
      rw [Function.update_of_ne hne, Function.update_self]
      exact ha

/-- **An `FO` sentence over an expansion is a second-order sentence over the
base.** The obstruction the exponential classes are built around, stated rather
than avoided: the quantifiers of a sentence read on the expanded universe become
second-order quantifier blocks over the base, two blocks per quantifier. -/
theorem exists_translate (X : ExpExpansion L) (φ : (X.E.sum Language.order).Sentence) :
    ∃ (Bs : List SOBlock) (ψ : (soLang (L.sum Language.order) Bs).Sentence) (pol : Bool),
      ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
        letI := X.mapLinearOrder A
        (@Sentence.Realize _ (X.Map A) _ φ ↔
          SORealize (L.sum Language.order) A Bs ψ pol) := by
  obtain ⟨d, hd⟩ := exists_transl (X := X) (φ.toPrenex_isPrenex)
  obtain ⟨K, hK⟩ := hd d 0 d (Nat.zero_add d) rfl Fin.elim0 (fun i => i.elim0)
  refine ⟨repBlocks X.pointBlock d,
    (unmergeHom (repBlocks X.pointBlock d) (L.sum Language.order)).onSentence K, true, ?_⟩
  intro A _ _ _ _
  let := X.mapLinearOrder A
  rw [sorealize_repBlocks X.pointBlock (L.sum Language.order) A inferInstance d K true]
  refine Iff.trans ?_ (hK A (fun _ => Classical.arbitrary _) id
    (fun _ k hk => absurd hk (Nat.not_lt_zero _)) (fun τs i k hk => by
      have : k = i := Fin.ext (by omega)
      rw [this]; rfl)).symm
  exact ((BoundedFormula.realize_toPrenex φ).symm.trans
    (iff_of_eq (congrArg _ (Subsingleton.elim _ _))))

end ExpExpansion

end DescriptiveComplexity
