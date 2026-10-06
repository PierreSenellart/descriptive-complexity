/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Sized

/-!
# Counting the solutions of exactly the threshold size, for sets of pairs

`DescriptiveComplexity.Counting.Sized` one arity up. Where the objective of a threshold
problem counts *arcs* – Feedback Arc Set – the threshold is the size of a
marked *binary* relation, the solution is a binary relation too, and “the two
have the same size” is certified by a bijection between two sets of pairs.
The unique one is again the monotone one, for the lexicographic order on
pairs, and the variable that guesses it is quaternary
(`DescriptiveComplexity.sizedPairsKernel`, `DescriptiveComplexity.witnessCount_sizedPairsKernel`,
`DescriptiveComplexity.sharpPDefinable_of_sizedPairs`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The block `B` extended with one quaternary relation variable, the monotone
bijection between two sets of pairs. -/
def SOBlock.withBij₂ (B : SOBlock) : SOBlock where
  ι := Unit ⊕ B.ι
  arity := Sum.elim (fun _ => 4) B.arity

section SizedPairs

variable (L : Language.{0, 0}) (B : SOBlock) {A : Type}

/-- The assignment of the original variables underlying an assignment of the
extended block. -/
def SOBlock.restPart₂ (ρ : B.withBij₂.Assignment A) : B.Assignment A :=
  fun i => ρ (Sum.inr i)

/-- The assignment of the extended block determined by a quaternary relation
and an assignment of the original block. -/
def SOBlock.joinBij₂ (R : (Fin 4 → A) → Prop) (ρ : B.Assignment A) :
    B.withBij₂.Assignment A :=
  fun p => match p with
    | Sum.inl _ => R
    | Sum.inr i => ρ i

/-- The inclusion of the vocabulary of an order-free kernel into that of the
sized kernel. -/
def sizedPairsLHom : L.sum B.lang →ᴸ (L.sum Language.order).sum B.withBij₂.lang where
  onFunction {_n} f :=
    match f with
    | Sum.inl g => Sum.inl (Sum.inl g)
    | Sum.inr g => nomatch g
  onRelation {n} r :=
    match n, r with
    | _, Sum.inl s => Sum.inl (Sum.inl s)
    | _, Sum.inr s => Sum.inr ⟨Sum.inr s.1, s.2⟩

/-- The structure of the sized kernel expands that of the order-free one. -/
theorem sizedPairsLHom_isExpansionOn (instA : L.Structure A) (lo : LinearOrder A)
    (ρ : B.withBij₂.Assignment A) :
    @LHom.IsExpansionOn _ _ (sizedPairsLHom L B) A
      (@sumStructure L B.lang A instA (B.structure (B.restPart₂ ρ)))
      (@sumStructure (L.sum Language.order) B.withBij₂.lang A
        (letI := instA; letI := lo; sumOrderStructure L A)
        (B.withBij₂.structure ρ)) := by
  let := instA
  let := lo
  let := B.structure (B.restPart₂ ρ)
  let := B.withBij₂.structure ρ
  exact
    { map_onFunction := fun {n} f x => by
        match f with
        | Sum.inl g => rfl
        | Sum.inr g => exact nomatch g
      map_onRelation := fun {n} r x => by
        match n, r with
        | _, Sum.inl s => rfl
        | _, Sum.inr s => rfl }

variable (mk : L.Relations 2) (i₀ : B.ι) (h₀ : B.arity i₀ = 2)

/-- The mark symbol over the vocabulary of the sized kernel. -/
abbrev sz₂MkSym : ((L.sum Language.order).sum B.withBij₂.lang).Relations 2 :=
  Sum.inl (Sum.inl mk)

/-- The sized relation, as a symbol of the sized kernel. -/
abbrev sz₂SelSym : ((L.sum Language.order).sum B.withBij₂.lang).Relations 2 :=
  Sum.inr ⟨Sum.inr i₀, h₀⟩

/-- The bijection variable, as a symbol of the sized kernel. -/
abbrev sz₂BijSym : ((L.sum Language.order).sum B.withBij₂.lang).Relations 4 :=
  Sum.inr ⟨Sum.inl (), rfl⟩

/-- The order symbol over the vocabulary of the sized kernel. -/
abbrev sz₂LeSym : ((L.sum Language.order).sum B.withBij₂.lang).Relations 2 :=
  Sum.inl (Sum.inr leSymb)

/-- The pair `(x, y)` is at most `(x', y')` lexicographically, as a
formula. -/
private def szPairLeF {α : Type} (x y x' y' : α) :
    ((L.sum Language.order).sum B.withBij₂.lang).Formula α :=
  (Relations.formula₂ (sz₂LeSym L B) (Term.var x) (Term.var x') ⊓
      ∼(Term.equal (Term.var x) (Term.var x'))) ⊔
    (Term.equal (Term.var x) (Term.var x') ⊓
      Relations.formula₂ (sz₂LeSym L B) (Term.var y) (Term.var y'))

/-- The bijection relates `(x, y)` to `(x', y')`, as a formula. -/
private def szPairBijF {α : Type} (x y x' y' : α) :
    ((L.sum Language.order).sum B.withBij₂.lang).Formula α :=
  Relations.formula (sz₂BijSym L B) ![Term.var x, Term.var y, Term.var x', Term.var y']

/-- The quaternary variable is the graph of a monotone bijection from the
marked pairs onto the sized relation, as a sentence. -/
noncomputable def monoBij₂S : ((L.sum Language.order).sum B.withBij₂.lang).Sentence :=
  Formula.iAlls (Fin 4)
      (szPairBijF L B (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3) ⟹
        Relations.formula₂ (sz₂MkSym L B mk) (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
          Relations.formula₂ (sz₂SelSym L B i₀ h₀) (Term.var (Sum.inr 2))
            (Term.var (Sum.inr 3))) ⊓
    (Formula.iAlls (Fin 2)
        (Relations.formula₂ (sz₂MkSym L B mk) (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⟹
          Formula.iExs (Fin 2) (szPairBijF L B (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1))
            (Sum.inr 0) (Sum.inr 1))) ⊓
      (Formula.iAlls (Fin 2)
          (Relations.formula₂ (sz₂SelSym L B i₀ h₀) (Term.var (Sum.inr 0))
              (Term.var (Sum.inr 1)) ⟹
            Formula.iExs (Fin 2) (szPairBijF L B (Sum.inr 0) (Sum.inr 1)
              (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 1)))) ⊓
        Formula.iAlls (Fin 8)
          (szPairBijF L B (Sum.inr 0) (Sum.inr 1) (Sum.inr 4) (Sum.inr 5) ⊓
              szPairBijF L B (Sum.inr 2) (Sum.inr 3) (Sum.inr 6) (Sum.inr 7) ⟹
            (szPairLeF L B (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)).iff
              (szPairLeF L B (Sum.inr 4) (Sum.inr 5) (Sum.inr 6) (Sum.inr 7)))))

/-- The pair `(a, b)`, as an argument of a variable of arity two. -/
def pairArg (a b : A) : Fin (B.arity i₀) → A := fun j => ![a, b] (Fin.cast h₀ j)

omit L in
theorem pairArg_eta (w : Fin (B.arity i₀) → A) :
    pairArg B i₀ h₀ (w (Fin.cast h₀.symm 0)) (w (Fin.cast h₀.symm 1)) = w := by
  funext j
  obtain ⟨k, rfl⟩ : ∃ k : Fin 2, j = Fin.cast h₀.symm k := ⟨Fin.cast h₀ j, by simp⟩
  fin_cases k <;> rfl

/-- Realization of the monotone-bijection sentence. -/
theorem realize_monoBij₂S (instA : L.Structure A) [LinearOrder A]
    (ρ : B.withBij₂.Assignment A) :
    @Sentence.Realize _ A
        (@sumStructure (L.sum Language.order) B.withBij₂.lang A _
          (B.withBij₂.structure ρ))
        (monoBij₂S L B mk i₀ h₀) ↔
      MonoBij (fun p : A ×ₗ A => RelMap mk ![(ofLex p).1, (ofLex p).2])
        (fun p : A ×ₗ A => ρ (Sum.inr i₀) (pairArg B i₀ h₀ (ofLex p).1 (ofLex p).2))
        fun p q : A ×ₗ A =>
          ρ (Sum.inl ()) ![(ofLex p).1, (ofLex p).2, (ofLex q).1, (ofLex q).2] := by
  let := B.withBij₂.structure ρ
  have hMk : ∀ (w : Fin 2 → A),
      RelMap (L := (L.sum Language.order).sum B.withBij₂.lang) (M := A)
        (sz₂MkSym L B mk) w ↔ RelMap mk w := fun _ => Iff.rfl
  have hSel : ∀ (a b : A),
      RelMap (L := (L.sum Language.order).sum B.withBij₂.lang) (M := A)
        (sz₂SelSym L B i₀ h₀) ![a, b] ↔ ρ (Sum.inr i₀) (pairArg B i₀ h₀ a b) :=
    fun _ _ => Iff.rfl
  have hBij : ∀ (w : Fin 4 → A),
      RelMap (L := (L.sum Language.order).sum B.withBij₂.lang) (M := A)
        (sz₂BijSym L B) w ↔ ρ (Sum.inl ()) w := fun _ => Iff.rfl
  have hLe : ∀ (w : Fin 2 → A),
      RelMap (L := (L.sum Language.order).sum B.withBij₂.lang) (M := A)
        (sz₂LeSym L B) w ↔ w 0 ≤ w 1 := fun _ => Iff.rfl
  have hlex : ∀ {α : Type} (v : α → A) (x y x' y' : α),
      (szPairLeF L B x y x' y').Realize v ↔
        (toLex (v x, v y) : A ×ₗ A) ≤ toLex (v x', v y') := by
    intro α v x y x' y'
    rw [Prod.Lex.toLex_le_toLex]
    simp only [szPairLeF, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      Formula.realize_equal, Formula.realize_rel₂, Term.realize_var, hLe,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact or_congr ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, h.ne⟩⟩ Iff.rfl
  have hbijF : ∀ {α : Type} (v : α → A) (x y x' y' : α),
      (szPairBijF L B x y x' y').Realize v ↔ ρ (Sum.inl ()) ![v x, v y, v x', v y'] := by
    intro α v x y x' y'
    rw [szPairBijF, Formula.realize_rel, hBij]
    refine iff_of_eq (congrArg _ (funext fun k => ?_))
    fin_cases k <;> rfl
  simp only [MonoBij, monoBij₂S, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs, Formula.realize_iff,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hMk, hSel, hbijF,
    hlex]
  refine and_congr ⟨fun h p q hpq => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h p hp => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h q hq => ?_, fun h i hi => ?_⟩
        ⟨fun h p p' q q' hpq hpq' => ?_, fun h i hi => ?_⟩))
  · exact h ![(ofLex p).1, (ofLex p).2, (ofLex q).1, (ofLex q).2] hpq
  · exact h (toLex (i 0, i 1)) (toLex (i 2, i 3)) hi
  · obtain ⟨j, hj⟩ := h ![(ofLex p).1, (ofLex p).2] hp
    exact ⟨toLex (j 0, j 1), hj⟩
  · obtain ⟨q, hq⟩ := h (toLex (i 0, i 1)) hi
    exact ⟨![(ofLex q).1, (ofLex q).2], hq⟩
  · obtain ⟨j, hj⟩ := h ![(ofLex q).1, (ofLex q).2] hq
    exact ⟨toLex (j 0, j 1), hj⟩
  · obtain ⟨p, hp⟩ := h (toLex (i 0, i 1)) hi
    exact ⟨![(ofLex p).1, (ofLex p).2], hp⟩
  · exact h ![(ofLex p).1, (ofLex p).2, (ofLex p').1, (ofLex p').2, (ofLex q).1,
      (ofLex q).2, (ofLex q').1, (ofLex q').2] ⟨hpq, hpq'⟩
  · exact h (toLex (i 0, i 1)) (toLex (i 2, i 3)) (toLex (i 4, i 5)) (toLex (i 6, i 7))
      hi.1 hi.2

variable (φ₀ : (L.sum B.lang).Sentence)

/-- **The sized kernel, for pairs**: the order-free kernel `φ₀`, and the extra
variable is the monotone bijection from the marked pairs onto the relation
`i₀`. -/
noncomputable def sizedPairsKernel :
    ((L.sum Language.order).sum B.withBij₂.lang).Sentence :=
  (sizedPairsLHom L B).onSentence φ₀ ⊓ monoBij₂S L B mk i₀ h₀

/-- Realization of the sized kernel for pairs. -/
theorem realize_sizedPairsKernel (instA : L.Structure A) [LinearOrder A]
    (ρ : B.withBij₂.Assignment A) :
    @Sentence.Realize _ A
        (@sumStructure (L.sum Language.order) B.withBij₂.lang A _
          (B.withBij₂.structure ρ))
        (sizedPairsKernel L B mk i₀ h₀ φ₀) ↔
      @Sentence.Realize (L.sum B.lang) A
          (@sumStructure L B.lang A instA (B.structure (B.restPart₂ ρ))) φ₀ ∧
        MonoBij (fun p : A ×ₗ A => RelMap mk ![(ofLex p).1, (ofLex p).2])
          (fun p : A ×ₗ A => ρ (Sum.inr i₀) (pairArg B i₀ h₀ (ofLex p).1 (ofLex p).2))
          fun p q : A ×ₗ A =>
            ρ (Sum.inl ()) ![(ofLex p).1, (ofLex p).2, (ofLex q).1, (ofLex q).2] := by
  have hmono := realize_monoBij₂S L B mk i₀ h₀ instA ρ
  have hexp := sizedPairsLHom_isExpansionOn L B instA inferInstance ρ
  let := B.structure (B.restPart₂ ρ)
  let := B.withBij₂.structure ρ
  rw [sizedPairsKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr (LHom.realize_onSentence A (sizedPairsLHom L B) φ₀) hmono

/-- **The witnesses of the sized kernel for pairs** are the assignments of the
block satisfying the order-free kernel whose relation has exactly as many pairs
as the marked relation, bijectively and whatever the linear order. -/
theorem witnessCount_sizedPairsKernel [instA : L.Structure A] [LinearOrder A] [Finite A] :
    witnessCount B.withBij₂ (sizedPairsKernel L B mk i₀ h₀ φ₀) A =
      Nat.card {ρ₀ : B.Assignment A //
        @Sentence.Realize (L.sum B.lang) A
            (@sumStructure L B.lang A instA (B.structure ρ₀)) φ₀ ∧
          {p : A × A | ρ₀ i₀ (pairArg B i₀ h₀ p.1 p.2)}.ncard =
            {p : A × A | RelMap mk ![p.1, p.2]}.ncard} := by
  have hfin : Finite (A ×ₗ A) := inferInstanceAs (Finite (A × A))
  have hex : ∀ ρ₀ : B.Assignment A,
      {p : A × A | ρ₀ i₀ (pairArg B i₀ h₀ p.1 p.2)}.ncard =
          {p : A × A | RelMap mk ![p.1, p.2]}.ncard →
        ∃ F : A ×ₗ A → A ×ₗ A → Prop,
          MonoBij (fun p : A ×ₗ A => RelMap mk ![(ofLex p).1, (ofLex p).2])
            (fun p : A ×ₗ A => ρ₀ i₀ (pairArg B i₀ h₀ (ofLex p).1 (ofLex p).2)) F :=
    fun ρ₀ h => exists_monoBij h
  refine Nat.card_congr
    { toFun := fun ρ => ⟨B.restPart₂ ρ.1,
        ((realize_sizedPairsKernel L B mk i₀ h₀ φ₀ instA ρ.1).mp ρ.2).1,
        ((realize_sizedPairsKernel L B mk i₀ h₀ φ₀ instA ρ.1).mp ρ.2).2.ncard_eq⟩
      invFun := fun ρ₀ =>
        ⟨B.joinBij₂ (fun w => (hex ρ₀.1 ρ₀.2.2).choose (toLex (w 0, w 1)) (toLex (w 2, w 3)))
            ρ₀.1,
          (realize_sizedPairsKernel L B mk i₀ h₀ φ₀ instA _).mpr
            ⟨ρ₀.2.1, (hex ρ₀.1 ρ₀.2.2).choose_spec⟩⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  rintro ⟨ρ, hρ⟩
  have hr := (realize_sizedPairsKernel L B mk i₀ h₀ φ₀ instA ρ).mp hρ
  have hF := (hex (B.restPart₂ ρ) hr.2.ncard_eq).choose_spec.ext hr.2
  refine Subtype.ext (funext fun p => ?_)
  cases p with
  | inl u =>
    refine funext fun (w : Fin 4 → A) => ?_
    exact (congrFun (congrFun hF (toLex (w 0, w 1))) (toLex (w 2, w 3))).trans
      (congrArg (ρ (Sum.inl ())) (funext fun k => by fin_cases k <;> rfl))
  | inr i => rfl

end SizedPairs

/-- **A count of the sets of pairs of exactly the threshold size is
`#P`-definable**, when the property of the solution is first-order: the size
is certified by the monotone bijection, for the lexicographic order, with the
marked relation. -/
theorem sharpPDefinable_of_sizedPairs {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) (B : SOBlock) (mk : L.Relations 2) (i₀ : B.ι)
    (h₀ : B.arity i₀ = 2) (φ₀ : (L.sum B.lang).Sentence)
    (hC : ∀ (A : Type) [instA : L.Structure A] [Finite A],
      C A = Nat.card {ρ₀ : B.Assignment A //
        @Sentence.Realize (L.sum B.lang) A
            (@sumStructure L B.lang A instA (B.structure ρ₀)) φ₀ ∧
          {p : A × A | ρ₀ i₀ (pairArg B i₀ h₀ p.1 p.2)}.ncard =
            {p : A × A | RelMap mk ![p.1, p.2]}.ncard}) :
    SharpPDefinable C :=
  ⟨B.withBij₂, sizedPairsKernel L B mk i₀ h₀ φ₀, fun A _ _ _ _ =>
    (hC A).trans (witnessCount_sizedPairsKernel L B mk i₀ h₀ φ₀).symm⟩

end DescriptiveComplexity
