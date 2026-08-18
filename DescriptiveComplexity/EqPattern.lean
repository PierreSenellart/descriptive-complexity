/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Padding

/-!
# Data read only through its equality pattern is first-order definable

The keystone of every “write the program down as an interpretation” step, and
the one a machine emitted rule by rule needs.

A transition table's attributes – when a rule applies, what state it moves to,
what symbol it writes – are *functions of its data*, and an interpretation can
only emit them if they are first-order. Asking each rule for a formula is one
way; this file is the other, and the cheaper one:

> a rule may read its data only through the **equality pattern** of that data –
> which coordinates hold the least element, which hold the greatest, and which
> two coordinates are equal – and any such reading is first-order definable,
> once and for all.

The pattern type `DescriptiveComplexity.EqPat` is finite, so a predicate that
factors through it is the disjunction, over the finitely many patterns it
admits, of the conjunction of equalities and disequalities that pins a pattern
(`DescriptiveComplexity.patSetF`,
`DescriptiveComplexity.realize_patSetF_of_factors`).

**What it does and does not cover.** The pattern is what a machine's own
*bookkeeping* reads – flags, markers, which slot holds which designated element
– and the whole **write** side of a rule, since everything a program stores is a
copy, a designated element or a successor. It is not the whole guard language of
a program that evaluates a *logic*: such a program eventually compares two of
its slots in the order, or asks a relation of the source vocabulary of them, and
neither is a function of the pattern. `DescriptiveComplexity.Draw.UGDefinable`
therefore carries a formula, with the disjunction below as one way of building
it.

**Uniformity in the structure is the point.** An interpretation carries *one*
formula for every instance, so the factoring function must not depend on the
structure: what a caller owes is a single `Q : EqPat c → Prop` and, for every
`A` and every tuple, `P w ↔ Q (patOf bot top w)`. That is a `Prop` about the
attribute, provable where it is defined, rather than a syntax tree threaded
through every abstraction the program is built from – which is what makes this
affordable for a program assembled out of parameterized kits.

The two designated elements are the order's least and greatest, because those
are the only elements an interpretation can name; `DescriptiveComplexity.botF`
is `Padding`'s and `DescriptiveComplexity.topF` is its mirror.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The pattern of a tuple -/

section Pattern

variable {A : Type} {c : ℕ}

/-- **The equality pattern of a tuple**, against two designated elements: which
coordinates hold the first, which hold the second, and which two coordinates
are equal. A plain product, so that it is finite and has decidable equality
without ceremony. -/
abbrev EqPat (c : ℕ) : Type :=
  (Fin c → Bool) × (Fin c → Bool) × (Fin c → Fin c → Bool)

open Classical in
/-- The pattern a tuple has. -/
noncomputable def patOf (bot top : A) (w : Fin c → A) : EqPat c :=
  (fun i => decide (w i = bot), fun i => decide (w i = top),
    fun i j => decide (w i = w j))

open Classical in
theorem patOf_fst {bot top : A} {w : Fin c → A} (i : Fin c) :
    (patOf bot top w).1 i = true ↔ w i = bot := by
  rw [patOf]
  exact decide_eq_true_iff

open Classical in
theorem patOf_snd {bot top : A} {w : Fin c → A} (i : Fin c) :
    (patOf bot top w).2.1 i = true ↔ w i = top := by
  rw [patOf]
  exact decide_eq_true_iff

open Classical in
theorem patOf_same {bot top : A} {w : Fin c → A} (i j : Fin c) :
    (patOf bot top w).2.2 i j = true ↔ w i = w j := by
  rw [patOf]
  exact decide_eq_true_iff

end Pattern

/-! ### The greatest element, as a formula

`DescriptiveComplexity.botF` says a coordinate is a minimum; this is its
mirror, and the two are the only elements an interpretation can name. -/

section Top

variable {L : Language.{0, 0}} {γ : Type}

/-- `x` is a maximum of the order, as a formula. -/
noncomputable def topF (x : γ) : (L.sum Language.order).Formula γ :=
  Formula.iAlls (Fin 1)
    (Relations.formula₂ leSymb (Term.var (Sum.inr 0)) (Term.var (Sum.inl x)))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

theorem realize_topF {x : γ} : (topF (L := L) x).Realize v ↔ IsTop (v x) := by
  rw [topF]
  simp only [Formula.realize_iAlls, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, relMap_leSymb]
  exact ⟨fun h b => h fun _ => b, fun h i => h (i 0)⟩

end Top

/-! ### The successor of an element

The one thing a program writes that is neither a copy nor a designated
element: a loop variable **advanced**. In a finite linear order the cover of a
non-maximal element exists and is unique, so “the next element” is a total
function, first-order definable and – what matters here – a function of a
*single* coordinate, hence usable as the source of an output slot. -/

section Succ

variable {A : Type}

/-- In a finite linear order, an element that is not a maximum is covered. -/
theorem exists_covBy_of_not_isTop [LinearOrder A] [Finite A] {a : A}
    (h : ¬IsTop a) : ∃ b : A, a ⋖ b := by
  classical
  letI := Fintype.ofFinite A
  have hne : (Finset.univ.filter fun b : A => a < b).Nonempty := by
    obtain ⟨b, hb⟩ : ∃ b : A, ¬b ≤ a := by
      by_contra hc
      exact h fun b => not_not.mp fun hb => hc ⟨b, hb⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, not_le.mp hb⟩⟩
  refine ⟨(Finset.univ.filter fun b : A => a < b).min' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp ((Finset.univ.filter fun b : A => a < b).min'_mem hne)).2
  · intro c hac hcb
    exact absurd ((Finset.univ.filter fun b : A => a < b).min'_le c
      (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac⟩)) (not_le.mpr hcb)

/-- **Covers are unique in a linear order.** -/
theorem covBy_unique [LinearOrder A] {a b b' : A} (h : a ⋖ b) (h' : a ⋖ b') :
    b = b' := by
  rcases lt_trichotomy b b' with hlt | heq | hlt
  · exact absurd hlt (h'.2 h.1)
  · exact heq
  · exact absurd hlt (h.2 h'.1)

open Classical in
/-- **The next element**: the cover, where there is one, and the element
itself at the top – so that a loop variable at the end of its range simply
stands still, which is what `DescriptiveComplexity.Draw.tupNext` does. -/
noncomputable def ordSucc [Preorder A] (a : A) : A :=
  if h : ∃ b : A, a ⋖ b then h.choose else a

theorem covBy_ordSucc [Preorder A] {a : A} (h : ∃ b : A, a ⋖ b) : a ⋖ ordSucc a := by
  classical
  rw [ordSucc, dif_pos h]
  exact h.choose_spec

theorem ordSucc_of_not_covBy [Preorder A] {a : A} (h : ¬∃ b : A, a ⋖ b) :
    ordSucc a = a := by
  classical
  rw [ordSucc, dif_neg h]

/-- **The cover is the next element.** -/
theorem eq_ordSucc_of_covBy [LinearOrder A] {a b : A} (h : a ⋖ b) :
    b = ordSucc a :=
  covBy_unique h (covBy_ordSucc ⟨b, h⟩)

end Succ

/-! ### The formula of a pattern -/

section Formulas

variable {L : Language.{0, 0}} {γ : Type} {c : ℕ}

/-- `x` is covered by `y`, as a formula: below it, and nothing strictly
between. -/
noncomputable def covByF (x y : γ) : (L.sum Language.order).Formula γ :=
  (Relations.formula₂ leSymb (Term.var x) (Term.var y) ⊓
      ∼(Relations.formula₂ leSymb (Term.var y) (Term.var x))) ⊓
    Formula.iAlls (Fin 1)
      (Relations.formula₂ leSymb (Term.var (Sum.inr 0)) (Term.var (Sum.inl x)) ⊔
        Relations.formula₂ leSymb (Term.var (Sum.inl y)) (Term.var (Sum.inr 0)))

/-- **A literal**: a formula or its negation, by a bit. -/
def litF (b : Bool) (φ : (L.sum Language.order).Formula γ) :
    (L.sum Language.order).Formula γ :=
  if b then φ else ∼φ

/-- **A pattern, as a formula**: each coordinate is or is not the least
element, is or is not the greatest, and each pair of coordinates is or is not
equal – one literal per decision the pattern records. -/
noncomputable def patF (p : EqPat c) (x : Fin c → γ) :
    (L.sum Language.order).Formula γ :=
  listInf
    (((List.finRange c).map fun i => litF (p.1 i) (botF (x i))) ++
      ((List.finRange c).map fun i => litF (p.2.1 i) (topF (x i))) ++
      ((List.finRange c).flatMap fun i => (List.finRange c).map fun j =>
        litF (p.2.2 i j) (Term.equal (Term.var (x i)) (Term.var (x j)))))

open Classical in
/-- **A predicate on patterns, as a formula**: the disjunction of the patterns
it admits, which is a *finite* disjunction because the pattern type is. -/
noncomputable def patSetF (Q : EqPat c → Prop) (x : Fin c → γ) :
    (L.sum Language.order).Formula γ :=
  listSup (((Finset.univ : Finset (EqPat c)).filter Q).toList.map fun p => patF p x)

end Formulas

/-! ### Having a pattern -/

section Has

variable {A : Type} {c : ℕ}

/-- **A tuple has a pattern**: the three families of decisions, read as
conditions on the tuple. -/
def HasPat (bot top : A) (p : EqPat c) (w : Fin c → A) : Prop :=
  (∀ i, w i = bot ↔ p.1 i = true) ∧ (∀ i, w i = top ↔ p.2.1 i = true) ∧
    ∀ i j, w i = w j ↔ p.2.2 i j = true

open Classical in
/-- Every tuple has the pattern it is read off. -/
theorem hasPat_patOf (bot top : A) (w : Fin c → A) :
    HasPat bot top (patOf bot top w) w :=
  ⟨fun i => (patOf_fst i).symm, fun i => (patOf_snd i).symm,
    fun i j => (patOf_same i j).symm⟩

open Classical in
/-- And it has only that one. -/
theorem eq_patOf_of_hasPat {bot top : A} {p : EqPat c} {w : Fin c → A}
    (h : HasPat bot top p w) : p = patOf bot top w := by
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
    (funext fun i => funext fun j => ?_))
  · exact Bool.coe_iff_coe.mp ⟨fun hb => (patOf_fst i).mpr ((h.1 i).mpr hb),
      fun hb => (h.1 i).mp ((patOf_fst i).mp hb)⟩
  · exact Bool.coe_iff_coe.mp ⟨fun hb => (patOf_snd i).mpr ((h.2.1 i).mpr hb),
      fun hb => (h.2.1 i).mp ((patOf_snd i).mp hb)⟩
  · exact Bool.coe_iff_coe.mp
      ⟨fun hb => (patOf_same i j).mpr ((h.2.2 i j).mpr hb),
        fun hb => (h.2.2 i j).mp ((patOf_same i j).mp hb)⟩

end Has

/-! ### Their realization -/

section Realize

variable {L : Language.{0, 0}} {γ : Type} {c : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}
variable {bot top : A}

theorem realize_litF {b : Bool} {φ : (L.sum Language.order).Formula γ} :
    (litF b φ).Realize v ↔ (φ.Realize v ↔ b = true) := by
  cases b
  · simp only [litF, if_neg Bool.false_ne_true, Formula.realize_not]
    exact ⟨fun h => ⟨fun hc => absurd hc h, fun hc => absurd hc Bool.false_ne_true⟩,
      fun h hc => Bool.false_ne_true (h.mp hc)⟩
  · rw [litF, if_pos rfl]
    exact ⟨fun h => ⟨fun _ => rfl, fun _ => h⟩, fun h => h.mpr rfl⟩

theorem realize_covByF {x y : γ} : (covByF (L := L) x y).Realize v ↔ v x ⋖ v y := by
  rw [covByF]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_sup,
    Formula.realize_iAlls, Formula.realize_rel₂, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr, relMap_leSymb]
  constructor
  · rintro ⟨⟨hle, hnl⟩, hmid⟩
    refine ⟨lt_of_le_of_ne hle fun hc => hnl (le_of_eq hc.symm), fun c hc hcb => ?_⟩
    rcases hmid fun _ => c with h | h
    · exact absurd h (not_le.mpr hc)
    · exact absurd h (not_le.mpr hcb)
  · intro h
    refine ⟨⟨le_of_lt h.1, not_le.mpr h.1⟩, fun z => ?_⟩
    by_cases hz : z 0 ≤ v x
    · exact Or.inl hz
    · exact Or.inr (not_lt.mp fun hc => h.2 (not_le.mp hz) hc)

/-- In a linear order, being a minimum is being *the* designated minimum. -/
private theorem isBot_iff (hb : IsBot bot) (a : A) : IsBot a ↔ a = bot :=
  ⟨fun h => le_antisymm (h bot) (hb a), fun h => h ▸ hb⟩

/-- And dually. -/
private theorem isTop_iff (ht : IsTop top) (a : A) : IsTop a ↔ a = top :=
  ⟨fun h => le_antisymm (ht a) (h top), fun h => h ▸ ht⟩

/-- **A pattern's formula holds exactly of the tuples that have it.** -/
theorem realize_patF (hb : IsBot bot) (ht : IsTop top) (p : EqPat c)
    (x : Fin c → γ) :
    (patF (L := L) p x).Realize v ↔ HasPat bot top p fun i => v (x i) := by
  rw [patF, realize_listInf]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun i j => ?_⟩
    · have hm := realize_litF.mp (h _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))
      exact ((isBot_iff hb _).symm.trans realize_botF.symm).trans hm
    · have hm := realize_litF.mp (h _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))
      exact ((isTop_iff ht _).symm.trans realize_topF.symm).trans hm
    · have hm := realize_litF.mp (h _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
          List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩)))
      refine Iff.trans ?_ hm
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
  · intro h ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · rcases List.mem_append.mp hψ with hψ | hψ
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
        exact realize_litF.mpr (((realize_botF.trans (isBot_iff hb _)).trans (h.1 i)))
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
        exact realize_litF.mpr (((realize_topF.trans (isTop_iff ht _)).trans (h.2.1 i)))
    · obtain ⟨i, -, hψ⟩ := List.mem_flatMap.mp hψ
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
      refine realize_litF.mpr (Iff.trans ?_ (h.2.2 i j))
      rw [Formula.realize_equal, Term.realize_var, Term.realize_var]

open Classical in
/-- **A predicate on patterns is defined by its disjunction.** -/
theorem realize_patSetF (hb : IsBot bot) (ht : IsTop top) (Q : EqPat c → Prop)
    (x : Fin c → γ) :
    (patSetF (L := L) Q x).Realize v ↔ Q (patOf bot top fun i => v (x i)) := by
  rw [patSetF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hψ
    have hQ := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
    rwa [eq_patOf_of_hasPat ((realize_patF hb ht p x).mp hr)] at hQ
  · intro hQ
    refine ⟨patF (patOf bot top fun i => v (x i)) x, List.mem_map.mpr
      ⟨patOf bot top fun i => v (x i), Finset.mem_toList.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩), rfl⟩, ?_⟩
    exact (realize_patF hb ht _ x).mpr (hasPat_patOf bot top _)

end Realize

/-! ### Writing a tuple, slot by slot

The other half of what a machine's rules do: a rule not only *fires* on its
data, it also *writes*. Everything the EXPSPACE program writes is a copy of one
of its input slots or one of the two designated elements, chosen by the input's
pattern – so one more builder finishes the toolbox. -/

section Write

variable {A : Type} {c : ℕ}

/-- **Where an output slot's value comes from**: a slot of the input, one of
the two designated elements, or the *next* element after a slot of the input –
which is what a loop variable being advanced needs, and the only source that
reads the order. -/
inductive SlotVal (c : ℕ) : Type
  /-- Copy this coordinate of the input. -/
  | copy : Fin c → SlotVal c
  /-- The clear element. -/
  | bot : SlotVal c
  /-- The set element. -/
  | top : SlotVal c
  /-- The element after this coordinate of the input. -/
  | succ : Fin c → SlotVal c
  deriving DecidableEq

variable [LinearOrder A]

/-- What a source names, at a tuple. -/
noncomputable def SlotVal.eval (bot top : A) (w : Fin c → A) : SlotVal c → A
  | .copy k => w k
  | .bot => bot
  | .top => top
  | .succ k => ordSucc (w k)

end Write

section WriteFormula

variable {L : Language.{0, 0}} {γ : Type} {c : ℕ}

/-- **A slot's source, as a formula**: the target variable is that coordinate
of the input, or a minimum, or a maximum. -/
noncomputable def slotValF (u : Fin c → γ) (y : γ) :
    SlotVal c → (L.sum Language.order).Formula γ
  | .copy k => Term.equal (Term.var y) (Term.var (u k))
  | .bot => botF y
  | .top => topF y
  | .succ k =>
    covByF (u k) y ⊔ (topF (u k) ⊓ Term.equal (Term.var y) (Term.var (u k)))

open Classical in
/-- **A tuple written slot by slot from another**, as a formula: for the
pattern the input has, each output coordinate is what that pattern's source
names. A disjunction over the patterns, as everything here is. -/
noncomputable def writeTupF (G : EqPat c → Fin c → SlotVal c) (u y : Fin c → γ) :
    (L.sum Language.order).Formula γ :=
  listSup ((Finset.univ : Finset (EqPat c)).toList.map fun p =>
    patF p u ⊓ listInf ((List.finRange c).map fun k => slotValF u (y k) (G p k)))

end WriteFormula

section RealizeWrite

variable {L : Language.{0, 0}} {γ : Type} {c : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}
variable {bot top : A}

theorem realize_slotValF [Finite A] (hb : IsBot bot) (ht : IsTop top) (u : Fin c → γ)
    (y : γ) (sv : SlotVal c) :
    (slotValF (L := L) u y sv).Realize v ↔
      v y = sv.eval bot top fun k => v (u k) := by
  match sv with
  | .copy k =>
    rw [slotValF, Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact Iff.rfl
  | .bot => exact realize_botF.trans (isBot_iff hb _)
  | .top => exact realize_topF.trans (isTop_iff ht _)
  | .succ k =>
    rw [slotValF]
    simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_equal,
      Term.realize_var, realize_covByF, realize_topF, SlotVal.eval]
    by_cases hex : ∃ b : A, v (u k) ⋖ b
    · have hnt : ¬IsTop (v (u k)) := fun htop =>
        absurd (htop _) (not_le.mpr (covBy_ordSucc hex).1)
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | ⟨htop, -⟩
        · exact eq_ordSucc_of_covBy h
        · exact absurd htop hnt
      · exact Or.inl (h ▸ covBy_ordSucc hex)
    · have hnt : IsTop (v (u k)) := by
        by_contra hc
        exact hex (exists_covBy_of_not_isTop hc)
      rw [ordSucc_of_not_covBy hex]
      exact ⟨fun h => h.elim (fun hc => absurd (hnt _) (not_le.mpr hc.1)) fun h => h.2,
        fun h => Or.inr ⟨hnt, h⟩⟩

end RealizeWrite

section Realize

variable {L : Language.{0, 0}} {γ : Type} {c : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}
variable {bot top : A}

/-- **A predicate that reads its data only through the equality pattern is
first-order definable**, by one formula for every structure – which is what an
interpretation needs, since it carries one formula for all of them. This is
what a transition table's guard has to offer, and what a program assembled out
of parameterized kits can afford to offer: a `Prop` about the attribute where
it is defined, rather than syntax threaded through every abstraction. -/
theorem realize_patSetF_of_factors (hb : IsBot bot) (ht : IsTop top)
    {P : (Fin c → A) → Prop} {Q : EqPat c → Prop}
    (hP : ∀ w : Fin c → A, P w ↔ Q (patOf bot top w)) (x : Fin c → γ) :
    (patSetF (L := L) Q x).Realize v ↔ P fun i => v (x i) :=
  (realize_patSetF hb ht Q x).trans (hP _).symm

end Realize

end DescriptiveComplexity
