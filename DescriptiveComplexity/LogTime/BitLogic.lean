/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.LogTime.Machine

/-!
# The bit-level logic, and definability in it

The syntax the machines of `DescriptiveComplexity.LogTime.Machine` decide, and
an API for building sentences of it the way
`DescriptiveComplexity.LogTime.Definable` builds sentences of `FO(≤, +, ×)`:
semantically, from the connectives and the quantifiers, with the sentence read
off only at the end.

## The logic

`DescriptiveComplexity.BitAtom`, over an arbitrary type of variables: the order,
the addition of ranks, the **bit at an index** `BitIx i x`, and an input relation
at a tuple of variables. Four atoms, and nothing here is `×`. This is
`FO(≤, +, BIT)` in the classical naming – `BIT(x, i)` with `i` an element – which
is what makes the bit atom a *reading* the machine can perform at a guessed
address, and the arithmetic of positions the plain arithmetic of the universe.

A `DescriptiveComplexity.BitSentence` is a quantifier prefix – a polarity per
variable, exactly the shape a machine's registers have – over a quantifier-free
`DescriptiveComplexity.BitKernel`. It is prenex by construction, and that is the
point: a machine has no normal form to apply, so the logic must arrive in one.

## Definability, and why the API is not the one for `ArithDef`

`DescriptiveComplexity.BitDef` says that a family of relations on valuations is
realized by *a prefix over a kernel*, not by an arbitrary formula. So the
closure lemmas cannot simply build a larger formula: each of them has to
**prenex as it goes**, and the three lemmas that let it do so are in
`DescriptiveComplexity.LogTime.Machine` –
`DescriptiveComplexity.prefixHolds_not` (negation dualizes a prefix),
`DescriptiveComplexity.prefixHolds_and_const` (a prefix absorbs a side
condition) and `DescriptiveComplexity.prefixHolds_add` (two prefixes
concatenate). That is what replaces a normal-form theorem, and it is why
disjunction is derived from negation and conjunction rather than proved: doing
so costs one `congr` instead of a fourth prefix lemma.

## Where it lands

`DescriptiveComplexity.BitDef.bitDefinable` reads a closed relation as a
sentence, and `DescriptiveComplexity.BitDefinable.ac0Definable` translates the
whole logic into `FO(≤, +, ×)` atom by atom. Three of the four atoms translate
outright (`DescriptiveComplexity.arithDef_le`, `_plus`, `_rel`); the bit atom
needs `DescriptiveComplexity.PowArithDef`, the definability of `i ↦ 2 ^ i`, which
is carried as a hypothesis and is the one classical theorem this development does
not prove. The converse direction, that a machine's acceptance is a sentence of
*this* logic rather than of the arithmetic one, is
`DescriptiveComplexity.LogTime.Simulate`, and it needs no such hypothesis.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {γ δ α β : Type}

/-! ### The syntax -/

/-- The atoms of the bit-level logic: the order, the addition of ranks, the bit
of an element at an index, and an input relation at a tuple of variables. -/
inductive BitAtom (L : Language.{0, 0}) (γ : Type) where
  /-- `x ≤ y`. -/
  | le (x y : γ) : BitAtom L γ
  /-- `orank x + orank y = orank z`. -/
  | plus (x y z : γ) : BitAtom L γ
  /-- The bit of `x` at the index `i` is set. -/
  | bit (i x : γ) : BitAtom L γ
  /-- An input relation at a tuple of variables. -/
  | rel {a : ℕ} (R : L.Relations a) (arg : Fin a → γ) : BitAtom L γ

/-- A quantifier-free kernel over the bit-level atoms. -/
inductive BitKernel (L : Language.{0, 0}) (γ : Type) where
  /-- An atom. -/
  | atom (a : BitAtom L γ) : BitKernel L γ
  /-- The constant `true`, so that a trivial relation needs no dummy variable. -/
  | tt : BitKernel L γ
  /-- Negation. -/
  | not (k : BitKernel L γ) : BitKernel L γ
  /-- Conjunction. -/
  | and (k k' : BitKernel L γ) : BitKernel L γ
  /-- Disjunction. -/
  | or (k k' : BitKernel L γ) : BitKernel L γ

/-- **A sentence of the bit-level logic, in prenex form**: a polarity per
variable and a quantifier-free kernel. Prenex by construction, which is what
makes the compilation into a machine a matter of atoms rather than of normal
forms. -/
structure BitSentence (L : Language.{0, 0}) where
  /-- The number of quantified variables. -/
  vars : ℕ
  /-- The quantifier at each variable: `true` existential, `false` universal. -/
  pol : Fin vars → Bool
  /-- The quantifier-free kernel. -/
  kernel : BitKernel L (Fin vars)

namespace BitAtom

/-- What an atom says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitAtom L γ → (γ → A) → Prop
  | .le x y, v => v x ≤ v y
  | .plus x y z, v => orank (v x) + orank (v y) = orank (v z)
  | .bit i x, v => BitIx (v i) (v x)
  | .rel R arg, v => RelMap R fun t => v (arg t)

/-- Renaming the variables of an atom. -/
def relabel (f : γ → δ) : BitAtom L γ → BitAtom L δ
  | .le x y => .le (f x) (f y)
  | .plus x y z => .plus (f x) (f y) (f z)
  | .bit i x => .bit (f i) (f x)
  | .rel R arg => .rel R fun t => f (arg t)

/-- Renaming is composition on the valuation. -/
theorem holds_relabel {A : Type} [L.Structure A] [LinearOrder A] [Finite A] (f : γ → δ)
    (a : BitAtom L γ) (v : δ → A) : (a.relabel f).Holds v ↔ a.Holds (v ∘ f) := by
  cases a <;> exact Iff.rfl

end BitAtom

namespace BitKernel

/-- What a kernel says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitKernel L γ → (γ → A) → Prop
  | .atom a, v => a.Holds v
  | .tt, _ => True
  | .not k, v => ¬ k.Holds v
  | .and k k', v => k.Holds v ∧ k'.Holds v
  | .or k k', v => k.Holds v ∨ k'.Holds v

/-- Renaming the variables of a kernel. -/
def relabel (f : γ → δ) : BitKernel L γ → BitKernel L δ
  | .atom a => .atom (a.relabel f)
  | .tt => .tt
  | .not k => .not (k.relabel f)
  | .and k k' => .and (k.relabel f) (k'.relabel f)
  | .or k k' => .or (k.relabel f) (k'.relabel f)

/-- Renaming is composition on the valuation. -/
theorem holds_relabel {A : Type} [L.Structure A] [LinearOrder A] [Finite A] (f : γ → δ)
    (k : BitKernel L γ) (v : δ → A) : (k.relabel f).Holds v ↔ k.Holds (v ∘ f) := by
  induction k with
  | atom a => exact a.holds_relabel f v
  | tt => exact Iff.rfl
  | not k ih => exact not_congr ih
  | and k k' ih ih' => exact and_congr ih ih'
  | or k k' ih ih' => exact or_congr ih ih'

end BitKernel

namespace BitSentence

/-- What a sentence says of an instance: the prefix, played over the kernel. -/
def Holds (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A] [Finite A] : Prop :=
  prefixHolds (A := A) φ.vars φ.pol fun v => φ.kernel.Holds v

end BitSentence

variable [L.IsRelational]

/-- A decision problem is **bit-definable** when a prenex sentence over the
order, the addition and the bit at an index – `FO(≤, +, BIT)` – decides it on
every nonempty finite ordered structure. -/
def BitDefinable (P : DecisionProblem L) : Prop :=
  ∃ φ : BitSentence L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ φ.Holds A

/-! ### Definable relations with free variables -/

section BitDef

variable {L : Language.{0, 0}}

/-- A family of relations is **bit-definable** when one quantifier prefix over
one quantifier-free bit-level kernel realizes it in every nonempty finite
ordered structure. The free variables are indexed by `α`, the quantified ones by
`Fin k`, exactly as a machine's registers are. -/
def BitDef (R : ArithRel L α) : Prop :=
  ∃ (k : ℕ) (pol : Fin k → Bool) (K : BitKernel L (α ⊕ Fin k)),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ prefixHolds k pol fun w => K.Holds (Sum.elim v w)

/-- Composing a valuation with a renaming that fixes the free variables. -/
theorem elim_comp_map {A : Type} (v : α → A) (u : γ → A) (f : δ → γ) :
    Sum.elim v u ∘ Sum.map (id : α → α) f = Sum.elim v (u ∘ f) := by
  funext z
  rcases z with a | d <;> rfl

namespace BitDef

/-- Definability transfers along a pointwise equivalence of relations. -/
theorem congr {R S : ArithRel L α} (h : BitDef R)
    (he : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
      R A v ↔ S A v) : BitDef S := by
  obtain ⟨k, pol, K, hK⟩ := h
  exact ⟨k, pol, K, fun A _ _ _ _ v => (he A v).symm.trans (hK A v)⟩

/-- **Renaming the free variables**. -/
theorem relabel {R : ArithRel L α} (h : BitDef R) (f : α → β) :
    BitDef (L := L) (α := β) fun A _ _ _ _ v => R A (v ∘ f) := by
  obtain ⟨k, pol, K, hK⟩ := h
  refine ⟨k, pol, K.relabel (Sum.map f id), fun A _ _ _ _ v => ?_⟩
  refine (hK A (v ∘ f)).trans (prefixHolds_congr k pol fun w => ?_)
  rw [K.holds_relabel]
  refine Iff.of_eq (_root_.congrArg K.Holds ?_)
  funext z
  rcases z with a | j <;> rfl

/-! #### Connectives -/

/-- The negation of a bit-definable relation is bit-definable: the prefix
dualizes. -/
theorem not {R : ArithRel L α} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ¬ R A v := by
  obtain ⟨k, pol, K, hK⟩ := h
  exact ⟨k, fun j => !pol j, K.not,
    fun A _ _ _ _ v => (not_congr (hK A v)).trans (prefixHolds_not k pol _)⟩

/-- The conjunction of two bit-definable relations is bit-definable: the two
prefixes concatenate. -/
theorem and {R S : ArithRel L α} (h : BitDef R) (h' : BitDef S) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => R A v ∧ S A v := by
  obtain ⟨k₁, pol₁, K₁, hK₁⟩ := h
  obtain ⟨k₂, pol₂, K₂, hK₂⟩ := h'
  refine ⟨k₁ + k₂, Fin.addCases pol₁ pol₂,
    (K₁.relabel (Sum.map id fun i => i.castAdd k₂)).and
      (K₂.relabel (Sum.map id fun j => j.natAdd k₁)), fun A _ _ _ _ v => ?_⟩
  have hp₁ : (fun i => Fin.addCases pol₁ pol₂ (i.castAdd k₂)) = pol₁ :=
    funext fun i => Fin.addCases_left _
  have hp₂ : (fun j => Fin.addCases pol₁ pol₂ (j.natAdd k₁)) = pol₂ :=
    funext fun j => Fin.addCases_right _
  have hsplit : ∀ u : Fin (k₁ + k₂) → A,
      ((K₁.relabel (Sum.map id fun i => i.castAdd k₂)).and
          (K₂.relabel (Sum.map id fun j => j.natAdd k₁))).Holds (Sum.elim v u) ↔
        K₁.Holds (Sum.elim v fun i => u (i.castAdd k₂)) ∧
          K₂.Holds (Sum.elim v fun j => u (j.natAdd k₁)) := by
    intro u
    refine and_congr ?_ ?_
    · rw [BitKernel.holds_relabel, elim_comp_map]
      exact Iff.rfl
    · rw [BitKernel.holds_relabel, elim_comp_map]
      exact Iff.rfl
  refine Iff.trans (and_congr (hK₁ A v) (hK₂ A v))
    (Iff.symm (Iff.trans (prefixHolds_congr _ _ hsplit) ?_))
  refine Iff.trans ?_
    (prefixHolds_and_const k₁ pol₁ (fun x => K₁.Holds (Sum.elim v x))
      (prefixHolds k₂ pol₂ fun y => K₂.Holds (Sum.elim v y)))
  refine Iff.trans (prefixHolds_add k₁ k₂ (Fin.addCases pol₁ pol₂)
    fun x y => K₁.Holds (Sum.elim v x) ∧ K₂.Holds (Sum.elim v y)) ?_
  rw [hp₁, hp₂]
  refine prefixHolds_congr k₁ pol₁ fun x => ?_
  exact (prefixHolds_congr k₂ pol₂ fun _ => and_comm).trans
    ((prefixHolds_and_const k₂ pol₂ _ _).trans and_comm)

/-- The always-true relation is bit-definable. -/
theorem top : BitDef (L := L) (α := α) fun _ _ _ _ _ _ => True :=
  ⟨0, Fin.elim0, .tt, fun _ _ _ _ _ _ => Iff.rfl⟩

/-- The always-false relation is bit-definable. -/
theorem bot : BitDef (L := L) (α := α) fun _ _ _ _ _ _ => False :=
  top.not.congr fun _ _ _ _ _ _ => ⟨fun h => h trivial, fun h => h.elim⟩

/-- The disjunction of two bit-definable relations is bit-definable, by De
Morgan: one `congr` rather than a fourth prefix lemma. -/
theorem or {R S : ArithRel L α} (h : BitDef R) (h' : BitDef S) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => R A v ∨ S A v :=
  (h.not.and h'.not).not.congr fun _ _ _ _ _ _ =>
    (not_congr not_or.symm).trans not_not

/-- An implication between bit-definable relations is bit-definable. -/
theorem imp {R S : ArithRel L α} (h : BitDef R) (h' : BitDef S) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => R A v → S A v :=
  (h.not.or h').congr fun _ _ _ _ _ _ => imp_iff_not_or.symm

/-- An equivalence between bit-definable relations is bit-definable. -/
theorem iff {R S : ArithRel L α} (h : BitDef R) (h' : BitDef S) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => (R A v ↔ S A v) :=
  ((h.imp h').and (h'.imp h)).congr fun _ _ _ _ _ _ =>
    ⟨fun hc => ⟨hc.1, hc.2⟩, fun hc => ⟨hc.mp, hc.mpr⟩⟩

/-- A case distinction made outside the structure is bit-definable when both
branches are. -/
theorem ite {R S : ArithRel L α} (c : Prop) [Decidable c] (h : BitDef R) (h' : BitDef S) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => if c then R A v else S A v := by
  by_cases hc : c
  · simpa [hc] using h
  · simpa [hc] using h'

/-- A truth value fixed outside the structure is bit-definable. -/
theorem prop (c : Prop) : BitDef (L := L) (α := α) fun _ _ _ _ _ _ => c := by
  by_cases hc : c
  · exact top.congr fun _ _ _ _ _ _ => by simp [hc]
  · exact bot.congr fun _ _ _ _ _ _ => by simp [hc]

/-- **A finite conjunction** of bit-definable relations, the index ranging over
a `Fin k` of the machine rather than of the instance. -/
theorem forallFin : ∀ {k : ℕ} {R : Fin k → ArithRel L α}, (∀ j, BitDef (R j)) →
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ∀ j, R j A v := by
  intro k
  induction k with
  | zero =>
    intro R _
    exact top.congr fun _ _ _ _ _ _ => ⟨fun _ j => j.elim0, fun _ => trivial⟩
  | succ k ih =>
    intro R h
    refine ((h 0).and (ih (R := fun j => R j.succ) fun j => h j.succ)).congr
      fun _ _ _ _ _ _ => ?_
    exact ⟨fun hc j => Fin.cases hc.1 (fun j' => hc.2 j') j, fun hall => ⟨hall 0, fun j => hall _⟩⟩

/-! #### Quantifiers -/

/-- **A quantifier prefix of `m` variables, prepended**. The new block is
outermost, so it is the first `m` indices of `Fin (m + k)`; this is the one
construction that touches the prefix, and `exs`/`alls` below are its
constant-polarity instances. A machine's register list is the general case. -/
theorem block {m : ℕ} (polB : Fin m → Bool) {R : ArithRel L (α ⊕ Fin m)} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v =>
      prefixHolds m polB fun w => R A (Sum.elim v w) := by
  obtain ⟨k, pol, K, hK⟩ := h
  refine ⟨m + k, Fin.addCases polB pol,
    K.relabel (Sum.elim (Sum.elim Sum.inl fun i => Sum.inr (i.castAdd k))
      fun j => Sum.inr (j.natAdd m)), fun A _ _ _ _ v => ?_⟩
  have hp₁ : (fun i : Fin m => Fin.addCases polB pol (i.castAdd k)) = polB :=
    funext fun i => Fin.addCases_left _
  have hp₂ : (fun j : Fin k => Fin.addCases polB pol (j.natAdd m)) = pol :=
    funext fun j => Fin.addCases_right _
  have hK' : ∀ u : Fin (m + k) → A,
      (K.relabel (Sum.elim (Sum.elim Sum.inl fun i => Sum.inr (i.castAdd k))
          fun j => Sum.inr (j.natAdd m))).Holds (Sum.elim v u) ↔
        K.Holds (Sum.elim (Sum.elim v fun i => u (i.castAdd k)) fun j => u (j.natAdd m)) := by
    intro u
    rw [BitKernel.holds_relabel]
    refine Iff.of_eq (_root_.congrArg K.Holds ?_)
    funext z
    rcases z with (a | i) | j <;> rfl
  refine Iff.trans (prefixHolds_congr m polB fun w => hK A (Sum.elim v w)) ?_
  refine Iff.symm (Iff.trans (prefixHolds_congr _ _ hK') ?_)
  refine Iff.trans (prefixHolds_add m k (Fin.addCases polB pol)
    fun x y => K.Holds (Sum.elim (Sum.elim v x) y)) ?_
  rw [hp₁, hp₂]

/-- **Existential quantification of a block** of `m` variables at once. -/
theorem exs {m : ℕ} {R : ArithRel L (α ⊕ Fin m)} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ∃ w : Fin m → A, R A (Sum.elim v w) :=
  (h.block fun _ => true).congr fun _ _ _ _ _ _ => prefixHolds_const_true m _

/-- **Universal quantification of a block** of `m` variables at once. -/
theorem alls {m : ℕ} {R : ArithRel L (α ⊕ Fin m)} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ∀ w : Fin m → A, R A (Sum.elim v w) :=
  (h.block fun _ => false).congr fun _ _ _ _ _ _ => prefixHolds_const_false m _

/-- **Existential quantification** of one variable, in the layout the
`ArithDef` API uses. -/
theorem ex {R : ArithRel L (α ⊕ Fin 1)} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ∃ a, R A (Sum.elim v fun _ => a) :=
  h.exs.congr fun _ _ _ _ _ _ => by
    refine ⟨fun hw => ?_, fun ha => ?_⟩
    · obtain ⟨w, hw⟩ := hw
      refine ⟨w 0, ?_⟩
      have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
        rw [Subsingleton.elim (0 : Fin 1) i]
      rwa [hw']
    · obtain ⟨a, ha⟩ := ha
      exact ⟨fun _ => a, ha⟩

/-- **Universal quantification** of one variable, in the same layout. -/
theorem all {R : ArithRel L (α ⊕ Fin 1)} (h : BitDef R) :
    BitDef (L := L) (α := α) fun A _ _ _ _ v => ∀ a, R A (Sum.elim v fun _ => a) :=
  h.alls.congr fun _ _ _ _ _ _ => by
    refine ⟨fun hw a => hw _, fun ha w => ?_⟩
    have hw' : (fun _ : Fin 1 => w 0) = w := funext fun i => by
      rw [Subsingleton.elim (0 : Fin 1) i]
    exact hw' ▸ ha (w 0)

end BitDef

/-! #### Atoms

Every atom is a kernel with an empty prefix, so each of these is `Iff.rfl`. -/

/-- The order between two variables is bit-definable. -/
theorem bitDef_le (x y : α) : BitDef (L := L) fun _ _ _ _ _ v => v x ≤ v y :=
  ⟨0, Fin.elim0, .atom (.le (Sum.inl x) (Sum.inl y)), fun _ _ _ _ _ _ => Iff.rfl⟩

/-- Addition of the ranks of three variables is bit-definable. -/
theorem bitDef_plus (x y z : α) :
    BitDef (L := L) fun _ _ _ _ _ v => orank (v x) + orank (v y) = orank (v z) :=
  ⟨0, Fin.elim0, .atom (.plus (Sum.inl x) (Sum.inl y) (Sum.inl z)), fun _ _ _ _ _ _ => Iff.rfl⟩

/-- The bit at an index is bit-definable: it is an atom of this logic, and the
one the machine reads by addressing. -/
theorem bitDef_bit (i x : α) :
    BitDef (L := L) fun _ _ _ _ _ v => BitIx (v i) (v x) :=
  ⟨0, Fin.elim0, .atom (.bit (Sum.inl i) (Sum.inl x)), fun _ _ _ _ _ _ => Iff.rfl⟩

/-- **Reading the input**: an input relation at a tuple of variables is
bit-definable. In the machine reading of this logic it is the query
instruction. -/
theorem bitDef_rel {a : ℕ} (R : L.Relations a) (arg : Fin a → α) :
    BitDef (L := L) fun _ _ _ _ _ v => RelMap R fun t => v (arg t) :=
  ⟨0, Fin.elim0, .atom (.rel R fun t => Sum.inl (arg t)), fun _ _ _ _ _ _ => Iff.rfl⟩

/-- The strict order is bit-definable. -/
theorem bitDef_lt (x y : α) : BitDef (L := L) fun _ _ _ _ _ v => v x < v y :=
  ((bitDef_le x y).and (bitDef_le y x).not).congr fun _ _ _ _ _ _ =>
    lt_iff_le_not_ge.symm

/-- Being the least element is bit-definable: `x + x = x`. -/
theorem bitDef_isZero (x : α) : BitDef (L := L) fun _ _ _ _ _ v => orank (v x) = 0 :=
  (bitDef_plus x x x).congr fun _ _ _ _ _ _ => by omega

/-- Being the least *nonzero* element is bit-definable. Where `FO(≤, +, ×)`
reads `orank x = 1` off the idempotence `x * x = x`, this logic has no `×` and
reads it off the order: nonzero, and below every nonzero element. -/
theorem bitDef_isOne (x : α) : BitDef (L := L) fun _ _ _ _ _ v => orank (v x) = 1 := by
  refine (((bitDef_isZero x).not).and
    ((((bitDef_isZero (Sum.inr 0 : α ⊕ Fin 1)).not).imp
      (bitDef_le (Sum.inl x) (Sum.inr 0))).all)).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h0, hle⟩
    by_contra hne
    have h1 : 2 ≤ orank (v x) := by omega
    have hcard : 1 < Nat.card A := by
      have hlt := orank_lt_card (v x)
      omega
    obtain ⟨y, hy⟩ := exists_orank_eq hcard
    have hxy : v x ≤ y := hle y (by omega)
    rw [← orank_le_iff] at hxy
    omega
  · intro h
    refine ⟨by omega, fun a ha => ?_⟩
    rw [← orank_le_iff]
    omega

/-- Being the greatest element is bit-definable, through the order alone. -/
theorem bitDef_isMax (x : α) :
    BitDef (L := L) fun A _ _ _ _ v => ∀ k : A, k ≤ v x :=
  (bitDef_le (L := L) (α := α ⊕ Fin 1) (Sum.inr 0) (Sum.inl x)).all

/-- **The top index is bit-definable**, and with nothing but the order and the
bit atom: it is the highest index carrying a bit of the greatest element
(`DescriptiveComplexity.isTopIx_iff_bits`). This is where the index naming pays
for itself – the end of the tape is *read*, where the place-value naming had to
compute a doubling that overflows. -/
theorem bitDef_isTopIx (i : α) : BitDef (L := L) fun _ _ _ _ _ v => IsTopIx (v i) := by
  have hk : BitDef (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1) fun _ _ _ _ _ w =>
      w (Sum.inl (Sum.inl i)) < w (Sum.inr 0) →
        ¬ BitIx (w (Sum.inr 0)) (w (Sum.inl (Sum.inr 0))) :=
    (bitDef_lt (Sum.inl (Sum.inl i)) (Sum.inr 0)).imp
      (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 0))).not
  have hm : BitDef (L := L) (α := α ⊕ Fin 1) fun A _ _ _ _ u =>
      (∀ k : A, k ≤ u (Sum.inr 0)) →
        (BitIx (u (Sum.inl i)) (u (Sum.inr 0)) ∧
          ∀ k : A, u (Sum.inl i) < k → ¬ BitIx k (u (Sum.inr 0))) :=
    (bitDef_isMax (Sum.inr 0)).imp
      ((bitDef_bit (Sum.inl i) (Sum.inr 0)).and hk.all)
  refine (hm.all).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h
    obtain ⟨m, hmax⟩ := exists_isMax A
    exact (isTopIx_iff_bits hmax).mpr (h m hmax)
  · intro h m hmax
    exact (isTopIx_iff_bits hmax).mp h

/-- **A low index is bit-definable** in the same way: one with a bit of the
greatest element above it. -/
theorem bitDef_isLowIx (i : α) : BitDef (L := L) fun _ _ _ _ _ v => IsLowIx (v i) := by
  have hk : BitDef (L := L) (α := (α ⊕ Fin 1) ⊕ Fin 1) fun _ _ _ _ _ w =>
      w (Sum.inl (Sum.inl i)) < w (Sum.inr 0) ∧
        BitIx (w (Sum.inr 0)) (w (Sum.inl (Sum.inr 0))) :=
    (bitDef_lt (Sum.inl (Sum.inl i)) (Sum.inr 0)).and
      (bitDef_bit (Sum.inr 0) (Sum.inl (Sum.inr 0)))
  have hm : BitDef (L := L) (α := α ⊕ Fin 1) fun A _ _ _ _ u =>
      (∀ k : A, k ≤ u (Sum.inr 0)) →
        ∃ k : A, u (Sum.inl i) < k ∧ BitIx k (u (Sum.inr 0)) :=
    (bitDef_isMax (Sum.inr 0)).imp hk.ex
  refine (hm.all).congr fun A _ _ _ _ v => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h
    obtain ⟨m, hmax⟩ := exists_isMax A
    exact (isLowIx_iff_bits hmax).mpr (h m hmax)
  · intro h m hmax
    exact (isLowIx_iff_bits hmax).mp h

/-- Equality is bit-definable, through the order. -/
theorem bitDef_eq (x y : α) : BitDef (L := L) fun _ _ _ _ _ v => v x = v y :=
  ((bitDef_le x y).and (bitDef_le y x)).congr fun _ _ _ _ _ _ =>
    ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end BitDef

/-! ### Into `FO(≤, +, ×)`

The translation that makes the bit-level logic a sub-notion of
`DescriptiveComplexity.AC0Definable` *without* going through the machine: atom
by atom, then the Boolean structure, then the prefix. Doing it here rather than
through `DescriptiveComplexity.LTDecidable.ac0Definable` is what lets the
simulation of a machine land in this logic rather than in the arithmetic one. -/

omit [L.IsRelational] in
/-- Every bit-level atom is an atom of `FO(≤, +, ×)` – **given the naming
bridge**, which is what the bit atom needs and the other three do not. -/
theorem BitAtom.arithDef (hpow : PowArithDef L) (a : BitAtom L γ) :
    ArithDef (L := L) (α := γ) fun _ _ _ _ _ v => a.Holds v := by
  cases a with
  | le x y => exact arithDef_le x y
  | plus x y z => exact arithDef_plus x y z
  | bit i x => exact hpow.arithDef_bitIx i x
  | rel R arg => exact arithDef_rel R arg

omit [L.IsRelational] in
/-- Every quantifier-free kernel is a formula of `FO(≤, +, ×)`, given the
bridge. -/
theorem BitKernel.arithDef (hpow : PowArithDef L) (k : BitKernel L γ) :
    ArithDef (L := L) (α := γ) fun _ _ _ _ _ v => k.Holds v := by
  induction k with
  | atom a => exact a.arithDef hpow
  | tt => exact ArithDef.top
  | not k ih => exact ih.not
  | and k k' ih ih' => exact ih.and ih'
  | or k k' ih ih' => exact ih.or ih'

/-- The renaming that peels the innermost quantified variable, moving it out of
the block and into the `Fin 1` the `ArithDef` quantifiers bind. -/
def peelVar (k : ℕ) : α ⊕ Fin (k + 1) → (α ⊕ Fin k) ⊕ Fin 1 :=
  Sum.elim (fun a => Sum.inl (Sum.inl a))
    (Fin.lastCases (Sum.inr 0) fun j => Sum.inl (Sum.inr j))

/-- Peeling a variable is `Fin.snoc` on the valuation. -/
theorem elim_comp_peelVar {A : Type} {k : ℕ} (u : α ⊕ Fin k → A) (a : A) :
    (Sum.elim u fun _ => a) ∘ peelVar k =
      Sum.elim (fun x => u (Sum.inl x)) (Fin.snoc (fun j => u (Sum.inr j)) a) := by
  funext z
  rcases z with x | j
  · rfl
  · induction j using Fin.lastCases with
    | last => simp [peelVar, Fin.snoc_last]
    | cast j' => simp [peelVar, Fin.snoc_castSucc]

omit [L.IsRelational] in
/-- **A quantifier prefix is a block of `ArithDef` quantifiers.** -/
theorem arithDef_prefixHolds : ∀ (k : ℕ) (pol : Fin k → Bool) {S : ArithRel L (α ⊕ Fin k)},
    ArithDef S →
      ArithDef (L := L) (α := α)
        fun A _ _ _ _ v => prefixHolds k pol fun w => S A (Sum.elim v w) := by
  intro k
  induction k with
  | zero =>
    intro pol S hS
    refine (hS.relabel (Sum.elim id Fin.elim0)).congr fun A _ _ _ _ v => ?_
    refine Iff.of_eq (_root_.congrArg (S A) ?_)
    funext z
    rcases z with a | j
    · rfl
    · exact j.elim0
  | succ k ih =>
    intro pol S hS
    have hT : ArithDef (L := L) (α := (α ⊕ Fin k) ⊕ Fin 1)
        (fun A _ _ _ _ z => S A (z ∘ peelVar k)) := hS.relabel (peelVar k)
    have hbody : ArithDef (L := L) (α := α ⊕ Fin k)
        (fun A _ _ _ _ u => if pol (Fin.last k) = true then
            ∃ a, S A (Sum.elim (fun x => u (Sum.inl x)) (Fin.snoc (fun j => u (Sum.inr j)) a))
          else ∀ a, S A (Sum.elim (fun x => u (Sum.inl x))
            (Fin.snoc (fun j => u (Sum.inr j)) a))) := by
      refine ArithDef.ite _ (hT.ex.congr fun A _ _ _ _ u => ?_)
        (hT.all.congr fun A _ _ _ _ u => ?_)
      · exact exists_congr fun a => Iff.of_eq (_root_.congrArg (S A) (elim_comp_peelVar u a))
      · exact forall_congr' fun a => Iff.of_eq (_root_.congrArg (S A) (elim_comp_peelVar u a))
    exact (ih (fun j => pol j.castSucc) hbody).congr fun A _ _ _ _ v => Iff.rfl

/-! ### From a closed relation to a sentence -/

/-- **The bridge to `DescriptiveComplexity.BitDefinable`**: a bit-definable
relation with no free variables *is* a sentence of the bit-level logic. -/
theorem BitDef.bitDefinable {P : DecisionProblem L} {R : ArithRel L Empty}
    (h : BitDef R)
    (hP : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R A Empty.elim) :
    BitDefinable P := by
  obtain ⟨k, pol, K, hK⟩ := h
  refine ⟨⟨k, pol, K.relabel (Sum.elim Empty.elim id)⟩, fun A _ _ _ _ => ?_⟩
  rw [hP A]
  refine (hK A Empty.elim).trans (prefixHolds_congr k pol fun w => ?_)
  rw [BitKernel.holds_relabel]
  refine Iff.of_eq (_root_.congrArg K.Holds ?_).symm
  funext z
  rcases z with e | j
  · exact e.elim
  · rfl

/-- **The bit-level logic is inside `FO(≤, +, ×)` once the namings are
bridged**: a `BitSentence` is an AC⁰ definition, proved directly rather than
through the machine, and the only thing it waits on is
`DescriptiveComplexity.PowArithDef` – the definability of `i ↦ 2 ^ i`, which is
[Immerman 1999][immerman1999descriptive] Thm 1.17(2). Everything else in the
translation is built. -/
theorem BitDefinable.ac0Definable {P : DecisionProblem L} (h : BitDefinable P)
    (hpow : PowArithDef L) : AC0Definable P := by
  obtain ⟨φ, hφ⟩ := h
  refine ArithDef.ac0Definable (R := fun A _ _ _ _ v =>
    prefixHolds φ.vars φ.pol fun w => φ.kernel.Holds fun j => Sum.elim v w (Sum.inr j)) ?_ ?_
  · exact arithDef_prefixHolds φ.vars φ.pol ((φ.kernel.arithDef hpow).relabel Sum.inr)
  · intro A _ _ _ _
    rw [hφ A]
    exact prefixHolds_congr φ.vars φ.pol fun w => Iff.rfl

end DescriptiveComplexity
