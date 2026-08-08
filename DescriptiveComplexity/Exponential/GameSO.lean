/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Game
import DescriptiveComplexity.Exponential.TagBits
import DescriptiveComplexity.SecondOrderMerge
import DescriptiveComplexity.Exponential.PSpaceOn

/-!
# A second-order quantifier prefix, played as a game

**The theorem**: every second-order sentence — an alternating prefix of block
quantifiers over a first-order kernel — defines a second-order alternating game
(`DescriptiveComplexity.soGameDefinable_soProblem`), whence
`DescriptiveComplexity.SigmaSODefinable.soGameDefinable` and `SO ⊆ SO-GAME`.

It is the game counterpart of
`DescriptiveComplexity.sotcDefinable_soProblem`, which peels the same prefix
into the state of a *walk*. A walk can only guess, so a universal block has to
be complemented away there; a game has universal moves, so the prefix is peeled
one block at a time with no complementation
(`DescriptiveComplexity.SOGameSpec.exBlock`).

## The construction

`DescriptiveComplexity.SOGameSpec.exBlock` prefixes a game with one quantified
block. Its states are the assignments of `SOBlock.cons B spec.B` extended by a
**phase** (`DescriptiveComplexity.SOGameSpec.Phase`, three arity-0 tag bits, as
`DescriptiveComplexity.SOBlock.withTag` supplies them):

* `pick` — the quantified block is chosen, by the existential or the universal
  player according to the polarity;
* `start` — the existential player chooses a starting state of the inner game.
  This phase is *always* existential and it is what a stuck position means:
  a specification with no starting state loses here, which is exactly
  `DescriptiveComplexity.SOGameSpec.Accepts` being false;
* `play` — the inner game is played, the chosen block frozen by every move
  (`DescriptiveComplexity.SOGameSpec.frozenS`).

Splitting `pick` from `start` is what makes the universal case correct: were the
choice of a starting state folded into a universal `pick` move, a block
assignment admitting no starting state would contribute no move at all and so
be silently skipped by the universal clause of
`DescriptiveComplexity.SOGameSpec.Wins`, instead of refuting it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOGameSpec

/-! ### The phases -/

/-- The three phases of a prefixed game. -/
inductive Phase
  /-- The quantified block is being chosen. -/
  | pick
  /-- A starting state of the inner game is being chosen. -/
  | start
  /-- The inner game is being played. -/
  | play
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.pick, .start, .play}, by intro x; cases x <;> simp⟩

/-! ### The state block -/

variable (L : Language.{0, 0}) (B M : SOBlock)

/-- The states of a prefixed game: an assignment of the quantified block, one of
the inner game's block, and a phase. -/
abbrev preBlock : SOBlock := (SOBlock.cons B M).withTag Phase

variable {B M} {A : Type}

/-- The state of a prefixed game at a phase, a chosen block and an inner
state. -/
def preAssign (p : Phase) (ρ : B.Assignment A) (σ : M.Assignment A) :
    (preBlock B M).Assignment A :=
  SOBlock.tagAssign p (consAssign ρ σ)

@[simp]
theorem dropTag_preAssign (p : Phase) (ρ : B.Assignment A) (σ : M.Assignment A) :
    SOBlock.dropTag (preAssign p ρ σ) = consAssign ρ σ :=
  rfl

/-- Every state of a prefixed game that carries a phase is of that shape. -/
theorem preAssign_eq (τ : (preBlock B M).Assignment A) (p : Phase)
    (hp : ∀ q : Phase, (τ (Sum.inl q) fun i => i.elim0) ↔ q = p) :
    τ = preAssign p (fun i => τ (Sum.inr (Sum.inl i))) fun j => τ (Sum.inr (Sum.inr j)) := by
  funext i
  match i with
  | Sum.inl q =>
    funext x
    haveI : IsEmpty (Fin ((preBlock B M).arity (Sum.inl q))) := inferInstanceAs (IsEmpty (Fin 0))
    have hx : x = fun i => i.elim0 := funext fun i => isEmptyElim i
    rw [hx]
    exact propext (hp q)
  | Sum.inr (Sum.inl _) => rfl
  | Sum.inr (Sum.inr _) => rfl

/-! ### Reading the inner game's sentences -/

variable (B M)

/-- The inner game's one-copy vocabulary, read in a prefixed state: the
quantified block and the inner block land in their components. -/
def preOneLHom :
    (((L.sum B.lang).sum Language.order).sum M.lang) →ᴸ
      ((L.sum Language.order).sum (preBlock B M).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => Sum.inl (Sum.inl g)
    | Sum.inl (Sum.inl (Sum.inr g)) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => Sum.inl (Sum.inl s)
    | Sum.inl (Sum.inl (Sum.inr s)) => Sum.inr ⟨Sum.inr (Sum.inl s.1), s.2⟩
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr s)
    | Sum.inr s => Sum.inr ⟨Sum.inr (Sum.inr s.1), s.2⟩

/-- The inner game's one-copy vocabulary, read in the **second** copy of a
prefixed state — what the move into the playing phase needs, the inner game's
starting condition being about the state the move enters. -/
def preSndLHom :
    (((L.sum B.lang).sum Language.order).sum M.lang) →ᴸ
      (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => Sum.inl (Sum.inl (Sum.inl g))
    | Sum.inl (Sum.inl (Sum.inr g)) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl s)) => Sum.inl (Sum.inl (Sum.inl s))
    | Sum.inl (Sum.inl (Sum.inr s)) => Sum.inr ⟨Sum.inr (Sum.inl s.1), s.2⟩
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inl (Sum.inr s))
    | Sum.inr s => Sum.inr ⟨Sum.inr (Sum.inr s.1), s.2⟩

/-- The inner game's two-copy vocabulary, read in a prefixed move: the
quantified block is read in the first copy, which every move freezes. -/
def preTwoLHom :
    ((((L.sum B.lang).sum Language.order).sum M.lang).sum M.lang) →ᴸ
      (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang) where
  onFunction {_} f :=
    match f with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl g))) => Sum.inl (Sum.inl (Sum.inl g))
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr g))) => isEmptyElim g
    | Sum.inl (Sum.inl (Sum.inr g)) => isEmptyElim g
    | Sum.inl (Sum.inr g) => isEmptyElim g
    | Sum.inr g => isEmptyElim g
  onRelation {_} r :=
    match r with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl s))) => Sum.inl (Sum.inl (Sum.inl s))
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr s))) => Sum.inl (Sum.inr ⟨Sum.inr (Sum.inl s.1), s.2⟩)
    | Sum.inl (Sum.inl (Sum.inr s)) => Sum.inl (Sum.inl (Sum.inr s))
    | Sum.inl (Sum.inr s) => Sum.inl (Sum.inr ⟨Sum.inr (Sum.inr s.1), s.2⟩)
    | Sum.inr s => Sum.inr ⟨Sum.inr (Sum.inr s.1), s.2⟩

variable {L B M} [instL : L.Structure A] [LinearOrder A]

theorem preOneLHom_isExpansionOn (p : Phase) (ρ : B.Assignment A) (σ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (preOneLHom L B M) A
      (@SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
        (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ)
      (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) (preAssign p ρ σ)) := by
  letI := B.structure₁ (L := L) ρ
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ
  letI := @SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ)
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => rfl
    | Sum.inl (Sum.inl (Sum.inr g)) => exact isEmptyElim g
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match n, r with
    | _, Sum.inl (Sum.inl (Sum.inl s)) => rfl
    | _, Sum.inl (Sum.inl (Sum.inr s)) => rfl
    | _, Sum.inl (Sum.inr s) => rfl
    | _, Sum.inr s => rfl

theorem realize_preOne (p : Phase) (ρ : B.Assignment A) (σ : M.Assignment A)
    (ψ : (((L.sum B.lang).sum Language.order).sum M.lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) (preAssign p ρ σ))
        ((preOneLHom L B M).onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
          (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ) ψ) := by
  letI := B.structure₁ (L := L) ρ
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ
  letI := @SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ)
  haveI := preOneLHom_isExpansionOn (L := L) (B := B) (M := M) p ρ σ
  exact LHom.realize_onSentence (M := A) (preOneLHom L B M) ψ

theorem preSndLHom_isExpansionOn (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (preSndLHom L B M) A
      (@SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
        (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ') _) σ')
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')) := by
  letI := B.structure₁ (L := L) ρ'
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ') _) σ'
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl g)) => rfl
    | Sum.inl (Sum.inl (Sum.inr g)) => exact isEmptyElim g
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match n, r with
    | _, Sum.inl (Sum.inl (Sum.inl s)) => rfl
    | _, Sum.inl (Sum.inl (Sum.inr s)) => rfl
    | _, Sum.inl (Sum.inr s) => rfl
    | _, Sum.inr s => rfl

theorem realize_preSnd (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A)
    (ψ : (((L.sum B.lang).sum Language.order).sum M.lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ'))
        ((preSndLHom L B M).onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
          (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ') _) σ') ψ) := by
  letI := B.structure₁ (L := L) ρ'
  letI := @SOBlock.structure₁ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ') _) σ'
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  haveI := preSndLHom_isExpansionOn (L := L) (B := B) (M := M) p q ρ ρ' σ σ'
  exact LHom.realize_onSentence (M := A) (preSndLHom L B M) ψ

theorem preTwoLHom_isExpansionOn (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (preTwoLHom L B M) A
      (@SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
        (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ σ')
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')) := by
  letI := B.structure₁ (L := L) ρ
  letI := @SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ σ'
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · match f with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl g))) => rfl
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr g))) => exact isEmptyElim g
    | Sum.inl (Sum.inl (Sum.inr g)) => exact isEmptyElim g
    | Sum.inl (Sum.inr g) => exact isEmptyElim g
    | Sum.inr g => exact isEmptyElim g
  · match n, r with
    | _, Sum.inl (Sum.inl (Sum.inl (Sum.inl s))) => rfl
    | _, Sum.inl (Sum.inl (Sum.inl (Sum.inr s))) => rfl
    | _, Sum.inl (Sum.inl (Sum.inr s)) => rfl
    | _, Sum.inl (Sum.inr s) => rfl
    | _, Sum.inr s => rfl

theorem realize_preTwo (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A)
    (ψ : ((((L.sum B.lang).sum Language.order).sum M.lang).sum M.lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ'))
        ((preTwoLHom L B M).onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
          (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ σ') ψ) := by
  letI := B.structure₁ (L := L) ρ
  letI := @SOBlock.structure₂ ((L.sum B.lang).sum Language.order) M A
    (@sumOrderStructure (L.sum B.lang) A (B.structure₁ (L := L) ρ) _) σ σ'
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  haveI := preTwoLHom_isExpansionOn (L := L) (B := B) (M := M) p q ρ ρ' σ σ'
  exact LHom.realize_onSentence (M := A) (preTwoLHom L B M) ψ

/-! ### The phase, and freezing the quantified block -/

variable (L B M)

/-- The tag bit of a phase, in a one-copy state. -/
noncomputable abbrev phaseF (p : Phase) :
    ((L.sum Language.order).sum (preBlock B M).lang).Sentence :=
  SOBlock.tagBitF (L := L.sum Language.order) (SOBlock.cons B M) Phase p

/-- The state is a well-formed one at the phase `p`. -/
noncomputable def atPhaseF (p : Phase) :
    ((L.sum Language.order).sum (preBlock B M).lang).Sentence :=
  SOBlock.tagGuardF (L := L.sum Language.order) (SOBlock.cons B M) Phase ⊓ phaseF L B M p

/-- The tag bit of a phase, in the second copy of a two-copy state. -/
noncomputable def phaseTwoF (p : Phase) :
    (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang).Sentence :=
  Relations.formula (Sum.inr (⟨Sum.inl p, rfl⟩ : (preBlock B M).lang.Relations 0)) Fin.elim0

open Classical in
/-- The second copy is a well-formed state at the phase `p`: its bit is set and
every other is not. -/
noncomputable def atPhaseTwoF (p : Phase) :
    (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang).Sentence :=
  phaseTwoF L B M p ⊓
    listInf ((finEnum Phase).map fun q => if q = p then ⊤ else ∼(phaseTwoF L B M q))

/-- The relation variable `i` of the quantified block, in the first copy. -/
abbrev preFstSym (i : B.ι) :
    (((L.sum Language.order).sum (preBlock B M).lang).sum
      (preBlock B M).lang).Relations (B.arity i) :=
  Sum.inl (Sum.inr ⟨Sum.inr (Sum.inl i), rfl⟩)

/-- The relation variable `i` of the quantified block, in the second copy. -/
abbrev preSndSym (i : B.ι) :
    (((L.sum Language.order).sum (preBlock B M).lang).sum
      (preBlock B M).lang).Relations (B.arity i) :=
  Sum.inr ⟨Sum.inr (Sum.inl i), rfl⟩

/-- The quantified block's variable `i` is unchanged by the move. -/
noncomputable def frozenAtS (i : B.ι) :
    (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang).Sentence :=
  Formula.iAlls (Fin (B.arity i))
    (((Relations.formula (preFstSym L B M i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (preSndSym L B M i) fun j => Term.var (Sum.inr j))) ⊓
      ((Relations.formula (preSndSym L B M i) fun j => Term.var (Sum.inr j)).imp
        (Relations.formula (preFstSym L B M i) fun j => Term.var (Sum.inr j))))

open Classical in
/-- **The quantified block is frozen**: every move of the playing phase leaves
it alone. -/
noncomputable def frozenS :
    (((L.sum Language.order).sum (preBlock B M).lang).sum (preBlock B M).lang).Sentence :=
  letI := Fintype.ofFinite B.ι
  listInf ((Finset.univ.toList : List B.ι).map (frozenAtS L B M))

variable {L B M}

theorem realize_phaseF (p q : Phase) (ρ : B.Assignment A) (σ : M.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) (preAssign q ρ σ)) (phaseF L B M p) ↔ p = q) :=
  SOBlock.realize_tagBitF (L := L.sum Language.order) (preAssign q ρ σ) p

theorem realize_atPhaseF (p q : Phase) (ρ : B.Assignment A) (σ : M.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) (preAssign q ρ σ)) (atPhaseF L B M p) ↔ p = q) := by
  letI := @SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign q ρ σ)
  refine Iff.trans Formula.realize_inf ?_
  refine Iff.trans (and_iff_right ?_) (realize_phaseF p q ρ σ)
  exact (SOBlock.realize_tagGuardF (L := L.sum Language.order) (preAssign q ρ σ)).mpr
    ⟨q, consAssign ρ σ, rfl⟩

/-- **A well-formed state**: one whose tag bits name a phase. -/
theorem exists_preAssign (τ : (preBlock B M).Assignment A)
    (h : @Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) τ)
      (SOBlock.tagGuardF (L := L.sum Language.order) (SOBlock.cons B M) Phase)) :
    ∃ (p : Phase) (ρ : B.Assignment A) (σ : M.Assignment A), τ = preAssign p ρ σ := by
  obtain ⟨p, ν, hν⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) τ).mp h
  refine ⟨p, fun i => ν (Sum.inl i), fun j => ν (Sum.inr j), ?_⟩
  rw [hν]
  exact congrArg (SOBlock.tagAssign p) (consAssign_split ν).symm

omit [LinearOrder A] in
/-- The argument tuple of a tag variable is the empty one, whatever it is. -/
theorem tagArg_subsingleton {r : Phase}
    (y z : Fin ((preBlock B M).arity (Sum.inl r)) → A) : y = z := by
  haveI : IsEmpty (Fin ((preBlock B M).arity (Sum.inl r))) := inferInstanceAs (IsEmpty (Fin 0))
  exact funext fun i => isEmptyElim i

/-- The tag bit of the second copy, read at an arbitrary state. -/
theorem realize_phaseTwoF' (r : Phase) (τ τ' : (preBlock B M).Assignment A)
    (x : Fin ((preBlock B M).arity (Sum.inl r)) → A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) τ τ') (phaseTwoF L B M r) ↔ τ' (Sum.inl r) x) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) τ τ'
  exact iff_of_eq (congrArg (τ' (Sum.inl r)) (tagArg_subsingleton _ x))

theorem realize_phaseTwoF (p q : Phase) (τ : (preBlock B M).Assignment A) (ρ' : B.Assignment A)
    (σ' : M.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) τ (preAssign q ρ' σ')) (phaseTwoF L B M p) ↔ p = q) := by
  exact realize_phaseTwoF' p τ (preAssign q ρ' σ') (fun i => i.elim0)

open Classical in
theorem realize_atPhaseTwoF (p q : Phase) (τ : (preBlock B M).Assignment A) (ρ' : B.Assignment A)
    (σ' : M.Assignment A) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) τ (preAssign q ρ' σ')) (atPhaseTwoF L B M p) ↔ p = q) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) τ (preAssign q ρ' σ')
  refine Iff.trans Formula.realize_inf ?_
  constructor
  · rintro ⟨h, -⟩
    exact (realize_phaseTwoF p q τ ρ' σ').mp h
  · intro hpq
    refine ⟨(realize_phaseTwoF p q τ ρ' σ').mpr hpq, ?_⟩
    rw [realize_listInf]
    intro ψ hψ
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hψ
    rcases eq_or_ne r p with rfl | hne
    · rw [if_pos rfl]
      exact Formula.realize_top.mpr trivial
    · rw [if_neg hne, Formula.realize_not]
      exact fun h => hne (((realize_phaseTwoF r q τ ρ' σ').mp h).trans hpq.symm)

open Classical in
/-- **The guarded phase of the second copy pins its shape**: a move that asserts
it lands on a well-formed state. -/
theorem exists_preAssign_two (p : Phase) (τ τ' : (preBlock B M).Assignment A)
    (h : @Sentence.Realize _ A
      (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
        (@sumOrderStructure L A instL _) τ τ') (atPhaseTwoF L B M p)) :
    ∃ (ρ' : B.Assignment A) (σ' : M.Assignment A), τ' = preAssign p ρ' σ' := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) τ τ'
  obtain ⟨hset, hrest⟩ := Formula.realize_inf.mp h
  rw [realize_listInf] at hrest
  have hbit : ∀ (r : Phase) (x : Fin ((preBlock B M).arity (Sum.inl r)) → A),
      τ' (Sum.inl r) x ↔ r = p := by
    intro r x
    rcases eq_or_ne r p with rfl | hne
    · exact ⟨fun _ => rfl, fun _ => (realize_phaseTwoF' r τ τ' x).mp hset⟩
    · refine ⟨fun hr => ?_, fun hr => absurd hr hne⟩
      have hne' := hrest _ (List.mem_map.mpr ⟨r, mem_finEnum r, rfl⟩)
      rw [if_neg hne, Formula.realize_not] at hne'
      exact absurd ((realize_phaseTwoF' r τ τ' x).mpr hr) hne'
  refine ⟨fun i => τ' (Sum.inr (Sum.inl i)), fun j => τ' (Sum.inr (Sum.inr j)), ?_⟩
  funext i
  match i with
  | Sum.inl r =>
    funext x
    exact propext (hbit r x)
  | Sum.inr (Sum.inl _) => rfl
  | Sum.inr (Sum.inr _) => rfl

/-! ### Freezing, read -/

theorem realize_frozenAtS (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A)
    (i : B.ι) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ'))
        (frozenAtS L B M i) ↔ ∀ x : Fin (B.arity i) → A, ρ i x ↔ ρ' i x) := by
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  rw [frozenAtS, Sentence.Realize, Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  simp only [Formula.realize_inf, Formula.realize_imp, Formula.realize_rel, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

open Classical in
theorem realize_frozenS (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : M.Assignment A) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ'))
        (frozenS L B M) ↔ ρ = ρ') := by
  classical
  letI := @SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  letI := Fintype.ofFinite B.ι
  rw [frozenS, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    exact propext ((realize_frozenAtS p q ρ ρ' σ σ' i).mp
      (h _ (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩)) x)
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_frozenAtS p q ρ ρ σ σ' i).mpr fun _ => Iff.rfl

/-! ### The prefixed game -/

theorem realize_sumInl_two (τ τ' : (preBlock B M).Assignment A)
    (ψ : ((L.sum Language.order).sum (preBlock B M).lang).Sentence) :
    (@Sentence.Realize _ A
        (@SOBlock.structure₂ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) τ τ') (LHom.sumInl.onSentence ψ) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
          (@sumOrderStructure L A instL _) τ) ψ) := by
  letI := @SOBlock.structure₁ (L.sum Language.order) (preBlock B M) A
    (@sumOrderStructure L A instL _) τ
  letI := (preBlock B M).structure τ'
  exact LHom.realize_onSentence (M := A) LHom.sumInl ψ

variable (L B)

open Classical in
/-- **A game, prefixed with one quantified block**: the block is chosen at the
phase `pick` by the player the polarity names, a starting state of the inner
game at the phase `start`, and the inner game is played from there with the
block frozen. -/
noncomputable def exBlock (pol : Bool) (spec : SOGameSpec (L.sum B.lang)) : SOGameSpec L where
  B := preBlock B spec.B
  move :=
    ((LHom.sumInl.onSentence (atPhaseF L B spec.B .pick) ⊓ atPhaseTwoF L B spec.B .start) ⊔
      ((LHom.sumInl.onSentence (atPhaseF L B spec.B .start) ⊓ atPhaseTwoF L B spec.B .play) ⊓
        (frozenS L B spec.B ⊓ (preSndLHom L B spec.B).onSentence spec.start))) ⊔
      ((LHom.sumInl.onSentence (atPhaseF L B spec.B .play) ⊓ atPhaseTwoF L B spec.B .play) ⊓
        (frozenS L B spec.B ⊓ (preTwoLHom L B spec.B).onSentence spec.move))
  univ := (atPhaseF L B spec.B .pick ⊓ (match pol with | true => ⊥ | false => ⊤)) ⊔
    (atPhaseF L B spec.B .play ⊓ (preOneLHom L B spec.B).onSentence spec.univ)
  won := atPhaseF L B spec.B .play ⊓ (preOneLHom L B spec.B).onSentence spec.won
  start := atPhaseF L B spec.B .pick

variable {L B} {pol : Bool} {spec : SOGameSpec (L.sum B.lang)}

theorem exBlock_isStart (p : Phase) (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).IsStart (preAssign p ρ σ) ↔ p = .pick) :=
  (realize_atPhaseF .pick p ρ σ).trans eq_comm

theorem exBlock_isWon (p : Phase) (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).IsWon (preAssign p ρ σ) ↔
      p = .play ∧ @SOGameSpec.IsWon (L.sum B.lang) spec A (B.structure₁ ρ) _ σ) := by
  letI : ((L.sum Language.order).sum (exBlock L B pol spec).B.lang).Structure A :=
    @SOBlock.structure₁ (L.sum Language.order) (preBlock B spec.B) A
      (@sumOrderStructure L A instL _) (preAssign p ρ σ)
  refine Iff.trans Formula.realize_inf (and_congr ?_ ?_)
  · exact (realize_atPhaseF .play p ρ σ).trans eq_comm
  · exact realize_preOne p ρ σ spec.won

theorem exBlock_isUniv (p : Phase) (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).IsUniv (preAssign p ρ σ) ↔
      (p = .pick ∧ pol = false) ∨
        (p = .play ∧ @SOGameSpec.IsUniv (L.sum B.lang) spec A (B.structure₁ ρ) _ σ)) := by
  letI : ((L.sum Language.order).sum (exBlock L B pol spec).B.lang).Structure A :=
    @SOBlock.structure₁ (L.sum Language.order) (preBlock B spec.B) A
      (@sumOrderStructure L A instL _) (preAssign p ρ σ)
  refine Iff.trans Formula.realize_sup (or_congr ?_ ?_)
  · refine Iff.trans Formula.realize_inf
      (and_congr ((realize_atPhaseF .pick p ρ σ).trans eq_comm) ?_)
    cases pol with
    | true => exact iff_of_false id (by simp)
    | false => exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  · exact Iff.trans Formula.realize_inf
      (and_congr ((realize_atPhaseF .play p ρ σ).trans eq_comm) (realize_preOne p ρ σ spec.univ))

theorem exBlock_move (p q : Phase) (ρ ρ' : B.Assignment A) (σ σ' : spec.State A) :
    ((exBlock L B pol spec).Move (preAssign p ρ σ) (preAssign q ρ' σ') ↔
      (p = .pick ∧ q = .start) ∨
        ((p = .start ∧ q = .play) ∧ ρ = ρ' ∧
            @SOGameSpec.IsStart (L.sum B.lang) spec A (B.structure₁ ρ') _ σ') ∨
          ((p = .play ∧ q = .play) ∧ ρ = ρ' ∧
            @SOGameSpec.Move (L.sum B.lang) spec A (B.structure₁ ρ) _ σ σ')) := by
  letI : (((L.sum Language.order).sum (exBlock L B pol spec).B.lang).sum
      (exBlock L B pol spec).B.lang).Structure A :=
    @SOBlock.structure₂ (L.sum Language.order) (preBlock B spec.B) A
      (@sumOrderStructure L A instL _) (preAssign p ρ σ) (preAssign q ρ' σ')
  refine Iff.trans Formula.realize_sup (Iff.trans (or_congr ?_ ?_) or_assoc)
  · refine Iff.trans Formula.realize_sup (or_congr ?_ ?_)
    · refine Iff.trans Formula.realize_inf (and_congr ?_ ?_)
      · exact Iff.trans (realize_sumInl_two _ _ (atPhaseF L B spec.B .pick))
          ((realize_atPhaseF .pick p ρ σ).trans eq_comm)
      · exact (realize_atPhaseTwoF .start q _ ρ' σ').trans eq_comm
    · refine Iff.trans Formula.realize_inf (and_congr (Iff.trans Formula.realize_inf ?_)
        (Iff.trans Formula.realize_inf (and_congr ?_ ?_)))
      · refine and_congr ?_ ?_
        · exact Iff.trans (realize_sumInl_two _ _ (atPhaseF L B spec.B .start))
            ((realize_atPhaseF .start p ρ σ).trans eq_comm)
        · exact (realize_atPhaseTwoF .play q _ ρ' σ').trans eq_comm
      · exact realize_frozenS p q ρ ρ' σ σ'
      · exact realize_preSnd p q ρ ρ' σ σ' spec.start
  · refine Iff.trans Formula.realize_inf (and_congr (Iff.trans Formula.realize_inf ?_)
      (Iff.trans Formula.realize_inf (and_congr ?_ ?_)))
    · refine and_congr ?_ ?_
      · exact Iff.trans (realize_sumInl_two _ _ (atPhaseF L B spec.B .play))
          ((realize_atPhaseF .play p ρ σ).trans eq_comm)
      · exact (realize_atPhaseTwoF .play q _ ρ' σ').trans eq_comm
    · exact realize_frozenS p q ρ ρ' σ σ'
    · exact realize_preTwo p q ρ ρ' σ σ' spec.move

/-- **Every move lands on a well-formed state**: each disjunct guards the tag
bits of the state it enters. -/
theorem exBlock_move_shape {τ τ' : (preBlock B spec.B).Assignment A}
    (h : (exBlock L B pol spec).Move τ τ') :
    ∃ (q : Phase) (ρ' : B.Assignment A) (σ' : spec.State A), τ' = preAssign q ρ' σ' := by
  letI : (((L.sum Language.order).sum (exBlock L B pol spec).B.lang).sum
      (exBlock L B pol spec).B.lang).Structure A :=
    @SOBlock.structure₂ (L.sum Language.order) (preBlock B spec.B) A
      (@sumOrderStructure L A instL _) τ τ'
  rcases Formula.realize_sup.mp h with h | h
  · rcases Formula.realize_sup.mp h with h | h
    · obtain ⟨ρ', σ', hτ'⟩ := exists_preAssign_two .start τ τ' (Formula.realize_inf.mp h).2
      exact ⟨.start, ρ', σ', hτ'⟩
    · obtain ⟨ρ', σ', hτ'⟩ :=
        exists_preAssign_two .play τ τ' (Formula.realize_inf.mp (Formula.realize_inf.mp h).1).2
      exact ⟨.play, ρ', σ', hτ'⟩
  · obtain ⟨ρ', σ', hτ'⟩ :=
      exists_preAssign_two .play τ τ' (Formula.realize_inf.mp (Formula.realize_inf.mp h).1).2
    exact ⟨.play, ρ', σ', hτ'⟩

/-! ### What the prefixed game wins -/

/-- **The playing phase plays the inner game**, from a win of the prefixed game
back to one of the inner one. -/
theorem inner_wins_of_wins {τ : (exBlock L B pol spec).State A}
    (h : (exBlock L B pol spec).Wins τ) {ρ : B.Assignment A} {σ : spec.State A}
    (hτ : τ = preAssign .play ρ σ) :
    @SOGameSpec.Wins (L.sum B.lang) spec A (B.structure₁ ρ) _ σ := by
  induction h generalizing ρ σ with
  | @won τ hw =>
    letI := B.structure₁ (L := L) ρ
    rw [hτ] at hw
    exact .won ((exBlock_isWon .play ρ σ).mp hw).2
  | @ex τ τ' hnu hmove hwin ih =>
    letI := B.structure₁ (L := L) ρ
    rw [hτ] at hnu hmove
    obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
    rw [hτ'] at hmove
    rcases (exBlock_move .play q ρ ρ' σ σ').mp hmove with ⟨h1, -⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨⟨-, hq⟩, hρ, hm⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · refine .ex (fun hu => hnu ((exBlock_isUniv .play ρ σ).mpr (Or.inr ⟨rfl, hu⟩))) hm ?_
      refine ih ?_
      rw [hτ', hq, hρ]
  | @all τ hu hex hall ih =>
    letI := B.structure₁ (L := L) ρ
    rw [hτ] at hu hex hall ih
    have huniv : @SOGameSpec.IsUniv (L.sum B.lang) spec A (B.structure₁ ρ) _ σ := by
      rcases (exBlock_isUniv .play ρ σ).mp hu with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (by simp)
      · exact h2
    refine .all huniv ?_ ?_
    · obtain ⟨τ', hmove⟩ := hex
      obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
      rw [hτ'] at hmove
      rcases (exBlock_move .play q ρ ρ' σ σ').mp hmove with ⟨h1, -⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨-, -, hm⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact ⟨σ', hm⟩
    · intro σ' hm
      refine ih (preAssign .play ρ σ') ?_ rfl
      exact (exBlock_move .play .play ρ ρ σ σ').mpr (Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl, hm⟩))

/-- **The playing phase plays the inner game**, from a win of the inner game to
one of the prefixed game. -/
theorem wins_play_of_inner (ρ : B.Assignment A) {σ : spec.State A}
    (h : @SOGameSpec.Wins (L.sum B.lang) spec A (B.structure₁ ρ) _ σ) :
    (exBlock L B pol spec).Wins (preAssign .play ρ σ) := by
  induction h with
  | @won σ hw => exact .won ((exBlock_isWon .play ρ σ).mpr ⟨rfl, hw⟩)
  | @ex σ σ' hnu hm hwin ih =>
    refine .ex (fun hu => ?_) ?_ ih
    · rcases (exBlock_isUniv .play ρ σ).mp hu with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (by simp)
      · exact hnu h2
    · exact (exBlock_move .play .play ρ ρ σ σ').mpr (Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl, hm⟩))
  | @all σ hu hex hall ih =>
    refine .all ((exBlock_isUniv .play ρ σ).mpr (Or.inr ⟨rfl, hu⟩)) ?_ ?_
    · obtain ⟨σ', hm⟩ := hex
      exact ⟨preAssign .play ρ σ',
        (exBlock_move .play .play ρ ρ σ σ').mpr (Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl, hm⟩))⟩
    · intro τ' hmove
      obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
      rw [hτ'] at hmove ⊢
      rcases (exBlock_move .play q ρ ρ' σ σ').mp hmove with
        ⟨h1, -⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨⟨-, hq⟩, hρ, hm⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · rw [hq, ← hρ]
        exact ih σ' hm

theorem wins_play_iff (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).Wins (preAssign .play ρ σ) ↔
      @SOGameSpec.Wins (L.sum B.lang) spec A (B.structure₁ ρ) _ σ) :=
  ⟨fun h => inner_wins_of_wins h rfl, fun h => wins_play_of_inner ρ h⟩

/-- **The starting phase chooses a starting state of the inner game**: it is
existential, and it is stuck exactly when the inner game has no starting
state. -/
theorem accepts_of_wins_start {τ : (exBlock L B pol spec).State A}
    (h : (exBlock L B pol spec).Wins τ) {ρ : B.Assignment A} {σ : spec.State A}
    (hτ : τ = preAssign .start ρ σ) :
    @SOGameSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ) _ := by
  letI := B.structure₁ (L := L) ρ
  cases h with
  | @won τ hw =>
    rw [hτ] at hw
    exact absurd ((exBlock_isWon .start ρ σ).mp hw).1 (by simp)
  | @ex τ τ' hnu hmove hwin =>
    rw [hτ] at hmove
    obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
    rw [hτ'] at hmove hwin
    rcases (exBlock_move .start q ρ ρ' σ σ').mp hmove with
      ⟨h1, -⟩ | ⟨⟨-, hq⟩, hρ, hst⟩ | ⟨⟨h1, -⟩, -⟩
    · exact absurd h1 (by simp)
    · refine ⟨σ', hρ ▸ hst, ?_⟩
      rw [hq] at hwin
      exact hρ ▸ (wins_play_iff ρ' σ').mp hwin
    · exact absurd h1 (by simp)
  | @all τ hu hex hall =>
    rw [hτ] at hu
    rcases (exBlock_isUniv .start ρ σ).mp hu with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by simp)

theorem wins_start_iff (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).Wins (preAssign .start ρ σ) ↔
      @SOGameSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ) _) := by
  letI := B.structure₁ (L := L) ρ
  refine ⟨fun h => accepts_of_wins_start h rfl, ?_⟩
  rintro ⟨σ', hstart, hwins⟩
  refine .ex (fun hu => ?_) ?_ ((wins_play_iff ρ σ').mpr hwins)
  · rcases (exBlock_isUniv .start ρ σ).mp hu with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by simp)
  · exact (exBlock_move .start .play ρ ρ σ σ').mpr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, hstart⟩))

/-- **The picking phase quantifies the block**, existentially or universally as
the polarity says. -/
theorem quantB_accepts_of_wins_pick {τ : (exBlock L B pol spec).State A}
    (h : (exBlock L B pol spec).Wins τ) {ρ : B.Assignment A} {σ : spec.State A}
    (hτ : τ = preAssign .pick ρ σ) :
    quantB pol fun ρ₀ : B.Assignment A =>
      @SOGameSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ₀) _ := by
  cases h with
  | @won τ hw =>
    rw [hτ] at hw
    exact absurd ((exBlock_isWon .pick ρ σ).mp hw).1 (by simp)
  | @ex τ τ' hnu hmove hwin =>
    rw [hτ] at hnu hmove
    cases pol with
    | false => exact absurd ((exBlock_isUniv .pick ρ σ).mpr (Or.inl ⟨rfl, rfl⟩)) hnu
    | true =>
      obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
      rw [hτ'] at hmove hwin
      rcases (exBlock_move .pick q ρ ρ' σ σ').mp hmove with
        ⟨-, hq⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨⟨h1, -⟩, -⟩
      · rw [hq] at hwin
        exact ⟨ρ', accepts_of_wins_start hwin rfl⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
  | @all τ hu hex hall =>
    rw [hτ] at hu hall
    cases pol with
    | true =>
      rcases (exBlock_isUniv .pick ρ σ).mp hu with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
    | false =>
      intro ρ₀
      refine accepts_of_wins_start (hall (preAssign .start ρ₀ σ) ?_) rfl
      exact (exBlock_move .pick .start ρ ρ₀ σ σ).mpr (Or.inl ⟨rfl, rfl⟩)

theorem wins_pick_iff (ρ : B.Assignment A) (σ : spec.State A) :
    ((exBlock L B pol spec).Wins (preAssign .pick ρ σ) ↔
      quantB pol fun ρ₀ : B.Assignment A =>
        @SOGameSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ₀) _) := by
  refine ⟨fun h => quantB_accepts_of_wins_pick h rfl, ?_⟩
  cases pol with
  | true =>
    rintro ⟨ρ₀, hacc⟩
    refine .ex (fun hu => ?_) ?_ ((wins_start_iff ρ₀ σ).mpr hacc)
    · rcases (exBlock_isUniv .pick ρ σ).mp hu with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
    · exact (exBlock_move .pick .start ρ ρ₀ σ σ).mpr (Or.inl ⟨rfl, rfl⟩)
  | false =>
    intro hall
    refine .all ((exBlock_isUniv .pick ρ σ).mpr (Or.inl ⟨rfl, rfl⟩))
      ⟨preAssign .start ρ σ, (exBlock_move .pick .start ρ ρ σ σ).mpr (Or.inl ⟨rfl, rfl⟩)⟩ ?_
    intro τ' hmove
    obtain ⟨q, ρ', σ', hτ'⟩ := exBlock_move_shape hmove
    rw [hτ'] at hmove ⊢
    rcases (exBlock_move .pick q ρ ρ' σ σ').mp hmove with
      ⟨-, hq⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨⟨h1, -⟩, -⟩
    · rw [hq]
      exact (wins_start_iff ρ' σ').mpr (hall ρ')
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)

/-- **What a prefixed game accepts**: what the inner game accepts, under the
quantified block. -/
theorem exBlock_accepts_iff :
    ((exBlock L B pol spec).Accepts A ↔
      quantB pol fun ρ₀ : B.Assignment A =>
        @SOGameSpec.Accepts (L.sum B.lang) spec A (B.structure₁ ρ₀) _) := by
  constructor
  · rintro ⟨τ, hstart, hwins⟩
    letI : ((L.sum Language.order).sum (exBlock L B pol spec).B.lang).Structure A :=
      @SOBlock.structure₁ (L.sum Language.order) (preBlock B spec.B) A
        (@sumOrderStructure L A instL _) τ
    obtain ⟨p, ρ, σ, hτ⟩ := exists_preAssign τ (Formula.realize_inf.mp hstart).1
    rw [hτ] at hstart hwins
    rw [(exBlock_isStart p ρ σ).mp hstart] at hwins
    exact quantB_accepts_of_wins_pick hwins rfl
  · intro h
    refine ⟨preAssign .pick (fun _ _ => False) fun _ _ => False, ?_, ?_⟩
    · exact (exBlock_isStart _ _ _).mpr rfl
    · exact (wins_pick_iff _ _).mpr h

/-! ### The kernel, as a game with no move -/

variable (L)

/-- The game that decides a first-order sentence: no move, and the sentence
decides the only position. -/
noncomputable def kernelGame (φ : L.Sentence) : SOGameSpec L where
  B := SOBlock.trivial
  move := ⊥
  univ := ⊥
  won := (LHom.sumInl : (L.sum Language.order) →ᴸ
      ((L.sum Language.order).sum SOBlock.trivial.lang)).onSentence
    ((LHom.sumInl : L →ᴸ L.sum Language.order).onSentence φ)
  start := ⊤

variable {L}

theorem realize_kernel_won (φ : L.Sentence) (τ : SOBlock.trivial.Assignment A) :
    ((kernelGame L φ).IsWon τ ↔ @Sentence.Realize L A instL φ) := by
  letI := SOBlock.trivial.structure τ
  letI : ((L.sum Language.order).sum (kernelGame L φ).B.lang).Structure A :=
    @SOBlock.structure₁ (L.sum Language.order) SOBlock.trivial A
      (@sumOrderStructure L A instL _) τ
  refine Iff.trans (LHom.realize_onSentence (M := A) LHom.sumInl _) ?_
  exact LHom.realize_onSentence (M := A) LHom.sumInl φ

theorem wins_kernel_iff (φ : L.Sentence) (τ : (kernelGame L φ).State A) :
    ((kernelGame L φ).Wins τ ↔ @Sentence.Realize L A instL φ) := by
  letI : ((L.sum Language.order).sum (kernelGame L φ).B.lang).Structure A :=
    @SOBlock.structure₁ (L.sum Language.order) SOBlock.trivial A
      (@sumOrderStructure L A instL _) τ
  refine ⟨fun h => ?_, fun h => .won ((realize_kernel_won φ τ).mpr h)⟩
  cases h with
  | @won τ hw => exact (realize_kernel_won φ τ).mp hw
  | @ex τ τ' hnu hmove hwin => exact hmove.elim
  | @all τ hu hex hall => exact hu.elim

theorem accepts_kernelGame (φ : L.Sentence) :
    ((kernelGame L φ).Accepts A ↔ @Sentence.Realize L A instL φ) := by
  constructor
  · rintro ⟨τ, -, hwins⟩
    exact (wins_kernel_iff φ τ).mp hwins
  · intro h
    letI : ((L.sum Language.order).sum (kernelGame L φ).B.lang).Structure A :=
      @SOBlock.structure₁ (L.sum Language.order) SOBlock.trivial A
        (@sumOrderStructure L A instL _) fun _ _ => False
    refine ⟨fun _ _ => False, ?_, (wins_kernel_iff φ _).mpr h⟩
    exact Formula.realize_top.mpr trivial

/-! ### The prefix, peeled one block at a time -/

/-- **The game a second-order sentence defines**: one quantified block per
block of the prefix, and the kernel at the end. -/
noncomputable def gameOfSO :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}), (soLang L Bs).Sentence → Bool → SOGameSpec L
  | [], _, φ, _ => kernelGame _ φ
  | B :: Bs, L, φ, pol => exBlock L B pol (gameOfSO Bs (L.sum B.lang) φ (!pol))

/-- **A second-order sentence is a second-order alternating game.** -/
theorem accepts_gameOfSO :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A) [LinearOrder A]
      (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SOGameSpec.Accepts L (gameOfSO Bs L φ pol) A instL _ ↔ @SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL _ φ pol
    exact accepts_kernelGame (L := L) (instL := instL) φ
  | cons B Bs ih =>
    intro L A instL _ φ pol
    refine Iff.trans (exBlock_accepts_iff (L := L) (B := B) (pol := pol)) ?_
    cases pol with
    | true =>
      exact exists_congr fun ρ =>
        ih (L.sum B.lang) A (@SOBlock.structure₁ L B A instL ρ) φ false
    | false =>
      exact forall_congr' fun ρ =>
        ih (L.sum B.lang) A (@SOBlock.structure₁ L B A instL ρ) φ true

end SOGameSpec

/-! ### `SO ⊆ SO-GAME` -/

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

/-- **Every `Σₖ`-definable problem is a second-order alternating game.** -/
theorem SigmaSODefinable.soGameDefinable {k : ℕ} (h : SigmaSODefinable k P) :
    SOGameDefinable P := by
  obtain ⟨Bs, -, φ, hφ⟩ := h
  refine ⟨SOGameSpec.gameOfSO Bs L φ true, fun A _ _ _ _ => ?_⟩
  exact (hφ A).trans (SOGameSpec.accepts_gameOfSO Bs L A ‹L.Structure A› φ true).symm

/-- **Every `Πₖ`-definable problem is a second-order alternating game.** -/
theorem PiSODefinable.soGameDefinable {k : ℕ} (h : PiSODefinable k P) :
    SOGameDefinable P := by
  obtain ⟨Bs, -, φ, hφ⟩ := h
  refine ⟨SOGameSpec.gameOfSO Bs L φ false, fun A _ _ _ _ => ?_⟩
  exact (hφ A).trans (SOGameSpec.accepts_gameOfSO Bs L A ‹L.Structure A› φ false).symm

/-- **Every level of the polynomial hierarchy is a second-order alternating
game.** Level 0 goes through `PTIME ⊆ NP`, the other levels are the definition
of `DescriptiveComplexity.SigmaP` read through
`DescriptiveComplexity.SigmaSODefinable.soGameDefinable`. -/
theorem SOGameDefinable.of_mem_sigmaP {k : ℕ} (h : P ∈ SigmaP k) : SOGameDefinable P := by
  cases k with
  | zero => exact SigmaSODefinable.soGameDefinable (k := 1) (PTIME_subset_NP h)
  | succ k => exact SigmaSODefinable.soGameDefinable (k := k + 1) h

/-- **`PH ⊆ SO-GAME`**: every problem of the polynomial hierarchy is the value
of a second-order alternating game. Read with
`DescriptiveComplexity.SOGameDefinable.mem_EXPTIME` it re-proves `PH ⊆ EXPTIME`,
this time through a game rather than through `PSPACE`. -/
theorem SOGameDefinable.of_mem_PH (h : P ∈ PH) : SOGameDefinable P := by
  obtain ⟨k, hk⟩ := h
  exact SOGameDefinable.of_mem_sigmaP hk

/-! ### A first-order property of an expansion -/

namespace ExpExpansion

variable (X : ExpExpansion L) (φ : (X.E.sum Language.order).Sentence) (Q : DecisionProblem L)

/-- **A first-order property of an exponential expansion is a second-order
alternating game**: its quantifiers become second-order blocks over the base
(`DescriptiveComplexity.ExpExpansion.exists_translate`) and the blocks become
moves. This is the game reading of
`DescriptiveComplexity.ExpExpansion.mem_PH_of_fo_on_expansion`, and it is what a
guard of a fixed-point rule over an expansion will be evaluated by. -/
theorem soGameDefinable_of_fo_on_expansion
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      letI := X.mapLinearOrder A
      (Q A ↔ @Sentence.Realize _ (X.Map A) _ φ)) :
    SOGameDefinable Q :=
  SOGameDefinable.of_mem_PH (mem_PH_of_fo_on_expansion X φ Q h)

end ExpExpansion

end DescriptiveComplexity
