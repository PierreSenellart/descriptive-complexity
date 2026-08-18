/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Matrix
import DescriptiveComplexity.Exponential.Increment
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.HeadAutomaton
import DescriptiveComplexity.PSpace

/-!
# Simulating a machine that walks an expanded universe

What every exponential class rests on: a walk over an *expanded* universe,
performed by a machine that only ever holds finitely many points of it, is a
walk over the base – an `DescriptiveComplexity.SOTCSpec`, since a point of the
expansion is an assignment of a block and `k` of them are an assignment of one
merged block. This file builds that specification out of a
`DescriptiveComplexity.HeadAutomaton` and proves the two walks step for step
equivalent.

Why an automaton rather than an FO(TC) specification: the tests a
`DescriptiveComplexity.HeadAutomaton` performs are **quantifier-free by fiat**
(`DescriptiveComplexity.HeadAutomaton.test_qf`), so
`DescriptiveComplexity.ExpExpansion.translQF` translates them as they stand and
no quantifier over the expanded universe is ever evaluated. Everything else the
machine does is an order primitive – stay, copy, jump to an end, step to a
neighbor – and those are written down in
`DescriptiveComplexity.Exponential.Increment`.

## The one hypothesis

A move to the *immediate successor* is the increment of the assignment only
when every tagged assignment is a point, i.e., when the expansion's domain
sentence is trivial. That is the hypothesis `htot` the correctness theorems
carry; `DescriptiveComplexity.ExpExpansion.trivialize` is how a general
expansion is brought into that shape, and
`DescriptiveComplexity.ExpExpansion.trivialize_domHolds` is the hypothesis
discharged.

## Slots

Everything the transition sentence says is about *one* or *two* points, sitting
somewhere inside a bigger block: one of the `k` rounds of the current state, or
one of the `k` rounds of the next one. A `DescriptiveComplexity.ExpExpansion.PtSlot`
is that placement – an arity-preserving map of the point block into a host
block – and each of the five things the machine can ask about points is written
once, at an arbitrary slot of an arbitrary host:

* `DescriptiveComplexity.ExpExpansion.slotTagF` – the point at a slot carries a
  given tag;
* `DescriptiveComplexity.ExpExpansion.slotGuardF` – a slot holds a point at all;
* `DescriptiveComplexity.ExpExpansion.eqPtF`,
  `DescriptiveComplexity.ExpExpansion.covPtF`,
  `DescriptiveComplexity.ExpExpansion.minPtF`,
  `DescriptiveComplexity.ExpExpansion.maxPtF` – equality, the covering relation
  and the two endpoints.

The state block is then `(repMerged X.pointBlock k).withTag M.State`, the two
copies of it that a transition sentence sees are `SOBlock.replicate 2`, and both
hosts are addressed by the same slot machinery.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Every merged assignment is one assignment per round -/

/-- **A merged assignment splits into its rounds**: the assembly map of
`DescriptiveComplexity.repBlockAssign` is onto, so a guessed state of the walk
below really is `k` guessed points. -/
theorem repBlockAssign_surjective (B : SOBlock) (A : Type) :
    ∀ k : ℕ, Function.Surjective (repBlockAssign B A k)
  | 0 => fun μ => ⟨Fin.elim0, funext fun i => Empty.elim i⟩
  | k + 1 => fun μ => by
    obtain ⟨ρs, hρs⟩ := repBlockAssign_surjective B A k fun j => μ (Sum.inr j)
    refine ⟨Fin.cons (fun i => μ (Sum.inl i)) ρs, ?_⟩
    have hcons : repBlockAssign B A (k + 1) (Fin.cons (fun i => μ (Sum.inl i)) ρs) =
        consAssign (fun i => μ (Sum.inl i)) (repBlockAssign B A k ρs) := rfl
    rw [hcons, hρs]
    exact consAssign_split μ

namespace ExpExpansion

variable {L : Language.{0, 0}}

/-! ### Slots -/

/-- A **slot**: where one point of an expanded universe sits inside a host
block. Both hosts the simulation uses – the state block and two copies of it –
are addressed through this one interface. -/
structure PtSlot (X : ExpExpansion L) (H : SOBlock) where
  /-- The relation variable of the host carrying each variable of the point
  block. -/
  ix : X.pointBlock.ι → H.ι
  /-- The placement preserves arities. -/
  arity : ∀ x, H.arity (ix x) = X.pointBlock.arity x

namespace PtSlot

variable {X : ExpExpansion L} {H : SOBlock} (s : PtSlot X H)

/-- The vocabulary map reading a sentence about one point at the slot. -/
def lhom : ((L.sum Language.order).sum X.pointBlock.lang) →ᴸ
    ((L.sum Language.order).sum H.lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order)) (SOBlock.homLHom s.ix s.arity)

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The assignment of the point block a slot reads out of a host assignment. -/
def read (σ : H.Assignment A) : X.pointBlock.Assignment A :=
  SOBlock.homAssign s.ix s.arity σ

/-- **Reading a sentence at a slot is reading it at the slot's assignment.** -/
theorem realize_lhom (σ : H.Assignment A)
    (φ : ((L.sum Language.order).sum X.pointBlock.lang).Sentence) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
        (s.lhom.onSentence φ) ↔
      @Sentence.Realize _ A
        (X.pointBlock.structure₁ (L := L.sum Language.order) (s.read σ)) φ) :=
  SOBlock.realize_homSentence s.ix s.arity σ φ

/-- The slot of `σ` holds the point `p`. -/
def At (σ : H.Assignment A) (p : X.Point A) : Prop :=
  s.read σ = SOBlock.tagAssign p.1 p.2

end PtSlot

section Slots

variable {X : ExpExpansion L} {H : SOBlock}

/-! ### What a slot can be asked -/

/-- The atom “the point at this slot carries the tag `t`”. -/
noncomputable def slotTagF (s : PtSlot X H) (t : X.Tag) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  s.lhom.onSentence (SOBlock.tagBitF X.B X.Tag t)

/-- The guard “this slot holds a point of the expanded universe”. -/
noncomputable def slotGuardF (s : PtSlot X H) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  s.lhom.onSentence X.pointGuardF

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_slotTagF {s : PtSlot X H} {σ : H.Assignment A} {p : X.Point A}
    (hs : s.At σ p) (t : X.Tag) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (slotTagF s t) ↔
      t = p.1) := by
  refine (s.realize_lhom σ _).trans ?_
  refine (SOBlock.realize_tagBitF (L := L.sum Language.order) (s.read σ) t).trans ?_
  rw [hs]
  exact Iff.rfl

theorem realize_slotGuardF (s : PtSlot X H) (σ : H.Assignment A) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (slotGuardF s) ↔
      ∃ p : X.Map A, s.At σ p.1) := by
  refine (s.realize_lhom σ _).trans ?_
  refine (realize_pointGuardF (X := X) (s.read σ)).trans ?_
  constructor
  · rintro ⟨t, ρ, heq, hdom⟩
    exact ⟨⟨(t, ρ), hdom⟩, heq⟩
  · rintro ⟨⟨⟨t, ρ⟩, hdom⟩, heq⟩
    exact ⟨t, ρ, heq, hdom⟩

/-! ### Two slots at once -/

/-- Two slots, read as a placement of the expansion's block replicated twice:
copy `0` is the first slot, copy `1` the second. -/
def pairIx (s₀ s₁ : PtSlot X H) : (X.B.replicate 2).ι → H.ι :=
  fun p => (![s₀, s₁] p.1).ix (Sum.inr p.2)

theorem pairIx_arity (s₀ s₁ : PtSlot X H) :
    ∀ p, H.arity (pairIx s₀ s₁ p) = (X.B.replicate 2).arity p :=
  fun p => (![s₀, s₁] p.1).arity (Sum.inr p.2)

/-- The vocabulary map reading a sentence about two assignments of the
expansion's block at two slots. -/
def pairLHom (s₀ s₁ : PtSlot X H) :
    ((L.sum Language.order).sum (X.B.replicate 2).lang) →ᴸ
      ((L.sum Language.order).sum H.lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (pairIx s₀ s₁) (pairIx_arity s₀ s₁))

/-- **Reading a two-copy sentence at two slots** is reading it at the two
assignments those slots hold. -/
theorem realize_pairLHom {s₀ s₁ : PtSlot X H} {σ : H.Assignment A} {p₀ p₁ : X.Point A}
    (h₀ : s₀.At σ p₀) (h₁ : s₁.At σ p₁)
    (φ : ((L.sum Language.order).sum (X.B.replicate 2).lang).Sentence) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
        ((pairLHom s₀ s₁).onSentence φ) ↔
      @Sentence.Realize _ A
        ((X.B.replicate 2).structure₁ (L := L.sum Language.order)
          (X.B.replicateAssign ![p₀.2, p₁.2])) φ) := by
  have hass : SOBlock.homAssign (pairIx s₀ s₁) (pairIx_arity s₀ s₁) σ =
      X.B.replicateAssign ![p₀.2, p₁.2] := by
    funext q u
    obtain ⟨c, y⟩ := q
    rcases c with ⟨_ | _ | c, hc⟩
    · exact congrFun (congrFun h₀ (Sum.inr y)) u
    · exact congrFun (congrFun h₁ (Sum.inr y)) u
    · omega
  have h := SOBlock.realize_homSentence (pairIx s₀ s₁) (pairIx_arity s₀ s₁) σ φ
  rwa [hass] at h

/-! ### The static half: facts about tags

A point is a tag and an assignment, and the tag half of every order question is
decided at formula-construction time: there are finitely many tags, so which
one is least, which is greatest and which covers which are *conditions on the
disjunct*, not conditions the sentence has to express. -/

variable (X) in
/-- The tag is the least one. -/
def IsMinTag (t : X.Tag) : Prop :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  ∀ t' : X.Tag, t ≤ t'

variable (X) in
/-- The tag is the greatest one. -/
def IsMaxTag (t : X.Tag) : Prop :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  ∀ t' : X.Tag, t' ≤ t

variable (X) in
/-- The second tag is the immediate successor of the first. -/
def TagCovBy (t₁ t₂ : X.Tag) : Prop :=
  letI : LinearOrder X.Tag := finiteLinearOrder X.Tag
  t₁ < t₂ ∧ ∀ t : X.Tag, ¬(t₁ < t ∧ t < t₂)

/-! ### The four questions a machine asks about points -/

/-- “The two slots hold the same point”: their tag bits agree, and their
assignments hold of the same atoms. -/
noncomputable def eqPtF (s₀ s₁ : PtSlot X H) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  listInf ((finEnum X.Tag).map fun t => slotTagF s₀ t ⇔ slotTagF s₁ t) ⊓
    (pairLHom s₀ s₁).onSentence (X.B.eqAssignF (L := L))

open Classical in
/-- “The point of the second slot is the immediate successor of the point of
the first”: one disjunct per pair of tags, the tag comparison decided
statically and the assignment half being either the binary increment or the
roll-over from the full assignment to the empty one. -/
noncomputable def covPtF (s₀ s₁ : PtSlot X H) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  listSup ((finEnum (X.Tag × X.Tag)).map fun q =>
    (slotTagF s₀ q.1 ⊓ slotTagF s₁ q.2) ⊓
      (if q.1 = q.2 then (pairLHom s₀ s₁).onSentence (X.B.succAssignF L)
        else if TagCovBy X q.1 q.2 then
          (pairLHom s₀ s₁).onSentence (X.B.topAssignF L 0 ⊓ X.B.botAssignF L 1)
        else ⊥))

open Classical in
/-- “The point of this slot is the least point”: the least tag, holding of
nothing. -/
noncomputable def minPtF (s : PtSlot X H) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  listSup ((finEnum X.Tag).map fun t => if IsMinTag X t then slotTagF s t else ⊥) ⊓
    (pairLHom s s).onSentence (X.B.botAssignF L 0)

open Classical in
/-- “The point of this slot is the greatest point”: the greatest tag, holding
of everything. -/
noncomputable def maxPtF (s : PtSlot X H) :
    ((L.sum Language.order).sum H.lang).Sentence :=
  listSup ((finEnum X.Tag).map fun t => if IsMaxTag X t then slotTagF s t else ⊥) ⊓
    (pairLHom s s).onSentence (X.B.topAssignF L 0)

/-! ### Their correctness -/

variable [Finite A] [Nonempty A]

omit [Finite A] in
theorem realize_eqPtF {s₀ s₁ : PtSlot X H} {σ : H.Assignment A} {p₀ p₁ : X.Point A}
    (h₀ : s₀.At σ p₀) (h₁ : s₁.At σ p₁) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (eqPtF s₀ s₁) ↔
      p₀ = p₁) := by
  let := H.structure₁ (L := L.sum Language.order) σ
  have hass : (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
      ((pairLHom s₀ s₁).onSentence (X.B.eqAssignF (L := L))) ↔ p₀.2 = p₁.2) := by
    refine (realize_pairLHom h₀ h₁ _).trans ?_
    refine (X.B.realize_eqAssignF ![p₀.2, p₁.2]).trans ?_
    exact ⟨fun h => X.B.atomSet_injective h, fun h => congrArg _ h⟩
  rw [eqPtF, Sentence.Realize, Formula.realize_inf, realize_listInf]
  constructor
  · rintro ⟨htag, hassign⟩
    refine Prod.ext ?_ (hass.mp hassign)
    have h := htag _ (List.mem_map.mpr ⟨p₀.1, mem_finEnum _, rfl⟩)
    rw [Formula.realize_iff] at h
    exact (realize_slotTagF h₁ p₀.1).mp (h.mp ((realize_slotTagF h₀ p₀.1).mpr rfl))
  · intro h
    refine ⟨fun ψ hψ => ?_, hass.mpr (congrArg (fun x => x.2) h)⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iff]
    exact (realize_slotTagF h₀ t).trans
      ((by rw [h] : (t = p₀.1) ↔ (t = p₁.1)).trans (realize_slotTagF h₁ t).symm)

theorem realize_covPtF {s₀ s₁ : PtSlot X H} {σ : H.Assignment A} {p₀ p₁ : X.Point A}
    (h₀ : s₀.At σ p₀) (h₁ : s₁.At σ p₁) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (covPtF s₀ s₁) ↔
      ((X.pointLinearOrder A).lt p₀ p₁ ∧
        ∀ r : X.Point A,
          ¬((X.pointLinearOrder A).lt p₀ r ∧ (X.pointLinearOrder A).lt r p₁))) := by
  classical
  let := H.structure₁ (L := L.sum Language.order) σ
  let : LinearOrder X.Tag := finiteLinearOrder X.Tag
  let := X.B.realIxLinearOrder A
  have hsucc : (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
      ((pairLHom s₀ s₁).onSentence (X.B.succAssignF L)) ↔
        SetSucc (X.B.realSet p₀.2) (X.B.realSet p₁.2)) :=
    (realize_pairLHom h₀ h₁ _).trans (X.B.realize_succAssignF ![p₀.2, p₁.2])
  have htb : (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
      ((pairLHom s₀ s₁).onSentence (X.B.topAssignF L 0 ⊓ X.B.botAssignF L 1)) ↔
        (X.B.atomSet p₀.2 = fun _ => True) ∧ (X.B.atomSet p₁.2 = fun _ => False)) := by
    let := (X.B.replicate 2).structure₁ (L := L.sum Language.order)
      (X.B.replicateAssign ![p₀.2, p₁.2])
    refine (realize_pairLHom h₀ h₁ _).trans (Iff.trans Formula.realize_inf ?_)
    exact and_congr (X.B.realize_topAssignF ![p₀.2, p₁.2] 0)
      (X.B.realize_botAssignF ![p₀.2, p₁.2] 1)
  refine Iff.trans ?_ (X.pointCovBy_iff A p₀ p₁).symm
  rw [covPtF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨⟨t₁, t₂⟩, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_inf, Formula.realize_inf] at hr
    obtain ⟨⟨hb₀, hb₁⟩, hbody⟩ := hr
    have e₀ : t₁ = p₀.1 := (realize_slotTagF h₀ t₁).mp hb₀
    have e₁ : t₂ = p₁.1 := (realize_slotTagF h₁ t₂).mp hb₁
    subst e₀
    subst e₁
    by_cases heq : p₀.1 = p₁.1
    · rw [if_pos heq] at hbody
      exact Or.inl ⟨heq, hsucc.mp hbody⟩
    · rw [if_neg heq] at hbody
      by_cases hcov : TagCovBy X p₀.1 p₁.1
      · rw [if_pos hcov] at hbody
        exact Or.inr ⟨hcov.1, hcov.2, (htb.mp hbody).1, (htb.mp hbody).2⟩
      · rw [if_neg hcov, Formula.realize_bot] at hbody
        exact hbody.elim
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨(p₀.1, p₁.1), mem_finEnum _, rfl⟩, ?_⟩
    dsimp only
    rw [Formula.realize_inf, Formula.realize_inf]
    refine ⟨⟨(realize_slotTagF h₀ _).mpr rfl, (realize_slotTagF h₁ _).mpr rfl⟩, ?_⟩
    rcases h with ⟨heq, hsc⟩ | ⟨hlt, hnb, htop, hbot⟩
    · rw [if_pos heq]
      exact hsucc.mpr hsc
    · have hcov : TagCovBy X p₀.1 p₁.1 := ⟨hlt, hnb⟩
      rw [if_neg (ne_of_lt hlt), if_pos hcov]
      exact htb.mpr ⟨htop, hbot⟩

theorem realize_minPtF {s : PtSlot X H} {σ : H.Assignment A} {p : X.Point A}
    (hs : s.At σ p) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (minPtF s) ↔
      ∀ q : X.Point A, (X.pointLinearOrder A).le p q) := by
  classical
  let := H.structure₁ (L := L.sum Language.order) σ
  have hbot : (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
      ((pairLHom s s).onSentence (X.B.botAssignF L 0)) ↔
        X.B.atomSet p.2 = fun _ => False) :=
    (realize_pairLHom hs hs _).trans (X.B.realize_botAssignF ![p.2, p.2] 0)
  refine Iff.trans ?_ (X.pointIsBot_iff A p).symm
  rw [minPtF, Sentence.Realize, Formula.realize_inf, realize_listSup]
  refine and_congr ?_ hbot
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hψ
    by_cases ht : IsMinTag X t
    · rw [if_pos ht] at hr
      have het : t = p.1 := (realize_slotTagF hs t).mp hr
      rw [← het]
      exact ht
    · rw [if_neg ht, Formula.realize_bot] at hr
      exact hr.elim
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨p.1, mem_finEnum _, rfl⟩, ?_⟩
    have ht : IsMinTag X p.1 := h
    rw [if_pos ht]
    exact (realize_slotTagF hs _).mpr rfl

theorem realize_maxPtF {s : PtSlot X H} {σ : H.Assignment A} {p : X.Point A}
    (hs : s.At σ p) :
    (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ) (maxPtF s) ↔
      ∀ q : X.Point A, (X.pointLinearOrder A).le q p) := by
  classical
  let := H.structure₁ (L := L.sum Language.order) σ
  have htop : (@Sentence.Realize _ A (H.structure₁ (L := L.sum Language.order) σ)
      ((pairLHom s s).onSentence (X.B.topAssignF L 0)) ↔
        X.B.atomSet p.2 = fun _ => True) :=
    (realize_pairLHom hs hs _).trans (X.B.realize_topAssignF ![p.2, p.2] 0)
  refine Iff.trans ?_ (X.pointIsTop_iff A p).symm
  rw [maxPtF, Sentence.Realize, Formula.realize_inf, realize_listSup]
  refine and_congr ?_ htop
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hψ
    by_cases ht : IsMaxTag X t
    · rw [if_pos ht] at hr
      have het : t = p.1 := (realize_slotTagF hs t).mp hr
      rw [← het]
      exact ht
    · rw [if_neg ht, Formula.realize_bot] at hr
      exact hr.elim
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨p.1, mem_finEnum _, rfl⟩, ?_⟩
    have ht : IsMaxTag X p.1 := h
    rw [if_pos ht]
    exact (realize_slotTagF hs _).mpr rfl

end Slots

/-! ### The configurations of a machine, as one block

A configuration is a control state and `k` points. The control state is a bit
vector (`DescriptiveComplexity.SOBlock.withTag`), the `k` points are the `k`
rounds of `DescriptiveComplexity.repMerged`, and the two configurations a
transition sentence compares are the two copies of
`DescriptiveComplexity.SOBlock.replicate`. -/

section Config

variable (X : ExpExpansion L) (k : ℕ) (S : Type) [Finite S]

/-- **The block whose assignments are the configurations**: one bit per control
state, and `k` rounds each holding one point of the expanded universe. -/
abbrev cfgBlock : SOBlock := (repMerged X.pointBlock k).withTag S

/-- The slot of the `i`-th round inside the configuration block. -/
def cfgSlot (i : Fin k) : PtSlot X (cfgBlock X k S) where
  ix x := Sum.inr (roundOneIx i X x)
  arity x := roundOneIx_arity i X x

/-- The slot of the `i`-th round of the `c`-th of two configurations. -/
def stepSlot (c : Fin 2) (i : Fin k) : PtSlot X ((cfgBlock X k S).replicate 2) where
  ix x := (c, (cfgSlot X k S i).ix x)
  arity x := (cfgSlot X k S i).arity x

/-- Reading a sentence about one configuration inside the `c`-th of two
copies. -/
def copyLHom (c : Fin 2) :
    ((L.sum Language.order).sum (cfgBlock X k S).lang) →ᴸ
      ((L.sum Language.order).sum ((cfgBlock X k S).replicate 2).lang) :=
  LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (fun y => (c, y)) fun _ => rfl)

/-- The atom “the control is in the state `s`”. -/
noncomputable def ctrlF (s : S) :
    ((L.sum Language.order).sum (cfgBlock X k S).lang).Sentence :=
  SOBlock.tagBitF (repMerged X.pointBlock k) S s

/-- The guard “this assignment is a configuration”: it names a control state,
and each of its `k` rounds holds a point of the expanded universe. -/
noncomputable def cfgGuardF : ((L.sum Language.order).sum (cfgBlock X k S).lang).Sentence :=
  SOBlock.tagGuardF (repMerged X.pointBlock k) S ⊓
    listInf ((List.finRange k).map fun i => slotGuardF (cfgSlot X k S i))

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The configuration assignment**: the control state in the tag bits, the
`k` points in the `k` rounds. -/
noncomputable def cfgAssign (s : S) (pts : Fin k → X.Map A) :
    (cfgBlock X k S).Assignment A :=
  SOBlock.tagAssign s (repBlockAssign X.pointBlock A k (roundAssign pts))

omit [L.Structure A] [LinearOrder A] in
/-- A round of a tagged assignment is read past the tag bits. -/
theorem cfgSlot_read (s : S) (μ : (repMerged X.pointBlock k).Assignment A) (i : Fin k) :
    (cfgSlot X k S i).read (SOBlock.tagAssign s μ) =
      SOBlock.homAssign (roundOneIx i X) (roundOneIx_arity i X) μ :=
  rfl

/-- **The `i`-th round of a configuration holds the `i`-th point.** -/
theorem cfgSlot_at (s : S) (pts : Fin k → X.Map A) (i : Fin k) :
    (cfgSlot X k S i).At (cfgAssign X k S s pts) (pts i).1 :=
  homAssign_roundOneIx i X (roundAssign pts)

omit [L.Structure A] [LinearOrder A] in
/-- **A round of one of two copies is that round of that copy.** -/
theorem stepSlot_at (σs : Fin 2 → (cfgBlock X k S).Assignment A) (c : Fin 2) (i : Fin k)
    {p : X.Point A} (h : (cfgSlot X k S i).At (σs c) p) :
    (stepSlot X k S c i).At ((cfgBlock X k S).replicateAssign σs) p :=
  h

/-- **Reading a configuration sentence in a copy** is reading it at that
copy's assignment. -/
theorem realize_copyLHom (σs : Fin 2 → (cfgBlock X k S).Assignment A) (c : Fin 2)
    (φ : ((L.sum Language.order).sum (cfgBlock X k S).lang).Sentence) :
    (@Sentence.Realize _ A
        (((cfgBlock X k S).replicate 2).structure₁ (L := L.sum Language.order)
          ((cfgBlock X k S).replicateAssign σs)) ((copyLHom X k S c).onSentence φ) ↔
      @Sentence.Realize _ A
        ((cfgBlock X k S).structure₁ (L := L.sum Language.order) (σs c)) φ) := by
  have hass : SOBlock.homAssign (fun y => (c, y)) (fun _ => rfl)
      ((cfgBlock X k S).replicateAssign σs) = σs c := rfl
  have h := SOBlock.realize_homSentence (B := cfgBlock X k S)
    (fun y => (c, y)) (fun _ => rfl) ((cfgBlock X k S).replicateAssign σs) φ
  rwa [hass] at h

theorem realize_ctrlF (s s' : S) (pts : Fin k → X.Map A) :
    (@Sentence.Realize _ A
        ((cfgBlock X k S).structure₁ (L := L.sum Language.order) (cfgAssign X k S s' pts))
        (ctrlF X k S s) ↔ s = s') :=
  SOBlock.realize_tagBitF (L := L.sum Language.order) (cfgAssign X k S s' pts) s

/-- **The guard is exactly “this is a configuration”.** -/
theorem realize_cfgGuardF (σ : (cfgBlock X k S).Assignment A) :
    (@Sentence.Realize _ A
        ((cfgBlock X k S).structure₁ (L := L.sum Language.order) σ) (cfgGuardF X k S) ↔
      ∃ (s : S) (pts : Fin k → X.Map A), σ = cfgAssign X k S s pts) := by
  let := (cfgBlock X k S).structure₁ (L := L.sum Language.order) σ
  rw [cfgGuardF, Sentence.Realize, Formula.realize_inf, realize_listInf]
  constructor
  · rintro ⟨htag, hrounds⟩
    obtain ⟨s, μ, rfl⟩ := (SOBlock.realize_tagGuardF (L := L.sum Language.order) σ).mp htag
    have hpt : ∀ i : Fin k, ∃ p : X.Map A,
        (cfgSlot X k S i).At (SOBlock.tagAssign s μ) p.1 := fun i =>
      (realize_slotGuardF _ _).mp (hrounds _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    choose pts hpts using hpt
    obtain ⟨ρs, rfl⟩ := repBlockAssign_surjective X.pointBlock A k μ
    have hρs : ρs = roundAssign pts := by
      funext i
      have h : (cfgSlot X k S i).read
          (SOBlock.tagAssign s (repBlockAssign X.pointBlock A k ρs)) =
            SOBlock.tagAssign (pts i).1.1 (pts i).1.2 := hpts i
      rw [cfgSlot_read, homAssign_roundOneIx] at h
      exact h
    exact ⟨s, pts,
      congrArg (fun ρ => SOBlock.tagAssign s (repBlockAssign X.pointBlock A k ρ)) hρs⟩
  · rintro ⟨s, pts, rfl⟩
    refine ⟨(SOBlock.realize_tagGuardF (L := L.sum Language.order) _).mpr ⟨s, _, rfl⟩,
      fun ψ hψ => ?_⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (realize_slotGuardF _ _).mpr ⟨pts i, cfgSlot_at X k S s pts i⟩

end Config

/-! ### The walk that simulates the machine -/

section Simulation

variable {X : ExpExpansion L} {k : ℕ} (M : HeadAutomaton X.E k)

/-- A quantifier-free formula about the `k` points of a configuration, read as
a sentence about the configuration. -/
noncomputable def testF (φ : (X.E.sum Language.order).Formula (Fin k)) :
    ((L.sum Language.order).sum (cfgBlock X k M.State).lang).Sentence :=
  (withTagLHom L (repMerged X.pointBlock k) M.State).onSentence (translQF X k finZeroElim φ)

open Classical in
/-- “The tests come out as the reading `r` says.” -/
noncomputable def readingF (r : M.TestIx → Bool) :
    ((L.sum Language.order).sum (cfgBlock X k M.State).lang).Sentence :=
  listInf (M.allTests.map fun i =>
    if r i then testF M (M.test i) else ∼(testF M (M.test i)))

/-- The move of one head, as a sentence about two configurations. Each case is
one of the four questions of `DescriptiveComplexity.ExpExpansion.eqPtF` and its
siblings, asked of the round the move reads and the round it writes. -/
noncomputable def moveF : HeadMove k → Fin k →
    ((L.sum Language.order).sum ((cfgBlock X k M.State).replicate 2).lang).Sentence
  | .stay, j => eqPtF (stepSlot X k M.State 0 j) (stepSlot X k M.State 1 j)
  | .toMin, j => minPtF (stepSlot X k M.State 1 j)
  | .toMax, j => maxPtF (stepSlot X k M.State 1 j)
  | .copy i, j => eqPtF (stepSlot X k M.State 0 i) (stepSlot X k M.State 1 j)
  | .succ i, j => covPtF (stepSlot X k M.State 0 i) (stepSlot X k M.State 1 j)
  | .pred i, j => covPtF (stepSlot X k M.State 1 j) (stepSlot X k M.State 0 i)

/-- One transition of the machine, as a sentence about two configurations: the
control state of each copy, the reading of the first, the guard of the second,
and the move of every head. -/
noncomputable def transF (s : M.State) (r : M.TestIx → Bool)
    (p : M.State × (Fin k → HeadMove k)) :
    ((L.sum Language.order).sum ((cfgBlock X k M.State).replicate 2).lang).Sentence :=
  ((copyLHom X k M.State 0).onSentence (ctrlF X k M.State s) ⊓
      (copyLHom X k M.State 1).onSentence (ctrlF X k M.State p.1)) ⊓
    (((copyLHom X k M.State 0).onSentence (readingF M r) ⊓
        (copyLHom X k M.State 1).onSentence (cfgGuardF X k M.State)) ⊓
      listInf ((List.finRange k).map fun j => moveF M (p.2 j) j))

/-- **The transition sentence of the simulation**: some transition of the
machine, at some control state and some reading. -/
noncomputable def machStepF :
    ((L.sum Language.order).sum ((cfgBlock X k M.State).replicate 2).lang).Sentence :=
  listSup ((finEnum M.State).map fun s =>
    listSup ((HeadAutomaton.allReadings M.TestIx).map fun r =>
      listSup ((M.trans s r).map fun p => transF M s r p)))

/-- **The walk over the base that simulates the machine**: its states are the
configurations, its transition sentence is the machine's table, its starting
states are the initial configurations and its accepting states are the ones
whose control accepts. -/
noncomputable def autoSpec : SOTCSpec L where
  B := cfgBlock X k M.State
  step := (SOBlock.twoLHom' (L.sum Language.order) (cfgBlock X k M.State)).onSentence (machStepF M)
  src := (ctrlF X k M.State M.start ⊓ cfgGuardF X k M.State) ⊓
    listInf ((List.finRange k).map fun i => minPtF (cfgSlot X k M.State i))
  tgt := listSup ((finEnum M.State).map fun s =>
    if M.accept s then ctrlF X k M.State s else ⊥)

/-! ### Correctness -/

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- With a trivial domain, quantifying over the points of the expanded universe
is quantifying over every tagged assignment. -/
theorem forall_point_of_total (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (P : X.Point A → Prop) : (∀ q : X.Map A, P q.1) ↔ ∀ q : X.Point A, P q :=
  ⟨fun h q => h ⟨q, htot q⟩, fun h q => h q.1⟩

theorem realize_testF (s : M.State) (pts : Fin k → X.Map A)
    {φ : (X.E.sum Language.order).Formula (Fin k)} (hqf : φ.IsQF) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A
        ((cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
          (cfgAssign X k M.State s pts)) (testF M φ) ↔
      φ.Realize (M := X.Map A) pts) := by
  let := X.mapLinearOrder A
  refine (realize_withTagLHom (cfgAssign X k M.State s pts) _).trans ?_
  exact realize_translQF pts hqf

theorem realize_readingF (s : M.State) (pts : Fin k → X.Map A) (r : M.TestIx → Bool) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A
        ((cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
          (cfgAssign X k M.State s pts)) (readingF M r) ↔ M.reading pts = r) := by
  classical
  let := X.mapLinearOrder A
  let := (cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
    (cfgAssign X k M.State s pts)
  have key : ∀ i : M.TestIx,
      (@Sentence.Realize _ A
        ((cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
          (cfgAssign X k M.State s pts))
        (if r i then testF M (M.test i) else ∼(testF M (M.test i))) ↔
          M.reading pts i = r i) := by
    intro i
    have ht := realize_testF M s pts (M.test_qf i)
    rw [HeadAutomaton.reading]
    cases hri : r i with
    | true => simp [ht]
    | false => simp [ht]
  rw [readingF, Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i
    exact (key i).mp (h _ (List.mem_map.mpr ⟨i, M.mem_allTests i, rfl⟩))
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact (key i).mpr rfl

theorem realize_moveF (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (σs : Fin 2 → (cfgBlock X k M.State).Assignment A) (s₀ s₁ : M.State)
    (x y : Fin k → X.Map A) (h₀ : σs 0 = cfgAssign X k M.State s₀ x)
    (h₁ : σs 1 = cfgAssign X k M.State s₁ y) (mv : HeadMove k) (j : Fin k) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A
        (((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
          ((cfgBlock X k M.State).replicateAssign σs)) (moveF M mv j) ↔
      mv.Holds x j (y j)) := by
  let := X.mapLinearOrder A
  have hx : ∀ i : Fin k, (stepSlot X k M.State 0 i).At
      ((cfgBlock X k M.State).replicateAssign σs) (x i).1 := by
    intro i
    refine stepSlot_at X k M.State σs 0 i ?_
    rw [h₀]
    exact cfgSlot_at X k M.State s₀ x i
  have hy : ∀ i : Fin k, (stepSlot X k M.State 1 i).At
      ((cfgBlock X k M.State).replicateAssign σs) (y i).1 := by
    intro i
    refine stepSlot_at X k M.State σs 1 i ?_
    rw [h₁]
    exact cfgSlot_at X k M.State s₁ y i
  cases mv with
  | stay =>
    refine (realize_eqPtF (hx j) (hy j)).trans ?_
    exact ⟨fun h => (Subtype.ext h).symm, fun h => congrArg Subtype.val h.symm⟩
  | toMin =>
    refine (realize_minPtF (hy j)).trans ?_
    exact (forall_point_of_total htot fun q => (X.pointLinearOrder A).le (y j).1 q).symm
  | toMax =>
    refine (realize_maxPtF (hy j)).trans ?_
    exact (forall_point_of_total htot fun q => (X.pointLinearOrder A).le q (y j).1).symm
  | copy i =>
    refine (realize_eqPtF (hx i) (hy j)).trans ?_
    exact ⟨fun h => (Subtype.ext h).symm, fun h => congrArg Subtype.val h.symm⟩
  | succ i =>
    refine (realize_covPtF (hx i) (hy j)).trans (and_congr Iff.rfl ?_)
    exact (forall_point_of_total htot fun q =>
      ¬((X.pointLinearOrder A).lt (x i).1 q ∧ (X.pointLinearOrder A).lt q (y j).1)).symm
  | pred i =>
    refine (realize_covPtF (hy j) (hx i)).trans (and_congr Iff.rfl ?_)
    exact (forall_point_of_total htot fun q =>
      ¬((X.pointLinearOrder A).lt (y j).1 q ∧ (X.pointLinearOrder A).lt q (x i).1)).symm

theorem realize_transF (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (σs : Fin 2 → (cfgBlock X k M.State).Assignment A) (s : M.State) (x : Fin k → X.Map A)
    (h₀ : σs 0 = cfgAssign X k M.State s x) (s₀ : M.State) (r : M.TestIx → Bool)
    (p : M.State × (Fin k → HeadMove k)) :
    letI := X.mapLinearOrder A
    (@Sentence.Realize _ A
        (((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
          ((cfgBlock X k M.State).replicateAssign σs)) (transF M s₀ r p) ↔
      (s₀ = s ∧ M.reading x = r ∧ ∃ y : Fin k → X.Map A,
        σs 1 = cfgAssign X k M.State p.1 y ∧ ∀ j, (p.2 j).Holds x j (y j))) := by
  let := X.mapLinearOrder A
  let := ((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
    ((cfgBlock X k M.State).replicateAssign σs)
  have hctrl0 : (@Sentence.Realize _ A _
      ((copyLHom X k M.State 0).onSentence (ctrlF X k M.State s₀)) ↔ s₀ = s) := by
    refine (realize_copyLHom X k M.State σs 0 _).trans ?_
    rw [h₀]
    exact realize_ctrlF X k M.State s₀ s x
  have hread : (@Sentence.Realize _ A _
      ((copyLHom X k M.State 0).onSentence (readingF M r)) ↔ M.reading x = r) := by
    refine (realize_copyLHom X k M.State σs 0 _).trans ?_
    rw [h₀]
    exact realize_readingF M s x r
  have hguard : (@Sentence.Realize _ A _
      ((copyLHom X k M.State 1).onSentence (cfgGuardF X k M.State)) ↔
        ∃ (s' : M.State) (y : Fin k → X.Map A), σs 1 = cfgAssign X k M.State s' y) :=
    (realize_copyLHom X k M.State σs 1 _).trans (realize_cfgGuardF X k M.State (σs 1))
  rw [transF, Sentence.Realize]
  simp only [Formula.realize_inf, realize_listInf]
  constructor
  · rintro ⟨⟨hc0, hc1⟩, ⟨hr, hg⟩, hm⟩
    obtain ⟨s', y, hy⟩ := hguard.mp hg
    have hps : p.1 = s' := by
      refine (realize_ctrlF X k M.State p.1 s' y).mp ?_
      have hc1' := (realize_copyLHom X k M.State σs 1 _).mp hc1
      rwa [hy] at hc1'
    refine ⟨hctrl0.mp hc0, hread.mp hr, y, by rw [hy, hps], fun j => ?_⟩
    refine (realize_moveF M htot σs s p.1 x y h₀ (by rw [hy, hps]) (p.2 j) j).mp ?_
    exact hm _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  · rintro ⟨hs₀, hr, y, hy, hm⟩
    refine ⟨⟨hctrl0.mpr hs₀, ?_⟩, ⟨hread.mpr hr, hguard.mpr ⟨p.1, y, hy⟩⟩, fun ψ hψ => ?_⟩
    · refine (realize_copyLHom X k M.State σs 1 _).mpr ?_
      rw [hy]
      exact (realize_ctrlF X k M.State p.1 p.1 y).mpr rfl
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
      exact (realize_moveF M htot σs s p.1 x y h₀ hy (p.2 j) j).mpr (hm j)

theorem step_autoSpec (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (σ τ : (cfgBlock X k M.State).Assignment A) (s : M.State) (x : Fin k → X.Map A)
    (hσ : σ = cfgAssign X k M.State s x) :
    letI := X.mapLinearOrder A
    ((autoSpec M).Step σ τ ↔ ∃ (s' : M.State) (y : Fin k → X.Map A),
      τ = cfgAssign X k M.State s' y ∧ M.Step (s, x) (s', y)) := by
  classical
  let := X.mapLinearOrder A
  let := ((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
    ((cfgBlock X k M.State).replicateAssign ![σ, τ])
  have hstep : (autoSpec M).Step σ τ ↔ @Sentence.Realize _ A
      (((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
        ((cfgBlock X k M.State).replicateAssign ![σ, τ])) (machStepF M) :=
    SOBlock.realize_twoLHom' (L := L.sum Language.order) (cfgBlock X k M.State) ![σ, τ]
      (machStepF M)
  have htr : ∀ (s₀ : M.State) (r : M.TestIx → Bool) (p : M.State × (Fin k → HeadMove k)),
      (@Sentence.Realize _ A
        (((cfgBlock X k M.State).replicate 2).structure₁ (L := L.sum Language.order)
          ((cfgBlock X k M.State).replicateAssign ![σ, τ])) (transF M s₀ r p) ↔
        (s₀ = s ∧ M.reading x = r ∧ ∃ y : Fin k → X.Map A,
          τ = cfgAssign X k M.State p.1 y ∧ ∀ j, (p.2 j).Holds x j (y j))) := fun s₀ r p =>
    realize_transF M htot ![σ, τ] s x hσ s₀ r p
  rw [hstep, machStepF, Sentence.Realize, realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨s₀, -, rfl⟩ := List.mem_map.mp hψ
    rw [realize_listSup] at hr
    obtain ⟨χ, hχ, hr⟩ := hr
    obtain ⟨rd, -, rfl⟩ := List.mem_map.mp hχ
    rw [realize_listSup] at hr
    obtain ⟨θ, hθ, hr⟩ := hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hθ
    obtain ⟨rfl, rfl, y, hy, hm⟩ := (htr s₀ rd p).mp hr
    exact ⟨p.1, y, hy, p, hp, rfl, hm⟩
  · rintro ⟨s', y, hy, p, hp, hps, hm⟩
    refine ⟨_, List.mem_map.mpr ⟨s, mem_finEnum _, rfl⟩, ?_⟩
    rw [realize_listSup]
    refine ⟨_, List.mem_map.mpr ⟨M.reading x, HeadAutomaton.mem_allReadings _, rfl⟩, ?_⟩
    rw [realize_listSup]
    refine ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    exact (htr s (M.reading x) p).mpr ⟨rfl, rfl, y, by rw [hy, hps], hm⟩

theorem isSrc_autoSpec (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (σ : (cfgBlock X k M.State).Assignment A) :
    letI := X.mapLinearOrder A
    ((autoSpec M).IsSrc σ ↔ ∃ x : Fin k → X.Map A,
      σ = cfgAssign X k M.State M.start x ∧ ∀ j, ∀ b : X.Map A, x j ≤ b) := by
  let := X.mapLinearOrder A
  have hmins : ∀ (s : M.State) (x : Fin k → X.Map A),
      ((@Formula.Realize _ A
          ((cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
            (cfgAssign X k M.State s x)) _
          (listInf ((List.finRange k).map fun i => minPtF (cfgSlot X k M.State i))) default) ↔
        ∀ j, ∀ b : X.Map A, x j ≤ b) := by
    intro s x
    let := (cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
      (cfgAssign X k M.State s x)
    rw [realize_listInf]
    constructor
    · intro h j
      exact (forall_point_of_total htot fun q => (X.pointLinearOrder A).le (x j).1 q).mpr
        ((realize_minPtF (cfgSlot_at X k M.State s x j)).mp
          (h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)))
    · intro h ψ hψ
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hψ
      exact (realize_minPtF (cfgSlot_at X k M.State s x j)).mpr
        ((forall_point_of_total htot fun q => (X.pointLinearOrder A).le (x j).1 q).mp (h j))
  let := (cfgBlock X k M.State).structure₁ (L := L.sum Language.order) σ
  change (@Formula.Realize _ A _ _
    ((ctrlF X k M.State M.start ⊓ cfgGuardF X k M.State) ⊓
      listInf ((List.finRange k).map fun i => minPtF (cfgSlot X k M.State i))) default ↔ _)
  rw [Formula.realize_inf, Formula.realize_inf]
  constructor
  · rintro ⟨⟨hc, hg⟩, hm⟩
    obtain ⟨s, x, rfl⟩ := (realize_cfgGuardF X k M.State σ).mp hg
    have hs : M.start = s := (realize_ctrlF X k M.State M.start s x).mp hc
    exact ⟨x, by rw [hs], (hmins s x).mp hm⟩
  · rintro ⟨x, rfl, hb⟩
    exact ⟨⟨(realize_ctrlF X k M.State M.start M.start x).mpr rfl,
      (realize_cfgGuardF X k M.State _).mpr ⟨M.start, x, rfl⟩⟩, (hmins M.start x).mpr hb⟩

omit [Finite A] [Nonempty A] in
theorem isTgt_autoSpec (σ : (cfgBlock X k M.State).Assignment A) (s : M.State)
    (x : Fin k → X.Map A) (hσ : σ = cfgAssign X k M.State s x) :
    (autoSpec M).IsTgt σ ↔ M.accept s = true := by
  classical
  subst hσ
  let := (cfgBlock X k M.State).structure₁ (L := L.sum Language.order)
    (cfgAssign X k M.State s x)
  change (@Formula.Realize _ A _ _
    (listSup ((finEnum M.State).map fun s' => if M.accept s' then ctrlF X k M.State s' else ⊥))
    default ↔ _)
  rw [realize_listSup]
  constructor
  · rintro ⟨ψ, hψ, hr⟩
    obtain ⟨s', -, rfl⟩ := List.mem_map.mp hψ
    by_cases hacc : M.accept s' = true
    · rw [if_pos hacc] at hr
      have hs' : s' = s := (realize_ctrlF X k M.State s' s x).mp hr
      rw [← hs']
      exact hacc
    · rw [if_neg hacc, Formula.realize_bot] at hr
      exact hr.elim
  · intro hacc
    refine ⟨_, List.mem_map.mpr ⟨s, mem_finEnum _, rfl⟩, ?_⟩
    rw [if_pos hacc]
    exact (realize_ctrlF X k M.State s s x).mpr rfl

/-- A walk of the simulation that starts at a configuration stays at
configurations, and is a run of the machine. -/
theorem reach_autoSpec_of (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    {σ τ : (cfgBlock X k M.State).Assignment A} (s : M.State) (x : Fin k → X.Map A)
    (hσ : σ = cfgAssign X k M.State s x) :
    letI := X.mapLinearOrder A
    (Relation.ReflTransGen (autoSpec M).Step σ τ →
      ∃ (s' : M.State) (y : Fin k → X.Map A), τ = cfgAssign X k M.State s' y ∧
        Relation.ReflTransGen M.Step (s, x) (s', y)) := by
  let := X.mapLinearOrder A
  intro h
  induction h with
  | refl => exact ⟨s, x, hσ, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨s', y, hc, hreach⟩ := ih
    obtain ⟨s'', z, hd, hstep⟩ := (step_autoSpec M htot c d s' y hc).mp hcd
    exact ⟨s'', z, hd, hreach.tail hstep⟩

/-- A run of the machine is a walk of the simulation. -/
theorem reach_autoSpec (htot : ∀ p : X.Point A, DomHolds (X := X) p)
    (a b : M.Config (X.Map A)) :
    letI := X.mapLinearOrder A
    (Relation.ReflTransGen M.Step a b →
      Relation.ReflTransGen (autoSpec M).Step (cfgAssign X k M.State a.1 a.2)
        (cfgAssign X k M.State b.1 b.2)) := by
  let := X.mapLinearOrder A
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    refine ih.tail ?_
    exact (step_autoSpec M htot _ _ c.1 c.2 rfl).mpr ⟨d.1, d.2, rfl, hcd⟩

/-- **The simulation is correct**: the walk over the base accepts exactly when
the machine accepts the expanded structure. -/
theorem accepts_autoSpec (htot : ∀ p : X.Point A, DomHolds (X := X) p) :
    letI := X.mapLinearOrder A
    ((autoSpec M).Accepts A ↔ M.Accepts (X.Map A)) := by
  let := X.mapLinearOrder A
  constructor
  · rintro ⟨σ, τ, hs, ht, hreach⟩
    obtain ⟨x, hσ, hmin⟩ := (isSrc_autoSpec M htot σ).mp hs
    obtain ⟨s', y, hτ, hrun⟩ := reach_autoSpec_of M htot M.start x hσ hreach
    exact ⟨(M.start, x), (s', y), ⟨rfl, hmin⟩, hrun,
      (isTgt_autoSpec M τ s' y hτ).mp ht⟩
  · rintro ⟨c₀, c, ⟨hstart, hmin⟩, hreach, hacc⟩
    refine ⟨cfgAssign X k M.State c₀.1 c₀.2, cfgAssign X k M.State c.1 c.2, ?_, ?_,
      reach_autoSpec M htot c₀ c hreach⟩
    · exact (isSrc_autoSpec M htot _).mpr ⟨c₀.2, by rw [hstart], hmin⟩
    · exact (isTgt_autoSpec M _ c.1 c.2 rfl).mpr hacc

end Simulation

end ExpExpansion

end DescriptiveComplexity
