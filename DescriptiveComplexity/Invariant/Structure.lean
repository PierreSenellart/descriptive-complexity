/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Stages
import DescriptiveComplexity.Invariant.OrderedPebble

/-!
# The invariant structure `Iᵏ A`

The quotient of the `k`-tuples of a structure by `≡ᵏ`
(`DescriptiveComplexity.InvMap`), as a structure
over the *invariant vocabulary* `DescriptiveComplexity.invLang`:

* one unary *bit* per coordinate equality (`DescriptiveComplexity.InvRel.eqBit`)
  and per base relation at a selection of coordinates
  (`DescriptiveComplexity.InvRel.relBit`) – the atomic type of a class;
* one binary *substitution* relation per pebble
  (`DescriptiveComplexity.InvRel.sub`): the classes reachable by moving that
  pebble – how the invariant structure quantifies over `A`;
* one binary *rearrangement* relation per coordinate selection
  (`DescriptiveComplexity.InvRel.rearr`): the class of a permuted, repeated,
  selected copy of a tuple – how the invariant structure reads relation
  variables at rearranged argument tuples.

The vocabulary does not depend on the agreement family `S`; the structure
does, and interprets the bit of a base relation *outside* `S` as false, which
keeps every interpretation well-defined on classes
(`DescriptiveComplexity.equivK_atomicAgreeOn_of_pairSub` for the coordinate
manipulations, the game move `DescriptiveComplexity.EquivK.update` for
substitution).

The second half of the file equips `Iᵏ A` with a linear order: any coloring
`c₀` whose agreement is atomic agreement (the syntactic bit coloring of the
definable refinement, in `DescriptiveComplexity.Invariant.OrderDef`) induces
the canonical order `DescriptiveComplexity.OrdK` on tuples, which descends to
a linear order on the classes (`DescriptiveComplexity.invLinearOrder`) – the
order the simulated computation of the Abiteboul–Vianu argument runs on.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The invariant vocabulary -/

/-- The relation symbols of the invariant vocabulary: atomic-type bits,
substitution along a pebble, rearrangement along a coordinate selection. -/
inductive InvRel (L : Language.{0, 0}) (k : ℕ) : ℕ → Type
  /-- The tuples of the class identify coordinates `i` and `j`. -/
  | eqBit (i j : Fin k) : InvRel L k 1
  /-- The base relation `R` holds on the tuples of the class at the
  selection `g` of coordinates. -/
  | relBit (R : Σ n, L.Relations n) (g : Fin R.1 → Fin k) : InvRel L k 1
  /-- The second class is reached from the first by moving pebble `j`. -/
  | sub (j : Fin k) : InvRel L k 2
  /-- The second class is the rearrangement of the first along `σ`. -/
  | rearr (σ : Fin k → Fin k) : InvRel L k 2

/-- The invariant vocabulary: the relational language of the invariant
structure. -/
def invLang (L : Language.{0, 0}) (k : ℕ) : Language.{0, 0} :=
  ⟨fun _ => Empty, InvRel L k⟩

instance (L : Language.{0, 0}) (k : ℕ) : IsRelational (invLang L k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-! ### The quotient -/

variable {L : Language.{0, 0}}

/-- `k`-tuples up to `≡ᵏ`, as a setoid. -/
def invSetoid (S : Set (Σ n, L.Relations n)) (k : ℕ) (A : Type) [L.Structure A] :
    Setoid (Fin k → A) :=
  ⟨EquivK (atomicAgreeOn S A k), equivK_atomicAgreeOn_equivalence⟩

/-- **The invariant structure's universe**: the `≡ᵏ`-classes of `k`-tuples
over `A`, relative to the agreement family `S`. -/
def InvMap (S : Set (Σ n, L.Relations n)) (k : ℕ) (A : Type) [L.Structure A] :
    Type :=
  Quotient (invSetoid S k A)

namespace InvMap

variable {S : Set (Σ n, L.Relations n)} {k : ℕ} {A : Type} [L.Structure A]

/-- The class of a `k`-tuple. -/
def mk (S : Set (Σ n, L.Relations n)) (u : Fin k → A) : InvMap S k A :=
  Quotient.mk (invSetoid S k A) u

theorem mk_eq_mk {u v : Fin k → A} :
    mk S u = mk S v ↔ EquivK (atomicAgreeOn S A k) u v :=
  Quotient.eq

theorem exists_rep (c : InvMap S k A) : ∃ u : Fin k → A, mk S u = c :=
  Quotient.exists_rep c

instance [Finite A] : Finite (InvMap S k A) :=
  Quotient.finite _

instance [Nonempty A] : Nonempty (InvMap S k A) :=
  ⟨mk S fun _ => Classical.arbitrary A⟩

section Rels

variable [Finite A]

omit [Finite A] in
private theorem equivK_equivalence' :
    Equivalence (EquivK (atomicAgreeOn S A k)) :=
  equivK_atomicAgreeOn_equivalence

/-- The equality bit on classes. -/
def eqBitRel (i j : Fin k) : InvMap S k A → Prop :=
  Quotient.lift (fun u => u i = u j) fun _ _ huv =>
    propext (huv.initial.1 i j)

/-- The relation bit on classes: false outside the agreement family, the
base relation at the selection inside it. -/
def relBitRel (R : Σ n, L.Relations n) (g : Fin R.1 → Fin k) :
    InvMap S k A → Prop :=
  Quotient.lift (fun u => R ∈ S ∧ RelMap R.2 fun p => u (g p)) fun _ _ huv =>
    propext (and_congr_right fun hR => huv.initial.2 R.2 hR g)

/-- The substitution relation on classes: the second class is reached from
the first by a move of pebble `j`. -/
def subRel (j : Fin k) : InvMap S k A → InvMap S k A → Prop :=
  Quotient.lift₂
    (fun u v => ∃ a, EquivK (atomicAgreeOn S A k) (Function.update u j a) v)
    (by
      intro u v u' v' huu' hvv'
      refine propext ⟨?_, ?_⟩
      · rintro ⟨a, ha⟩
        obtain ⟨a', ha'⟩ := huu'.update j a
        exact ⟨a', equivK_equivalence'.trans (equivK_equivalence'.symm ha')
          (equivK_equivalence'.trans ha hvv')⟩
      · rintro ⟨a, ha⟩
        obtain ⟨a', ha'⟩ := (equivK_equivalence'.symm huu').update j a
        exact ⟨a', equivK_equivalence'.trans (equivK_equivalence'.symm ha')
          (equivK_equivalence'.trans ha (equivK_equivalence'.symm hvv'))⟩)

/-- The rearrangement relation on classes: the second class is the
rearrangement of the first along `σ`. -/
def rearrRel (σ : Fin k → Fin k) : InvMap S k A → InvMap S k A → Prop :=
  Quotient.lift₂
    (fun u v => EquivK (atomicAgreeOn S A k) (fun p => u (σ p)) v)
    (by
      intro u v u' v' huu' hvv'
      have h : EquivK (atomicAgreeOn S A k) (fun p => u (σ p))
          fun p => u' (σ p) :=
        equivK_atomicAgreeOn_of_pairSub (fun j => ⟨σ j, rfl, rfl⟩) huu'
      refine propext ⟨fun hu => ?_, fun hu => ?_⟩
      · exact equivK_equivalence'.trans (equivK_equivalence'.symm h)
          (equivK_equivalence'.trans hu hvv')
      · exact equivK_equivalence'.trans h
          (equivK_equivalence'.trans hu (equivK_equivalence'.symm hvv')))

/-- **The invariant structure**: the interpretation of the invariant
vocabulary on the `≡ᵏ`-classes. -/
instance structure' : (invLang L k).Structure (InvMap S k A) where
  funMap f := isEmptyElim f
  RelMap {n} r x :=
    match n, r, x with
    | _, .eqBit i j, x => eqBitRel i j (x 0)
    | _, .relBit R g, x => relBitRel R g (x 0)
    | _, .sub j, x => subRel j (x 0) (x 1)
    | _, .rearr σ, x => rearrRel σ (x 0) (x 1)

/-! #### Reading the relations at representatives -/

theorem relMap_eqBit (i j : Fin k) (x : Fin 1 → InvMap S k A) (u : Fin k → A)
    (hu : x 0 = mk S u) :
    RelMap (L := invLang L k) (.eqBit i j) x ↔ u i = u j := by
  change eqBitRel i j (x 0) ↔ _
  rw [hu]
  exact Iff.rfl

theorem relMap_relBit (R : Σ n, L.Relations n) (g : Fin R.1 → Fin k)
    (x : Fin 1 → InvMap S k A) (u : Fin k → A) (hu : x 0 = mk S u) :
    RelMap (L := invLang L k) (.relBit R g) x ↔
      (R ∈ S ∧ RelMap R.2 fun p => u (g p)) := by
  change relBitRel R g (x 0) ↔ _
  rw [hu]
  exact Iff.rfl

theorem relMap_sub (j : Fin k) (x : Fin 2 → InvMap S k A) (u v : Fin k → A)
    (hu : x 0 = mk S u) (hv : x 1 = mk S v) :
    RelMap (L := invLang L k) (.sub j) x ↔
      ∃ a, EquivK (atomicAgreeOn S A k) (Function.update u j a) v := by
  change subRel j (x 0) (x 1) ↔ _
  rw [hu, hv]
  exact Iff.rfl

theorem relMap_rearr (σ : Fin k → Fin k) (x : Fin 2 → InvMap S k A)
    (u v : Fin k → A) (hu : x 0 = mk S u) (hv : x 1 = mk S v) :
    RelMap (L := invLang L k) (.rearr σ) x ↔
      EquivK (atomicAgreeOn S A k) (fun p => u (σ p)) v := by
  change rearrRel σ (x 0) (x 1) ↔ _
  rw [hu, hv]
  exact Iff.rfl

end Rels

end InvMap

/-! ### The linear order on the classes -/

section Order

variable {S : Set (Σ n, L.Relations n)} {k : ℕ} {A : Type} [L.Structure A]
variable {β : Type*} [LinearOrder β] {c₀ : (Fin k → A) → β}

/-- Any coloring whose agreement is atomic agreement induces, through the
canonical order on tuples (`DescriptiveComplexity.OrdK`), a linear order on
the `≡ᵏ`-classes (decidability by choice). -/
@[instance_reducible]
noncomputable def invLinearOrder [Finite A]
    (hc : colorAgree c₀ = atomicAgreeOn S A k) : LinearOrder (InvMap S k A) := by
  have hE : ∀ {u v : Fin k → A}, EquivK (atomicAgreeOn S A k) u v ↔
      EquivK (colorAgree c₀) u v := by
    intro u v
    rw [hc]
  refine
    { le := Quotient.lift₂ (fun u v => OrdK c₀ u v ∨
        EquivK (atomicAgreeOn S A k) u v) ?_
      le_refl := ?_
      le_trans := ?_
      le_antisymm := ?_
      le_total := ?_
      toDecidableLE := fun _ _ => Classical.propDecidable _ }
  · -- well-definedness
    intro u v u' v' huu' hvv'
    have huu'' := hE.mp huu'
    have hvv'' := hE.mp hvv'
    refine propext (or_congr ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h => ?_, fun h => ?_⟩)
    · exact OrdK.congr_right c₀ ((equivK_equivalence (colorAgree_equivalence c₀)).symm
        huu'') (OrdK.congr_left c₀ h hvv'')
    · exact OrdK.congr_right c₀ huu''
        (OrdK.congr_left c₀ h ((equivK_equivalence (colorAgree_equivalence c₀)).symm
          hvv''))
    · exact (equivK_atomicAgreeOn_equivalence.trans
        (equivK_atomicAgreeOn_equivalence.symm huu')
        (equivK_atomicAgreeOn_equivalence.trans h hvv'))
    · exact (equivK_atomicAgreeOn_equivalence.trans huu'
        (equivK_atomicAgreeOn_equivalence.trans h
          (equivK_atomicAgreeOn_equivalence.symm hvv')))
  · -- reflexivity
    intro c
    obtain ⟨u, rfl⟩ := InvMap.exists_rep c
    exact Or.inr (equivK_atomicAgreeOn_equivalence.refl u)
  · -- transitivity
    intro a b c
    obtain ⟨u, rfl⟩ := InvMap.exists_rep a
    obtain ⟨v, rfl⟩ := InvMap.exists_rep b
    obtain ⟨w, rfl⟩ := InvMap.exists_rep c
    rintro (h₁ | h₁) (h₂ | h₂)
    · exact Or.inl (ordK_trans c₀ h₁ h₂)
    · exact Or.inl (OrdK.congr_left c₀ h₁ (hE.mp h₂))
    · exact Or.inl (OrdK.congr_right c₀ (hE.mp h₁) h₂)
    · exact Or.inr (equivK_atomicAgreeOn_equivalence.trans h₁ h₂)
  · -- antisymmetry
    intro a b
    obtain ⟨u, rfl⟩ := InvMap.exists_rep a
    obtain ⟨v, rfl⟩ := InvMap.exists_rep b
    rintro (h₁ | h₁) (h₂ | h₂)
    · exact absurd h₂ (ordK_asymm c₀ h₁)
    · exfalso
      have h2' := hE.mp h₂
      rw [← incompRel_ordK_eq] at h2'
      exact h2'.2 h₁
    · exfalso
      have h1' := hE.mp h₁
      rw [← incompRel_ordK_eq] at h1'
      exact h1'.2 h₂
    · exact Quotient.sound h₁
  · -- totality
    intro a b
    obtain ⟨u, rfl⟩ := InvMap.exists_rep a
    obtain ⟨v, rfl⟩ := InvMap.exists_rep b
    rcases Classical.em (EquivK (atomicAgreeOn S A k) u v) with h | h
    · exact Or.inl (Or.inr h)
    · rcases ordK_or_of_not_equivK c₀ (fun h' => h (hE.mpr h')) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')

/-- The order on classes, read at representatives: strictly below in the
canonical order, or equivalent. -/
theorem invLinearOrder_le_iff [Finite A]
    (hc : colorAgree c₀ = atomicAgreeOn S A k) (u v : Fin k → A) :
    (letI := invLinearOrder (S := S) hc;
      InvMap.mk S u ≤ InvMap.mk (A := A) S v) ↔
      (OrdK c₀ u v ∨ EquivK (atomicAgreeOn S A k) u v) :=
  Iff.rfl

end Order

end DescriptiveComplexity
