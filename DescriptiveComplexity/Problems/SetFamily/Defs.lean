/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Numbers.Unary

/-!
# Set Cover, Hitting Set and Set Packing: definitions

The three classical problems on set systems ([Karp 1972][karp1972reducibility]),
as decision problems on `FirstOrder.Language.setSystem`-structures: a universe
carrying two unary marks separating the ground *elements* from the *sets* of a
family, a binary incidence relation between them, and a third unary mark
carrying the numeric threshold `k` in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary` (the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free).

* `DescriptiveComplexity.SetCover`: some subfamily of at most `k` sets covers every
  element;
* `DescriptiveComplexity.HittingSet`: some set of at most `k` elements meets every
  set of the family;
* `DescriptiveComplexity.SetPacking`: some subfamily of at least `k` pairwise
  disjoint sets exists.

They are the set-system counterparts of the clique family
(`DescriptiveComplexity.Problems.CliqueFamily`), and are organized the same way: the
semantics is carried by generic properties of predicates on a type –
`DescriptiveComplexity.CoversOn`, its transpose `DescriptiveComplexity.HitsOn` (elements
and sets exchanged, incidence read backwards) and `DescriptiveComplexity.PacksOn` –
which the isomorphism-invariance proofs and the reductions share. Set Cover
and Hitting Set being literally one property read in two directions is what
makes them inter-reducible by a single interpretation
(`DescriptiveComplexity.Problems.SetFamily.Reductions`), just as complementation
relates Clique and Independent Set.

Two conventions worth stating once:

* Nothing forces an element of the universe to be an element or a set, or
  forbids it to be both: elements outside both marks are junk that no
  condition mentions, which is what lets a first-order interpretation build a
  set system inside a tagged power of its input universe without a
  definable-subset mechanism. Junk *marked* elements would change the
  threshold, so interpretations remain responsible for the mark they define.
* Disjointness in `DescriptiveComplexity.PacksOn` is required of the ground
  elements only. This is not cosmetic: the interpretation of
  `DescriptiveComplexity.Problems.SetFamily.FromGraphs` produces junk tuples incident
  to two sets each, and those must not count as witnesses of an intersection.

As with the clique family, cardinality thresholds are only meaningful on
finite structures, so finiteness of the universe is part of the yes-instances;
by `DescriptiveComplexity.ComplexityClass.mem_congr_finite` this does not affect
any complexity-theoretic statement.
-/

/- The language of set systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of set systems. -/
inductive setSystemRel : ℕ → Type
  /-- `elem a`: the element `a` belongs to the ground set. -/
  | elem : setSystemRel 1
  /-- `fam a`: the element `a` is one of the sets of the family. -/
  | fam : setSystemRel 1
  /-- `mem a b`: the ground element `a` belongs to the set `b`. -/
  | mem : setSystemRel 2
  /-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : setSystemRel 1
  deriving DecidableEq

/-- The relational language of set systems: a bipartite incidence structure
between ground elements and sets of a family, together with a marked subset of
the universe whose cardinality serves as threshold. -/
protected def setSystem : Language :=
  ⟨fun _ => Empty, setSystemRel⟩
  deriving IsRelational

/-- The ground-element symbol of set systems. -/
abbrev ssElem : Language.setSystem.Relations 1 := .elem

/-- The family symbol of set systems. -/
abbrev ssFam : Language.setSystem.Relations 1 := .fam

/-- The incidence symbol of set systems. -/
abbrev ssMem : Language.setSystem.Relations 2 := .mem

/-- The mark symbol of set systems. -/
abbrev ssMarked : Language.setSystem.Relations 1 := .marked

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic covering property

The property underlying both problems, for arbitrary unary predicates `Ep`
(ground elements), `Fp` (sets of the family) and `Kp` (marks), and an
arbitrary binary predicate `Mp` (incidence) on a type. -/

section Generic

variable {A : Type}

/-- Some subfamily of the `Fp`-sets covers every `Ep`-element and is at most
as large as the number encoded by the `Kp`-marked elements: “some cover is at
most as large as the marked set”. -/
def CoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard ≤ {x | Kp x}.ncard

/-- Some set of `Ep`-elements meets every `Fp`-set and is at most as large as
the number encoded by the `Kp`-marked elements: “some hitting set is at most
as large as the marked set”. This is `DescriptiveComplexity.CoversOn` with the roles
of elements and sets exchanged and the incidence relation transposed. -/
def HitsOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CoversOn Fp Ep (fun s x => Mp x s) Kp

/-- Some subfamily of the `Fp`-sets is pairwise disjoint – no `Ep`-element
belongs to two distinct members – and is at least as large as the number
encoded by the `Kp`-marked elements: “some packing is at least as large as the
marked set”. -/
def PacksOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
    (∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')) ∧
    {x | Kp x}.ncard ≤ {s | G s}.ncard

/-- Some subfamily of the `Fp`-sets covers every `Ep`-element *exactly once*:
it covers, and no element belongs to two distinct members. Unlike the three
properties above this one carries no threshold – exactness is the whole
constraint. -/
def ExactlyCoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    ∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')

/-- Exactness in the “exactly one” form: covering plus disjointness is one
covering set per element. -/
theorem exactlyCoversOn_iff_unique (Ep Fp : A → Prop) (Mp : A → A → Prop) :
    ExactlyCoversOn Ep Fp Mp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      ∀ x, Ep x → ∃! s, G s ∧ Mp x s := by
  refine exists_congr fun G => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hcov, hdisj⟩ x hx
    obtain ⟨s, hs, hms⟩ := hcov x hx
    refine ⟨s, ⟨hs, hms⟩, fun s' hs' => ?_⟩
    by_contra hne
    exact hdisj s' s hs'.1 hs hne x hx ⟨hs'.2, hms⟩
  · intro h
    refine ⟨fun x hx => ?_, fun s s' hs hs' hne x hx => ?_⟩
    · obtain ⟨s, hs, -⟩ := h x hx
      exact ⟨s, hs⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨s₀, -, huniq⟩ := h x hx
      exact hne ((huniq s ⟨hs, h1⟩).trans (huniq s' ⟨hs', h2⟩).symm)

/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold condition can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/

section Embedding

variable [Finite A]

/-- The cover threshold as an injection of the cover into the marked set. -/
theorem coversOn_iff_embedding (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) :
    CoversOn Ep Fp Mp Kp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧ Nonempty ({s // G s} ↪ {x // Kp x}) :=
  exists_congr fun G =>
    and_congr_right fun _ =>
      and_congr_right fun _ => (nonempty_embedding_iff_ncard_le G Kp).symm

/-- The hitting-set threshold as an injection of the hitting set into the
marked set. -/
theorem hitsOn_iff_embedding (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) :
    HitsOn Ep Fp Mp Kp ↔ ∃ H : A → Prop, (∀ x, H x → Ep x) ∧
      (∀ s, Fp s → ∃ x, H x ∧ Mp x s) ∧ Nonempty ({x // H x} ↪ {x // Kp x}) :=
  coversOn_iff_embedding _ _ _ Kp

/-- The packing threshold as an injection of the marked set into the packing:
a *lower* bound, so the injection runs the other way round. -/
theorem packsOn_iff_embedding (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) :
    PacksOn Ep Fp Mp Kp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      (∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')) ∧
      Nonempty ({x // Kp x} ↪ {s // G s}) :=
  exists_congr fun G =>
    and_congr_right fun _ =>
      and_congr_right fun _ => (nonempty_embedding_iff_ncard_le Kp G).symm

end Embedding

variable {B : Type}

/-- `CoversOn` transports along an equivalence commuting with the four
predicates. -/
theorem CoversOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CoversOn EB FB MB KB) : CoversOn EA FA MA KA := by
  obtain ⟨G, hGF, hcov, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard

private theorem symm_hUn {PB : B → Prop} {PA : A → Prop} (u : B ≃ A)
    (hP : ∀ b, PB b ↔ PA (u b)) (a : A) : PA a ↔ PB (u.symm a) := by
  rw [hP]
  simp

private theorem symm_hBin {MB : B → B → Prop} {MA : A → A → Prop} (u : B ≃ A)
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (a a' : A) :
    MA a a' ↔ MB (u.symm a) (u.symm a') := by
  rw [hM]
  simp

/-- `CoversOn` transports along an equivalence, iff version. -/
theorem CoversOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CoversOn EB FB MB KB ↔ CoversOn EA FA MA KA :=
  ⟨CoversOn.of_equiv u hE hF hM hK,
    CoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩

/-- `HitsOn` transports along an equivalence, iff version. -/
theorem HitsOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    HitsOn EB FB MB KB ↔ HitsOn EA FA MA KA :=
  CoversOn.equiv_iff u hF hE (fun b b' => hM b' b) hK

/-- `PacksOn` transports along an equivalence commuting with the four
predicates. -/
theorem PacksOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : PacksOn EB FB MB KB) : PacksOn EA FA MA KA := by
  obtain ⟨G, hGF, hdisj, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun s s' hs hs' hne x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard

/-- `ExactlyCoversOn` transports along an equivalence commuting with the three
predicates. -/
theorem ExactlyCoversOn.of_equiv (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (h : ExactlyCoversOn EB FB MB) :
    ExactlyCoversOn EA FA MA := by
  obtain ⟨G, hGF, hcov, hdisj⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_,
    fun s s' hs hs' hne x hx => ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩

/-- `ExactlyCoversOn` transports along an equivalence, iff version. -/
theorem ExactlyCoversOn.equiv_iff (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) :
    ExactlyCoversOn EB FB MB ↔ ExactlyCoversOn EA FA MA :=
  ⟨ExactlyCoversOn.of_equiv u hE hF hM,
    ExactlyCoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)⟩

/-- `PacksOn` transports along an equivalence, iff version. -/
theorem PacksOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    PacksOn EB FB MB KB ↔ PacksOn EA FA MA KA :=
  ⟨PacksOn.of_equiv u hE hF hM hK,
    PacksOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩

end Generic

/-! ### The two problems -/

section Problems

section Shorthands

variable {A : Type} [Language.setSystem.Structure A]

/-- Being a ground element in a set system. -/
def SSElem (a : A) : Prop := RelMap ssElem ![a]

/-- Being a set of the family in a set system. -/
def SSFam (a : A) : Prop := RelMap ssFam ![a]

/-- Incidence in a set system. -/
def SSMem (a b : A) : Prop := RelMap ssMem ![a, b]

/-- Markedness in a set system. -/
def SSMarked (a : A) : Prop := RelMap ssMarked ![a]

end Shorthands

variable (A : Type) [Language.setSystem.Structure A]

/-- A set system admits a cover at most as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSetCover : Prop :=
  Finite A ∧ CoversOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits a hitting set at most as large as its marked set. -/
def HasSmallHittingSet : Prop :=
  Finite A ∧ HitsOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits a packing at least as large as its marked set. -/
def HasLargeSetPacking : Prop :=
  Finite A ∧ PacksOn (SSElem (A := A)) SSFam SSMem SSMarked

/-- A set system admits an exact cover: a subfamily covering every ground
element exactly once. There is no threshold here, so no finiteness
assumption either. -/
def HasExactCover : Prop :=
  ExactlyCoversOn (SSElem (A := A)) SSFam SSMem

end Problems

/-! ### Isomorphism-invariance and the bundled problems -/

section Iso

variable {A B : Type} [Language.setSystem.Structure A] [Language.setSystem.Structure B]

private theorem ssElem_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSElem a ↔ SSElem (e a) :=
  relMap_equiv₁ e ssElem a

private theorem ssFam_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSFam a ↔ SSFam (e a) :=
  relMap_equiv₁ e ssFam a

private theorem ssMem_map (e : A ≃[Language.setSystem] B) (a b : A) :
    SSMem a b ↔ SSMem (e a) (e b) :=
  relMap_equiv₂ e ssMem a b

private theorem ssMarked_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSMarked a ↔ SSMarked (e a) :=
  relMap_equiv₁ e ssMarked a

/-- The set-cover threshold property is isomorphism-invariant. -/
theorem hasSmallSetCover_iso (e : A ≃[Language.setSystem] B) :
    HasSmallSetCover A ↔ HasSmallSetCover B :=
  and_congr e.toEquiv.finite_iff
    (CoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The hitting-set threshold property is isomorphism-invariant. -/
theorem hasSmallHittingSet_iso (e : A ≃[Language.setSystem] B) :
    HasSmallHittingSet A ↔ HasSmallHittingSet B :=
  and_congr e.toEquiv.finite_iff
    (HitsOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The set-packing threshold property is isomorphism-invariant. -/
theorem hasLargeSetPacking_iso (e : A ≃[Language.setSystem] B) :
    HasLargeSetPacking A ↔ HasLargeSetPacking B :=
  and_congr e.toEquiv.finite_iff
    (PacksOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))

/-- The exact-cover property is isomorphism-invariant. -/
theorem hasExactCover_iso (e : A ≃[Language.setSystem] B) :
    HasExactCover A ↔ HasExactCover B :=
  ExactlyCoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)

end Iso

/-- SET COVER, as a problem on set systems: is there a subfamily covering
every ground element, at most as large as the marked set? -/
def SetCover : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasSmallSetCover A inst
  iso_invariant := fun e => hasSmallSetCover_iso e

/-- HITTING SET, as a problem on set systems: is there a set of ground
elements meeting every set of the family, at most as large as the marked
set? -/
def HittingSet : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasSmallHittingSet A inst
  iso_invariant := fun e => hasSmallHittingSet_iso e

/-- SET PACKING, as a problem on set systems: is there a pairwise disjoint
subfamily at least as large as the marked set? -/
def SetPacking : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasLargeSetPacking A inst
  iso_invariant := fun e => hasLargeSetPacking_iso e

/-- EXACT COVER, as a problem on set systems: is there a subfamily covering
every ground element exactly once? The marked set plays no role – exactness
replaces the threshold. -/
def ExactCover : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasExactCover A inst
  iso_invariant := fun e => hasExactCover_iso e

end DescriptiveComplexity
