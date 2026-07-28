/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.Encoding

/-!
# Well-formed instances and computable decodings

The decoding direction of an encoding (`DescriptiveComplexity.Encoding`):
membership results transfer to the concrete problem along a faithful encoding
for free, but reading a *hardness* theorem back to concrete data needs a
converse – the abstract problem must not be hard only on junk structures the
encoding never produces. This file makes that converse checkable, in two
independent, composable pieces designed to keep the user-facing work minimal.

**Well-formedness is a decision problem.** The junk-free structures are cut
out by an isomorphism-invariant property `W` – typically a plain first-order
sentence, bundled by `DescriptiveComplexity.DecisionProblem.ofSentence` so that
invariance comes for free. Hardness *on well-formed instances* then needs no
new framework at all: it is ordinary hardness of the conjunction `W ⊓ P`
(pointwise `∧`, the `Min` instance below), and the library's existing
machinery applies to it unchanged. A user upgrades an existing completeness
proof with two one-liners:

* **hardness**: a reduction into `P` whose images are all well-formed is a
  reduction into `W ⊓ P` –
  `DescriptiveComplexity.FOReduction.withInvariant` /
  `DescriptiveComplexity.OrderedFOReduction.withInvariant` turn the existing
  reduction plus an image lemma into the strengthened one;
* **membership**: `DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`
  conjoins the sentence `W` into the existing `Σ₁` kernel.

The choice of `W` is self-policing: chosen too narrow, the hardness reduction
cannot land in it; chosen too wide, the decoding below cannot handle it.
Both failure modes are proofs that do not close, never silent unsoundness.

**Decodings are computations.** The lesson of
`DescriptiveComplexity.Encoding.CoversUpTo`'s removal is that an *existential*
decoding statement (`∀ A, ∃ i, Conc i ↔ P A`) is classically near-vacuous:
casing on `P A` discharges it with no decoding whatsoever, whenever the
concrete type has one yes- and one no-instance. The honest content is a
*function*, so `DescriptiveComplexity.Decoding` bundles one, with the same
computability hygiene as encoders: a plain `def`

* `dec : FinPresentation L → Option ι` – from concretely presented finite
  structures (`DescriptiveComplexity.FinPresentation`: a size and a `Bool`-valued
  relation table) to concrete instances, `none` *being* the junk case, so no
  proof-carrying arguments and no partiality tricks;
* `sound` – whatever `dec` returns is decided by `Conc` exactly as the
  presented structure is by `P`;
* `total` – on well-formed (nonempty) presentations, `dec` returns something.

Because `dec` is `Option`-valued and computable, it can be *run*: `#guard`s
can test a decoder on small presentations exactly as they test encoders, and
the compiler rejects a decoder whose data decides an undecidable predicate.
The residual gap is also the same as for encoders: computability is enforced,
a *complexity bound* is not (a decoder may brute-force the answer); that
would need the machine bridge (`ROADMAP.md` §7).

The `Prop`-level consequence – every well-formed finite structure is
semantically a concrete instance – is
`DescriptiveComplexity.Decoding.exists_conc_iff`; unlike its removed
predecessor it cannot be established by classical casing, because it is
derived from the bundled function.

Worked decoders are in the two tutorials
(`DescriptiveComplexity.Examples.ConjunctiveQueries`,
`DescriptiveComplexity.Examples.GraphCrawling`); the crawling one exists only
thanks to well-formedness – on structures marking several roots no honest
decoder can choose without computing reachability, and `W` (“exactly one
root”) is what removes them.

## Main declarations

* `DescriptiveComplexity.DecisionProblem.ofSentence`: a first-order sentence
  as a decision problem, the usual shape of a well-formedness condition;
* the `Min` instance on `DescriptiveComplexity.DecisionProblem`, giving the
  restriction `W ⊓ P`;
* `DescriptiveComplexity.FOReduction.withInvariant` and
  `DescriptiveComplexity.OrderedFOReduction.withInvariant`: strengthen a
  reduction's target by an invariant its images satisfy;
* `DescriptiveComplexity.SigmaSODefinable.inf_ofSentence`: conjoin a
  first-order sentence into a `Σₖ` definition;
* `DescriptiveComplexity.Encoding.Faithful.inf`: encoded instances that are
  well-formed are faithful for the restricted problem;
* `DescriptiveComplexity.FinPresentation` and `DescriptiveComplexity.Decoding`:
  concretely presented structures and computable decodings, with
  `DescriptiveComplexity.Decoding.exists_conc_iff` as the `Prop`-level
  consequence.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Well-formedness as a decision problem -/

/-- The conjunction of two decision problems: a structure is a yes-instance
when it is one of both. Written `W ⊓ P` (through the `Min` instance below);
with `W` a well-formedness condition, `W ⊓ P` is “`P`, on well-formed
instances”. -/
protected def DecisionProblem.and (W P : DecisionProblem L) : DecisionProblem L where
  Holds := fun A inst => @DecisionProblem.Holds L W A inst ∧ @DecisionProblem.Holds L P A inst
  iso_invariant := fun e => and_congr (W.iso_invariant e) (P.iso_invariant e)

instance : Min (DecisionProblem L) :=
  ⟨DecisionProblem.and⟩

@[simp]
theorem DecisionProblem.min_holds (W P : DecisionProblem L) (A : Type) [L.Structure A] :
    (W ⊓ P) A ↔ W A ∧ P A :=
  Iff.rfl

/-- A first-order sentence, read as a decision problem: the structures
satisfying it. Isomorphism-invariance is automatic, which makes this the
cheapest way to state a well-formedness condition `W`. -/
protected def DecisionProblem.ofSentence (ψ : L.Sentence) : DecisionProblem L where
  Holds := fun A inst => @Sentence.Realize L A inst ψ
  iso_invariant := fun e => StrongHomClass.realize_sentence e ψ

@[simp]
theorem DecisionProblem.ofSentence_holds (ψ : L.Sentence) (A : Type) [L.Structure A] :
    DecisionProblem.ofSentence ψ A ↔ A ⊨ ψ :=
  Iff.rfl

/-! ### Reductions with an image invariant

A reduction into `P` whose images all satisfy `W` is a reduction into
`W ⊓ P` – so hardness of the restricted problem costs one image lemma on top
of the reduction already at hand. Only the *last* hop of a reduction chain
needs the lemma: composing any further reduction in front leaves the images
unchanged. -/

variable {L' : Language.{0, 0}} [L'.IsRelational]

/-- Strengthen the target of a reduction by an invariant its images satisfy. -/
def FOReduction.withInvariant {P : DecisionProblem L} {Q : DecisionProblem L'}
    (f : P ≤ᶠᵒ Q) (W : DecisionProblem L')
    (h : ∀ (A : Type) [L.Structure A] [Nonempty A], W (f.toInterpretation.Map A)) :
    P ≤ᶠᵒ (W ⊓ Q) :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => (f.correct A).trans ⟨fun hq => ⟨h A, hq⟩, And.right⟩ }

/-- Strengthen the target of an ordered reduction by an invariant its images
satisfy. -/
def OrderedFOReduction.withInvariant {P : DecisionProblem L} {Q : DecisionProblem L'}
    (f : P ≤ᶠᵒ[≤] Q) (W : DecisionProblem L')
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      W (f.toInterpretation.Map A)) :
    P ≤ᶠᵒ[≤] (W ⊓ Q) :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => (f.correct A).trans ⟨fun hq => ⟨h A, hq⟩, And.right⟩ }

/-! ### Conjoining a sentence into a second-order definition -/

instance (B : SOBlock) (A : Type) : Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

/-- A sentence of the base language, lifted to the language of a kernel: the
symbols are unchanged, only their address in the iterated sum grows. -/
def soLift : ∀ {L : Language.{0, 0}} (Bs : List SOBlock),
    L.Sentence → (soLang L Bs).Sentence
  | _, [], ψ => ψ
  | _, _ :: Bs, ψ => soLift Bs (LHom.sumInl.onSentence ψ)

/-- Realization of a lifted sentence conjoined into a kernel: the lifted
conjunct does not mention the quantified relation variables, so it pulls out
of the second-order quantifiers. -/
private theorem sorealize_soLift_inf :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (inst : L.Structure A)
      (ψ : L.Sentence) (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A inst Bs (soLift Bs ψ ⊓ φ) pol ↔
        (@Sentence.Realize L A inst ψ ∧ @SORealize L A inst Bs φ pol)
  | [], L, A, inst, ψ, φ, pol => by
    change @Sentence.Realize L A inst (ψ ⊓ φ) ↔ _
    exact Formula.realize_inf
  | B :: Bs, L, A, inst, ψ, φ, pol => by
    have hψ : ∀ ρ : B.Assignment A,
        @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
            (LHom.sumInl.onSentence ψ) ↔
          @Sentence.Realize L A inst ψ := fun ρ => by
      letI := B.structure ρ
      exact LHom.sumInl.realize_onSentence (M := A) ψ
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, hρ⟩
        obtain ⟨h1, h2⟩ := (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ false).mp hρ
        exact ⟨(hψ ρ).mp h1, ρ, h2⟩
      · rintro ⟨h1, ρ, h2⟩
        exact ⟨ρ, (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ false).mpr
            ⟨(hψ ρ).mpr h1, h2⟩⟩
    | false =>
      constructor
      · intro h
        obtain ⟨ρ₀⟩ : Nonempty (B.Assignment A) := inferInstance
        refine ⟨(hψ ρ₀).mp ((sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ₀)) _ φ true).mp (h ρ₀)).1,
          fun ρ => ((sorealize_soLift_inf Bs (L.sum B.lang) A
            (@sumStructure L B.lang A inst (B.structure ρ)) _ φ true).mp (h ρ)).2⟩
      · rintro ⟨h1, h2⟩ ρ
        exact (sorealize_soLift_inf Bs (L.sum B.lang) A
          (@sumStructure L B.lang A inst (B.structure ρ)) _ φ true).mpr
            ⟨(hψ ρ).mpr h1, h2 ρ⟩

/-- **Conjoining a first-order sentence preserves `Σₖ`-definability**: the
sentence joins the kernel, lifted along the block languages. This is the
membership half of restricting a problem to its well-formed instances. -/
theorem SigmaSODefinable.inf_ofSentence {k : ℕ} {P : DecisionProblem L}
    (h : SigmaSODefinable k P) (ψ : L.Sentence) :
    SigmaSODefinable k (DecisionProblem.ofSentence ψ ⊓ P) := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  refine ⟨Bs, hlen, soLift Bs ψ ⊓ φ, ?_⟩
  intro A inst _ _
  exact (and_congr Iff.rfl (hφ A)).trans
    (sorealize_soLift_inf Bs L A inst ψ φ true).symm

/-! ### Faithfulness for the restricted problem -/

/-- A faithful encoding whose images are all well-formed is faithful for the
restricted problem: the completeness theorem for `W ⊓ P` reads back to the
same concrete predicate. -/
theorem Encoding.Faithful.inf [L.IsRelational] {ι : Type*} {e : Encoding L ι}
    {Conc : ι → Prop} {P : DecisionProblem L} (hf : e.Faithful Conc P)
    (W : DecisionProblem L) (hW : ∀ i, W (e.Univ i)) : e.Faithful Conc (W ⊓ P) :=
  fun i => (hf i).trans ⟨fun hp => ⟨hW i, hp⟩, And.right⟩

/-! ### Concretely presented structures and computable decodings -/

/-- A concretely presented finite `L`-structure: a size and a computable
relation table. This is the input type of decoders – the “raw bytes” a
decoding computation reads. -/
structure FinPresentation (L : Language.{0, 0}) where
  /-- The number of elements. -/
  card : ℕ
  /-- The relations, as computations on `Fin card`. -/
  relBool : ∀ {n}, L.Relations n → (Fin n → Fin card) → Bool

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str [L.IsRelational] (S : FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

@[simp]
theorem FinPresentation.relMap_iff [L.IsRelational] (S : FinPresentation L) {n}
    (R : L.Relations n) (x : Fin n → Fin S.card) :
    RelMap R x ↔ S.relBool R x = true :=
  Iff.rfl

open Classical in
/-- Any nonempty finite structure, presented concretely (classically: the
presentation decides the relations by choice, which is fine for the
`Prop`-level transport below – actual decoders never see it). -/
noncomputable def FinPresentation.ofStructure (A : Type) [L.Structure A] [Fintype A] :
    FinPresentation L :=
  ⟨Fintype.card A, fun {_} R x => decide (RelMap R fun j => (Fintype.equivFin A).symm (x j))⟩

open Classical in
/-- The presented structure is isomorphic to the original one. -/
noncomputable def FinPresentation.equivOfStructure [L.IsRelational] (A : Type)
    [L.Structure A] [Fintype A] : A ≃[L] Fin (FinPresentation.ofStructure (L := L) A).card :=
  { toEquiv := Fintype.equivFin A
    map_fun' := fun {n} f _ => isEmptyElim f
    map_rel' := fun {n} R x => by
      change decide (RelMap R fun j => (Fintype.equivFin A).symm ((Fintype.equivFin A) (x j)))
          = true ↔ _
      rw [decide_eq_true_eq]
      simp }

/-- A computable decoding of well-formed structures into concrete instances:
the converse of an encoding, with the same hygiene. `dec` is a plain
computation from presented structures to `Option ι` – returning `none` *is*
the junk case, so there are no proof-carrying arguments and the decoder can
be run and `#guard`-tested; `sound` says decoded instances are equidecided
with the structure they came from; `total` says well-formed nonempty
presentations always decode. See the module docstring for why the bundled
function, and not a `∀∃` statement, is the meaningful notion. -/
structure Decoding (L : Language.{0, 0}) [L.IsRelational] {ι : Type*}
    (W : DecisionProblem L) (Conc : ι → Prop) (P : DecisionProblem L) where
  /-- The decoder: a computation from presented structures to concrete
  instances, `none` on junk. Keep it a plain `def`-legible field, as for
  `Encoding.relBool`. -/
  dec : FinPresentation L → Option ι
  /-- Decoded instances are decided by the concrete semantics exactly as the
  presented structure is by the abstract problem. -/
  sound : ∀ (S : FinPresentation L) (i : ι), i ∈ dec S → (Conc i ↔ P (Fin S.card))
  /-- Well-formed nonempty presentations always decode. -/
  total : ∀ S : FinPresentation L, 0 < S.card → W (Fin S.card) → (dec S).isSome

/-- **Well-formed structures are semantically concrete**: along a decoding,
every well-formed nonempty finite structure is decided by the abstract
problem exactly as some concrete instance is by the concrete semantics. This
is the honest form of the removed `Encoding.CoversUpTo` – honest because it
is derived from the bundled computation, not established by casing on
`P A`. -/
theorem Decoding.exists_conc_iff [L.IsRelational] {ι : Type*} {W : DecisionProblem L}
    {Conc : ι → Prop} {P : DecisionProblem L} (d : Decoding L W Conc P)
    (A : Type) [L.Structure A] [Finite A] [Nonempty A] (hW : W A) :
    ∃ i, Conc i ↔ P A := by
  haveI : Fintype A := Fintype.ofFinite A
  have g := FinPresentation.equivOfStructure (L := L) A
  have hW' : W (Fin (FinPresentation.ofStructure (L := L) A).card) :=
    (W.iso_invariant g).mp hW
  have hpos : 0 < (FinPresentation.ofStructure (L := L) A).card := Fintype.card_pos
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (d.total (FinPresentation.ofStructure (L := L) A) hpos hW')
  exact ⟨i, (d.sound _ i hi).trans (P.iso_invariant g).symm⟩

end DescriptiveComplexity
