/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Encoding
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.Problems.SubgraphIso

/-!
# Subgraph Isomorphism on concrete graphs: encoding and decoding

`DescriptiveComplexity.SubgraphIso` is a problem on `FirstOrder.Language.twoGraphs`-structures.
A user starts from two concrete graphs – a pattern on `p` vertices and a host
on `h` vertices, each a finite set of directed edges – and the textbook
question, `DescriptiveComplexity.ConcreteSubgraphIsoHolds`: is there an
injective map from the pattern's vertices to the host's carrying every edge
of the pattern to an edge of the host? This file ties the two together in
both directions, with the machinery of `DescriptiveComplexity.Encoding` and
`DescriptiveComplexity.Decoding`, the way the two tutorials
(`DescriptiveComplexity.Examples.ConjunctiveQueries`,
`DescriptiveComplexity.Examples.GraphCrawling`) do for their domains.

* `DescriptiveComplexity.subgraphIsoEncoding`: the pattern's vertices to the
  left of a sum, the host's to the right, the marks reading the side and the
  two adjacency relations reading the two edge sets. The size bounds are
  discharged at construction: the universe *is* the vertex set, and an edge
  set has at most quadratically many elements.
* `DescriptiveComplexity.subgraphIsoEncoding_faithful`: the abstract problem
  computes the textbook one on every encoded instance.
* `DescriptiveComplexity.subgraphIsoDecoding`: the decoder, which needs **no
  well-formedness condition**. The semantics of `SubgraphIso` ignores the
  elements in neither mark, and never relates the pattern role and the host
  role of one element – the guessed map sends pattern vertices to host
  vertices, and a vertex may be its own image – so a structure marking an
  element as both is the same instance as one where that element is split
  in two. The decoder therefore reads *every* presented structure back:
  pattern vertices are the pattern-marked elements, host vertices the
  host-marked ones, each enumerated in order, and the edges are read off the
  tables. Contrast the crawling tutorial, where the decoder exists only on
  single-root websites, and compare `DescriptiveComplexity.bwDecoding`, the
  other decoder of the library whose condition is `⊤`.

Both directions go through one lemma,
`DescriptiveComplexity.subgraphIsoOn_iff_concrete`: against an enumeration of
the pattern vertices and one of the host vertices, the generic property
`DescriptiveComplexity.SubgraphIsoOn` *is* the textbook predicate. The encoding
enumerates them by the two injections of the sum, the decoding by
`Finset.orderIsoOfFin` on the two marked sets.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The concrete problem -/

/-- A concrete instance of Subgraph Isomorphism: a pattern graph on
`Fin pat` and a host graph on `Fin host`, each given by its set of directed
edges. -/
structure SubgraphIsoInstance where
  /-- The number of pattern vertices. -/
  pat : ℕ
  /-- The number of host vertices. -/
  host : ℕ
  /-- The edges of the pattern. -/
  patEdges : Finset (Fin pat × Fin pat)
  /-- The edges of the host. -/
  hostEdges : Finset (Fin host × Fin host)
  deriving DecidableEq

/-- The textbook size of a concrete instance: vertices and edges of both
graphs. The one audited line of the encoding. -/
def sgSize (i : SubgraphIsoInstance) : ℕ :=
  i.pat + i.host + i.patEdges.card + i.hostEdges.card

/-- The textbook semantics of a concrete instance: an injective map from the
pattern's vertices to the host's carrying every edge of the pattern to an
edge of the host. -/
def ConcreteSubgraphIsoHolds (i : SubgraphIsoInstance) : Prop :=
  ∃ f : Fin i.pat → Fin i.host, Function.Injective f ∧
    ∀ a b, (a, b) ∈ i.patEdges → (f a, f b) ∈ i.hostEdges

/-! ### The generic property, against enumerations of the two vertex sets -/

section Generic

variable {A : Type}

/-- `SubgraphIsoOn` as an injective map between the two *subtypes*: the
guessed map of the definition, restricted to the pattern, and back. -/
theorem subgraphIsoOn_iff_subtype (PV HV : A → Prop) (PE HE : A → A → Prop) :
    SubgraphIsoOn PV HV PE HE ↔
      ∃ f : {x // PV x} → {y // HV y}, Function.Injective f ∧
        ∀ x y, PE x.1 y.1 → HE (f x).1 (f y).1 := by
  classical
  constructor
  · rintro ⟨g, hmaps, hinj, hedge⟩
    refine ⟨fun x => ⟨g x.1, hmaps x.1 x.2⟩, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · exact Subtype.ext (hinj x.1 y.1 x.2 y.2 (congrArg Subtype.val hxy))
    · exact hedge x.1 y.1 x.2 y.2 hxy
  · rintro ⟨f, hinj, hedge⟩
    refine ⟨fun x => if h : PV x then (f ⟨x, h⟩).1 else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun x y hx hy hxy => ?_⟩
    · simp only [dif_pos hx]
      exact (f ⟨x, hx⟩).2
    · simp only [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (hinj (Subtype.ext hxy))
    · simp only [dif_pos hx, dif_pos hy]
      exact hedge ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- **The generic property is the textbook predicate**, once the pattern and
host vertices are enumerated (`eP`, `eH`) and the two edge sets are read
through the enumerations (`hEP`, `hEH`). The encoding and the decoding below
each supply one pair of enumerations. -/
theorem subgraphIsoOn_iff_concrete (i : SubgraphIsoInstance) (PV HV : A → Prop)
    (PE HE : A → A → Prop) (eP : Fin i.pat ≃ {x // PV x}) (eH : Fin i.host ≃ {y // HV y})
    (hEP : ∀ a b, (a, b) ∈ i.patEdges ↔ PE (eP a).1 (eP b).1)
    (hEH : ∀ a b, (a, b) ∈ i.hostEdges ↔ HE (eH a).1 (eH b).1) :
    ConcreteSubgraphIsoHolds i ↔ SubgraphIsoOn PV HV PE HE := by
  rw [subgraphIsoOn_iff_subtype]
  constructor
  · rintro ⟨f, hinj, hedge⟩
    refine ⟨fun x => eH (f (eP.symm x)), fun x y hxy => ?_, fun x y hxy => ?_⟩
    · exact eP.symm.injective (hinj (eH.injective hxy))
    · exact (hEH _ _).mp (hedge (eP.symm x) (eP.symm y) ((hEP _ _).mpr (by simpa using hxy)))
  · rintro ⟨f, hinj, hedge⟩
    refine ⟨fun a => eH.symm (f (eP a)), fun a b hab => ?_, fun a b hab => ?_⟩
    · exact eP.injective (hinj (eH.symm.injective hab))
    · rw [hEH]
      simpa using hedge (eP a) (eP b) ((hEP a b).mp hab)

end Generic

/-! ### The encoding -/

/-- The encoder, standalone and auditable: a plain `def`, so the compiler
vouches that it computes. Pattern vertices are the left injections, host
vertices the right ones, and the two adjacency relations decide membership in
the two edge sets on their own side. -/
def sgRelBool (i : SubgraphIsoInstance) {n : ℕ} (R : Language.twoGraphs.Relations n) :
    (Fin n → (Fin i.pat ⊕ Fin i.host)) → Bool :=
  match n, R with
  | _, .patV => fun x => (x 0).isLeft
  | _, .hostV => fun x => (x 0).isRight
  | _, .patE => fun x =>
    match x 0, x 1 with
    | Sum.inl a, Sum.inl b => decide ((a, b) ∈ i.patEdges)
    | _, _ => false
  | _, .hostE => fun x =>
    match x 0, x 1 with
    | Sum.inr a, Sum.inr b => decide ((a, b) ∈ i.hostEdges)
    | _, _ => false

/-- The encoding of concrete instances by `Language.twoGraphs`-structures:
universe `Fin pat ⊕ Fin host`, relations by `sgRelBool`. The universe is the
vertex set, so nothing is padded, and an edge set has at most quadratically
many elements, so nothing is compressed. -/
def subgraphIsoEncoding : Encoding Language.twoGraphs SubgraphIsoInstance where
  size := sgSize
  Univ := fun i => Fin i.pat ⊕ Fin i.host
  deceq := fun _ => inferInstance
  fintype := fun _ => inferInstance
  relBool := fun i {n} R => sgRelBool i R
  card_le := Encoding.linear_bound (c := 1) fun i => by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, sgSize]
    omega
  le_card := ⟨2, 2, fun i => by
    have hP : i.patEdges.card ≤ i.pat * i.pat := by
      simpa [Fintype.card_prod, Fintype.card_fin] using i.patEdges.card_le_univ
    have hH : i.hostEdges.card ≤ i.host * i.host := by
      simpa [Fintype.card_prod, Fintype.card_fin] using i.hostEdges.card_le_univ
    simp only [sgSize, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    nlinarith⟩

section Faithful

variable (i : SubgraphIsoInstance)

/-- On an encoded instance, being a pattern vertex is being a left injection. -/
theorem sgEnc_patV (x : subgraphIsoEncoding.Univ i) : TGPatV x ↔ x.isLeft = true :=
  Iff.rfl

/-- On an encoded instance, being a host vertex is being a right injection. -/
theorem sgEnc_hostV (x : subgraphIsoEncoding.Univ i) : TGHostV x ↔ x.isRight = true :=
  Iff.rfl

/-- Pattern adjacency on an encoded instance, at two left injections. -/
theorem sgEnc_patE (a b : Fin i.pat) :
    TGPatE (A := subgraphIsoEncoding.Univ i) (Sum.inl a) (Sum.inl b) ↔ (a, b) ∈ i.patEdges :=
  decide_eq_true_iff

/-- Host adjacency on an encoded instance, at two right injections. -/
theorem sgEnc_hostE (a b : Fin i.host) :
    TGHostE (A := subgraphIsoEncoding.Univ i) (Sum.inr a) (Sum.inr b) ↔ (a, b) ∈ i.hostEdges :=
  decide_eq_true_iff

/-- The pattern vertices of an encoded instance, enumerated by the left
injection. -/
def sgEncPatEquiv : Fin i.pat ≃ {x : subgraphIsoEncoding.Univ i // TGPatV x} where
  toFun a := ⟨Sum.inl a, rfl⟩
  invFun x := x.1.getLeft ((sgEnc_patV i x.1).mp x.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨(a | b), hx⟩
    · rfl
    · exact absurd ((sgEnc_patV i _).mp hx) Bool.false_ne_true

/-- The host vertices of an encoded instance, enumerated by the right
injection. -/
def sgEncHostEquiv : Fin i.host ≃ {y : subgraphIsoEncoding.Univ i // TGHostV y} where
  toFun b := ⟨Sum.inr b, rfl⟩
  invFun y := y.1.getRight ((sgEnc_hostV i y.1).mp y.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨(a | b), hy⟩
    · exact absurd ((sgEnc_hostV i _).mp hy) Bool.false_ne_true
    · rfl

/-- **The encoding is faithful**: `SubgraphIso` computes the textbook
predicate on every encoded instance. -/
theorem subgraphIsoEncoding_faithful :
    subgraphIsoEncoding.Faithful ConcreteSubgraphIsoHolds SubgraphIso := by
  intro i
  change ConcreteSubgraphIsoHolds i ↔ HasSubgraphIso (subgraphIsoEncoding.Univ i)
  rw [HasSubgraphIso, and_iff_right (inferInstance : Finite (subgraphIsoEncoding.Univ i))]
  exact subgraphIsoOn_iff_concrete i _ _ _ _ (sgEncPatEquiv i) (sgEncHostEquiv i)
    (fun a b => (sgEnc_patE i a b).symm) fun a b => (sgEnc_hostE i a b).symm

end Faithful

/-! ### A worked instance, run -/

/-- A concrete instance: the directed triangle as pattern, the complete
directed graph on four vertices as host. -/
def sgExample : SubgraphIsoInstance :=
  ⟨3, 4, {(0, 1), (1, 2), (2, 0)}, Finset.univ.filter fun q => q.1 ≠ q.2⟩

/-- The triangle embeds in the complete graph, by the identity on the first
three vertices. -/
example : ConcreteSubgraphIsoHolds sgExample :=
  ⟨Fin.castLE (by decide), Fin.castLE_injective _, by decide⟩

/-- … and, through the faithfulness theorem, its encoded structure is a
yes-instance of the abstract problem. -/
example : SubgraphIso (subgraphIsoEncoding.Univ sgExample) :=
  (subgraphIsoEncoding_faithful sgExample).mp
    ⟨Fin.castLE (by decide), Fin.castLE_injective _, by decide⟩

section
set_option linter.hashCommand false

#guard subgraphIsoEncoding.relBool sgExample tgPatV (![Sum.inl 0] : Fin 1 → Fin 3 ⊕ Fin 4)
#guard !subgraphIsoEncoding.relBool sgExample tgPatV (![Sum.inr 0] : Fin 1 → Fin 3 ⊕ Fin 4)
#guard subgraphIsoEncoding.relBool sgExample tgPatE
  (![Sum.inl 2, Sum.inl 0] : Fin 2 → Fin 3 ⊕ Fin 4)
#guard !subgraphIsoEncoding.relBool sgExample tgPatE
  (![Sum.inl 0, Sum.inl 2] : Fin 2 → Fin 3 ⊕ Fin 4)
#guard subgraphIsoEncoding.relBool sgExample tgHostE
  (![Sum.inr 0, Sum.inr 3] : Fin 2 → Fin 3 ⊕ Fin 4)
#guard !subgraphIsoEncoding.relBool sgExample tgHostE
  (![Sum.inr 3, Sum.inr 3] : Fin 2 → Fin 3 ⊕ Fin 4)

end

/-! ### The decoding -/

section Decoder

variable (S : FinPresentation Language.twoGraphs)

/-- The pattern vertices of a presented structure. -/
def sgPatVs : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool tgPatV ![x]

/-- The host vertices of a presented structure. -/
def sgHostVs : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool tgHostV ![x]

theorem mem_sgPatVs (x : Fin S.card) : x ∈ sgPatVs S ↔ TGPatV x := by
  simp [sgPatVs, TGPatV]

theorem mem_sgHostVs (x : Fin S.card) : x ∈ sgHostVs S ↔ TGHostV x := by
  simp [sgHostVs, TGHostV]

/-- The decoder: enumerate the pattern vertices and the host vertices, in
order, and read the two edge sets off the tables through the enumerations.
Total: every presented structure is an instance. -/
def sgDecode : Option SubgraphIsoInstance :=
  some ⟨(sgPatVs S).card, (sgHostVs S).card,
    Finset.univ.filter fun q => S.relBool tgPatE
      ![(sgPatVs S).orderEmbOfFin rfl q.1, (sgPatVs S).orderEmbOfFin rfl q.2],
    Finset.univ.filter fun q => S.relBool tgHostE
      ![(sgHostVs S).orderEmbOfFin rfl q.1, (sgHostVs S).orderEmbOfFin rfl q.2]⟩

/-- The pattern vertices of a presented structure, enumerated in order. -/
noncomputable def sgDecPatEquiv : Fin (sgPatVs S).card ≃ {x : Fin S.card // TGPatV x} :=
  ((sgPatVs S).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (mem_sgPatVs S))

/-- The host vertices of a presented structure, enumerated in order. -/
noncomputable def sgDecHostEquiv : Fin (sgHostVs S).card ≃ {y : Fin S.card // TGHostV y} :=
  ((sgHostVs S).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (mem_sgHostVs S))

theorem sgDecode_sound (i : SubgraphIsoInstance) (hi : i ∈ sgDecode S) :
    ConcreteSubgraphIsoHolds i ↔ SubgraphIso (Fin S.card) := by
  rw [Option.mem_def, sgDecode, Option.some.injEq] at hi
  subst hi
  change _ ↔ HasSubgraphIso (Fin S.card)
  rw [HasSubgraphIso, and_iff_right (inferInstance : Finite (Fin S.card))]
  refine subgraphIsoOn_iff_concrete _ _ _ _ _ (sgDecPatEquiv S) (sgDecHostEquiv S)
    (fun a b => ?_) fun a b => ?_
  · simp [sgDecPatEquiv, TGPatE, Finset.coe_orderIsoOfFin_apply]
  · simp [sgDecHostEquiv, TGHostE, Finset.coe_orderIsoOfFin_apply]

theorem sgDecode_total (_hpos : 0 < S.card)
    (_hW : DecisionProblem.ofSentence (⊤ : Language.twoGraphs.Sentence) (Fin S.card)) :
    (sgDecode S).isSome :=
  rfl

end Decoder

/-- **The computable decoding of presented structures**, with no
well-formedness condition. Together with `subgraphIsoEncoding_faithful` it
closes the loop: encoded instances are equidecided, and *every* nonempty
finite structure decodes to an equidecided concrete instance, so
`SubgraphIso` is nowhere hard only on junk. -/
def subgraphIsoDecoding : Decoding Language.twoGraphs (DecisionProblem.ofSentence ⊤)
    ConcreteSubgraphIsoHolds SubgraphIso where
  dec := sgDecode
  sound := sgDecode_sound
  total := sgDecode_total

/-- A presented four-element structure: element `0` a pattern vertex, `1`
and `2` host vertices, `3` in both roles, with the pattern edge `0 → 3` and
the host edges `3 → 1` and `1 → 2`. The decoder *runs* on it: the pattern has
two vertices and one edge, the host three vertices and two edges. -/
def sgPres : FinPresentation Language.twoGraphs where
  card := 4
  relBool := fun {n} R =>
    match n, R with
    | _, .patV => fun x => x 0 == 0 || x 0 == 3
    | _, .hostV => fun x => x 0 != 0
    | _, .patE => fun x => x 0 == 0 && x 1 == 3
    | _, .hostE => fun x => (x 0 == 3 && x 1 == 1) || (x 0 == 1 && x 1 == 2)

section
set_option linter.hashCommand false

#guard ((sgDecode sgPres).map fun i => i.pat) = some 2
#guard ((sgDecode sgPres).map fun i => i.host) = some 3
#guard ((sgDecode sgPres).map fun i => i.patEdges.card) = some 1
#guard ((sgDecode sgPres).map fun i => i.hostEdges.card) = some 2

end

/-- **Hardness reads back to concrete data**: every nonempty finite
`twoGraphs`-structure is decided by `SubgraphIso` exactly as some pair of
concrete graphs is by the textbook predicate. -/
theorem exists_concreteSubgraphIso_iff (A : Type) [Language.twoGraphs.Structure A]
    [Finite A] [Nonempty A] : ∃ i, ConcreteSubgraphIsoHolds i ↔ SubgraphIso A :=
  subgraphIsoDecoding.exists_conc_iff A (by simp)

end DescriptiveComplexity
