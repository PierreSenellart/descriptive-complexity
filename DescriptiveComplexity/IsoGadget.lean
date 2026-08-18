/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import Mathlib.ModelTheory.Graph

/-!
# The two marked sides of an isomorphism problem, as structures

Every problem of the GI degree says “the two marked sides of the instance are
isomorphic”, and every reduction between two such problems runs one gadget on
the pattern side and the same gadget on the host side. The reductions built so
far (`DescriptiveComplexity.Problems.DagIso`) pay for that shape twice: each
characterization lemma is stated once for the pattern side and once, verbatim,
for the host side.

This file is the first half of the cure. It reads a marked binary relation
inside a structure as a `FirstOrder.Language.graph`-structure in its own right
(`DescriptiveComplexity.sideStructure`), and shows that the semantic condition
these problems use – `DescriptiveComplexity.RelIsoOn`, a bijection of the two
marked sets preserving the relation in both directions – is exactly an
isomorphism of those two structures
(`DescriptiveComplexity.relIsoOn_iff_nonempty_sideEquiv`).

The point is what it makes statable: a gadget can then be given on *single*
graphs, where the pattern/host distinction does not exist, and its correctness
asked for in the form “`F G ≅ F H` implies `G ≅ H`” – one statement instead of
two mirrored families. The forward implication is free, an interpretation being
functorial (`DescriptiveComplexity.FOInterpretation.mapLEquiv`).

Nothing here is specific to a vocabulary: the side is given by a unary
predicate and a binary one, so the same lemmas serve
`FirstOrder.Language.twoGraphs` (`patV`/`patE`) and
`FirstOrder.Language.twoDags` (`patV`/`patArc`), whose extra relations the
isomorphism ignores.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### A marked relation as a graph -/

section Side

variable {A : Type}

/-- The marked part of a binary relation, as a structure over the language of
graphs: the universe is the marked set, and adjacency is the relation. -/
@[instance_reducible]
def sideStructure (V : A → Prop) (E : A → A → Prop) : Language.graph.Structure {x : A // V x} where
  funMap f := isEmptyElim f
  RelMap {n} r :=
    match n, r with
    | _, .adj => fun w => E (w 0).1 (w 1).1

@[simp]
theorem sideStructure_adj (V : A → Prop) (E : A → A → Prop) (x y : {x : A // V x}) :
    (sideStructure V E).RelMap Language.adj ![x, y] ↔ E x.1 y.1 :=
  Iff.rfl

/-- An isomorphism of the two sides, as structures over the language of
graphs. -/
abbrev SideEquiv (PV HV : A → Prop) (PE HE : A → A → Prop) : Type :=
  @Language.Equiv Language.graph {x : A // PV x} {y : A // HV y}
    (sideStructure PV PE) (sideStructure HV HE)

end Side

/-! ### The generic property -/

section Generic

variable {A : Type}

/-- Some map is a bijection of the `PV`-vertices onto the `HV`-vertices
carrying `PE`-edges to `HE`-edges *and back*: an isomorphism of the two marked
graphs. Compare `DescriptiveComplexity.SubgraphIsoOn`, which asks only for an
injection and only for the forward implication. -/
def RelIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    (∀ y, HV y → ∃ x, PV x ∧ f x = y) ∧
    ∀ x y, PV x → PV y → (PE x y ↔ HE (f x) (f y))

variable {B : Type}

/-- `RelIsoOn` transports along an equivalence commuting with the four
predicates. -/
theorem RelIsoOn.of_equiv (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b'))
    (h : RelIsoOn PVB HVB PEB HEB) : RelIsoOn PVA HVA PEA HEA := by
  obtain ⟨f, hmaps, hinj, hsurj, hedge⟩ := h
  refine ⟨fun a => u (f (u.symm a)), fun x hx => ?_, fun x y hx hy hxy => ?_,
    fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact (hHV (f (u.symm x))).mp (hmaps _ ((hPV (u.symm x)).mpr (by simpa using hx)))
  · have hux : u.symm x = u.symm y :=
      hinj _ _ ((hPV _).mpr (by simpa using hx)) ((hPV _).mpr (by simpa using hy))
        (u.injective hxy)
    simpa using congrArg u hux
  · obtain ⟨b, hb, hfb⟩ := hsurj (u.symm y) ((hHV (u.symm y)).mpr (by simpa using hy))
    exact ⟨u b, (hPV b).mp hb, by simp [hfb]⟩
  · have h := hedge (u.symm x) (u.symm y) ((hPV _).mpr (by simpa using hx))
      ((hPV _).mpr (by simpa using hy))
    rw [hPE, hHE] at h
    simpa using h

/-- `RelIsoOn` transports along an equivalence, iff version. -/
theorem RelIsoOn.equiv_iff (u : B ≃ A) {PVB HVB : B → Prop} {PEB HEB : B → B → Prop}
    {PVA HVA : A → Prop} {PEA HEA : A → A → Prop}
    (hPV : ∀ b, PVB b ↔ PVA (u b)) (hHV : ∀ b, HVB b ↔ HVA (u b))
    (hPE : ∀ b b', PEB b b' ↔ PEA (u b) (u b'))
    (hHE : ∀ b b', HEB b b' ↔ HEA (u b) (u b')) :
    RelIsoOn PVB HVB PEB HEB ↔ RelIsoOn PVA HVA PEA HEA :=
  ⟨RelIsoOn.of_equiv u hPV hHV hPE hHE,
    RelIsoOn.of_equiv u.symm (fun a => by rw [hPV]; simp) (fun a => by rw [hHV]; simp)
      (fun a a' => by rw [hPE]; simp) fun a a' => by rw [hHE]; simp⟩

/-- **The property is isomorphism of the two marked graphs**: a map of the
universe as in `DescriptiveComplexity.RelIsoOn` is the same thing as an
equivalence of the marked subsets carrying one adjacency relation to the
other. -/
theorem relIsoOn_iff_equiv (PV HV : A → Prop) (PE HE : A → A → Prop) :
    RelIsoOn PV HV PE HE ↔
      ∃ e : {x : A // PV x} ≃ {y : A // HV y},
        ∀ x y : {x : A // PV x}, PE x.1 y.1 ↔ HE (e x).1 (e y).1 := by
  classical
  constructor
  · rintro ⟨f, hmaps, hinj, hsurj, hedge⟩
    have hbij : Function.Bijective fun x : {x : A // PV x} => (⟨f x.1, hmaps x.1 x.2⟩ :
        {y : A // HV y}) := by
      constructor
      · exact fun x y hxy => Subtype.ext (hinj x.1 y.1 x.2 y.2 (congrArg Subtype.val hxy))
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, hfx⟩ := hsurj y hy
        exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
    exact ⟨Equiv.ofBijective _ hbij, fun x y => hedge x.1 y.1 x.2 y.2⟩
  · rintro ⟨e, hedge⟩
    refine ⟨fun x => if h : PV x then (e ⟨x, h⟩).1 else x, fun x hx => ?_,
      fun x y hx hy hxy => ?_, fun y hy => ?_, fun x y hx hy => ?_⟩
    · change HV (if h : PV x then (e ⟨x, h⟩).1 else x)
      rw [dif_pos hx]
      exact (e ⟨x, hx⟩).2
    · have hxy' : (if h : PV x then (e ⟨x, h⟩).1 else x) =
          if h : PV y then (e ⟨y, h⟩).1 else y := hxy
      rw [dif_pos hx, dif_pos hy] at hxy'
      exact congrArg Subtype.val (e.injective (Subtype.ext hxy'))
    · obtain ⟨z, hz⟩ : ∃ z : {x : A // PV x}, e z = ⟨y, hy⟩ :=
        ⟨e.symm ⟨y, hy⟩, e.apply_symm_apply _⟩
      refine ⟨z.1, z.2, ?_⟩
      change (if h : PV z.1 then (e ⟨z.1, h⟩).1 else z.1) = y
      rw [dif_pos z.2, Subtype.coe_eta, hz]
    · change PE x y ↔ HE (if h : PV x then (e ⟨x, h⟩).1 else x)
        (if h : PV y then (e ⟨y, h⟩).1 else y)
      rw [dif_pos hx, dif_pos hy]
      exact hedge ⟨x, hx⟩ ⟨y, hy⟩

end Generic

/-! ### The two sides as structures -/

section Sides

variable {A : Type}

/-- **The condition is an isomorphism of the two sides**, as structures over
the language of graphs. This is the form a gadget's correctness is stated
against: on single graphs, where no pattern/host distinction exists. -/
theorem relIsoOn_iff_nonempty_sideEquiv (PV HV : A → Prop) (PE HE : A → A → Prop) :
    RelIsoOn PV HV PE HE ↔ Nonempty (SideEquiv PV HV PE HE) := by
  let := sideStructure PV PE
  let := sideStructure HV HE
  rw [relIsoOn_iff_equiv]
  constructor
  · rintro ⟨e, hedge⟩
    exact ⟨{ toEquiv := e
             map_fun' := fun f => isEmptyElim f
             map_rel' := fun {n} r x => by
               cases r
               have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
               rw [hx]
               exact (hedge (x 0) (x 1)).symm }⟩
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, fun x y => ?_⟩
    have hcomp : (e.toFun ∘ ![x, y]) = ![e.toEquiv x, e.toEquiv y] := by
      funext i; fin_cases i <;> rfl
    have h := e.map_rel' Language.adj ![x, y]
    rw [hcomp] at h
    simpa [sideStructure] using h.symm

end Sides

end DescriptiveComplexity
