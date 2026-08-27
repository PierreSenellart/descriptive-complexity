/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureParam
import DescriptiveComplexity.FixedPointStepRel

/-!
# Pulling a walk back through a relativized interpretation

A walk on the structure an interpretation produces is a walk on the base
structure: its tuples become tuples of coordinates, and the tags of its points
– being finite, static data – are carried in the mode
(`DescriptiveComplexity.ParamTCSpec.comapRel`). This is
`DescriptiveComplexity.TCSpec.comap` of
`DescriptiveComplexity.TransitiveClosurePull` with the two features a reduction
notion needs added: **parameters**, so that what is pulled back is a relation
rather than a sentence, and a **definable domain**, so that the interpretation
may be relativized.

## What the domain costs

Over the whole universe the encoding of nodes is a bijection and the transfer
is an isomorphism of walks. Over a definable domain it is not: a tagged tuple
of the base need not be a point of the target at all. The pulled walk is
therefore *guarded* – its step formula asks both endpoints to be in the domain
(`DescriptiveComplexity.ParamTCSpec.domTupleF`) – so that it never leaves the
image of the encoding, and the correspondence
(`DescriptiveComplexity.ParamTCSpec.reachAt_comapRel_iff`) is stated between
in-domain nodes, which is where the formulas that read it evaluate it: the
guarded pullback of `DescriptiveComplexity.RelComposition` hands every atom its
arguments already in the domain.

## What it is for

Two things. It is what pulls a membership walk back through a reduction
(`DescriptiveComplexity.TCSpec.pullSpec`), the first half of the closure of
`DescriptiveComplexity.NL` under `≤ᵗᶜ`, the second half being the flattening
of the pulled walk (`DescriptiveComplexity.TransitiveClosureFlatten`); and it
is what pulls the *outer* walks of a composite back to the base, the first
half of transitivity of `≤ᵗᶜ` (`DescriptiveComplexity.TCReduction.trans`),
whose second half is the same flattening.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dim : ℕ}

/-! ### The guarded pullback at an arbitrary variable type -/

section PullRelF

variable {β : Type}

/-- The guarded pullback of a formula at an arbitrary variable type: the
relativized sibling of `DescriptiveComplexity.FOInterpretation.pullF`. -/
noncomputable def RelFOInterpretation.pullRelF (I : RelFOInterpretation L₁ L₂ Tag dim)
    (φ : L₂.Formula β) (τ : β → Tag) : L₁.Formula (β × Fin dim) :=
  (I.pullRel (φ : L₂.BoundedFormula β 0) (Sum.elim τ finZeroElim)).relabel
    fun p => (Sum.elim id finZeroElim p.1, p.2)

theorem RelFOInterpretation.realize_pullRelF (I : RelFOInterpretation L₁ L₂ Tag dim)
    {A : Type} [L₁.Structure A] (φ : L₂.Formula β) (τ : β → Tag) (v : β × Fin dim → A)
    (hv : ∀ b, (I.domFormula (τ b)).Realize fun j => v (b, j)) :
    (I.pullRelF φ τ).Realize v ↔
      φ.Realize (M := I.MapRel A) fun b => ⟨(τ b, fun j => v (b, j)), hv b⟩ := by
  have hv' : ∀ b : β ⊕ Fin 0,
      (I.domFormula (Sum.elim τ finZeroElim b)).Realize fun j =>
        (v ∘ fun p : (β ⊕ Fin 0) × Fin dim =>
          (Sum.elim id finZeroElim p.1, p.2)) (b, j) := by
    rintro (b | z)
    · exact hv b
    · exact z.elim0
  rw [RelFOInterpretation.pullRelF, Formula.realize_relabel,
    I.realize_pullRel (φ : L₂.BoundedFormula β 0) (Sum.elim τ finZeroElim) _ hv']
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.MapRel A) (φ : L₂.BoundedFormula β 0) a b)
    (funext fun b => rfl) (Subsingleton.elim _ _))

end PullRelF

namespace ParamTCSpec

/-! ### Coordinates of a pulled node -/

section Coordinates

variable (s : ParamTCSpec L₂) (dim)

/-- The coordinate of a pulled tuple holding the `j`-th coordinate of the
`i`-th point. -/
def coordIx {n : ℕ} (i : Fin n) (j : Fin dim) : Fin (n * dim) :=
  finProdFinEquiv (i, j)

variable {s dim}

/-- The point of the target a pulled tuple encodes at its `i`-th slot. -/
def pointOf {A : Type} {n : ℕ} (τ : Fin n → Tag) (w : Fin (n * dim) → A) (i : Fin n) :
    Tag × (Fin dim → A) :=
  (τ i, fun j => w (coordIx dim i j))

end Coordinates

/-! ### The pulled walk -/

section Comap

variable (s : ParamTCSpec L₂) (I : RelFOInterpretation L₁ L₂ Tag dim)

open Classical in
/-- “Every point this tuple encodes is in the domain”, as a formula. -/
noncomputable def domTupleF {n : ℕ} (τ : Fin n → Tag) : L₁.Formula (Fin (n * dim)) :=
  Formula.iInf fun i : Fin n =>
    (I.domFormula (τ i)).relabel fun j => coordIx dim i j

omit [L₂.IsRelational] [Finite Tag] in
theorem realize_domTupleF {A : Type} [L₁.Structure A] {n : ℕ} (τ : Fin n → Tag)
    (w : Fin (n * dim) → A) :
    (domTupleF I τ).Realize w ↔
      ∀ i, (I.domFormula (τ i)).Realize fun j => w (coordIx dim i j) := by
  classical
  rw [domTupleF, Formula.realize_iInf]
  exact forall_congr' fun i => Formula.realize_relabel

/-- The variables of a pulled step formula: the two tuples and the
parameters, each spread over its coordinates. -/
def comapVar :
    (((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) × Fin dim) →
      ((Fin (s.k * dim) ⊕ Fin (s.k * dim)) ⊕ Fin (s.par * dim))
  | (Sum.inl (Sum.inl i), j) => Sum.inl (Sum.inl (coordIx dim i j))
  | (Sum.inl (Sum.inr i), j) => Sum.inl (Sum.inr (coordIx dim i j))
  | (Sum.inr i, j) => Sum.inr (coordIx dim i j)

/-- The relabelling of a guard on one tuple into the step formula's
variables. -/
def comapSrcVar : Fin (s.k * dim) → ((Fin (s.k * dim) ⊕ Fin (s.k * dim)) ⊕ Fin (s.par * dim)) :=
  fun m => Sum.inl (Sum.inl m)

@[inherit_doc comapSrcVar]
def comapTgtVar : Fin (s.k * dim) → ((Fin (s.k * dim) ⊕ Fin (s.k * dim)) ⊕ Fin (s.par * dim)) :=
  fun m => Sum.inl (Sum.inr m)

@[inherit_doc comapSrcVar]
def comapParVar :
    Fin (s.par * dim) → ((Fin (s.k * dim) ⊕ Fin (s.k * dim)) ⊕ Fin (s.par * dim)) :=
  Sum.inr

/-- **The pullback of a walk through a relativized interpretation**, at a
static assignment of tags to its parameters: the tuples become tuples of
coordinates, the tags of the two endpoints are carried in the mode, and the
step is guarded by the domain formulas of everything it mentions. -/
noncomputable def comapRel (τp : Fin s.par → Tag) : ParamTCSpec L₁ where
  Mode := s.Mode × (Fin s.k → Tag)
  k := s.k * dim
  par := s.par * dim
  step := fun m n =>
    ((domTupleF I m.2).relabel (comapSrcVar s) ⊓
        (domTupleF I n.2).relabel (comapTgtVar s)) ⊓
      ((domTupleF I τp).relabel (comapParVar s) ⊓
        (I.pullRelF (s.step m.1 n.1)
          (Sum.elim (Sum.elim m.2 n.2) τp)).relabel (comapVar s))

end Comap

/-! ### The nodes of the pulled walk -/

section Nodes

variable {s : ParamTCSpec L₂} {I : RelFOInterpretation L₁ L₂ Tag dim} {A : Type} [L₁.Structure A]
variable {τp : Fin s.par → Tag}

/-- A node of the pulled walk is *in domain* when every point it encodes is a
point of the target. -/
def InDom (a : (s.comapRel I τp).Node A) : Prop :=
  ∀ i, (I.domFormula (a.1.2 i)).Realize fun j => a.2 (coordIx dim i j)

/-- A valuation of the pulled parameters is in domain when every point it
encodes is. -/
def ParInDom (I : RelFOInterpretation L₁ L₂ Tag dim) (τp : Fin s.par → Tag)
    (z : Fin (s.par * dim) → A) : Prop :=
  ∀ i, (I.domFormula (τp i)).Realize fun j => z (coordIx dim i j)

/-- The node of the target that an in-domain node encodes. -/
def decode (a : (s.comapRel I τp).Node A) (ha : InDom a) : s.Node (I.MapRel A) :=
  (a.1.1, fun i => ⟨(a.1.2 i, fun j => a.2 (coordIx dim i j)), ha i⟩)

/-- The parameters of the target that an in-domain valuation encodes. -/
def decodePar {z : Fin (s.par * dim) → A} (hz : ParInDom I τp z) : Fin s.par → I.MapRel A :=
  fun i => ⟨(τp i, fun j => z (coordIx dim i j)), hz i⟩

variable (τp)

/-- A node of the target, read as a node of the pulled walk. -/
def encode (c : s.Node (I.MapRel A)) : (s.comapRel I τp).Node A :=
  ((c.1, fun i => (c.2 i).1.1), fun m =>
    (c.2 (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2)

variable {τp}

theorem coord_encode (τp : Fin s.par → Tag) (c : s.Node (I.MapRel A)) (i : Fin s.k)
    (j : Fin dim) : (encode τp c).2 (coordIx dim i j) = (c.2 i).1.2 j := by
  simp only [encode, coordIx, Equiv.symm_apply_apply]

/-- The encoding of a node of the target is in domain. -/
theorem inDom_encode (τp : Fin s.par → Tag) (c : s.Node (I.MapRel A)) :
    InDom (encode τp c) := by
  intro i
  have hco : (fun j => (encode τp c).2 (coordIx dim i j)) = (c.2 i).1.2 :=
    funext fun j => coord_encode τp c i j
  rw [hco]
  exact (c.2 i).2

/-- Encoding and decoding are inverse on nodes of the target. -/
theorem decode_encode (τp : Fin s.par → Tag) (c : s.Node (I.MapRel A)) :
    decode (encode τp c) (inDom_encode τp c) = c := by
  refine Prod.ext_iff.mpr ⟨rfl, funext fun i => Subtype.ext (Prod.ext_iff.mpr ⟨rfl, ?_⟩)⟩
  exact funext fun j => coord_encode τp c i j

end Nodes

/-! ### Steps and reachability correspond -/

section Correspondence

variable {s : ParamTCSpec L₂} {I : RelFOInterpretation L₁ L₂ Tag dim} {A : Type}
  [L₁.Structure A] {τp : Fin s.par → Tag}

/-- **A step of the pulled walk is a step of the original one**, both endpoints
and the parameters being in the domain. -/
theorem stepAt_comapRel_iff {z : Fin (s.par * dim) → A} (a b : (s.comapRel I τp).Node A) :
    (s.comapRel I τp).StepAt z a b ↔
      ∃ (ha : InDom a) (hb : InDom b) (hz : ParInDom I τp z),
        s.StepAt (decodePar hz) (decode a ha) (decode b hb) := by
  set v : ((Fin (s.k * dim) ⊕ Fin (s.k * dim)) ⊕ Fin (s.par * dim)) → A :=
    Sum.elim (Sum.elim a.2 b.2) z with hv
  have hsrc : ((domTupleF I a.1.2).relabel (comapSrcVar s)).Realize v ↔ InDom a := by
    rw [Formula.realize_relabel, realize_domTupleF]
    exact Iff.rfl
  have htgt : ((domTupleF I b.1.2).relabel (comapTgtVar s)).Realize v ↔ InDom b := by
    rw [Formula.realize_relabel, realize_domTupleF]
    exact Iff.rfl
  have hpar : ((domTupleF I τp).relabel (comapParVar s)).Realize v ↔ ParInDom I τp z := by
    rw [Formula.realize_relabel, realize_domTupleF]
    exact Iff.rfl
  have hmain : ∀ (ha : InDom a) (hb : InDom b) (hz : ParInDom I τp z),
      (((I.pullRelF (s.step a.1.1 b.1.1) (Sum.elim (Sum.elim a.1.2 b.1.2) τp)).relabel
        (comapVar s)).Realize v ↔
          s.StepAt (decodePar hz) (decode a ha) (decode b hb)) := by
    intro ha hb hz
    have hdom : ∀ q : (Fin s.k ⊕ Fin s.k) ⊕ Fin s.par,
        (I.domFormula ((Sum.elim (Sum.elim a.1.2 b.1.2) τp) q)).Realize
          fun j => (v ∘ comapVar s) (q, j) := by
      rintro ((i | i) | i)
      · exact ha i
      · exact hb i
      · exact hz i
    rw [Formula.realize_relabel,
      I.realize_pullRelF (s.step a.1.1 b.1.1) (Sum.elim (Sum.elim a.1.2 b.1.2) τp)
        (v ∘ comapVar s) hdom]
    refine iff_of_eq (congrArg (Formula.Realize (s.step a.1.1 b.1.1)) ?_)
    funext q
    rcases q with (i | i) | i <;> rfl
  constructor
  · intro h
    obtain ⟨h12, h34⟩ := Formula.realize_inf.mp h
    obtain ⟨h1, h2⟩ := Formula.realize_inf.mp h12
    obtain ⟨h3, h4⟩ := Formula.realize_inf.mp h34
    have ha := hsrc.mp h1
    have hb := htgt.mp h2
    have hz := hpar.mp h3
    exact ⟨ha, hb, hz, (hmain ha hb hz).mp h4⟩
  · rintro ⟨ha, hb, hz, h⟩
    refine Formula.realize_inf.mpr ⟨Formula.realize_inf.mpr ⟨hsrc.mpr ha, htgt.mpr hb⟩,
      Formula.realize_inf.mpr ⟨hpar.mpr hz, (hmain ha hb hz).mpr h⟩⟩

/-- **The pulled walk reaches what the original one reaches**, from an
in-domain node. The target's membership in the domain is part of the
conclusion: a walk cannot leave the domain, its steps being guarded. -/
theorem reachAt_comapRel_forward {z : Fin (s.par * dim) → A} {a b : (s.comapRel I τp).Node A}
    (h : (s.comapRel I τp).ReachAt z a b) (ha : InDom a) (hz : ParInDom I τp z) :
    ∃ hb : InDom b, s.ReachAt (decodePar hz) (decode a ha) (decode b hb) := by
  induction h with
  | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨hc, hac⟩ := ih
    obtain ⟨hc', hd, hz', hstep⟩ := (stepAt_comapRel_iff c d).mp hcd
    refine ⟨hd, ?_⟩
    have hce : decode c hc = decode c hc' := rfl
    exact hac.tail (hce ▸ hstep)

/-- **And conversely**: what the original walk reaches, the pulled one
reaches. -/
theorem reachAt_comapRel_backward {z : Fin (s.par * dim) → A} (hz : ParInDom I τp z)
    {c d : s.Node (I.MapRel A)} (h : s.ReachAt (decodePar hz) c d) :
    (s.comapRel I τp).ReachAt z (encode τp c) (encode τp d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
    refine ih.tail ((stepAt_comapRel_iff (encode τp x) (encode τp y)).mpr
      ⟨inDom_encode τp x, inDom_encode τp y, hz, ?_⟩)
    rw [decode_encode τp x, decode_encode τp y]
    exact hxy

/-- **Reachability corresponds**, between nodes of the domain. -/
theorem reachAt_comapRel_iff {z : Fin (s.par * dim) → A} {a b : (s.comapRel I τp).Node A}
    (ha : InDom a) (hb : InDom b) (hz : ParInDom I τp z) :
    (s.comapRel I τp).ReachAt z a b ↔
      s.ReachAt (decodePar hz) (decode a ha) (decode b hb) := by
  constructor
  · intro h
    obtain ⟨hb', hr⟩ := reachAt_comapRel_forward h ha hz
    have : decode b hb' = decode b hb := rfl
    exact this ▸ hr
  · intro h
    have hae : encode τp (decode a ha) = a := by
      refine Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨rfl, rfl⟩, funext fun m => ?_⟩
      change (decode a ha).2 (finProdFinEquiv.symm m).1 |>.1.2 (finProdFinEquiv.symm m).2 = a.2 m
      change a.2 (coordIx dim (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) = a.2 m
      refine congrArg a.2 ?_
      simp only [coordIx, Prod.mk.eta]
      exact Equiv.apply_symm_apply _ _
    have hbe : encode τp (decode b hb) = b := by
      refine Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨rfl, rfl⟩, funext fun m => ?_⟩
      change (decode b hb).2 (finProdFinEquiv.symm m).1 |>.1.2 (finProdFinEquiv.symm m).2 = b.2 m
      change b.2 (coordIx dim (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) = b.2 m
      refine congrArg b.2 ?_
      simp only [coordIx, Prod.mk.eta]
      exact Equiv.apply_symm_apply _ _
    have := reachAt_comapRel_backward hz h
    rwa [hae, hbe] at this

end Correspondence

end ParamTCSpec

end DescriptiveComplexity
