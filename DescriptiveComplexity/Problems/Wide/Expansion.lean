/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Defs
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Expansion

/-!
# The wide machine as an exponential expansion

The construction that makes the wide machine a *member* of an exponential class:
an `DescriptiveComplexity.ExpExpansion` of `FirstOrder.Language.wide`-structures
whose expanded vocabulary is `FirstOrder.Language.turing`. Read on an instance
`A`, it produces exactly the ordinary machine instance whose universe is
`DescriptiveComplexity.WPoint A` – so a wide machine *is* an ordinary machine,
one exponential up, and nothing has to be said about resources.

Three things fix the whole design.

* **The block is one unary relation variable** (`addrBlock`), so an assignment
  *is* a subset of the instance and the expanded universe is its power set.
  There is no padding to worry about, and the binary-number order on addresses
  can be written directly rather than through
  `DescriptiveComplexity.SOBlock.ordLeF`, which would compare padded atoms
  against the *ambient* order rather than against the instance's own.
* **Two tags** (`DescriptiveComplexity.Wide.WTag`): `addr`, whose domain
  sentence is `⊤`, so those points are all the addresses; and `ctrl`, whose
  domain sentence says the variable is a **singleton**, so those points are the
  elements of the instance. This is the standard way of keeping the base
  universe visible inside an expanded one.
* **Every defining sentence is a static choice on the tags** followed by one of
  five sentences: a mark of the control (`markS`), a binary attribute of it
  (`binS`), the singleton condition (`singleS`), the order on addresses
  (`addrLeS`) and the initial tape (`inpS`). Every quantifier in them ranges
  over the **base** – an element, never an address – which is exactly what
  keeps them first-order there.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Wide

/-! ### The vocabularies -/

/-- The ordered vocabulary of wide-machine instances: what an expansion's
sentences may read besides the block. -/
abbrev wOrd : Language.{0, 0} := Language.wide.sum Language.order

/-- **The block whose assignments are the addresses**: a single unary relation
variable, so an assignment is a subset of the instance. -/
abbrev addrBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The base vocabulary expanded by one copy of the block. -/
abbrev wide1 : Language.{0, 0} := wOrd.sum addrBlock.lang

/-- The base vocabulary expanded by two copies of the block. -/
abbrev wide2 : Language.{0, 0} := wide1.sum addrBlock.lang

/-- A unary symbol of the instance, in the ordered vocabulary: a raw `Sum.inl`
does not elaborate at that type. -/
abbrev wSym₁ (r : Language.wide.Relations 1) : wOrd.Relations 1 := Sum.inl r

/-- A binary symbol of the instance, in the ordered vocabulary. -/
abbrev wSym₂ (r : Language.wide.Relations 2) : wOrd.Relations 2 := Sum.inl r

/-- The relation variable of the block, at one copy. -/
abbrev bit1 : wide1.Relations 1 := Sum.inr ⟨(), rfl⟩

/-- The relation variable of the first of two copies. -/
abbrev bitA : wide2.Relations 1 := Sum.inl (Sum.inr ⟨(), rfl⟩)

/-- The relation variable of the second of two copies. -/
abbrev bitB : wide2.Relations 1 := Sum.inr ⟨(), rfl⟩

/-! ### Addresses, as assignments of the block -/

section Bits

variable {A : Type}

/-- **The address an assignment is**: the elements its relation variable
holds of. -/
def wbits (ρ : addrBlock.Assignment A) : A → Prop := fun x => ρ () fun _ => x

/-- **The assignment an address is**, the inverse of
`DescriptiveComplexity.Wide.wbits`. -/
def wassign (s : A → Prop) : addrBlock.Assignment A := fun _ v => s (v 0)

@[simp]
theorem wbits_wassign (s : A → Prop) : wbits (wassign s) = s := rfl

/-- A unary relation variable is read at its only argument. -/
theorem apply₁ (f : (Fin 1 → A) → Prop) (v : Fin 1 → A) : f v ↔ f fun _ => v 0 :=
  iff_of_eq (congrArg f (funext fun j => congrArg v (Subsingleton.elim j 0)))

/-- **An assignment of the block is the assignment of its address**: the single
variable being unary, nothing else is stored. -/
@[simp]
theorem wassign_wbits (ρ : addrBlock.Assignment A) : wassign (wbits ρ) = ρ := by
  funext i v
  match i with
  | () => exact propext (apply₁ (ρ ()) v).symm

/-- Two assignments of the block holding the same address are equal. -/
theorem wassign_injective : Function.Injective (wbits (A := A)) := fun ρ σ h => by
  rw [← wassign_wbits ρ, ← wassign_wbits σ, h]

end Bits

/-! ### The guards of the base vocabulary -/

section Guards

variable {γ : Type}

/-- A unary mark of the instance. -/
noncomputable def markG (r : Language.wide.Relations 1) (x : γ) : wOrd.Formula γ :=
  Relations.formula₁ (wSym₁ r) (Term.var x)

/-- A binary attribute of the instance. -/
noncomputable def attrG (r : Language.wide.Relations 2) (x y : γ) : wOrd.Formula γ :=
  Relations.formula₂ (wSym₂ r) (Term.var x) (Term.var y)

/-- `x` and `y` are the same element. -/
noncomputable def eqG (x y : γ) : wOrd.Formula γ := Term.equal (Term.var x) (Term.var y)

/-- `x` is strictly below `y` in the instance's own order. -/
noncomputable def ltG (x y : γ) : wOrd.Formula γ :=
  attrG wmLe x y ⊓ ∼(attrG wmLe y x)

variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_markG (r : Language.wide.Relations 1) (x : γ) :
    (markG r x).Realize v ↔ RelMap r ![v x] := by
  rw [markG, Formula.realize_rel₁, relMap_sumInl]
  simp only [Term.realize_var]

@[simp]
theorem realize_attrG (r : Language.wide.Relations 2) (x y : γ) :
    (attrG r x y).Realize v ↔ RelMap r ![v x, v y] := by
  rw [attrG, Formula.realize_rel₂, relMap_sumInl]
  simp only [Term.realize_var]

@[simp]
theorem realize_eqG (x y : γ) : (eqG x y).Realize v ↔ v x = v y := by
  rw [eqG, Formula.realize_equal, Term.realize_var, Term.realize_var]

@[simp]
theorem realize_ltG (x y : γ) :
    (ltG x y).Realize v ↔ (WMLe (v x) (v y) ∧ ¬WMLe (v y) (v x)) := by
  rw [ltG, Formula.realize_inf, Formula.realize_not]
  exact and_congr (realize_attrG wmLe x y) (not_congr (realize_attrG wmLe y x))

end Guards

/-! ### The atoms of the block, and the lifts -/

section Atoms

variable {γ : Type}

/-- The address of the single copy holds `x`. -/
noncomputable def bit1F (x : γ) : wide1.Formula γ := Relations.formula₁ bit1 (Term.var x)

/-- The address of the first of two copies holds `x`. -/
noncomputable def bitAF (x : γ) : wide2.Formula γ := Relations.formula₁ bitA (Term.var x)

/-- The address of the second of two copies holds `x`. -/
noncomputable def bitBF (x : γ) : wide2.Formula γ := Relations.formula₁ bitB (Term.var x)

/-- A base guard, read at one copy of the block. -/
noncomputable def lift1 (φ : wOrd.Formula γ) : wide1.Formula γ := LHom.sumInl.onFormula φ

/-- A base guard, read at two copies of the block. -/
noncomputable def lift2 (φ : wOrd.Formula γ) : wide2.Formula γ :=
  LHom.sumInl.onFormula (LHom.sumInl.onFormula φ)

variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_bit1F (ρ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) _ (bit1F x) v ↔
      wbits ρ (v x)) := by
  letI := addrBlock.structure₁ (L := wOrd) ρ
  rw [bit1F, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_bitAF (ρ σ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) _ (bitAF x) v ↔
      wbits ρ (v x)) := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [bitAF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_bitBF (ρ σ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) _ (bitBF x) v ↔
      wbits σ (v x)) := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [bitBF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_lift1 (ρ : addrBlock.Assignment A) (φ : wOrd.Formula γ) :
    (@Formula.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) _ (lift1 φ) v ↔
      φ.Realize v) := by
  letI := addrBlock.structure ρ
  rw [lift1]
  exact LHom.realize_onFormula _ φ

@[simp]
theorem realize_lift2 (ρ σ : addrBlock.Assignment A) (φ : wOrd.Formula γ) :
    (@Formula.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) _ (lift2 φ) v ↔
      φ.Realize v) := by
  letI := addrBlock.structure ρ
  letI := addrBlock.structure σ
  letI := addrBlock.structure₁ (L := wOrd) ρ
  rw [lift2]
  exact (LHom.realize_onFormula _ (LHom.sumInl.onFormula φ)).trans
    (LHom.realize_onFormula _ φ)

end Atoms

/-! ### The five sentences

Everything an expansion of `FirstOrder.Language.wide` has to say, once each. -/

/-- **A mark of the control**: the point is the element `x`, and `x` carries the
mark `r`. -/
noncomputable def markS (r : Language.wide.Relations 1) : wide1.Sentence :=
  Formula.iExs (Fin 1) (bit1F (Sum.inr 0) ⊓ lift1 (markG r (Sum.inr 0)))

/-- **A binary attribute of the control**: the two points are the elements `x`
and `y`, and `r` holds of them. -/
noncomputable def binS (r : Language.wide.Relations 2) : wide2.Sentence :=
  Formula.iExs (Fin 2) (bitAF (Sum.inr 0) ⊓
    (bitBF (Sum.inr 1) ⊓ lift2 (attrG r (Sum.inr 0) (Sum.inr 1))))

/-- **The domain sentence of the control tag**: the address is a singleton, so
the point is an element of the instance. -/
noncomputable def singleS : wide1.Sentence :=
  Formula.iExs (Fin 1) (bit1F (Sum.inr 0)) ⊓
    Formula.iAlls (Fin 2) ((bit1F (Sum.inr 0) ⊓ bit1F (Sum.inr 1)) ⟹
      lift1 (eqG (Sum.inr 0) (Sum.inr 1)))

/-- **The order on addresses**: the two addresses agree, or, at some element the
first is out of and the second in, they agree at every strictly smaller
element. -/
noncomputable def addrLeS : wide2.Sentence :=
  Formula.iAlls (Fin 1) (bitAF (Sum.inr 0) ⇔ bitBF (Sum.inr 0)) ⊔
    Formula.iExs (Fin 1)
      (Formula.iAlls (Fin 1) (lift2 (ltG (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⟹
          (bitAF (Sum.inr 0) ⇔ bitBF (Sum.inr 0))) ⊓
        (∼(bitAF (Sum.inr 0)) ⊓ bitBF (Sum.inr 0)))

/-- **The initial tape**: the first address is the initial segment cut by some
element `x`, the second point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpS : wide2.Sentence :=
  Formula.iExs (Fin 2)
    (Formula.iAlls (Fin 1)
        (bitAF (Sum.inr 0) ⇔ lift2 (attrG wmLe (Sum.inr 0) (Sum.inl (Sum.inr 0)))) ⊓
      (bitBF (Sum.inr 1) ⊓ lift2 (attrG wmInp (Sum.inr 0) (Sum.inr 1))))

/-! ### What the five sentences say -/

section Realize

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]

/-- An address is a singleton: it holds something, and at most one thing. -/
def WMSingle (s : A → Prop) : Prop := (∃ x, s x) ∧ ∀ x y, s x → s y → x = y

omit [Language.wide.Structure A] [LinearOrder A] in
/-- A singleton address is the address of an element. -/
theorem exists_eq_of_wmSingle {s : A → Prop} (h : WMSingle s) : ∃ x, ∀ y, s y ↔ y = x := by
  obtain ⟨⟨x, hx⟩, huniq⟩ := h
  exact ⟨x, fun y => ⟨fun hy => huniq y x hy hx, fun hy => hy ▸ hx⟩⟩

omit [Language.wide.Structure A] [LinearOrder A] in
/-- The address of an element is a singleton. -/
theorem wmSingle_eq (x : A) : WMSingle (fun y => y = x) :=
  ⟨⟨x, rfl⟩, fun _ _ h1 h2 => h1.trans h2.symm⟩

/-- The trivially true sentence, at one copy of the block. -/
theorem realize_topS (ρ : addrBlock.Assignment A) :
    @Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) ⊤ := by
  letI := addrBlock.structure₁ (L := wOrd) ρ
  exact Formula.realize_top.mpr trivial

/-- The trivially false sentence, at one copy of the block. -/
theorem not_realize_botS (ρ : addrBlock.Assignment A) :
    ¬@Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) ⊥ := by
  letI := addrBlock.structure₁ (L := wOrd) ρ
  exact fun h => Formula.realize_bot.mp h

/-- The trivially true sentence, at two copies of the block. -/
theorem realize_topS₂ (ρ σ : addrBlock.Assignment A) :
    @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) ⊤ := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  exact Formula.realize_top.mpr trivial

/-- The trivially false sentence, at two copies of the block. -/
theorem not_realize_botS₂ (ρ σ : addrBlock.Assignment A) :
    ¬@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) ⊥ := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  exact fun h => Formula.realize_bot.mp h

theorem realize_markS (r : Language.wide.Relations 1) (ρ : addrBlock.Assignment A) :
    (@Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) (markS r) ↔
      ∃ x, wbits ρ x ∧ RelMap r ![x]) := by
  letI := addrBlock.structure₁ (L := wOrd) ρ
  rw [markS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_bit1F, realize_lift1,
    realize_markG, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩

theorem realize_binS (r : Language.wide.Relations 2) (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) (binS r) ↔
      ∃ x y, wbits ρ x ∧ wbits σ y ∧ RelMap r ![x, y]) := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [binS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_bitAF, realize_bitBF,
    realize_lift2, realize_attrG, Sum.elim_inr]
  exact ⟨fun ⟨w, h1, h2, h3⟩ => ⟨w 0, w 1, h1, h2, h3⟩,
    fun ⟨x, y, h1, h2, h3⟩ => ⟨![x, y], h1, h2, h3⟩⟩

theorem realize_singleS (ρ : addrBlock.Assignment A) :
    (@Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) ρ) singleS ↔
      WMSingle (wbits ρ)) := by
  letI := addrBlock.structure₁ (L := wOrd) ρ
  rw [singleS, WMSingle, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_imp, realize_bit1F, realize_lift1, realize_eqG, Sum.elim_inr]
  exact and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩
    ⟨fun h x y h1 h2 => h ![x, y] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩

theorem realize_addrLeS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) addrLeS ↔
      WMSetLe WMLe (wbits ρ) (wbits σ)) := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [addrLeS, WMSetLe, Sentence.Realize]
  simp only [Formula.realize_sup, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_iff, Formula.realize_not,
    realize_bitAF, realize_bitBF, realize_lift2, realize_ltG, Sum.elim_inl, Sum.elim_inr]
  refine or_congr ⟨fun h x => h fun _ => x, fun h w => h (w 0)⟩ ?_
  exact ⟨fun ⟨w, hb, hs, ht⟩ => ⟨w 0, fun y hy => hb (fun _ => y) hy, hs, ht⟩,
    fun ⟨x, hb, hs, ht⟩ => ⟨fun _ => x, fun w hw => hb (w 0) hw, hs, ht⟩⟩

theorem realize_inpS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) inpS ↔
      ∃ x y, WMDown WMLe (wbits ρ) x ∧ wbits σ y ∧ WMInp x y) := by
  letI := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [inpS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_iff, realize_bitAF, realize_bitBF, realize_lift2, realize_attrG,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun ⟨w, hd, hb, hi⟩ => ⟨w 0, w 1, fun y => hd fun _ => y, hb, hi⟩,
    fun ⟨x, y, hd, hb, hi⟩ => ⟨![x, y], fun w => hd (w 0), hb, hi⟩⟩

end Realize

/-! ### The tags, and the defining sentences -/

/-- The two tags of the expansion: the addresses, and the elements of the
instance. -/
inductive WTag where
  /-- An address: any assignment of the block. -/
  | addr
  /-- A control element: a singleton assignment of the block. -/
  | ctrl
  deriving DecidableEq

instance : Fintype WTag := ⟨{WTag.addr, WTag.ctrl}, by intro x; cases x <;> simp⟩

/-- The domain sentence of each tag: an address is unrestricted, a control
element is a singleton. -/
noncomputable def domT : WTag → wide1.Sentence
  | .addr => ⊤
  | .ctrl => singleS

/-- Being a position: the addresses are the positions. -/
noncomputable def posnT : WTag → wide1.Sentence
  | .addr => ⊤
  | .ctrl => ⊥

/-- A mark of the control, at a tag: only control elements carry it. -/
noncomputable def markT (r : Language.wide.Relations 1) : WTag → wide1.Sentence
  | .addr => ⊥
  | .ctrl => markS r

/-- A binary attribute of the control, at a pair of tags. -/
noncomputable def binT (r : Language.wide.Relations 2) : WTag → WTag → wide2.Sentence
  | .ctrl, .ctrl => binS r
  | _, _ => ⊥

/-- The order of the machine, at a pair of tags: the addresses come first, in
the binary-number order, then the control elements in the instance's order. -/
noncomputable def leT : WTag → WTag → wide2.Sentence
  | .addr, .addr => addrLeS
  | .addr, .ctrl => ⊤
  | .ctrl, .addr => ⊥
  | .ctrl, .ctrl => binS wmLe

/-- The initial tape, at a pair of tags: an address holds a symbol. -/
noncomputable def inpT : WTag → WTag → wide2.Sentence
  | .addr, .ctrl => inpS
  | _, _ => ⊥

/-- Reading a one-copy sentence inside the block replicated once. -/
noncomputable def onS1 (φ : wide1.Sentence) : (wOrd.sum (addrBlock.replicate 1).lang).Sentence :=
  (addrBlock.oneLHom wOrd).onSentence φ

/-- Reading a two-copy sentence inside the block replicated twice. -/
noncomputable def onS2 (φ : wide2.Sentence) : (wOrd.sum (addrBlock.replicate 2).lang).Sentence :=
  (addrBlock.twoLHom wOrd).onSentence φ

/-- **The expansion of a wide-machine instance**: two tags, the one-variable
block, and the vocabulary of ordinary machines, every symbol of which is defined
by a static choice on the tags followed by one of the five sentences. -/
noncomputable def wideExp : ExpExpansion Language.wide where
  Tag := WTag
  B := addrBlock
  E := Language.turing
  dom := domT
  relSentence {n} r τ :=
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tr => onS1 (markT wmTr (τ 0))
    | _, .start => onS1 (markT wmStart (τ 0))
    | _, .acc => onS1 (markT wmAcc (τ 0))
    | _, .blank => onS1 (markT wmBlank (τ 0))
    | _, .right => onS1 (markT wmRight (τ 0))
    | _, .le => onS2 (leT (τ 0) (τ 1))
    | _, .tsrc => onS2 (binT wmSrc (τ 0) (τ 1))
    | _, .tread => onS2 (binT wmRead (τ 0) (τ 1))
    | _, .tdst => onS2 (binT wmDst (τ 0) (τ 1))
    | _, .twrite => onS2 (binT wmWrite (τ 0) (τ 1))
    | _, .inp => onS2 (inpT (τ 0) (τ 1))
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨.addr, addrBlock.botAssign A, ?_⟩
    letI := addrBlock.structure₁ (L := wOrd) (addrBlock.botAssign A)
    exact Formula.realize_top.mpr trivial

section Structure

variable (A : Type) [Language.wide.Structure A] [LinearOrder A]

/-- The expanded structure of `DescriptiveComplexity.Wide.wideExp`, at the
vocabulary of machines – equal to the expansion's own by definition, but not
syntactically, so instance search has to be handed it. -/
@[instance_reducible]
noncomputable def wideStructure : Language.turing.Structure (wideExp.Map A) :=
  wideExp.mapStructure A

variable {A}

/-- **Reading a one-copy sentence at a point**: the replicated assignment holds
the point's address in its single copy. -/
theorem realize_onS1 (φ : wide1.Sentence) (x : wideExp.Map A) :
    (@Sentence.Realize _ A ((addrBlock.replicate 1).structure₁ (L := wOrd)
        (addrBlock.replicateAssign fun i => ((![x] : Fin 1 → wideExp.Map A) i).1.2))
      (onS1 φ) ↔
      @Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) x.1.2) φ) :=
  addrBlock.realize_oneLHom (L := wOrd) _ φ

/-- **Reading a two-copy sentence at two points**: the replicated assignment
holds the first point's address in copy `0` and the second's in copy `1`. -/
theorem realize_onS2 (φ : wide2.Sentence) (x y : wideExp.Map A) :
    (@Sentence.Realize _ A ((addrBlock.replicate 2).structure₁ (L := wOrd)
        (addrBlock.replicateAssign fun i => ((![x, y] : Fin 2 → wideExp.Map A) i).1.2))
      (onS2 φ) ↔
      @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) x.1.2 y.1.2) φ) :=
  addrBlock.realize_twoLHom (L := wOrd) _ φ

end Structure

end Wide

end DescriptiveComplexity
