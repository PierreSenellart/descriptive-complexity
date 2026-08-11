/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpAtoms
import DescriptiveComplexity.Problems.Wide.PfpRepAtoms
import DescriptiveComplexity.Problems.Wide.PfpSlots

/-!
# The data of the EXPSPACE reduction, bundled

Everything the EXPSPACE program is built *from*, in one record: the
expansion, the partial-fixed-point definition, one prenex pack per step
formula and one for the output sentence, and the encoding layout with its
coordinate budget. On top of it, the **derived dimensions** the slot and
control inventories of `DescriptiveComplexity.Problems.Wide.PfpSlots` are
sized by: the variable index `DescriptiveComplexity.Pfp.PfpData.VarIx`
(`none` is the output), the prefix lengths `nOf` and their maximum `ki`, the
outer block count `ko`, the classified atoms of each matrix
(`DescriptiveComplexity.Pfp.PfpData.kindOf`) and their counts.

The point of bundling: the program's phase and rule types are indexed by
this data (one call site per variable, per atom, per argument position), so
every site file takes one `PfpData` and nothing else, and the dimensions are
*defined* as the exact maxima rather than constrained by inequalities.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- **The data of the EXPSPACE reduction**: the expansion, the definition,
the prenex packs, and the encoding layout with its coordinate budget. -/
structure PfpData (L : Language.{0, 0}) : Type 1 where
  /-- The exponential expansion the machine's tape simulates. -/
  X : ExpExpansion L
  /-- The partial-fixed-point definition being iterated. -/
  d : StepDef (X.E.sum Language.order)
  /-- A prenex pack per step formula. -/
  pk : ∀ i : d.B.ι, PrenexPack (d.step i)
  /-- A prenex pack for the output sentence, its (no) free variables
  re-bound. -/
  pkOut : PrenexPack (d.out.relabel (Empty.elim : Empty → Fin 0))
  /-- A prenex pack per domain sentence of the expansion: the gate's `dom`
  sub-evaluation runs its prefix as an element loop. -/
  domPk : ∀ t : X.Tag,
    PrenexPack ((X.dom t).relabel (Empty.elim : Empty → Fin 0))
  /-- A prenex pack per defining sentence of the expansion, at each relation
  symbol and tuple of tags: the expansion atoms' sub-folds run these. -/
  relPk : ∀ {n : ℕ} (r : X.E.Relations n) (τ : Fin n → X.Tag),
    PrenexPack ((X.relSentence r τ).relabel (Empty.elim : Empty → Fin 0))
  /-- The coordinate budget of the encodings: the name slots of a mark. -/
  dd0 : ℕ
  /-- The dimension of the interpretation. -/
  dd : ℕ
  /-- The encoding layout of the points. -/
  ly : EncLayout (PtCode X) (blockArityBound X.B) dd
  /-- The layout inhabits the first `dd0` coordinates, so a padded cell's
  mark can carry its own encoding-relevant coordinates in name slots. -/
  lyLt : ∀ j : Fin dd,
    ((∃ q : PtCode X, ly.cIx q = j) ∨ ∃ p : Fin (blockArityBound X.B), ly.pIx p = j) →
    (j : ℕ) < dd0
  /-- The budget fits in the dimension. -/
  dd0Le : dd0 ≤ dd

namespace PfpData

variable (dt : PfpData L)

/-! ### The variable index -/

/-- **The variables the program evaluates a formula for**: the fixed-point
variables, and (`none`) the output sentence. -/
abbrev VarIx : Type := Option dt.d.B.ι

/-- The number of outer argument blocks: enough for every variable's
arguments. -/
noncomputable def ko : ℕ := blockArityBound dt.d.B

/-- The arity of a variable – the number of blocks its address prefix
reads; `0` for the output. -/
def arOf : dt.VarIx → ℕ
  | none => 0
  | some i => dt.d.B.arity i

/-- The prefix length of a variable's pack. Reducible: the pack's own
statements are about `(dt.pk i).n`, and `rw` matches at implicit
transparency. -/
@[reducible] def nOf : dt.VarIx → ℕ
  | none => dt.pkOut.n
  | some i => (dt.pk i).n

/-- The polarities of a variable's pack. -/
@[reducible] def polOf : dt.VarIx → ℕ → Bool
  | none => dt.pkOut.pol
  | some i => (dt.pk i).pol

/-- The matrix of a variable's pack. -/
@[reducible] def matOf : ∀ v : dt.VarIx,
    ((dt.X.E.sum Language.order).sum dt.d.B.lang).BoundedFormula Empty (dt.nOf v)
  | none => dt.pkOut.mat
  | some i => (dt.pk i).mat

theorem matOf_isQF : ∀ v : dt.VarIx, (dt.matOf v).IsQF
  | none => dt.pkOut.isQF
  | some i => (dt.pk i).isQF

theorem arOf_le_nOf : ∀ v : dt.VarIx, dt.arOf v ≤ dt.nOf v
  | none => Nat.zero_le _
  | some i => (dt.pk i).kLe

theorem arOf_le_ko : ∀ v : dt.VarIx, dt.arOf v ≤ dt.ko
  | none => Nat.zero_le _
  | some i => arity_le_blockArityBound dt.d.B i

/-- The number of inner argument blocks: the longest prefix among the
packs. -/
noncomputable def ki : ℕ :=
  letI := Fintype.ofFinite dt.VarIx
  Finset.univ.sup dt.nOf

theorem nOf_le_ki (v : dt.VarIx) : dt.nOf v ≤ dt.ki := by
  letI := Fintype.ofFinite dt.VarIx
  exact Finset.le_sup (Finset.mem_univ v)

/-! ### The classified atoms -/

/-- The atoms of a variable's matrix, in evaluation order. -/
def atomsOf (v : dt.VarIx) :
    List (((dt.X.E.sum Language.order).sum dt.d.B.lang).BoundedFormula Empty (dt.nOf v)) :=
  qfAtoms (dt.matOf v)

/-- The number of atoms of a variable's matrix. -/
def natOf (v : dt.VarIx) : ℕ := (dt.atomsOf v).length

/-- The largest atom count among the matrices: the size of the verdict
inventory. -/
noncomputable def natMax : ℕ :=
  letI := Fintype.ofFinite dt.VarIx
  Finset.univ.sup dt.natOf

theorem natOf_le_natMax (v : dt.VarIx) : dt.natOf v ≤ dt.natMax := by
  letI := Fintype.ofFinite dt.VarIx
  exact Finset.le_sup (Finset.mem_univ v)

/-- **The kind of an atom**, read off the syntax: the index data of the
per-atom call sites. -/
noncomputable def kindOf (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    MatAtom dt.X dt.d (dt.nOf v) :=
  (matAtom? ((dt.atomsOf v).get a)).get
    (isSome_matAtom?_of_mem_qfAtoms (dt.matOf v) _ ((dt.atomsOf v).get_mem a))

/-- The classifier agrees with the kind. -/
theorem matAtom?_get (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    matAtom? ((dt.atomsOf v).get a) = some (dt.kindOf v a) :=
  (Option.some_get _).symm

/-! ### The slot and control inventories, sized -/

/-! ### The control dimensions -/

/-- The prefix depth of an expansion atom's defining sentences, maximized
over the tag tuples; `0` for the other kinds, whose loops are the
coordinate ones. -/
noncomputable def kindDepth {n : ℕ} : MatAtom dt.X dt.d n → ℕ
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    (Finset.univ : Finset (Fin k → dt.X.Tag)).sup fun τ => (dt.relPk e τ).n
  | _ => 0

/-- The leaf-read budget of an atom: the **block**-atom count of its defining
sentences' matrices – the base-vocabulary atoms are guards and take no trip –
`2` for the coordinate loops of an equality or order atom, `0` for a stage
atom. -/
noncomputable def kindReads {n : ℕ} : MatAtom dt.X dt.d n → ℕ
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    (Finset.univ : Finset (Fin k → dt.X.Tag)).sup fun τ =>
      (blkAtoms (dt.relPk e τ).mat).length
  | .eq _ _ => 2
  | .ord _ _ => 2
  | .stage _ _ => 0

/-- The domain sentences' largest prefix depth. -/
noncomputable def domDepth : ℕ :=
  letI := Fintype.ofFinite dt.X.Tag
  Finset.univ.sup fun t => (dt.domPk t).n

/-- The domain sentences' largest read-leaf count. -/
noncomputable def domReads : ℕ :=
  letI := Fintype.ofFinite dt.X.Tag
  Finset.univ.sup fun t => (blkAtoms (dt.domPk t).mat).length

/-- **The loop-variable budget**: the coordinate loops' width and every
element loop's depth. -/
noncomputable def eDim : ℕ :=
  letI := Fintype.ofFinite dt.VarIx
  max (max dt.dd0 dt.domDepth)
    (Finset.univ.sup fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindDepth (dt.kindOf v a))

/-- **The leaf-read budget.** -/
noncomputable def nfDim : ℕ :=
  letI := Fintype.ofFinite dt.VarIx
  max dt.domReads
    (Finset.univ.sup fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindReads (dt.kindOf v a))

/-- The number of argument points an atom's kind reads the tags of: the arity
of an expansion atom, `0` for the other kinds. -/
noncomputable def kindArgs {n : ℕ} : MatAtom dt.X dt.d n → ℕ
  | @MatAtom.exp _ _ _ _ k _ _ => k
  | _ => 0

/-- **The tag-flag budget**: one per argument position of an expansion atom
and tag, and one block's worth for the gates – whose domain evaluation reads
the tag of the single block it gates, and which must be paid for even when no
expansion atom occurs. -/
noncomputable def ntgDim : ℕ :=
  letI := Fintype.ofFinite dt.VarIx
  letI := Fintype.ofFinite dt.X.Tag
  ((Finset.univ.sup fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindArgs (dt.kindOf v a)) + 1) *
    Fintype.card dt.X.Tag

/-- **The accumulator budget**: one per prefix level, and one over. -/
noncomputable def naDim : ℕ := dt.ki + 1

theorem dd0_le_eDim : dt.dd0 ≤ dt.eDim :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem domDepth_le_eDim : dt.domDepth ≤ dt.eDim :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem kindDepth_le_eDim (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    dt.kindDepth (dt.kindOf v a) ≤ dt.eDim := by
  letI := Fintype.ofFinite dt.VarIx
  refine le_trans ?_ (le_max_right _ _)
  exact le_trans
    (Finset.le_sup (f := fun a : Fin (dt.natOf v) => dt.kindDepth (dt.kindOf v a))
      (Finset.mem_univ a))
    (Finset.le_sup (f := fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindDepth (dt.kindOf v a))
      (Finset.mem_univ v))

theorem domReads_le_nfDim : dt.domReads ≤ dt.nfDim := le_max_left _ _

/-- **An expansion atom's tag flags fit**: one per argument position and
tag. -/
theorem kindArgs_mul_card_le_ntgDim (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    letI := Fintype.ofFinite dt.X.Tag
    dt.kindArgs (dt.kindOf v a) * Fintype.card dt.X.Tag ≤ dt.ntgDim := by
  letI := Fintype.ofFinite dt.VarIx
  letI := Fintype.ofFinite dt.X.Tag
  refine Nat.mul_le_mul_right _ (le_trans ?_ (Nat.le_succ _))
  exact le_trans
    (Finset.le_sup (f := fun a : Fin (dt.natOf v) => dt.kindArgs (dt.kindOf v a))
      (Finset.mem_univ a))
    (Finset.le_sup (f := fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindArgs (dt.kindOf v a))
      (Finset.mem_univ v))

/-- **A gate's tag flags fit**: one block's worth is always paid for. -/
theorem card_le_ntgDim :
    letI := Fintype.ofFinite dt.X.Tag
    Fintype.card dt.X.Tag ≤ dt.ntgDim := by
  letI := Fintype.ofFinite dt.VarIx
  letI := Fintype.ofFinite dt.X.Tag
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem kindReads_le_nfDim (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    dt.kindReads (dt.kindOf v a) ≤ dt.nfDim := by
  letI := Fintype.ofFinite dt.VarIx
  refine le_trans ?_ (le_max_right _ _)
  exact le_trans
    (Finset.le_sup (f := fun a : Fin (dt.natOf v) => dt.kindReads (dt.kindOf v a))
      (Finset.mem_univ a))
    (Finset.le_sup (f := fun v : dt.VarIx =>
      Finset.univ.sup fun a : Fin (dt.natOf v) => dt.kindReads (dt.kindOf v a))
      (Finset.mem_univ v))

/-- **The control slots of the program**, at the computed budgets. -/
noncomputable abbrev CtlIx : Type :=
  Ctl dt.eDim dt.naDim dt.natMax dt.nfDim dt.ntgDim

/-- The track slots of the program. -/
noncomputable abbrev SlotIx : Type := Slot dt.d.B.ι dt.ko dt.ki dt.dd0

/-- The slots' equality is classically decidable – the variable index only
carries `Finite`, and the rules that update slots (`Function.update`) are
noncomputable throughout. -/
noncomputable instance : DecidableEq dt.SlotIx := Classical.decEq _

/-- The block-index type of the program's addresses. -/
noncomputable abbrev KIx : Type := Fin dt.ko ⊕ₗ Fin dt.ki

end PfpData

end Pfp

end DescriptiveComplexity
