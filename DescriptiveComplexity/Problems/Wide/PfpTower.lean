/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpStageAtom
import DescriptiveComplexity.Problems.Wide.PfpTagged
import DescriptiveComplexity.Problems.Wide.PfpSeq
import DescriptiveComplexity.Problems.Wide.PfpRepAtoms
import DescriptiveComplexity.Problems.Wide.PfpVar
import DescriptiveComplexity.Problems.Wide.PfpRound

/-!
# The phase tower: the program's phase and site types, assembled

The full program's phase type, from the leaves up: per classified atom its
machinery's phases – a stage atom's random access, an expansion atom's
tag-branched loops, a comparison's coordinate loop – then the matrix as a
sequence over the atoms, the gates as a sequence over the argument blocks,
one variable's machinery around them, the evaluation's spine over the
variable list, and the outer program around everything.

The kind-dependent types are indexed by the **kind itself**
(`DescriptiveComplexity.Pfp.KindPh` and friends match on a
`DescriptiveComplexity.Pfp.MatAtom`), so every downstream definition
reduces per constructor; the stuck `DescriptiveComplexity.Pfp.PfpData.kindOf`
application appears only at the instantiation
(`DescriptiveComplexity.Pfp.PfpData.AtomPh` etc.).

The element loops of an atom run one read trip per atom of the defining
matrix – the guard atoms' trips read a harmless witness cell and their
flags are ignored by the folds – so the loop lengths match the
`DescriptiveComplexity.Pfp.PfpData.kindReads` budgets on the nose.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)

/-! ### The per-kind machinery types -/

/-- The loop count of an expansion atom's branch: one read per **block**
atom of the defining matrix – the base-vocabulary atoms are guards and need
no trip. -/
noncomputable def relNr {k : ℕ} (e : dt.X.E.Relations k)
    (τ : Fin k → dt.X.Tag) : ℕ :=
  (blkAtoms (dt.relPk e τ).mat).length

/-- The loop count of a domain branch. -/
noncomputable def domNr (t : dt.X.Tag) : ℕ :=
  (blkAtoms (dt.domPk t).mat).length

/-- **The machinery phases of an atom kind**: a stage atom's random access,
an expansion atom's tag-branched loops, a comparison's coordinate loop. -/
noncomputable def KindPh {n : ℕ} : MatAtom dt.X dt.d.B n → Type
  | .stage i _ => StagePh (dt.d.B.arity i)
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    TagPh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag) (dt.relNr e)
  | .eq _ _ => ElemPh 2
  | .ord _ _ => ElemPh 2

/-- **The machinery sites of an atom kind.** -/
noncomputable def KindSite {n : ℕ} : MatAtom dt.X dt.d.B n → Type
  | .stage i _ => StageSite (dt.d.B.arity i)
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    TagSite (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag) (dt.relNr e)
  | .eq _ _ => ElemSite 2
  | .ord _ _ => ElemSite 2

/-- **The rule shape of an atom kind's sites.** -/
noncomputable def KindSh {n : ℕ} :
    ∀ κ : MatAtom dt.X dt.d.B n, dt.KindSite κ → Type
  | .stage i _ => StageSh (dt.d.B.arity i)
  | @MatAtom.exp _ _ _ _ k e _ =>
    letI := Fintype.ofFinite dt.X.Tag
    TagSh (k * Fintype.card dt.X.Tag) (Fin k → dt.X.Tag) (dt.relNr e)
  | .eq _ _ => ElemSh 2
  | .ord _ _ => ElemSh 2

/-! ### The tower -/

/-- The machinery phases of the `a`-th atom of a variable's matrix. -/
noncomputable def AtomPh (v : dt.VarIx) (a : Fin (dt.natOf v)) : Type :=
  dt.KindPh (dt.kindOf v a)

/-- The machinery sites of the `a`-th atom. -/
noncomputable def AtomSite (v : dt.VarIx) (a : Fin (dt.natOf v)) : Type :=
  dt.KindSite (dt.kindOf v a)

/-- The rule shapes of the `a`-th atom's sites. -/
noncomputable def AtomSh (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    dt.AtomSite v a → Type :=
  dt.KindSh (dt.kindOf v a)

/-- **The matrix's phases**: the sequence over the classified atoms. -/
noncomputable def MatrixPh (v : dt.VarIx) : Type :=
  SeqPh (dt.natOf v) (dt.AtomPh v)

/-- **The matrix's sites.** -/
noncomputable def MatrixSite (v : dt.VarIx) : Type :=
  SeqSite (dt.natOf v) (dt.AtomSite v)

/-- **One gate block's phases**: the well-shapedness file test, and the
tag-branched domain evaluation. -/
noncomputable def GateBlockPh : Type :=
  letI := Fintype.ofFinite dt.X.Tag
  TestPh ⊕ TagPh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr

/-- **One gate block's sites**: the file test's, and the domain
evaluation's. -/
noncomputable def GateBlockSite : Type :=
  letI := Fintype.ofFinite dt.X.Tag
  Unit ⊕ TagSite (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr

/-- **The rule shape of a gate block's sites.** -/
noncomputable def GateBlockSh : dt.GateBlockSite → Type
  | Sum.inl _ => TestRule ⊕ Bool
  | Sum.inr s =>
    letI := Fintype.ofFinite dt.X.Tag
    TagSh (Fintype.card dt.X.Tag) dt.X.Tag dt.domNr s

/-- **The gates' phases**: the sequence over the argument blocks. -/
noncomputable def GatesPh (v : dt.VarIx) : Type :=
  SeqPh (dt.arOf v) fun _ => dt.GateBlockPh

/-- **The gates' sites.** -/
noncomputable def GatesSite (v : dt.VarIx) : Type :=
  SeqSite (dt.arOf v) fun _ => dt.GateBlockSite

/-- The number of quantified levels of a variable's pack. -/
noncomputable def nIn (v : dt.VarIx) : ℕ := dt.nOf v - dt.arOf v

/-- **The inner gates' phases**: one gate block per quantified level of
the variable's pack, at the VAL register's blocks. -/
noncomputable def IGatesPh (v : dt.VarIx) : Type :=
  SeqPh (dt.nIn v) fun _ => dt.GateBlockPh

/-- **The inner gates' sites.** -/
noncomputable def IGatesSite (v : dt.VarIx) : Type :=
  SeqSite (dt.nIn v) fun _ => dt.GateBlockSite

/-- **One round's machinery phases**: the inner gates, the branch, and the
matrix. -/
noncomputable def RoundPhF (v : dt.VarIx) : Type :=
  RoundPh (dt.IGatesPh v) (dt.MatrixPh v)

/-- **One variable's machinery phases**, gates and round plugged in. -/
noncomputable def VarPhF (v : dt.VarIx) : Type :=
  VarPh dt.CarryB (dt.GatesPh v) (dt.RoundPhF v)

/-- **The enumeration of the fixed-point variables.** -/
noncomputable def varList : List dt.d.B.ι :=
  letI := Fintype.ofFinite dt.d.B.ι
  Finset.univ.toList

/-- The number of fixed-point variables. -/
noncomputable def nv : ℕ := dt.varList.length

/-- The variable at a spine position. -/
noncomputable def varAt (j : Fin dt.nv) : dt.VarIx :=
  some (dt.varList.get j)

/-- **The evaluation's machinery phases**: one copy of the variable
machinery per spine position, and the output's. -/
noncomputable def PMF : Type :=
  (Σ j : Fin dt.nv, dt.VarPhF (dt.varAt j)) ⊕ dt.VarPhF none

/-- **The evaluation's phases**: the spine over the machineries. -/
@[reducible] noncomputable def PEF : Type := EvalPh dt.nv dt.PMF

/-- **The program's phases.** -/
@[reducible] noncomputable def PF : Type := OuterPh dt.PEF

/-! ### The site tower -/

/-- **The rule shape of the matrix's sites.** -/
noncomputable def MatrixSh (v : dt.VarIx) : dt.MatrixSite v → Type :=
  SeqSh (dt.natOf v) (dt.AtomSh v)

/-- **The rule shape of the gates' sites.** -/
noncomputable def GatesSh (v : dt.VarIx) : dt.GatesSite v → Type :=
  SeqSh (dt.arOf v) fun _ => dt.GateBlockSh

/-- **The rule shape of the inner gates' sites.** -/
noncomputable def IGatesSh (v : dt.VarIx) : dt.IGatesSite v → Type :=
  SeqSh (dt.nIn v) fun _ => dt.GateBlockSh

/-- **One round's machinery sites.** -/
noncomputable def RoundSiteF (v : dt.VarIx) : Type :=
  RoundSite (dt.IGatesSite v) (dt.MatrixSite v)

/-- **The rule shape of one round's machinery sites.** -/
noncomputable def RoundShF (v : dt.VarIx) : dt.RoundSiteF v → Type :=
  RoundSh (dt.IGatesSite v) (dt.MatrixSite v) (dt.IGatesSh v)
    (dt.MatrixSh v)

/-- **One variable's machinery sites.** -/
noncomputable def VarSiteF (v : dt.VarIx) : Type :=
  VarSite (dt.GatesSite v) (dt.RoundSiteF v)

/-- **The rule shape of one variable's machinery sites.** -/
noncomputable def VarShF (v : dt.VarIx) : dt.VarSiteF v → Type :=
  VarSh (dt.GatesSite v) (dt.RoundSiteF v) (dt.GatesSh v) (dt.RoundShF v)
    dt.CarryB

/-- **The evaluation's machinery sites.** -/
noncomputable def SMF : Type :=
  (Σ j : Fin dt.nv, dt.VarSiteF (dt.varAt j)) ⊕ dt.VarSiteF none

/-- **The rule shape of the evaluation's machinery sites.** -/
noncomputable def SMSh : dt.SMF → Type
  | Sum.inl ⟨j, s⟩ => dt.VarShF (dt.varAt j) s
  | Sum.inr s => dt.VarShF none s

/-- **The evaluation's sites.** -/
noncomputable def SEF : Type := EvalSite dt.nv dt.SMF

/-- **The rule shape of the evaluation's sites.** -/
noncomputable def SESh : dt.SEF → Type :=
  EvalSh dt.nv dt.SMF dt.SMSh

/-- **The program's sites.** -/
noncomputable def SF : Type := OuterSite dt.SEF

/-- **The rule shape of the program's sites.** -/
noncomputable def SFSh : dt.SF → Type :=
  OuterSh dt.SEF dt.SESh

end PfpData

/-! ### The owner maps of the tower

Each machinery's phases are owned by its sites – the per-shape maps live
with their rules (`DescriptiveComplexity.Pfp.elemOwn` and friends); the
maps below compose them up the tower. -/

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)

/-- The owner map of an atom kind's machinery. -/
noncomputable def kindOwn {n : ℕ} :
    ∀ κ : MatAtom dt.X dt.d.B n, dt.KindPh κ → dt.KindSite κ
  | .stage _ _ => stageOwn
  | @MatAtom.exp _ _ _ _ _ _ _ => tagOwn
  | .eq _ _ => elemOwn
  | .ord _ _ => elemOwn

/-- The owner map of a gate block. -/
noncomputable def gateBlockOwn : dt.GateBlockPh → dt.GateBlockSite
  | Sum.inl _ => Sum.inl ()
  | Sum.inr p => Sum.inr (tagOwn p)

/-- The owner map of one round's machinery. -/
noncomputable def roundOwnF (v : dt.VarIx) : dt.RoundPhF v → dt.RoundSiteF v :=
  roundOwn (seqOwn fun _ => dt.gateBlockOwn)
    (seqOwn fun a => dt.kindOwn (dt.kindOf v a))

/-- The owner map of one variable's machinery. -/
noncomputable def varOwnF (v : dt.VarIx) : dt.VarPhF v → dt.VarSiteF v :=
  varOwn (seqOwn fun _ => dt.gateBlockOwn) (dt.roundOwnF v)

/-- The owner map of the evaluation's machineries. -/
noncomputable def smOwn : dt.PMF → dt.SMF
  | Sum.inl ⟨j, p⟩ => Sum.inl ⟨j, dt.varOwnF (dt.varAt j) p⟩
  | Sum.inr p => Sum.inr (dt.varOwnF none p)

/-- The owner map of the evaluation's phases. -/
noncomputable def seOwn : dt.PEF → dt.SEF :=
  evalOwn (ownM := dt.smOwn)

/-- **The owner map of the program's phases.** -/
noncomputable def sfOwn : dt.PF → dt.SF :=
  outerOwner (ownE := dt.seOwn)

end PfpData

/-! ### Finiteness, up the tower

The machine's universe carries the phases (and the rule names) as tags, so
every type of the tower is finite; the instances go by injection into sums
of the components'. -/

instance {n : ℕ} {SS : Type} [Finite SS] : Finite (ChainSite n SS) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin n ⊕ SS)
      | .sub s => Sum.inr s)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {k : ℕ} : Finite (StagePh k) :=
  Finite.of_injective
    (fun p => match p with
      | .savP t => (Sum.inl (0, t) :
          (Fin 5 × TrackPh) ⊕ (Fin k × ChainPh 3 TuplePS) ⊕
            (Fin 2 × ResetPh) ⊕ (Fin 2 × SeekPh) ⊕ Fin 2)
      | .clrP t => Sum.inl (1, t)
      | .cm1P t => Sum.inl (2, t)
      | .resP t => Sum.inl (3, t)
      | .cm2P t => Sum.inl (4, t)
      | .tupP ℓ c => Sum.inr (Sum.inl (ℓ, c))
      | .rst1P r => Sum.inr (Sum.inr (Sum.inl (0, r)))
      | .rst2P r => Sum.inr (Sum.inr (Sum.inl (1, r)))
      | .skP s => Sum.inr (Sum.inr (Sum.inr (Sum.inl (0, s))))
      | .sk2P s => Sum.inr (Sum.inr (Sum.inr (Sum.inl (1, s))))
      | .cR1 => Sum.inr (Sum.inr (Sum.inr (Sum.inr 0)))
      | .cR2 => Sum.inr (Sum.inr (Sum.inr (Sum.inr 1))))
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {k : ℕ} : Finite (StageSite k) :=
  Finite.of_injective
    (fun p => match p with
      | .tup ℓ c => (Sum.inl (ℓ, c) : (Fin k × ChainSite 3 TupleSS) ⊕ Fin 11)
      | .sav => Sum.inr 0
      | .clr => Sum.inr 1
      | .cR1 => Sum.inr 2
      | .rst1 => Sum.inr 3
      | .cm1 => Sum.inr 4
      | .sk => Sum.inr 5
      | .res => Sum.inr 6
      | .cR2 => Sum.inr 7
      | .rst2 => Sum.inr 8
      | .cm2 => Sum.inr 9
      | .sk2 => Sum.inr 10)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {nr : ℕ} : Finite (ElemPh nr) :=
  Finite.of_injective
    (fun p => match p with
      | .rdP j r => (Sum.inl (j, r) : (Fin nr × ReadPh) ⊕ Fin 2)
      | .e0 => Sum.inr 0
      | .e1 => Sum.inr 1)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {nr : ℕ} : Finite (ElemSite nr) :=
  Finite.of_injective
    (fun p => match p with
      | .rd j => (Sum.inl j : Fin nr ⊕ Fin 2)
      | .e0 => Sum.inr 0
      | .e1 => Sum.inr 1)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {m : ℕ} {T : Type} [Finite T] {nrOf : T → ℕ} :
    Finite (TagPh m T nrOf) :=
  Finite.of_injective
    (fun p => match p with
      | .tagRdP i r => (Sum.inl (i, r) :
          (Fin m × ReadPh) ⊕ (Σ τ : T, ElemPh (nrOf τ)) ⊕ Fin 1)
      | .loopP τ p => Sum.inr (Sum.inl ⟨τ, p⟩)
      | .brP => Sum.inr (Sum.inr 0))
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {m : ℕ} {T : Type} [Finite T] {nrOf : T → ℕ} :
    Finite (TagSite m T nrOf) :=
  Finite.of_injective
    (fun p => match p with
      | .tagRd i => (Sum.inl i : Fin m ⊕ (Σ τ : T, ElemSite (nrOf τ)) ⊕ Fin 1)
      | .loop τ s => Sum.inr (Sum.inl ⟨τ, s⟩)
      | .br => Sum.inr (Sum.inr 0))
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {n : ℕ} {PA : Fin n → Type} [∀ a, Finite (PA a)] :
    Finite (SeqPh n PA) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin (n + 1) ⊕ Σ a : Fin n, PA a)
      | .sub a p => Sum.inr ⟨a, p⟩)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {n : ℕ} {SA : Fin n → Type} [∀ a, Finite (SA a)] :
    Finite (SeqSite n SA) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin (n + 1) ⊕ Σ a : Fin n, SA a)
      | .sub a s => Sum.inr ⟨a, s⟩)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {B PG PX : Type} [Finite B] [Finite PG] [Finite PX] :
    Finite (VarPh B PG PX) :=
  Finite.of_injective
    (fun p => match p with
      | .gatesP p => (Sum.inl p :
          PG ⊕ PX ⊕ TrackPh ⊕ TestPh ⊕ IncrPh B ⊕ Fin 4)
      | .matrixP p => Sum.inr (Sum.inl p)
      | .clearValP t => Sum.inr (Sum.inr (Sum.inl t))
      | .valTestP t => Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))
      | .valIncrP p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))
      | .vchk0 => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 0))))
      | .vchk1 => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 1))))
      | .mchk1 => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 2))))
      | .vchk2 => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 3)))))
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {SG SX : Type} [Finite SG] [Finite SX] : Finite (VarSite SG SX) :=
  Finite.of_injective
    (fun p => match p with
      | .gates s => (Sum.inl s : SG ⊕ SX ⊕ Fin 7)
      | .matrix s => Sum.inr (Sum.inl s)
      | .vchk0 => Sum.inr (Sum.inr 0)
      | .vchk1 => Sum.inr (Sum.inr 1)
      | .clearVal => Sum.inr (Sum.inr 2)
      | .mchk1 => Sum.inr (Sum.inr 3)
      | .valTest => Sum.inr (Sum.inr 4)
      | .valIncr => Sum.inr (Sum.inr 5)
      | .vchk2 => Sum.inr (Sum.inr 6))
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {nv : ℕ} {SM : Type} [Finite SM] : Finite (EvalSite nv SM) :=
  Finite.of_injective
    (fun p => match p with
      | .chk k => (Sum.inl k : Fin (nv + 1) ⊕ SM)
      | .sub s => Sum.inr s)
    (by intro a b h; cases a <;> cases b <;> simp_all)

instance {SE : Type} [Finite SE] : Finite (OuterSite SE) :=
  Finite.of_injective
    (fun p => match p with
      | .eval e => (Sum.inl e : SE ⊕ Fin 14)
      | .start => Sum.inr 0
      | .tgtTop => Sum.inr 1
      | .seek1 => Sum.inr 2
      | .reset1 => Sum.inr 3
      | .clearMir1 => Sum.inr 4
      | .sweepAdv => Sum.inr 5
      | .reset2 => Sum.inr 6
      | .clearMir2 => Sum.inr 7
      | .compare => Sum.inr 8
      | .homeCmp => Sum.inr 9
      | .copy => Sum.inr 10
      | .homeCopy => Sum.inr 11
      | .homeOut => Sum.inr 12
      | .accept => Sum.inr 13)
    (by intro a b h; cases a <;> cases b <;> simp_all)

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)

noncomputable instance {n : ℕ} (κ : MatAtom dt.X dt.d.B n) :
    Finite (dt.KindPh κ) := by
  cases κ with
  | stage i ts => exact inferInstanceAs (Finite (StagePh _))
  | exp e ts =>
    letI := Fintype.ofFinite dt.X.Tag
    exact inferInstanceAs (Finite (TagPh _ _ _))
  | eq j₁ j₂ => exact inferInstanceAs (Finite (ElemPh 2))
  | ord j₁ j₂ => exact inferInstanceAs (Finite (ElemPh 2))

noncomputable instance {n : ℕ} (κ : MatAtom dt.X dt.d.B n) :
    Finite (dt.KindSite κ) := by
  cases κ with
  | stage i ts => exact inferInstanceAs (Finite (StageSite _))
  | exp e ts =>
    letI := Fintype.ofFinite dt.X.Tag
    exact inferInstanceAs (Finite (TagSite _ _ _))
  | eq j₁ j₂ => exact inferInstanceAs (Finite (ElemSite 2))
  | ord j₁ j₂ => exact inferInstanceAs (Finite (ElemSite 2))

noncomputable instance (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    Finite (dt.AtomPh v a) :=
  inferInstanceAs (Finite (dt.KindPh (dt.kindOf v a)))

noncomputable instance (v : dt.VarIx) (a : Fin (dt.natOf v)) :
    Finite (dt.AtomSite v a) :=
  inferInstanceAs (Finite (dt.KindSite (dt.kindOf v a)))

noncomputable instance (v : dt.VarIx) : Finite (dt.MatrixPh v) :=
  inferInstanceAs (Finite (SeqPh _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.MatrixSite v) :=
  inferInstanceAs (Finite (SeqSite _ _))

noncomputable instance : Finite dt.GateBlockPh := by
  unfold GateBlockPh
  infer_instance

noncomputable instance : Finite dt.GateBlockSite := by
  unfold GateBlockSite
  infer_instance

noncomputable instance (v : dt.VarIx) : Finite (dt.GatesPh v) :=
  inferInstanceAs (Finite (SeqPh _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.GatesSite v) :=
  inferInstanceAs (Finite (SeqSite _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.IGatesPh v) :=
  inferInstanceAs (Finite (SeqPh _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.IGatesSite v) :=
  inferInstanceAs (Finite (SeqSite _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.RoundPhF v) :=
  inferInstanceAs (Finite (RoundPh _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.RoundSiteF v) :=
  inferInstanceAs (Finite (RoundSite _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.VarPhF v) :=
  inferInstanceAs (Finite (VarPh _ _ _))

noncomputable instance (v : dt.VarIx) : Finite (dt.VarSiteF v) :=
  inferInstanceAs (Finite (VarSite _ _))

noncomputable instance : Finite dt.PMF := by
  unfold PMF
  infer_instance

noncomputable instance : Finite dt.SMF := by
  unfold SMF
  infer_instance

noncomputable instance : Finite dt.PEF :=
  inferInstanceAs (Finite (EvalPh _ _))

noncomputable instance : Finite dt.SEF :=
  inferInstanceAs (Finite (EvalSite _ _))

noncomputable instance : Finite dt.PF :=
  inferInstanceAs (Finite (OuterPh _))

noncomputable instance : Finite dt.SF :=
  inferInstanceAs (Finite (OuterSite _))

end PfpData

end Pfp

end DescriptiveComplexity
