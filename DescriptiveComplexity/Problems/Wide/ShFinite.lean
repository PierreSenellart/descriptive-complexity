/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpProg

/-!
# The rule names of the EXPSPACE program are finitely many

`DescriptiveComplexity.Problems.Wide.PfpTower` gives every **site** type of the
program's tower a `Finite` instance, and every leaf kit's rule type has one where
it is defined; what was missing is the tower's **shapes** – the rules each site
contributes – and hence the rule names themselves, which the run layer asks for
as the hypothesis `Finite (dt.RIx …)` and which an interpretation needs of its
tag type.

There is no mathematics here: a shape is a match on a site whose leaves are a
kit's rules, a sum of them with a verdict, or the shape one level down, so each
instance is one line per constructor. They are stated at the abstract
machineries first (`ChainSh`, `SeqSh`, `ElemSh`, `StageSh`, `TagSh`, `RoundSh`,
`VarSh`, `EvalSh`, `OuterSh`), then read up the concrete tower to
`DescriptiveComplexity.Pfp.PfpData.SFSh`, and the file ends at
`DescriptiveComplexity.Pfp.PfpData.finite_RIx`.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language

/-! ### The branch rules of a tag dispatch -/

instance {T : Type} [Finite T] : Finite (BrRule T) :=
  Finite.of_injective
    (fun r => match r with
      | .stay => (none : Option T)
      | .dsp t => some t)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-! ### The shapes of the abstract machineries -/

instance instFiniteTupleSh : ∀ c, Finite (TupleSh c)
  | false => inferInstanceAs (Finite (ReadRule ⊕ Bool))
  | true => inferInstanceAs (Finite (WriteRule ⊕ Unit))

instance instFiniteChainSh {n : ℕ} {SS : Type} {ShS : SS → Type} [∀ s, Finite (ShS s)] :
    ∀ c, Finite (ChainSh n SS ShS c)
  | .chk _ => inferInstanceAs (Finite EvalChkRule)
  | .sub s => inferInstanceAs (Finite (ShS s))

instance instFiniteElemSh {nr : ℕ} : ∀ c, Finite (ElemSh nr c)
  | .e0 => inferInstanceAs (Finite EvalChkRule)
  | .rd _ => inferInstanceAs (Finite (ReadRule ⊕ Bool))
  | .e1 => inferInstanceAs (Finite EvalChkRule)

instance instFiniteStageSh {k : ℕ} : ∀ c, Finite (StageSh k c)
  | .sav => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .clr => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .tup _ c => inferInstanceAs (Finite (ChainSh 3 TupleSS TupleSh c))
  | .cR1 => inferInstanceAs (Finite EvalChkRule)
  | .rst1 => inferInstanceAs (Finite (ResetRule ⊕ Unit))
  | .cm1 => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .sk => inferInstanceAs (Finite (SeekRule ⊕ Bool))
  | .res => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .cR2 => inferInstanceAs (Finite EvalChkRule)
  | .rst2 => inferInstanceAs (Finite (ResetRule ⊕ Unit))
  | .cm2 => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .sk2 => inferInstanceAs (Finite (SeekRule ⊕ Unit))

instance instFiniteTagSh {m : ℕ} {T : Type} [Finite T] {nrOf : T → ℕ} :
    ∀ c, Finite (TagSh m T nrOf c)
  | .tagRd _ => inferInstanceAs (Finite (ReadRule ⊕ Bool))
  | .br => inferInstanceAs (Finite (BrRule T))
  | .loop τ s => inferInstanceAs (Finite (ElemSh (nrOf τ) s))

instance instFiniteSeqSh {n : ℕ} {SA : Fin n → Type} {ShA : ∀ a : Fin n, SA a → Type}
    [∀ a s, Finite (ShA a s)] : ∀ c, Finite (SeqSh n ShA c)
  | .chk _ => inferInstanceAs (Finite EvalChkRule)
  | .sub a s => inferInstanceAs (Finite (ShA a s))

instance instFiniteRoundSh {SG SX : Type} {ShG : SG → Type} {ShX : SX → Type}
    [∀ s, Finite (ShG s)] [∀ s, Finite (ShX s)] :
    ∀ c, Finite (RoundSh SG SX ShG ShX c)
  | .ig s => inferInstanceAs (Finite (ShG s))
  | .rchk => inferInstanceAs (Finite EvalChkRule)
  | .mat s => inferInstanceAs (Finite (ShX s))

instance instFiniteVarSh {SG SX B : Type} {ShG : SG → Type} {ShX : SX → Type}
    [∀ s, Finite (ShG s)] [∀ s, Finite (ShX s)] [Finite B] :
    ∀ c, Finite (VarSh SG SX ShG ShX B c)
  | .vchk0 => inferInstanceAs (Finite EvalChkRule)
  | .gates s => inferInstanceAs (Finite (ShG s))
  | .vchk1 => inferInstanceAs (Finite EvalChkRule)
  | .clearVal => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .matrix s => inferInstanceAs (Finite (ShX s))
  | .mchk1 => inferInstanceAs (Finite EvalChkRule)
  | .valTest => inferInstanceAs (Finite (TestRule ⊕ Bool))
  | .valIncr => inferInstanceAs (Finite (IncrRule B ⊕ B))
  | .vchk2 => inferInstanceAs (Finite EvalChkRule)

instance instFiniteEvalSh {nv : ℕ} {SM : Type} {ShM : SM → Type} [∀ s, Finite (ShM s)] :
    ∀ c, Finite (EvalSh nv SM ShM c)
  | .chk _ => inferInstanceAs (Finite EvalChkRule)
  | .sub s => inferInstanceAs (Finite (ShM s))

instance instFiniteOuterSh {SE : Type} {ShE : SE → Type} [∀ s, Finite (ShE s)] :
    ∀ c, Finite (OuterSh SE ShE c)
  | .start => inferInstanceAs (Finite Unit)
  | .tgtTop => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .seek1 => inferInstanceAs (Finite (SeekRule ⊕ Unit))
  | .reset1 => inferInstanceAs (Finite (ResetRule ⊕ Unit))
  | .clearMir1 => inferInstanceAs (Finite (TrackRule ⊕ Unit))
  | .sweepAdv => inferInstanceAs (Finite (AdvRule ⊕ Unit))
  | .reset2 => inferInstanceAs (Finite (ResetRule ⊕ Unit))
  | .clearMir2 => inferInstanceAs (Finite (TrackRule ⊕ Bool))
  | .compare => inferInstanceAs (Finite (SweepRule ⊕ Bool))
  | .homeCmp => inferInstanceAs (Finite (HomeKit.HomeRule ⊕ Unit))
  | .copy => inferInstanceAs (Finite (WSweepRule ⊕ Unit))
  | .homeCopy => inferInstanceAs (Finite (HomeKit.HomeRule ⊕ Unit))
  | .homeOut => inferInstanceAs (Finite (HomeKit.HomeRule ⊕ Unit))
  | .accept => inferInstanceAs (Finite Empty)
  | .eval e => inferInstanceAs (Finite (ShE e))

/-! ### And of the concrete tower -/

namespace PfpData

variable {L : Language.{0, 0}} (dt : PfpData L)

noncomputable instance instFiniteKindSh {n : ℕ} :
    ∀ (κ : MatAtom dt.X dt.d n) (s : dt.KindSite κ), Finite (dt.KindSh κ s)
  | .stage i _, s => instFiniteStageSh (k := dt.d.B.arity i) s
  | @MatAtom.exp _ _ _ _ k e _, s =>
    letI := Fintype.ofFinite dt.X.Tag
    instFiniteTagSh (m := k * Fintype.card dt.X.Tag) (T := Fin k → dt.X.Tag)
      (nrOf := dt.relNr e) s
  | .eq _ _, s => instFiniteElemSh (nr := 2) s
  | .ord _ _, s => instFiniteElemSh (nr := 2) s

noncomputable instance instFiniteAtomSh (v : dt.VarIx) (a : Fin (dt.natOf v))
    (s : dt.AtomSite v a) : Finite (dt.AtomSh v a s) :=
  instFiniteKindSh dt (dt.kindOf v a) s

noncomputable instance instFiniteGateBlockSh :
    ∀ s : dt.GateBlockSite, Finite (dt.GateBlockSh s)
  | Sum.inl _ => inferInstanceAs (Finite (TestRule ⊕ Bool))
  | Sum.inr s =>
    letI := Fintype.ofFinite dt.X.Tag
    instFiniteTagSh (m := Fintype.card dt.X.Tag) (T := dt.X.Tag) (nrOf := dt.domNr) s

noncomputable instance instFiniteMatrixSh (v : dt.VarIx) (s : dt.MatrixSite v) :
    Finite (dt.MatrixSh v s) :=
  instFiniteSeqSh (n := dt.natOf v) (ShA := dt.AtomSh v) s

noncomputable instance instFiniteGatesSh (v : dt.VarIx) (s : dt.GatesSite v) :
    Finite (dt.GatesSh v s) :=
  instFiniteSeqSh (n := dt.arOf v) (ShA := fun _ => dt.GateBlockSh) s

noncomputable instance instFiniteIGatesSh (v : dt.VarIx) (s : dt.IGatesSite v) :
    Finite (dt.IGatesSh v s) :=
  instFiniteSeqSh (n := dt.nIn v) (ShA := fun _ => dt.GateBlockSh) s

noncomputable instance instFiniteRoundShF (v : dt.VarIx) (s : dt.RoundSiteF v) :
    Finite (dt.RoundShF v s) :=
  instFiniteRoundSh (ShG := dt.IGatesSh v) (ShX := dt.MatrixSh v) s

noncomputable instance instFiniteVarShF (v : dt.VarIx) (s : dt.VarSiteF v) :
    Finite (dt.VarShF v s) :=
  instFiniteVarSh (ShG := dt.GatesSh v) (ShX := dt.RoundShF v) (B := dt.CarryB) s

noncomputable instance instFiniteSMSh : ∀ s : dt.SMF, Finite (dt.SMSh s)
  | Sum.inl ⟨j, s⟩ => instFiniteVarShF dt (dt.varAt j) s
  | Sum.inr s => instFiniteVarShF dt none s

noncomputable instance instFiniteSESh (s : dt.SEF) : Finite (dt.SESh s) :=
  instFiniteEvalSh (nv := dt.nv) (ShM := dt.SMSh) s

noncomputable instance instFiniteSFSh (s : dt.SF) : Finite (dt.SFSh s) :=
  instFiniteOuterSh (ShE := dt.SESh) s

/-! ### The rule names -/

/-- **The rule names of the program are finitely many**: a site and one of its
rules, both of finitely many. This is the hypothesis the run layer carries and
the finiteness an interpretation needs of its tag type. -/
noncomputable instance finite_RIx {A Q : Type} [Fintype Q] [Fintype dt.SlotIx]
    [LinearOrder A] {zero one : A} (hzo : zero ≠ one)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v) :
    Finite (dt.RIx zero one hzo args) :=
  inferInstanceAs (Finite ((i : dt.SF) × dt.SFSh i))

end PfpData

end Pfp

end DescriptiveComplexity
