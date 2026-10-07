/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxEval
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxRoundSem
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxBridge
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMLe)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax822549Proofs.DescriptiveComplexity

/-!
# A gated position's semantic pack, at an arbitrary file and phase

What a leg of the evaluation is run with is a *pack* per position and VAL
content: the points the position's argument blocks encode. This file builds
them – it does not assume them – from the two bridges a coarse file needs
(`hpassEnc`, `hgateEnc`) and nothing else, so the space-bounded program and the
clocked one get their packs from the same place.

The construction is one step: a gated position's blocks are encodings
(`ixIsEnc_of_gatedAt`, the bridge read forwards), and `ixPassSem` turns
encodings into a pack. `ixGatedSem` is that pack at the state the matrix's
atoms run at, `ixGatedSem₀` at the round's own, and `ixGatedSem_eq_semCastT`
says the first is the second transported – which is what the VAL loop's bridge
asks of a threaded family. The transport lemmas under them
(`ixPassW_congr`, `ixKindSemCast_passSem`, and the one-pack family) say the same
thing once: a pack sees the state through the mirror and VAL alone.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}

variable [Fintype dt.SlotIx]

variable [LinearOrder A] [LinearOrder R]

variable [LinearOrder (P)]

variable [Lax822549.WideMachines.wide.Structure
  (Univ A R (P) dt.KIx dt.dd)]

variable [Finite A] [Finite R] [Finite (P)]

variable {PR : Prog A R (P) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}

variable {I : Type} [Finite I]

variable (F : LaidFile dt A R (P) I)

variable {elt : I → Univ A R (P) dt.KIx dt.dd}

variable (hinj : Function.Injective elt)

variable (hhasP : F.toLayout.HasName PR.zero)

variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))

variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : Lax904597.Machines.IsLinOrd F.le)

variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)

variable {e₀ : Univ A R (P) dt.KIx dt.dd}

variable (he₀ : ∀ y, Lax822549.WideMachines.WMLe e₀ y)

variable {Use : I → Prop}

variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt Lax822549.WideMachines.WMLe (elt u) (elt u'))

variable (hup : ∀ (u : I) (x : Univ A R (P) dt.KIx dt.dd),
  Use u → WMLt Lax822549.WideMachines.WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)

variable (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
  Lax822549.WideMachines.WMLe x y ↔ tagTupleLe x y)

variable [Nonempty A] [L.IsRelational] [L.Structure A]

variable (hpassEnc : ∀ (vi : dt.VarIx)
    (stV : TapeSt dt A R (P) I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
    IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr elt stV.val)
      (Tag.arg (toLex (dt.igBlk vi ℓ)) :
        Tag R (P) dt.KIx)))

variable (hgateEnc : ∀ (j : Fin dt.nv)
    (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st ↔
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx)))

variable [Finite dt.KIx]

variable {v : Univ A R P dt.KIx dt.dd → Prop}

section PackCast

section OnePack

end OnePack

end PackCast

section GatedPack

variable [LinearOrder (dt.X.Map A)]

/-! ### What a gated position knows

The branch `DescriptiveComplexity.Draw.Data.ixGatedAt` takes is not merely
the one where the machine runs the machinery: it is the one where the
argument blocks **are** encodings, which is what a semantic pack needs to
exist at all. `DescriptiveComplexity.Draw.Data.gate_trichotomy` says the
three legs are exhaustive; read in the other direction it says a gated
position's blocks encode points. -/

include hgateEnc in
omit [Finite I] [LinearOrder (dt.X.Map A)]
  [Finite (P)] [Finite dt.KIx] [L.IsRelational]
  [Finite R] in
/-- **A gated position's argument blocks are encodings** – the converse of
`testOf_of_encMap`/`wit_of_encMap`/`domHolds_of_encMap`, off the
trichotomy. This is what makes a position's semantic pack *constructible*
rather than assumed: at a junk position no pack exists, and at a gated one
the points are the blocks' own. -/
theorem ixIsEnc_of_gatedAt (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st)
    (ℓ : Fin (dt.arOf (dt.varAt j))) :
    IsEnc dt.ly PR.zero PR.one
      (wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R P dt.KIx)) :=
  (hgateEnc j st).mp hg ℓ

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hgateEnc in
/-- **A gated position's semantic pack, built** – not assumed. The blocks
are encodings (`ixIsEnc_of_gatedAt`), so their points are the valuation the
pass decodes, and `ixPassSem` builds the pack there; `ixKindSemCast` carries it
to the state the matrix's atoms run at, which differs from it in the two
scratch registers alone. This is what a branched leg's `semT` is. -/
noncomputable def ixGatedSem (_hzo : PR.zero ≠ PR.one)
    (_hlin : Lax904597.Machines.IsLinOrd
      (Lax822549.WideMachines.WMLe (A := Univ A R P dt.KIx dt.dd)))
    {v : Univ A R P dt.KIx dt.dd → Prop}
    {ιV : Type} (mV : ιV → I → Prop)
    (j : Fin dt.nv) (st : TapeSt dt A R P I)
    (hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st)
    (p : IxScratch dt A R P I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b) :=
  dt.ixKindSemCast PR.zero PR.one (dt.varAt j)
    ((dt.ixMatSt_fields (v := v)
      (st := dt.ixVarRdSt st p (mV a)) (b : ℕ)).2.1).symm
    ((dt.ixMatSt_fields (v := v)
      (st := dt.ixVarRdSt st p (mV a)) (b : ℕ)).2.2.2.1).symm
    (dt.kindOf (dt.varAt j) b)
    (dt.ixPassSem (elt := elt)
      (F := F) (hpassEnc := hpassEnc) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) hp
      (fun ℓ => (ixIsEnc_of_gatedAt (dt := dt) (elt := elt) (F := F) (hgateEnc := hgateEnc)
        j st hg ℓ).choose)
      (fun ℓ => (ixIsEnc_of_gatedAt (dt := dt) (elt := elt) (F := F) (hgateEnc := hgateEnc)
        j st hg ℓ).choose_spec) b)

end GatedPack

/-! ### The gates' bridge, proved

`hgateEnc` is a hypothesis of the layers above because an arbitrary file need
not have a register for every element it is asked about. Where it does – any
file laid by blocks and tuples – the bridge is the elementwise one
(`gate_trichotomy` and `testOf_of_encMap`) read through
`DescriptiveComplexity.Draw.Data.wellShapedG_ixBack_iff`. -/

section GateBridge

omit [Finite R] [Finite P] [Finite I] [L.IsRelational] [Finite dt.KIx] in
include hinj hix hblkP in
/-- **The gates' bridge at a coarse file, proved**: a position is gated exactly
when the blocks of its mirror's *address* below the variable's arity are
encodings. This is `hgateEnc`, at any file whose registers stand for elements,
whose tuples are their elements' (`hargP`). Nothing has to be said about which
elements have registers: a failing element is one the address holds, hence a
register's already. -/
theorem ixGatedAt_iff_isEnc (RF : RegFile (Univ A R P dt.KIx dt.dd))
    (hargP : ∀ u : I, F.arg u = (elt u).2)
    (hzo : PR.zero ≠ PR.one)
    (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R P dt.KIx dt.dd)))
    (j : Fin dt.nv) (st : TapeSt dt A R P I) :
    dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st ↔
      ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        IsEnc dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) : Tag R P dt.KIx)) := by
  classical
  have := Fintype.ofFinite A
  have hcellinj : Function.Injective F.cell := F.toIxFile.injective hix
  have hpass : ∀ (u : I),
      PR.passTracksAt F.cell Slot.mir
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir (F.cell u) =
        dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st (F.cell u) :=
    fun u => passTracks_of_back (PR := PR) (t := Slot.mir)
      (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (m := st.mir)
      F.toIxFile (fun _ => rfl) (F.cell u)
  constructor
  · -- gated ⇒ encodings: the trichotomy's other two cases are what gating rules out
    rintro ⟨hshape, htag⟩ ℓ
    rcases ix_gate_trichotomy (lay := F.toLayout) (elt := elt) RF hcellinj hinj
      hblkP hargP hzo hlin st
      (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) with h | ⟨u₀, hbad⟩ | ⟨-, hbad⟩
    · exact h
    · exact absurd (by
        rw [← hpass u₀]
        exact hshape ℓ u₀) hbad
    · exact absurd (htag ℓ) hbad
  · -- encodings ⇒ gated: the shape test at a register is the elementwise one
    intro henc
    refine ⟨fun ℓ u => ?_, fun ℓ => ?_⟩
    · obtain ⟨p, hp⟩ := henc ℓ
      rw [ixShapeAt, hpass u]
      refine (wellShapedG_ixBack_iff (lay := F.toLayout) (elt := elt)
        hcellinj hinj hblkP hargP hzo st _ u).mpr ?_
      have hdiag := (wellShapedG_ixBack_iff (lay := dt.diagLayout RF.cell)
        (elt := id) (RF.injective hlin) Function.injective_id (fun _ => rfl)
        (fun _ => rfl) hzo
        ({ mir := ixAddr elt st.mir, tgt := ixAddr elt st.tgt,
           sav := ixAddr elt st.sav, val := ixAddr elt st.val, old := st.old,
           new := st.new, wk := st.wk, bot := st.bot, ltp := st.ltp } :
          TapeStD dt A R P)
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) (elt u)).mp
        (dt.testOf_of_encMap RF hzo hlin hp (elt u))
      intro hb hm
      exact hdiag hb (by rw [ixAddr_id] at *; exact hm)
    · obtain ⟨p, hp⟩ := henc ℓ
      have htagEq : dt.ixTagAt (PR := PR) (elt := elt) j st ℓ = p.1.1 :=
        dt.dspTagOf_encMap hzo hp
      refine ⟨fun t' => ?_, ?_⟩
      · rw [htagEq]
        exact dt.wit_of_encMap hzo hp t'
      · rw [htagEq]
        exact dt.domHolds_of_encMap hzo hp

omit [Finite R] [Finite P] [Finite I] [L.IsRelational] [Finite dt.KIx] in
include hinj hix hblkP in
/-- **The inner gates' bridge at a coarse file, proved**: a level's gate passes
exactly when the block of VAL's *address* is an encoding. This is `hpassEnc`,
and it asks *less* than the gates' bridge did: only that the registers stand for
elements and that their tuples are their elements'. Nothing has to be said about
which elements have registers, because the members of the block are the marked
registers' own tuples. The verdict half is
`DescriptiveComplexity.Draw.Data.igVerdict_iff_isEnc`, which asks only that
the block's members be encoding-shaped, and that is what the shape test says. -/
theorem ixIGPassP_iff_isEnc
    (hargP : ∀ u : I, F.arg u = (elt u).2)
    (hzo : PR.zero ≠ PR.one)
    (vi : dt.VarIx) (stV : TapeSt dt A R P I) (ℓ : Fin (dt.nIn vi)) :
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt stV.val)
          (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)) := by
  classical
  have hcellinj : Function.Injective F.cell := F.toIxFile.injective hix
  constructor
  · rintro ⟨htest, hone, hdom⟩
    refine (dt.igVerdict_iff_isEnc hzo ?_).mp ⟨hone, hdom⟩
    -- every member of the block is an encoding shape: it is a register's tuple,
    -- and the shape test passed there
    rintro w ⟨u, he, hv⟩
    have hblk : tagBlk (elt u).1 = some (dt.igBlk vi ℓ) := by
      rw [he]
      exact (tagBlk_eq_some_iff _ _).mpr rfl
    have hval : ixAddr elt stV.val (elt u) := ⟨u, rfl, hv⟩
    obtain ⟨hpdd, hn⟩ :=
      (wellShapedIG_ixBack_iff (lay := F.toLayout) (elt := elt) hcellinj hinj
        hblkP hargP hzo stV (dt.igBlk vi ℓ) u).mp (htest u) hblk hval
    have h2 : (elt u).2 = w := congrArg Prod.snd he
    rcases hn with ⟨t, ht⟩ | ⟨i, w', hw'⟩
    · exact Or.inl ⟨t, h2 ▸ dt.eq_encTup_of_marks hpdd ht⟩
    · exact Or.inr ⟨i, w', h2 ▸ dt.eq_encTup_of_marks hpdd hw'⟩
  · rintro ⟨p, hp⟩
    refine ⟨fun u => ?_, ?_, ?_⟩
    · refine (wellShapedIG_ixBack_iff (lay := F.toLayout) (elt := elt) hcellinj
        hinj hblkP hargP hzo stV (dt.igBlk vi ℓ) u).mpr ?_
      intro hblk hval
      have htag : (elt u).1 = (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx) :=
        (tagBlk_eq_some_iff _ _).mp hblk
      have hmem : encMap dt.ly PR.zero PR.one p ((elt u).2) := by
        rw [← hp]
        change ixAddr elt stV.val
          ((Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx), (elt u).2)
        rw [← htag]
        exact (by exact hval : ixAddr elt stV.val (elt u))
      have hshape : (∃ t : dt.X.Tag,
            (elt u).2 = encTagTup dt.ly PR.zero PR.one t) ∨
          ∃ (i : dt.X.B.ι) (w : Fin (dt.X.B.arity i) → A),
            (elt u).2 = encAsgTup dt.ly PR.zero PR.one i w := by
        rcases hmem with h | ⟨i, w, -, h⟩
        · exact Or.inl ⟨p.1.1, h⟩
        · exact Or.inr ⟨i, w, h⟩
      refine ⟨?_, ?_⟩
      · rcases hshape with ⟨t, ht⟩ | ⟨i, w, hw⟩
        · rw [ht]
          exact fun j hj => dt.encTup_pdd _ _ hj
        · rw [hw]
          exact fun j hj => dt.encTup_pdd _ _ hj
      · rcases hshape with ⟨t, ht⟩ | ⟨i, w, hw⟩
        · exact Or.inl ⟨t, fun j => by rw [ht]⟩
        · exact Or.inr ⟨i, w, fun j => by rw [hw]⟩
    · rw [dt.dspTagOf_encMap hzo hp]
      exact dt.wit_of_encMap hzo hp
    · rw [dt.dspTagOf_encMap hzo hp]
      exact dt.domHolds_of_encMap hzo hp

end GateBridge

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


