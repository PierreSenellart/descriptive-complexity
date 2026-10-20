/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxVerdict
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxPack
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawSpineSem
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawIxEval
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

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

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

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# What the spine does to the tape, at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawSpineSem` read at a coarse file: what a
whole spine leaves on the tape at one address, the sweep's fold over the
addresses, and the semantic packs the positions are run with.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R : Type}

variable [Fintype dt.SlotIx]

variable [LinearOrder A] [LinearOrder R]

variable {P : Type}

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

/-! ### One position's write -/

variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

/-! ### The spine's writes -/

section Spine

end Spine

/-! ### The spine's semantic reading -/

section SpineNext

end SpineNext

/-! ### What a whole sweep leaves behind -/

section SweepDict

end SweepDict

/-! ### The address's cell, in dictionary form -/

section AddrDict

end AddrDict

/-! ### The semantic pack, transported along the spine -/

/-! ### The per-position families, built -/

section Family

variable [LinearOrder (dt.X.Map A)]

variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}

variable (mV : ιV → I → Prop)

variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)

variable (st₀ : TapeSt dt A R (P) I)

variable (f₀ : dt.CtlIx → A)

variable (sem₀ : ∀ (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a))
      elt (dt.kindOf (dt.varAt j) b))

variable (tOf : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)

/-! ### The per-position families, threaded -/

/-! ### The per-position families, branched

The threaded family above runs the gated leg at every position, which a
sweep cannot afford: it visits junk addresses too. The branched family
takes whichever of the three legs each position's own gates call for
(`DescriptiveComplexity.Draw.Data.ixLegStB`), and is otherwise the same
recursion – the mirror still rides, because no leg writes it.

Its semantic parameter is **not** the entry state's pack transported: it is
the *conditioned* family `DescriptiveComplexity.Draw.Data.ixGatedSem`
inhabits – a pack at every gated position of every state, at every address.
Conditioned, because at a junk position no pack exists (the argument blocks
encode nothing there); quantified over the address as well, because the sweep runs this spine at
`v := w` for an address `w` its own binders are fixed before. With that type the
parameter is supplied outright at the top – `fun w => dt.ixGatedSem hzo hlin
mV` – and no semantic assumption about a position survives in the run
layer. -/

variable (semB : ∀ (w : Univ A R (P) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
  ∀ (p : IxScratch dt A R (P) I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b))

/-- **One node of the spine, branched**. -/
noncomputable def ixSpineNodeB :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNodeB n
    if h : n < dt.nv then
      ⟨dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2,
        (dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2).1.trans prev.2.1,
        dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2⟩
    else prev

/-- The branched tape family of the spine. -/
noncomputable def ixSpineStOfB (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).1

/-- The branched control family of the spine. -/
noncomputable def ixSpineFsOfB (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.2

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the branched family** – by construction. -/
theorem ixSpineStOfB_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).mir = st₀.mir :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.1

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The marker rides the branched family**: no leg writes the working
register, so the `hwkOf` a spine asks for is the entry state's. -/
theorem ixSpineStOfB_wk (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).wk = st₀.wk := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.wk = st₀.wk := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The bottom mark rides the branched family** – the `hbotOf` a spine asks
for. -/
theorem ixSpineStOfB_bot (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).bot = st₀.bot := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.bot = st₀.bot := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The dictionary rides the branched family**: no leg of the evaluation
writes the `old` tracks, so the stage the spine reads at its last checkpoint is
the stage it was entered with. This is what lets a *guessing* program discharge
the output's `hdict`: what its guess wrote is what the verdict is read
against. -/
theorem ixSpineStOfB_old (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).old = st₀.old := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.old = st₀.old := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dif_pos hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.2.1).trans ih
      · rw [dif_neg hm]
        exact ih
  exact hn (k : ℕ)

/-- The packs of the branched family: the parameter's own, at the position's
state – the gate being what makes them exist. -/
noncomputable def ixSpineSemOfB (j : Fin dt.nv)
    (hg : dt.ixGatedAt (PR := PR) (elt := elt) F j
      (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV st₀ f₀ semB j.castSucc))
    (p : IxScratch dt A R (P) I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) v (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b) :=
  semB v j (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB j.castSucc) hg p a
    hp b

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched control's cover equation** –
`DescriptiveComplexity.Draw.Data.nexIxSpineB_reachesIn`'s `hfs`. -/
theorem ixSpineFsOfB_succ (j : Fin dt.nv) :
    dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).2.2 = _
  rw [ixSpineNodeB, dif_pos j.isLt]
  rfl

omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched tape's cover equation** –
`DescriptiveComplexity.Draw.Data.nexIxSpineB_reachesIn`'s `hst`. -/
theorem ixSpineStOfB_succ (j : Fin dt.nv) :
    dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).1 = _
  rw [ixSpineNodeB, dif_pos j.isLt]
  rfl

/-! ### The branched spine's dictionary at one address

Gating is per variable, and so is the reading: at an address whose blocks
below a variable's arity all encode points, that variable's cell holds one
step of the iteration there; where one of them does not, the position takes
an ungated leg, writes `False`, and the dictionary is `False` too. Nothing
is assumed of the *other* variables' blocks – which is what a sweep needs,
since it passes every address. -/

include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **The verdict the output's leg leaves is the output sentence**, at the
stage the tracks hold. The output variable is nullary, so its blocks encode
the empty tuple and there is nothing to ask of them – which is why this is the
one verdict a program can take at the address its head starts on. This is the
`hacc` a run through the output's machinery
(`DescriptiveComplexity.Draw.Data.nexIxEvalOutB_reachesIn`) asks for, and the
reason the accepting bit says anything at all. -/
theorem ixOutAcc_iff_out
    (hlin : Lax904597.Machines.IsLinOrd (Lax822549.WideMachines.WMLe (A := Univ A R (P) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd, Lax822549.WideMachines.WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R (P) dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (st : TapeSt dt A R (P) I)
    {Below : (Univ A R (P) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP none ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (f₀ : dt.CtlIx → A) :
    (dt.varArgsOf PR.zero PR.one none).accBit
        (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf
          (fun a hp b => dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
            none (dt.ixRoundSt st (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
          f₀) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out :=
  dt.ixAccVerdict_out (elt := elt) (F := F) (hinj := hinj) (hhasP := hhasP)
    (heltP := heltP) (hix := hix) (hblkP := hblkP) (hmono := hmono) (hup := hup)
    (hpassEnc := hpassEnc) (st := st) (mV := mV) (hlin := hlin) (hord := hord)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
    (hKin := hKin) (hTop := hTop) (σ := σ) (hdict := hdict) (hbelow := hbelow)
    (hordP := hordP) (hsem := fun _ _ _ => rfl) (fG := _)

end Family

/-! ### The sweep's families, over an arbitrary per-address leg

Everything the sweep's families need of an address's evaluation is *what
state and control it ends in*. Taking those two as parameters makes the
whole layer – the iteration, its two cover equations, and the ride lemmas
that discharge `reaches_sweep`'s `hwkE`/`hmirE`/`hltpE` – serve any
evaluation: the spine as first built, its threaded twin, and the branched
form a junk address will need. -/

section SweepGen

end SweepGen

/-! ### The sweep's families -/

/-! ### The stage atom's restore, as an algebra

`DescriptiveComplexity.Draw.Data.stageEndSt st v = { st with sav := v,
tgt := v }`: the random access **writes** the home address into SAV and
TARGET whatever they held, so a stage atom is transparent exactly when they
held it already – which is what `ixStageEndSt_eq`'s two hypotheses say, and
why they are not a proof artifact.

Closing the sweep's gap by “reading the mirror” therefore means *threading*
that normalization rather than assuming it away: an atom's exit state is
`ixStageEndSt st v`, and the layers above carry it. These are the equations
that threading needs; they are all definitional, which is what makes the
propagation mechanical. -/

section StageEnd

end StageEnd

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


