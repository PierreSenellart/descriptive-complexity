/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexDef
import DescriptiveComplexity.Problems.Wide.DrawInterp

/-!
# The clocked machine, written down

`DescriptiveComplexity.Draw.Data.reads_progFrom` says of a program that the
interpreted structure reads its table, and it says it of
`DescriptiveComplexity.Draw.Data.progFrom` – the program assembled from a
definable rule set, a start phase, an accepting predicate and an initial mark.
The clocked program is written by hand (`DescriptiveComplexity.Draw.Data.nexProg`),
so what is needed here is that the two are the *same program*: they differ in
one field only, the initial pointer, and there the file's first register carries
the least tuple, which is clear at every coordinate.

With that, the clocked machine is written down exactly as the space-bounded one
is: `nexInterp` is the interpretation and `reads_nexProg` the fact a reduction
hands the run layer. What is left to a reduction emitting it is its own
`DescriptiveComplexity.Draw.Data.VarArgs`, the obligation the space-bounded
reduction already meets.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} {dt : Data L}
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] [Finite dt.KIx] [Nonempty dt.KIx]

/-- **The clocked program's rule names**, as the interpretation names them: a
site of the outer layer or of the evaluation, and one of that site's rules. -/
abbrev NexRTag (dt : Data L) (G : Type) : Type :=
  RTagOf (NexSite dt.SEF) (NexSh dt.SEF (Option dt.KIx) G dt.NexSESh)

/-- **The clocked program's phases.** -/
abbrev NexPF (dt : Data L) : Type := NexPh (Option dt.KIx) (EvalPh dt.nv dt.PMF)

/-- **The tags of the clocked machine's universe.** -/
abbrev NexITag (dt : Data L) (G : Type) : Type :=
  dt.ITagOf (NexSite dt.SEF) (NexSh dt.SEF (Option dt.KIx) G dt.NexSESh) dt.NexPF

variable {G : Type}

/-- **The clocked program is the program the interpretation writes down**: the
rules are the same function of the rule name, the start phase, the accepting
predicate and the blank tape are the same, and the initial pointer – the file's
first register – is clear at every coordinate, because the least index of the
layout carries the least tuple. -/
theorem nexProg_eq_progFrom (e : Env L)
    (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (coord : Fin dt.dd → dt.CtlIx)
    (β : SweepSpec e.α dt.CtlIx dt.SlotIx (Option dt.KIx))
    (γ : GuessSpec e.α dt.CtlIx dt.SlotIx (Option dt.KIx) G)
    (args : ∀ v : dt.VarIx, dt.VarArgs (A := e.α) (Q := dt.CtlIx) v)
    (bot : Option dt.KIx) :
    dt.nexProg e.zero e.one e.hzo hpl coord β γ args bot =
      dt.progFrom hpl e
        (fun i ρ => dt.nexRule e.one β γ
          (dt.nexEvalRuleF e.zero e.one args) (.chk 0) bot i ρ)
        NexPh.start (fun p f => p = NexPh.acceptP ∧ (args none).accBit f)
        blankMark := by
  have hst : dt.ctlOf coord (fun _ => e.zero) (blkBot e.α dt.KIx dt.dd).2 =
      fun _ => e.zero := by
    funext q
    rw [ctlOf]
    split
    · exact snd_blkBot_apply e.hbot _
    · rfl
  simp only [nexProg, progFrom, hst]
  rfl

/-! ### The interpretation, and what it reads

The clocked program's guess writes one bit per fixed-point variable of the
source, so the guessed data of its outer layer is `dt.d.B.ι → Bool`; that is the
rule names' second component, and the reduction supplies the two orders on the
names and the phases (any linear order will do – they are finite types). -/

variable [LinearOrder (dt.NexRTag (dt.d.B.ι → Bool))] [LinearOrder dt.NexPF]
variable {coord : Fin dt.dd → dt.CtlIx}
variable {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}

/-- **The clocked machine, written down**: the interpretation of the
wide-machine vocabulary whose universe is tagged by the clocked program's own
rule names and phases. -/
noncomputable def nexInterp (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (hcoord : Function.Injective coord)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v)
    (bot : Option dt.KIx) :
    FOInterpretation (L.sum Language.order) Language.wide
      (dt.NexITag (dt.d.B.ι → Bool)) dt.dd :=
  dt.drawInterp hpl (uRulesDefinable_nexProg (bot := bot) hcoord h)
    (uGDefinable_nexAccept (h none)) NexPh.start blankMark

/-- **The interpreted structure reads the clocked program's table**: the whole
point of the definability layer, at the program the reduction emits. This is
what the run layer's lemmas are stated under. -/
theorem reads_nexProg (hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd)
    (hcoord : Function.Injective coord)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v)
    (bot : Option dt.KIx) (e : Env L)
    [ws : Language.wide.Structure
      (Univ e.α (dt.NexRTag (dt.d.B.ι → Bool)) dt.NexPF dt.KIx dt.dd)]
    (hws : ws = (nexInterp hpl hcoord h bot).mapStructure e.α) :
    (dt.nexProg e.zero e.one e.hzo hpl coord (dt.buildSpec e.zero e.one coord)
      (dt.regionSpec e.zero e.one) (args e) bot).table.Reads := by
  rw [nexProg_eq_progFrom]
  exact dt.reads_progFrom hpl (uRulesDefinable_nexProg (bot := bot) hcoord h)
    (uGDefinable_nexAccept (h none)) NexPh.start blankMark e hws

end Data

end Draw

end DescriptiveComplexity
