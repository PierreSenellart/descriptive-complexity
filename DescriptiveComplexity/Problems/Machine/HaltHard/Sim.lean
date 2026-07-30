/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.SimRet

/-!
# The assembled simulation

The dispatch phase (`DescriptiveComplexity.HaltHard.sim_norm`) and the six
pops of `SimRet.lean` assemble into the correctness statement of the
simulating machine: from the resting configuration of a continuation `k` and
value `v`, the machine reaches an accepting configuration exactly when the
abstract evaluation `Turing.ToPartrec.Cont.eval` of `k` on `v` terminates
(`DescriptiveComplexity.HaltHard.reach_acc_iff_evalDom`).

The two directions meet at `DescriptiveComplexity.HaltHard.popTarget`, the
continuation and value the machine rests at after one pop –
`Turing.ToPartrec.stepRet`, one frame at a time. The machine side is
`DescriptiveComplexity.HaltHard.cycle_counted`: a counted run from rest to
the rest of the pop target. Its count is positive whenever the pop dispatches
a code – the run factors through a dispatch configuration whose state is not
the resting state – and the two pops that may in principle be silent
(`cons₂`, and `fix` on a zero flag) shrink the continuation instead, so both
directions recurse along the lexicographic order on (steps, continuation
size): forward on the abstract step count, since those two pops do not
consume an abstract step, and backward on the machine step count, split along
the cycle by determinism (`DescriptiveComplexity.HaltHard.stepsTo_det`). The
abstract side of each pop is `DescriptiveComplexity.HaltHard.stepRet_popTarget`,
and termination of the abstract machine is traded for termination of
`Turing.ToPartrec.Cont.eval` through `Turing.ToPartrec.stepRet_eval`.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-! ### The pop target -/

/-- **The pop target**: the continuation and value the machine rests at after
popping the top frame of `k` with value `v` – `Turing.ToPartrec.stepRet`, one
frame at a time, with the dispatches it triggers carried out by
`DescriptiveComplexity.HaltHard.pStepNormal`. On the empty continuation the
machine accepts instead, so that case is junk. -/
def popTarget : PCont c → List ℕ → PCont c × List ℕ
  | .halt, v => (.halt, v)
  | .cons₁ p as k, v => pStepNormal p (.cons₂ v k) as
  | .cons₂ ns k, v => (k, ns.headI :: v)
  | .comp p k, v => pStepNormal p k v
  | .fix p k, v => if v.headI = 0 then (k, v.tail) else pStepNormal p (.fix p k) v.tail

/-- One abstract step reaches the pop target: `Turing.ToPartrec.stepRet` on
`k` and `v` is either the `Turing.ToPartrec.Cfg.ret` of the pop target – when
the pop dispatches a code – or, for the two silent pops, definitionally the
`stepRet` of the pop target, whose continuation is then smaller. -/
theorem stepRet_popTarget {k : PCont c} (hk : k ≠ PCont.halt) (v : List ℕ) :
    stepRet k.toCont v =
        Cfg.ret (popTarget k v).1.toCont (popTarget k v).2 ∨
      (stepRet k.toCont v = stepRet (popTarget k v).1.toCont (popTarget k v).2 ∧
        sizeOf (popTarget k v).1 < sizeOf k) := by
  cases k with
  | halt => exact absurd rfl hk
  | cons₁ p as k₀ =>
    exact Or.inl (pStepNormal_toCont p (.cons₂ v k₀) as)
  | cons₂ ns k₀ =>
    refine Or.inr ⟨rfl, ?_⟩
    simp [popTarget]
  | comp p k₀ =>
    exact Or.inl (pStepNormal_toCont p k₀ v)
  | fix p k₀ =>
    rcases hv : v.headI with - | y
    · refine Or.inr ⟨?_, ?_⟩
      · change (if v.headI = 0 then stepRet k₀.toCont v.tail else _) = _
        rw [if_pos hv]
        simp only [popTarget, hv, if_pos]
      · simp [popTarget, hv]
    · refine Or.inl ?_
      change (if v.headI = 0 then _ else stepNormal (codeAt p) (Cont.fix (codeAt p) k₀.toCont)
        v.tail) = _
      rw [if_neg (by omega)]
      have h := pStepNormal_toCont p (.fix p k₀) v.tail
      rw [show popTarget (PCont.fix p k₀) v = pStepNormal p (.fix p k₀) v.tail by
        simp [popTarget, hv]]
      exact h

/-! ### Termination of the abstract machine, as counted runs -/

/-- Counted runs of the abstract machine `Turing.ToPartrec.step`. -/
def ASteps : ℕ → Cfg → Cfg → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ d, step a = some d ∧ ASteps n d b

/-- A counted abstract run, extended by one step at its end. -/
theorem ASteps.trans_step : ∀ {n : ℕ} {a b d : Cfg},
    ASteps n a b → step b = some d → ASteps (n + 1) a d := by
  intro n
  induction n with
  | zero => intro a b d hab hbd; exact ⟨d, by rw [show a = b from hab]; exact hbd, rfl⟩
  | succ n ih =>
    rintro a b d ⟨e, hstep, hrest⟩ hbd
    exact ⟨e, hstep, ih hrest hbd⟩

/-- An abstract reachability is a counted run of some length. -/
theorem asteps_of_reaches {a b : Cfg} (h : StateTransition.Reaches step a b) :
    ∃ n, ASteps n a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.trans_step hstep⟩

/-- Termination of `Turing.ToPartrec.Cont.eval` yields a counted abstract run
from the return configuration to a halting configuration. -/
theorem exists_asteps_halt_of_dom {K : Cont} {v : List ℕ} (h : (K.eval v).Dom) :
    ∃ N w, ASteps N (Cfg.ret K v) (Cfg.halt w) := by
  have hd : (StateTransition.eval step (stepRet K v)).Dom := by
    rw [stepRet_eval]
    exact h
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨hreach, hterm⟩ := StateTransition.mem_eval.mp hb
  obtain ⟨w, rfl⟩ : ∃ w, b = Cfg.halt w := by
    cases b with
    | halt w => exact ⟨w, rfl⟩
    | ret k' v' => exact absurd hterm (by simp [step])
  obtain ⟨n, hn⟩ := asteps_of_reaches hreach
  exact ⟨n + 1, w, stepRet K v, rfl, hn⟩

/-! ### Transfer of termination along one pop -/

/-- Termination of `Turing.ToPartrec.Cont.eval` is termination of the
sequential run from the return configuration. -/
theorem contEval_dom_iff_evalStep {K : Cont} {v : List ℕ} :
    (K.eval v).Dom ↔ (StateTransition.eval step (stepRet K v)).Dom := by
  rw [stepRet_eval]
  exact Iff.rfl

/-- Peeling the one step a return configuration always makes. -/
theorem evalStep_ret (K : Cont) (v : List ℕ) :
    StateTransition.eval step (Cfg.ret K v) = StateTransition.eval step (stepRet K v) :=
  StateTransition.reaches_eval (Relation.ReflTransGen.single (Option.mem_def.mpr rfl))

/-- **Termination transfers along one pop**: the abstract evaluation of a
nonempty continuation terminates exactly when that of its pop target does. -/
theorem dom_popTarget {k : PCont c} (hk : k ≠ PCont.halt) (v : List ℕ) :
    ((popTarget k v).1.toCont.eval (popTarget k v).2).Dom ↔ (k.toCont.eval v).Dom := by
  rcases stepRet_popTarget hk v with h | ⟨h, -⟩
  · rw [contEval_dom_iff_evalStep (K := k.toCont), h, evalStep_ret,
      ← contEval_dom_iff_evalStep]
  · rw [contEval_dom_iff_evalStep (K := k.toCont), h, ← contEval_dom_iff_evalStep]

/-! ### The machine cycle -/

/-- Accepting configurations are terminal. -/
theorem lstep_acc {x : LCfg c} (hx : x.q = SimQ.acc) : lstep x = none := by
  obtain ⟨q, L, s, R⟩ := x
  subst hx
  have h : simStep (c := c) .acc s = none := by cases s <;> rfl
  simp [lstep, h]

/-- **The counted machine cycle**: from the resting configuration of a
nonempty continuation, a counted run to the resting configuration of the pop
target. The count is zero only if the pop was silent, in which case the
continuation shrank – the escape hatch both lexicographic inductions use. -/
theorem cycle_counted {k : PCont c} (hk : k ≠ PCont.halt) {fr : List (SimSym c)}
    (hfr : FrameSeg k fr) (g : ℕ) (v : List ℕ) (j t : ℕ) :
    ∃ m g' fr' j' t', FrameSeg (popTarget k v).1 fr' ∧
      stepsTo m (restCfg g fr v j t) (restCfg g' fr' (popTarget k v).2 j' t') ∧
      (m = 0 → sizeOf (popTarget k v).1 < sizeOf k) := by
  obtain ⟨n, w, rfl, htop⟩ := hfr.gap_split
  cases htop with
  | halt => exact absurd rfl hk
  | @cons₁ p as k₀ w' hw' =>
    obtain ⟨t', hr₁⟩ := pop_cons₁ n hw' g v j t
    obtain ⟨g', fr', j', t'', hfr', hr₂⟩ := sim_norm (sizeOf (codeAt p)) p le_rfl
      (.cons₂ v k₀) as (Q := .nSeekR p) rfl (g - ((encVal (c := c) v).length + 1))
      (FrameSeg.cons₂ (FrameSeg.gaps _ hw')) j t'
    obtain ⟨m₁, hm₁⟩ := reach_iff_stepsTo.mp hr₁
    obtain ⟨m₂, hm₂⟩ := reach_iff_stepsTo.mp hr₂
    rcases m₁ with - | m₁
    · have heq : restCfg g (List.replicate n SimSym.bk ++
          SimSym.hCons₁ p :: (encVal as ++ w')) v j t = atMid (.nSeekR p)
          (g - ((encVal (c := c) v).length + 1)) (SimSym.hCons₂ ::
          ((encVal v).reverse ++ (List.replicate (n + (encVal (c := c) as).length + 1)
          SimSym.bk ++ w'))) as j t' := hm₁
      exact absurd (congrArg LCfg.q heq) (by simp)
    · exact ⟨m₁ + 1 + m₂, g', fr', j', t'', hfr', hm₁.trans hm₂,
        fun h => absurd h (by omega)⟩
  | @cons₂ ns k₀ w' hw' =>
    obtain ⟨t', hr⟩ := pop_cons₂ ns n hw' g v j t
    obtain ⟨m, hm⟩ := reach_iff_stepsTo.mp hr
    refine ⟨m, g, _, j, t', FrameSeg.gaps _ hw', hm, fun _ => ?_⟩
    simp [popTarget]
  | @comp p k₀ w' hw' =>
    have hr₁ := pop_comp (p := p) n hw' g v j t
    obtain ⟨g', fr', j', t', hfr', hr₂⟩ := sim_norm (sizeOf (codeAt p)) p le_rfl k₀ v
      (Q := .nSeekR p) rfl g (FrameSeg.gaps (n + 1) hw') j t
    obtain ⟨m₁, hm₁⟩ := reach_iff_stepsTo.mp hr₁
    obtain ⟨m₂, hm₂⟩ := reach_iff_stepsTo.mp hr₂
    rcases m₁ with - | m₁
    · have heq : restCfg g (List.replicate n SimSym.bk ++ SimSym.hComp p :: w') v j t =
          atMid (.nSeekR p) g (List.replicate (n + 1) SimSym.bk ++ w') v j t := hm₁
      exact absurd (congrArg LCfg.q heq) (by simp)
    · exact ⟨m₁ + 1 + m₂, g', fr', j', t', hfr', hm₁.trans hm₂,
        fun h => absurd h (by omega)⟩
  | @fix p k₀ w' hw' =>
    rcases hv : v.headI with - | y
    · rw [show popTarget (PCont.fix p k₀) v = (k₀, v.tail) by simp [popTarget, hv]]
      obtain ⟨t', hr⟩ := pop_fix_stop n hw' g hv j t
      obtain ⟨m, hm⟩ := reach_iff_stepsTo.mp hr
      refine ⟨m, g, _, j, t', FrameSeg.gaps _ hw', hm, fun _ => ?_⟩
      simp
    · rw [show popTarget (PCont.fix p k₀) v = pStepNormal p (.fix p k₀) v.tail by
        simp [popTarget, hv]]
      obtain ⟨t', hr₁⟩ := pop_fix_go n hw' g hv j t
      obtain ⟨g', fr', j', t'', hfr', hr₂⟩ := sim_norm (sizeOf (codeAt p)) p le_rfl
        (.fix p k₀) v.tail (Q := .nSeekL p) rfl g
        (FrameSeg.gaps n (FrameSeg.fix hw')) j t'
      obtain ⟨m₁, hm₁⟩ := reach_iff_stepsTo.mp hr₁
      obtain ⟨m₂, hm₂⟩ := reach_iff_stepsTo.mp hr₂
      rcases m₁ with - | m₁
      · have heq : restCfg g (List.replicate n SimSym.bk ++ SimSym.hFix p :: w') v j t =
            atMid (.nSeekL p) g (List.replicate n SimSym.bk ++ SimSym.hFix p :: w')
            v.tail j t' := hm₁
        exact absurd (congrArg LCfg.q heq) (by simp)
      · exact ⟨m₁ + 1 + m₂, g', fr', j', t'', hfr', hm₁.trans hm₂,
          fun h => absurd h (by omega)⟩

/-! ### The two directions -/

/-- **Forward simulation**: if the abstract machine halts from the return
configuration of `k` and `v` in `N` steps, the simulating machine accepts
from the resting configuration of any frame region of `k`, by lexicographic
recursion on `(N, sizeOf k)` – the two silent pops keep `N` and shrink `k`. -/
theorem reach_acc_of_asteps (N : ℕ) (k : PCont c) (v w : List ℕ)
    (hN : ASteps N (Cfg.ret k.toCont v) (Cfg.halt w)) (g : ℕ) (fr : List (SimSym c))
    (hfr : FrameSeg k fr) (j t : ℕ) :
    ∃ x, x.q = SimQ.acc ∧ Reach (restCfg g fr v j t) x := by
  by_cases hk : k = PCont.halt
  · -- the empty continuation: the machine accepts outright
    subst hk
    obtain ⟨n, w', rfl, htop⟩ := hfr.gap_split
    cases htop
    obtain ⟨y, hy, hr⟩ := pop_halt n g v j t
    exact ⟨y, hy, Reach.cast (by simp) rfl hr⟩
  · obtain ⟨n, hNn⟩ : ∃ n, N = n + 1 := by
      rcases N with - | n
      · exact absurd (show Cfg.ret _ _ = Cfg.halt w from hN) (by simp)
      · exact ⟨n, rfl⟩
    rw [hNn] at hN
    obtain ⟨d, hd, hrest⟩ := hN
    simp only [step, Option.some.injEq] at hd
    subst hd
    obtain ⟨m, g', fr', j', t', hfr', hm, -⟩ := cycle_counted hk hfr g v j t
    rcases stepRet_popTarget hk v with hsr | ⟨hsr, hsz⟩
    · rw [hsr] at hrest
      obtain ⟨x, hx, hr⟩ := reach_acc_of_asteps n _ _ w hrest g' fr' hfr' j' t'
      exact ⟨x, hx, Reach.trans (reach_iff_stepsTo.mpr ⟨m, hm⟩) hr⟩
    · rw [hsr] at hrest
      have hN' : ASteps (n + 1) (Cfg.ret (popTarget k v).1.toCont (popTarget k v).2)
          (Cfg.halt w) := ⟨_, rfl, hrest⟩
      obtain ⟨x, hx, hr⟩ := reach_acc_of_asteps (n + 1) _ _ w hN' g' fr' hfr' j' t'
      exact ⟨x, hx, Reach.trans (reach_iff_stepsTo.mpr ⟨m, hm⟩) hr⟩
  termination_by (N, sizeOf k)
  decreasing_by
  · subst hNn
    exact Prod.Lex.left _ _ (by omega)
  · subst hNn
    exact Prod.Lex.right _ hsz

/-- **Backward simulation**: if the simulating machine accepts from the
resting configuration of `k` and `v` in `N` steps, the abstract evaluation of
`k` on `v` terminates, by lexicographic recursion on `(N, sizeOf k)` – the
counted cycle is split off the accepting run by determinism, and a silent
cycle shrinks `k`. -/
theorem dom_of_stepsTo_acc (N : ℕ) (k : PCont c) (v : List ℕ) (g : ℕ)
    (fr : List (SimSym c)) (j t : ℕ) (x : LCfg c) (hfr : FrameSeg k fr)
    (hN : stepsTo N (restCfg g fr v j t) x) (hx : x.q = SimQ.acc) :
    (k.toCont.eval v).Dom := by
  have hxt : lstep x = none := lstep_acc hx
  by_cases hk : k = PCont.halt
  · subst hk
    change ((pure v : Part (List ℕ))).Dom
    trivial
  · obtain ⟨m, g', fr', j', t', hfr', hm, h0⟩ := cycle_counted hk hfr g v j t
    have hmN : m ≤ N := le_of_stepsTo_terminal hN hxt hm
    have hrest := stepsTo_det hm hN hmN
    exact (dom_popTarget hk v).mp
      (dom_of_stepsTo_acc (N - m) _ _ g' fr' j' t' x hfr' hrest hx)
  termination_by (N, sizeOf k)
  decreasing_by
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact Prod.Lex.right _ (h0 rfl)
    · exact Prod.Lex.left _ _ (by omega)

/-! ### The correctness statement -/

/-- **Correctness of the simulating machine**: from the resting configuration
of a continuation `k` and value `v`, the machine reaches an accepting
configuration exactly when `Turing.ToPartrec.Cont.eval` of `k` on `v`
terminates. -/
theorem reach_acc_iff_evalDom {k : PCont c} {fr : List (SimSym c)} (hfr : FrameSeg k fr)
    (g : ℕ) (v : List ℕ) (j t : ℕ) :
    (∃ x, x.q = SimQ.acc ∧ Reach (restCfg g fr v j t) x) ↔ (k.toCont.eval v).Dom := by
  constructor
  · rintro ⟨x, hx, hr⟩
    obtain ⟨N, hN⟩ := reach_iff_stepsTo.mp hr
    exact dom_of_stepsTo_acc N k v g fr j t x hfr hN hx
  · intro h
    obtain ⟨N, w, hN⟩ := exists_asteps_halt_of_dom h
    exact reach_acc_of_asteps N k v w hN g fr hfr j t

end HaltHard

end DescriptiveComplexity
