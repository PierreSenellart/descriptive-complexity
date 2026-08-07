/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MachineAltSpace.Spec

/-!
# Alternating acceptance in bounded space is in EXPTIME

The third layer, and the theorem: `DescriptiveComplexity.ATMAcceptSpace` is a
`DescriptiveComplexity.SOGameSpec`, so it is in EXPTIME
(`DescriptiveComplexity.atmAcceptSpace_mem_EXPTIME`) – EXPTIME's first natural
problem, and one that needs no succinctness argument.

The correspondence is a **bisimulation between two inductive predicates of the
same shape**: `DescriptiveComplexity.SOGameSpec.Wins` on assignments of the
configuration block and `DescriptiveComplexity.ATMData.AltWin` on
configurations. It needs exactly two lemmas beyond the four realization ones —
*a move lands on a configuration* and *a start is a configuration* – so junk
assignments, which the block has plenty of, are never reached and never have to
be reasoned about.

Where the promises go: `DescriptiveComplexity.ExpDefinable` compares `P A` with
`Q (X.Map A)`, and `DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksSplit` are conditions on `A` alone, so they
ride on the `start` sentence – a game with no starting state is lost, which is
what a failed promise should mean.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ATMSpace

/-- **The alternating machine, as a second-order game**: its states are the
assignments of the configuration block, its moves are the machine's steps, the
universal player owns the states marked by the second block, an accepting state
wins outright, and the starting states are the initial configurations of a
well-formed machine whose marks split. -/
noncomputable def atmSpec : SOGameSpec (Language.turingAlt 2) where
  B := cfgBlock
  move := isCfgBS ⊓ stepS
  univ := univS
  won := wonS
  start := startS

section Correct

variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]

/-- **A move is a step**, between configurations. -/
theorem move_cfgOf (c c' : Config A) :
    atmSpec.Move (cfgOf c) (cfgOf c') ↔ (atmData 2 A).toTMData.Step c c' := by
  letI := cfgBlock.structure₂ (L := tmaOrd) (cfgOf c) (cfgOf c')
  change (@Sentence.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) (cfgOf c) (cfgOf c'))
    (isCfgBS ⊓ stepS)) ↔ _
  refine Iff.trans Formula.realize_inf ?_
  refine Iff.trans (and_congr (realize_isCfgBS (cfgOf c) (cfgOf c')) (realize_stepS c c')) ?_
  exact and_iff_right (isCfg_cfgOf c')

/-- **A move lands on a configuration**: the move sentence says so outright,
which is what keeps the walk out of the junk assignments. -/
theorem move_isCfg {ρ σ : atmSpec.State A} (h : atmSpec.Move ρ σ) :
    ∃ c' : Config A, σ = cfgOf c' := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  have h' : @Sentence.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ)
    (isCfgBS ⊓ stepS) := h
  exact exists_cfgOf ((realize_isCfgBS ρ σ).mp (Formula.realize_inf.mp h').1)

/-- **The universal states are the ones the second mark owns.** -/
theorem isUniv_cfgOf (hsplit : (atmData 2 A).BlocksSplit) (c : Config A) :
    atmSpec.IsUniv (cfgOf c) ↔ (atmData 2 A).IsUniv true c.state := by
  refine (realize_univS c).trans ?_
  refine Iff.trans ?_ (ATMData.isUniv_true_iff_blk_one hsplit c.state).symm
  exact ⟨fun h => ⟨by omega, h⟩, fun ⟨_, h⟩ => h⟩

/-- **The states that win outright are the accepting ones.** -/
theorem isWon_cfgOf (c : Config A) :
    atmSpec.IsWon (cfgOf c) ↔ (atmData 2 A).Acc c.state :=
  realize_wonS c

/-- **The starting states are the initial configurations**, of a machine whose
two promises hold. -/
theorem isStart_iff (ρ : atmSpec.State A) :
    atmSpec.IsStart ρ ↔ ((atmData 2 A).toTMData.WellFormed ∧ (atmData 2 A).BlocksSplit ∧
      ∃ c : Config A, ρ = cfgOf c ∧ (atmData 2 A).toTMData.IsInit c) :=
  realize_startS ρ

/-! ### The bisimulation -/

/-- What winning says about the configuration an assignment is. -/
def WinsCfg (ρ : atmSpec.State A) : Prop :=
  ∀ c : Config A, ρ = cfgOf c → (atmData 2 A).AltWin true c

/-- Winning the game is winning the machine's game. -/
theorem altWin_of_wins (hsplit : (atmData 2 A).BlocksSplit) {ρ : atmSpec.State A}
    (h : atmSpec.Wins ρ) : WinsCfg ρ := by
  induction h with
  | @won ρ hw =>
    intro c hc
    subst hc
    exact .acc ((isWon_cfgOf c).mp hw)
  | @ex ρ σ hu hm _ ih =>
    intro c hc
    subst hc
    obtain ⟨c', rfl⟩ := move_isCfg hm
    exact .ex (fun hcu => hu ((isUniv_cfgOf hsplit c).mpr hcu)) ((move_cfgOf c c').mp hm)
      (ih c' rfl)
  | @all ρ hu hex _ ih =>
    intro c hc
    subst hc
    refine .all ((isUniv_cfgOf hsplit c).mp hu) ?_ ?_
    · obtain ⟨σ, hσ⟩ := hex
      obtain ⟨c', rfl⟩ := move_isCfg hσ
      exact ⟨c', (move_cfgOf c c').mp hσ⟩
    · intro d hd
      exact ih (cfgOf d) ((move_cfgOf c d).mpr hd) d rfl

/-- Winning the machine's game is winning the game. -/
theorem wins_of_altWin (hsplit : (atmData 2 A).BlocksSplit) {c : Config A}
    (h : (atmData 2 A).AltWin true c) : atmSpec.Wins (cfgOf c) := by
  induction h with
  | @acc d ha => exact .won ((isWon_cfgOf d).mpr ha)
  | @ex d d' hu hstep _ ih =>
    exact .ex (fun hcu => hu ((isUniv_cfgOf hsplit d).mp hcu)) ((move_cfgOf d d').mpr hstep) ih
  | @all d hu hex _ ih =>
    refine .all ((isUniv_cfgOf hsplit d).mpr hu) ?_ ?_
    · obtain ⟨e, he⟩ := hex
      exact ⟨cfgOf e, (move_cfgOf d e).mpr he⟩
    · intro σ hσ
      obtain ⟨e, rfl⟩ := move_isCfg hσ
      exact ih e ((move_cfgOf d e).mp hσ)

/-- **The game accepts exactly when the machine does.** -/
theorem accepts_atmSpec : atmSpec.Accepts A ↔ ATMAcceptSpace A := by
  constructor
  · rintro ⟨ρ, hs, hw⟩
    obtain ⟨hwf, hsplit, c, rfl, hinit⟩ := (isStart_iff ρ).mp hs
    exact ⟨hwf, hsplit, c, hinit, altWin_of_wins hsplit hw c rfl⟩
  · rintro ⟨hwf, hsplit, c, hinit, hw⟩
    exact ⟨cfgOf c, (isStart_iff _).mpr ⟨hwf, hsplit, c, rfl, hinit⟩, wins_of_altWin hsplit hw⟩

end Correct

end ATMSpace

open ATMSpace in
/-- **Alternating acceptance in bounded space is a second-order game.** -/
theorem atmAcceptSpace_soGameDefinable : SOGameDefinable ATMAcceptSpace :=
  ⟨atmSpec, fun _A _ _ _ _ => accepts_atmSpec.symm⟩

/-- **Alternating acceptance in bounded space is in EXPTIME**
(`APSPACE ⊆ EXPTIME`, half of [Chandra–Kozen–Stockmeyer
1981][chandra1981alternation]): the game on the configuration graph is
`DescriptiveComplexity.GAME` read over the expansion whose points are the
configurations, and GAME is in `DescriptiveComplexity.PTIME`.

This is EXPTIME's first natural problem, and it needs no succinctness argument:
the expansion is applied *after* the problem, which is the composition that
exists. Hardness is a separate matter – it is the Chandra–Kozen–Stockmeyer
simulation, and `ROADMAP.md` prices it. -/
theorem atmAcceptSpace_mem_EXPTIME : ATMAcceptSpace ∈ EXPTIME :=
  atmAcceptSpace_soGameDefinable.mem_EXPTIME

end DescriptiveComplexity
