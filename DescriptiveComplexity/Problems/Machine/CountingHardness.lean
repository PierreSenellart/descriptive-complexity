/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Counting
import DescriptiveComplexity.Problems.Machine.Interp

/-!
# Counting accepting runs is parsimoniously `#P`-complete

The machine bridge of the counting world. The machine `M_φ` of a CNF instance
(`DescriptiveComplexity.satMachine`) has exactly as many accepting runs as `φ` has
models (`DescriptiveComplexity.card_haltWalk_satMachine`), so the reduction of
`DescriptiveComplexity.Problems.Machine.Interp` is parsimonious
(`DescriptiveComplexity.SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept`). With
membership (`DescriptiveComplexity.sharpNtmAccept_mem_sharpP`) this gives

* `DescriptiveComplexity.sharpNtmAccept_sharpP_parsimoniousComplete`, and
* `DescriptiveComplexity.mem_sharpP_iff_le_sharpNtmAccept`: a counting problem is in
  `#P` – counts the witnesses of an existential second-order sentence – exactly
  when it reduces parsimoniously to counting the accepting runs of a
  nondeterministic machine within a polynomial budget. That is the definition
  of `#P` in [Valiant 1979][valiant1979complexity].

## Why the counts agree

The machine branches only at the guess, and it guesses only at the variables
of the formula, writing “false” at every other element. So:

* an accepting run ends on the tape of the assignment it guessed, which is a
  model (`DescriptiveComplexity.good_of_haltWalk`, from the run analysis
  `DescriptiveComplexity.sat_of_guess`);
* every model has a run ending on its tape
  (`DescriptiveComplexity.exists_haltWalk_of_good`);
* two runs ending on the same tape are the same run
  (`DescriptiveComplexity.haltWalk_ext`): a truth value once written is never
  overwritten, so the final tape says what each guess step wrote, and away from
  the guess the machine is deterministic.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

noncomputable section

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The assignments the machine can guess and accept: true only at variables
of the instance, and satisfying every clause. -/
def SatGood (ν : A → Bool) : Prop :=
  (∀ x : A, ν x = true → SatVar x) ∧ ∀ e : A, SatCl e → ∃ y : A, SatLit e y (ν y)

omit [Language.sat.Structure A] in
theorem symV_injective {v v' : Bool} {x : A} (h : (symV v x : SatV A) = symV v' x) :
    v = v' := by
  have h := (one_eq_one_iff.mp h).1
  revert h
  cases v <;> cases v' <;> simp

omit [Language.sat.Structure A] in
theorem symV_ne_symU {v : Bool} {x y : A} : (symV v x : SatV A) ≠ symU y := by
  intro h
  have h := (one_eq_one_iff.mp h).1
  revert h
  cases v <;> simp

/-- **Every model has a run**: a halting walk ending on its tape. -/
theorem exists_haltWalk_of_good (ν : A → Bool) (h : SatGood ν) :
    ∃ conf : SatV A → Config (SatV A), (satMachine A).IsHaltWalk conf ∧
      ∀ p, MaxPos tagTupleLe SatPosn p → (conf p).tape = doneTape ν := by
  obtain ⟨n, cfin, hn, hrun, hacc, hend⟩ := satMachine_run_of_sat ν h.1 h.2
  obtain ⟨conf, hconf, hmax⟩ := TMData.exists_haltWalk_of_stepsIn satMachine_wellFormed
    (isInit_confGuess ν) hn hrun hacc (fun _ _ hd => not_step_of_acc hd)
  exact ⟨conf, hconf, fun p hp => by rw [hmax p hp]; exact stepsIn_posEnd_tape ν _ cfin hend⟩

/-- **Every run is the run of a model**: a halting walk ends on the tape of an
assignment the machine can guess and accept. -/
theorem good_of_haltWalk {conf : SatV A → Config (SatV A)}
    (h : (satMachine A).IsHaltWalk conf) :
    ∃ ν : A → Bool, SatGood ν ∧
      ∀ p, MaxPos tagTupleLe SatPosn p → (conf p).tape = doneTape ν := by
  obtain ⟨p₁, hp₁⟩ := exists_maxPos (isLinOrd_tagTupleLe (A := A)) exists_satPosn
  obtain ⟨n, -, hsteps⟩ := TMData.IsWalk.exists_stepsIn (M := satMachine A)
    isLinOrd_tagTupleLe h.1 minPos_posStart p₁ hp₁.1
  have hinit := h.1.1 posStart minPos_posStart
  rw [isInit_eq_confGuess hinit (fun _ => false)] at hsteps
  obtain ⟨ν, hν, hsat, htape⟩ := sat_of_guess n (fun _ => false) posStart (conf p₁)
    (fun _ h => Bool.noConfusion h) satPosn_posStart posStart_le_posEnd hsteps
    (h.1.2.2 p₁ hp₁)
  refine ⟨ν, ⟨hν, hsat⟩, fun p hp => ?_⟩
  rw [isLinOrd_tagTupleLe.2.2.1 p p₁ (hp₁.2 p hp.1) (hp.2 p₁ hp₁.1)]
  exact htape

/-- A truth value on the tape survives a step. -/
theorem step_symV_persist {c d : Config (SatV A)} (hs : (satMachine A).Step c d)
    {r : SatV A} {v : Bool} {x : A} (hr : c.tape r = symV v x) : d.tape r = symV v x := by
  by_cases hrh : r = c.head
  · have hng : ¬ (c.state = stGuess ∧ ∃ y : A, c.tape c.head = symU y) := by
      rintro ⟨-, y, hy⟩
      rw [← hrh, hr] at hy
      exact symV_ne_symU hy
    rw [step_tape_eq hs hng]
    exact hr
  · obtain ⟨τ, -, -, -, -, -, hframe, -⟩ := hs
    rw [hframe r hrh]
    exact hr

/-- **A truth value on the tape survives the rest of a walk.** -/
theorem walk_symV_persist {conf : SatV A → Config (SatV A)} (h : (satMachine A).IsWalk conf)
    {p r : SatV A} {v : Bool} {x : A} (hp : SatPosn p) (hr : (conf p).tape r = symV v x) :
    ∀ p', SatPosn p' → tagTupleLe p p' → (conf p').tape r = symV v x := by
  have hlin := isLinOrd_tagTupleLe (A := A)
  have key : ∀ k : ℕ, ∀ p', SatPosn p' → bitRank tagTupleLe SatPosn p' = k → tagTupleLe p p' →
      (conf p').tape r = symV v x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p' hp' hrank hle
      by_cases hpp : p' = p
      · rw [hpp]
        exact hr
      have hnmin : ¬ MinPos tagTupleLe SatPosn p' := fun hmin =>
        hpp (hlin.2.2.1 p' p (hmin.2 p hp) hle)
      obtain ⟨q, hq⟩ := exists_predPos hlin hp' hnmin
      have hpq : tagTupleLe p q := by
        rcases hlin.2.2.2 p q with hle' | hle'
        · exact hle'
        · rcases hq.2.2.2.2 p hp hle' hle with heq | heq
          · rw [heq]
            exact hlin.1 q
          · exact absurd heq.symm hpp
      have hrq : bitRank tagTupleLe SatPosn q + 1 = k := by
        rw [← hrank, bitRank_succPos hlin hq]
      have hq' := ih (bitRank tagTupleLe SatPosn q) (by omega) q hq.1 rfl hpq
      rcases h.2.1 q p' hq with hstep | ⟨-, heq⟩
      · exact step_symV_persist hstep hq'
      · rw [heq]
        exact hq'
  exact fun p' hp' hle => key _ p' hp' rfl hle

/-- **Two runs ending on the same tape are the same run.** -/
theorem haltWalk_ext {conf conf' : SatV A → Config (SatV A)}
    (h : (satMachine A).IsHaltWalk conf) (h' : (satMachine A).IsHaltWalk conf')
    {p₁ : SatV A} (hp₁ : MaxPos tagTupleLe SatPosn p₁)
    (htape : (conf p₁).tape = (conf' p₁).tape) : conf = conf' := by
  have hlin := isLinOrd_tagTupleLe (A := A)
  have key : ∀ k : ℕ, ∀ p, SatPosn p → bitRank tagTupleLe SatPosn p = k → conf p = conf' p := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p hp hrank
      by_cases hmin : MinPos tagTupleLe SatPosn p
      · rw [isInit_eq_confGuess (h.1.1 p hmin) (fun _ => false),
          isInit_eq_confGuess (h'.1.1 p hmin) (fun _ => false)]
      obtain ⟨q, hq⟩ := exists_predPos hlin hp hmin
      have hrq : bitRank tagTupleLe SatPosn q + 1 = k := by
        rw [← hrank, bitRank_succPos hlin hq]
      have hqq : conf q = conf' q := ih (bitRank tagTupleLe SatPosn q) (by omega) q hq.1 rfl
      have hs := h.1.2.1 q p hq
      have hs' := h'.1.2.1 q p hq
      rw [← hqq] at hs'
      rcases hs with hstep | ⟨hacc, heq⟩ <;> rcases hs' with hstep' | ⟨hacc', heq'⟩
      · by_cases hg : (conf q).state = stGuess ∧ ∃ x : A, (conf q).tape (conf q).head = symU x
        · obtain ⟨hst, x, hx⟩ := hg
          obtain ⟨v, hv⟩ := step_guess_write hstep hst hx
          obtain ⟨v', hv'⟩ := step_guess_write hstep' hst hx
          have hfin := walk_symV_persist h.1 hp hv p₁ hp₁.1 (hp₁.2 p hp)
          have hfin' := walk_symV_persist h'.1 hp hv' p₁ hp₁.1 (hp₁.2 p hp)
          rw [htape, hfin'] at hfin
          refine step_functional_of_write hstep hstep' ?_
          rw [hv, hv', symV_injective hfin]
        · exact step_functional_off_guess hg hstep hstep'
      · exact absurd hstep (not_step_of_acc hacc')
      · exact absurd hstep' (not_step_of_acc hacc)
      · rw [heq, heq', hqq]
  funext t
  by_cases ht : SatPosn t
  · exact key _ t ht rfl
  · rw [h.2.2 t posStart ht minPos_posStart, h'.2.2 t posStart ht minPos_posStart]
    exact key _ posStart satPosn_posStart rfl

omit [Language.sat.Structure A] in
theorem doneTape_injective {ν ν' : A → Bool} (h : doneTape ν = doneTape ν') : ν = ν' := by
  funext x
  have hx := congrFun h (posCell x)
  rw [doneTape_cell ν (q := posCell x) rfl (fun a => botA_le a),
    doneTape_cell ν' (q := posCell x) rfl (fun a => botA_le a)] at hx
  exact symV_injective hx

/-- **The machine of a CNF instance has as many accepting runs as the
assignments it can guess and accept.** -/
theorem card_haltWalk_satMachine :
    Nat.card {conf : SatV A → Config (SatV A) // (satMachine A).IsHaltWalk conf} =
      Nat.card {ν : A → Bool // SatGood ν} := by
  obtain ⟨p₁, hp₁⟩ := exists_maxPos (isLinOrd_tagTupleLe (A := A)) exists_satPosn
  let F : {ν : A → Bool // SatGood ν} →
      {conf : SatV A → Config (SatV A) // (satMachine A).IsHaltWalk conf} := fun ν =>
    ⟨(exists_haltWalk_of_good ν.1 ν.2).choose, (exists_haltWalk_of_good ν.1 ν.2).choose_spec.1⟩
  have hF : ∀ ν, ((F ν).1 p₁).tape = doneTape ν.1 := fun ν =>
    (exists_haltWalk_of_good ν.1 ν.2).choose_spec.2 p₁ hp₁
  have hbij : Function.Bijective F := by
    constructor
    · intro ν ν' hνν'
      refine Subtype.ext (doneTape_injective ?_)
      rw [← hF ν, ← hF ν', hνν']
    · rintro ⟨conf, hconf⟩
      obtain ⟨ν, hν, htape⟩ := good_of_haltWalk hconf
      refine ⟨⟨ν, hν⟩, Subtype.ext ?_⟩
      refine haltWalk_ext (F ⟨ν, hν⟩).2 hconf hp₁ ?_
      rw [hF ⟨ν, hν⟩, htape p₁ hp₁]
  exact (Nat.card_congr (Equiv.ofBijective F hbij)).symm

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- The assignments the machine can guess and accept are the models of the
formula, with truth values read as propositions. -/
theorem card_satGood_eq_card_satModel :
    Nat.card {ν : A → Bool // SatGood ν} = Nat.card {ν : A → Prop // SatModel A ν} := by
  classical
  let e : (A → Bool) ≃ (A → Prop) :=
    { toFun := fun ν x => ν x = true
      invFun := fun ν x => decide (ν x)
      left_inv := fun ν => funext fun x => by simp
      right_inv := fun ν => funext fun x => by simp }
  refine Nat.card_congr (Equiv.subtypeEquiv e fun ν => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, h1⟩
    obtain ⟨y, hy⟩ := h2 c hc
    rcases hy with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · exact ⟨y, Or.inl ⟨hp, hv⟩⟩
    · exact ⟨y, Or.inr ⟨hn, by rw [show e ν y = (ν y = true) from rfl, hv]; simp⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun c hc => ?_⟩
    obtain ⟨y, hy⟩ := h1 c hc
    rcases hy with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · exact ⟨y, Or.inl ⟨hp, hv⟩⟩
    · exact ⟨y, Or.inr ⟨hn, Bool.eq_false_iff.mpr hv⟩⟩

namespace SatTM

/-- **Correctness of the interpretation, for counting**: the machine described
by the interpreted structure has as many accepting runs as the CNF instance has
models. -/
theorem sharpNtmAccept_map (A : Type) [Language.sat.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] : SharpNTMAccept (satTuringInterp.Map A) = SharpSAT A := by
  have hag := agree_satMachine (A := A)
  have hwf : (tmData (satTuringInterp.Map A)).WellFormed :=
    hag.wellFormed.mp satMachine_wellFormed
  rw [sharpNtmAccept_apply, sharpSat_apply, ← card_satGood_eq_card_satModel,
    ← card_haltWalk_satMachine, hag.card_haltWalk]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun conf => and_iff_right hwf)

/-- **#SAT reduces parsimoniously to counting the accepting runs of a
machine**: the reduction building `M_φ` inside the instance preserves the
number of solutions. -/
def sharpSat_ordered_parsimonious_sharpNtmAccept : SharpSAT ≤ᵖ[≤] SharpNTMAccept where
  Tag := SatTag
  dim := 2
  toInterpretation := satTuringInterp
  correct A _ _ _ _ := (sharpNtmAccept_map A).symm

end SatTM

end

/-! ### The machine characterization of `#P` -/

/-- Counting the accepting runs of a machine is parsimoniously `#P`-hard. -/
theorem sharpNtmAccept_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpNTMAccept :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept sharpSat_sharpP_parsimoniousHard

/-- **Counting the accepting runs of a nondeterministic machine is
parsimoniously `#P`-complete.** The class of this library is defined in logic;
this theorem is the bridge saying it is the machine one. -/
theorem sharpNtmAccept_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpNTMAccept :=
  ⟨sharpNtmAccept_mem_sharpP, sharpNtmAccept_sharpP_parsimoniousHard⟩

/-- **The machine characterization of `#P`**: a counting problem counts the
witnesses of an existential second-order sentence exactly when it reduces
parsimoniously to counting the accepting runs of a nondeterministic machine. -/
theorem mem_sharpP_iff_le_sharpNtmAccept {L : Language.{0, 0}} [L.IsRelational]
    (C : CountingProblem L) : C ∈ SharpP ↔ Nonempty (C ≤ᵖ[≤] SharpNTMAccept) :=
  ⟨fun hC => (sharpSat_parsimoniousHard_of_sharpPDefinable C hC).map fun g =>
      g.trans SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept,
    fun ⟨f⟩ => SharpP.mem_of_orderedParsimonious f sharpNtmAccept_mem_sharpP⟩

/-- **Counting accepting runs and counting models reduce to each other**,
parsimoniously: the counting form of the Cook–Levin correspondence. -/
theorem sharpNtmAccept_interreducible_sharpSat :
    Nonempty (SharpNTMAccept ≤ᵖ[≤] SharpSAT) ∧ Nonempty (SharpSAT ≤ᵖ[≤] SharpNTMAccept) :=
  ⟨sharpNtmAccept_reduces_to_sharpSat, ⟨SatTM.sharpSat_ordered_parsimonious_sharpNtmAccept⟩⟩

end DescriptiveComplexity
