/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Membership
import DescriptiveComplexity.Problems.Sat.CountingHardness

/-!
# Counting the accepting runs of a machine

The counting version of `DescriptiveComplexity.NTMAccept`, on the same vocabulary: the
number of accepting runs of the machine an instance describes – the quantity
`#P` was introduced to measure ([Valiant 1979][valiant1979complexity]).

A run is counted through its layout along the positions, as in
`DescriptiveComplexity.TMData.IsWalk`, with two more requirements that make the layout
of a run unique (`DescriptiveComplexity.TMData.IsHaltWalk`):

* an accepting configuration is *repeated*, never left: a run is counted up to
  the first accepting configuration it reaches, as for a machine whose
  accepting states are halting;
* times that are not positions carry the initial configuration: the clock of a
  run is the positions, and a walk says something only there.

`DescriptiveComplexity.SharpNTMAccept` is the bundled counting problem; its support is
machine acceptance (`DescriptiveComplexity.sharpNtmAccept_support_iff`), and it
belongs to `#P` (`DescriptiveComplexity.sharpNtmAccept_mem_sharpP`): the tableau of
Fagin's argument is functionally determined by the run, so its guesses are the
runs, bijectively (`DescriptiveComplexity.haltWalkEquiv`). With the counting
Cook–Levin theorem this gives its textbook form,
`DescriptiveComplexity.sharpNtmAccept_reduces_to_sharpSat`: counting the accepting runs
of a machine reduces parsimoniously to counting the models of a CNF formula.

The converse reduction is in
`DescriptiveComplexity.Problems.Machine.CountingHardness`, which makes this problem
parsimoniously `#P`-complete and `#P` the class of the problems reducing to
it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

namespace TMData

variable {A : Type} (M : TMData A)

/-- **A halting walk**: a walk that repeats an accepting configuration once it
has reached one, and carries the initial configuration at the times that are
not positions. A run from an initial configuration to the first accepting one,
within the budget, has exactly one such layout. -/
def IsHaltWalk (conf : A → Config A) : Prop :=
  M.IsWalk conf ∧
    (∀ p q, SuccPos M.Le M.Posn p q → M.Acc (conf p).state → conf q = conf p) ∧
    ∀ t p₀, ¬ M.Posn t → MinPos M.Le M.Posn p₀ → conf t = conf p₀

variable {M}

/-- **Acceptance is a halting walk**: an accepting run, cut at the first
accepting configuration it reaches, lays out along the positions. -/
theorem accepts_iff_exists_haltWalk [Finite A] (hwf : M.WellFormed) :
    M.Accepts ↔ ∃ conf : A → Config A, M.IsHaltWalk conf := by
  refine ⟨?_, fun ⟨conf, h⟩ => (accepts_iff_exists_walk hwf).mpr ⟨conf, h.1⟩⟩
  obtain ⟨hlin, hne, -⟩ := hwf
  rintro ⟨c₀, c, n, hinit, hlt, hrun, hacc⟩
  classical
  obtain ⟨f, hf0, hfn, hfs⟩ := exists_run n c₀ c hrun
  have hex : ∃ i, M.Acc (f i).state := ⟨n, by rw [hfn]; exact hacc⟩
  have hin : Nat.find hex ≤ n := Nat.find_min' hex (by rw [hfn]; exact hacc)
  have hfi : M.Acc (f (Nat.find hex)).state := Nat.find_spec hex
  have hposn : ∀ {p}, M.Posn p →
      (if M.Posn p then f (min (bitRank M.Le M.Posn p) (Nat.find hex)) else f 0) =
        f (min (bitRank M.Le M.Posn p) (Nat.find hex)) := fun hp => if_pos hp
  refine ⟨fun t => if M.Posn t then f (min (bitRank M.Le M.Posn t) (Nat.find hex)) else f 0,
    ⟨fun p hp => ?_, fun p q hpq => ?_, fun p hp => ?_⟩, fun p q hpq hpa => ?_,
    fun t p₀ ht hp₀ => ?_⟩
  · dsimp only
    rw [hposn hp.1, bitRank_eq_zero_of_minPos hlin hp, Nat.zero_min, hf0]
    exact hinit
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) (Nat.find hex) with hcase | hcase
    · refine Or.inl ?_
      rw [hrq, min_eq_left (by omega), min_eq_left (by omega)]
      exact hfs _ (by omega)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [min_eq_right hcase]
        exact hfi
      · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp
    dsimp only
    rw [hposn hp.1, min_eq_right (by omega)]
    exact hfi
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only at hpa ⊢
    rw [hposn hpq.1] at hpa
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) (Nat.find hex) with hcase | hcase
    · rw [min_eq_left (by omega)] at hpa
      exact absurd hpa (Nat.find_min hex hcase)
    · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · dsimp only
    rw [if_neg ht, hposn hp₀.1, bitRank_eq_zero_of_minPos hlin hp₀, Nat.zero_min]

/-- **A run to an accepting configuration is a halting walk**, for a machine
whose accepting configurations have no successor: the run lays out along the
positions and ends on the configuration it reached. -/
theorem exists_haltWalk_of_stepsIn [Finite A] (hwf : M.WellFormed) {c₀ c : Config A} {n : ℕ}
    (hinit : M.IsInit c₀) (hlt : n < Nat.card {p : A // M.Posn p}) (hrun : M.StepsIn n c₀ c)
    (hacc : M.Acc c.state) (hhalt : ∀ d e : Config A, M.Acc d.state → ¬ M.Step d e) :
    ∃ conf : A → Config A, M.IsHaltWalk conf ∧ ∀ p, MaxPos M.Le M.Posn p → conf p = c := by
  obtain ⟨hlin, -, -⟩ := hwf
  classical
  obtain ⟨f, hf0, hfn, hfs⟩ := exists_run n c₀ c hrun
  have hposn : ∀ {p}, M.Posn p →
      (if M.Posn p then f (min (bitRank M.Le M.Posn p) n) else f 0) =
        f (min (bitRank M.Le M.Posn p) n) := fun hp => if_pos hp
  refine ⟨fun t => if M.Posn t then f (min (bitRank M.Le M.Posn t) n) else f 0,
    ⟨⟨fun p hp => ?_, fun p q hpq => ?_, fun p hp => ?_⟩, fun p q hpq hpa => ?_,
      fun t p₀ ht hp₀ => ?_⟩, fun p hp => ?_⟩
  · dsimp only
    rw [hposn hp.1, bitRank_eq_zero_of_minPos hlin hp, Nat.zero_min, hf0]
    exact hinit
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) n with hcase | hcase
    · refine Or.inl ?_
      rw [hrq, min_eq_left (by omega), min_eq_left (by omega)]
      exact hfs _ hcase
    · refine Or.inr ⟨?_, ?_⟩
      · rw [min_eq_right hcase, hfn]
        exact hacc
      · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp
    dsimp only
    rw [hposn hp.1, min_eq_right (by omega), hfn]
    exact hacc
  · have hrq : bitRank M.Le M.Posn q = bitRank M.Le M.Posn p + 1 := bitRank_succPos hlin hpq
    dsimp only at hpa ⊢
    rw [hposn hpq.1] at hpa
    rw [hposn hpq.1, hposn hpq.2.1]
    rcases lt_or_ge (bitRank M.Le M.Posn p) n with hcase | hcase
    · rw [min_eq_left (by omega)] at hpa
      exact absurd (hfs _ hcase) (hhalt _ _ hpa)
    · rw [hrq, min_eq_right (by omega), min_eq_right hcase]
  · dsimp only
    rw [if_neg ht, hposn hp₀.1, bitRank_eq_zero_of_minPos hlin hp₀, Nat.zero_min]
  · have hmax : bitRank M.Le M.Posn p + 1 = Nat.card {x : A // M.Posn x} :=
      bitRank_maxPos hp
    dsimp only
    rw [hposn hp.1, min_eq_right (by omega), hfn]

/-! ### Halting walks of agreeing machines -/

section Agree

variable {B : Type} {u : B ≃ A} {N : TMData B}

/-- Agreement of machines is symmetric. -/
theorem Agree.symm (h : Agree u N M) : Agree u.symm M N where
  posn a := by rw [h.posn, Equiv.apply_symm_apply]
  le a a' := by rw [h.le, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  tr a := by rw [h.tr, Equiv.apply_symm_apply]
  start a := by rw [h.start, Equiv.apply_symm_apply]
  acc a := by rw [h.acc, Equiv.apply_symm_apply]
  blank a := by rw [h.blank, Equiv.apply_symm_apply]
  right a := by rw [h.right, Equiv.apply_symm_apply]
  src a a' := by rw [h.src, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  read a a' := by rw [h.read, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  dst a a' := by rw [h.dst, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  write a a' := by rw [h.write, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  inp a a' := by rw [h.inp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit M in
theorem _root_.DescriptiveComplexity.Config.map_symm_map (u : B ≃ A) (c : Config B) :
    (c.map u).map u.symm = c := by
  refine Config.ext ?_ ?_ (funext fun p => ?_) <;> simp [Config.map]

/-- **Halting walks transport along an agreement.** -/
theorem Agree.isHaltWalk_map (h : Agree u N M) {conf : B → Config B}
    (hw : N.IsHaltWalk conf) : M.IsHaltWalk fun a => (conf (u.symm a)).map u := by
  have hmin : ∀ {a}, MinPos M.Le M.Posn a → MinPos N.Le N.Posn (u.symm a) := fun ha =>
    h.minPos.mpr (by rwa [Equiv.apply_symm_apply])
  have hsucc : ∀ {a a'}, SuccPos M.Le M.Posn a a' →
      SuccPos N.Le N.Posn (u.symm a) (u.symm a') := fun ha =>
    h.succPos.mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  obtain ⟨⟨hinit, hstep, hacc⟩, hhalt, hoff⟩ := hw
  refine ⟨⟨fun a ha => h.isInit.mp (hinit _ (hmin ha)), fun a a' hs => ?_, fun a ha => ?_⟩,
    fun a a' hs ha => ?_, fun a a₀ ha ha₀ => ?_⟩
  · rcases hstep _ _ (hsucc hs) with hst | ⟨hac, heq⟩
    · exact Or.inl (h.step.mp hst)
    · refine Or.inr ⟨(h.acc _).mp hac, ?_⟩
      dsimp only
      rw [heq]
  · refine (h.acc _).mp (hacc (u.symm a) ⟨(h.posn _).mpr ?_, fun q hq => (h.le _ _).mpr ?_⟩)
    · rw [Equiv.apply_symm_apply]
      exact ha.1
    · rw [Equiv.apply_symm_apply]
      exact ha.2 (u q) ((h.posn q).mp hq)
  · dsimp only
    rw [hhalt _ _ (hsucc hs) ((h.acc _).mpr ha)]
  · dsimp only
    rw [hoff (u.symm a) (u.symm a₀) (fun hp => ha ?_) (hmin ha₀)]
    have := (h.posn _).mp hp
    rwa [Equiv.apply_symm_apply] at this

/-- **Agreeing machines have as many halting walks.** -/
theorem Agree.card_haltWalk (h : Agree u N M) :
    Nat.card {conf : B → Config B // N.IsHaltWalk conf} =
      Nat.card {conf : A → Config A // M.IsHaltWalk conf} :=
  Nat.card_congr
    { toFun := fun c => ⟨fun a => (c.1 (u.symm a)).map u, h.isHaltWalk_map c.2⟩
      invFun := fun c => ⟨fun b => (c.1 (u b)).map u.symm, h.symm.isHaltWalk_map c.2⟩
      left_inv := fun c => Subtype.ext (funext fun b => by
        change ((c.1 (u.symm (u b))).map u).map u.symm = c.1 b
        rw [Equiv.symm_apply_apply, Config.map_symm_map])
      right_inv := fun c => Subtype.ext (funext fun a => by
        change ((c.1 (u (u.symm a))).map u.symm).map u = c.1 a
        rw [Equiv.apply_symm_apply]
        exact Config.map_symm_map u.symm _) }

end Agree

/-! ### The relational form of a halting walk -/

section Relational

variable (M) (Q H : A → A → Prop) (T : A → A → A → Prop)

/-- The three relations describe the same configuration at `t'` as at `t`. -/
def RelSame (t t' : A) : Prop :=
  (∀ q, Q t' q ↔ Q t q) ∧ (∀ p, H t' p ↔ H t p) ∧ ∀ p a, T t' p a ↔ T t p a

/-- **A halting walk, guessed as three relations.** -/
structure RelHaltWalk : Prop where
  /-- The relations are a walk. -/
  walk : M.RelWalk Q H T
  /-- An accepting configuration is repeated. -/
  halt : ∀ t t', SuccPos M.Le M.Posn t t' → (∀ q, Q t q → M.Acc q) → RelSame Q H T t t'
  /-- Times that are not positions carry the initial configuration. -/
  off : ∀ t t₀, ¬ M.Posn t → MinPos M.Le M.Posn t₀ → RelSame Q H T t₀ t

variable {M Q H T}

/-- Times at which the relations agree carry the same configuration. -/
theorem RelWalk.conf_eq_of_relSame (h : M.RelWalk Q H T) {t t' : A}
    (hs : RelSame Q H T t t') : h.conf t' = h.conf t := by
  obtain ⟨hq, hh, ht⟩ := hs
  refine Config.ext (h.quniq t _ _ ((hq _).mp (h.qex t').choose_spec) (h.qex t).choose_spec)
    (h.huniq t _ _ ((hh _).mp (h.hex t').choose_spec) (h.hex t).choose_spec)
    (funext fun p => ?_)
  exact h.tuniq t p _ _ ((ht p _).mp (h.tex t' p).choose_spec) (h.tex t p).choose_spec

/-- A relational halting walk is a halting walk, through the configurations it
describes. -/
theorem RelHaltWalk.isHaltWalk (h : M.RelHaltWalk Q H T) : M.IsHaltWalk h.walk.conf := by
  refine ⟨h.walk.isWalk, fun p q hpq hacc => ?_, fun t p₀ ht hp₀ => ?_⟩
  · refine h.walk.conf_eq_of_relSame (h.halt p q hpq fun q' hq' => ?_)
    rw [h.walk.quniq p q' _ hq' (h.walk.qex p).choose_spec]
    exact hacc
  · exact h.walk.conf_eq_of_relSame (h.off t p₀ ht hp₀)

/-- A halting walk is a relational halting walk, through the graphs of its
configurations. -/
theorem IsHaltWalk.relHaltWalk {conf : A → Config A} (h : M.IsHaltWalk conf) :
    M.RelHaltWalk (fun t q => q = (conf t).state) (fun t p => p = (conf t).head)
      (fun t p a => a = (conf t).tape p) := by
  obtain ⟨hw, hhalt, hoff⟩ := h
  refine ⟨hw.relWalk, fun t t' htt' hacc => ?_, fun t t₀ ht ht₀ => ?_⟩
  · have heq := hhalt t t' htt' (hacc _ rfl)
    refine ⟨fun q => ?_, fun p => ?_, fun p a => ?_⟩ <;> dsimp only <;> rw [heq]
  · have heq := hoff t t₀ ht ht₀
    refine ⟨fun q => ?_, fun p => ?_, fun p a => ?_⟩ <;> dsimp only <;> rw [heq]

end Relational

end TMData

/-! ### The kernel -/

section Builders

variable {α : Type}

/-- The state at `t` is accepting, as a formula. -/
noncomputable def tqAccAtF (t : α) : tqSOLang.Formula α :=
  fo%[t] ∀ q, tqStateF⟨t, q⟩ → tqAccF⟨q⟩

/-- The configuration at `t'` is the one at `t`, as a formula. -/
noncomputable def tqSameF (t t' : α) : tqSOLang.Formula α :=
  fo%[t, t'] (∀ q, tqStateF⟨t', q⟩ ↔ tqStateF⟨t, q⟩) ∧
    (∀ p, tqHeadF⟨t', p⟩ ↔ tqHeadF⟨t, p⟩) ∧
    ∀ p a, tqTapeF⟨t', p, a⟩ ↔ tqTapeF⟨t, p, a⟩

/-- An accepting configuration is repeated. -/
noncomputable def tqHaltClause : tqSOLang.Sentence :=
  fo% ∀ t t', tqSuccPosF⟨t, t'⟩ ∧ tqAccAtF⟨t⟩ → tqSameF⟨t, t'⟩

/-- Times that are not positions carry the initial configuration. -/
noncomputable def tqOffClause : tqSOLang.Sentence :=
  fo% ∀ t t₀, ¬ tqPosnF⟨t⟩ ∧ tqMinPosF⟨t₀⟩ → tqSameF⟨t₀, t⟩

/-- **The kernel of the counting problem**: the kernel of machine acceptance,
and the two clauses that make the tableau of a run unique. -/
noncomputable def sharpTqKernel : tqSOLang.Sentence :=
  tqKernel ⊓ (tqHaltClause ⊓ tqOffClause)

end Builders

section RealizeKernel

variable {A : Type} [Language.turing.Structure A] (ρ : tmGuessBlock.Assignment A)

local notation "SOStruc" => @sumStructure Language.turing tmGuessBlock.lang A _
  (tmGuessBlock.structure ρ)

variable {α : Type} (v : α → A)

theorem realize_tqAccAtF (t : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqAccAtF t) v) ↔
      ∀ q, ρ .state ![v t, q] → TMAcc q := by
  simp only [tqAccAtF, Formula.realize_imp, Formula.realize_iAlls, realize_tqStateF,
    realize_tqAccF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h q hq => h (fun _ => q) hq, fun h i hi => h (i 0) hi⟩

theorem realize_tqSameF (t t' : α) :
    (@Formula.Realize tqSOLang A SOStruc _ (tqSameF t t') v) ↔
      TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
        (fun t p a => ρ .tape ![t, p, a]) (v t) (v t') := by
  simp only [tqSameF, Formula.realize_inf, Formula.realize_iff, Formula.realize_iAlls,
    realize_tqStateF, realize_tqHeadF, realize_tqTapeF, Sum.elim_inl, Sum.elim_inr,
    TMData.RelSame]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩
  · exact ⟨fun h p => h fun _ => p, fun h i => h (i 0)⟩
  · exact ⟨fun h p a => h ![p, a], fun h i => h (i 0) (i 1)⟩

theorem realize_tqHaltClause :
    (@Sentence.Realize tqSOLang A SOStruc tqHaltClause) ↔
      ∀ t t', SuccPos TMLe TMPosn t t' → (∀ q, ρ .state ![t, q] → TMAcc q) →
        TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) t t' := by
  simp only [tqHaltClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_tqSuccPosF, realize_tqAccAtF, realize_tqSameF, Sum.elim_inr]
  exact ⟨fun h t t' h₁ h₂ => h ![t, t'] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

theorem realize_tqOffClause :
    (@Sentence.Realize tqSOLang A SOStruc tqOffClause) ↔
      ∀ t t₀, ¬ TMPosn t → MinPos TMLe TMPosn t₀ →
        TMData.RelSame (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) t₀ t := by
  simp only [tqOffClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, realize_tqPosnF, realize_tqMinPosF,
    realize_tqSameF, Sum.elim_inr]
  exact ⟨fun h t t₀ h₁ h₂ => h ![t, t₀] ⟨h₁, h₂⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

/-- **The kernel says exactly what it should**: the instance is well formed and
the guessed relations are a halting walk. -/
theorem realize_sharpTqKernel :
    (@Sentence.Realize tqSOLang A SOStruc sharpTqKernel) ↔
      (tmData A).WellFormed ∧
        (tmData A).RelHaltWalk (fun t q => ρ .state ![t, q]) (fun t p => ρ .head ![t, p])
          (fun t p a => ρ .tape ![t, p, a]) := by
  have hinf : ∀ φ ψ : tqSOLang.Sentence, (@Sentence.Realize tqSOLang A SOStruc (φ ⊓ ψ)) ↔
      (@Sentence.Realize tqSOLang A SOStruc φ) ∧ (@Sentence.Realize tqSOLang A SOStruc ψ) := by
    intro φ ψ
    let := tmGuessBlock.structure ρ
    exact Formula.realize_inf
  rw [sharpTqKernel, hinf, hinf, realize_tqKernel, realize_tqHaltClause, realize_tqOffClause]
  exact ⟨fun ⟨⟨hwf, hw⟩, hh, ho⟩ => ⟨hwf, hw, hh, ho⟩,
    fun ⟨hwf, hw, hh, ho⟩ => ⟨⟨hwf, hw⟩, hh, ho⟩⟩

end RealizeKernel

/-! ### Runs are the witnesses of the kernel -/

section Count

variable (A : Type) [Language.turing.Structure A]

/-- The guess of the block describing a family of configurations: the graphs of
its state, head and tape. -/
def confAssign {A : Type} (conf : A → Config A) : tmGuessBlock.Assignment A :=
  fun i => match i with
    | .state => fun w : Fin 2 → A => w 1 = (conf (w 0)).state
    | .head => fun w : Fin 2 → A => w 1 = (conf (w 0)).head
    | .tape => fun w : Fin 3 → A => w 2 = (conf (w 0)).tape (w 1)

/-- **The halting walks of a machine are the witnesses of the kernel**,
bijectively: the three guessed relations are functional, so they are the graphs
of the configurations they describe. -/
noncomputable def haltWalkEquiv :
    {ρ : tmGuessBlock.Assignment A //
        @Sentence.Realize tqSOLang A
          (@sumStructure Language.turing tmGuessBlock.lang A _ (tmGuessBlock.structure ρ))
          sharpTqKernel} ≃
      {conf : A → Config A // (tmData A).WellFormed ∧ (tmData A).IsHaltWalk conf} where
  toFun ρ :=
    ⟨((realize_sharpTqKernel ρ.1).mp ρ.2).2.walk.conf,
      ((realize_sharpTqKernel ρ.1).mp ρ.2).1, ((realize_sharpTqKernel ρ.1).mp ρ.2).2.isHaltWalk⟩
  invFun c :=
    ⟨confAssign c.1, (realize_sharpTqKernel _).mpr ⟨c.2.1, c.2.2.relHaltWalk⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    refine Subtype.ext (funext fun i => ?_)
    have hw := ((realize_sharpTqKernel ρ).mp hρ).2.walk
    cases i with
    | state =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw' : ρ .state ![w 0, w 1] ↔ ρ .state w :=
        iff_of_eq (congrArg (ρ .state) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.qex (w 0)).choose_spec,
        fun h => hw.quniq (w 0) _ _ h (hw.qex (w 0)).choose_spec⟩
    | head =>
      refine funext fun (w : Fin 2 → A) => propext ?_
      have hw' : ρ .head ![w 0, w 1] ↔ ρ .head w :=
        iff_of_eq (congrArg (ρ .head) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.hex (w 0)).choose_spec,
        fun h => hw.huniq (w 0) _ _ h (hw.hex (w 0)).choose_spec⟩
    | tape =>
      refine funext fun (w : Fin 3 → A) => propext ?_
      have hw' : ρ .tape ![w 0, w 1, w 2] ↔ ρ .tape w :=
        iff_of_eq (congrArg (ρ .tape) (funext fun k => by fin_cases k <;> rfl))
      refine Iff.trans ?_ hw'
      exact ⟨fun h => h ▸ (hw.tex (w 0) (w 1)).choose_spec,
        fun h => hw.tuniq (w 0) (w 1) _ _ h (hw.tex (w 0) (w 1)).choose_spec⟩
  right_inv := by
    rintro ⟨conf, hconf⟩
    refine Subtype.ext (funext fun t => ?_)
    have hw := ((realize_sharpTqKernel (confAssign conf)).mp
      ((realize_sharpTqKernel _).mpr ⟨hconf.1, hconf.2.relHaltWalk⟩)).2.walk
    exact Config.ext (hw.qex t).choose_spec (hw.hex t).choose_spec
      (funext fun p => (hw.tex t p).choose_spec)

/-- The number of halting walks is the number of witnesses of the kernel. -/
theorem card_haltWalk_eq_witnessCount :
    Nat.card {conf : A → Config A // (tmData A).WellFormed ∧ (tmData A).IsHaltWalk conf} =
      witnessCount tmGuessBlock sharpTqKernel A :=
  (Nat.card_congr (haltWalkEquiv A)).symm

end Count

/-! ### The counting problem -/

/-- **Counting accepting runs**: the number of runs of the machine described by
the instance that reach an accepting state within as many steps as there are
positions, each counted up to the first accepting configuration it reaches,
through its layout along the positions (`DescriptiveComplexity.TMData.IsHaltWalk`). As
for `DescriptiveComplexity.NTMAccept`, the well-formedness promises are folded in: an
ill-formed instance has no run. -/
noncomputable def SharpNTMAccept : CountingProblem Language.turing where
  Count := fun A inst =>
    Nat.card {conf : A → Config A //
      @TMData.WellFormed A (@tmData A inst) ∧ @TMData.IsHaltWalk A (@tmData A inst) conf}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_haltWalk_eq_witnessCount A, card_haltWalk_eq_witnessCount B]
    exact witnessCount_iso tmGuessBlock sharpTqKernel e

theorem sharpNtmAccept_apply (A : Type) [Language.turing.Structure A] :
    SharpNTMAccept A =
      Nat.card {conf : A → Config A //
        (tmData A).WellFormed ∧ (tmData A).IsHaltWalk conf} :=
  rfl

/-- **The support of counting accepting runs is machine acceptance.** -/
theorem sharpNtmAccept_support_iff (A : Type) [Language.turing.Structure A] [Finite A] :
    SharpNTMAccept.support A ↔ NTMAccept A := by
  have hfin : Finite {conf : A → Config A //
      (tmData A).WellFormed ∧ (tmData A).IsHaltWalk conf} :=
    Finite.of_equiv _ (haltWalkEquiv A)
  rw [CountingProblem.support_iff, sharpNtmAccept_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨conf, hwf, hconf⟩, -⟩
    exact ⟨hwf, (TMData.accepts_iff_exists_haltWalk hwf).mpr ⟨conf, hconf⟩⟩
  · rintro ⟨hwf, hacc⟩
    obtain ⟨conf, hconf⟩ := (TMData.accepts_iff_exists_haltWalk hwf).mp hacc
    exact ⟨⟨⟨conf, hwf, hconf⟩⟩, hfin⟩

/-- **Counting accepting runs is in `#P`**: the runs are the witnesses of an
existential second-order sentence, the tableau of a run being determined by
it. -/
theorem sharpNtmAccept_mem_sharpP : SharpNTMAccept ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_haltWalk_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel tmGuessBlock sharpTqKernel)

/-- **The textbook counting Cook–Levin theorem**: counting the accepting runs
of a machine reduces, parsimoniously, to counting the models of a CNF formula.
As on the decision side, no tableau-to-CNF encoding appears: the `Σ₁`
definition of a run feeds the generic parsimonious Tseitin reduction. -/
theorem sharpNtmAccept_reduces_to_sharpSat : Nonempty (SharpNTMAccept ≤ᵖ[≤] SharpSAT) :=
  sharpSat_parsimoniousHard_of_sharpPDefinable SharpNTMAccept sharpNtmAccept_mem_sharpP

end DescriptiveComplexity
