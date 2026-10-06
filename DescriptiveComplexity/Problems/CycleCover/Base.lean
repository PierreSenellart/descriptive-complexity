/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Counting
import DescriptiveComplexity.Permanent.CycNext
import DescriptiveComplexity.Permanent.Flat
import DescriptiveComplexity.Permanent.Minor

/-!
# The base graph of a #1-in-SAT instance

The reduction of #1-in-SAT to #Cycle Cover attaches Valiant's XOR gadget at
one **site** per occurrence of a literal in a clause; this file builds the
**base graph** the gadgets are attached to, and evaluates the terms of the XOR
sum (`DescriptiveComplexity.Site.xorSum`) it leaves.

## The graph

An **occurrence** (`DescriptiveComplexity.SatCover.Occ`) is a real one, the
literal `(x, s)` in the clause `c`, or a *dummy* one, the literal `(x, s)` in
the tautological clause `x ∨ ¬x` added for every variable `x`; the dummy
clause is written `⊥`. Every occurrence `o` has a **track node** `trk o` and a
**spoke** `spk o`, and every clause, dummy ones included, a **hub**. The base
edges are:

* the **track** of each literal `(x, s)`: a cycle through the track nodes of
  its occurrences, in the order of the clauses, the dummy occurrence first
  (`DescriptiveComplexity.SatCover.nextOcc`, built on
  `DescriptiveComplexity.cycNext`);
* from each spoke to its hub, and from each hub to each of its spokes.

The site of an occurrence pairs the self-loop at its track node with the
self-loop at its spoke, so that exactly one of the two is used: the track
loop when the literal is **true** and the spoke loop when it is **false**.
A cycle cover of the base graph with the chosen loops forced is then unique
when the choice is **consistent**
(`DescriptiveComplexity.SatCover.Consistent`) – the track of a literal is
used entirely or not at all, so the loops of a literal are all chosen or
none, exactly one loop of the two dummy occurrences of a variable is chosen,
so that each variable has one value, and exactly one spoke of each clause is
free to close a cycle with its hub, so that each clause has exactly one true
literal – and does not exist otherwise
(`DescriptiveComplexity.SatCover.pdel_base`). The consistent choices are the
exactly-one models (`DescriptiveComplexity.SatCover.consistentEquiv`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc Finset

namespace SatCover

variable {A : Type} [Language.sat.Structure A]

/-! ### Occurrences and nodes -/

/-- An occurrence is valid when it is a real one, `(x, s)` in the clause `c`,
or the dummy one of a variable. -/
def OccValid (o : WithBot A × A × Bool) : Prop :=
  (o.1 = ⊥ ∧ SatOccurs A o.2.1) ∨ ∃ c : A, o.1 = c ∧ OccIn c o.2.1 o.2.2

/-- **The occurrences**: the real ones and the dummy ones. -/
abbrev Occ (A : Type) [Language.sat.Structure A] : Type :=
  {o : WithBot A × A × Bool // OccValid o}

namespace Occ

variable (o : Occ A)

/-- The clause of an occurrence, `⊥` for a dummy one. -/
abbrev c : WithBot A := o.1.1

/-- The variable of an occurrence. -/
abbrev x : A := o.1.2.1

/-- The sign of an occurrence. -/
abbrev s : Bool := o.1.2.2

theorem ext {o o' : Occ A} (hc : o.c = o'.c) (hx : o.x = o'.x) (hs : o.s = o'.s) : o = o' :=
  Subtype.ext (Prod.ext hc (Prod.ext hx hs))

/-- The variable of an occurrence is a variable of the formula. -/
theorem satOccurs : SatOccurs A o.x := by
  obtain ⟨⟨c, x, s⟩, hv⟩ := o
  rcases hv with ⟨_, h⟩ | ⟨c', _, hc, h⟩
  · exact h
  · cases s
    · exact ⟨c', hc, Or.inr h⟩
    · exact ⟨c', hc, Or.inl h⟩

theorem occIn_of_coe {c : A} (h : o.c = c) : OccIn c o.x o.s := by
  rcases o.2 with ⟨hb, _⟩ | ⟨c', hc', h'⟩
  · exact absurd (hb.symm.trans h) WithBot.bot_ne_coe
  · exact WithBot.coe_injective (hc'.symm.trans h) ▸ h'

/-- The dummy occurrence of a variable. -/
def dummy (x : A) (hx : SatOccurs A x) (s : Bool) : Occ A :=
  ⟨(⊥, x, s), Or.inl ⟨rfl, hx⟩⟩

/-- A real occurrence. -/
def real (c x : A) (s : Bool) (h : OccIn c x s) : Occ A :=
  ⟨(c, x, s), Or.inr ⟨c, rfl, h⟩⟩

end Occ

/-- **The hubs**: one per clause, and one per variable for its dummy
clause. -/
abbrev Hub (A : Type) [Language.sat.Structure A] : Type :=
  {c : A // IsCl c} ⊕ {x : A // SatOccurs A x}

/-- **The nodes of the base graph**: a track node and a spoke per occurrence,
and the hubs. -/
abbrev Node (A : Type) [Language.sat.Structure A] : Type :=
  Occ A ⊕ Occ A ⊕ Hub A

/-- The track node of an occurrence. -/
abbrev trk (o : Occ A) : Node A := Sum.inl o

/-- The spoke of an occurrence. -/
abbrev spk (o : Occ A) : Node A := Sum.inr (Sum.inl o)

/-- A hub, as a node. -/
abbrev hub (h : Hub A) : Node A := Sum.inr (Sum.inr h)

open Classical in
/-- The hub of the clause of an occurrence. -/
noncomputable def hubOf (o : Occ A) : Hub A :=
  if h : o.c = ⊥ then Sum.inr ⟨o.x, o.satOccurs⟩
  else Sum.inl ⟨o.c.unbot h, (o.occIn_of_coe (WithBot.coe_unbot _ h).symm).isCl⟩

theorem hubOf_of_bot {o : Occ A} (h : o.c = ⊥) : hubOf o = Sum.inr ⟨o.x, o.satOccurs⟩ := by
  rw [hubOf, dite_eq_left h]

theorem hubOf_of_coe {o : Occ A} {c : A} (h : o.c = c) :
    hubOf o = Sum.inl ⟨c, (o.occIn_of_coe h).isCl⟩ := by
  have h' : o.c ≠ ⊥ := h ▸ WithBot.coe_ne_bot
  rw [hubOf, dite_eq_right h']
  exact congrArg Sum.inl (Subtype.ext (by
    change o.c.unbot h' = c
    exact WithBot.coe_injective ((WithBot.coe_unbot _ h').trans h)))

/-- The hub of an occurrence is that of a clause iff the occurrence is in
the clause. -/
theorem hubOf_eq_inl_iff (o : Occ A) (c : {c : A // IsCl c}) : hubOf o = Sum.inl c ↔ o.c = c.1 := by
  constructor
  · intro h
    by_cases hb : o.c = ⊥
    · rw [hubOf_of_bot hb] at h
      exact absurd h Sum.inr_ne_inl
    · obtain ⟨c', hc'⟩ := WithBot.ne_bot_iff_exists.mp hb
      rw [hubOf_of_coe hc'.symm] at h
      rw [← hc']
      exact congrArg (fun c : {c : A // IsCl c} => ((c.1 : A) : WithBot A)) (Sum.inl.inj h)
  · intro h
    rw [hubOf_of_coe h]

/-- The hub of an occurrence is that of a variable iff the occurrence is the
dummy one of the variable. -/
theorem hubOf_eq_inr_iff (o : Occ A) (x : {x : A // SatOccurs A x}) :
    hubOf o = Sum.inr x ↔ o.c = ⊥ ∧ o.x = x.1 := by
  constructor
  · intro h
    by_cases hb : o.c = ⊥
    · rw [hubOf_of_bot hb] at h
      exact ⟨hb, congrArg Subtype.val (Sum.inr.inj h)⟩
    · obtain ⟨c', hc'⟩ := WithBot.ne_bot_iff_exists.mp hb
      rw [hubOf_of_coe hc'.symm] at h
      exact absurd h Sum.inl_ne_inr
  · rintro ⟨hb, hx⟩
    rw [hubOf_of_bot hb]
    exact congrArg Sum.inr (Subtype.ext hx)

/-! ### The tracks -/

variable [LinearOrder A] [Fintype A]

open Classical in
/-- The clauses an occurrence of the literal `(x, s)` can be in, the dummy
clause `⊥` first. -/
noncomputable def chain (x : A) (s : Bool) : Finset (WithBot A) :=
  insert ⊥ ((univ.filter fun c : A => OccIn c x s).image WithBot.some)

theorem mem_chain {x : A} {s : Bool} {c : WithBot A} :
    c ∈ chain x s ↔ c = ⊥ ∨ ∃ c' : A, c = c' ∧ OccIn c' x s := by
  classical
  simp only [chain, mem_insert, mem_image, mem_filter, mem_univ, true_and]
  exact or_congr_right (exists_congr fun c' => ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩)

theorem c_mem_chain (o : Occ A) : o.c ∈ chain o.x o.s := by
  rw [mem_chain]
  rcases o.2 with ⟨h, _⟩ | ⟨c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, h⟩

theorem chain_nonempty (x : A) (s : Bool) : (chain x s).Nonempty :=
  ⟨⊥, mem_chain.mpr (Or.inl rfl)⟩

/-- **The next occurrence of the same literal**, cyclically. -/
noncomputable def nextOcc (o : Occ A) : Occ A :=
  ⟨(cycNext (chain o.x o.s) o.c, o.x, o.s), by
    rcases mem_chain.mp (cycNext_mem (chain_nonempty o.x o.s) o.c) with h | ⟨c, hc, h⟩
    · exact Or.inl ⟨h, o.satOccurs⟩
    · exact Or.inr ⟨c, hc, h⟩⟩

@[simp] theorem nextOcc_c (o : Occ A) : (nextOcc o).c = cycNext (chain o.x o.s) o.c := rfl

@[simp] theorem nextOcc_x (o : Occ A) : (nextOcc o).x = o.x := rfl

@[simp] theorem nextOcc_s (o : Occ A) : (nextOcc o).s = o.s := rfl

theorem nextOcc_injective : Function.Injective (nextOcc (A := A)) := by
  intro o o' h
  have hx : o.x = o'.x := by simpa only [nextOcc_x] using congrArg Occ.x h
  have hs : o.s = o'.s := by simpa only [nextOcc_s] using congrArg Occ.s h
  refine Occ.ext ?_ hx hs
  have hc := congrArg Occ.c h
  rw [nextOcc_c, nextOcc_c, hx, hs] at hc
  exact cycNext_injOn _ (hx ▸ hs ▸ c_mem_chain o) (c_mem_chain o') hc

/-! ### The base edges -/

/-- **The edges of the base graph.** -/
inductive BaseEdge : Node A → Node A → Prop
  /-- Along the track of a literal. -/
  | track (o : Occ A) : BaseEdge (trk o) (trk (nextOcc o))
  /-- From a spoke to its hub. -/
  | spoke (o : Occ A) : BaseEdge (spk o) (hub (hubOf o))
  /-- From a hub to each of its spokes. -/
  | hub (o : Occ A) : BaseEdge (hub (hubOf o)) (spk o)

theorem baseEdge_trk_iff {o : Occ A} {n : Node A} :
    BaseEdge (trk o) n ↔ n = trk (nextOcc o) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .track o

theorem baseEdge_spk_iff {o : Occ A} {n : Node A} : BaseEdge (spk o) n ↔ n = hub (hubOf o) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .spoke o

theorem baseEdge_hub_iff {h : Hub A} {n : Node A} :
    BaseEdge (hub h) n ↔ ∃ o, n = spk o ∧ hubOf o = h := by
  constructor
  · intro h'
    cases h' with
    | hub o => exact ⟨o, rfl, rfl⟩
  · rintro ⟨o, rfl, rfl⟩
    exact .hub o

theorem baseEdge_to_trk_iff {n : Node A} {o' : Occ A} :
    BaseEdge n (trk o') ↔ ∃ o, n = trk o ∧ nextOcc o = o' := by
  constructor
  · intro h
    cases h with
    | track o => exact ⟨o, rfl, rfl⟩
  · rintro ⟨o, rfl, rfl⟩
    exact .track o

theorem baseEdge_to_spk_iff {n : Node A} {o : Occ A} : BaseEdge n (spk o) ↔ n = hub (hubOf o) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .hub o

theorem baseEdge_to_hub_iff {n : Node A} {h : Hub A} :
    BaseEdge n (hub h) ↔ ∃ o, n = spk o ∧ hubOf o = h := by
  constructor
  · intro h'
    cases h' with
    | spoke o => exact ⟨o, rfl, rfl⟩
  · rintro ⟨o, rfl, rfl⟩
    exact .spoke o

open Classical in
/-- **The base matrix**: the adjacency matrix of the base graph. -/
noncomputable def baseM : Node A → Node A → ℤ :=
  fun n n' => if BaseEdge n n' then 1 else 0

/-! ### The sites and the choices -/

instance instFintypeWithBot : Fintype (WithBot A) := inferInstanceAs (Fintype (Option A))

omit [LinearOrder A] [Fintype A] in
instance instFiniteWithBot [Finite A] : Finite (WithBot A) := inferInstanceAs (Finite (Option A))

open Classical in
noncomputable instance instFintypeOcc : Fintype (Occ A) := Subtype.fintype _

open Classical in
noncomputable instance instFintypeHub : Fintype (Hub A) := inferInstance

noncomputable instance instFintypeNode : Fintype (Node A) := inferInstance

instance instDecidableEqOcc : DecidableEq (Occ A) := Subtype.instDecidableEq

set_option synthInstance.maxSize 512 in
instance instDecidableEqHub : DecidableEq (Hub A) := inferInstance

set_option synthInstance.maxSize 512 in
instance instDecidableEqNode : DecidableEq (Node A) := inferInstance

/-- **The site of an occurrence**: the self-loop at its track node, used when
the literal is true, paired with the self-loop at its spoke, used when it is
false. -/
def site (o : Occ A) : Site (Node A) :=
  ⟨trk o, spk o, trk o, spk o⟩

/-- The rows deleted by the choice `U` of the occurrences whose track loop is
used: their track nodes, and the spokes of the other occurrences. -/
noncomputable def del (U : Finset (Occ A)) : Finset (Node A) :=
  U.image trk ∪ Uᶜ.image spk

theorem trk_mem_del {U : Finset (Occ A)} {o : Occ A} : trk o ∈ del U ↔ o ∈ U := by
  simp [del]

theorem spk_mem_del {U : Finset (Occ A)} {o : Occ A} : spk o ∈ del U ↔ o ∉ U := by
  simp [del]

theorem hub_notMem_del {U : Finset (Occ A)} {h : Hub A} : hub h ∉ del U := by
  simp [del]

/-- **A consistent choice**: the track loops of a literal are all chosen or
none (the track is then used entirely or not at all), and every hub has
exactly one spoke whose loop is not chosen, to close a cycle with. -/
def Consistent (U : Finset (Occ A)) : Prop :=
  (∀ o ∈ U, nextOcc o ∈ U) ∧ (∀ o, o ∉ U → nextOcc o ∉ U) ∧
    ∀ h : Hub A, ∃! o : Occ A, hubOf o = h ∧ o ∈ U

/-- The nodes left by a choice. -/
abbrev Rem (U : Finset (Occ A)) : Type := {n : Node A // n ∉ del U}

/-- A cycle cover of the base graph with the chosen loops forced: a
permutation of the remaining nodes along the base edges. -/
def Valid (U : Finset (Occ A)) (e : Rem U ≃ Rem U) : Prop :=
  ∀ n, BaseEdge n.1 (e n).1

/-- **A forced cover exists only for a consistent choice.** -/
theorem consistent_of_valid {U : Finset (Occ A)} {e : Rem U ≃ Rem U} (he : Valid U e) :
    Consistent U := by
  refine ⟨fun o ho => ?_, fun o ho => ?_, fun h => ?_⟩
  · by_contra hn
    have hm := he (e.symm ⟨trk (nextOcc o), trk_mem_del.not.mpr hn⟩)
    rw [Equiv.apply_symm_apply] at hm
    obtain ⟨o', ho', hn'⟩ := baseEdge_to_trk_iff.mp hm
    rw [nextOcc_injective hn'] at ho'
    exact (e.symm _).2 (ho' ▸ trk_mem_del.mpr ho)
  · have hm := he ⟨trk o, trk_mem_del.not.mpr ho⟩
    rw [baseEdge_trk_iff] at hm
    exact fun hn => (e _).2 (hm ▸ trk_mem_del.mpr hn)
  · have hm := he ⟨hub h, hub_notMem_del⟩
    obtain ⟨o, ho, hoh⟩ := baseEdge_hub_iff.mp hm
    have hoU : o ∈ U := by
      have h2 := (e ⟨hub h, hub_notMem_del⟩).2
      rw [ho] at h2
      exact not_not.mp (spk_mem_del.not.mp h2)
    refine ⟨o, ⟨hoh, hoU⟩, fun o' ⟨hoh', ho'⟩ => ?_⟩
    have h1 := he ⟨spk o, spk_mem_del.not.mpr (not_not.mpr hoU)⟩
    have h2 := he ⟨spk o', spk_mem_del.not.mpr (not_not.mpr ho')⟩
    rw [baseEdge_spk_iff] at h1 h2
    have := e.injective (Subtype.ext ((h2.trans (congrArg hub (hoh'.trans hoh.symm))).trans
      h1.symm))
    exact Sum.inl.inj (Sum.inr.inj (congrArg Subtype.val this))

/-- **The forced cover of a consistent choice**, as a map: along the tracks,
from each spoke to its hub, from each hub to its one free spoke. -/
noncomputable def forced {U : Finset (Occ A)} (hU : Consistent U) : Rem U → Rem U
  | ⟨Sum.inl o, h⟩ => ⟨trk (nextOcc o), trk_mem_del.not.mpr (hU.2.1 o (trk_mem_del.not.mp h))⟩
  | ⟨Sum.inr (Sum.inl o), _⟩ => ⟨hub (hubOf o), hub_notMem_del⟩
  | ⟨Sum.inr (Sum.inr h), _⟩ => ⟨spk (Classical.choose (hU.2.2 h).exists),
      spk_mem_del.not.mpr (not_not.mpr (Classical.choose_spec (hU.2.2 h).exists).2)⟩

theorem forced_injective {U : Finset (Occ A)} (hU : Consistent U) :
    Function.Injective (forced hU) := by
  rintro ⟨n, hn⟩ ⟨n', hn'⟩ h
  rcases n with o | o | k <;> rcases n' with o' | o' | k' <;>
    simp only [forced, Subtype.mk.injEq, trk, spk, hub, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at h
  · exact Subtype.ext (congrArg Sum.inl (nextOcc_injective h))
  · have ho : o ∈ U := not_not.mp (spk_mem_del.not.mp hn)
    have ho' : o' ∈ U := not_not.mp (spk_mem_del.not.mp hn')
    exact Subtype.ext (congrArg spk ((hU.2.2 (hubOf o)).unique ⟨rfl, ho⟩ ⟨h.symm, ho'⟩))
  · exact Subtype.ext (congrArg hub (((Classical.choose_spec (hU.2.2 k).exists).1.symm.trans
      (congrArg hubOf h)).trans (Classical.choose_spec (hU.2.2 k').exists).1))

/-- The forced cover of a consistent choice. -/
noncomputable def forcedEquiv {U : Finset (Occ A)} (hU : Consistent U) : Rem U ≃ Rem U :=
  Equiv.ofBijective (forced hU) (Finite.injective_iff_bijective.mp (forced_injective hU))

theorem valid_forcedEquiv {U : Finset (Occ A)} (hU : Consistent U) : Valid U (forcedEquiv hU) := by
  rintro ⟨n, hn⟩
  rcases n with o | o | h
  · exact .track o
  · exact .spoke o
  · exact baseEdge_hub_iff.mpr ⟨_, rfl, (Classical.choose_spec (hU.2.2 h).exists).1⟩

/-- **The forced cover is unique.** -/
theorem valid_unique {U : Finset (Occ A)} {e e' : Rem U ≃ Rem U} (he : Valid U e)
    (he' : Valid U e') : e = e' := by
  have hU := consistent_of_valid he
  refine Equiv.ext fun ⟨n, hn⟩ => Subtype.ext ?_
  rcases n with o | o | h
  · exact (baseEdge_trk_iff.mp (he ⟨trk o, hn⟩)).trans (baseEdge_trk_iff.mp (he' ⟨trk o, hn⟩)).symm
  · exact (baseEdge_spk_iff.mp (he ⟨spk o, hn⟩)).trans (baseEdge_spk_iff.mp (he' ⟨spk o, hn⟩)).symm
  · obtain ⟨o, ho, hoh⟩ := baseEdge_hub_iff.mp (he ⟨hub h, hn⟩)
    obtain ⟨o', ho', hoh'⟩ := baseEdge_hub_iff.mp (he' ⟨hub h, hn⟩)
    rw [ho, ho', (hU.2.2 h).unique ⟨hoh, not_not.mp (spk_mem_del.not.mp (ho ▸ (e _).2))⟩
      ⟨hoh', not_not.mp (spk_mem_del.not.mp (ho' ▸ (e' _).2))⟩]

open Classical in
/-- **The term of the XOR sum of a choice**: `1` when the choice is
consistent, `0` otherwise. -/
theorem pdel_base (U : Finset (Occ A)) :
    pdel baseM (del U) (del U) = if Consistent U then 1 else 0 := by
  rw [pdel]
  change bperm (fun a b : Rem U => if BaseEdge a.1 b.1 then (1 : ℤ) else 0) = _
  rw [bperm_boole]
  by_cases hU : Consistent U
  · rw [ite_eq_left hU, Nat.cast_eq_one, Fintype.card_eq_one_iff]
    exact ⟨⟨forcedEquiv hU, valid_forcedEquiv hU⟩, fun e =>
      Subtype.ext (valid_unique e.2 (valid_forcedEquiv hU))⟩
  · rw [ite_eq_right hU, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact ⟨fun e => hU (consistent_of_valid e.2)⟩

/-! ### The XOR sum over all the choices -/

open Site

omit [LinearOrder A] [Fintype A] in
theorem site_injective : Function.Injective (site (A := A)) :=
  fun _ _ h => Sum.inl.inj (congrArg Site.u h)

omit [LinearOrder A] [Fintype A] in
theorem mem_cols_map_site {l : List (Occ A)} {n : Node A} :
    n ∈ cols (l.map site) ↔ ∃ o ∈ l, n = trk o ∨ n = spk o := by
  induction l with
  | nil => simp [cols]
  | cons o l ih =>
    simp only [List.map_cons, cols, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨o', ho', h⟩)
      · exact ⟨o, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨o, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨o', Or.inr ho', h⟩
    · rintro ⟨o', rfl | ho', h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨o', ho', Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨o', ho', Or.inr h⟩)

omit [LinearOrder A] [Fintype A] in
theorem cols_map_site_nodup {l : List (Occ A)} (hl : l.Nodup) : (cols (l.map site)).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons o l ih =>
    have hnd := List.nodup_cons.mp hl
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ih hnd.2⟩⟩
    · rw [List.mem_cons, mem_cols_map_site, not_or]
      refine ⟨Sum.inl_ne_inr, ?_⟩
      rintro ⟨o', ho', h | h⟩
      · exact hnd.1 (Sum.inl.inj h ▸ ho')
      · exact Sum.inl_ne_inr h
    · rw [mem_cols_map_site]
      rintro ⟨o', ho', h | h⟩
      · exact Sum.inr_ne_inl h
      · exact hnd.1 (Sum.inl.inj (Sum.inr.inj h) ▸ ho')

/-- The sites, enumerated. -/
noncomputable def sites : List (Site (Node A)) :=
  univ.toList.map site

theorem sites_toFinset : (sites (A := A)).toFinset = univ.image site := by
  ext s
  simp only [sites, List.mem_toFinset, List.mem_map, Finset.mem_toList, mem_univ, true_and,
    mem_image]

/-- The rows deleted by a choice, as the sites read them. -/
theorem delRows_sites (U : Finset (Occ A)) : delRows sites (U.image site) = del U := by
  have hmem : ∀ o, (∃ a ∈ U, site a = site o) ↔ o ∈ U := fun o =>
    ⟨fun ⟨o', ho', h'⟩ => site_injective h' ▸ ho', fun h => ⟨o, h, rfl⟩⟩
  ext n
  simp only [delRows, sites_toFinset, image_image, mem_image, mem_univ, true_and,
    Function.comp_apply, hmem, del, mem_union, mem_compl]
  constructor
  · rintro ⟨o, rfl⟩
    by_cases ho : o ∈ U
    · rw [ite_eq_left ho]
      exact Or.inl ⟨o, ho, rfl⟩
    · rw [ite_eq_right ho]
      exact Or.inr ⟨o, ho, rfl⟩
  · rintro (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩)
    · exact ⟨o, by rw [ite_eq_left ho]; rfl⟩
    · exact ⟨o, by rw [ite_eq_right ho]; rfl⟩

open Classical in
/-- **The permanent of the base graph with the gadgets attached**: `4` to the
number of sites, times the number of consistent choices. -/
theorem bperm_attachAll_sites :
    bperm (attachAll baseM (sites (A := A))) =
      4 ^ Fintype.card (Occ A) * ((univ : Finset (Finset (Occ A))).filter Consistent).card := by
  have hu : ∀ s ∈ sites (A := A), s.u ≠ s.u' := by
    simp only [sites, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun _ _ => Sum.inl_ne_inr
  have hcols : (cols (sites (A := A))).Nodup := cols_map_site_nodup (Finset.nodup_toList _)
  have hself : ∀ s ∈ sites (A := A), s.v = s.u ∧ s.v' = s.u' := by
    simp only [sites, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun _ _ => ⟨rfl, rfl⟩
  have hlen : (sites (A := A)).length = Fintype.card (Occ A) := by
    rw [sites, List.length_map, Finset.length_toList, card_univ]
  rw [← pdel_empty, ← Finset.map_empty (baseEmb (sites (A := A))),
    pdel_attachAll baseM sites ∅ ∅ hu hcols (fun _ _ => ⟨notMem_empty _, notMem_empty _⟩),
    xorSum_eq_sum baseM sites hcols hself ∅ (fun _ _ => ⟨notMem_empty _, notMem_empty _⟩),
    sites_toFinset, powerset_image,
    Finset.sum_image fun _ _ _ _ h => image_injective site_injective h, hlen]
  congr 1
  rw [← Finset.sum_boole]
  exact Finset.sum_congr rfl fun U _ => by rw [empty_union, delRows_sites, pdel_base]

end SatCover

end DescriptiveComplexity
