/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax945089Proofs.DescriptiveComplexity.Iterate
import Mathlib.Data.Fintype.Pi
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
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
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax945089.EhrenfeuchtGames
import Lax945089.OrderFreeFirstOrder
import Lax945089.Parity
import Lax945089.PebbleGames
import Lax945089.TransitiveClosureReductions

/-!
# The `k`-pebble refinement, over an abstract initial relation

The combinatorial core of `k`-variable equivalence `≡ᵏ`
([Abiteboul–Vianu 1991][abiteboul1991generic];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 3), with no logic in sight:
positions are `k`-tuples over a bare type `A`, an *initial relation* `E₀`
stands in for «same atomic type», and one round of the `k`-pebble game refines
a relation `E` to `DescriptiveComplexity.pebbleRefine E₀ E` – the pairs that
are in `E₀` and survive one exchange of a pebble
(`DescriptiveComplexity.PebbleBackForth`).

`DescriptiveComplexity.EquivK E₀` is the limit of the descending refinement
chain `DescriptiveComplexity.pebbleStage`, that is, the *greatest* fixed point
of the refinement:

* the chain plateaus within the number of pairs of tuples
  (`DescriptiveComplexity.exists_pebbleStage_succ_eq`, the antitone half of
  `DescriptiveComplexity.exists_succ_eq_of_antitone_subset`), so on a finite
  type the limit is a stage and is itself a fixed point
  (`DescriptiveComplexity.equivK_iff`, the interface characterization);
* any relation below `E₀` that survives its own back-and-forth condition is
  below the limit (`DescriptiveComplexity.le_equivK`, the coinduction
  principle), which is what «greatest» means and how anything is ever proved
  `≡ᵏ`-equivalent;
* the limit is an equivalence relation whenever `E₀` is
  (`DescriptiveComplexity.equivK_equivalence`);
* refining the initial relation by anything the limit already refines does not
  change the limit (`DescriptiveComplexity.equivK_inf_eq`) – read with `E₀'`
  the agreement on a `≡ᵏ`-invariant relation, this is the *expansion* lemma:
  `≡ᵏ` is unchanged when the structure is expanded by an `≡ᵏ`-invariant
  relation. It is the lemma that carries the `≡ᵏ`-invariance of fixed-point
  logics, each stage of an induction being such an expansion.

Keeping `E₀` abstract keeps the vocabulary out: the instantiation at «same
atomic type over a structure» – necessarily over the *finitely many* symbols a
definition actually mentions – is where the logic enters, and lives with the
invariance results for the fixed-point logics, not here. The same skeleton
with rounds in place of pebbles is the Ehrenfeucht–Fraïssé refinement, a
second consumer this file is stated to serve.
-/

namespace Lax945089Proofs.DescriptiveComplexity

/-! ### Relations on `k`-tuples -/

/-- A relation between `k`-tuples over `A`: the positions of the `k`-pebble
game. -/
abbrev PebbleRel (A : Type) (k : ℕ) : Type :=
  (Fin k → A) → (Fin k → A) → Prop

variable {A : Type} {k : ℕ}

/-- Pointwise implication of relations on `k`-tuples, spelled out (the
lattice order, kept explicit per the conventions of this library). -/
def PebbleRel.Le (E E' : PebbleRel A k) : Prop :=
  ∀ a b : Fin k → A, E a b → E' a b

/-! ### One round of the game -/

/-- The back-and-forth condition of the `k`-pebble game relative to a
relation `E`: whichever pebble the spoiler moves, on whichever side, the
duplicator can move the same pebble on the other side and stay in `E`. -/
def PebbleBackForth (E : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ i : Fin k,
    (∀ c : A, ∃ d : A, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : A, ∃ c : A, E (Function.update a i c) (Function.update b i d))

/-- One round of refinement: agree initially, and survive one exchange of a
pebble relative to `E`. -/
def pebbleRefine (E₀ E : PebbleRel A k) : PebbleRel A k :=
  fun a b => E₀ a b ∧ PebbleBackForth E a b

/-- The back-and-forth condition is monotone in the relation it is relative
to. -/
theorem pebbleBackForth_mono {E E' : PebbleRel A k} (h : E.Le E') :
    (PebbleBackForth E).Le (PebbleBackForth E') := by
  intro a b hab i
  refine ⟨fun c => ?_, fun d => ?_⟩
  · obtain ⟨d, hd⟩ := (hab i).1 c
    exact ⟨d, h _ _ hd⟩
  · obtain ⟨c, hc⟩ := (hab i).2 d
    exact ⟨c, h _ _ hc⟩

/-- One round of refinement is monotone in the refined relation. -/
theorem pebbleRefine_mono (E₀ : PebbleRel A k) {E E' : PebbleRel A k} (h : E.Le E') :
    (pebbleRefine E₀ E).Le (pebbleRefine E₀ E') :=
  fun a b hab => ⟨hab.1, pebbleBackForth_mono h a b hab.2⟩

/-! ### The refinement chain and its limit -/

/-- The descending refinement chain, from the all-relation: what one round
cannot yet tell apart, twice refined, thrice refined … -/
def pebbleStage (E₀ : PebbleRel A k) : ℕ → PebbleRel A k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine E₀ (pebbleStage E₀ n)

/-- **`k`-equivalence relative to an initial relation**: the limit of the
refinement chain – equivalently (`DescriptiveComplexity.equivK_iff`,
`DescriptiveComplexity.le_equivK`) the greatest fixed point of one round of
refinement. -/
def EquivK (E₀ : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ n, pebbleStage E₀ n a b

variable {E₀ : PebbleRel A k}

/-- The refinement chain descends. -/
theorem pebbleStage_succ_le (E₀ : PebbleRel A k) (n : ℕ) :
    (pebbleStage E₀ (n + 1)).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun a b _ => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih

/-- The refinement chain descends, monotonically. -/
theorem pebbleStage_le_of_le (E₀ : PebbleRel A k) {m n : ℕ} (hmn : m ≤ n) :
    (pebbleStage E₀ n).Le (pebbleStage E₀ m) := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ h => h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact fun a b h => ih (Nat.lt_succ_iff.mp hlt) a b (pebbleStage_succ_le E₀ n a b h)
    · rw [heq]; exact fun _ _ h => h

/-- The limit is below the initial relation. -/
theorem EquivK.initial {a b : Fin k → A} (h : EquivK E₀ a b) : E₀ a b :=
  (h 1).1

/-! ### Coinduction: the limit is the greatest post-fixed point -/

/-- **The coinduction principle**: a relation below its own refinement is
below the limit. This is how tuples are ever proved `≡ᵏ`-equivalent – exhibit
a back-and-forth system containing the pair. -/
theorem le_equivK {E : PebbleRel A k} (h : E.Le (pebbleRefine E₀ E)) :
    E.Le (EquivK E₀) := by
  intro a b hab n
  induction n generalizing a b with
  | zero => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih a b (h a b hab)

/-! ### Stabilization on a finite type -/

section Finite

variable [Finite A]

/-- The refinement chain plateaus within the number of pairs of `k`-tuples:
consecutive stages agree from there on. -/
theorem exists_pebbleStage_succ_eq (E₀ : PebbleRel A k) :
    ∃ N ≤ Nat.card ((Fin k → A) × (Fin k → A)),
      pebbleStage E₀ (N + 1) = pebbleStage E₀ N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_antitone_subset
    (c := fun n => {p : (Fin k → A) × (Fin k → A) | pebbleStage E₀ n p.1 p.2})
    (fun n p hp => pebbleStage_succ_le E₀ n p.1 p.2 hp)
  refine ⟨N, hN, ?_⟩
  funext a b
  exact propext ⟨fun h => (Set.ext_iff.mp heq (a, b)).mp h,
    fun h => (Set.ext_iff.mp heq (a, b)).mpr h⟩

omit [Finite A] in
private theorem pebbleStage_eq_of_succ_eq {N : ℕ}
    (hN : pebbleStage E₀ (N + 1) = pebbleStage E₀ N) {n : ℕ} (hn : N ≤ n) :
    pebbleStage E₀ n = pebbleStage E₀ N := by
  induction n with
  | zero => rw [Nat.le_zero.mp hn]
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with h | h
    · have : pebbleStage E₀ n = pebbleStage E₀ N := ih (by omega)
      calc pebbleStage E₀ (n + 1) = pebbleRefine E₀ (pebbleStage E₀ n) := rfl
        _ = pebbleRefine E₀ (pebbleStage E₀ N) := by rw [this]
        _ = pebbleStage E₀ N := hN
    · rw [le_antisymm hn h]

/-- **On a finite type the limit is a fixed point of the refinement** – the
greatest one, by `DescriptiveComplexity.le_equivK`. -/
theorem pebbleRefine_equivK (E₀ : PebbleRel A k) :
    pebbleRefine E₀ (EquivK E₀) = EquivK E₀ := by
  obtain ⟨N, hle, hN⟩ := exists_pebbleStage_succ_eq E₀
  have hlim : EquivK E₀ = pebbleStage E₀ N := by
    funext a b
    refine propext ⟨fun h => h N, fun h n => ?_⟩
    rcases Nat.le_total n N with hn | hn
    · exact pebbleStage_le_of_le E₀ hn a b h
    · rw [pebbleStage_eq_of_succ_eq hN hn]; exact h
  rw [hlim]
  exact hN

/-- **The interface characterization of `≡ᵏ` on a finite type**: initial
agreement together with the back-and-forth condition relative to `≡ᵏ`
itself. Consumers should use this, never the stages. -/
theorem equivK_iff (E₀ : PebbleRel A k) (a b : Fin k → A) :
    EquivK E₀ a b ↔ E₀ a b ∧ PebbleBackForth (EquivK E₀) a b := by
  conv_lhs => rw [← pebbleRefine_equivK E₀]
  exact Iff.rfl

/-- **The game move**: from an equivalent pair, moving a pebble on the left
can be answered on the right. -/
theorem EquivK.update {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (c : A) :
    ∃ d : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).1 c

/-- The game move, from the right. -/
theorem EquivK.update_right {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (d : A) :
    ∃ c : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).2 d

/-! ### Pair substructures

A tuple pair obtained by selecting, permuting and repeating coordinate pairs
of an equivalent pair is equivalent: duplicated pebbles only make the
duplicator's task easier. This is the well-definedness lemma behind every
operation on `≡ᵏ`-classes that rearranges coordinates – the substitution and
rearrangement relations of the invariant structure. -/

end Finite

/-! ### Equivalence -/

section Equivalence

end Equivalence

/-! ### Monotonicity and the expansion lemma -/

/-- The stages are monotone in the initial relation. -/
theorem pebbleStage_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) (n : ℕ) :
    (pebbleStage E₀' n).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    exact fun a b hab => ⟨h a b hab.1, pebbleBackForth_mono ih a b hab.2⟩

/-- `≡ᵏ` is monotone in the initial relation. -/
theorem equivK_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) :
    (EquivK E₀').Le (EquivK E₀) :=
  fun a b hab n => pebbleStage_mono h n a b (hab n)

/-- **The expansion lemma**: refining the initial relation by anything `≡ᵏ`
already refines does not change `≡ᵏ`. Read with `E₀'` the conjunction of `E₀`
and agreement on an `≡ᵏ`-invariant relation, this says `≡ᵏ` is unchanged when
the structure is expanded by an `≡ᵏ`-invariant relation – the lemma that
carries the `≡ᵏ`-invariance of the fixed-point logics, stage by stage. -/
theorem equivK_inf_eq [Finite A] {E₀ E₀' : PebbleRel A k} (hle : E₀'.Le E₀)
    (hinv : (EquivK E₀).Le E₀') : EquivK E₀' = EquivK E₀ := by
  funext a b
  refine propext ⟨fun h => equivK_mono hle a b h, fun h => ?_⟩
  refine le_equivK (E₀ := E₀') (E := EquivK E₀) (fun a b hab => ?_) a b h
  exact ⟨hinv a b hab, ((equivK_iff E₀ a b).mp hab).2⟩

end Lax945089Proofs.DescriptiveComplexity


