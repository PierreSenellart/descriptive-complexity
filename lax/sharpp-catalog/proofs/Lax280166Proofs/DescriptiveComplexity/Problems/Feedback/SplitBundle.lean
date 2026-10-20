/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Feedback.CountingArc
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques

namespace Lax280166.CountingFeedbackSets
end Lax280166.CountingFeedbackSets

namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingCliques (CliqueOfSizeOn)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingFeedbackSets (FasOfSizeOn)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Feedback (UncutArc)
end Lax280166Proofs.DescriptiveComplexity

/-!
# The conflict split graph: feedback arc sets with no slack

The graph behind the parsimonious hardness of #Feedback Arc Set, on a vertex
type of its own (`DescriptiveComplexity.SplitBundle.SB`).

The textbook reduction to Feedback Arc Set splits each vertex `a` into an
*internal arc* `vin a → vout a`, cutting which stands for removing `a`. It is
not parsimonious, for two reasons, and the graph of this file removes both.

* A *crossing* arc can be cut instead of an internal one. Here two vertices in
  conflict are joined by **two parallel paths** in each direction
  (`vout a → mid j a b → vin b`, `j : Bool`), so a crossing arc alone cuts
  nothing, and cutting a whole bundle costs two arcs where an internal arc
  costs one.
* A solution can be *padded*: a superset of a feedback arc set is one. So the
  instance has to leave no slack, and that is a property of the source. The
  conflict relation here is “distinct and not adjacent both ways” in a graph
  whose cliques are **at most as large as the marked set**
  (the promise of `DescriptiveComplexity.SplitBundle.card_fas_eq_card_clique`), and the
  threshold is the number of unmarked vertices. Keeping an internal arc is
  keeping a vertex, the kept vertices have to be pairwise adjacent, and there
  are too many of them to keep unless nothing is wasted.

The count then goes through
(`DescriptiveComplexity.SplitBundle.internal_of_fas`): a feedback arc set of the
threshold size with `b` arcs outside the internal ones cuts at most `b / 2`
bundles, the vertices that are neither cut nor at the source of a cut bundle
form a clique, and the promise bounds that clique. Hence `b = 0`: the feedback
arc sets of the threshold size are the complements of the cliques of the
threshold size, bijectively.

A graph with no marked vertex has one clique of the threshold size, the empty
one, and no promise to offer; it is sent to the graph with no arc.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace SplitBundle

/-- The vertices of the conflict split graph. -/
inductive SB (A : Type) : Type
  /-- The entry copy of a vertex. -/
  | vin (a : A)
  /-- The exit copy of a vertex. -/
  | vout (a : A)
  /-- The middle of one of the two parallel paths from `a` to `b`. -/
  | mid (j : Bool) (a b : A)

instance {A : Type} [Finite A] : Finite (SB A) := by
  let enc : SB A → Fin 3 × Bool × A × Option A := fun v =>
    match v with
    | .vin a => (0, false, a, none)
    | .vout a => (1, false, a, none)
    | .mid j a b => (2, j, a, some b)
  refine Finite.of_injective enc fun u v h => ?_
  cases u <;> cases v <;> simp_all [enc]

section Graph

variable {A : Type} (Adj : A → A → Prop) (K : A → Prop)

/-- Two vertices are in conflict: distinct, and not adjacent both ways. -/
def Conf (a b : A) : Prop := a ≠ b ∧ (¬Adj a b ∨ ¬Adj b a)

theorem Conf.symm {Adj : A → A → Prop} {a b : A} (h : Conf Adj a b) : Conf Adj b a :=
  ⟨h.1.symm, h.2.symm⟩

/-- The arcs of the conflict split graph – none if no vertex is marked. -/
def SArc : SB A → SB A → Prop
  | .vin a, .vout b => (∃ z, K z) ∧ a = b
  | .vout a, .mid _ a' b => (∃ z, K z) ∧ a = a' ∧ Conf Adj a b
  | .mid _ a b, .vin b' => (∃ z, K z) ∧ b = b' ∧ Conf Adj a b
  | _, _ => False

/-- The marked arcs: the internal arcs of the unmarked vertices. -/
def SMark : SB A → SB A → Prop
  | .vin a, .vout b => (∃ z, K z) ∧ a = b ∧ ¬K a
  | _, _ => False

/-- The feedback arc set of a set of vertices: the internal arcs of the
others. -/
def FS (S : A → Prop) : SB A → SB A → Prop
  | .vin a, .vout b => a = b ∧ ¬S a
  | _, _ => False

/-- The internal arcs of a set of vertices are as many as the set. -/
theorem ncard_internal (P : A → Prop) :
    {p : SB A × SB A | ∃ a, P a ∧ p = (.vin a, .vout a)}.ncard = {a | P a}.ncard := by
  have h : {p : SB A × SB A | ∃ a, P a ∧ p = (.vin a, .vout a)} =
      (fun a => ((SB.vin a, SB.vout a) : SB A × SB A)) '' {a | P a} := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [h, Set.ncard_image_of_injective _ fun a b hab => SB.vin.inj (congrArg Prod.fst hab)]

theorem fs_iff (S : A → Prop) (p : SB A × SB A) :
    FS S p.1 p.2 ↔ ∃ a, ¬S a ∧ p = (.vin a, .vout a) := by
  obtain ⟨u, v⟩ := p
  constructor
  · intro h
    cases u <;> cases v <;> try exact (h : False).elim
    obtain ⟨hab, hS⟩ := h
    subst hab
    exact ⟨_, hS, rfl⟩
  · rintro ⟨a, ha, hp⟩
    rw [Prod.mk.injEq] at hp
    rw [hp.1, hp.2]
    exact ⟨rfl, ha⟩

theorem smark_iff (hK : ∃ z, K z) (p : SB A × SB A) :
    SMark K p.1 p.2 ↔ ∃ a, ¬K a ∧ p = (.vin a, .vout a) := by
  obtain ⟨u, v⟩ := p
  constructor
  · intro h
    cases u <;> cases v <;> try exact (h : False).elim
    obtain ⟨-, hab, hS⟩ := h
    subst hab
    exact ⟨_, hS, rfl⟩
  · rintro ⟨a, ha, hp⟩
    rw [Prod.mk.injEq] at hp
    rw [hp.1, hp.2]
    exact ⟨hK, rfl, ha⟩

theorem ncard_smark (hK : ∃ z, K z) :
    {p : SB A × SB A | SMark K p.1 p.2}.ncard = {a | ¬K a}.ncard := by
  rw [← ncard_internal fun a => ¬K a]
  exact congrArg Set.ncard (Set.ext fun p => smark_iff K hK p)

variable [Finite A]

/-! ### From a clique to a feedback arc set -/

open Classical in
/-- The rank certifying that cutting the internal arcs outside a clique leaves
an acyclic graph. -/
noncomputable def rk (S : A → Prop) : SB A → ℤ
  | .vin a => if S a then 0 else 3
  | .vout a => if S a then 1 else -2
  | .mid _ a _ => if S a then 2 else -1

/-- **The internal arcs outside a clique of the threshold size are a feedback
arc set of the threshold size.** -/
theorem fas_of_clique (hK : ∃ z, K z) {S : A → Prop} (hS : Lax280166.CountingCliques.CliqueOfSizeOn Adj K S) :
    Lax280166.CountingFeedbackSets.FasOfSizeOn (SArc Adj K) (SMark K) (FS S) := by
  classical
  refine ⟨fun u v h => ?_, ?_, ?_⟩
  · cases u <;> cases v <;> try exact (h : False).elim
    exact ⟨hK, h.1⟩
  · refine (acyclicRel_iff_exists_order _).mpr ⟨fun u v => rk S u < rk S v,
      fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, fun _ => lt_irrefl _, ?_⟩
    rintro u v ⟨harc, hcut⟩
    cases u <;> cases v <;> try exact (harc : False).elim
    · rename_i a b
      obtain ⟨-, hab⟩ := harc
      subst hab
      have hSa : S a := by
        by_contra h
        exact hcut ⟨rfl, h⟩
      simp [rk, hSa]
    · rename_i a j a' b
      obtain ⟨-, hab, -⟩ := harc
      subst hab
      by_cases hSa : S a <;> simp [rk, hSa]
    · rename_i j a b b'
      obtain ⟨-, hbb, hconf⟩ := harc
      subst hbb
      by_cases hSa : S a
      · have hSb : ¬S b := fun hSb =>
          hconf.2.elim (fun h => h (hS.1 a b hSa hSb hconf.1))
            fun h => h (hS.1 b a hSb hSa hconf.1.symm)
        simp [rk, hSa, hSb]
      · by_cases hSb : S b <;> simp [rk, hSa, hSb]
  · rw [ncard_smark K hK, ← (ncard_not_eq_iff S K).mpr hS.2,
      ← ncard_internal fun a => ¬S a]
    exact congrArg Set.ncard (Set.ext fun p => fs_iff S p)

/-! ### From a feedback arc set to a clique -/

/-- The vertex and the path an arc of a bundle belongs to. -/
def bundleOf : SB A × SB A → Option (A × Bool)
  | (.mid j a _, _) => some (a, j)
  | (_, .mid j a _) => some (a, j)
  | _ => none

/-- **A feedback arc set of the threshold size consists of internal arcs, and
the vertices it keeps are a clique of the threshold size** – provided no clique
is larger than the marked set. -/
theorem internal_of_fas (hK : ∃ z, K z)
    (hP : ∀ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adj x y) →
      {x | S x}.ncard ≤ {x | K x}.ncard)
    {F : SB A → SB A → Prop} (hF : Lax280166.CountingFeedbackSets.FasOfSizeOn (SArc Adj K) (SMark K) F) :
    Lax280166.CountingCliques.CliqueOfSizeOn Adj K (fun a => ¬F (.vin a) (.vout a)) ∧
      F = FS fun a => ¬F (.vin a) (.vout a) := by
  classical
  obtain ⟨-, hac, hcard⟩ := hF
  -- a bundle is cut when both its paths are
  have hT : ∀ x y, (¬F (.vin x) (.vout x) ∧ ¬∃ v, Conf Adj x v ∧
        ∀ j, F (.vout x) (.mid j x v) ∨ F (.mid j x v) (.vin v)) →
      (¬F (.vin y) (.vout y) ∧ ¬∃ v, Conf Adj y v ∧
        ∀ j, F (.vout y) (.mid j y v) ∨ F (.mid j y v) (.vin v)) → x ≠ y → Adj x y := by
    intro x y hx hy hxy
    by_contra hadj
    have hconf : Conf Adj x y := ⟨hxy, Or.inl hadj⟩
    obtain ⟨j, hj⟩ : ∃ j, ¬(F (.vout x) (.mid j x y) ∨ F (.mid j x y) (.vin y)) := by
      by_contra h
      exact hx.2 ⟨y, hconf, fun j => by_contra fun hj => h ⟨j, hj⟩⟩
    obtain ⟨j', hj'⟩ : ∃ j, ¬(F (.vout y) (.mid j y x) ∨ F (.mid j y x) (.vin x)) := by
      by_contra h
      exact hy.2 ⟨x, hconf.symm, fun j => by_contra fun hj => h ⟨j, hj⟩⟩
    have e₁ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.vin x) (.vout x) := ⟨⟨hK, rfl⟩, hx.1⟩
    have e₂ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.vout x) (.mid j x y) :=
      ⟨⟨hK, rfl, hconf⟩, fun h => hj (Or.inl h)⟩
    have e₃ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.mid j x y) (.vin y) :=
      ⟨⟨hK, rfl, hconf⟩, fun h => hj (Or.inr h)⟩
    have e₄ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.vin y) (.vout y) := ⟨⟨hK, rfl⟩, hy.1⟩
    have e₅ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.vout y) (.mid j' y x) :=
      ⟨⟨hK, rfl, hconf.symm⟩, fun h => hj' (Or.inl h)⟩
    have e₆ : Lax799700.Feedback.UncutArc (SArc Adj K) F (.mid j' y x) (.vin x) :=
      ⟨⟨hK, rfl, hconf.symm⟩, fun h => hj' (Or.inr h)⟩
    exact hac (.vin x)
      ((((((Relation.TransGen.single e₁).tail e₂).tail e₃).tail e₄).tail e₅).tail e₆)
  have hpromise := hP _ hT
  -- the arcs of `F`: the internal ones, and the others
  have hPF : {p : SB A × SB A | F p.1 p.2} =
      {p | ∃ a, F (.vin a) (.vout a) ∧ p = (.vin a, .vout a)} ∪
        {p | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)} := by
    ext p
    constructor
    · intro hp
      by_cases hint : ∃ a, p = (.vin a, .vout a)
      · obtain ⟨a, rfl⟩ := hint
        exact Or.inl ⟨a, hp, rfl⟩
      · exact Or.inr ⟨hp, hint⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨hp, -⟩)
      exacts [ha, hp]
  have hdisj : Disjoint {p : SB A × SB A | ∃ a, F (.vin a) (.vout a) ∧ p = (.vin a, .vout a)}
      {p | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)} :=
    Set.disjoint_left.mpr fun p ⟨a, _, hp⟩ hb => hb.2 ⟨a, hp⟩
  have hcount := congrArg Set.ncard hPF
  rw [Set.ncard_union_eq hdisj, ncard_internal, hcard, ncard_smark K hK] at hcount
  -- a cut bundle costs two arcs
  have hD : 2 * {u | ∃ v, Conf Adj u v ∧
        ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)}.ncard ≤
      {p : SB A × SB A | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)}.ncard := by
    let g : {u // ∃ v, Conf Adj u v ∧
          ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)} × Bool → SB A × SB A :=
      fun x => if F (.vout x.1.1) (.mid x.2 x.1.1 x.1.2.choose) then
        (.vout x.1.1, .mid x.2 x.1.1 x.1.2.choose)
      else (.mid x.2 x.1.1 x.1.2.choose, .vin x.1.2.choose)
    have hg : ∀ x, F (g x).1 (g x).2 ∧ ¬∃ a, g x = (.vin a, .vout a) := by
      intro x
      by_cases h : F (.vout x.1.1) (.mid x.2 x.1.1 x.1.2.choose)
      · have he : g x = (.vout x.1.1, .mid x.2 x.1.1 x.1.2.choose) := if_pos h
        rw [he]
        exact ⟨h, fun ⟨a, ha⟩ => by simp at ha⟩
      · have he : g x = (.mid x.2 x.1.1 x.1.2.choose, .vin x.1.2.choose) := if_neg h
        rw [he]
        exact ⟨(x.1.2.choose_spec.2 x.2).resolve_left h, fun ⟨a, ha⟩ => by simp at ha⟩
    have hrec' : ∀ x, bundleOf (g x) = some (x.1.1, x.2) := by
      intro x
      by_cases h : F (.vout x.1.1) (.mid x.2 x.1.1 x.1.2.choose)
      · have he : g x = (.vout x.1.1, .mid x.2 x.1.1 x.1.2.choose) := if_pos h
        rw [he]
        rfl
      · have he : g x = (.mid x.2 x.1.1 x.1.2.choose, .vin x.1.2.choose) := if_neg h
        rw [he]
        rfl
    let f : {u // ∃ v, Conf Adj u v ∧
          ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)} × Bool →
        {p : SB A × SB A // F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)} := fun x => ⟨g x, hg x⟩
    have hrec : ∀ x, bundleOf (f x).1 = some (x.1.1, x.2) := hrec'
    have hinj : Function.Injective f := by
      intro x y hxy
      have h := (hrec x).symm.trans ((congrArg (fun z => bundleOf z.1) hxy).trans (hrec y))
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    have hle := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod] at hle
    have hbool : Nat.card Bool = 2 := by simp
    rw [hbool] at hle
    have h₁ := Nat.card_coe_set_eq {u | ∃ v, Conf Adj u v ∧
      ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)}
    have h₂ := Nat.card_coe_set_eq
      {p : SB A × SB A | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)}
    have hle' : {u | ∃ v, Conf Adj u v ∧
          ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)}.ncard * 2 ≤
        {p : SB A × SB A | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)}.ncard :=
      h₁ ▸ h₂ ▸ hle
    omega
  -- the kept vertices away from the cut bundles are many
  have hcompl := Set.ncard_add_ncard_compl
    ({a | F (.vin a) (.vout a)} ∪ {u | ∃ v, Conf Adj u v ∧
      ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)})
  have hunion := Set.ncard_union_le {a | F (.vin a) (.vout a)}
    {u | ∃ v, Conf Adj u v ∧ ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)}
  have hTset : ({a | F (.vin a) (.vout a)} ∪ {u | ∃ v, Conf Adj u v ∧
        ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)})ᶜ =
      {x | ¬F (.vin x) (.vout x) ∧ ¬∃ v, Conf Adj x v ∧
        ∀ j, F (.vout x) (.mid j x v) ∨ F (.mid j x v) (.vin v)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact Iff.rfl
  rw [hTset] at hcompl
  have hKn := Set.ncard_add_ncard_compl {x : A | K x}
  have hKc : {x : A | K x}ᶜ = {x | ¬K x} := rfl
  rw [hKc] at hKn
  have hb0 : {p : SB A × SB A | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)}.ncard = 0 := by
    omega
  have hd0 : {u | ∃ v, Conf Adj u v ∧
      ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)}.ncard = 0 := by omega
  have hint : ∀ u v, F u v → ∃ a, u = .vin a ∧ v = .vout a := by
    intro u v huv
    by_contra hno
    have hmem : (u, v) ∈ {p : SB A × SB A | F p.1 p.2 ∧ ¬∃ a, p = (.vin a, .vout a)} :=
      ⟨huv, fun ⟨a, ha⟩ => hno ⟨a, (Prod.mk.injEq _ _ _ _ ▸ ha).1, (Prod.mk.injEq _ _ _ _ ▸ ha).2⟩⟩
    rw [(Set.ncard_eq_zero (Set.toFinite _)).mp hb0] at hmem
    exact hmem
  have hnoD : ∀ u, ¬∃ v, Conf Adj u v ∧
      ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v) := by
    intro u hu
    have hmem : u ∈ {u | ∃ v, Conf Adj u v ∧
        ∀ j, F (.vout u) (.mid j u v) ∨ F (.mid j u v) (.vin v)} := hu
    rw [(Set.ncard_eq_zero (Set.toFinite _)).mp hd0] at hmem
    exact hmem
  refine ⟨⟨fun x y hx hy hxy => hT x y ⟨hx, hnoD x⟩ ⟨hy, hnoD y⟩ hxy, ?_⟩, ?_⟩
  · refine (ncard_not_eq_iff (fun a => ¬F (.vin a) (.vout a)) K).mp ?_
    have hset : {x : A | ¬¬F (.vin x) (.vout x)} = {a | F (.vin a) (.vout a)} :=
      Set.ext fun x => not_not
    rw [hset]
    omega
  · funext u v
    apply propext
    constructor
    · intro huv
      obtain ⟨a, rfl, rfl⟩ := hint u v huv
      exact ⟨rfl, not_not.mpr huv⟩
    · intro huv
      cases u <;> cases v <;> try exact (huv : False).elim
      obtain ⟨hab, hC⟩ := huv
      subst hab
      exact not_not.mp hC

/-- **The feedback arc sets of the threshold size of the conflict split graph
are the cliques of the threshold size**, as many: provided the graph has no
marked vertex, or no clique larger than its marked set. -/
theorem card_fas_eq_card_clique
    (hprom : (¬∃ z, K z) ∨ ∀ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adj x y) →
      {x | S x}.ncard ≤ {x | K x}.ncard) :
    Nat.card {F : SB A → SB A → Prop // Lax280166.CountingFeedbackSets.FasOfSizeOn (SArc Adj K) (SMark K) F} =
      Nat.card {S : A → Prop // Lax280166.CountingCliques.CliqueOfSizeOn Adj K S} := by
  classical
  by_cases hK : ∃ z, K z
  · have hP := hprom.resolve_left (not_not.mpr hK)
    exact Nat.card_congr
      { toFun := fun F => ⟨_, (internal_of_fas Adj K hK hP F.2).1⟩
        invFun := fun S => ⟨FS S.1, fas_of_clique Adj K hK S.2⟩
        left_inv := fun F => Subtype.ext (internal_of_fas Adj K hK hP F.2).2.symm
        right_inv := fun S => Subtype.ext (funext fun a => propext
          ⟨fun h => by_contra fun hS => h ⟨rfl, hS⟩, fun hS h => h.2 hS⟩) }
  · -- no marked vertex: no arc, and the empty clique
    have hK0 : {x : A | K x} = ∅ := Set.eq_empty_of_forall_notMem fun x hx => hK ⟨x, hx⟩
    have hnoarc : ∀ u v, ¬SArc Adj K u v := by
      intro u v h
      cases u <;> cases v <;> first | exact (h : False).elim | exact hK h.1
    have hnomark : {p : SB A × SB A | SMark K p.1 p.2} = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp => by
        obtain ⟨u, v⟩ := p
        have h : SMark K u v := hp
        cases u <;> cases v <;> first | exact (h : False).elim | exact hK h.1
    exact Nat.card_congr
      { toFun := fun _ => ⟨fun _ => False, fun _ _ h => h.elim, by
          rw [hK0]
          simp⟩
        invFun := fun _ => ⟨fun _ _ => False, fun _ _ h => h.elim,
          fun x hx => by
            cases hx with
            | single h => exact hnoarc _ _ h.1
            | tail _ h => exact hnoarc _ _ h.1, by
          rw [hnomark]
          simp⟩
        left_inv := fun F => Subtype.ext (funext fun u => funext fun v =>
          propext ⟨fun h => h.elim, fun h => hnoarc u v (F.2.1 u v h)⟩)
        right_inv := fun S => Subtype.ext (funext fun x => propext
          ⟨fun h => h.elim, fun hx => by
            have h0 : {x | S.1 x}.ncard = 0 := by
              rw [S.2.2, hK0]
              simp
            have hmem : x ∈ {x | S.1 x} := hx
            rw [(Set.ncard_eq_zero (Set.toFinite _)).mp h0] at hmem
            exact hmem⟩) }

end Graph

end SplitBundle

end Lax280166Proofs.DescriptiveComplexity


