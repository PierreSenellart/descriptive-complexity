/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Reachability
import DescriptiveComplexity.TransitiveClosureReach
import DescriptiveComplexity.DetLogSpace

/-!
# REACHd: deterministic reachability, complete for LOGSPACE

The problem REACHd – is some marked target reachable from some marked source
along *forced* arcs? – over the same vocabulary `FirstOrder.Language.stGraph` as
REACH. It is to `DescriptiveComplexity.LOGSPACE` what REACH is to
`DescriptiveComplexity.NL`, and its two halves are the mirror image of that pair:
membership because the problem *is* a deterministic walk, hardness because the
graph of a deterministic walk is such a problem.

## No promise, and why

The textbook statement of REACHd restricts the input to graphs of outdegree at
most one. A promise problem is awkward here: it would either need a
well-formedness conjunct (`DescriptiveComplexity.DecisionProblem.ofSentence`) carried
through every reduction, or leave the yes-instances undefined on the graphs
that break the promise – and isomorphism-invariance would then have to be
proved of a partial specification.

So the outdegree bound is imposed *semantically* instead, by the same move
determinization makes one level up (`DescriptiveComplexity.TCSpec.det`): the walk may
follow an arc only when it is the only arc out of its source
(`DescriptiveComplexity.DetEdge`). Every marked graph is then a legal instance, the
problem is invariant by transport, and on graphs that do have outdegree at most
one it is exactly REACH (`DescriptiveComplexity.detReachable_iff_reachable`) – which is
what the hardness proof uses, the interpreted graph of a deterministic walk
being functional by construction.

## Completeness

* **Membership** (`DescriptiveComplexity.reachd_dtcDefinable`): REACHd is a single
  deterministic transitive closure, at arity one and with a single mode – the
  very specification `DescriptiveComplexity.reachSpec` that witnesses
  `DescriptiveComplexity.reach_tcDefinable`, read through its determinization. The
  determinized step relation *is* `DescriptiveComplexity.DetEdge`.
* **The complement**, UNREACHd, is complete as well
  (`DescriptiveComplexity.UNREACHd_LOGSPACE_complete`, in
  `DescriptiveComplexity.Problems.ReachabilityDet.Complement`), which is how
  `L = coL` is obtained.
* **Hardness** (`DescriptiveComplexity.reachd_hard_of_dtcDefinable`): the interpretation
  is the graph of the walk itself (`DescriptiveComplexity.TCDischarge.tcInterp`), reused
  verbatim from the FO(TC) discharge; all that is new is that the walk of a
  determinized specification is functional, so that reachability in the
  interpreted graph and *deterministic* reachability agree.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Defs

variable {A : Type} [Language.stGraph.Structure A]

/-- A *forced* arc: an arc that is the only one out of its source. Following
these is the deterministic walk on a marked graph, with no promise on the
instance. -/
def DetEdge (a b : A) : Prop :=
  SGEdge a b ∧ ∀ c : A, SGEdge a c → c = b

variable (A) in
/-- Some marked target is reachable from some marked source along a (possibly
empty) path of forced arcs. -/
def DetReachable : Prop :=
  ∃ s t : A, SGSource s ∧ SGTarget t ∧ Relation.ReflTransGen DetEdge s t

/-- On a graph of outdegree at most one, deterministic reachability is
reachability: every arc is forced. -/
theorem detReachable_iff_reachable
    (h : ∀ a b c : A, SGEdge a b → SGEdge a c → b = c) :
    DetReachable A ↔ Reachable A := by
  have he : ∀ a b : A, DetEdge a b ↔ SGEdge a b :=
    fun a b => ⟨And.left, fun hab => ⟨hab, fun c hc => h a c b hc hab⟩⟩
  have hpath : ∀ a b : A, Relation.ReflTransGen DetEdge a b ↔
      Relation.ReflTransGen SGEdge a b := by
    refine fun a b => ⟨fun hr => ?_, fun hr => ?_⟩
    · induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | @tail c d _ hcd ih => exact ih.tail ((he c d).mp hcd)
    · induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | @tail c d _ hcd ih => exact ih.tail ((he c d).mpr hcd)
  exact ⟨fun ⟨s, t, hs, ht, hr⟩ => ⟨s, t, hs, ht, (hpath s t).mp hr⟩,
    fun ⟨s, t, hs, ht, hr⟩ => ⟨s, t, hs, ht, (hpath s t).mpr hr⟩⟩

end Defs

section Iso

variable {A B : Type} [Language.stGraph.Structure A] [Language.stGraph.Structure B]

private theorem detEdge_map (e : A ≃[Language.stGraph] B) (a b : A) :
    DetEdge a b ↔ DetEdge (e a) (e b) := by
  refine and_congr (relMap_equiv₂ e sgEdge a b) ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · have hc' : SGEdge a (e.symm c) :=
      (relMap_equiv₂ e sgEdge a (e.symm c)).mpr
        ((iff_of_eq (congrArg (SGEdge (e a)) (e.apply_symm_apply c))).mpr hc)
    exact (e.apply_symm_apply c).symm.trans (congrArg (fun x => e x) (h (e.symm c) hc'))
  · exact e.toEquiv.injective (h (e c) ((relMap_equiv₂ e sgEdge a c).mp hc))

private theorem detReflTransGen_map (e : A ≃[Language.stGraph] B) {a b : A}
    (h : Relation.ReflTransGen DetEdge a b) :
    Relation.ReflTransGen DetEdge (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((detEdge_map e c d).mp hcd)

private theorem detReachable_of_iso (e : A ≃[Language.stGraph] B) (h : DetReachable A) :
    DetReachable B := by
  obtain ⟨s, t, hs, ht, hpath⟩ := h
  exact ⟨e s, e t, (relMap_equiv₁ e sgSource s).mp hs,
    (relMap_equiv₁ e sgTarget t).mp ht, detReflTransGen_map e hpath⟩

/-- Deterministic reachability is isomorphism-invariant. -/
theorem detReachable_iso (e : A ≃[Language.stGraph] B) :
    DetReachable A ↔ DetReachable B :=
  ⟨detReachable_of_iso e, detReachable_of_iso e.symm⟩

end Iso

/-- **REACHd**, deterministic reachability: is a marked target reachable from a
marked source along forced arcs? -/
def REACHd : DecisionProblem Language.stGraph where
  Holds := fun A inst => @DetReachable A inst
  iso_invariant := fun e => detReachable_iso e

/-! ### Membership: REACHd is a deterministic transitive closure -/

section Membership

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A]

/-- The determinized walk of `DescriptiveComplexity.reachSpec` follows exactly the
forced arcs. The uniqueness clause quantifies over successor *nodes*, which at
a single mode and arity one are just the successor vertices. -/
theorem det_step_reachSpec (a b : reachSpec.Node A) :
    reachSpec.det.Step a b ↔ DetEdge (a.2 0) (b.2 0) := by
  rw [TCSpec.det_step_iff]
  refine and_congr (step_reachSpec a b) ⟨fun h y hy => ?_, fun h c hc => ?_⟩
  · have hy' := h ((), fun _ => y) ((step_reachSpec a ((), fun _ => y)).mpr hy)
    exact congrArg (fun n : reachSpec.Node A => n.2 0) hy'
  · have hc' := h (c.2 0) ((step_reachSpec a c).mp hc)
    refine Prod.ext_iff.mpr ⟨Subsingleton.elim _ _, funext fun i => ?_⟩
    have hci : c.2 i = c.2 0 := congrArg c.2 (Subsingleton.elim i 0)
    have hbi : b.2 0 = b.2 i := congrArg b.2 (Subsingleton.elim 0 i)
    exact (hci.trans hc').trans hbi

/-- A path of forced arcs is a walk of the determinized specification. -/
theorem detReach_of_reflTransGen {x y : A} (h : Relation.ReflTransGen DetEdge x y) :
    reachSpec.det.Reach ((), fun _ => x) ((), fun _ => y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact ih.tail ((det_step_reachSpec ((), fun _ => b) ((), fun _ => c)).mpr hbc)

/-- A walk of the determinized specification is a path of forced arcs. -/
theorem reflTransGen_of_detReach {u v : reachSpec.Node A}
    (h : reachSpec.det.Reach u v) : Relation.ReflTransGen DetEdge (u.2 0) (v.2 0) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ((det_step_reachSpec b c).mp hbc)

variable (A) in
/-- The determinized specification accepts exactly the graphs with a forced
path from a marked source to a marked target. -/
theorem det_accepts_reachSpec_iff : reachSpec.det.Accepts A ↔ DetReachable A := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨(u : reachSpec.Node A).2 0, (v : reachSpec.Node A).2 0,
      (realize_tcSourceF u.2).mp hu, (realize_tcTargetF v.2).mp hv,
      reflTransGen_of_detReach huv⟩
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨((), fun _ => s), ((), fun _ => t), (realize_tcSourceF _).mpr hs,
      (realize_tcTargetF _).mpr ht, detReach_of_reflTransGen hpath⟩

end Membership

/-- **REACHd is FO(DTC) definable**: it is a single *deterministic* transitive
closure of the edge relation, at arity one – the specification of REACH read
through its determinization. -/
theorem reachd_dtcDefinable : DTCDefinable REACHd := by
  refine ⟨reachSpec, ?_⟩
  intro A _ _ _ _
  exact (det_accepts_reachSpec_iff A).symm

/-- REACHd is in LOGSPACE. -/
theorem reachd_mem_LOGSPACE : REACHd ∈ LOGSPACE :=
  reachd_dtcDefinable

/-! ### Hardness: the graph of a deterministic walk -/

section Hardness

variable {L : Language.{0, 0}}

namespace TCSpec

variable {spec : TCSpec L} {A : Type} [L.Structure A] [LinearOrder A]

/-- Padding a specification with a spare mode preserves functionality: the
spare mode has no transitions at all. -/
theorem pad_functional (h : spec.Functional A) : spec.pad.Functional A := by
  rintro ⟨p, x⟩ ⟨q, y⟩ ⟨r, z⟩ hb hc
  cases p with
  | none => exact absurd hb (fun hb' => hb')
  | some m =>
    cases q with
    | none => exact absurd hb (fun hb' => hb')
    | some m' =>
      cases r with
      | none => exact absurd hc (fun hc' => hc')
      | some m'' =>
        exact congrArg (fun n : spec.Node A => ((some n.1 : Option spec.Mode), n.2))
          (h (m, x) (m', y) (m'', z) hb hc)

end TCSpec

open TCDischarge in
/-- The graph interpreted from a functional specification has outdegree at most
one: its arcs *are* the transitions of the walk. -/
theorem functional_sgEdge_tcInterp (spec : TCSpec L) {A : Type} [L.Structure A]
    [LinearOrder A] (h : spec.Functional A) (a b c : (tcInterp spec).Map A)
    (hb : SGEdge a b) (hc : SGEdge a c) : b = c :=
  h a b c ((sgEdge_tcInterp spec a b).mp hb) ((sgEdge_tcInterp spec a c).mp hc)

open TCDischarge in
/-- **Correctness of the deterministic discharge**: in the graph of a
functional walk, deterministic reachability is reachability, hence acceptance. -/
theorem detReachable_tcInterp_iff (spec : TCSpec L) (A : Type) [L.Structure A]
    [LinearOrder A] (h : spec.Functional A) :
    DetReachable ((tcInterp spec).Map A) ↔ spec.Accepts A :=
  (detReachable_iff_reachable (functional_sgEdge_tcInterp spec h)).trans
    (reachable_tcInterp_iff spec A)

open TCDischarge in
/-- **The generic FO(DTC) reduction**: an ordered first-order reduction to
REACHd from any problem defined, on nonempty finite ordered structures, by a
single deterministic transitive closure. The interpretation is the graph of the
determinized walk – functional by construction, which is exactly the condition
under which the target problem's forced arcs are all of its arcs. -/
noncomputable def dtcReduction (spec : TCSpec L) (P : DecisionProblem L)
    (hP : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.det.Accepts A) : P ≤ᶠᵒ[≤] REACHd where
  Tag := spec.det.pad.Mode
  dim := spec.det.pad.k
  toInterpretation := tcInterp spec.det.pad
  correct A _ _ _ _ :=
    (hP A).trans ((spec.det.pad_accepts_iff A).symm.trans
      (detReachable_tcInterp_iff spec.det.pad A
        (TCSpec.pad_functional TCSpec.det_functional)).symm)

/-- **LOGSPACE-hardness of REACHd, machine-free**: every FO(DTC) definable
problem admits an ordered first-order reduction to REACHd. -/
theorem reachd_hard_of_dtcDefinable (P : DecisionProblem L) (hP : DTCDefinable P) :
    Nonempty (P ≤ᶠᵒ[≤] REACHd) := by
  obtain ⟨spec, hspec⟩ := hP
  exact ⟨dtcReduction spec P hspec⟩

end Hardness

/-- **REACHd is LOGSPACE-hard**: the FO(DTC) discharge, whose interpretation is
the graph of the deterministic walk itself. -/
theorem reachd_LOGSPACE_hard : LOGSPACE.Hard REACHd :=
  (hard_LOGSPACE_iff REACHd).mpr fun Q hQ =>
    (reachd_hard_of_dtcDefinable Q hQ).map OrderedFOReduction.toRel

/-- **REACHd is LOGSPACE-complete.** Both halves are the same observation read
in opposite directions: deterministic reachability *is* a deterministic
transitive closure (membership), and a deterministic transitive closure *is*
deterministic reachability in the graph of its walk (hardness). Compare REACH,
whose NL-completeness needs Immerman–Szelepcsényi on the membership side; here
nothing of the kind is required, the fragment issue that forces it not arising
for an operator-based logic. -/
theorem REACHd_LOGSPACE_complete : LOGSPACE.Complete REACHd :=
  ⟨reachd_mem_LOGSPACE, reachd_LOGSPACE_hard⟩

end DescriptiveComplexity
