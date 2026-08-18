/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.ImmermanSzelepcsenyi

/-!
# REACH is NL-complete

The FO(TC) discharge: every `DescriptiveComplexity.TCDefinable` problem admits an
ordered first-order reduction to `DescriptiveComplexity.REACH`
(`DescriptiveComplexity.reach_hard_of_tcDefinable`). With `REACH ∈ NL`
(`DescriptiveComplexity.reach_mem_NL`) and `NL = FO(TC)`
(`DescriptiveComplexity.tcDefinable_iff_mem_NL`) this closes REACH's completeness for
`DescriptiveComplexity.NL` (`DescriptiveComplexity.REACH_NL_complete`) – directed
`s`-`t` reachability being *the* canonical NL-complete problem ([Jones
1975][jones1975space]; [Immerman 1999][immerman1999descriptive], ch. 3).

## The reduction is the walk itself

Where the discharges of the clausal fragments have to *emit* an instance –
one propositional clause per clause of the program and per instantiation of
its universally quantified variables – the discharge into REACH has nothing to
build: the graph of the walk of a `DescriptiveComplexity.TCSpec` already *is* a
marked graph, and reachability in it is what the specification accepts by
definition.

The fit is exact, and it is the tags that make it so. A `TCSpec` walks on
nodes that are a mode together with a `k`-tuple
(`DescriptiveComplexity.TCSpec.Node`), which is literally the universe
`Tag × A^dim` of a tagged interpretation
(`DescriptiveComplexity.FOInterpretation.Map`) at `Tag := spec.Mode` and
`dim := spec.k`. So the interpretation

```
   edge((m, x̄), (m', ȳ))  :=  step m m' (x̄, ȳ)
   source((m, x̄))         :=  src m x̄
   target((m, x̄))         :=  tgt m x̄
```

is nothing but the specification's three formulas, relabelled from their
`Fin k ⊕ Fin k` (resp. `Fin k`) variables to the argument-major variables
`Fin n × Fin k` an interpretation uses. There is no junk to gate away: *every*
tagged tuple is a genuine node of the walk, so an ordinary (unrelativized)
ordered reduction suffices.

One wrinkle: a reduction must map nonempty structures to nonempty structures,
so its tag type must be nonempty, while a `TCSpec` may perfectly well have no
modes at all (and then accept nothing). `DescriptiveComplexity.TCSpec.pad`, already
at hand from the complementation proof, adds one spare isolated mode and
changes no acceptance, which is exactly the fix.

## What this does *not* claim

As everywhere in this library, no machine model is involved: `NL` is *defined*
by the Krom fragment (`DescriptiveComplexity.SigmaSOKromDefinable`), and the
NL-hardness proved here is hardness for that class. Grädel's capture theorem
against logarithmic-space machines ([Grädel 1992][gradel1992capturing]) is not
formalized. Note also how much of the library this one-page reduction rests
on: `REACH ∈ NL` is Immerman–Szelepcsényi, and the passage from an SO-Krom
definition to an FO(TC) one is the translation of
`DescriptiveComplexity.KromTransitiveClosure`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace TCDischarge

variable (spec : TCSpec L)

/-! ### The interpretation

The variables of a `DescriptiveComplexity.TCSpec` formula are one or two `k`-tuples;
those of an interpretation's defining formula are indexed by
argument-then-coordinate. The two selectors below are the renamings between
them. -/

/-- The renaming of the transition formula's variables: the current tuple is
the first argument of `edge`, the next one is its second argument. -/
def stepVar : Fin spec.k ⊕ Fin spec.k → Fin 2 × Fin spec.k :=
  Sum.elim (fun i => (0, i)) (fun i => (1, i))

/-- The renaming of an endpoint formula's variables: the tuple is the only
argument of `source`, resp. `target`. -/
def endVar : Fin spec.k → Fin 1 × Fin spec.k := fun i => (0, i)

/-- The defining formula of `edge` at a pair of modes: the transition formula
of those modes. -/
noncomputable def edgeF (m m' : spec.Mode) :
    (L.sum Language.order).Formula (Fin 2 × Fin spec.k) :=
  (spec.step m m').relabel (stepVar spec)

/-- The defining formula of `source` at a mode: the source formula of that
mode. -/
noncomputable def srcF (m : spec.Mode) :
    (L.sum Language.order).Formula (Fin 1 × Fin spec.k) :=
  (spec.src m).relabel (endVar spec)

/-- The defining formula of `target` at a mode: the target formula of that
mode. -/
noncomputable def tgtF (m : spec.Mode) :
    (L.sum Language.order).Formula (Fin 1 × Fin spec.k) :=
  (spec.tgt m).relabel (endVar spec)

/-- **The graph of the walk**, as an interpretation into the vocabulary of
marked graphs: a vertex is a node of the specification – a mode together with
a `k`-tuple – an arc is a transition, and the marks are the specification's
starting and accepting nodes. -/
noncomputable def tcInterp :
    FOInterpretation (L.sum Language.order) Language.stGraph spec.Mode spec.k where
  relFormula {n} R :=
    match n, R with
    | _, .edge => fun t => edgeF spec (t 0) (t 1)
    | _, .source => fun t => srcF spec (t 0)
    | _, .target => fun t => tgtF spec (t 0)

/-! ### Correctness -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A]

theorem realize_edgeF (m m' : spec.Mode) (v : Fin 2 × Fin spec.k → A) :
    (edgeF spec m m').Realize v ↔
      spec.Step ((m, fun i => v (0, i)) : spec.Node A) (m', fun i => v (1, i)) := by
  rw [edgeF, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.step m m').Realize (funext fun j => by cases j <;> rfl))

theorem realize_srcF (m : spec.Mode) (v : Fin 1 × Fin spec.k → A) :
    (srcF spec m).Realize v ↔ spec.IsSrc ((m, fun i => v (0, i)) : spec.Node A) := by
  rw [srcF, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.src m).Realize (funext fun _ => rfl))

theorem realize_tgtF (m : spec.Mode) (v : Fin 1 × Fin spec.k → A) :
    (tgtF spec m).Realize v ↔ spec.IsTgt ((m, fun i => v (0, i)) : spec.Node A) := by
  rw [tgtF, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.tgt m).Realize (funext fun _ => rfl))

/-- An arc of the interpreted graph is a transition of the walk. -/
theorem sgEdge_tcInterp (a b : (tcInterp spec).Map A) : SGEdge a b ↔ spec.Step a b := by
  rw [SGEdge, FOInterpretation.relMap_map]
  exact realize_edgeF spec a.1 b.1 _

/-- A marked source of the interpreted graph is a starting node of the walk. -/
theorem sgSource_tcInterp (a : (tcInterp spec).Map A) : SGSource a ↔ spec.IsSrc a := by
  rw [SGSource, FOInterpretation.relMap_map]
  exact realize_srcF spec a.1 _

/-- A marked target of the interpreted graph is an accepting node of the
walk. -/
theorem sgTarget_tcInterp (a : (tcInterp spec).Map A) : SGTarget a ↔ spec.IsTgt a := by
  rw [SGTarget, FOInterpretation.relMap_map]
  exact realize_tgtF spec a.1 _

/-- A directed path of the interpreted graph is a walk of the specification,
and conversely. -/
theorem reflTransGen_tcInterp (a b : (tcInterp spec).Map A) :
    Relation.ReflTransGen SGEdge a b ↔ spec.Reach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((sgEdge_tcInterp spec c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((sgEdge_tcInterp spec c d).mpr hcd)

variable (A) in
/-- **Correctness of the discharge**: a marked target of the interpreted graph
is reachable from a marked source exactly when the specification accepts. Both
directions are the identity on nodes – the graph *is* the walk. -/
theorem reachable_tcInterp_iff : Reachable ((tcInterp spec).Map A) ↔ spec.Accepts A := by
  constructor
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨s, t, (sgSource_tcInterp spec s).mp hs, (sgTarget_tcInterp spec t).mp ht,
      (reflTransGen_tcInterp spec s t).mp hpath⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u, v, (sgSource_tcInterp spec u).mpr hu, (sgTarget_tcInterp spec v).mpr hv,
      (reflTransGen_tcInterp spec u v).mpr huv⟩

end Correctness

/-- **The generic FO(TC) reduction**: an ordered first-order reduction to
REACH from any problem defined, on nonempty finite ordered structures, by a
single transitive closure whose modes are nonempty. -/
noncomputable def tcReduction [L.IsRelational] [Nonempty spec.Mode] (P : DecisionProblem L)
    (hP : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A) : P ≤ᶠᵒ[≤] REACH where
  Tag := spec.Mode
  dim := spec.k
  toInterpretation := tcInterp spec
  correct A _ _ _ _ := (hP A).trans (reachable_tcInterp_iff spec A).symm

end TCDischarge

/-! ### NL-completeness -/

open TCDischarge in
/-- **NL-hardness of REACH, machine-free**: every FO(TC) definable problem
admits an ordered first-order reduction to REACH. The interpretation is the
graph of the walk itself; padding the specification with one spare mode
(`DescriptiveComplexity.TCSpec.pad`) is only there to keep the tag type nonempty, as a
reduction requires. -/
theorem reach_hard_of_tcDefinable [L.IsRelational] (P : DecisionProblem L) (hP : TCDefinable P) :
    Nonempty (P ≤ᶠᵒ[≤] REACH) := by
  obtain ⟨spec, hspec⟩ := hP
  exact ⟨tcReduction spec.pad P fun A => (hspec A).trans (spec.pad_accepts_iff A).symm⟩

/-- **REACH is NL-hard**: an SO-Krom definable problem is FO(TC) definable
(`DescriptiveComplexity.tcDefinable_iff_mem_NL`, i.e., Immerman–Szelepcsényi through the
two translations), and an FO(TC) definition reduces to reachability in the
graph of its walk. -/
theorem reach_NL_hard : NL.Hard REACH :=
  (hard_NL_iff REACH).mpr fun Q hQ =>
    (reach_hard_of_tcDefinable Q ((tcDefinable_iff_mem_NL Q).mpr hQ)).map
      OrderedFOReduction.toRel

/-- **REACH is NL-complete.** Membership is `DescriptiveComplexity.reach_mem_NL` – which
is Immerman–Szelepcsényi, the Krom fragment defining non-reachability head-on;
hardness is `DescriptiveComplexity.reach_NL_hard`, the FO(TC) discharge. Directed
`s`-`t` reachability is the canonical NL-complete problem ([Jones
1975][jones1975space]), here complete under order-invariant first-order
reductions rather than logarithmic-space ones. -/
theorem REACH_NL_complete : NL.Complete REACH :=
  ⟨reach_mem_NL, reach_NL_hard⟩

/-- **UNREACH is NL-hard**, by complementing the reduction: the complement of
a problem in NL is in NL (`DescriptiveComplexity.mem_NL_compl_iff`), that complement
reduces to REACH, and *the very same interpretation* reduces the problem itself
to UNREACH (`DescriptiveComplexity.OrderedFOReduction.compl`, the correctness of a
reduction being an equivalence). -/
theorem unreach_NL_hard : NL.Hard UNREACH :=
  (hard_NL_iff UNREACH).mpr fun Q hQ => by
    have h := (reach_hard_of_tcDefinable Qᶜ
      ((tcDefinable_iff_mem_NL Qᶜ).mpr ((mem_NL_compl_iff Q).mpr hQ))).map
        OrderedFOReduction.compl
    rw [DecisionProblem.compl_compl] at h
    exact h.map OrderedFOReduction.toRel

/-- **UNREACH is NL-complete** as well, and the two halves come from opposite
sides. Membership is the head-on Krom program
(`DescriptiveComplexity.unreach_mem_NL`): a clausal fragment states closure and
rejection, so non-reachability is what it defines directly. Hardness is
`DescriptiveComplexity.unreach_NL_hard`, which needs `NL = coNL`; without
Immerman–Szelepcsényi neither half would be available for *both* problems, and
the two would sit on either side of a complement that is not known to be
crossable. -/
theorem UNREACH_NL_complete : NL.Complete UNREACH :=
  ⟨unreach_mem_NL, unreach_NL_hard⟩

end DescriptiveComplexity
