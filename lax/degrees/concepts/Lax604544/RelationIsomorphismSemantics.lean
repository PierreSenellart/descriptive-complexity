import Lax904597.Problems
import Lax904597.Interpretations
import Lax904597.Relativized
import Lax904597.Classes
import Lax904597.Sat
import Lax799700.SubgraphIso
import Lax485149.Problems
import Lax485149.TwoSat
import Lax485149.ClassNL
import Lax535992.HornSat
import Lax535992.ClassPTIME
import Lax564036.Hierarchy
import Lax564036.Tautology
import Lax624099.ClassRE
import Lax624099.FiniteSatisfiability
import Lax604544.Degrees
import Lax604544.RelationIsomorphism
import Lax604544.GraphIsomorphism
import Lax604544.DagIsomorphism

/-!
---
title: Isomorphism of marked relations as an equivalence
type: lemma
---
Two marked relations are isomorphic if and only if there is a bijection
between the two marked sets, as types, carrying one relation to the other
in both directions. This is the equivalence under which decision problems
are required to be invariant, read on the two sides of one instance.
-/

namespace Lax604544.RelationIsomorphismSemantics

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Sat Lax799700.SubgraphIso
open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME
open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability
open Lax604544.Degrees Lax604544.RelationIsomorphism
open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- Isomorphism of marked relations is an equivalence of the marked sets. -/
axiom relIsoOn_iff_equiv : ∀ {A : Type} (PV HV : A → Prop) (PE HE : A → A → Prop),
  RelIsoOn PV HV PE HE ↔
    ∃ e : {x // PV x} ≃ {x // HV x}, ∀ (x y : {x // PV x}), PE ↑x ↑y ↔ HE ↑(e x) ↑(e y)

end Lax604544.RelationIsomorphismSemantics
