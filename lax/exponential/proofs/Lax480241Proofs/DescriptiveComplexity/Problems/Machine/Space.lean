/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax480241Proofs.DescriptiveComplexity.Problems.Machine.Defs
import Lax480241Proofs.DescriptiveComplexity.PSpace
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData

namespace Lax480241.Expansions.SOBlock
end Lax480241.Expansions.SOBlock

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config IsLinOrd MinPos SuccPos tmData)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax134656.SecondOrderTransitiveClosure (SOTCDefinable SOTCSpec)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax480241.Expansions.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

namespace FirstOrder.Language
export Lax904597.Machines (tmAcc tmBlank tmDst tmInp tmLe tmPosn tmRead tmRight tmSrc tmStart tmTr tmWrite turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax134656.SpaceBoundedMachines.TMData (AcceptsSpace)
end Lax904597.Machines.TMData

/-!
# The space-bounded machine problems are in PSPACE

The membership half of the machine bridge for PSPACE. A configuration of a
machine is a state, a head position and a tape, and each of the three *is* a
relation on the universe: the tape is a binary relation (the graph of a
function), the state and the head are unary marks (singletons). So a
configuration is an assignment of a three-variable block
(`DescriptiveComplexity.SpaceTM.mBlock`), one step of the machine is a first-order
condition on two consecutive assignments, and acceptance – reachability in the
configuration graph, since `DescriptiveComplexity.TMData.AcceptsSpace` has no step
bound – is a transitive closure over those assignments. That is an SO(TC)
specification, with nothing left to arrange.

This is the same phenomenon as for SUCCINCT-REACH: the problem is the syntactic
image of the logic, so membership is a transcription rather than a construction.
Nothing here plays the role of `DescriptiveComplexity.Problems.Machine.Walk`,
which exists only to cash in the *unary time bound* of the time-bounded model by
indexing a run by the positions; with the bound dropped a run may be
exponentially long and no longer fits in the structure, which is precisely why
the space-bounded problems are SO(TC) rather than `Σ₁`.

The one wrinkle is that an assignment of the block is an arbitrary triple of
relations, while a configuration is a *functional total* tape and two
*singletons*. That is a first-order condition (`DescriptiveComplexity.SpaceTM.cfgF`), it
holds of every assignment coming from a configuration, and the transition
sentence demands it of the state it moves to, so every state along an accepting
walk is a configuration.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The formula builders

Kept in a namespace of their own: the shapes below (`wfF`, `stepF` …) are the
transcription of one machine model into sentences, and their names are the
generic ones the other reduction layers of the catalog also use. -/

namespace SpaceTM

/-! ### Generic sentence shapes

Each builder is parameterized by the relation symbols it reads, so that the
same one serves over the one-copy and the two-copy expansions. -/

section Shapes

variable {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {γ : Type}

/-- The tape is functional: a cell holds at most one symbol. -/
noncomputable def funcF (t : L'.Relations 2) : L'.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Relations.formula₂ t (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1))).imp
        ((FirstOrder.Language.Relations.formula₂ t (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
          (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
            (FirstOrder.Language.Term.var (Sum.inr 2)))))

/-- The mark is inhabited. -/
noncomputable def someF (s : L'.Relations 1) : L'.Formula γ :=
  FirstOrder.Language.Formula.iExs (Fin 1)
      (FirstOrder.Language.Relations.formula₁ s (FirstOrder.Language.Term.var (Sum.inr 0)))

/-- The mark holds of at most one element. -/
noncomputable def uniqF (s : L'.Relations 1) : L'.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
      ((FirstOrder.Language.Relations.formula₁ s (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        ((FirstOrder.Language.Relations.formula₁ s (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 1)))))

variable {v : γ → M}

@[simp]
theorem realize_funcF (t : L'.Relations 2) :
    (funcF (γ := γ) t).Realize v ↔ ∀ p a b : M, RelMap t ![p, a] → RelMap t ![p, b] → a = b := by
  rw [funcF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h p a b => h ![p, a, b], fun h i => h (i 0) (i 1) (i 2)⟩

@[simp]
theorem realize_someF (s : L'.Relations 1) :
    (someF (γ := γ) s).Realize v ↔ ∃ q : M, RelMap s ![q] := by
  rw [someF]
  simp only [Formula.realize_iExs, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

@[simp]
theorem realize_uniqF (s : L'.Relations 1) :
    (uniqF (γ := γ) s).Realize v ↔ ∀ q q' : M, RelMap s ![q] → RelMap s ![q'] → q = q' := by
  rw [uniqF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h q q' => h ![q, q'], fun h i => h (i 0) (i 1)⟩

/-! #### The guarded conjuncts -/

/-! #### The conjuncts of the transition sentence -/

/-- The transition has the marked element as its source (or destination). -/
noncomputable def markArgF (r : L'.Relations 2) (s : L'.Relations 1) (x : γ) :
    L'.Formula γ :=
  ((Relations.formula₁ s (Term.var (Sum.inr 0))).imp
    (Relations.formula₂ r (Term.var (Sum.inl x)) (Term.var (Sum.inr 0)))).iAlls (Fin 1)

/-- The transition reads (or writes) the symbol held by the marked cell. -/
noncomputable def cellArgF (r : L'.Relations 2) (h : L'.Relations 1) (t : L'.Relations 2)
    (x : γ) : L'.Formula γ :=
  ((Relations.formula₁ h (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
      (Relations.formula₂ r (Term.var (Sum.inl x)) (Term.var (Sum.inr 1))))).iAlls (Fin 2)

/-- `y` is the position immediately after `x`. -/
noncomputable def succPosF (le : L'.Relations 2) (posn : L'.Relations 1) (x y : γ) :
    L'.Formula γ :=
  ((Relations.formula₁ posn (Term.var x) ⊓ Relations.formula₁ posn (Term.var y)) ⊓
      (Relations.formula₂ le (Term.var x) (Term.var y) ⊓
        ∼(Term.equal (Term.var x) (Term.var y)))) ⊓
    ((Relations.formula₁ posn (Term.var (Sum.inr 0))).imp
      ((Relations.formula₂ le (Term.var (Sum.inl x)) (Term.var (Sum.inr 0))).imp
        ((Relations.formula₂ le (Term.var (Sum.inr 0)) (Term.var (Sum.inl y))).imp
          (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl x)) ⊔
            Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl y)))))).iAlls (Fin 1)

@[simp]
theorem realize_markArgF (r : L'.Relations 2) (s : L'.Relations 1) (x : γ) :
    (markArgF r s x).Realize v ↔
      ∀ q : M, RelMap s ![q] → RelMap r ![v x, q] := by
  rw [markArgF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩

@[simp]
theorem realize_cellArgF (r : L'.Relations 2) (h : L'.Relations 1) (t : L'.Relations 2)
    (x : γ) :
    (cellArgF r h t x).Realize v ↔
      ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap r ![v x, a] := by
  rw [cellArgF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun hh p a => hh ![p, a], fun hh i => hh (i 0) (i 1)⟩

@[simp]
theorem realize_succPosF (le : L'.Relations 2) (posn : L'.Relations 1) (x y : γ) :
    (succPosF le posn x y).Realize v ↔
      Lax904597.Machines.SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) (v x) (v y) := by
  rw [succPosF, Lax904597.Machines.SuccPos]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_sup, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr, ne_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, fun r hr hxr hry => h5 (fun _ => r) hr hxr hry⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, fun i hi hxi hiy => h5 (i 0) hi hxi hiy⟩

/-! #### Well-formedness -/

/-- The relation is a linear order. -/
noncomputable def linOrdF (le : L'.Relations 2) : L'.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
          (FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 3)
          ((FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))).imp
            ((FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 2))).imp
              (FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2))))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 2)
          ((FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))).imp
            ((FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 0))).imp
              (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 1))))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 2)
          (FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1)) ⊔
            FirstOrder.Language.Relations.formula₂ le (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- **Well-formedness of the instance**, as a sentence: the order is linear,
there is a position, the input is functional, and there is exactly one blank. -/
noncomputable def wfF (le inp : L'.Relations 2) (posn blank : L'.Relations 1) :
    L'.Formula γ :=
  linOrdF le ⊓ (someF posn ⊓ (funcF inp ⊓ (someF blank ⊓ uniqF blank)))

@[simp]
theorem realize_linOrdF (le : L'.Relations 2) :
    (linOrdF (γ := γ) le).Realize v ↔ Lax904597.Machines.IsLinOrd (fun a b : M => RelMap le ![a, b]) := by
  rw [linOrdF, Lax904597.Machines.IsLinOrd]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, and_assoc]
  refine and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a b c => h ![a, b, c], fun h i => h (i 0) (i 1) (i 2)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩

@[simp]
theorem realize_wfF (le inp : L'.Relations 2) (posn blank : L'.Relations 1) :
    (wfF (γ := γ) le inp posn blank).Realize v ↔
      (Lax904597.Machines.IsLinOrd (fun a b : M => RelMap le ![a, b]) ∧
        ((∃ p : M, RelMap posn ![p]) ∧
          ((∀ p a b : M, RelMap inp ![p, a] → RelMap inp ![p, b] → a = b) ∧
            ((∃ b : M, RelMap blank ![b]) ∧
              ∀ a b : M, RelMap blank ![a] → RelMap blank ![b] → a = b)))) := by
  rw [wfF]
  simp only [Formula.realize_inf, realize_linOrdF, realize_someF, realize_funcF, realize_uniqF]

/-! #### The transition sentence -/

/-- At most one transition applies in a given state on a given symbol. -/
noncomputable def trUniqF (tr : L'.Relations 1) (src rd : L'.Relations 2) : L'.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      ((FirstOrder.Language.Relations.formula₁ tr (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        ((FirstOrder.Language.Relations.formula₁ tr (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          ((FirstOrder.Language.Relations.formula₂ src (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2))).imp
            ((FirstOrder.Language.Relations.formula₂ src (FirstOrder.Language.Term.var (Sum.inr 1))
                  (FirstOrder.Language.Term.var (Sum.inr 2))).imp
              ((FirstOrder.Language.Relations.formula₂ rd (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 3))).imp
                ((FirstOrder.Language.Relations.formula₂ rd (FirstOrder.Language.Term.var (Sum.inr 1))
                      (FirstOrder.Language.Term.var (Sum.inr 3))).imp
                  (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1)))))))))

/-- **Determinism of the instance**, as a sentence. -/
noncomputable def detF (tr start : L'.Relations 1) (src rd dst wr : L'.Relations 2) :
    L'.Formula γ :=
  uniqF start ⊓ (trUniqF tr src rd ⊓ (funcF dst ⊓ funcF wr))

@[simp]
theorem realize_trUniqF (tr : L'.Relations 1) (src rd : L'.Relations 2) :
    (trUniqF (γ := γ) tr src rd).Realize v ↔
      ∀ τ τ' q a : M, RelMap tr ![τ] → RelMap tr ![τ'] → RelMap src ![τ, q] →
        RelMap src ![τ', q] → RelMap rd ![τ, a] → RelMap rd ![τ', a] → τ = τ' := by
  rw [trUniqF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h τ τ' q a => h ![τ, τ', q, a], fun h i => h (i 0) (i 1) (i 2) (i 3)⟩

@[simp]
theorem realize_detF (tr start : L'.Relations 1) (src rd dst wr : L'.Relations 2) :
    (detF (γ := γ) tr start src rd dst wr).Realize v ↔
      ((∀ q q' : M, RelMap start ![q] → RelMap start ![q'] → q = q') ∧
        ((∀ τ τ' q a : M, RelMap tr ![τ] → RelMap tr ![τ'] → RelMap src ![τ, q] →
            RelMap src ![τ', q] → RelMap rd ![τ, a] → RelMap rd ![τ', a] → τ = τ') ∧
          ((∀ τ q q' : M, RelMap dst ![τ, q] → RelMap dst ![τ, q'] → q = q') ∧
            ∀ τ a a' : M, RelMap wr ![τ, a] → RelMap wr ![τ, a'] → a = a'))) := by
  rw [detF]
  simp only [Formula.realize_inf, realize_uniqF, realize_trUniqF, realize_funcF]

end Shapes

/-! ### The block and the specification -/

section Spec

/-- The block whose assignments are the configurations: the tape as a binary
relation variable, the state and the head as unary marks. -/
abbrev mBlock : Lax904597.SecondOrder.SOBlock where
  ι := Option Bool
  arity := fun i => match i with | none => 2 | some _ => 1

/-- The symbol for the tape. -/
def mSymT : mBlock.lang.Relations 2 := ⟨none, rfl⟩

/-- The symbol for the state. -/
def mSymS : mBlock.lang.Relations 1 := ⟨some false, rfl⟩

/-- The symbol for the head. -/
def mSymH : mBlock.lang.Relations 1 := ⟨some true, rfl⟩

/-- The ordered expansion of the machine vocabulary. -/
abbrev mBase : Language := Lax904597.Machines.turing.sum Language.order

/-- The vocabulary of a one-copy expansion by the block. -/
abbrev mLang₁ : Language := mBase.sum mBlock.lang

/-- A machine symbol in the one-copy expansion. -/
abbrev mIn₁ {n : ℕ} (r : Lax904597.Machines.turing.Relations n) : mLang₁.Relations n := Sum.inl (Sum.inl r)

/-- The tape of the state, in the one-copy expansion. -/
abbrev mT₁ : mLang₁.Relations 2 := Sum.inr mSymT

/-- The state mark, in the one-copy expansion. -/
abbrev mS₁ : mLang₁.Relations 1 := Sum.inr mSymS

/-- The head mark, in the one-copy expansion. -/
abbrev mH₁ : mLang₁.Relations 1 := Sum.inr mSymH

end Spec

/-! ### Reading a state back as a configuration -/

section Reading

variable {A : Type} [Lax904597.Machines.turing.Structure A] [LinearOrder A]

/-- The tape held by a state of the walk. -/
def mTape (ρ : mBlock.Assignment A) (p a : A) : Prop := ρ none ![p, a]

/-- The state mark held by a state of the walk. -/
def mState (ρ : mBlock.Assignment A) (q : A) : Prop := ρ (some false) ![q]

/-- The head mark held by a state of the walk. -/
def mHead (ρ : mBlock.Assignment A) (p : A) : Prop := ρ (some true) ![p]

/-- The state of the walk that a configuration is. -/
def cfgAssign (c : Lax904597.Machines.Config A) : mBlock.Assignment A
  | none => fun x => c.tape (x 0) = x 1
  | some false => fun x => x 0 = c.state
  | some true => fun x => x 0 = c.head

omit [Lax904597.Machines.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mTape_cfgAssign (c : Lax904597.Machines.Config A) (p a : A) :
    mTape (cfgAssign c) p a ↔ c.tape p = a := Iff.rfl

omit [Lax904597.Machines.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mState_cfgAssign (c : Lax904597.Machines.Config A) (q : A) :
    mState (cfgAssign c) q ↔ q = c.state := Iff.rfl

omit [Lax904597.Machines.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mHead_cfgAssign (c : Lax904597.Machines.Config A) (p : A) :
    mHead (cfgAssign c) p ↔ p = c.head := Iff.rfl

/-! #### The symbols, read back -/

theorem relMap_mIn₁ {n : ℕ} (ρ : mBlock.Assignment A) (r : Lax904597.Machines.turing.Relations n)
    (w : Fin n → A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) n (mIn₁ r) w ↔ RelMap r w := Iff.rfl

theorem relMap_mS₁ (ρ : mBlock.Assignment A) (q : A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) 1 mS₁ ![q] ↔ mState ρ q := Iff.rfl

end Reading

/-! ### Correctness -/

section Correct

end Correct

section Det

end Det

end SpaceTM

open SpaceTM

/-! ### The two problems are in PSPACE -/

end Lax480241Proofs.DescriptiveComplexity


