/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax832283Proofs.DescriptiveComplexity.Strings.Program
import Lax832283Proofs.DescriptiveComplexity.Strings.Transport
import Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
import Lax832283Proofs.DescriptiveComplexity.FixedPointInflationary
import Lax832283Proofs.DescriptiveComplexity.OrderWalk
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
import Lax751879.FixedPointSemantics
import Lax751879.FixedPointSyntax
import Lax751879.LeastFixedPoints
import Lax751879.OrderedStructures
import Lax751879.PolynomialTime
import Lax751879.StructureEncoding
import Lax832283.StringProblems
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder
import Lax988886.ExistentialSecondOrder
import Lax988886.FiniteStructures
import Lax988886.NondeterministicPolynomialTime

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax751879.FixedPointSemantics
end Lax751879.FixedPointSemantics

namespace Lax751879.FixedPointSyntax
end Lax751879.FixedPointSyntax

namespace Lax751879.LeastFixedPoints
end Lax751879.LeastFixedPoints

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax832283.StringProblems
end Lax832283.StringProblems

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures
export Lax751879.OrderedStructures (OrderedStructure Symbol Vocabulary)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.OrderedStructures

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.LeastFixedPoints
export Lax751879.LeastFixedPoints (stage)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.LeastFixedPoints

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax
export Lax751879.FixedPointSyntax (RawFormula Sentence)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSyntax

namespace Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics
export Lax751879.FixedPointSemantics (RelationEnv bodyOperator eval extend)
end Lax832283Proofs.DescriptiveComplexity.Strings.Lax.FixedPointSemantics

namespace Lax832283Proofs.DescriptiveComplexity.Strings
export Lax832283.StringProblems (FinVocab ofOrdered)
end Lax832283Proofs.DescriptiveComplexity.Strings

namespace Lax832283Proofs.DescriptiveComplexity
export Lax535992.InflationaryFixedPoint (StepDef)
end Lax832283Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax535992.InflationaryFixedPoint.SOBlock (structure₁)
end Lax904597.SecondOrder.SOBlock

/-!
# FO(LFP) of the archive, as a definition of the library

A formula of the archive may nest, negate, and parameterize its fixed points, and a
fixed point may be nested in the body of another one and mention its relation variable.
`DescriptiveComplexity.Strings.compile` turns any such formula into one inflationary
program, by induction on the formula, the operations of
`DescriptiveComplexity.Strings.Prog` doing the work.

## Parameters and relation variables

A relation variable bound by a fixed point in a context of `m` element variables has a
different value at each assignment of these. The program stores all of them at once, by
giving the relation `m` further coordinates. Since a binder only ever extends the context
of element variables, the parameters of an enclosing fixed point are still in the context
when its variable is read: reading it means passing their current positions. So what
`DescriptiveComplexity.Strings.compile` takes for a relation variable is a function
producing the atom, given the arguments of the variable and the positions of the
parameters; going under a binder composes the positions.

## Fixed points

For a fixed point with a body in `k + m` variables, the body compiles to a program over the
vocabulary expanded by a relation of arity `k + m`, and
`DescriptiveComplexity.Strings.Prog.iter` iterates it once per `k`-tuple of the universe.
That is enough rounds: there are as many `k`-tuples as the size of the set the operator
acts on, for each value of the parameters, and the operator is monotone
(`DescriptiveComplexity.Strings.Lax.FixedPointSemantics.positiveBodyMonotone`), so
`DescriptiveComplexity.Strings.Lax.LeastFixedPoints.finiteConvergence` applies. Positivity
is used nowhere else: the program itself does not care.
-/

namespace Lax832283Proofs.DescriptiveComplexity.Strings

open FirstOrder Language Structure

open Lax.OrderedStructures Lax.LeastFixedPoints Lax.FixedPointSyntax Lax.FixedPointSemantics

variable {σ : Lax751879.OrderedStructures.Vocabulary}

/-- The formulas of an ordered vocabulary with free variables in a context. -/
abbrev OF (K : Language.{0, 0}) (m : ℕ) : Type := (K.sum Language.order).Formula (Fin m)

/-- The atoms of the input vocabulary, in a language `K`. -/
abbrev RelOps (σ : Lax751879.OrderedStructures.Vocabulary) (K : Language.{0, 0}) : Type :=
  ∀ (r : Lax751879.OrderedStructures.Symbol σ) (m' : ℕ), (Fin (σ.get r) → Fin m') → OF K m'

/-- The atoms of the relation variables, in a language `K`: from the arguments of the
variable, in a context `m'`, and the positions in that context of the `m` variables of the
current context. -/
abbrev VarOps (ρ : List ℕ) (m : ℕ) (K : Language.{0, 0}) : Type :=
  ∀ (r : Fin ρ.length) (m' : ℕ), (Fin (ρ.get r) → Fin m') → (Fin m → Fin m') → OF K m'

/-- The atoms under a quantifier. -/
def VarOps.shift {ρ : List ℕ} {m : ℕ} {K : Language.{0, 0}} (Γ : VarOps ρ m K) :
    VarOps ρ (m + 1) K :=
  fun r m' a q => Γ r m' a (q ∘ Fin.succ)

/-- The inclusion of a vocabulary in its expansion by a relation. -/
abbrev liftOF {K : Language.{0, 0}} {a m' : ℕ} (φ : OF K m') : OF (Prog.KX K a) m' :=
  (LHom.sumMap (LHom.sumInl (L' := (Prog.xBlock a).lang)) (LHom.id Language.order)).onFormula φ

/-- The atom of the relation bound by a fixed point. -/
noncomputable def xAtomF {K : Language.{0, 0}} {k m m' : ℕ} (a : Fin k → Fin m')
    (q : Fin (k + m) → Fin m') : OF (Prog.KX K (k + m)) m' :=
  Relations.formula (Sum.inl (Prog.xSym K (k + m)))
    (Fin.append (fun i => Term.var (a i)) (fun i => Term.var (q (Fin.natAdd k i))))

/-- The atoms under a fixed point. -/
noncomputable def VarOps.bind {ρ : List ℕ} {K : Language.{0, 0}} {m : ℕ} (k : ℕ)
    (Γ : VarOps ρ m K) : VarOps (k :: ρ) (k + m) (Prog.KX K (k + m)) := fun r =>
  Fin.cases (motive := fun r : Fin (k :: ρ).length => ∀ (m' : ℕ), (Fin ((k :: ρ).get r) → Fin m') →
      (Fin (k + m) → Fin m') → OF (Prog.KX K (k + m)) m')
    (fun _ a q => xAtomF a q)
    (fun r _ a q => liftOF (Γ r _ a (q ∘ Fin.natAdd k))) r

/-- **The compilation of a formula into a program.** -/
noncomputable def compile : ∀ {m : ℕ} {ρ : List ℕ} (_ : Lax751879.FixedPointSyntax.RawFormula σ m ρ) {K : Language.{0, 0}}
    [K.IsRelational] (_ : RelOps σ K) (_ : VarOps ρ m K), Prog K m
  | _, _, .truth, _, _, _, _ => .ofFormula ⊤
  | _, _, .equal x y, _, _, _, _ => .ofFormula (Term.equal (Term.var x) (Term.var y))
  | _, _, .less x y, K, _, _, _ => .ofFormula (ltF (L := K) x y)
  | _, _, .relation r args, _, _, Δ, _ => .ofFormula (Δ r _ args)
  | _, _, .variable r args, _, _, _, Γ => .ofFormula (Γ r _ args id)
  | _, _, .neg φ, _, _, Δ, Γ => (compile φ Δ Γ).neg
  | _, _, .conj φ ψ, _, _, Δ, Γ => Prog.conj (compile φ Δ Γ) (compile ψ Δ Γ)
  | _, _, .exists' φ, _, _, Δ, Γ => (compile φ Δ Γ.shift).ex
  | m, _, .lfp k body args, K, _, Δ, Γ =>
      (Prog.iter (compile body (K := Prog.KX K (k + m))
        (fun r m' a => liftOF (Δ r m' a)) (Γ.bind k)) k).rename
        (Fin.append args id)

/-! ### Correctness -/

section Correct

variable (S : Lax751879.OrderedStructures.OrderedStructure σ)

/-- A formula read through the inclusion of a vocabulary in its expansion. -/
private theorem realize_liftOF {K : Language.{0, 0}} [K.Structure (Fin S.size)] {a m' : ℕ}
    (W : (Prog.xBlock a).Assignment (Fin S.size)) (φ : OF K m') (w : Fin m' → Fin S.size) :
    @Formula.Realize _ _ (Prog.xOrd W) _ (liftOF (a := a) φ) w ↔ φ.Realize w := by
  let := Prog.xStr (K := K) W
  let := (Prog.xBlock a).structure W
  let := orderStructure (M := Fin S.size)
  have : (LHom.sumMap (LHom.sumInl (L := K) (L' := (Prog.xBlock a).lang))
      (LHom.id Language.order)).IsExpansionOn (Fin S.size) := inferInstance
  exact LHom.realize_onFormula (M := Fin S.size) _ φ

/-- The slices of the iterated operator are the iterated slices of the operator. -/
private theorem stage_slice {m k : ℕ} {ρ : List ℕ} (body : Lax751879.FixedPointSyntax.RawFormula σ (k + m) (k :: ρ))
    (η : (Fin m → Fin S.size) → Lax751879.FixedPointSemantics.RelationEnv S.size ρ)
    (G : Set (Fin (k + m) → Fin S.size) → Set (Fin (k + m) → Fin S.size))
    (hG : ∀ (W : Set (Fin (k + m) → Fin S.size)) (a : Fin k → Fin S.size) (v : Fin m → Fin S.size),
      Fin.append a v ∈ G W ↔
        Lax751879.FixedPointSemantics.eval body S (Fin.append a v) (Lax751879.FixedPointSemantics.extend {a' | Fin.append a' v ∈ W} (η v)))
    (t : ℕ) (a : Fin k → Fin S.size) (v : Fin m → Fin S.size) :
    Fin.append a v ∈ Lax751879.LeastFixedPoints.stage G t ↔ a ∈ Lax751879.LeastFixedPoints.stage (Lax751879.FixedPointSemantics.bodyOperator body S v (η v)) t := by
  induction t generalizing a with
  | zero => exact Iff.rfl
  | succ t ih =>
    refine (hG _ a v).trans ?_
    have : {a' | Fin.append a' v ∈ Lax751879.LeastFixedPoints.stage G t} = Lax751879.LeastFixedPoints.stage (Lax751879.FixedPointSemantics.bodyOperator body S v (η v)) t := by
      ext a'
      exact ih a'
    rw [this]
    exact Iff.rfl

/-- **The compilation is correct.** -/
theorem val_compile (hS : 0 < S.size) {m : ℕ} {ρ : List ℕ} (φ : Lax751879.FixedPointSyntax.RawFormula σ m ρ)
    (hφ : φ.Admissible) {K : Language.{0, 0}} [K.IsRelational] [K.Structure (Fin S.size)]
    (Δ : RelOps σ K) (Γ : VarOps ρ m K)
    (η : (Fin m → Fin S.size) → Lax751879.FixedPointSemantics.RelationEnv S.size ρ)
    (hΔ : ∀ (r : Lax751879.OrderedStructures.Symbol σ) (m' : ℕ) (a : Fin (σ.get r) → Fin m') (w : Fin m' → Fin S.size),
      (Δ r m' a).Realize w ↔ S.relation r (w ∘ a) = true)
    (hΓ : ∀ (r : Fin ρ.length) (m' : ℕ) (a : Fin (ρ.get r) → Fin m') (q : Fin m → Fin m')
      (w : Fin m' → Fin S.size), (Γ r m' a q).Realize w ↔ w ∘ a ∈ η (w ∘ q) r)
    (w : Fin m → Fin S.size) :
    (compile φ Δ Γ).Val (Fin S.size) w ↔ Lax751879.FixedPointSemantics.eval φ S w (η w) := by
  have : Nonempty (Fin S.size) := Fin.pos_iff_nonempty.mp hS
  induction φ generalizing K with
  | truth => exact (Prog.val_ofFormula _ _ _).trans (by simp [Lax751879.FixedPointSemantics.eval])
  | equal x y =>
    refine (Prog.val_ofFormula _ _ _).trans ?_
    simp [Lax751879.FixedPointSemantics.eval, Formula.realize_equal]
  | less x y =>
    exact (Prog.val_ofFormula _ _ _).trans (realize_ltF x y)
  | relation r args =>
    exact (Prog.val_ofFormula _ _ _).trans (hΔ r _ args w)
  | «variable» r args =>
    exact (Prog.val_ofFormula _ _ _).trans (hΓ r _ args id w)
  | neg φ ih =>
    exact not_congr (ih hφ Δ Γ η hΔ hΓ w)
  | conj φ ψ ih₁ ih₂ =>
    exact (Prog.val_conj _ _ _ _).trans
      (and_congr (ih₁ hφ.1 Δ Γ η hΔ hΓ w) (ih₂ hφ.2 Δ Γ η hΔ hΓ w))
  | exists' φ ih =>
    refine (Prog.val_ex _ _ _).trans (exists_congr fun a => ?_)
    exact ih hφ Δ Γ.shift (fun x => η (x ∘ Fin.succ)) hΔ
      (fun r m' a' q w' => hΓ r m' a' (q ∘ Fin.succ) w') (Fin.cons a w)
  | @lfp m ρ k body args ih =>
    let p := compile body (K := Prog.KX K (k + m)) (fun r m' a => liftOF (Δ r m' a)) (Γ.bind k)
    refine (Prog.val_rename _ _ _ _).trans ?_
    refine (Prog.val_iter _).trans ?_
    have hG : ∀ (W : Set (Fin (k + m) → Fin S.size)) (a : Fin k → Fin S.size)
        (v : Fin m → Fin S.size), Fin.append a v ∈ Prog.gOp p W ↔
        Lax751879.FixedPointSemantics.eval body S (Fin.append a v) (Lax751879.FixedPointSemantics.extend {a' | Fin.append a' v ∈ W} (η v)) := by
      intro W a v
      let := Prog.xStr (K := K) (fun _ => W)
      have hval := ih hφ.1 (K := Prog.KX K (k + m)) (fun r m' a => liftOF (Δ r m' a)) (Γ.bind k)
        (fun u => Lax751879.FixedPointSemantics.extend {a' | Fin.append a' (u ∘ Fin.natAdd k) ∈ W} (η (u ∘ Fin.natAdd k)))
        (fun r m' a' w' => (realize_liftOF S (fun _ => W) (Δ r m' a') w').trans (hΔ r m' a' w'))
        ?_ (Fin.append a v)
      · have hv : Fin.append a v ∘ Fin.natAdd k = v := funext fun q => Fin.append_right a v q
        rw [hv] at hval
        exact hval
      · intro r
        refine Fin.cases ?_ (fun r' => ?_) r
        · intro m' a' q w'
          change W _ ↔ W _
          refine iff_of_eq (congrArg W ?_)
          funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp [Function.comp]
          · simp [Function.comp]
        · intro m' a' q w'
          exact (realize_liftOF S (fun _ => W) _ w').trans (hΓ r' m' a' _ w')
    have hx : w ∘ Fin.append args id = Fin.append (w ∘ args) w := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
    rw [hx]
    refine (stage_slice S body η _ hG _ (w ∘ args) w).trans ?_
    have hcard : Nat.card (Fin k → Fin S.size) = Fintype.card (Fin k → Fin S.size) :=
      Nat.card_eq_fintype_card
    rw [hcard, finiteConvergence _ (positiveBodyMonotone body hφ.1 hφ.2 S w (η w))]
    exact Iff.rfl

end Correct

/-! ### From a formula of the archive to a definition of the library -/

section Definable

variable {L : Language.{0, 0}} [L.IsRelational] (V : Lax832283.StringProblems.FinVocab L)

/-- The relation atoms of the input vocabulary. -/
noncomputable def baseRel : RelOps V.σ L := fun r _ a =>
  Relations.formula (Sum.inl (V.ofSym r)) fun i => Term.var (a i)

/-- There is no relation variable at the top. -/
def baseVar : VarOps [] 0 L := fun r => r.elim0

/-- The induction of a sentence of the archive. -/
noncomputable def sentenceDef (φ : Lax751879.FixedPointSyntax.RawFormula V.σ 0 []) : Lax535992.InflationaryFixedPoint.StepDef (L.sum Language.order) :=
  let p := compile φ (baseRel V) (baseVar (L := L))
  ⟨p.B, p.step, p.out.relabel (Fin.elim0 : Fin 0 → Empty)⟩

theorem sentenceDef_holds (S : Lax751879.OrderedStructures.OrderedStructure V.σ) (hS : 0 < S.size)
    (φ : Lax751879.FixedPointSyntax.Sentence V.σ) :
    letI := Lax832283.StringProblems.ofOrdered V S
    (sentenceDef V φ.1).IFPHolds (Fin S.size) ↔
      Lax751879.FixedPointSemantics.eval φ.1 S Fin.elim0 (fun r => r.elim0) := by
  let := Lax832283.StringProblems.ofOrdered V S
  let p := compile φ.1 (baseRel V) (baseVar (L := L))
  have hval := val_compile S hS φ.1 φ.2 (K := L) (baseRel V) (baseVar (L := L))
    (fun _ r => r.elim0) ?_ (fun r => r.elim0) Fin.elim0
  · refine Iff.trans ?_ hval
    let := p.B.structure₁ (L := L.sum Language.order) (p.sd.inflLimit (Fin S.size))
    change (p.out.relabel _).Realize default ↔ p.out.Realize _
    refine Formula.realize_relabel.trans (iff_of_eq (congrArg _ (Subsingleton.elim _ _)))
  · intro r m' a w
    exact (relMap_ofOrdered_ofSym V S r _)

end Definable

end Lax832283Proofs.DescriptiveComplexity.Strings


