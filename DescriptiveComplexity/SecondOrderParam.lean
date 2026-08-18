/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrder

/-!
# A block with one argument more

Two constructions want the same operation on a block of relation variables: an
iteration run *at a parameter* (`DescriptiveComplexity.FixedPointParam`) gives
every variable the parameter as a further argument, and a kernel whose variables
must all have an argument
(`DescriptiveComplexity.Exponential.KernelArity`) gives them a dummy one. The
block, the symbol map and the way an assignment of the extended block is read at
one value of the extra argument are the same in both, and are here.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {N : Type}

/-- The block `B` with one extra argument on every relation variable: the
parameter the iteration is run at. -/
def SOBlock.withParam (B : SOBlock) : SOBlock where
  ι := B.ι
  arity i := B.arity i + 1

/-- A relation variable of the block, read at the extended block: one argument
more. -/
def SOBlock.paramSym (B : SOBlock) {m : ℕ} (r : B.lang.Relations m) :
    B.withParam.lang.Relations (m + 1) :=
  ⟨r.1, congrArg (· + 1) r.2⟩

variable {N : Type}

/-- An assignment of the extended block, read at one parameter. -/
def SOBlock.atParam (B : SOBlock) (ρ : B.withParam.Assignment N) (c : N) : B.Assignment N :=
  fun i x => ρ i (Fin.cons c x)

/-- **Reading a parameterized relation variable**: the extended variable at a
tuple whose first argument is the parameter is the original variable, read at
the assignment taken at that parameter. -/
theorem SOBlock.relMap_paramSym (B : SOBlock) (ρ : B.withParam.Assignment N) (c : N) {m : ℕ}
    (b : B.lang.Relations m) (w : Fin (m + 1) → N) (hw : w 0 = c) :
    (@RelMap B.withParam.lang N (B.withParam.structure ρ) (m + 1) (B.paramSym b) w ↔
      @RelMap B.lang N (B.structure (B.atParam ρ c)) m b fun i => w i.succ) := by
  have hvec : (fun j => w (Fin.cast (congrArg (· + 1) b.2) j)) =
      Fin.cons c fun j => w (Fin.cast b.2 j).succ := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Fin.cons_zero]
      exact (congrArg w (Fin.ext rfl)).trans hw
    · rw [Fin.cons_succ]
      exact congrArg w (Fin.ext rfl)
  exact iff_of_eq (congrArg (ρ b.1) hvec)

end DescriptiveComplexity
