/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderBlockHom
import DescriptiveComplexity.SecondOrderTransitiveClosurePull

/-!
# Independent copies of a second-order block

An exponential expansion (`DescriptiveComplexity.ExpExpansion`) defines an
`n`-ary relation on its universe – the assignments of a block `B` – by a
first-order sentence that must read `n` assignments at once. The vocabulary it
is written over is therefore `n` independent copies of `B.lang`, packaged here
as a single block `DescriptiveComplexity.SOBlock.replicate`:

* its relation variables are pairs `(k, i)` of a copy index and a variable of
  `B`, with the arity of `i`;
* `DescriptiveComplexity.SOBlock.replicateAssign` assembles one assignment per
  copy into an assignment of the replicated block – on the nose, since the
  index type is a plain product;
* `DescriptiveComplexity.SOBlock.replicateSym` names the symbol of copy `k`,
  read back by `DescriptiveComplexity.SOBlock.relMap_replicateSym`.

This is a *product* presentation of a quantifier prefix, as opposed to the
iterated-merge presentation of `DescriptiveComplexity.repMerged`
(`DescriptiveComplexity.SecondOrderReplicate`), which is built by recursion on
`k` and whose index type is a nest of sums. The product presentation is what
this development needs, for one reason: replication **commutes with the
pullback of a block through an interpretation** definitionally
(`DescriptiveComplexity.SOBlock.homAssign_replicatePullHom`), because both
sides re-associate the same `Σ`-type over a product. Pulling an expansion back
through an interpretation is exactly that re-association, so the commutation is
the load-bearing lemma of `DescriptiveComplexity.Exponential.Pull` and is
proved by `rfl`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

/-! ### The replicated block -/

/-- `n` independent copies of a block: one relation variable per pair of a copy
index and a relation variable of `B`, keeping its arity. -/
def replicate (B : SOBlock) (n : ℕ) : SOBlock where
  ι := Fin n × B.ι
  arity p := B.arity p.2

@[simp]
theorem replicate_arity (B : SOBlock) (n : ℕ) (p : Fin n × B.ι) :
    (B.replicate n).arity p = B.arity p.2 :=
  rfl

/-- The assignment of the replicated block determined by one assignment per
copy. The index type being a plain product, this is currying and nothing
more. -/
def replicateAssign (B : SOBlock) {A : Type} {n : ℕ} (ρs : Fin n → B.Assignment A) :
    (B.replicate n).Assignment A :=
  fun p => ρs p.1 p.2

/-- The relation symbol of the `k`-th copy corresponding to a symbol of the
block's own vocabulary. -/
def replicateSym (B : SOBlock) {n m : ℕ} (k : Fin n) (r : B.lang.Relations m) :
    (B.replicate n).lang.Relations m :=
  ⟨(k, r.1), r.2⟩

/-- **Reading back the relation variable of a copy.** -/
theorem relMap_replicateSym (B : SOBlock) {A : Type} {n m : ℕ} (k : Fin n)
    (r : B.lang.Relations m) (ρs : Fin n → B.Assignment A) (v : Fin m → A) :
    @RelMap (B.replicate n).lang A ((B.replicate n).structure (B.replicateAssign ρs)) m
        (B.replicateSym k r) v ↔
      @RelMap B.lang A (B.structure (ρs k)) m r v :=
  Iff.rfl

/-! ### Replication commutes with the pullback through an interpretation

`DescriptiveComplexity.SOBlock.pull` turns an `a`-ary variable on the
interpreted universe `Tag × A^d` into one `(a · d)`-ary variable on `A` per
tuple of tags. Applied to the replicated block it produces variables indexed by
`Σ (k, i), Fin (B.arity i) → Tag`; replicating the pulled block produces
variables indexed by `Fin n × Σ i, Fin (B.arity i) → Tag`. These are the same
data re-associated, with equal arities, so the induced block morphism is an
arity-preserving bijection and the transported assignments agree by `rfl`. -/

variable (B : SOBlock) (T : Type) [Finite T] (d n : ℕ)

/-- The re-association of indices identifying the pullback of a replicated
block with the replication of the pulled block. -/
def replicatePullHom : ((B.replicate n).pull T d).ι → ((B.pull T d).replicate n).ι :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)

theorem replicatePullHom_arity :
    ∀ i, ((B.pull T d).replicate n).arity (B.replicatePullHom T d n i) =
      ((B.replicate n).pull T d).arity i :=
  fun _ => rfl

/-- The vocabulary morphism reading a sentence over the pullback of the
replicated block inside the replication of the pulled block. -/
def replicatePullLHom : ((B.replicate n).pull T d).lang →ᴸ ((B.pull T d).replicate n).lang :=
  homLHom (B.replicatePullHom T d n) (B.replicatePullHom_arity T d n)

/-- **The load-bearing commutation**: replicating the pulled assignments and
transporting back along the re-association gives the pullback of the replicated
assignment. Both sides read `ρs k i` at the same decoded arguments, so this is
definitional. -/
theorem homAssign_replicatePullHom {A : Type}
    (ρs : Fin n → B.Assignment (T × (Fin d → A))) :
    homAssign (B.replicatePullHom T d n) (B.replicatePullHom_arity T d n)
        ((B.pull T d).replicateAssign fun k => B.pullAssign (ρs k)) =
      (B.replicate n).pullAssign (B.replicateAssign ρs) :=
  rfl

end SOBlock

end DescriptiveComplexity
