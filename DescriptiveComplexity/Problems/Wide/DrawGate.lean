/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawEnc

/-!
# The gate, decomposed the way the machine checks it

`DescriptiveComplexity.Draw.IsEnc` – a block value encodes a point of the
expanded universe – is an existential over points, which is not a shape a
machine can test. This file decomposes it into the three questions the
program's gate subroutine actually asks:

* **exactly one tag's witness is present** – one membership question per tag,
  finitely many, and the answers are the control's tag flags;
* **every member is well-shaped** – a witness tuple or a member tuple: one
  file test, the per-cell question read off the name marks, and *tag-free*,
  which is why the code of a member carries no tag
  (`DescriptiveComplexity.Draw.PtCode`);
* **the domain sentence holds of the decoded assignment** – where
  `DescriptiveComplexity.Draw.decRho` reads the assignment back one membership
  question per bit, which is the element-loop sub-evaluation.

`DescriptiveComplexity.Draw.isEnc_iff_parts` is the equivalence. Uniqueness of
the witness is a clause and not an afterthought – with tag-free members it is
the only thing tying the block value to one tag – and it costs nothing: the
machine reads every tag's witness cell anyway, so the condition is a
one-hotness test on the flags it has just filled.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

section Gate

variable {L : Language.{0, 0}} {X : ExpExpansion L}
variable {dd : ℕ} (ly : EncLayout (PtCode X) (blockArityBound X.B) dd)
variable {A : Type} (zero one : A)

/-- **The assignment a block value decodes to at a tag**: one membership
question per bit. On a value that is an encoding this is the encoded
assignment; elsewhere it is read only under the gate's other clauses. -/
def decRho (S : (Fin dd → A) → Prop) : X.B.Assignment A :=
  fun i w => S (encAsgTup ly zero one i w)

variable {zero one}

/-- On an encoding, the decoded assignment is the encoded one. -/
theorem decRho_encPt (hne : zero ≠ one) (p : X.Point A) :
    decRho ly zero one (encPt ly zero one p) = p.2 := by
  funext i w
  exact propext (mem_encPt_asg ly hne p i w)

variable [L.Structure A] [LinearOrder A]

/-- **The gate, decomposed**: a block value is an encoding exactly when some
tag's witness belongs to it, every member is well-shaped for that tag, and the
domain sentence holds of the decoded assignment. These are the three questions
the machine's gate subroutine asks, in the order it asks them. -/
theorem isEnc_iff_parts (hne : zero ≠ one) (S : (Fin dd → A) → Prop) :
    IsEnc ly (A := A) zero one S ↔
      ∃ t : X.Tag, S (encTagTup ly zero one t) ∧
        (∀ t' : X.Tag, S (encTagTup ly zero one t') → t' = t) ∧
        (∀ v : Fin dd → A, S v → ((∃ t' : X.Tag, v = encTagTup ly zero one t') ∨
          ∃ (i : X.B.ι) (w : Fin (X.B.arity i) → A), v = encAsgTup ly zero one i w)) ∧
        ExpExpansion.DomHolds (X := X) (t, decRho ly zero one S) := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m.1.1, encPt_tagTup ly m.1, fun t' ht' => ?_, fun v hv => ?_, ?_⟩
    · exact ((mem_encPt_tag ly hne m.1 t').mp ht').symm
    · rcases hv with hv | ⟨i, w, -, hv⟩
      · exact Or.inl ⟨m.1.1, hv⟩
      · exact Or.inr ⟨i, w, hv⟩
    · have hd : decRho ly zero one (encMap ly zero one m) = m.1.2 :=
        decRho_encPt ly hne m.1
      rw [hd]
      exact m.2
  · rintro ⟨t, hwit, huniq, hshape, hdom⟩
    refine ⟨ExpExpansion.pt t (decRho ly zero one S) hdom, ?_⟩
    funext v
    refine propext ?_
    constructor
    · intro hv
      rcases hshape v hv with ⟨t', rfl⟩ | ⟨i, w, rfl⟩
      · rw [huniq t' hv]
        exact Or.inl rfl
      · exact Or.inr ⟨i, w, hv, rfl⟩
    · rintro (rfl | ⟨i, w, hw, rfl⟩)
      · exact hwit
      · exact hw

end Gate

end Draw

end DescriptiveComplexity
