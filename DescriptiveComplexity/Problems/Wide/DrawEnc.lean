/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawGeom
import DescriptiveComplexity.Exponential.Expansion

/-!
# Encoding the points of an expansion as block values

A point of an exponential expansion is a tag together with an assignment of
the expansion's block – an exponential object. The EXPSPACE reduction stores
one point per **argument block** of a machine address, so it needs an injective
encoding of points as *block values*, the subsets of the tuple space
`Fin dd → A` an address holds at one tag.

The encoding is a set of tuples, each carrying a **discrete code** and a
**payload** laid out at fixed coordinates (`DescriptiveComplexity.Draw.EncLayout`
fixes the coordinates, `DescriptiveComplexity.Draw.encTup` writes one tuple):

* the *tag witness* `encTup (t, none) 0⃗`, present in every encoding – without
  it, the empty assignments at two different tags would collide;
* one *member tuple* `encTup (t, some i) (pad w)` per tuple `w` the assignment
  puts in its relation variable `i`, the payload canonically padded to the
  block's arity bound.

The discrete code is one-hot in the two designated elements, so
`DescriptiveComplexity.Draw.encTup_code_inj` reads the code back and
`DescriptiveComplexity.Draw.encPt_injective` makes the whole encoding injective;
`DescriptiveComplexity.Draw.mem_encPt_asg` reads one bit of the assignment off
one membership question, which is the form the machine's register lookups take.
`DescriptiveComplexity.Draw.IsEnc` – *being* the encoding of a point of the
expanded universe – is the gate the relativization lemma of
`DescriptiveComplexity.Problems.Wide.DrawRel` asks for
(`DescriptiveComplexity.Draw.isEnc_iff`).
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

/-! ### The layout of one tuple -/

/-- **The coordinates of an encoded tuple**: where the discrete code sits, where
the payload sits, disjointly. The reduction instantiates this once, with
explicit arithmetic; everything else reads the coordinates through it. -/
structure EncLayout (D : Type) (a' dd : ℕ) where
  /-- The coordinate of each component of the one-hot discrete code. -/
  cIx : D → Fin dd
  /-- The coordinate of each payload position. -/
  pIx : Fin a' → Fin dd
  /-- Code coordinates are distinct. -/
  cInj : Function.Injective cIx
  /-- Payload coordinates are distinct. -/
  pInj : Function.Injective pIx
  /-- Code and payload coordinates are disjoint. -/
  disj : ∀ (q : D) (p : Fin a'), cIx q ≠ pIx p

section Tup

variable {D : Type} {a' dd : ℕ} (ly : EncLayout D a' dd) {A : Type} (zero one : A)

open Classical in
/-- **One encoded tuple**: the one-hot code of the discrete datum at the code
coordinates, the payload at the payload coordinates, the designated `zero`
everywhere else. -/
noncomputable def encTup (d : D) (pay : Fin a' → A) : Fin dd → A :=
  Function.extend ly.cIx (fun q => if q = d then one else zero)
    (Function.extend ly.pIx pay fun _ => zero)

variable {ly zero one}

open Classical in
/-- The code coordinates of an encoded tuple spell the one-hot code. -/
theorem encTup_cIx (d q : D) (pay : Fin a' → A) :
    encTup ly zero one d pay (ly.cIx q) = if q = d then one else zero :=
  ly.cInj.extend_apply _ _ q

/-- The payload coordinates of an encoded tuple spell the payload. -/
theorem encTup_pIx (d : D) (pay : Fin a' → A) (p : Fin a') :
    encTup ly zero one d pay (ly.pIx p) = pay p := by
  rw [encTup, Function.extend_apply' _ _ _ fun hc => hc.elim fun q hq => ly.disj q p hq]
  exact ly.pInj.extend_apply _ _ p

/-- The remaining coordinates of an encoded tuple hold the designated `zero`. -/
theorem encTup_of_ne (d : D) (pay : Fin a' → A) {j : Fin dd}
    (hc : ∀ q : D, ly.cIx q ≠ j) (hp : ∀ p : Fin a', ly.pIx p ≠ j) :
    encTup ly zero one d pay j = zero := by
  rw [encTup, Function.extend_apply' _ _ _ fun hcon => hcon.elim fun q hq => hc q hq]
  exact Function.extend_apply' _ _ _ fun hcon => hcon.elim fun p hp' => hp p hp'

/-- **The code reads back**: two encoded tuples that are equal carry the same
discrete datum. -/
theorem encTup_code_inj (hne : zero ≠ one) {d d' : D} {pay pay' : Fin a' → A}
    (h : encTup ly zero one d pay = encTup ly zero one d' pay') : d = d' := by
  have hd := congrFun h (ly.cIx d)
  rw [encTup_cIx, encTup_cIx, if_pos rfl] at hd
  by_contra hcon
  rw [if_neg hcon] at hd
  exact hne hd.symm

/-- **The payload reads back**: two encoded tuples that are equal carry the same
payload. -/
theorem encTup_pay_inj {d d' : D} {pay pay' : Fin a' → A}
    (h : encTup ly zero one d pay = encTup ly zero one d' pay') : pay = pay' :=
  funext fun p => by
    have hp := congrFun h (ly.pIx p)
    rwa [encTup_pIx, encTup_pIx] at hp

end Tup

/-! ### The encoding of a point -/

section Point

variable {L : Language.{0, 0}} {X : ExpExpansion L}

/-- **The discrete data an encoded tuple can carry**: either the *witness* of
a tag – the tuple every encoding carries, and the only place a tag appears –
or the relation variable of the block whose tuple the payload is.

The tag is deliberately **not** in a member's code. It is what makes «this
block value is well-shaped» a question about one cell and nothing else, so
the machine's gate can ask it of every cell by a file test: a member of a
foreign tag is not merely rejected, it does not exist. What is left for the
control is «exactly one witness», and the machine reads every tag's witness
cell anyway. -/
abbrev PtCode (X : ExpExpansion L) : Type := X.Tag ⊕ X.B.ι

variable {dd : ℕ} (ly : EncLayout (PtCode X) (blockArityBound X.B) dd)
variable {A : Type} (zero one : A)

/-- **One member tuple of an encoded point**: the relation variable in the
code, the variable's tuple in the payload, canonically padded to the block's
arity bound. -/
noncomputable def encAsgTup (i : X.B.ι) (w : Fin (X.B.arity i) → A) :
    Fin dd → A :=
  encTup ly zero one (Sum.inr i) (pad zero w)

/-- **The tag witness of an encoded point**: the one tuple that carries the
tag. -/
noncomputable def encTagTup (t : X.Tag) : Fin dd → A :=
  encTup ly zero one (Sum.inl t) fun _ => zero

/-- **The encoding of a point as a block value**: the tag witness, plus one
member tuple per tuple of the assignment. -/
noncomputable def encPt (p : X.Point A) : (Fin dd → A) → Prop := fun v =>
  v = encTagTup ly zero one p.1 ∨
    ∃ (i : X.B.ι) (w : Fin (X.B.arity i) → A), p.2 i w ∧ v = encAsgTup ly zero one i w

variable {zero one}

/-- **An encoding is never everything**: every member of it carries a one-hot
code, so the all-`zero` tuple is not one. This is what puts a tuple's address
*strictly* below the logical top — the top's blocks are full. -/
theorem not_encPt_zeroTup (hne : zero ≠ one) (p : X.Point A) :
    ¬encPt ly zero one p (fun _ => zero) := by
  rintro (h | ⟨i, w, -, h⟩)
  · have hc := congrFun h (ly.cIx (Sum.inl p.1))
    rw [encTagTup, encTup_cIx, if_pos rfl] at hc
    exact hne hc
  · have hc := congrFun h (ly.cIx (Sum.inr i))
    rw [encAsgTup, encTup_cIx, if_pos rfl] at hc
    exact hne hc

/-- The tag witness belongs to the encoding. -/
theorem encPt_tagTup (p : X.Point A) : encPt ly zero one p (encTagTup ly zero one p.1) :=
  Or.inl rfl

/-- **A membership question at a tag witness reads the tag**: the tag witness of
`t` belongs to the encoding of `p` exactly when `p` carries the tag `t`. -/
theorem mem_encPt_tag (hne : zero ≠ one) (p : X.Point A) (t : X.Tag) :
    encPt ly zero one p (encTagTup ly zero one t) ↔ p.1 = t := by
  constructor
  · rintro (h | ⟨i, w, -, h⟩)
    · exact Sum.inl.inj (encTup_code_inj hne h.symm)
    · exact absurd (encTup_code_inj hne h.symm) (by simp)
  · rintro rfl
    exact encPt_tagTup ly p

/-- **A membership question at a member tuple reads one bit of the assignment**:
the member tuple of `(t, i, w)` belongs to the encoding of `p` exactly when `p`
carries the tag `t` and its assignment holds of `w` at `i`. This is the form
the machine's register lookups take. -/
theorem mem_encPt_asg (hne : zero ≠ one) (p : X.Point A) (i : X.B.ι)
    (w : Fin (X.B.arity i) → A) :
    encPt ly zero one p (encAsgTup ly zero one i w) ↔ p.2 i w := by
  constructor
  · rintro (h | ⟨i', w', hw', h⟩)
    · exact absurd (encTup_code_inj hne h) (by simp)
    · have hcode := encTup_code_inj hne h.symm
      have hi : i = i' := Sum.inr.inj hcode.symm
      subst hi
      have hpay : pad zero w = pad (dd := blockArityBound X.B) zero w' :=
        encTup_pay_inj h
      have hw : w = w' := pad_injective (arity_le_blockArityBound X.B i) hpay
      subst hw
      exact hw'
  · intro hw
    exact Or.inr ⟨i, w, hw, rfl⟩

/-- **The encoding is injective on points.** -/
theorem encPt_injective (hne : zero ≠ one) :
    Function.Injective (encPt ly (A := A) zero one) := by
  intro p p' h
  have htag : p.1 = p'.1 := by
    have := (mem_encPt_tag ly hne p' p.1).mp (h ▸ encPt_tagTup ly p)
    exact this.symm
  refine Prod.ext htag (funext fun i => funext fun w => propext ?_)
  exact (mem_encPt_asg ly hne p i w).symm.trans
    ((iff_of_eq (congrFun h (encAsgTup ly zero one i w))).trans
      (mem_encPt_asg ly hne p' i w))

/-! ### The gate -/

variable [L.Structure A] [LinearOrder A]

variable (zero one) in
/-- **The encoding of a point of the expanded universe**: the domain condition
is carried by the subtype, so this is the map whose image the machine's gates
carve out. -/
noncomputable def encMap (m : X.Map A) : (Fin dd → A) → Prop := encPt ly zero one m.1

variable (zero one) in
/-- **Being an encoding**: the gate of the relativization – a block value passes
exactly when it encodes a point of the expanded universe, domain condition
included. -/
def IsEnc (S : (Fin dd → A) → Prop) : Prop := ∃ m : X.Map A, S = encMap ly zero one m

/-- The encoding of the expanded universe is injective. -/
theorem encMap_injective (hne : zero ≠ one) :
    Function.Injective (encMap ly (A := A) zero one) := fun _m _m' h =>
  ExpExpansion.map_ext
    (congrArg Prod.fst (encPt_injective ly hne h))
    (congrArg Prod.snd (encPt_injective ly hne h))

/-- The gate is the image of the encoding, in the orientation the
relativization lemma asks for. -/
theorem isEnc_iff (S : (Fin dd → A) → Prop) :
    IsEnc ly (A := A) zero one S ↔ ∃ m : X.Map A, encMap ly zero one m = S :=
  exists_congr fun _ => eq_comm

end Point

end Draw

end DescriptiveComplexity
