/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Machine.Space

/-!
# Determinism is a promise a reduction can enforce: `DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace`

The transfer step of the PSPACE machine bridge. Hardness travels *forward*
along reductions, so a single hardness proof – for the deterministic problem,
which is the harder one to establish – gives the nondeterministic one as soon
as `DescriptiveComplexity.DTMAcceptSpace` reduces to
`DescriptiveComplexity.NTMAcceptSpace`.

The two problems differ only in that the deterministic one folds
`DescriptiveComplexity.TMData.Deterministic` into its yes-instances. That
condition is first-order (`DescriptiveComplexity.SpaceTM.detF`), so the
reduction is the *identity* interpretation – one dimension, one tag – with a
single change: the accepting states of the image are the accepting states of
the source **guarded by the determinism sentence**. A source whose table is
deterministic is copied verbatim; a source whose table is not has no accepting
state at all in the image, hence no accepting run, and both sides are
no-instances.

Nothing here needs an order, so this is a plain `≤ᶠᵒ` reduction; the ordered
and relativized readings follow.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace DetToNondet

/-! ### The interpretation -/

/-- The determinism of the instance, as a first-order formula whose free
variables are unused: the guard the image puts on its accepting states. -/
noncomputable def detG (γ : Type) : Language.turing.Formula γ :=
  SpaceTM.detF tmTr tmStart tmSrc tmRead tmDst tmWrite

/-- **The identity interpretation with a guarded accepting predicate.** Every
symbol is copied; `acc` is copied only when the transition table is
deterministic. -/
noncomputable def detInterp : FOInterpretation Language.turing Language.turing Unit 1 where
  relFormula {n} R _ :=
    match n, R with
    | _, .posn => fo%⟨u⟩ tmPosn(u)
    | _, .tr => fo%⟨u⟩ tmTr(u)
    | _, .start => fo%⟨u⟩ tmStart(u)
    | _, .acc => fo%⟨u⟩ !(detG _) ∧ tmAcc(u)
    | _, .blank => fo%⟨u⟩ tmBlank(u)
    | _, .right => fo%⟨u⟩ tmRight(u)
    | _, .le => fo%⟨u, v⟩ tmLe(u, v)
    | _, .tsrc => fo%⟨u, v⟩ tmSrc(u, v)
    | _, .tread => fo%⟨u, v⟩ tmRead(u, v)
    | _, .tdst => fo%⟨u, v⟩ tmDst(u, v)
    | _, .twrite => fo%⟨u, v⟩ tmWrite(u, v)
    | _, .inp => fo%⟨u, v⟩ tmInp(u, v)

section Reading

variable {A : Type} [Language.turing.Structure A]

/-- The universe of the image is the universe of the source. -/
noncomputable abbrev toBase (x : detInterp.Map A) : A := detInterp.mapEquivSelf A x

@[simp]
theorem detG_realize {γ : Type} (v : γ → A) :
    (detG γ).Realize v ↔ (tmData A).Deterministic := by
  rw [detG]
  simp only [SpaceTM.realize_detF]
  exact Iff.rfl

/-- The unary symbols other than `acc` are copied, so their reading is the
reading of the source. -/
private theorem rel₁_map (R : Language.turing.Relations 1)
    (h : ∀ t, detInterp.relFormula R t = Relations.formula₁ R (Term.var (0, 0)))
    (x : detInterp.Map A) : (RelMap R ![x] : Prop) ↔ RelMap R ![toBase x] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x]) ?_
  rw [h]
  simp only [Formula.realize_rel₁, Term.realize_var]
  exact Iff.rfl

/-- The binary symbols are copied, so their reading is the reading of the
source. -/
private theorem rel₂_map (R : Language.turing.Relations 2)
    (h : ∀ t, detInterp.relFormula R t =
      Relations.formula₂ R (Term.var (0, 0)) (Term.var (1, 0)))
    (x y : detInterp.Map A) :
    (RelMap R ![x, y] : Prop) ↔ RelMap R ![toBase x, toBase y] := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A R ![x, y]) ?_
  rw [h]
  simp only [Formula.realize_rel₂, Term.realize_var]
  exact Iff.rfl

@[simp] theorem posn_map (x : detInterp.Map A) : TMPosn x ↔ TMPosn (toBase x) :=
  rel₁_map tmPosn (fun _ => rfl) x
@[simp] theorem tr_map (x : detInterp.Map A) : TMTr x ↔ TMTr (toBase x) :=
  rel₁_map tmTr (fun _ => rfl) x
@[simp] theorem start_map (x : detInterp.Map A) : TMStart x ↔ TMStart (toBase x) :=
  rel₁_map tmStart (fun _ => rfl) x
@[simp] theorem blank_map (x : detInterp.Map A) : TMBlank x ↔ TMBlank (toBase x) :=
  rel₁_map tmBlank (fun _ => rfl) x
@[simp] theorem right_map (x : detInterp.Map A) : TMRight x ↔ TMRight (toBase x) :=
  rel₁_map tmRight (fun _ => rfl) x

@[simp] theorem le_map (x y : detInterp.Map A) : TMLe x y ↔ TMLe (toBase x) (toBase y) :=
  rel₂_map tmLe (fun _ => rfl) x y
@[simp] theorem src_map (x y : detInterp.Map A) : TMSrc x y ↔ TMSrc (toBase x) (toBase y) :=
  rel₂_map tmSrc (fun _ => rfl) x y
@[simp] theorem read_map (x y : detInterp.Map A) :
    TMRead x y ↔ TMRead (toBase x) (toBase y) :=
  rel₂_map tmRead (fun _ => rfl) x y
@[simp] theorem dst_map (x y : detInterp.Map A) : TMDst x y ↔ TMDst (toBase x) (toBase y) :=
  rel₂_map tmDst (fun _ => rfl) x y
@[simp] theorem write_map (x y : detInterp.Map A) :
    TMWrite x y ↔ TMWrite (toBase x) (toBase y) :=
  rel₂_map tmWrite (fun _ => rfl) x y
@[simp] theorem inp_map (x y : detInterp.Map A) : TMInp x y ↔ TMInp (toBase x) (toBase y) :=
  rel₂_map tmInp (fun _ => rfl) x y

/-- **The accepting states of the image are guarded**: an element is accepting
there exactly when the source table is deterministic and it is accepting in the
source. -/
@[simp]
theorem acc_map (x : detInterp.Map A) :
    TMAcc x ↔ ((tmData A).Deterministic ∧ TMAcc (toBase x)) := by
  refine Iff.trans (FOInterpretation.relMap_map detInterp A tmAcc ![x]) ?_
  simp only [detInterp, Formula.realize_inf, detG_realize, Formula.realize_rel₁,
    Term.realize_var]
  exact Iff.rfl

/-- **A deterministic instance is copied verbatim.** -/
theorem agree_of_det (hdet : (tmData A).Deterministic) :
    (tmData (detInterp.Map A)).Agree (detInterp.mapEquivSelf A) (tmData A) where
  posn := posn_map
  le := le_map
  tr := tr_map
  start := start_map
  acc x := (acc_map x).trans (and_iff_right hdet)
  blank := blank_map
  right := right_map
  src := src_map
  read := read_map
  dst := dst_map
  write := write_map
  inp := inp_map

/-- **A nondeterministic instance has no accepting state in the image**, so its
image cannot accept. -/
theorem not_acceptsSpace_of_not_det (hdet : ¬(tmData A).Deterministic) :
    ¬(tmData (detInterp.Map A)).AcceptsSpace := by
  rintro ⟨-, c, -, -, hacc⟩
  exact hdet ((acc_map c.state).mp hacc).1

end Reading

/-- **The reduction is correct**: the image accepts in bounded space exactly
when the source is a well-formed *deterministic* machine accepting in bounded
space. -/
theorem correct (A : Type) [Language.turing.Structure A] [Finite A] [Nonempty A] :
    DTMAcceptSpace A ↔ NTMAcceptSpace (detInterp.Map A) := by
  by_cases hdet : (tmData A).Deterministic
  · have h := agree_of_det hdet
    exact ⟨fun ⟨hwf, _, hacc⟩ => ⟨h.wellFormed.mpr hwf, h.acceptsSpace.mpr hacc⟩,
      fun ⟨hwf, hacc⟩ => ⟨h.wellFormed.mp hwf, hdet, h.acceptsSpace.mp hacc⟩⟩
  · exact ⟨fun h => absurd h.2.1 hdet, fun h => absurd h.2 (not_acceptsSpace_of_not_det hdet)⟩

end DetToNondet

/-- **Deterministic space-bounded acceptance reduces to the nondeterministic
problem.** The interpretation is the identity, save that the image only keeps
its accepting states when the source table is deterministic – a first-order
condition, so the promise folded into the yes-instances of
`DescriptiveComplexity.DTMAcceptSpace` is enforced by the reduction itself. -/
noncomputable def dtmAcceptSpace_fo_reduction_ntmAcceptSpace :
    DTMAcceptSpace ≤ᶠᵒ NTMAcceptSpace where
  Tag := Unit
  dim := 1
  toInterpretation := DetToNondet.detInterp
  correct := DetToNondet.correct

end DescriptiveComplexity
