/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RelExpansion

/-!
# The relativized expansion over the doubled universe is the expansion

The point of `DescriptiveComplexity.Draw.relExp`, discharged: over the doubled
universe of `DescriptiveComplexity.Draw.dblInterp` its points are the original
expansion's points over the instance, and its relations are the original's
(`DescriptiveComplexity.Draw.relExpMapEquiv`).

Three things make that work, and each was arranged for it. A doubled universe
always has a marked part, so the fallback tag contributes no point. A point's
assignment is *supported*, so it is the extension of a unique assignment of the
instance. And every sentence the expansion is made of transports by
`DescriptiveComplexity.Draw.realize_relOldBlock` – the domain sentence at one copy
of the block, and each defining sentence at `n` copies, where the extension
commutes with replication exactly.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

section MapEquiv

variable {L : Language.{0, 0}} [L.IsRelational] {X : ExpExpansion L}
variable {A : Type} [L.Structure A] [LinearOrder A] [Nonempty A]

omit [L.IsRelational] [L.Structure A] [LinearOrder A] [Nonempty A] in
/-- **Extending commutes with replication**, exactly: the index type of a
replicated block is a plain product and the extension acts coordinate by
coordinate. -/
theorem extAssign_replicateAssign {n : ℕ} (ρs : Fin n → X.B.Assignment A) :
    extAssign (L := L) (B := X.B.replicate n) (X.B.replicateAssign ρs) =
      X.B.replicateAssign fun i => extAssign (ρs i) := rfl

/-- The fallback tag contributes no point over a doubled universe: there is
always a marked element. -/
theorem not_domHolds_none (ρ : X.B.Assignment ((dblInterp L).Map A)) :
    ¬ExpExpansion.DomHolds (X := relExp X)
      ((none, ρ) : (relExp X).Point ((dblInterp L).Map A)) := by
  intro h
  letI := (relExp X).B.structure₁ (L := (newLang L).sum Language.order) ρ
  have h1 := (Formula.realize_inf.mp h).1
  have h2 := (realize_noOldSentence (L := L) ρ).mp h1
  exact h2 (dblPt false (Classical.arbitrary A))
    ((relMap_dbl_old (L := L) _).mpr rfl)

omit [Nonempty A] in
/-- **A point's assignment is supported**: that is what the domain sentence's
second conjunct says. -/
theorem supported_of_domHolds {t : X.Tag} {ρ : X.B.Assignment ((dblInterp L).Map A)}
    (h : ExpExpansion.DomHolds (X := relExp X)
      ((some t, ρ) : (relExp X).Point ((dblInterp L).Map A))) : Supported ρ := by
  letI := (relExp X).B.structure₁ (L := (newLang L).sum Language.order) ρ
  intro i w hw j
  exact (relMap_dbl_old (L := L) _).mp
    ((realize_suppSentence X.B ρ).mp (Formula.realize_inf.mp h).2 i w hw j)

omit [Nonempty A] in
/-- **A point of the relativized expansion is a point of the expansion**, at the
extended assignment. -/
theorem domHolds_relExp_iff (t : X.Tag) (ρ₀ : X.B.Assignment A) :
    ExpExpansion.DomHolds (X := relExp X)
        ((some t, extAssign ρ₀) : (relExp X).Point ((dblInterp L).Map A)) ↔
      ExpExpansion.DomHolds (X := X) ((t, ρ₀) : X.Point A) := by
  letI := (relExp X).B.structure₁ (L := (newLang L).sum Language.order)
    (extAssign (L := L) ρ₀)
  constructor
  · intro h
    exact (realize_relOldBlock ρ₀ (X.dom t)).mp (Formula.realize_inf.mp h).1
  · intro h
    refine Formula.realize_inf.mpr ⟨(realize_relOldBlock ρ₀ (X.dom t)).mpr h, ?_⟩
    refine (realize_suppSentence X.B (extAssign ρ₀)).mpr fun i w hw j => ?_
    exact (relMap_dbl_old (L := L) _).mpr (hw.1 j)

/-- **A point of the expansion, as a point of the relativized expansion over the
doubled universe.** -/
noncomputable def toRelExpPt (p : X.Map A) : (relExp X).Map ((dblInterp L).Map A) :=
  ⟨(some p.1.1, extAssign p.1.2), (domHolds_relExp_iff p.1.1 p.1.2).mpr p.2⟩

omit [Nonempty A] in
theorem toRelExpPt_injective : Function.Injective (toRelExpPt (X := X) (A := A)) := by
  intro p q h
  have h1 : some p.1.1 = some q.1.1 := congrArg (fun x => x.1.1) h
  have h2 : extAssign (L := L) p.1.2 = extAssign q.1.2 := congrArg (fun x => x.1.2) h
  refine ExpExpansion.map_ext (Option.some.inj h1) ?_
  rw [← resAssign_extAssign (L := L) p.1.2, ← resAssign_extAssign (L := L) q.1.2, h2]

theorem toRelExpPt_surjective : Function.Surjective (toRelExpPt (X := X) (A := A)) := by
  rintro ⟨⟨t, ρ⟩, h⟩
  match t with
  | none => exact absurd h (not_domHolds_none (X := X) ρ)
  | some t =>
    have hsupp : Supported ρ := supported_of_domHolds h
    obtain ⟨ρ₀, rfl⟩ : ∃ ρ₀, ρ = extAssign ρ₀ :=
      ⟨resAssign ρ, (extAssign_resAssign hsupp).symm⟩
    exact ⟨⟨(t, ρ₀), (domHolds_relExp_iff t ρ₀).mp h⟩, rfl⟩

/-- **The relativized expansion over the doubled universe is the expansion over
the instance**: the same points, the same relations. -/
noncomputable def relExpMapEquiv :
    @Language.Equiv X.E (X.Map A) ((relExp X).Map ((dblInterp L).Map A))
      (ExpExpansion.mapStructure X A)
      (ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)) :=
  letI : X.E.Structure ((relExp X).Map ((dblInterp L).Map A)) :=
    ExpExpansion.mapStructure (relExp X) ((dblInterp L).Map A)
  { toEquiv := Equiv.ofBijective _ ⟨toRelExpPt_injective, toRelExpPt_surjective⟩
    map_fun' := fun {_} f _ => isEmptyElim f
    map_rel' := fun {n} r x => by
      classical
      have hex : ∃ σ : Fin n → X.Tag, ∀ i, (some (x i).1.1 : Option X.Tag) = some (σ i) :=
        ⟨fun i => (x i).1.1, fun _ => rfl⟩
      have hchoose : hex.choose = fun i => (x i).1.1 :=
        funext fun i => (Option.some.inj (hex.choose_spec i)).symm
      have hrel : (relExp X).relSentence r (fun i => (some (x i).1.1 : Option X.Tag)) =
          relativizeTo (oldGuard (L := L) (X.B.replicate n))
            ((newBlockLHom (X.B.replicate n)).onSentence
            (X.relSentence r fun i => (x i).1.1)) := by
        rw [show (relExp X).relSentence r (fun i => (some (x i).1.1 : Option X.Tag)) =
          dite (∃ σ : Fin n → X.Tag, ∀ i, (some (x i).1.1 : Option X.Tag) = some (σ i))
            (fun h => relativizeTo (oldGuard (L := L) (X.B.replicate n))
              ((newBlockLHom (X.B.replicate n)).onSentence (X.relSentence r h.choose)))
            (fun _ => ⊥) from rfl, dif_pos hex, hchoose]
      change @Sentence.Realize _ ((dblInterp L).Map A)
        ((X.B.replicate n).structure₁ (X.B.replicateAssign fun i => extAssign (x i).1.2))
        ((relExp X).relSentence r (fun i => (some (x i).1.1 : Option X.Tag))) ↔ _
      rw [hrel, ← extAssign_replicateAssign (X := X) fun i => (x i).1.2]
      exact realize_relOldBlock (X.B.replicateAssign fun i => (x i).1.2)
        (X.relSentence r fun i => (x i).1.1) }

end MapEquiv

end Draw

end DescriptiveComplexity
