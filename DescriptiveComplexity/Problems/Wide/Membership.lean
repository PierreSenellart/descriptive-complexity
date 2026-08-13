/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Expansion
import DescriptiveComplexity.Exponential.Classes
import DescriptiveComplexity.Problems.Machine
import DescriptiveComplexity.Problems.Machine.Space

/-!
# The wide machines are members of the exponential classes

The payoff of `DescriptiveComplexity.Problems.Wide.Expansion`: the expansion's
points **are** the universe of the wide machine
(`DescriptiveComplexity.Wide.wideEquiv`), so the machine an instance describes
and the machine the expanded structure describes agree fieldwise
(`DescriptiveComplexity.Wide.wideAgree`) and the three wide problems are exactly
the three ordinary machine problems read over the expansion. With
`DescriptiveComplexity.ntmAccept_mem_NP` and
`DescriptiveComplexity.ntmAcceptSpace_mem_PSPACE` that gives

* `DescriptiveComplexity.wideAccept_mem_NEXPTIME` – `NEXPTIME := NP.exp`, so
  this is the definition being exercised;
* `DescriptiveComplexity.wideAcceptSpace_mem_EXPSPACE` and its deterministic
  variant, through `DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`.

No resource argument appears anywhere: the exponent is in the *universe* the
machine runs over, and everything else is the composition that
`DescriptiveComplexity.ExpDefinable` is made of – an expansion applied after the
problem, which is the composition that exists.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace Wide

section Embed

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]

/-- An address satisfies the domain sentence of its tag, which is `⊤`. -/
theorem domHolds_addr (s : A → Prop) :
    ExpExpansion.DomHolds (X := wideExp) (WTag.addr, wassign s) := by
  letI := wideExp.B.structure₁ (L := wOrd) (wassign s)
  exact Formula.realize_top.mpr trivial

/-- The singleton address of an element satisfies the domain sentence of the
control tag. -/
theorem domHolds_ctrl (x : A) :
    ExpExpansion.DomHolds (X := wideExp) (WTag.ctrl, wassign fun y => y = x) :=
  (realize_singleS _).mpr (wmSingle_eq x)

/-- **The universe of the wide machine sits inside the expansion**: an address
becomes the point tagged `addr` carrying it, a control element the point tagged
`ctrl` carrying its singleton. -/
noncomputable def wideEmbed : WPoint A → wideExp.Map A
  | Sum.inl s => ⟨(WTag.addr, wassign s), domHolds_addr s⟩
  | Sum.inr x => ⟨(WTag.ctrl, wassign fun y => y = x), domHolds_ctrl x⟩

@[simp]
theorem wideEmbed_addr_tag (s : A → Prop) : (wideEmbed (Sum.inl s) : wideExp.Map A).1.1 =
    WTag.addr :=
  rfl

@[simp]
theorem wideEmbed_ctrl_tag (x : A) : (wideEmbed (Sum.inr x) : wideExp.Map A).1.1 =
    WTag.ctrl :=
  rfl

/-- **The embedding is onto the whole expanded universe**: every point tagged
`addr` is an address, and every point tagged `ctrl` is a control element,
because its domain sentence made its assignment a singleton. -/
theorem wideEmbed_bijective : Function.Bijective (wideEmbed (A := A)) := by
  constructor
  · rintro (s | x) (t | y) h
    · have h1 : wassign s = wassign t := congrArg (fun p => p.1.2) h
      exact congrArg Sum.inl (by
        rw [← wbits_wassign s, ← wbits_wassign t, h1])
    · exact absurd (congrArg (fun p => p.1.1) h) (by simp)
    · exact absurd (congrArg (fun p => p.1.1) h) (by simp)
    · have h1 : (fun z => z = x) = fun z => z = y := by
        rw [← wbits_wassign fun z => z = x, ← wbits_wassign fun z => z = y]
        exact congrArg wbits (congrArg (fun p => p.1.2) h)
      exact congrArg Sum.inr (by simpa using congrFun h1 x)
  · rintro ⟨⟨t, ρ⟩, hdom⟩
    match t with
    | WTag.addr => exact ⟨Sum.inl (wbits ρ), ExpExpansion.map_ext rfl (wassign_wbits ρ)⟩
    | WTag.ctrl =>
      obtain ⟨x, hx⟩ := exists_eq_of_wmSingle ((realize_singleS ρ).mp hdom)
      have h1 : (wassign fun z => z = x) = ρ := by
        rw [show (fun z => z = x) = wbits ρ from (funext fun z => propext (hx z)).symm]
        exact wassign_wbits ρ
      exact ⟨Sum.inr x, ExpExpansion.map_ext rfl h1⟩

/-- **The points of the expansion are the universe of the wide machine.** -/
noncomputable def wideEquiv : WPoint A ≃ wideExp.Map A :=
  Equiv.ofBijective _ wideEmbed_bijective

@[simp]
theorem wideEquiv_apply (p : WPoint A) : wideEquiv p = wideEmbed p := rfl

end Embed

/-! ### The twelve symbols

Each defining sentence is read at the points the embedding produces, and turns
out to be the corresponding field of `DescriptiveComplexity.wideData`. The two
generic lemmas do the bookkeeping – the tag match and the passage from the
replicated block to one or two stacked copies – once for all. -/

section Symbols

variable {A : Type} [Language.wide.Structure A] [LinearOrder A]

/-- Reading a unary symbol of the expanded vocabulary at one point. -/
theorem realize_one (rt : Language.turing.Relations 1) (φ : WTag → wide1.Sentence)
    (h : ∀ τ : Fin 1 → wideExp.Tag, wideExp.relSentence rt τ = onS1 (φ (τ 0)))
    (x : wideExp.Map A) :
    letI := wideStructure A
    (RelMap rt ![x] ↔
      @Sentence.Realize wide1 A (addrBlock.structure₁ (L := wOrd) x.1.2) (φ x.1.1)) := by
  letI := wideStructure A
  have h1 := wideExp.relMap_map rt ![x]
  rw [h] at h1
  exact h1.trans (realize_onS1 _ x)

/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : Language.turing.Relations 2) (φ : WTag → WTag → wide2.Sentence)
    (h : ∀ τ : Fin 2 → wideExp.Tag, wideExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : wideExp.Map A) :
    letI := wideStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) x.1.2 y.1.2)
        (φ x.1.1 y.1.1)) := by
  letI := wideStructure A
  have h1 := wideExp.relMap_map rt ![x, y]
  rw [h] at h1
  exact h1.trans (realize_onS2 _ x y)

/-- **The positions of the expanded machine are the addresses.** -/
theorem relMap_posn (p : WPoint A) :
    letI := wideStructure A
    (RelMap tmPosn ![wideEmbed p] ↔ (wideData A).Posn p) := by
  letI := wideStructure A
  rw [realize_one tmPosn posnT (fun _ => rfl) (wideEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_true (realize_topS _) trivial
  | Sum.inr x => exact iff_of_false (not_realize_botS _) (fun h => h)

/-- **A mark of the expanded machine is the corresponding mark of the
instance**, carried by the control elements alone. -/
theorem relMap_mark (rt : Language.turing.Relations 1) (r : Language.wide.Relations 1)
    (h : ∀ τ : Fin 1 → wideExp.Tag, wideExp.relSentence rt τ = onS1 (markT r (τ 0)))
    (p : WPoint A) :
    letI := wideStructure A
    (RelMap rt ![wideEmbed p] ↔ wpMark (fun x => RelMap r ![x]) p) := by
  letI := wideStructure A
  rw [realize_one rt (markT r) h (wideEmbed p)]
  match p with
  | Sum.inl s => exact iff_of_false (not_realize_botS _) (fun h => h)
  | Sum.inr x =>
    refine (realize_markS r _).trans ?_
    exact ⟨fun ⟨z, hz, hr⟩ => hz ▸ hr, fun hr => ⟨x, rfl, hr⟩⟩

/-- **A binary attribute of the expanded machine is the corresponding attribute
of the instance**, holding of control elements alone. -/
theorem relMap_attr (rt : Language.turing.Relations 2) (r : Language.wide.Relations 2)
    (h : ∀ τ : Fin 2 → wideExp.Tag, wideExp.relSentence rt τ = onS2 (binT r (τ 0) (τ 1)))
    (p q : WPoint A) :
    letI := wideStructure A
    (RelMap rt ![wideEmbed p, wideEmbed q] ↔ wpAttr (fun x y => RelMap r ![x, y]) p q) := by
  letI := wideStructure A
  rw [realize_two rt (binT r) h (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS r _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The order of the expanded machine**: addresses in the binary-number order
the instance's own order induces, then the control elements in that order. -/
theorem relMap_le (p q : WPoint A) :
    letI := wideStructure A
    (RelMap tmLe ![wideEmbed p, wideEmbed q] ↔ (wideData A).Le p q) := by
  letI := wideStructure A
  rw [realize_two tmLe leT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact realize_addrLeS _ _
  | Sum.inl s, Sum.inr y => exact iff_of_true (realize_topS₂ _ _) trivial
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y =>
    refine (realize_binS wmLe _ _).trans ?_
    exact ⟨fun ⟨a, b, ha, hb, hr⟩ => ha ▸ hb ▸ hr, fun hr => ⟨x, y, rfl, rfl, hr⟩⟩

/-- **The initial tape of the expanded machine**: the address cutting the
initial segment of an element holds that element's input symbol. -/
theorem relMap_inp (p q : WPoint A) :
    letI := wideStructure A
    (RelMap tmInp ![wideEmbed p, wideEmbed q] ↔ (wideData A).Inp p q) := by
  letI := wideStructure A
  rw [realize_two tmInp inpT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_inpS _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)

end Symbols

/-! ### The two machines agree -/

section Agree

variable (A : Type) [Language.wide.Structure A] [LinearOrder A]

/-- **The wide machine of the instance is the ordinary machine of the
expansion**, fieldwise along `DescriptiveComplexity.Wide.wideEquiv`. -/
theorem wideAgree :
    letI := wideStructure A
    TMData.Agree (wideEquiv (A := A)) (wideData A) (tmData (wideExp.Map A)) := by
  letI := wideStructure A
  exact ⟨fun p => (relMap_posn p).symm, fun p q => (relMap_le p q).symm,
    fun p => (relMap_mark tmTr wmTr (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmStart wmStart (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmAcc wmAcc (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmBlank wmBlank (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmRight wmRight (fun _ => rfl) p).symm,
    fun p q => (relMap_attr tmSrc wmSrc (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmRead wmRead (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmDst wmDst (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmWrite wmWrite (fun _ => rfl) p q).symm,
    fun p q => (relMap_inp p q).symm⟩

end Agree

end Wide

/-! ### The memberships -/

section Membership

open Wide

/-- **The wide machine is the ordinary machine of the expansion**: acceptance of
the one is acceptance of the other. -/
theorem wideAccept_iff_expansion (A : Type) [Language.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (WideAccept A ↔ NTMAccept (wideExp.Map A)) := by
  letI := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed h.accepts

/-- The space-bounded version of `DescriptiveComplexity.wideAccept_iff_expansion`. -/
theorem wideAcceptSpace_iff_expansion (A : Type) [Language.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (WideAcceptSpace A ↔ NTMAcceptSpace (wideExp.Map A)) := by
  letI := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed h.acceptsSpace

/-- The deterministic space-bounded version of
`DescriptiveComplexity.wideAccept_iff_expansion`. -/
theorem dwideAcceptSpace_iff_expansion (A : Type) [Language.wide.Structure A] [LinearOrder A] :
    letI := wideStructure A
    (DWideAcceptSpace A ↔ DTMAcceptSpace (wideExp.Map A)) := by
  letI := wideStructure A
  have h := wideAgree A
  exact and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)

/-- **The wide machine is in NEXPTIME**, which is `NP.exp`: the expansion turns
it into `DescriptiveComplexity.NTMAccept`, and that problem is in NP. This is
the first natural member the class has. -/
theorem wideAccept_mem_NEXPTIME : WideAccept ∈ NEXPTIME := by
  letI hinst : ∀ (A : Type) [Language.wide.Structure A] [LinearOrder A],
      Language.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  refine ⟨wideExp, NTMAccept, ntmAccept_mem_NP, ?_⟩
  intro A _ _ _ _
  exact wideAccept_iff_expansion A

/-- **The space-bounded wide machine is in EXPSPACE**: the expansion turns it
into `DescriptiveComplexity.NTMAcceptSpace`, and that problem is in PSPACE. -/
theorem wideAcceptSpace_mem_EXPSPACE : WideAcceptSpace ∈ EXPSPACE := by
  letI hinst : ∀ (A : Type) [Language.wide.Structure A] [LinearOrder A],
      Language.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wideExp, NTMAcceptSpace, ntmAcceptSpace_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact wideAcceptSpace_iff_expansion A

/-- **The deterministic space-bounded wide machine is in EXPSPACE**, through
`DescriptiveComplexity.DTMAcceptSpace`. -/
theorem dwideAcceptSpace_mem_EXPSPACE : DWideAcceptSpace ∈ EXPSPACE := by
  letI hinst : ∀ (A : Type) [Language.wide.Structure A] [LinearOrder A],
      Language.turing.Structure (wideExp.Map A) := fun A => wideStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wideExp, DTMAcceptSpace, dtmAcceptSpace_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact dwideAcceptSpace_iff_expansion A

end Membership

end DescriptiveComplexity
