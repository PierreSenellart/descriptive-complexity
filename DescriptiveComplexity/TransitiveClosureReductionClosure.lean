/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureSentenceDecide
import DescriptiveComplexity.TransitiveClosureParamPull
import DescriptiveComplexity.TransitiveClosureReductionComposition
import DescriptiveComplexity.DetLogSpace

/-!
# NL is closed under FO(TC) reductions, and LOGSPACE under FO(DTC) reductions

The two closure theorems the reductions with a logic inside were missing:

* `DescriptiveComplexity.mem_NL_of_tcReduction` – **NL is closed under
  `≤ᵗᶜ`**, so `≤ᵗᶜ` is the reduction notion of NL as `≤ˡᶠᵖ` is that of PTIME;
* `DescriptiveComplexity.mem_LOGSPACE_of_dtcReduction` – **LOGSPACE is closed
  under `≤ᵈᵗᶜ`**, the many-one logarithmic-space reduction of the textbooks.

Both are Immerman's normal form, in the walk-algebra form of
`DescriptiveComplexity.TransitiveClosureDecide`. Given `P ≤ᵗᶜ Q` and a walk
deciding `Q`, the walk is pulled back through the reduction's interpretation
(`DescriptiveComplexity.TCSpec.pullSpec`, the sentence-level reading of
`DescriptiveComplexity.ParamTCSpec.comapRel`): a walk over the base structure
*expanded by the reachability relations of the reduction's own walks*. Its
step, source and target formulas read those relations, and every such
formula has a decider (`DescriptiveComplexity.Decider.exists_of_formula`, the
atoms being `DescriptiveComplexity.ParamTCSpec.reachDecider`); the walk is
flattened (`DescriptiveComplexity.ParamTCSpec.flat`) and the sentence
“some source reaches some target” is one decider
(`DescriptiveComplexity.ParamTCSpec.sentenceDecider`), hence one
`DescriptiveComplexity.TCSpec` – FO(TC) definability of `P`, which is
membership in NL (`DescriptiveComplexity.tcDefinable_iff_mem_NL`).

The deterministic case runs the same assembly with the deterministic atoms
(`DescriptiveComplexity.ParamTCSpec.detReachDecider`), the searching flat
walk, and the deterministic reading of everything: each construction is
functional, so the resulting specification is unchanged by determinization
(`DescriptiveComplexity.Decider.det_accepts_toSpec`), which is FO(DTC)
definability. The searching flat walk simulates the outer walk only when that
one is functional – which the pullback of a determinized walk is
(`DescriptiveComplexity.TCSpec.pullSpec_functional`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Transport along an isomorphism, with explicit structures -/

section Transport

variable {L'' : Language.{0, 0}} {M N : Type} {instM : L''.Structure M} {instN : L''.Structure N}
  (e : @Language.Equiv L'' M N instM instN)

/-- A step of a parameterized walk transports along an isomorphism. -/
theorem ParamTCSpec.stepAt_of_equiv (s : ParamTCSpec L'') (z : Fin s.par → M) (a b : s.Node M) :
    @ParamTCSpec.StepAt L'' s N instN (e ∘ z) (a.1, e ∘ a.2) (b.1, e ∘ b.2) ↔
      @ParamTCSpec.StepAt L'' s M instM z a b := by
  change @Formula.Realize L'' N instN _ (s.step a.1 b.1) (Sum.elim (Sum.elim (e ∘ a.2) (e ∘ b.2))
    (e ∘ z)) ↔ @Formula.Realize L'' M instM _ (s.step a.1 b.1) (Sum.elim (Sum.elim a.2 b.2) z)
  rw [← realize_formula_of_equiv e]
  refine iff_of_eq (congrArg (@Formula.Realize L'' N instN _ (s.step a.1 b.1))
    (funext fun i => ?_))
  rcases i with (i | i) | i <;> rfl

/-- Reachability in a parameterized walk transports along an isomorphism. -/
theorem ParamTCSpec.reachAt_of_equiv (s : ParamTCSpec L'') (z : Fin s.par → M) (a b : s.Node M) :
    @ParamTCSpec.ReachAt L'' s N instN (e ∘ z) (a.1, e ∘ a.2) (b.1, e ∘ b.2) ↔
      @ParamTCSpec.ReachAt L'' s M instM z a b := by
  constructor
  · intro h
    have key : ∀ c d : s.Node N, @ParamTCSpec.ReachAt L'' s N instN (e ∘ z) c d →
        @ParamTCSpec.ReachAt L'' s M instM z (c.1, e.symm ∘ c.2) (d.1, e.symm ∘ d.2) := by
      intro c d hcd
      refine Relation.ReflTransGen.lift (fun f : s.Node N => (f.1, e.symm ∘ f.2))
        (fun f f' hff' => ?_) _ _ hcd
      change @ParamTCSpec.StepAt L'' s M instM z (f.1, e.symm ∘ f.2) (f'.1, e.symm ∘ f'.2)
      rw [← ParamTCSpec.stepAt_of_equiv e s z]
      convert hff' using 2 <;> funext i <;> simp
    have := key _ _ h
    simpa [Function.comp_def] using this
  · intro h
    refine Relation.ReflTransGen.lift (fun f : s.Node M => (f.1, e ∘ f.2)) (fun f f' hff' => ?_)
      _ _ h
    exact (ParamTCSpec.stepAt_of_equiv e s z f f').mpr hff'

end Transport

/-! ### The pullback of a sentence through a relativized ordered interpretation -/

namespace TCSpec

variable {L₁ L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag] {dim : ℕ}
variable (spec : TCSpec L') (J : RelFOInterpretation L₁ (L'.sum Language.order) Tag dim)

/-- **The pullback of a specification's walk** through a relativized ordered
interpretation. -/
@[reducible]
noncomputable def pullSpec : ParamTCSpec L₁ :=
  spec.toParam.comapRel J Fin.elim0

/-- The pulled source formula: the tuple is in the domain and encodes a
source. -/
noncomputable def pullSrc (m : (spec.pullSpec J).Mode) : L₁.Formula (Fin (spec.pullSpec J).k) :=
  (J.pullRelF (spec.src m.1) m.2).relabel (fun p => ParamTCSpec.coordIx dim p.1 p.2) ⊓
    ParamTCSpec.domTupleF J m.2

/-- The pulled target formula. -/
noncomputable def pullTgt (m : (spec.pullSpec J).Mode) : L₁.Formula (Fin (spec.pullSpec J).k) :=
  (J.pullRelF (spec.tgt m.1) m.2).relabel (fun p => ParamTCSpec.coordIx dim p.1 p.2) ⊓
    ParamTCSpec.domTupleF J m.2

variable {A : Type} [L₁.Structure A]

/-- The valuation of the (absent) parameters of the pulled walk. -/
abbrev pullPar (A : Type) : Fin (spec.pullSpec J).par → A :=
  fun i => (Fin.cast (Nat.zero_mul dim) i).elim0

theorem realize_pullSrc (a : (spec.pullSpec J).Node A) :
    (spec.pullSrc J a.1).Realize a.2 ↔
      ∃ ha : ParamTCSpec.InDom a,
        (@Formula.Realize _ (J.MapRel A) (RelFOInterpretation.mapRelStructure J A) _
          (spec.src a.1.1) (ParamTCSpec.decode a ha).2) := by
  have h1 : (spec.pullSrc J a.1).Realize a.2 ↔
      ((J.pullRelF (spec.src a.1.1) a.1.2).relabel
        (fun p => ParamTCSpec.coordIx dim p.1 p.2)).Realize a.2 ∧
        (ParamTCSpec.domTupleF J a.1.2).Realize a.2 :=
    Formula.realize_inf
  have h2 : ((J.pullRelF (spec.src a.1.1) a.1.2).relabel
      (fun p => ParamTCSpec.coordIx dim p.1 p.2)).Realize a.2 ↔
      (J.pullRelF (spec.src a.1.1) a.1.2).Realize
        (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) :=
    Formula.realize_relabel
  have h3 : (ParamTCSpec.domTupleF J a.1.2).Realize a.2 ↔ ParamTCSpec.InDom a :=
    ParamTCSpec.realize_domTupleF J a.1.2 a.2
  rw [h1, h2, h3]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (J.realize_pullRelF (spec.src a.1.1) a.1.2
      (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) h2).mp h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨(J.realize_pullRelF (spec.src a.1.1) a.1.2
      (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) h2).mpr h1, h2⟩

theorem realize_pullTgt (a : (spec.pullSpec J).Node A) :
    (spec.pullTgt J a.1).Realize a.2 ↔
      ∃ ha : ParamTCSpec.InDom a,
        (@Formula.Realize _ (J.MapRel A) (RelFOInterpretation.mapRelStructure J A) _
          (spec.tgt a.1.1) (ParamTCSpec.decode a ha).2) := by
  have h1 : (spec.pullTgt J a.1).Realize a.2 ↔
      ((J.pullRelF (spec.tgt a.1.1) a.1.2).relabel
        (fun p => ParamTCSpec.coordIx dim p.1 p.2)).Realize a.2 ∧
        (ParamTCSpec.domTupleF J a.1.2).Realize a.2 :=
    Formula.realize_inf
  have h2 : ((J.pullRelF (spec.tgt a.1.1) a.1.2).relabel
      (fun p => ParamTCSpec.coordIx dim p.1 p.2)).Realize a.2 ↔
      (J.pullRelF (spec.tgt a.1.1) a.1.2).Realize
        (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) :=
    Formula.realize_relabel
  have h3 : (ParamTCSpec.domTupleF J a.1.2).Realize a.2 ↔ ParamTCSpec.InDom a :=
    ParamTCSpec.realize_domTupleF J a.1.2 a.2
  rw [h1, h2, h3]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (J.realize_pullRelF (spec.tgt a.1.1) a.1.2
      (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) h2).mp h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨(J.realize_pullRelF (spec.tgt a.1.1) a.1.2
      (a.2 ∘ fun p => ParamTCSpec.coordIx dim p.1 p.2) h2).mpr h1, h2⟩

/-- Decoding then encoding is the identity on in-domain nodes. -/
theorem encode_decode (a : (spec.pullSpec J).Node A) (ha : ParamTCSpec.InDom a) :
    ParamTCSpec.encode Fin.elim0 (ParamTCSpec.decode a ha) = a := by
  refine Prod.ext (Prod.ext rfl rfl) (funext fun m => ?_)
  change a.2 (ParamTCSpec.coordIx dim (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) =
    a.2 m
  refine congrArg a.2 ?_
  simp only [ParamTCSpec.coordIx, Prod.mk.eta]
  exact Equiv.apply_symm_apply _ _

variable (A) in
/-- **The pulled sentence**: some pulled source reaches some pulled target. -/
def PulledAccepts : Prop :=
  ∃ a b : (spec.pullSpec J).Node A, (spec.pullSrc J a.1).Realize a.2 ∧
    (spec.pullTgt J b.1).Realize b.2 ∧ (spec.pullSpec J).ReachAt (spec.pullPar J A) a b

/-- **The pulled sentence says what the original says on the interpreted
structure**, read with the interpretation's own structure. -/
theorem pulledAccepts_iff :
    spec.PulledAccepts J A ↔
      ∃ u v : spec.Node (J.MapRel A),
        (@Formula.Realize _ (J.MapRel A) (RelFOInterpretation.mapRelStructure J A) _
          (spec.src u.1) u.2) ∧
        (@Formula.Realize _ (J.MapRel A) (RelFOInterpretation.mapRelStructure J A) _
          (spec.tgt v.1) v.2) ∧
        @ParamTCSpec.ReachAt _ spec.toParam (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
          (fun i => i.elim0) u v := by
  have hz : ParamTCSpec.ParInDom J (s := spec.toParam) Fin.elim0 (spec.pullPar J A) :=
    fun i => i.elim0
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨ha', hsrc⟩ := (spec.realize_pullSrc J a).mp ha
    obtain ⟨hb', htgt⟩ := (spec.realize_pullTgt J b).mp hb
    refine ⟨ParamTCSpec.decode a ha', ParamTCSpec.decode b hb', hsrc, htgt, ?_⟩
    have := (ParamTCSpec.reachAt_comapRel_iff (s := spec.toParam) (I := J) ha' hb' hz).mp hab
    rwa [Subsingleton.elim (fun i : Fin 0 => i.elim0) (ParamTCSpec.decodePar hz)]
  · rintro ⟨u, v, hu, hv, huv⟩
    refine ⟨ParamTCSpec.encode (s := spec.toParam) (I := J) Fin.elim0 u,
      ParamTCSpec.encode (s := spec.toParam) (I := J) Fin.elim0 v, ?_, ?_, ?_⟩
    · refine (spec.realize_pullSrc J _).mpr
        ⟨ParamTCSpec.inDom_encode (s := spec.toParam) (I := J) Fin.elim0 u, ?_⟩
      rw [ParamTCSpec.decode_encode]
      exact hu
    · refine (spec.realize_pullTgt J _).mpr
        ⟨ParamTCSpec.inDom_encode (s := spec.toParam) (I := J) Fin.elim0 v, ?_⟩
      rw [ParamTCSpec.decode_encode]
      exact hv
    · refine ParamTCSpec.reachAt_comapRel_backward (s := spec.toParam) (I := J) hz ?_
      rwa [Subsingleton.elim (ParamTCSpec.decodePar hz) (fun i : Fin 0 => i.elim0)]

/-- **The pullback of a functional walk is functional**: steps correspond
between in-domain nodes, and out-of-domain nodes have none. -/
theorem pullSpec_functional
    (h : ∀ u v w : spec.Node (J.MapRel A),
      @ParamTCSpec.StepAt _ spec.toParam (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
        (fun i => i.elim0) u v →
      @ParamTCSpec.StepAt _ spec.toParam (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
        (fun i => i.elim0) u w → v = w)
    (z : Fin (spec.pullSpec J).par → A) (a b c : (spec.pullSpec J).Node A)
    (hb : (spec.pullSpec J).StepAt z a b) (hc : (spec.pullSpec J).StepAt z a c) : b = c := by
  obtain ⟨ha, hb', hz, hsb⟩ := (ParamTCSpec.stepAt_comapRel_iff a b).mp hb
  obtain ⟨ha₂, hc', hz₂, hsc⟩ := (ParamTCSpec.stepAt_comapRel_iff a c).mp hc
  rw [Subsingleton.elim (ParamTCSpec.decodePar hz) (fun i : Fin 0 => i.elim0)] at hsb
  rw [Subsingleton.elim (ParamTCSpec.decodePar hz₂) (fun i : Fin 0 => i.elim0)] at hsc
  have := h _ _ _ hsb hsc
  rw [← spec.encode_decode J b hb', ← spec.encode_decode J c hc', this]

end TCSpec

/-! ### The sentence on the interpreted structure, pulled back -/

section Interp

variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag] [LinearOrder Tag]
  {dim : ℕ} (I : TCInterpretation (L.sum Language.order) L' Tag dim) (spec : TCSpec L')
  (A : Type) [L.Structure A] [LinearOrder A]

/-- The reduction's interpretation, extended by the lexicographic order. -/
noncomputable abbrev TCInterpretation.ordInterp :
    RelFOInterpretation ((L.sum Language.order).sum I.fam.block.lang) (L'.sum Language.order)
      Tag dim :=
  I.toRel.ordExtendSrc LHom.sumInl

/-- **Acceptance on the interpreted structure is the pulled sentence** on
the base structure expanded by the reduction's walks. -/
theorem TCInterpretation.accepts_iff_pulled :
    (letI := I.mapLinearOrder A; spec.Accepts (I.Map A)) ↔
      (letI := I.expStructure A; spec.PulledAccepts I.ordInterp A) := by
  let := I.expStructure A
  let := I.mapLinearOrder A
  let e := I.toRel.ordExtendSrcLEquiv LHom.sumInl (I.expStructure A)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [TCSpec.pulledAccepts_iff]
  refine exists_congr fun u => exists_congr fun v => and_congr ?_ (and_congr ?_ ?_)
  · exact realize_formula_of_equiv e (spec.src u.1) u.2
  · exact realize_formula_of_equiv e (spec.tgt v.1) v.2
  · rw [← spec.reachAt_toParam (fun i => i.elim0) u v]
    exact ParamTCSpec.reachAt_of_equiv e spec.toParam (fun i => i.elim0) u v

end Interp

/-! ### Closure of FO(TC) definability -/

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L}
  {Q : DecisionProblem L'}

/-- A bottom element of a finite nonempty linear order. -/
theorem exists_bot (A : Type) [LinearOrder A] [Finite A] [Nonempty A] : ∃ a₀ : A, ∀ a, a₀ ≤ a := by
  obtain ⟨a₀, -, h⟩ := (Finite.to_wellFoundedLT (α := A)).wf.has_min Set.univ
    ⟨Classical.arbitrary A, Set.mem_univ _⟩
  exact ⟨a₀, fun a => not_lt.mp (h a (Set.mem_univ a))⟩

/-- **FO(TC) definability is closed under FO(TC) reductions**: the normal
form. -/
theorem TCDefinable.of_tcReduction (f : P ≤ᵗᶜ Q) (h : TCDefinable Q) : TCDefinable P := by
  classical
  obtain ⟨spec, hspec⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  set I := f.toInterpretation
  set S := spec.pullSpec I.ordInterp
  -- the deciders of the reduction's own walks
  have hD := I.fam.decides_reachDeciders
  -- the deciders of the pulled step, source and target formulas
  choose Dstep hstep using fun m n => Decider.exists_of_formula₀ (fun A _ _ => I.fam.reachAssign A)
    I.fam.reachDeciders hD (S.step m n)
  choose Dsrc hsrc using fun m => Decider.exists_of_formula₀ (fun A _ _ => I.fam.reachAssign A)
    I.fam.reachDeciders hD (spec.pullSrc I.ordInterp m)
  choose Dtgt htgt using fun m => Decider.exists_of_formula₀ (fun A _ _ => I.fam.reachAssign A)
    I.fam.reachDeciders hD (spec.pullTgt I.ordInterp m)
  let Dr := fun m n => (S.flat Dstep false).toParam.reachDecider (Sum.inl m) (Sum.inl n)
  let toEmpty : Fin S.par → Empty := fun i => (Fin.cast (Nat.zero_mul _) i).elim0
  refine ⟨((S.sentenceDecider Dstep false Dsrc Dtgt Dr).relabelPar toEmpty).toSpec, ?_⟩
  intro A _ _ _ _
  let := I.mapLinearOrder A
  have : Finite (I.Map A) := I.map_finite A
  have : Nonempty (I.Map A) := f.map_nonempty A
  obtain ⟨a₀, hbot⟩ := exists_bot A
  let instE := I.expStructure A
  have hsim : ∀ a b : S.Node A, (S.flat Dstep false).ReachAt (Decider.noPar A ∘ toEmpty)
      (S.flatEnc Dstep false a₀ a) (S.flatEnc Dstep false a₀ b) ↔
        S.ReachAt (Decider.noPar A ∘ toEmpty) a b :=
    S.reachAt_flat_iff Dstep (fun p x y => (hstep p.1 p.2).1 A _) hbot
  have hdec := S.decides_sentenceDecider Dstep false (spec.pullSrc I.ordInterp)
    (spec.pullTgt I.ordInterp) Dsrc Dtgt Dr hbot (Decider.noPar A ∘ toEmpty)
    (fun m x => (hsrc m).1 A x) (fun m x => (htgt m).1 A x)
    (fun m n w => (S.flat Dstep false).toParam.decides_reachDecider (ma := Sum.inl m)
      (mb := Sum.inl n) w)
    hsim
  rw [Decider.accepts_toSpec _ (Decider.decides_relabelPar _ _ _ hdec), f.correct A,
    hspec (I.Map A), I.accepts_iff_pulled spec A]
  change spec.PulledAccepts I.ordInterp A ↔ _
  have hz : spec.pullPar I.ordInterp A = Decider.noPar A ∘ toEmpty :=
    funext fun i => (Fin.cast (Nat.zero_mul _) i).elim0
  rw [TCSpec.PulledAccepts, hz]

/-- **FO(DTC) definability is closed under FO(DTC) reductions**: the normal
form, deterministically. -/
theorem DTCDefinable.of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : DTCDefinable Q) : DTCDefinable P := by
  classical
  obtain ⟨spec, hspec⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  set I : TCInterpretation (L.sum Language.order) L' f.Tag f.dim := ⟨f.fam.det, f.toRel⟩
  set S := spec.det.pullSpec I.ordInterp
  have hD := f.fam.decides_detReachDeciders
  have hDf := f.fam.functional_detReachDeciders
  choose Dstep hstep using fun m n => Decider.exists_of_formula₀
    (fun A _ _ => f.fam.det.reachAssign A) f.fam.detReachDeciders hD (S.step m n)
  choose Dsrc hsrc using fun m => Decider.exists_of_formula₀
    (fun A _ _ => f.fam.det.reachAssign A) f.fam.detReachDeciders hD
    (spec.det.pullSrc I.ordInterp m)
  choose Dtgt htgt using fun m => Decider.exists_of_formula₀
    (fun A _ _ => f.fam.det.reachAssign A) f.fam.detReachDeciders hD
    (spec.det.pullTgt I.ordInterp m)
  let Dr := fun m n => (S.flat Dstep true).toParam.detReachDecider (Sum.inl m) (Sum.inl n)
  let toEmpty : Fin S.par → Empty := fun i => (Fin.cast (Nat.zero_mul _) i).elim0
  refine ⟨((S.sentenceDecider Dstep true Dsrc Dtgt Dr).relabelPar toEmpty).toSpec, ?_⟩
  intro A _ _ _ _
  let := I.mapLinearOrder A
  have : Finite (I.Map A) := I.map_finite A
  have : Nonempty (I.Map A) := f.map_nonempty A
  obtain ⟨a₀, hbot⟩ := exists_bot A
  let instE := I.expStructure A
  have hstepf : ∀ p : S.Mode × S.Mode, (Dstep p.1 p.2).Functional A :=
    fun p => (hstep p.1 p.2).2 A (fun q => hDf A q)
  have hflat : (S.flat Dstep true).toParam.Functional A :=
    CoordWalk.functional_toParam _ (S.functional_flat Dstep hstepf)
  have hS : ∀ a b c : S.Node A, S.StepAt (Decider.noPar A ∘ toEmpty) a b →
      S.StepAt (Decider.noPar A ∘ toEmpty) a c → b = c := by
    refine spec.det.pullSpec_functional I.ordInterp ?_ _
    intro u v w huv huw
    let e := I.toRel.ordExtendSrcLEquiv LHom.sumInl (I.expStructure A)
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    let : LinearOrder (I.toRel.MapRel A) := I.mapLinearOrder A
    have h1 := (ParamTCSpec.stepAt_of_equiv e spec.det.toParam (fun i => i.elim0) u v).mpr huv
    have h2 := (ParamTCSpec.stepAt_of_equiv e spec.det.toParam (fun i => i.elim0) u w).mpr huw
    rw [spec.det.stepAt_toParam] at h1 h2
    exact TCSpec.det_functional (spec := spec) (A := I.toRel.MapRel A) _ _ _ h1 h2
  have hsim : ∀ a b : S.Node A, (S.flat Dstep true).ReachAt (Decider.noPar A ∘ toEmpty)
      (S.flatEnc Dstep true a₀ a) (S.flatEnc Dstep true a₀ b) ↔
        S.ReachAt (Decider.noPar A ∘ toEmpty) a b :=
    S.reachAt_flat_iff_of_functional Dstep (fun p x y => (hstep p.1 p.2).1 A _) hbot hS
  have hr : S.DecidesReach Dstep true Dr A := by
    intro m n w
    refine ((S.flat Dstep true).toParam.decides_detReachDecider (Sum.inl m) (Sum.inl n) w).congr ?_
    exact ParamTCSpec.reachAt_det_of_functional hflat _ _ _
  have hdec := S.decides_sentenceDecider Dstep true (spec.det.pullSrc I.ordInterp)
    (spec.det.pullTgt I.ordInterp) Dsrc Dtgt Dr hbot (Decider.noPar A ∘ toEmpty)
    (fun m x => (hsrc m).1 A x) (fun m x => (htgt m).1 A x) hr hsim
  have hfun : ((S.sentenceDecider Dstep true Dsrc Dtgt Dr).relabelPar toEmpty).Functional A :=
    Decider.functional_relabelPar _ _ (S.functional_sentenceDecider Dstep true Dsrc Dtgt Dr
      (fun m => (hsrc m).2 A fun q => hDf A q) (fun m => (htgt m).2 A fun q => hDf A q)
      fun m n => (S.flat Dstep true).toParam.functional_detReachDecider (Sum.inl m) (Sum.inl n))
  rw [Decider.det_accepts_toSpec _ (Decider.decides_relabelPar _ _ _ hdec) hfun, f.correct A,
    hspec (I.Map A), I.accepts_iff_pulled spec.det A]
  change spec.det.PulledAccepts I.ordInterp A ↔ _
  have hz : spec.det.pullPar I.ordInterp A = Decider.noPar A ∘ toEmpty :=
    funext fun i => (Fin.cast (Nat.zero_mul _) i).elim0
  rw [TCSpec.PulledAccepts, hz]

end Closure

/-! ### The classes -/

section Classes

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L}
  {Q : DecisionProblem L'}

/-- **NL is closed under FO(TC) reductions.** -/
theorem mem_NL_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ NL) : P ∈ NL :=
  (tcDefinable_iff_mem_NL P).mp (TCDefinable.of_tcReduction f ((tcDefinable_iff_mem_NL Q).mpr h))

/-- **NL is closed under FO(DTC) reductions.** -/
theorem mem_NL_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ NL) : P ∈ NL :=
  mem_NL_of_tcReduction f.toTC h

/-- **LOGSPACE is closed under FO(DTC) reductions.** -/
theorem mem_LOGSPACE_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ LOGSPACE) : P ∈ LOGSPACE :=
  DTCDefinable.of_dtcReduction f h

/-- An FO(TC) reduction complements: the same interpretation reduces the
complements. -/
noncomputable def TCReduction.compl (f : P ≤ᵗᶜ Q) : Pᶜ ≤ᵗᶜ Qᶜ :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    map_nonempty := f.map_nonempty
    correct := fun A _ _ _ _ => not_congr (f.correct A) }

/-- An FO(DTC) reduction complements. -/
noncomputable def DTCReduction.compl (f : P ≤ᵈᵗᶜ Q) : Pᶜ ≤ᵈᵗᶜ Qᶜ :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    fam := f.fam
    toRel := f.toRel
    map_nonempty := f.map_nonempty
    correct := fun A _ _ _ _ => not_congr (f.correct A) }

/-- **coNL is closed under FO(TC) reductions.** -/
theorem mem_coNL_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ coNL) : P ∈ coNL :=
  (NL.mem_compl P).mpr (mem_NL_of_tcReduction f.compl ((NL.mem_compl Q).mp h))

/-- **coLOGSPACE is closed under FO(DTC) reductions** (the complement class
`LOGSPACE.compl` is `DescriptiveComplexity.coLOGSPACE`, which is defined with
its complete problem in `DescriptiveComplexity.Problems.ReachabilityDet.Complement`). -/
theorem mem_coLOGSPACE_of_dtcReduction (f : P ≤ᵈᵗᶜ Q) (h : Q ∈ LOGSPACE.compl) :
    P ∈ LOGSPACE.compl :=
  (LOGSPACE.mem_compl P).mpr (mem_LOGSPACE_of_dtcReduction f.compl ((LOGSPACE.mem_compl Q).mp h))

end Classes

end DescriptiveComplexity
