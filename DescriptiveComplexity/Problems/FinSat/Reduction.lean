/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Hardness
import DescriptiveComplexity.RecursivelyEnumerable

/-!
# The reduction to FINSAT, and its correctness

`DescriptiveComplexity.Problems.FinSat.Hardness` evaluates the encoded sentence `σ_A`
node by node; this file closes the two directions and assembles the ordered
first-order reduction.

* **⟹** – an assignment of the block over an extended universe `A ⊕ Fin m` *is*
  a model of `σ_A`: take `A ⊕ Fin m` as the model, the intended assignment
  `Sum.inl` of the prefix variables, and the interpretation
  `DescriptiveComplexity.FinSat.blockI` the assignment induces. The prefix and
  the diagram are `DescriptiveComplexity.FinSat.gval_of_kernel`, the kernel is
  `DescriptiveComplexity.FinSat.gval_kernel`.
* **⟸** – a finite model of `σ_A` *is* such an assignment. The existential
  prefix is walked once more, this time to read the witnesses off: at each node
  the truth definition hands over a value for that node's variable, so an
  induction along the input order produces an environment giving every prefix
  variable a value, and the diagram makes that assignment `ι` injective. Its
  complement in the model is finite – that is the `m` – so the model is
  `A ⊕ Fin m` up to a bijection, and the relations of the instance read through
  `ι` are exactly those of the extended structure.

The two remaining pieces of bookkeeping the converse needs are here too: the
truth definition at the nodes only the converse inspects (the prefix, the top
conjunction and a distinctness literal), and the fact that `Gval` only sees an
interpretation at the symbols some node carries
(`DescriptiveComplexity.FinSat.gval_congr_I`), which is what lets the model's
own interpretation be replaced by the one a block assignment induces.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

section Reduction

variable {L : Language.{0, 0}} (B : SOBlock) (φ : ((newLang L).sum B.lang).Sentence)
variable {A : Type} [L.Structure A] [LinearOrder A]
variable {a₀ : A} {M : Type}

/-! ### The head of a one-block second-order satisfaction -/

/-- Realization of a one-block `∃SO` sentence is realization of its kernel in
the expansion by an assignment. -/
theorem sorealize_head_iff {A' : Type} [(newLang L).Structure A'] :
    SORealize (newLang L) A' [B] φ true ↔
      ∃ μ : B.Assignment A', Tseitin.RealizeWith μ φ finZeroElim := by
  refine exists_congr fun μ => ?_
  exact iff_of_eq (congrArg₂
    (fun (val : Empty → A') (xs : Fin 0 → A') =>
      @BoundedFormula.Realize _ A' (Tseitin.assignStructure (newLang L) μ) _ _ φ val xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-! ### The extended universe reads the instance through `Sum.inl`

The two facts about the model that the kernel recursion
(`DescriptiveComplexity.FinSat.gval_kernel`) asks for, on the extended
structure. -/

omit [LinearOrder A] in
theorem relMap_ext_iff' [L.IsRelational] {m k : ℕ} (r : L.Relations k)
    (u : Fin k → A ⊕ Fin m) :
    RelMap (L := newLang L) (Sum.inl r) u ↔
      ∃ y : Fin k → A, RelMap r y ∧ ∀ j, u j = Sum.inl (y j) :=
  (relMap_ext_iff r u).trans
    ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩

omit [LinearOrder A] in
theorem relMap_ext_old' [L.IsRelational] {m : ℕ} (u : Fin 1 → A ⊕ Fin m) :
    RelMap (L := newLang L) (Sum.inr Language.oldSym) u ↔ ∃ a : A, u 0 = Sum.inl a :=
  (relMap_ext_old u).trans isOld_iff

/-! ### ⟹ : an assignment of the block is a model of the encoded sentence -/

/-- **The image of a yes-instance is finitely satisfiable**: the extended
universe carrying the assignment is a model of `σ_A`, with `Sum.inl` as the
intended assignment of the prefix variables. -/
theorem finSatOn_of_realizeWith [L.IsRelational] [Finite A] [Nonempty A] {m : ℕ}
    (μ : B.Assignment (A ⊕ Fin m)) (hμ : Tseitin.RealizeWith μ φ finZeroElim) :
    FinSatOn ((finsatInterp B φ).Map A) := by
  classical
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : A, IsBot b₀ := Finite.exists_min (id : A → A)
  refine ⟨image_isWF B φ, A ⊕ Fin m, inferInstance, inferInstance,
    blockI B φ b₀ μ, local_blockI B φ hb₀ μ, ?_⟩
  refine gval_of_kernel B φ hb₀ (blockI B φ b₀ μ) Sum.inl Sum.inl_injective ?_
  intro v hv
  refine (gval_kernel B φ hb₀ μ Sum.inl (fun r u => relMap_ext_iff' r u)
    (fun u => relMap_ext_old' u) φ (SubEmb.refl φ) (Nat.zero_le _) v hv).1.mpr ?_
  rwa [Subsingleton.elim (pref (Nat.zero_le (Tseitin.maxCtx φ)) (envOf B φ b₀ v)) finZeroElim]

/-! ### The nodes only the converse inspects

Reading a model of `σ_A` means going through the truth definition at the nodes
the ⟹ direction only had to *build*: a node of the existential prefix, the top
conjunction, and a distinctness literal of the diagram. As everywhere, the
clauses that cannot fire are ruled out by the tag. -/

/-- A tag no positive equality literal is defined at carries none. -/
theorem not_eqG_tag (ha₀ : IsBot a₀) (t : FTag B φ)
    (ht : ∀ t' t'' : FTag B φ, eqBodyF B φ t t' t'' = ⊥)
    (w : Fin (tagDim B φ t) → A) (x y : (finsatInterp B φ).Map A) :
    ¬EqG (ptOf B φ a₀ t w) x y := by
  intro h
  obtain ⟨hx, hy⟩ := canon_of_eqG B φ h
  obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
  obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
  exact not_eqG_ptOf B φ ha₀ _ _ _ (ht t' t'') w w' w'' h

/-- The same for the negated equality literals. -/
theorem not_neqG_tag (ha₀ : IsBot a₀) (t : FTag B φ)
    (ht : ∀ t' t'' : FTag B φ, neqBodyF B φ t t' t'' = ⊥)
    (w : Fin (tagDim B φ t) → A) (x y : (finsatInterp B φ).Map A) :
    ¬NeqG (ptOf B φ a₀ t w) x y := by
  intro h
  obtain ⟨hx, hy⟩ := canon_of_neqG B φ h
  obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
  obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
  exact not_neqG_ptOf B φ ha₀ _ _ _ (ht t' t'') w w' w'' h

/-- **A node of the prefix binds its own variable, and nothing else.** -/
theorem bindG_pre_iff (ha₀ : IsBot a₀) (a : A) (x : (finsatInterp B φ).Map A) :
    BindG (prePt B φ a₀ a) x ↔ x = pvarPt B φ a₀ a := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (bindG_iff_pt B φ ha₀ Tag.pre (fun _ => a) x).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨q, pol⟩ | ⟨q, pol⟩ | ⟨q, pol, j⟩ <;>
      try exact absurd h (not_bindG_ptOf B φ ha₀ _ _ rfl _ _)
    have hw := tup_one_eq B φ (t := Tag.pvar) rfl w' (by norm_num : (0 : ℕ) < 1)
    rw [hw] at h ⊢
    exact congrArg (ptOf B φ a₀ Tag.pvar)
      (funext fun _ => ((bindG_pre_pvar B φ ha₀ a _).mp h).symm)
  · rintro rfl
    exact (bindG_pre_pvar B φ ha₀ a a).mpr rfl

/-- **A distinctness literal of the diagram, inverted**: it exists only for a
distinct pair, and relates the two prefix variables of that pair. -/
theorem neqG_neq_iff (ha₀ : IsBot a₀) (a b : A) (x y : (finsatInterp B φ).Map A) :
    NeqG (neqPt B φ a₀ a b) x y ↔
      a ≠ b ∧ x = pvarPt B φ a₀ a ∧ y = pvarPt B φ a₀ b := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := canon_of_neqG B φ h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
    obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
    rcases t' with _ | _ | _ | _ | l₁ | i | j | ⟨q, pol⟩ | ⟨q, pol⟩ | ⟨q, pol, j⟩ <;>
      rcases t'' with _ | _ | _ | _ | l₂ | i' | j' | ⟨q', pol'⟩ | ⟨q', pol'⟩ | ⟨q', pol', j'⟩ <;>
      try exact absurd h (not_neqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)
    have hw' := tup_one_eq B φ (t := Tag.pvar) rfl w' (by norm_num : (0 : ℕ) < 1)
    have hw'' := tup_one_eq B φ (t := Tag.pvar) rfl w'' (by norm_num : (0 : ℕ) < 1)
    rw [hw', hw''] at h ⊢
    obtain ⟨h1, h2, h3⟩ := (neqG_neq_pvar B φ ha₀ a b _ _).mp h
    exact ⟨h3, congrArg (ptOf B φ a₀ Tag.pvar) (funext fun _ => h1.symm),
      congrArg (ptOf B φ a₀ Tag.pvar) (funext fun _ => h2.symm)⟩
  · rintro ⟨hab, rfl, rfl⟩
    exact (neqG_neq_pvar B φ ha₀ a b a b).mpr ⟨rfl, rfl, hab⟩

/-- The truth definition at a node of the existential prefix: it binds its own
variable, so the only clause that can fire hands over a value for it. -/
theorem gstep_pre (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (a : A) :
    gstep I rec v (prePt B φ a₀ a) ↔
      ∃ d : M, ∃ c, ChildG (prePt B φ a₀ a) c ∧
        rec (upd v (pvarPt B φ a₀ a) d) c := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, x, hx, h⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact ((andG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((orG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · rw [(bindG_pre_iff B φ ha₀ a x).mp hx] at h
      exact h
    · exact absurd hxy (not_eqG_tag B φ ha₀ Tag.pre (fun _ _ => rfl) _ x y)
    · exact absurd hxy (not_neqG_tag B φ ha₀ Tag.pre (fun _ _ => rfl) _ x y)
    · exact absurd hps (not_posG_of_ne_nd B φ Tag.pre (by simp) _ s)
    · exact absurd hps (not_negG_of_ne_nd B φ Tag.pre (by simp) _ s)
  · rintro ⟨d, c, hc, hr⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(exG_ptOf B φ ha₀ Tag.pre _).mpr trivial, pvarPt B φ a₀ a,
        (bindG_pre_iff B φ ha₀ a _).mpr rfl, d, c, hc, hr⟩)))

/-- The truth definition at the top conjunction. -/
theorem gstep_body (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) :
    gstep I rec v (bodyPt B φ a₀) ↔ ∀ c, ChildG (bodyPt B φ a₀) c → rec v c := by
  simp only [gstep]
  constructor
  · rintro (⟨-, h⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact h
    · exact ((orG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact absurd hxy (not_eqG_tag B φ ha₀ Tag.body (fun _ _ => rfl) _ x y)
    · exact absurd hxy (not_neqG_tag B φ ha₀ Tag.body (fun _ _ => rfl) _ x y)
    · exact absurd hps (not_posG_of_ne_nd B φ Tag.body (by simp) _ s)
    · exact absurd hps (not_negG_of_ne_nd B φ Tag.body (by simp) _ s)
  · intro h
    exact Or.inl ⟨(andG_ptOf B φ ha₀ Tag.body _).mpr trivial, h⟩

/-- The truth definition at a distinctness literal of the diagram. -/
theorem gstep_neq (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (a b : A) :
    gstep I rec v (neqPt B φ a₀ a b) ↔
      a ≠ b ∧ v (pvarPt B φ a₀ a) ≠ v (pvarPt B φ a₀ b) := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, hne⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact ((andG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((orG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact absurd hxy (not_eqG_tag B φ ha₀ Tag.neq (fun _ _ => rfl) _ x y)
    · obtain ⟨hab, rfl, rfl⟩ := (neqG_neq_iff B φ ha₀ a b x y).mp hxy
      exact ⟨hab, hne⟩
    · exact absurd hps (not_posG_of_ne_nd B φ Tag.neq (by simp) _ s)
    · exact absurd hps (not_negG_of_ne_nd B φ Tag.neq (by simp) _ s)
  · rintro ⟨hab, hne⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨pvarPt B φ a₀ a, pvarPt B φ a₀ b,
        (neqG_neq_iff B φ ha₀ a b _ _).mpr ⟨hab, rfl, rfl⟩, hne⟩)))))

variable [L.IsRelational] [Finite A] [Nonempty A]

theorem gval_pre_iff (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (a : A) :
    Gval I v (prePt B φ a₀ a) ↔
      ∃ d : M, ∃ c, ChildG (prePt B φ a₀ a) c ∧
        Gval I (upd v (pvarPt B φ a₀ a) d) c := by
  have : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  exact (Gval_isEval (image_isWF B φ) I v _).trans (gstep_pre B φ ha₀ I (Gval I) v a)

theorem gval_body_iff (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) :
    Gval I v (bodyPt B φ a₀) ↔ ∀ c, ChildG (bodyPt B φ a₀) c → Gval I v c := by
  have : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  exact (Gval_isEval (image_isWF B φ) I v _).trans (gstep_body B φ ha₀ I (Gval I) v)

theorem gval_neq_iff (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (a b : A) :
    Gval I v (neqPt B φ a₀ a b) ↔
      a ≠ b ∧ v (pvarPt B φ a₀ a) ≠ v (pvarPt B φ a₀ b) := by
  have : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  exact (Gval_isEval (image_isWF B φ) I v _).trans (gstep_neq B φ ha₀ I (Gval I) v a b)

/-- **The witnesses of the prefix, read off a model**: from the node of `a` the
truth definition hands over a value for `x_a` and passes to the next node, so an
induction along the input order produces an environment satisfying the top
conjunction and agreeing with the given one below `a`. -/
theorem exists_body_env (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop) :
    ∀ (a : A) (v : (finsatInterp B φ).Map A → M), Gval I v (prePt B φ a₀ a) →
      ∃ v' : (finsatInterp B φ).Map A → M,
        (∀ b : A, b < a → v' (pvarPt B φ a₀ b) = v (pvarPt B φ a₀ b)) ∧
          Gval I v' (bodyPt B φ a₀) := by
  intro a
  induction a using order_induction_down with
  | hmax z hz =>
    intro v hv
    obtain ⟨d, c, hc, hr⟩ := (gval_pre_iff B φ ha₀ I v z).mp hv
    rcases (childG_pre_iff B φ ha₀ z c).mp hc with ⟨b, rfl, hzb, -⟩ | ⟨rfl, -⟩
    · exact absurd (hz b) (not_le.mpr hzb)
    · exact ⟨upd v (pvarPt B φ a₀ z) d, fun b hb =>
        upd_of_ne _ _ (fun hcc => absurd (pvarPt_inj B φ hcc) (ne_of_lt hb)), hr⟩
  | hstep w z hwz hnb ih =>
    intro v hv
    obtain ⟨d, c, hc, hr⟩ := (gval_pre_iff B φ ha₀ I v w).mp hv
    rcases (childG_pre_iff B φ ha₀ w c).mp hc with ⟨b, rfl, hwb, hnb'⟩ | ⟨rfl, hm⟩
    · have hbz : b = z := by
        rcases lt_trichotomy b z with h | h | h
        · exact absurd ⟨hwb, h⟩ (hnb b)
        · exact h
        · exact absurd ⟨hwz, h⟩ (hnb' z)
      subst hbz
      obtain ⟨v', hagree, hbody⟩ := ih _ hr
      refine ⟨v', fun b hbw => ?_, hbody⟩
      rw [hagree b (hbw.trans hwz)]
      exact upd_of_ne _ _ (fun hcc => absurd (pvarPt_inj B φ hcc) (ne_of_lt hbw))
    · exact absurd (hm z) (not_le.mpr hwz)

/-! ### The interpretation a model carries is a block assignment

The truth definition reads an interpretation only at the symbols some node
carries, and those are exactly the symbols of the relation variables. So the
model's own interpretation may be replaced by the one induced by the assignment
that reads it back – which is what turns a model of `σ_A` into a witness of the
`∃SO[new]` definition. -/

omit [L.IsRelational] [Finite A] [Nonempty A] in
/-- **`Gval` only sees an interpretation at the symbols of the atoms**. -/
theorem gval_congr_I
    {I I' : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop}
    (h : ∀ (s : (finsatInterp B φ).Map A) (w : (finsatInterp B φ).Map A → M),
      (∃ g, PosG g s ∨ NegG g s) → (I s w ↔ I' s w)) :
    ∀ (k : ℕ) (v : (finsatInterp B φ).Map A → M) (g : (finsatInterp B φ).Map A),
      gval I k v g → gval I' k v g := by
  intro k
  induction k with
  | zero => intro _ _ hg; exact hg.elim
  | succ k ih =>
    intro v g hg
    simp only [gval_succ, gstep] at hg ⊢
    rcases hg with ⟨hk, hall⟩ | ⟨hk, c, hc, hd⟩ | ⟨hk, hall⟩ | ⟨hk, x, hx, d, c, hc, hd⟩ |
      hl | hl | ⟨s, hps, w, hw, hI⟩ | ⟨s, hps, w, hw, hI⟩
    · exact Or.inl ⟨hk, fun c hc => ih _ _ (hall c hc)⟩
    · exact Or.inr (Or.inl ⟨hk, c, hc, ih _ _ hd⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hk, fun x hx d c hc => ih _ _ (hall x hx d c hc)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, x, hx, d, c, hc, ih _ _ hd⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨s, hps, w, hw, (h s w ⟨_, Or.inl hps⟩).mp hI⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s, hps, w, hw, fun hc => hI ((h s w ⟨_, Or.inr hps⟩).mpr hc)⟩))))))

omit [L.Structure A] [L.IsRelational] [Finite A] [Nonempty A] in
/-- An element canonical at dimension zero carrying the tag of an argument
position *is* that position. -/
theorem eq_aposPt (ha₀ : IsBot a₀) {x : (finsatInterp B φ).Map A}
    {j : Fin (finsatDim B φ)} (ht : x.1 = Tag.apos j) (h : Canon 0 x.2) :
    x = aposPt B φ a₀ j :=
  Prod.ext_iff.mpr ⟨ht, eq_of_canon_zero B φ h (canon_ptOf B φ ha₀ (Tag.apos j) _)⟩

omit [L.Structure A] [LinearOrder A] [L.IsRelational] [Finite A] [Nonempty A] in
theorem aposPt_inj {j j' : Fin (finsatDim B φ)}
    (h : aposPt B φ a₀ j = aposPt B φ a₀ j') : j = j' :=
  Tag.apos.inj (congrArg Prod.fst h)

open Classical in
/-- **The block assignment a model's interpretation carries**: the relation of a
variable is its symbol's, read at an assignment of the argument positions
holding the tuple. -/
noncomputable def blockOf (a₀ : A)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop) (junk : M) :
    B.Assignment M :=
  fun i u => I (symPt B φ a₀ i) fun q =>
    if h : ∃ j : Fin (finsatDim B φ), q = aposPt B φ a₀ j ∧ (j : ℕ) < B.arity i
      then u ⟨(h.choose : ℕ), h.choose_spec.2⟩ else junk

omit [L.IsRelational] [Finite A] [Nonempty A] in
/-- It reads the interpretation back: at the symbol of a relation variable whose
arity fits in the dimension, the interpretation induced by that assignment is
the interpretation itself. -/
theorem blockOf_agree (ha₀ : IsBot a₀)
    {I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop}
    (hloc : Local I) (junk : M) (i : B.ι) (hari : B.arity i ≤ finsatDim B φ)
    (w : (finsatInterp B φ).Map A → M) :
    I (symPt B φ a₀ i) w ↔ blockI B φ a₀ (blockOf B φ a₀ I junk) (symPt B φ a₀ i) w := by
  classical
  rw [blockI_symPt]
  refine hloc _ _ _ ?_
  intro q hq
  obtain ⟨-, hcq, hst⟩ := shape_of_sigG B φ _ q hq
  obtain ⟨i', j, hsym, hqt, hj⟩ := sigTag_cases B φ hst
  have hii : i' = i := (Tag.sym.inj hsym).symm
  subst hii
  have hqe : q = aposPt B φ a₀ j := eq_aposPt B φ ha₀ hqt hcq
  subst hqe
  have hex : ∃ j' : Fin (finsatDim B φ),
      aposPt B φ a₀ j = aposPt B φ a₀ j' ∧ (j' : ℕ) < B.arity i' := ⟨j, rfl, hj⟩
  have hchoose : hex.choose = j := (aposPt_inj B φ hex.choose_spec.1).symm
  change w (aposPt B φ a₀ j) = dite _ _ _
  rw [dif_pos hex, argTup, dif_pos hex.choose.isLt]
  exact (congrArg (fun z => w (aposPt B φ a₀ z)) (Fin.ext (congrArg Fin.val hchoose))).symm

/-! ### ⟸ : a model of the encoded sentence is an assignment of the block -/

/-- The model, seen through the intended assignment of the prefix variables: a
relation of the instance holds of a tuple of the model exactly when the tuple is
the image of one where it holds. This is the shape an extended universe has
(`DescriptiveComplexity.relMap_ext_iff`), and all the kernel recursion asks
of a model. -/
@[instance_reducible]
def viaIotaBase (ι : A → M) : L.Structure M where
  funMap f := isEmptyElim f
  RelMap {_k} r u := ∃ y, RelMap r y ∧ ∀ j, u j = ι (y j)

/-- The marking predicate on such a model: the elements in the image. -/
@[instance_reducible]
def viaIotaOld (ι : A → M) : Language.oldMark.Structure M where
  RelMap | .old => fun u => ∃ a : A, u 0 = ι a

/-- The model as a structure over `DescriptiveComplexity.newLang L`. -/
@[instance_reducible]
def viaIota (ι : A → M) : (newLang L).Structure M :=
  @sumStructure L Language.oldMark M (viaIotaBase ι) (viaIotaOld ι)

/-- **A model of the encoded sentence is an extended universe**: the intended
assignment is injective, so its complement is the invented part. -/
theorem realizeWith_of_finSatOn (hfs : FinSatOn ((finsatInterp B φ).Map A)) :
    ∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true := by
  classical
  obtain ⟨-, M, hMfin, hMne, I, hloc, hroot⟩ := hfs
  have := hMfin
  have := hMne
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  -- the prefix, walked to read off the witnesses
  have hpre : Gval I (fun _ => Classical.arbitrary M) (prePt B φ a₀ a₀) :=
    hroot _ _ ((rootG_pre B φ ha₀ a₀).mpr fun b => ha₀ b)
  obtain ⟨v, -, hbody⟩ := exists_body_env B φ ha₀ I a₀ _ hpre
  set ι : A → M := fun a => v (pvarPt B φ a₀ a) with hι
  have hchild := (gval_body_iff B φ ha₀ I v).mp hbody
  have hinj : Function.Injective ι := by
    intro a b hab
    by_contra hne
    exact ((gval_neq_iff B φ ha₀ I v a b).mp
      (hchild _ ((childG_body_iff B φ ha₀ _).mpr (Or.inl ⟨a, b, hne, rfl⟩)))).2 hab
  have hker : Gval I v (ndPt B φ a₀ (rootPos B φ) true) :=
    hchild _ ((childG_body_iff B φ ha₀ _).mpr (Or.inr rfl))
  -- the block assignment the interpretation carries
  let : (newLang L).Structure M := viaIota ι
  set μ : B.Assignment M := blockOf B φ a₀ I (Classical.arbitrary M) with hμ
  have hagree : ∀ (s : (finsatInterp B φ).Map A) (w : (finsatInterp B φ).Map A → M),
      (∃ g, PosG g s ∨ NegG g s) → (I s w ↔ blockI B φ a₀ μ s w) := by
    rintro s w ⟨g, hg⟩
    have hshape : Canon 0 s.2 ∧ atomTag B φ true g.1 s.1 ∨ Canon 0 s.2 ∧
        atomTag B φ false g.1 s.1 := by
      rcases hg with hg | hg
      · exact Or.inl ⟨(shape_of_posG B φ g s hg).2.1, (shape_of_posG B φ g s hg).2.2⟩
      · exact Or.inr ⟨(shape_of_negG B φ g s hg).2.1, (shape_of_negG B φ g s hg).2.2⟩
    obtain ⟨hcs, p, i, -, hst, hsym⟩ : ∃ (_ : Canon 0 s.2) (p : Pos B φ) (i : B.ι),
        True ∧ s.1 = Tag.sym i ∧ blockSym B φ p = some i := by
      rcases hshape with ⟨hcs, hat⟩ | ⟨hcs, hat⟩ <;>
        · obtain ⟨p, i, -, hst, hsym⟩ := atomTag_cases B φ hat
          exact ⟨hcs, p, i, trivial, hst, hsym⟩
    have hse : s = symPt B φ a₀ i := eq_symPt B φ ha₀ hst hcs
    subst hse
    refine blockOf_agree B φ ha₀ hloc _ i ?_ w
    rw [← arityOf_eq (f := φ) hsym]
    exact (arityOf_le φ p.2).trans (maxArity_le_finsatDim B φ)
  have hker' : Gval (blockI B φ a₀ μ) v (ndPt B φ a₀ (rootPos B φ) true) := by
    obtain ⟨k, hk⟩ := hker
    exact ⟨k, gval_congr_I B φ hagree k v _ hk⟩
  -- the kernel holds over the model
  have hRW : Tseitin.RealizeWith μ φ (finZeroElim : Fin 0 → M) := by
    have h := (gval_kernel B φ ha₀ μ ι (fun r u => Iff.rfl) (fun u => Iff.rfl) φ
      (SubEmb.refl φ) (Nat.zero_le _) v (fun b => rfl)).1.mp hker'
    rwa [Subsingleton.elim (pref (Nat.zero_le (Tseitin.maxCtx φ)) (envOf B φ a₀ v))
      (finZeroElim : Fin 0 → M)] at h
  -- the model is an extended universe
  obtain ⟨m, e, he⟩ : ∃ (m : ℕ) (e : M ≃ A ⊕ Fin m), ∀ a : A, e (ι a) = Sum.inl a := by
    obtain ⟨m, ⟨eq⟩⟩ := Finite.exists_equiv_fin { x : M // x ∈ (Set.range ι)ᶜ }
    refine ⟨m, (Equiv.Set.sumCompl (Set.range ι)).symm.trans
      ((Equiv.ofInjective ι hinj).symm.sumCongr eq), fun a => ?_⟩
    rw [Equiv.trans_apply,
      Equiv.Set.sumCompl_symm_apply_of_mem (Set.mem_range_self a), Equiv.sumCongr_apply]
    exact congrArg Sum.inl ((Equiv.symm_apply_eq _).mpr (Subtype.ext rfl))
  have emap : M ≃[newLang L] (A ⊕ Fin m) :=
    { toEquiv := e
      map_fun' := fun f _ => isEmptyElim f
      map_rel' := fun {_k} r x => by
        cases r with
        | inl s =>
          rw [relMap_ext_iff]
          constructor
          · rintro ⟨y, hx, hy⟩
            refine ⟨y, hy, fun i => e.injective ?_⟩
            rw [he (y i)]
            exact hx i
          · rintro ⟨y, hy, hx⟩
            refine ⟨y, fun i => ?_, hy⟩
            change e (x i) = Sum.inl (y i)
            rw [hx i]
            exact he (y i)
        | inr s =>
          cases s
          change IsOld (e (x 0)) ↔ ∃ a : A, x 0 = ι a
          rw [isOld_iff]
          constructor
          · rintro ⟨a, ha⟩
            refine ⟨a, e.injective ?_⟩
            rw [ha, he]
          · rintro ⟨a, ha⟩
            rw [ha]
            exact ⟨a, he a⟩ }
  exact ⟨m, (sorealize_iso emap [B] φ true).mp
    ((sorealize_head_iff B φ).mpr ⟨μ, hRW⟩)⟩

/-! ### The reduction -/

/-- **The image is finitely satisfiable exactly at the yes-instances.** -/
theorem finsat_image_iff :
    (∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true) ↔
      FinSatOn ((finsatInterp B φ).Map A) := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨μ, hμ⟩ := (sorealize_head_iff B φ).mp hm
    exact finSatOn_of_realizeWith B φ μ hμ
  · exact realizeWith_of_finSatOn B φ

/-- **The reduction to FINSAT**: the ordered first-order interpretation sending
an instance to the encoded sentence `σ_A`, from any problem defined, on nonempty
finite structures, by an `∃SO[new]` sentence with a single block.

Stated for relational sources: a language with function symbols would leave the
sentence guessing their junk interpretation on invented arguments, and every
vocabulary the catalog states a `DescriptiveComplexity.DecisionProblem` over is
relational. -/
noncomputable def finsatReduction (Q : DecisionProblem L)
    (hφ : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      Q A ↔ ∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true) :
    Q ≤ᶠᵒ[≤] FINSAT where
  Tag := FTag B φ
  dim := finsatDim B φ
  toInterpretation := finsatInterp B φ
  correct A _ _ _ _ := (hφ A).trans (finsat_image_iff B φ)

end Reduction

/-- **Trakhtenbrot's theorem, the hardness half over a relational vocabulary**:
every `∃SO[new]`-definable problem over a relational vocabulary admits an
ordered first-order reduction to finite satisfiability.

Membership is `DescriptiveComplexity.finsat_mem_RE`; together they say
that finite satisfiability is complete for `∃SO[new]`. Cofinal hardness
(`DescriptiveComplexity.RE.Hard`) quantifies over every *relational* source
vocabulary (`DescriptiveComplexity.hard_RE_iff`), which is exactly what this
supplies. -/
theorem finsat_hard_of_sigmaSONewDefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L),
      SigmaSONewDefinable Q → Nonempty (Q ≤ᶠᵒ[≤] FINSAT) := by
  rintro L _ Q ⟨B, φ, hφ⟩
  exact ⟨finsatReduction B φ Q hφ⟩

end FinSat

end DescriptiveComplexity
