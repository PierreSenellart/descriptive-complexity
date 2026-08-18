/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Invariant.Structure
import DescriptiveComplexity.FixedPointPartial
import DescriptiveComplexity.Composition

/-!
# Simulating a `k`-variable induction on the invariant structure

The forward simulation of the Abiteboul–Vianu argument
(`DescriptiveComplexity.AbiteboulVianu`): a simultaneous induction within the `k`-variable
budget runs, step for step, on the invariant structure `Iᵏ A`
(`DescriptiveComplexity.InvMap`). Its stage relations are `≡ᵏ`-invariant
(`DescriptiveComplexity.Invariant.Stages`), so they are *unary* relations on
the classes; one application of a step formula is evaluated on the classes by
the **pebble compiler** (`DescriptiveComplexity.pebbleCompile`), which
translates a formula over the base vocabulary expanded by the block into a
formula over the invariant vocabulary expanded by the unary copy of the block
(`DescriptiveComplexity.classBlock`), one free class variable standing for
the current pebble assignment:

* atomic formulas become atomic-type bits of the class;
* block atoms follow a rearrangement relation to the class of the reordered
  argument tuple, and read the unary relation variable there;
* a quantifier spends a fresh pebble: it becomes a quantifier over the
  classes reachable along that pebble's substitution relation.

The compiler is exact (`DescriptiveComplexity.realize_pebbleCompile`, the
same pebble induction as the `k`-variable invariance lemma
`DescriptiveComplexity.realize_equivK`, which also absorbs each re-choice of
a representative); the induced induction on the invariant structure and the
stage-by-stage tracking are `DescriptiveComplexity.StepDef.invStepDef` and
its lemmas, further down.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}} {k : ℕ} {B : SOBlock}

/-! ### The unary copy of a block -/

/-- The unary copy of a block: the same relation variables, all unary – on
the invariant structure, an invariant relation is a set of classes.
(Reducible so that numerals elaborate at the block's arities.) -/
@[reducible]
def classBlock (B : SOBlock) : SOBlock where
  ι := B.ι
  arity := fun _ => 1

/-- The relation symbol of an invariant-vocabulary relation, in the expansion
by the unary block. -/
abbrev invRelSym (L : Language.{0, 0}) (k : ℕ) (B : SOBlock) {n : ℕ}
    (r : InvRel L k n) : ((invLang L k).sum (classBlock B).lang).Relations n :=
  Sum.inl r

/-! ### The pebble compiler -/

/-- The coordinate selection of a block atom, extended to a rearrangement of
all `k` pebbles (fixing the pebbles beyond the atom's arity). -/
def blockSel {l : ℕ} (sel : Fin l → Fin k) : Fin k → Fin k :=
  fun q => if hq : (q : ℕ) < l then sel ⟨q.1, hq⟩ else q

theorem blockSel_castLE {l : ℕ} (sel : Fin l → Fin k) {a : ℕ} (ha : a ≤ k)
    (hal : a = l) (j : Fin a) :
    blockSel sel (Fin.castLE ha j) = sel (Fin.cast hal j) := by
  rw [blockSel, dif_pos (show ((Fin.castLE ha j : Fin k) : ℕ) < l from hal ▸ j.isLt)]
  exact congrArg sel (Fin.ext rfl)

open Classical in
/-- **The pebble compiler**: a formula over the base vocabulary expanded by
the block, its free variables read through the selection `g` and its bound
variables through `h`, becomes a formula over the invariant vocabulary
expanded by the unary block, with one free class variable. Atomic formulas
read the atomic-type bits of the class; block atoms follow a rearrangement to
the class of their argument tuple; each quantifier spends a fresh pebble,
quantifying over the classes along its substitution relation. (When no fresh
pebble is left the compiled formula is `⊥`; the budget hypothesis of
`DescriptiveComplexity.realize_pebbleCompile` rules the case out.) -/
noncomputable def pebbleCompile [L.IsRelational] {m : ℕ} (g : Fin m → Fin k) :
    ∀ {n : ℕ}, (L.sum B.lang).BoundedFormula (Fin m) n → (Fin n → Fin k) →
      ((invLang L k).sum (classBlock B).lang).Formula (Fin 1)
  | _, .falsum, _ => ⊥
  | _, .equal t₁ t₂, h =>
      Relations.formula
        (invRelSym L k B (.eqBit (Sum.elim g h t₁.varOf) (Sum.elim g h t₂.varOf)))
        fun _ => Term.var 0
  | _, .rel R ts, h =>
      match R with
      | Sum.inl r =>
          Relations.formula
            (invRelSym L k B (.relBit ⟨_, r⟩ fun p => Sum.elim g h (ts p).varOf))
            fun _ => Term.var 0
      | Sum.inr rv =>
          Formula.iExs (Fin 1)
            (Relations.formula
                (invRelSym L k B
                  (.rearr (blockSel fun p => Sum.elim g h (ts p).varOf)))
                ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⊓
              Relations.formula (varInSym (invLang L k) (classBlock B) rv.1)
                fun _ => Term.var (Sum.inr 0))
  | _, .imp f₁ f₂, h => pebbleCompile g f₁ h ⟹ pebbleCompile g f₂ h
  | _, .all ψ, h =>
      if hfresh : ∃ p : Fin k, (∀ i, g i ≠ p) ∧ ∀ j, h j ≠ p then
        Formula.iAlls (Fin 1)
          (Relations.formula (invRelSym L k B (.sub hfresh.choose))
              ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⟹
            (pebbleCompile g ψ (Fin.snoc h hfresh.choose)).relabel
              fun _ => Sum.inr 0)
      else ⊥

/-! ### Exactness of the compiler -/

section Realize

variable [L.IsRelational] {S : Set (Σ n, L.Relations n)} {A : Type}
variable [L.Structure A] [Finite A]
variable {X : (classBlock B).Assignment (InvMap S k A)}

omit [L.IsRelational] in
private theorem realize_rearrBody (σ : Fin k → Fin k) (i : B.ι)
    (val c : Fin 1 → InvMap S k A) :
    (@Formula.Realize _ (InvMap S k A)
      ((classBlock B).structure₁ (L := invLang L k) X) _
      (Relations.formula (invRelSym L k B (.rearr σ))
          ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⊓
        Relations.formula (varInSym (invLang L k) (classBlock B) i)
          fun _ => Term.var (Sum.inr 0))
      (Sum.elim val c)) ↔
      (InvMap.rearrRel σ (val 0) (c 0) ∧ X i fun _ => c 0) := by
  let := (classBlock B).structure₁ (L := invLang L k) X
  rw [Formula.realize_inf, Formula.realize_rel, Formula.realize_rel]
  exact Iff.rfl

omit [L.IsRelational] in
private theorem realize_subAtom (p : Fin k) (val c : Fin 1 → InvMap S k A) :
    (@Formula.Realize _ (InvMap S k A)
      ((classBlock B).structure₁ (L := invLang L k) X) _
      (Relations.formula (invRelSym L k B (.sub p))
        ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)])
      (Sum.elim val c)) ↔ InvMap.subRel p (val 0) (c 0) := by
  let := (classBlock B).structure₁ (L := invLang L k) X
  rw [Formula.realize_rel]
  exact Iff.rfl

/-- **Exactness of the pebble compiler**: over an invariant block assignment
`ρ` on `A` and its unary image `X` on the classes, the compiled formula holds
at the class of `v` exactly when the original formula holds at the pebble
assignment `v`. The induction is the one of the `k`-variable invariance
lemma: each quantifier spends a fresh pebble, and re-choosing a
representative is absorbed by the invariance lemma itself
(`DescriptiveComplexity.realize_equivK`). -/
theorem realize_pebbleCompile {m : ℕ} {ρ : B.Assignment A}
    (hρ : AssignInvariant S A k ρ) (harity : ∀ i, B.arity i ≤ k)
    (hX : ∀ (i : B.ι) (w : Fin k → A),
      X i (fun _ => InvMap.mk S w) ↔ ρ i fun p => w (Fin.castLE (harity i) p)) :
    ∀ {n : ℕ} (φ : (L.sum B.lang).BoundedFormula (Fin m) n)
      (g : Fin m → Fin k) (h : Fin n → Fin k),
      Function.Injective h → (∀ i j, g i ≠ h j) →
      (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card + qdepth φ ≤ k →
      RelsIn (blockRelsExtend S B) φ →
      ∀ v : Fin k → A,
      ((@Formula.Realize _ (InvMap S k A)
          ((classBlock B).structure₁ (L := invLang L k) X) _
          (pebbleCompile g φ h) fun _ => InvMap.mk S v) ↔
        @BoundedFormula.Realize _ A (B.structure₁ (L := L) ρ) _ _ φ
          (fun i => v (g i)) fun j => v (h j)) := by
  intro n φ
  induction φ with
  | falsum =>
    intro g h _ _ _ _ v
    exact iff_of_false (fun hf => hf) fun hf => hf
  | @equal n t₁ t₂ =>
    intro g h _ _ _ _ v
    obtain ⟨x₁, rfl⟩ := exists_eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := exists_eq_var_of_isRelational t₂
    have hval : (Sum.elim (fun i => v (g i)) fun j => v (h j)) =
        fun y : Fin m ⊕ Fin n => v (Sum.elim g h y) := by
      funext y
      rcases y with i | j <;> rfl
    have hL : (@Formula.Realize _ (InvMap S k A)
        ((classBlock B).structure₁ (L := invLang L k) X) _
        (pebbleCompile g
          (BoundedFormula.equal (Term.var x₁) (Term.var x₂)) h)
          fun _ => InvMap.mk S v) ↔
        v (Sum.elim g h x₁) = v (Sum.elim g h x₂) :=
      InvMap.relMap_eqBit (Sum.elim g h x₁) (Sum.elim g h x₂)
        (fun _ => InvMap.mk S v) v rfl
    refine hL.trans ?_
    exact iff_of_eq (congrArg₂ Eq (congrFun hval x₁) (congrFun hval x₂)).symm
  | @rel n l R ts =>
    intro g h _ _ _ hS v
    have hts : ∀ p, ∃ x, ts p = Term.var x :=
      fun p => exists_eq_var_of_isRelational (ts p)
    choose x hx using hts
    have hsub : ts = fun p => Term.var (x p) := funext hx
    subst hsub
    have hval : (Sum.elim (fun i => v (g i)) fun j => v (h j)) =
        fun y : Fin m ⊕ Fin n => v (Sum.elim g h y) := by
      funext y
      rcases y with i | j <;> rfl
    cases R with
    | inl r =>
      have hmem : (⟨l, r⟩ : Σ n', L.Relations n') ∈ S := hS
      have hL : (@Formula.Realize _ (InvMap S k A)
          ((classBlock B).structure₁ (L := invLang L k) X) _
          (pebbleCompile g (BoundedFormula.rel (Sum.inl r)
            fun p => Term.var (x p)) h) fun _ => InvMap.mk S v) ↔
          ((⟨l, r⟩ : Σ n', L.Relations n') ∈ S ∧
            RelMap r fun p => v (Sum.elim g h (x p))) :=
        InvMap.relMap_relBit ⟨l, r⟩ (fun p => Sum.elim g h (x p))
          (fun _ => InvMap.mk S v) v rfl
      refine (hL.trans (and_iff_right hmem)).trans ?_
      exact iff_of_eq
        (congrArg (RelMap r) (funext fun p => (congrFun hval (x p)).symm))
    | inr rv =>
      -- a block atom: follow the rearrangement, read the unary variable
      have he : pebbleCompile (B := B) g
          (BoundedFormula.rel (Sum.inr rv) fun p => Term.var (x p)) h =
          Formula.iExs (Fin 1)
            (Relations.formula
                (invRelSym L k B
                  (.rearr (blockSel fun p => Sum.elim g h (x p))))
                ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⊓
              Relations.formula (varInSym (invLang L k) (classBlock B) rv.1)
                fun _ => Term.var (Sum.inr 0)) := by
        simp only [pebbleCompile, Language.Term.varOf]
      have hcomp : (@Formula.Realize _ (InvMap S k A)
          ((classBlock B).structure₁ (L := invLang L k) X) _
          (pebbleCompile g (BoundedFormula.rel (Sum.inr rv)
            fun p => Term.var (x p)) h) fun _ => InvMap.mk S v) ↔
          ∃ c : Fin 1 → InvMap S k A,
            (InvMap.rearrRel (blockSel fun p => Sum.elim g h (x p))
              (InvMap.mk S v) (c 0) ∧ X rv.1 fun _ => c 0) := by
        rw [he]
        let := (classBlock B).structure₁ (L := invLang L k) X
        rw [Formula.realize_iExs]
        exact exists_congr fun c =>
          realize_rearrBody (blockSel fun p => Sum.elim g h (x p)) rv.1
            (fun _ => InvMap.mk S v) c
      refine hcomp.trans ?_
      have hRHS : (@BoundedFormula.Realize _ A (B.structure₁ (L := L) ρ) _ _
          (BoundedFormula.rel (Sum.inr rv) fun p => Term.var (x p))
          (fun i => v (g i)) fun j => v (h j)) ↔
          ρ rv.1 fun j => v (Sum.elim g h (x (Fin.cast rv.2 j))) :=
        iff_of_eq (congrArg (ρ rv.1)
          (funext fun j => congrFun hval (x (Fin.cast rv.2 j))))
      rw [hRHS]
      have hσ : ∀ j : Fin (B.arity rv.1),
          blockSel (fun p => Sum.elim g h (x p)) (Fin.castLE (harity rv.1) j) =
            Sum.elim g h (x (Fin.cast rv.2 j)) :=
        fun j => blockSel_castLE _ (harity rv.1) rv.2 j
      constructor
      · rintro ⟨c, hre, hXc⟩
        obtain ⟨w, hw⟩ := InvMap.exists_rep (c 0)
        rw [← hw] at hre hXc
        have hre' : EquivK (atomicAgreeOn S A k)
            (fun p => v (blockSel (fun p' => Sum.elim g h (x p')) p)) w := hre
        have hXw : ρ rv.1 fun p => w (Fin.castLE (harity rv.1) p) :=
          (hX rv.1 w).mp hXc
        have hinv := hρ rv.1 (Fin.castLE (harity rv.1))
          (equivK_atomicAgreeOn_equivalence.symm hre')
        have harg : (fun p => v (blockSel (fun p' => Sum.elim g h (x p'))
              (Fin.castLE (harity rv.1) p))) =
            fun j => v (Sum.elim g h (x (Fin.cast rv.2 j))) :=
          funext fun j => congrArg v (hσ j)
        exact (iff_of_eq (congrArg (ρ rv.1) harg)).mp (hinv.mp hXw)
      · intro hρv
        refine ⟨fun _ => InvMap.mk S
          fun p => v (blockSel (fun p' => Sum.elim g h (x p')) p), ?_, ?_⟩
        · exact equivK_atomicAgreeOn_equivalence.refl _
        · refine (hX rv.1 _).mpr ?_
          have harg : (fun p => v (blockSel (fun p' => Sum.elim g h (x p'))
                (Fin.castLE (harity rv.1) p))) =
              fun j => v (Sum.elim g h (x (Fin.cast rv.2 j))) :=
            funext fun j => congrArg v (hσ j)
          exact (iff_of_eq (congrArg (ρ rv.1) harg)).mpr hρv
  | @imp n f₁ f₂ ih₁ ih₂ =>
    intro g h hinj hdisj hroom hS v
    let := B.structure₁ (L := L) ρ
    rw [BoundedFormula.realize_imp]
    have hL : (@Formula.Realize _ (InvMap S k A)
        ((classBlock B).structure₁ (L := invLang L k) X) _
        (pebbleCompile g (f₁ ⟹ f₂) h) fun _ => InvMap.mk S v) ↔
        ((@Formula.Realize _ (InvMap S k A)
          ((classBlock B).structure₁ (L := invLang L k) X) _
          (pebbleCompile g f₁ h) fun _ => InvMap.mk S v) →
        (@Formula.Realize _ (InvMap S k A)
          ((classBlock B).structure₁ (L := invLang L k) X) _
          (pebbleCompile g f₂ h) fun _ => InvMap.mk S v)) :=
      letI := (classBlock B).structure₁ (L := invLang L k) X
      Formula.realize_imp
    rw [hL]
    have h₁ := ih₁ g h hinj hdisj
      (by have := le_max_left (qdepth f₁) (qdepth f₂); simp only [qdepth] at hroom; omega)
      hS.1 v
    have h₂ := ih₂ g h hinj hdisj
      (by have := le_max_right (qdepth f₁) (qdepth f₂); simp only [qdepth] at hroom; omega)
      hS.2 v
    exact imp_congr h₁ h₂
  | @all n ψ ih =>
    intro g h hinj hdisj hroom hS v
    let := B.structure₁ (L := L) ρ
    -- a fresh pebble exists within the budget
    have hcard : (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card <
        (Finset.univ : Finset (Fin k)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      simp only [qdepth] at hroom
      omega
    obtain ⟨p₀, -, hp₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hfresh : ∃ p : Fin k, (∀ i, g i ≠ p) ∧ ∀ j, h j ≠ p :=
      ⟨p₀,
        fun i heq => hp₀ (Finset.mem_union_left _
          (heq ▸ Finset.mem_image_of_mem g (Finset.mem_univ i))),
        fun j heq => hp₀ (Finset.mem_union_right _
          (heq ▸ Finset.mem_image_of_mem h (Finset.mem_univ j)))⟩
    have hpg : ∀ i, g i ≠ hfresh.choose := hfresh.choose_spec.1
    have hph : ∀ j, h j ≠ hfresh.choose := hfresh.choose_spec.2
    -- the extended selections for the body, and their budget
    have hinj' : Function.Injective
        (Fin.snoc h hfresh.choose : Fin (n + 1) → Fin k) :=
      snoc_injective hinj hph
    have hdisj' : ∀ i j, g i ≠ (Fin.snoc h hfresh.choose : Fin (n + 1) → Fin k) j := by
      intro i j
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hpg i
      | cast q => rw [Fin.snoc_castSucc]; exact hdisj i q
    have hroom' : (Finset.image g Finset.univ ∪
          Finset.image (Fin.snoc h hfresh.choose : Fin (n + 1) → Fin k)
            Finset.univ).card + qdepth ψ ≤ k := by
      have hsub : Finset.image g Finset.univ ∪
            Finset.image (Fin.snoc h hfresh.choose : Fin (n + 1) → Fin k)
              Finset.univ ⊆
          insert hfresh.choose
            (Finset.image g Finset.univ ∪ Finset.image h Finset.univ) := by
        refine Finset.union_subset ?_ ?_
        · exact fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)
        · refine image_snoc_subset.trans ?_
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hy')
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le hfresh.choose
        (Finset.image g Finset.univ ∪ Finset.image h Finset.univ)
      simp only [qdepth] at hroom
      omega
    -- transporting a valuation across an update at the fresh pebble
    have hval : ∀ (u : Fin k → A) (c : A),
        ((fun i => Function.update u hfresh.choose c (g i)) = fun i => u (g i)) ∧
          (fun j => Function.update u hfresh.choose c
              ((Fin.snoc h hfresh.choose : Fin (n + 1) → Fin k) j)) =
            Fin.snoc (fun j => u (h j)) c := by
      intro u c
      refine ⟨funext fun i => Function.update_of_ne (hpg i) .., funext fun j => ?_⟩
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last, Fin.snoc_last, Function.update_self]
      | cast q =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact Function.update_of_ne (hph q) ..
    -- the compiled quantifier: over the classes along the substitution
    have hL : (@Formula.Realize _ (InvMap S k A)
        ((classBlock B).structure₁ (L := invLang L k) X) _
        (pebbleCompile g ψ.all h) fun _ => InvMap.mk S v) ↔
        ∀ c : Fin 1 → InvMap S k A,
          InvMap.subRel hfresh.choose (InvMap.mk S v) (c 0) →
          (@Formula.Realize _ (InvMap S k A)
            ((classBlock B).structure₁ (L := invLang L k) X) _
            (pebbleCompile g ψ (Fin.snoc h hfresh.choose)) fun _ => c 0) := by
      let := (classBlock B).structure₁ (L := invLang L k) X
      have he : pebbleCompile (B := B) g ψ.all h =
          Formula.iAlls (Fin 1)
            (Relations.formula (invRelSym L k B (.sub hfresh.choose))
                ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⟹
              (pebbleCompile g ψ (Fin.snoc h hfresh.choose)).relabel
                fun _ => Sum.inr 0) := by
        rw [pebbleCompile, dif_pos hfresh]
      rw [he, Formula.realize_iAlls]
      refine forall_congr' fun c => ?_
      rw [Formula.realize_imp, Formula.realize_relabel]
      refine imp_congr (realize_subAtom hfresh.choose (fun _ => InvMap.mk S v) c)
        (iff_of_eq (congrArg _ ?_))
      funext q
      rfl
    rw [hL, BoundedFormula.realize_all]
    constructor
    · intro hall b
      have hsubOK : InvMap.subRel hfresh.choose (InvMap.mk S v)
          (InvMap.mk S (Function.update v hfresh.choose b)) :=
        ⟨b, equivK_atomicAgreeOn_equivalence.refl _⟩
      have hcomp := hall (fun _ => InvMap.mk S
        (Function.update v hfresh.choose b)) hsubOK
      have hih := ih g (Fin.snoc h hfresh.choose) hinj' hdisj' hroom' hS
        (Function.update v hfresh.choose b)
      rw [hih] at hcomp
      rw [(hval v b).1, (hval v b).2] at hcomp
      exact hcomp
    · intro hall c hsubc
      obtain ⟨w, hw⟩ := InvMap.exists_rep (c 0)
      rw [← hw] at hsubc ⊢
      obtain ⟨a, haw⟩ := hsubc
      have hψa := hall a
      rw [← (hval v a).1, ← (hval v a).2] at hψa
      -- transfer along the representative change, by the invariance lemma
      have haw' : EquivK (@atomicAgreeOn (L.sum B.lang) (blockRelsExtend S B) A
          (B.structure₁ (L := L) ρ) k) (Function.update v hfresh.choose a) w := by
        rw [equivK_structure₁_eq hρ]
        exact haw
      have htr := realize_equivK (L := L.sum B.lang) ψ g
        (Fin.snoc h hfresh.choose) hinj' hdisj' hroom' hS
        (Function.update v hfresh.choose a) w haw'
      have hih := ih g (Fin.snoc h hfresh.choose) hinj' hdisj' hroom' hS w
      exact hih.mpr (htr.mp hψa)

end Realize

/-! ### Sentences over an empty variable supply -/

/-- A sentence, re-typed over an empty supply of `Fin`-indexed variables, so
that the pebble compiler applies to it. -/
def sentenceFin0 {L' : Language.{0, 0}} (φ : L'.Sentence) : L'.Formula (Fin 0) :=
  φ.mapTermRel (fun _ t => t.relabel (Sum.map (fun e => Empty.elim e) id))
    (fun _ => id) fun _ => id

private theorem qdepth_mapTermRelFin0 {L' : Language.{0, 0}} :
    ∀ {n : ℕ} (φ : L'.BoundedFormula Empty n),
      qdepth (φ.mapTermRel
        (fun _ t => t.relabel (Sum.map (fun e => Empty.elim e) id))
        (fun _ => id) (fun _ => id) : L'.BoundedFormula (Fin 0) n) =
        qdepth φ := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp f₁ f₂ ih₁ ih₂ =>
    simp only [BoundedFormula.mapTermRel, qdepth, ih₁, ih₂]
  | all ψ ih =>
    simp only [BoundedFormula.mapTermRel, qdepth, id_eq, ih]

theorem qdepth_sentenceFin0 {L' : Language.{0, 0}} (φ : L'.Sentence) :
    qdepth (sentenceFin0 φ) = qdepth φ :=
  qdepth_mapTermRelFin0 φ

private theorem relsIn_mapTermRelFin0 {L' : Language.{0, 0}}
    {S' : Set (Σ n, L'.Relations n)} :
    ∀ {n : ℕ} {φ : L'.BoundedFormula Empty n}, RelsIn S' φ →
      RelsIn S' (φ.mapTermRel
        (fun _ t => t.relabel (Sum.map (fun e => Empty.elim e) id))
        (fun _ => id) (fun _ => id) : L'.BoundedFormula (Fin 0) n) := by
  intro n φ h
  induction φ with
  | falsum => trivial
  | equal => trivial
  | rel => exact h
  | imp f₁ f₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all ψ ih => exact ih h

theorem relsIn_sentenceFin0 {L' : Language.{0, 0}}
    {S' : Set (Σ n, L'.Relations n)} {φ : L'.Sentence} (h : RelsIn S' φ) :
    RelsIn S' (sentenceFin0 φ) :=
  relsIn_mapTermRelFin0 h

theorem realize_sentenceFin0 {L' : Language.{0, 0}} {M : Type}
    {instM : L'.Structure M} (φ : L'.Sentence) (v : Fin 0 → M) :
    (@Formula.Realize L' M instM _ (sentenceFin0 φ) v) ↔
      @Sentence.Realize L' M instM φ := by
  let := instM
  have h := BoundedFormula.realize_mapTermRel_id (L' := L')
    (φ := φ) (v := fun e => Empty.elim e) (v' := v) (xs := (default : Fin 0 → M))
    (ft := fun _ t => t.relabel (Sum.map (fun e => Empty.elim e) id))
    (fr := fun _ => id)
    (fun n t xs => by
      rw [Term.realize_relabel]
      refine congrArg (fun env => Term.realize env t) (funext fun y => ?_)
      rcases y with e | j
      · exact e.elim
      · rfl)
    (fun n R x => rfl)
  refine h.trans ?_
  exact iff_of_eq (congrArg
    (fun w : Empty → M => BoundedFormula.Realize φ w (default : Fin 0 → M))
    (Subsingleton.elim _ _))

/-! ### The induced induction on the invariant structure -/

/-- The unary image on the classes of a block assignment: the class of `w`
is in the image of variable `i` when `ρ` holds at the initial coordinates of
`w`. -/
def invAssign {B : SOBlock} (S : Set (Σ n, L.Relations n)) {A : Type}
    [L.Structure A] (harity : ∀ i, B.arity i ≤ k) (ρ : B.Assignment A) :
    (classBlock B).Assignment (InvMap S k A) :=
  fun i x => ∃ w : Fin k → A, x 0 = InvMap.mk S w ∧
    ρ i fun p => w (Fin.castLE (harity i) p)

theorem invAssign_mk {B : SOBlock} {S : Set (Σ n, L.Relations n)} {A : Type}
    [L.Structure A] {harity : ∀ i, B.arity i ≤ k} {ρ : B.Assignment A}
    (hρ : AssignInvariant S A k ρ) (i : B.ι) (w : Fin k → A) :
    invAssign S harity ρ i (fun _ => InvMap.mk S w) ↔
      ρ i fun p => w (Fin.castLE (harity i) p) := by
  constructor
  · rintro ⟨w', hw', hρw'⟩
    exact (hρ i (Fin.castLE (harity i)) (InvMap.mk_eq_mk.mp hw')).mpr hρw'
  · intro h
    exact ⟨w, rfl, h⟩

/-- The unary image determines an invariant assignment: read any tuple at an
extension of its arguments. -/
theorem invAssign_injOn {B : SOBlock} {S : Set (Σ n, L.Relations n)} {A : Type}
    [L.Structure A] [Nonempty A] {harity : ∀ i, B.arity i ≤ k}
    {ρ₁ ρ₂ : B.Assignment A}
    (h₁ : AssignInvariant S A k ρ₁) (h₂ : AssignInvariant S A k ρ₂)
    (h : invAssign S harity ρ₁ = invAssign S harity ρ₂) : ρ₁ = ρ₂ := by
  classical
  funext i y
  have key : ∀ u : Fin k → A,
      ((ρ₁ i fun p => u (Fin.castLE (harity i) p)) ↔
        ρ₂ i fun p => u (Fin.castLE (harity i) p)) := fun u =>
    (invAssign_mk h₁ i u).symm.trans
      ((iff_of_eq (congrFun (congrFun h i) fun _ => InvMap.mk S u)).trans
        (invAssign_mk h₂ i u))
  have hy : ∃ u : Fin k → A, (fun p => u (Fin.castLE (harity i) p)) = y := by
    refine ⟨fun q => if hq : (q : ℕ) < B.arity i then y ⟨q.1, hq⟩ else
      Classical.arbitrary A, funext fun p => ?_⟩
    change (if hq : ((Fin.castLE (harity i) p : Fin k) : ℕ) < B.arity i then
      y ⟨((Fin.castLE (harity i) p : Fin k) : ℕ), hq⟩ else
      Classical.arbitrary A) = y p
    rw [dif_pos (show ((Fin.castLE (harity i) p : Fin k) : ℕ) < B.arity i from
      p.isLt)]
    exact congrArg y (Fin.ext rfl)
  obtain ⟨u, hu⟩ := hy
  rw [← hu]
  exact propext (key u)

namespace StepDef

variable [L.IsRelational] (d : StepDef L)

omit [L.IsRelational] in
/-- The arity part of the variable budget. -/
theorem VarBound.arity_le {d : StepDef L} {k : ℕ} (h : d.VarBound k) (i : d.B.ι) :
    d.B.arity i ≤ k :=
  le_trans (Nat.le_add_right _ _) (h i)

/-- **The induced induction on the invariant structure**: the same relation
variables, unary; the step formulas and the output, compiled by the pebble
compiler. -/
@[reducible]
noncomputable def invStepDef (k : ℕ) (harity : ∀ i, d.B.arity i ≤ k) :
    StepDef (invLang L k) where
  B := classBlock d.B
  step := fun i => pebbleCompile (Fin.castLE (harity i)) (d.step i) Fin.elim0
  out := Formula.iExs (Fin 1)
    ((pebbleCompile (B := d.B) Fin.elim0 (sentenceFin0 d.out) Fin.elim0).relabel
      fun _ => Sum.inr 0)

variable {S : Set (Σ n, L.Relations n)} {A : Type} [L.Structure A] [Finite A]
variable {harity : ∀ i, d.B.arity i ≤ k}

omit [L.IsRelational] in
private theorem budget_step (hbound : d.VarBound k) (i : d.B.ι) :
    (Finset.image (Fin.castLE (harity i)) Finset.univ ∪
      Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ).card +
        qdepth (d.step i) ≤ k := by
  have h1 : Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ = ∅ := by
    simp
  rw [h1, Finset.union_empty]
  have h2 : (Finset.image (Fin.castLE (harity i)) Finset.univ).card ≤
      d.B.arity i :=
    Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
  have h3 := hbound i
  omega

/-- **The partial stages of the induced induction are the images of the
original ones**: the pebble compiler tracks the iteration stage by stage. -/
theorem partStage_invStepDef (hbound : d.VarBound k) (hrels : d.UsesRels S)
    (n : ℕ) :
    ((d.invStepDef k harity).partStage (InvMap S k A) n :
        (classBlock d.B).Assignment (InvMap S k A)) =
      invAssign S harity (d.partStage A n) := by
  induction n with
  | zero =>
    funext i x
    refine propext (iff_of_false (fun hf => hf) ?_)
    rintro ⟨w, -, hf⟩
    exact hf
  | succ n ih =>
    funext i x
    obtain ⟨u, hu⟩ := InvMap.exists_rep (x 0)
    have hxeq : x = fun _ => InvMap.mk S u := by
      funext q
      have hq : q = 0 := Subsingleton.elim q 0
      rw [hq, hu]
    rw [hxeq]
    have hρn : AssignInvariant S A k (d.partStage A n) :=
      d.partStage_invariant hbound hrels n
    have hρn1 : AssignInvariant S A k (d.partStage A (n + 1)) :=
      d.partStage_invariant hbound hrels (n + 1)
    have hL1 : (d.invStepDef k harity).partStage (InvMap S k A) (n + 1) i
        (fun _ => InvMap.mk S u) ↔
        (d.invStepDef k harity).next (invAssign S harity (d.partStage A n)) i
          (fun _ => InvMap.mk S u) := by
      rw [(d.invStepDef k harity).partStage_succ, ih]
    have hcomp := realize_pebbleCompile
      (X := invAssign S harity (d.partStage A n)) hρn harity
      (fun i' w => invAssign_mk hρn i' w) (d.step i) (Fin.castLE (harity i))
      Fin.elim0 (Function.injective_of_subsingleton _) (fun _ j => j.elim0)
      (d.budget_step hbound i) (hrels.1 i) u
    have hxs : (fun j : Fin 0 => u (Fin.elim0 j)) = (default : Fin 0 → A) :=
      Subsingleton.elim _ _
    rw [hxs] at hcomp
    have hR1 : invAssign S harity (d.partStage A (n + 1)) i
        (fun _ => InvMap.mk S u) ↔
        d.partStage A (n + 1) i fun p => u (Fin.castLE (harity i) p) :=
      invAssign_mk hρn1 i u
    have hR2 : (d.partStage A (n + 1) i fun p => u (Fin.castLE (harity i) p)) ↔
        d.next (d.partStage A n) i fun p => u (Fin.castLE (harity i) p) := by
      rw [d.partStage_succ]
    exact propext (hL1.trans (hcomp.trans ((hR1.trans hR2).symm)))

/-- Convergence transfers between the induction and its image on the
invariant structure. -/
theorem isFixedPt_invStepDef_iff [Nonempty A] (hbound : d.VarBound k)
    (hrels : d.UsesRels S) (n : ℕ) :
    IsFixedPt (d.invStepDef k harity).next
        ((d.invStepDef k harity).partStage (InvMap S k A) n) ↔
      IsFixedPt d.next (d.partStage A n) := by
  have h1 : IsFixedPt (d.invStepDef k harity).next
      ((d.invStepDef k harity).partStage (InvMap S k A) n) ↔
      (d.invStepDef k harity).partStage (InvMap S k A) (n + 1) =
        (d.invStepDef k harity).partStage (InvMap S k A) n := by
    rw [(d.invStepDef k harity).partStage_succ]
    exact Iff.rfl
  have h2 : IsFixedPt d.next (d.partStage A n) ↔
      d.partStage A (n + 1) = d.partStage A n := by
    rw [d.partStage_succ]
    exact Iff.rfl
  rw [h1, h2, d.partStage_invStepDef hbound hrels (n + 1),
    d.partStage_invStepDef hbound hrels n]
  constructor
  · intro h
    exact invAssign_injOn (d.partStage_invariant hbound hrels (n + 1))
      (d.partStage_invariant hbound hrels n) h
  · intro h
    rw [h]

omit [L.IsRelational] in
private theorem budget_out (houtd : qdepth d.out ≤ k) :
    (Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ ∪
      Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ).card +
        qdepth (sentenceFin0 d.out) ≤ k := by
  have h1 : Finset.image (Fin.elim0 : Fin 0 → Fin k) Finset.univ = ∅ := by
    simp
  rw [h1, Finset.union_empty, Finset.card_empty, qdepth_sentenceFin0]
  omega

/-- **The forward simulation**: the partial value of the induced induction
on the invariant structure is the partial value of the original
induction. -/
theorem pfpHolds_invStepDef [Nonempty A] (hbound : d.VarBound k)
    (hrels : d.UsesRels S) (houtd : qdepth d.out ≤ k) :
    (d.invStepDef k harity).PFPHolds (InvMap S k A) ↔ d.PFPHolds A := by
  refine exists_congr fun n =>
    and_congr (d.isFixedPt_invStepDef_iff hbound hrels n) ?_
  have hρn : AssignInvariant S A k (d.partStage A n) :=
    d.partStage_invariant hbound hrels n
  have hout2 : ∀ u : Fin k → A,
      ((@Formula.Realize _ (InvMap S k A)
        ((classBlock d.B).structure₁ (L := invLang L k)
          (invAssign S harity (d.partStage A n))) _
        (pebbleCompile (B := d.B) Fin.elim0 (sentenceFin0 d.out) Fin.elim0)
          fun _ => InvMap.mk S u) ↔
        (@Sentence.Realize _ A (d.B.structure₁ (L := L) (d.partStage A n))
          d.out)) := by
    intro u
    have hcomp := realize_pebbleCompile
      (X := invAssign S harity (d.partStage A n)) hρn harity
      (fun i' w => invAssign_mk hρn i' w) (sentenceFin0 d.out) Fin.elim0
      Fin.elim0 (Function.injective_of_subsingleton _) (fun i' j => j.elim0)
      (d.budget_out houtd) (relsIn_sentenceFin0 hrels.2) u
    refine hcomp.trans ?_
    have hxs : (fun j : Fin 0 => u (Fin.elim0 j)) = (default : Fin 0 → A) :=
      Subsingleton.elim _ _
    rw [hxs]
    exact realize_sentenceFin0 (instM := d.B.structure₁ (L := L)
      (d.partStage A n)) d.out default
  have hout1 : (@Sentence.Realize _ (InvMap S k A)
      ((classBlock d.B).structure₁ (L := invLang L k)
        ((d.invStepDef k harity).partStage (InvMap S k A) n))
      (d.invStepDef k harity).out) ↔
      ∃ c : Fin 1 → InvMap S k A,
        (@Formula.Realize _ (InvMap S k A)
          ((classBlock d.B).structure₁ (L := invLang L k)
            (invAssign S harity (d.partStage A n))) _
          (pebbleCompile (B := d.B) Fin.elim0 (sentenceFin0 d.out) Fin.elim0)
            fun _ => c 0) := by
    rw [d.partStage_invStepDef hbound hrels n]
    let := (classBlock d.B).structure₁ (L := invLang L k)
      (invAssign S harity (d.partStage A n))
    have h0 : (@Sentence.Realize _ (InvMap S k A)
        ((classBlock d.B).structure₁ (L := invLang L k)
          (invAssign S harity (d.partStage A n)))
        (d.invStepDef k harity).out) ↔
        ∃ c : Fin 1 → InvMap S k A,
          ((pebbleCompile (B := d.B) Fin.elim0 (sentenceFin0 d.out)
              Fin.elim0).relabel (fun _ => Sum.inr 0)).Realize
            (Sum.elim (default : Empty → InvMap S k A) c) :=
      Formula.realize_iExs
    refine h0.trans (exists_congr fun c => ?_)
    rw [Formula.realize_relabel]
    exact iff_of_eq (congrArg _ (funext fun q => rfl))
  refine hout1.trans ?_
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨u, hu⟩ := InvMap.exists_rep (c 0)
    have hceq : (fun _ : Fin 1 => c 0) = fun _ => InvMap.mk S u := by
      funext q
      rw [← hu]
    rw [hceq] at hc
    exact (hout2 u).mp hc
  · intro hA
    exact ⟨fun _ => InvMap.mk S fun _ => Classical.arbitrary A,
      (hout2 _).mpr hA⟩

end StepDef

end DescriptiveComplexity
