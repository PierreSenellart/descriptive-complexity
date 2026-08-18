/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.PSpace

/-!
# The space-bounded machine problems are in PSPACE

The membership half of the machine bridge for PSPACE. A configuration of a
machine is a state, a head position and a tape, and each of the three *is* a
relation on the universe: the tape is a binary relation (the graph of a
function), the state and the head are unary marks (singletons). So a
configuration is an assignment of a three-variable block
(`DescriptiveComplexity.mBlock`), one step of the machine is a first-order
condition on two consecutive assignments, and acceptance – reachability in the
configuration graph, since `DescriptiveComplexity.TMData.AcceptsSpace` has no step
bound – is a transitive closure over those assignments. That is an SO(TC)
specification on the nose.

This is the same phenomenon as for SUCCINCT-REACH: the problem is the syntactic
image of the logic, so membership is a transcription rather than a construction.
Nothing here plays the role of `DescriptiveComplexity.Problems.Machine.Walk`,
which exists only to cash in the *unary time bound* of the time-bounded model by
indexing a run by the positions; with the bound dropped a run may be
exponentially long and no longer fits in the structure, which is precisely why
the space-bounded problems are SO(TC) rather than `Σ₁`.

The one wrinkle is that an assignment of the block is an arbitrary triple of
relations, while a configuration is a *functional total* tape and two
*singletons*. That is a first-order condition (`DescriptiveComplexity.cfgS`), it
holds of every assignment coming from a configuration, and the transition
sentence demands it of the state it moves to, so every state along an accepting
walk is a configuration.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The formula builders

Kept in a namespace of their own: the shapes below (`wfF`, `stepF`, …) are the
transcription of one machine model into sentences, and their names are the
generic ones the other reduction layers of the catalog also use. -/

namespace SpaceTM

/-! ### Generic sentence shapes

Each builder is parameterized by the relation symbols it reads, so that the
same one serves over the one-copy and the two-copy expansions. -/

section Shapes

variable {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {γ : Type}

/-- The tape is total: every cell holds a symbol. -/
noncomputable def totalF (t : L'.Relations 2) : L'.Formula γ :=
  ((Relations.formula₂ t (Term.var (Sum.inl (Sum.inr 0))) (Term.var (Sum.inr 0))).iExs
    (Fin 1)).iAlls (Fin 1)

/-- The tape is functional: a cell holds at most one symbol. -/
noncomputable def funcF (t : L'.Relations 2) : L'.Formula γ :=
  ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2))).imp
      (Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))))).iAlls (Fin 3)

/-- The mark is inhabited. -/
noncomputable def someF (s : L'.Relations 1) : L'.Formula γ :=
  (Relations.formula₁ s (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- The mark holds of at most one element. -/
noncomputable def uniqF (s : L'.Relations 1) : L'.Formula γ :=
  ((Relations.formula₁ s (Term.var (Sum.inr 0))).imp
    ((Relations.formula₁ s (Term.var (Sum.inr 1))).imp
      (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))).iAlls (Fin 2)

/-- **The assignment is a configuration**: a total functional tape and two
singleton marks. -/
noncomputable def cfgF (t : L'.Relations 2) (s h : L'.Relations 1) : L'.Formula γ :=
  (totalF t ⊓ funcF t) ⊓ ((someF s ⊓ uniqF s) ⊓ (someF h ⊓ uniqF h))

variable {v : γ → M}

@[simp]
theorem realize_totalF (t : L'.Relations 2) :
    (totalF (γ := γ) t).Realize v ↔ ∀ p : M, ∃ a : M, RelMap t ![p, a] := by
  rw [totalF]
  simp only [Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h p
    obtain ⟨i, hi⟩ := h fun _ => p
    exact ⟨i 0, hi⟩
  · intro h i
    obtain ⟨a, ha⟩ := h (i 0)
    exact ⟨fun _ => a, ha⟩

@[simp]
theorem realize_funcF (t : L'.Relations 2) :
    (funcF (γ := γ) t).Realize v ↔ ∀ p a b : M, RelMap t ![p, a] → RelMap t ![p, b] → a = b := by
  rw [funcF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h p a b => h ![p, a, b], fun h i => h (i 0) (i 1) (i 2)⟩

@[simp]
theorem realize_someF (s : L'.Relations 1) :
    (someF (γ := γ) s).Realize v ↔ ∃ q : M, RelMap s ![q] := by
  rw [someF]
  simp only [Formula.realize_iExs, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩

@[simp]
theorem realize_uniqF (s : L'.Relations 1) :
    (uniqF (γ := γ) s).Realize v ↔ ∀ q q' : M, RelMap s ![q] → RelMap s ![q'] → q = q' := by
  rw [uniqF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h q q' => h ![q, q'], fun h i => h (i 0) (i 1)⟩

@[simp]
theorem realize_cfgF (t : L'.Relations 2) (s h : L'.Relations 1) :
    (cfgF (γ := γ) t s h).Realize v ↔
      ((∀ p : M, ∃ a : M, RelMap t ![p, a]) ∧
          (∀ p a b : M, RelMap t ![p, a] → RelMap t ![p, b] → a = b)) ∧
        (((∃ q : M, RelMap s ![q]) ∧ ∀ q q' : M, RelMap s ![q] → RelMap s ![q'] → q = q') ∧
          ((∃ p : M, RelMap h ![p]) ∧ ∀ p p' : M, RelMap h ![p] → RelMap h ![p'] → p = p')) := by
  rw [cfgF]
  simp only [Formula.realize_inf, realize_totalF, realize_funcF, realize_someF, realize_uniqF]

/-! #### The guarded conjuncts -/

/-- Everything the first mark holds of, the second holds of too. -/
noncomputable def markImpF (s r : L'.Relations 1) : L'.Formula γ :=
  ((Relations.formula₁ s (Term.var (Sum.inr 0))).imp
    (Relations.formula₁ r (Term.var (Sum.inr 0)))).iAlls (Fin 1)

/-- The marked position is a least position. -/
noncomputable def minPosF (h posn : L'.Relations 1) (le : L'.Relations 2) : L'.Formula γ :=
  ((Relations.formula₁ h (Term.var (Sum.inr 0))).imp
    (Relations.formula₁ posn (Term.var (Sum.inr 0)) ⊓
      ((Relations.formula₁ posn (Term.var (Sum.inr 0))).imp
          (Relations.formula₂ le (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr 0)))).iAlls (Fin 1))).iAlls (Fin 1)

/-- The tape is an initial tape: each cell holds its input symbol where the
input is defined, and the blank elsewhere. -/
noncomputable def initTapeF (t inp : L'.Relations 2) (blank : L'.Relations 1) :
    L'.Formula γ :=
  ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    (Relations.formula₂ inp (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊔
      (Formula.iAlls (Fin 1) (∼(Relations.formula₂ inp (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr 0)))) ⊓
        Relations.formula₁ blank (Term.var (Sum.inr 1))))).iAlls (Fin 2)

@[simp]
theorem realize_markImpF (s r : L'.Relations 1) :
    (markImpF (γ := γ) s r).Realize v ↔ ∀ q : M, RelMap s ![q] → RelMap r ![q] := by
  rw [markImpF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Term.realize_var, Sum.elim_inr]
  exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩

@[simp]
theorem realize_minPosF (h posn : L'.Relations 1) (le : L'.Relations 2) :
    (minPosF (γ := γ) h posn le).Realize v ↔
      ∀ p : M, RelMap h ![p] →
        MinPos (fun x y => RelMap le ![x, y]) (fun x => RelMap posn ![x]) p := by
  rw [minPosF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    MinPos]
  constructor
  · intro hh p hp
    obtain ⟨h1, h2⟩ := hh (fun _ => p) hp
    exact ⟨h1, fun q hq => h2 (fun _ => q) hq⟩
  · intro hh i hi
    obtain ⟨h1, h2⟩ := hh (i 0) hi
    exact ⟨h1, fun j hj => h2 (j 0) hj⟩

@[simp]
theorem realize_initTapeF (t inp : L'.Relations 2) (blank : L'.Relations 1) :
    (initTapeF (γ := γ) t inp blank).Realize v ↔
      ∀ p a : M, RelMap t ![p, a] →
        (RelMap inp ![p, a] ∨ ((∀ b : M, ¬RelMap inp ![p, b]) ∧ RelMap blank ![a])) := by
  rw [initTapeF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_sup,
    Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hh p a hpa
    refine (hh ![p, a] hpa).imp id fun hb => ⟨fun b => ?_, hb.2⟩
    exact hb.1 fun _ => b
  · intro hh i hi
    refine (hh (i 0) (i 1) hi).imp id fun hb => ⟨fun j => hb.1 (j 0), hb.2⟩

/-! #### The conjuncts of the transition sentence -/

/-- The transition has the marked element as its source (or destination). -/
noncomputable def markArgF (r : L'.Relations 2) (s : L'.Relations 1) (τ : L'.Term γ) :
    L'.Formula γ :=
  ((Relations.formula₁ s (Term.var (Sum.inr 0))).imp
    (Relations.formula₂ r (τ.relabel Sum.inl) (Term.var (Sum.inr 0)))).iAlls (Fin 1)

/-- The transition reads (or writes) the symbol held by the marked cell. -/
noncomputable def cellArgF (r : L'.Relations 2) (h : L'.Relations 1) (t : L'.Relations 2)
    (τ : L'.Term γ) : L'.Formula γ :=
  ((Relations.formula₁ h (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
      (Relations.formula₂ r (τ.relabel Sum.inl) (Term.var (Sum.inr 1))))).iAlls (Fin 2)

/-- Cells other than the marked one hold the same symbol before and after. -/
noncomputable def frameF (t t' : L'.Relations 2) (h : L'.Relations 1) : L'.Formula γ :=
  Formula.iAlls (Fin 2) ((∼(Relations.formula₁ h (Term.var (Sum.inr 0)))).imp
    (((Relations.formula₂ t' (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
        (Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))) ⊓
      ((Relations.formula₂ t (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
        (Relations.formula₂ t' (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))))

/-- `y` is the position immediately after `x`. -/
noncomputable def succPosF (le : L'.Relations 2) (posn : L'.Relations 1) (x y : L'.Term γ) :
    L'.Formula γ :=
  ((Relations.formula₁ posn x ⊓ Relations.formula₁ posn y) ⊓
      (Relations.formula₂ le x y ⊓ ∼(Term.equal x y))) ⊓
    ((Relations.formula₁ posn (Term.var (Sum.inr 0))).imp
      ((Relations.formula₂ le (x.relabel Sum.inl) (Term.var (Sum.inr 0))).imp
        ((Relations.formula₂ le (Term.var (Sum.inr 0)) (y.relabel Sum.inl)).imp
          (Term.equal (Term.var (Sum.inr 0)) (x.relabel Sum.inl) ⊔
            Term.equal (Term.var (Sum.inr 0)) (y.relabel Sum.inl))))).iAlls (Fin 1)

/-- The head moves to the neighbouring position in the direction the transition
names. -/
noncomputable def moveF (right h h' posn : L'.Relations 1) (le : L'.Relations 2)
    (τ : L'.Term γ) : L'.Formula γ :=
  (Relations.formula₁ right τ ⊓
      ((Relations.formula₁ h (Term.var (Sum.inr 0))).imp
        ((Relations.formula₁ h' (Term.var (Sum.inr 1))).imp
          (succPosF le posn (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))).iAlls (Fin 2)) ⊔
    (∼(Relations.formula₁ right τ) ⊓
      ((Relations.formula₁ h (Term.var (Sum.inr 0))).imp
        ((Relations.formula₁ h' (Term.var (Sum.inr 1))).imp
          (succPosF le posn (Term.var (Sum.inr 1)) (Term.var (Sum.inr 0))))).iAlls (Fin 2))

@[simp]
theorem realize_markArgF (r : L'.Relations 2) (s : L'.Relations 1) (τ : L'.Term γ) :
    (markArgF r s τ).Realize v ↔
      ∀ q : M, RelMap s ![q] → RelMap r ![τ.realize v, q] := by
  rw [markArgF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl,
    Sum.elim_inr]
  exact ⟨fun h q => h fun _ => q, fun h i => h (i 0)⟩

@[simp]
theorem realize_cellArgF (r : L'.Relations 2) (h : L'.Relations 1) (t : L'.Relations 2)
    (τ : L'.Term γ) :
    (cellArgF r h t τ).Realize v ↔
      ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap r ![τ.realize v, a] := by
  rw [cellArgF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl,
    Sum.elim_inr]
  exact ⟨fun hh p a => hh ![p, a], fun hh i => hh (i 0) (i 1)⟩

@[simp]
theorem realize_frameF (t t' : L'.Relations 2) (h : L'.Relations 1) :
    (frameF t t' h).Realize v ↔
      ∀ p a : M, ¬RelMap h ![p] → (RelMap t' ![p, a] ↔ RelMap t ![p, a]) := by
  rw [frameF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr]
  constructor
  · intro hh p a hp
    exact ⟨(hh ![p, a] hp).1, (hh ![p, a] hp).2⟩
  · intro hh i hi
    exact ⟨(hh (i 0) (i 1) hi).mp, (hh (i 0) (i 1) hi).mpr⟩

@[simp]
theorem realize_succPosF (le : L'.Relations 2) (posn : L'.Relations 1) (x y : L'.Term γ) :
    (succPosF le posn x y).Realize v ↔
      SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a])
        (x.realize v) (y.realize v) := by
  rw [succPosF, SuccPos]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_sup, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Term.realize_relabel, Sum.elim_comp_inl,
    Sum.elim_inr, ne_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, fun r hr hxr hry => h5 (fun _ => r) hr hxr hry⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, fun i hi hxi hiy => h5 (i 0) hi hxi hiy⟩

@[simp]
theorem realize_moveF (right h h' posn : L'.Relations 1) (le : L'.Relations 2)
    (τ : L'.Term γ) :
    (moveF right h h' posn le τ).Realize v ↔
      ((RelMap right ![τ.realize v] ∧ ∀ p p' : M, RelMap h ![p] → RelMap h' ![p'] →
          SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p p') ∨
        (¬RelMap right ![τ.realize v] ∧ ∀ p p' : M, RelMap h ![p] → RelMap h' ![p'] →
          SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p' p)) := by
  rw [moveF]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁, realize_succPosF,
    Term.realize_var, Sum.elim_inr]
  exact or_congr (and_congr Iff.rfl ⟨fun hh p p' => hh ![p, p'], fun hh i => hh (i 0) (i 1)⟩)
    (and_congr Iff.rfl ⟨fun hh p p' => hh ![p, p'], fun hh i => hh (i 0) (i 1)⟩)

/-! #### Well-formedness -/

/-- The relation is a linear order. -/
noncomputable def linOrdF (le : L'.Relations 2) : L'.Formula γ :=
  ((Relations.formula₂ le (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).iAlls (Fin 1) ⊓
      ((Relations.formula₂ le (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
        ((Relations.formula₂ le (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
          (Relations.formula₂ le (Term.var (Sum.inr 0))
            (Term.var (Sum.inr 2))))).iAlls (Fin 3)) ⊓
    (((Relations.formula₂ le (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
        ((Relations.formula₂ le (Term.var (Sum.inr 1)) (Term.var (Sum.inr 0))).imp
          (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))).iAlls (Fin 2) ⊓
      (Relations.formula₂ le (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊔
        Relations.formula₂ le (Term.var (Sum.inr 1)) (Term.var (Sum.inr 0))).iAlls (Fin 2))

/-- **Well-formedness of the instance**, as a sentence: the order is linear,
there is a position, the input is functional, and there is exactly one blank. -/
noncomputable def wfF (le inp : L'.Relations 2) (posn blank : L'.Relations 1) :
    L'.Formula γ :=
  linOrdF le ⊓ (someF posn ⊓ (funcF inp ⊓ (someF blank ⊓ uniqF blank)))

@[simp]
theorem realize_linOrdF (le : L'.Relations 2) :
    (linOrdF (γ := γ) le).Realize v ↔ IsLinOrd (fun a b : M => RelMap le ![a, b]) := by
  rw [linOrdF, IsLinOrd]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, and_assoc]
  refine and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a b c => h ![a, b, c], fun h i => h (i 0) (i 1) (i 2)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩
  · exact ⟨fun h a b => h ![a, b], fun h i => h (i 0) (i 1)⟩

@[simp]
theorem realize_wfF (le inp : L'.Relations 2) (posn blank : L'.Relations 1) :
    (wfF (γ := γ) le inp posn blank).Realize v ↔
      (IsLinOrd (fun a b : M => RelMap le ![a, b]) ∧
        ((∃ p : M, RelMap posn ![p]) ∧
          ((∀ p a b : M, RelMap inp ![p, a] → RelMap inp ![p, b] → a = b) ∧
            ((∃ b : M, RelMap blank ![b]) ∧
              ∀ a b : M, RelMap blank ![a] → RelMap blank ![b] → a = b)))) := by
  rw [wfF]
  simp only [Formula.realize_inf, realize_linOrdF, realize_someF, realize_funcF, realize_uniqF]

/-! #### The transition sentence -/

/-- **One step of the machine**, as a condition on two consecutive
assignments. -/
noncomputable def stepF (tr right posn : L'.Relations 1) (src rd dst wr le : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (s' h' : L'.Relations 1)
    (t' : L'.Relations 2) : L'.Formula γ :=
  Formula.iExs (Fin 1)
    ((Relations.formula₁ tr (Term.var (Sum.inr 0)) ⊓
        (markArgF src s (Term.var (Sum.inr 0)) ⊓ cellArgF rd h t (Term.var (Sum.inr 0)))) ⊓
      ((markArgF dst s' (Term.var (Sum.inr 0)) ⊓ cellArgF wr h t' (Term.var (Sum.inr 0))) ⊓
        (frameF t t' h ⊓ moveF right h h' posn le (Term.var (Sum.inr 0)))))

@[simp]
theorem realize_stepF (tr right posn : L'.Relations 1) (src rd dst wr le : L'.Relations 2)
    (s h : L'.Relations 1) (t : L'.Relations 2) (s' h' : L'.Relations 1) (t' : L'.Relations 2) :
    (stepF (γ := γ) tr right posn src rd dst wr le s h t s' h' t').Realize v ↔
      ∃ τ : M, (RelMap tr ![τ] ∧
          ((∀ q : M, RelMap s ![q] → RelMap src ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t ![p, a] → RelMap rd ![τ, a])) ∧
        (((∀ q : M, RelMap s' ![q] → RelMap dst ![τ, q]) ∧
            ∀ p a : M, RelMap h ![p] → RelMap t' ![p, a] → RelMap wr ![τ, a]) ∧
          ((∀ p a : M, ¬RelMap h ![p] → (RelMap t' ![p, a] ↔ RelMap t ![p, a])) ∧
            ((RelMap right ![τ] ∧ ∀ p p' : M, RelMap h ![p] → RelMap h' ![p'] →
                SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p p') ∨
              (¬RelMap right ![τ] ∧ ∀ p p' : M, RelMap h ![p] → RelMap h' ![p'] →
                SuccPos (fun a b => RelMap le ![a, b]) (fun a => RelMap posn ![a]) p' p)))) := by
  rw [stepF]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁,
    realize_markArgF, realize_cellArgF, realize_frameF, realize_moveF, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨τ, hτ⟩ => ⟨fun _ => τ, hτ⟩⟩

/-- At most one transition applies in a given state on a given symbol. -/
noncomputable def trUniqF (tr : L'.Relations 1) (src rd : L'.Relations 2) : L'.Formula γ :=
  Formula.iAlls (Fin 4)
    ((Relations.formula₁ tr (Term.var (Sum.inr 0))).imp
      ((Relations.formula₁ tr (Term.var (Sum.inr 1))).imp
        ((Relations.formula₂ src (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2))).imp
          ((Relations.formula₂ src (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
            ((Relations.formula₂ rd (Term.var (Sum.inr 0)) (Term.var (Sum.inr 3))).imp
              ((Relations.formula₂ rd (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3))).imp
                (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))))))))

/-- **Determinism of the instance**, as a sentence. -/
noncomputable def detF (tr start : L'.Relations 1) (src rd dst wr : L'.Relations 2) :
    L'.Formula γ :=
  uniqF start ⊓ (trUniqF tr src rd ⊓ (funcF dst ⊓ funcF wr))

@[simp]
theorem realize_trUniqF (tr : L'.Relations 1) (src rd : L'.Relations 2) :
    (trUniqF (γ := γ) tr src rd).Realize v ↔
      ∀ τ τ' q a : M, RelMap tr ![τ] → RelMap tr ![τ'] → RelMap src ![τ, q] →
        RelMap src ![τ', q] → RelMap rd ![τ, a] → RelMap rd ![τ', a] → τ = τ' := by
  rw [trUniqF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
    Formula.realize_rel₂, Formula.realize_equal, Term.realize_var, Sum.elim_inr]
  exact ⟨fun h τ τ' q a => h ![τ, τ', q, a], fun h i => h (i 0) (i 1) (i 2) (i 3)⟩

@[simp]
theorem realize_detF (tr start : L'.Relations 1) (src rd dst wr : L'.Relations 2) :
    (detF (γ := γ) tr start src rd dst wr).Realize v ↔
      ((∀ q q' : M, RelMap start ![q] → RelMap start ![q'] → q = q') ∧
        ((∀ τ τ' q a : M, RelMap tr ![τ] → RelMap tr ![τ'] → RelMap src ![τ, q] →
            RelMap src ![τ', q] → RelMap rd ![τ, a] → RelMap rd ![τ', a] → τ = τ') ∧
          ((∀ τ q q' : M, RelMap dst ![τ, q] → RelMap dst ![τ, q'] → q = q') ∧
            ∀ τ a a' : M, RelMap wr ![τ, a] → RelMap wr ![τ, a'] → a = a'))) := by
  rw [detF]
  simp only [Formula.realize_inf, realize_uniqF, realize_trUniqF, realize_funcF]

end Shapes

/-! ### The block and the specification -/

section Spec

/-- The block whose assignments are the configurations: the tape as a binary
relation variable, the state and the head as unary marks. -/
abbrev mBlock : SOBlock where
  ι := Option Bool
  arity := fun i => match i with | none => 2 | some _ => 1

/-- The symbol for the tape. -/
def mSymT : mBlock.lang.Relations 2 := ⟨none, rfl⟩

/-- The symbol for the state. -/
def mSymS : mBlock.lang.Relations 1 := ⟨some false, rfl⟩

/-- The symbol for the head. -/
def mSymH : mBlock.lang.Relations 1 := ⟨some true, rfl⟩

/-- The ordered expansion of the machine vocabulary. -/
abbrev mBase : Language := Language.turing.sum Language.order

/-- The vocabulary of a one-copy expansion by the block. -/
abbrev mLang₁ : Language := mBase.sum mBlock.lang

/-- The vocabulary of a two-copy expansion by the block. -/
abbrev mLang₂ : Language := mLang₁.sum mBlock.lang

/-- A machine symbol in the one-copy expansion. -/
abbrev mIn₁ {n : ℕ} (r : Language.turing.Relations n) : mLang₁.Relations n := Sum.inl (Sum.inl r)

/-- The tape of the state, in the one-copy expansion. -/
abbrev mT₁ : mLang₁.Relations 2 := Sum.inr mSymT

/-- The state mark, in the one-copy expansion. -/
abbrev mS₁ : mLang₁.Relations 1 := Sum.inr mSymS

/-- The head mark, in the one-copy expansion. -/
abbrev mH₁ : mLang₁.Relations 1 := Sum.inr mSymH

/-- A machine symbol in the two-copy expansion. -/
abbrev mIn₂ {n : ℕ} (r : Language.turing.Relations n) : mLang₂.Relations n :=
  Sum.inl (Sum.inl (Sum.inl r))

/-- The tape of the current state. -/
abbrev mTc₂ : mLang₂.Relations 2 := Sum.inl (Sum.inr mSymT)

/-- The state mark of the current state. -/
abbrev mSc₂ : mLang₂.Relations 1 := Sum.inl (Sum.inr mSymS)

/-- The head mark of the current state. -/
abbrev mHc₂ : mLang₂.Relations 1 := Sum.inl (Sum.inr mSymH)

/-- The tape of the next state. -/
abbrev mTn₂ : mLang₂.Relations 2 := Sum.inr mSymT

/-- The state mark of the next state. -/
abbrev mSn₂ : mLang₂.Relations 1 := Sum.inr mSymS

/-- The head mark of the next state. -/
abbrev mHn₂ : mLang₂.Relations 1 := Sum.inr mSymH

/-- **The specification**: the states are the configurations, the transition is
one step of the machine, the starting states are the initial configurations of a
well-formed instance and the accepting ones are those in an accepting state. -/
noncomputable def mSpec : SOTCSpec Language.turing where
  B := mBlock
  step :=
    stepF (mIn₂ tmTr) (mIn₂ tmRight) (mIn₂ tmPosn) (mIn₂ tmSrc) (mIn₂ tmRead) (mIn₂ tmDst)
        (mIn₂ tmWrite) (mIn₂ tmLe) mSc₂ mHc₂ mTc₂ mSn₂ mHn₂ mTn₂ ⊓
      cfgF mTn₂ mSn₂ mHn₂
  src :=
    wfF (mIn₁ tmLe) (mIn₁ tmInp) (mIn₁ tmPosn) (mIn₁ tmBlank) ⊓
      (cfgF mT₁ mS₁ mH₁ ⊓
        (markImpF mS₁ (mIn₁ tmStart) ⊓
          (minPosF mH₁ (mIn₁ tmPosn) (mIn₁ tmLe) ⊓
            initTapeF mT₁ (mIn₁ tmInp) (mIn₁ tmBlank))))
  tgt := markImpF mS₁ (mIn₁ tmAcc)

/-- **The deterministic specification**: the same walk, with determinism of the
instance demanded of the starting states. -/
noncomputable def mSpecDet : SOTCSpec Language.turing where
  B := mBlock
  step := mSpec.step
  src := detF (mIn₁ tmTr) (mIn₁ tmStart) (mIn₁ tmSrc) (mIn₁ tmRead) (mIn₁ tmDst)
      (mIn₁ tmWrite) ⊓ mSpec.src
  tgt := mSpec.tgt

end Spec

/-! ### Reading a state back as a configuration -/

section Reading

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

/-- The tape held by a state of the walk. -/
def mTape (ρ : mBlock.Assignment A) (p a : A) : Prop := ρ none ![p, a]

/-- The state mark held by a state of the walk. -/
def mState (ρ : mBlock.Assignment A) (q : A) : Prop := ρ (some false) ![q]

/-- The head mark held by a state of the walk. -/
def mHead (ρ : mBlock.Assignment A) (p : A) : Prop := ρ (some true) ![p]

/-- A state of the walk *is* a configuration: its tape is total and functional
and its two marks are singletons. -/
def IsCfgOn (ρ : mBlock.Assignment A) : Prop :=
  ((∀ p : A, ∃ a : A, mTape ρ p a) ∧ (∀ p a b : A, mTape ρ p a → mTape ρ p b → a = b)) ∧
    (((∃ q : A, mState ρ q) ∧ ∀ q q' : A, mState ρ q → mState ρ q' → q = q') ∧
      ((∃ p : A, mHead ρ p) ∧ ∀ p p' : A, mHead ρ p → mHead ρ p' → p = p'))

/-- The state of the walk that a configuration is. -/
def cfgAssign (c : Config A) : mBlock.Assignment A
  | none => fun x => c.tape (x 0) = x 1
  | some false => fun x => x 0 = c.state
  | some true => fun x => x 0 = c.head

omit [Language.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mTape_cfgAssign (c : Config A) (p a : A) :
    mTape (cfgAssign c) p a ↔ c.tape p = a := Iff.rfl

omit [Language.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mState_cfgAssign (c : Config A) (q : A) :
    mState (cfgAssign c) q ↔ q = c.state := Iff.rfl

omit [Language.turing.Structure A] [LinearOrder A] in
@[simp]
theorem mHead_cfgAssign (c : Config A) (p : A) :
    mHead (cfgAssign c) p ↔ p = c.head := Iff.rfl

omit [Language.turing.Structure A] [LinearOrder A] in
theorem isCfgOn_cfgAssign (c : Config A) : IsCfgOn (cfgAssign c) :=
  ⟨⟨fun p => ⟨c.tape p, rfl⟩, fun _ _ _ ha hb => ha.symm.trans hb⟩,
    ⟨⟨c.state, rfl⟩, fun _ _ hq hq' => hq.trans hq'.symm⟩,
      ⟨c.head, rfl⟩, fun _ _ hp hp' => hp.trans hp'.symm⟩

/-- The configuration a state of the walk is, when it is one. -/
noncomputable def cfgOf {ρ : mBlock.Assignment A} (h : IsCfgOn ρ) : Config A where
  state := h.2.1.1.choose
  head := h.2.2.1.choose
  tape := fun p => (h.1.1 p).choose

omit [Language.turing.Structure A] [LinearOrder A] in
theorem mState_cfgOf {ρ : mBlock.Assignment A} (h : IsCfgOn ρ) (q : A) :
    mState ρ q ↔ q = (cfgOf h).state :=
  ⟨fun hq => h.2.1.2 q _ hq h.2.1.1.choose_spec, fun hq => hq ▸ h.2.1.1.choose_spec⟩

omit [Language.turing.Structure A] [LinearOrder A] in
theorem mHead_cfgOf {ρ : mBlock.Assignment A} (h : IsCfgOn ρ) (p : A) :
    mHead ρ p ↔ p = (cfgOf h).head :=
  ⟨fun hp => h.2.2.2 p _ hp h.2.2.1.choose_spec, fun hp => hp ▸ h.2.2.1.choose_spec⟩

omit [Language.turing.Structure A] [LinearOrder A] in
theorem mTape_cfgOf {ρ : mBlock.Assignment A} (h : IsCfgOn ρ) (p a : A) :
    mTape ρ p a ↔ (cfgOf h).tape p = a :=
  ⟨fun ha => h.1.2 p _ _ (h.1.1 p).choose_spec ha, fun ha => ha ▸ (h.1.1 p).choose_spec⟩

/-! #### The symbols, read back -/

theorem relMap_mIn₁ {n : ℕ} (ρ : mBlock.Assignment A) (r : Language.turing.Relations n)
    (w : Fin n → A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) n (mIn₁ r) w ↔ RelMap r w := Iff.rfl

theorem relMap_mT₁ (ρ : mBlock.Assignment A) (p a : A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) 2 mT₁ ![p, a] ↔ mTape ρ p a := Iff.rfl

theorem relMap_mS₁ (ρ : mBlock.Assignment A) (q : A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) 1 mS₁ ![q] ↔ mState ρ q := Iff.rfl

theorem relMap_mH₁ (ρ : mBlock.Assignment A) (p : A) :
    @RelMap mLang₁ A (mBlock.structure₁ (L := mBase) ρ) 1 mH₁ ![p] ↔ mHead ρ p := Iff.rfl

theorem relMap_mIn₂ {n : ℕ} (ρ σ : mBlock.Assignment A) (r : Language.turing.Relations n)
    (w : Fin n → A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) n (mIn₂ r) w ↔ RelMap r w := Iff.rfl

theorem relMap_mTc₂ (ρ σ : mBlock.Assignment A) (p a : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 2 mTc₂ ![p, a] ↔ mTape ρ p a := Iff.rfl

theorem relMap_mSc₂ (ρ σ : mBlock.Assignment A) (q : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 1 mSc₂ ![q] ↔ mState ρ q := Iff.rfl

theorem relMap_mHc₂ (ρ σ : mBlock.Assignment A) (p : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 1 mHc₂ ![p] ↔ mHead ρ p := Iff.rfl

theorem relMap_mTn₂ (ρ σ : mBlock.Assignment A) (p a : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 2 mTn₂ ![p, a] ↔ mTape σ p a := Iff.rfl

theorem relMap_mSn₂ (ρ σ : mBlock.Assignment A) (q : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 1 mSn₂ ![q] ↔ mState σ q := Iff.rfl

theorem relMap_mHn₂ (ρ σ : mBlock.Assignment A) (p : A) :
    @RelMap mLang₂ A (mBlock.structure₂ (L := mBase) ρ σ) 1 mHn₂ ![p] ↔ mHead σ p := Iff.rfl

theorem mRealize_inf₁ (ρ : mBlock.Assignment A) (φ ψ : mLang₁.Sentence) :
    @Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) (φ ⊓ ψ) ↔
      (@Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) φ ∧
        @Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) ψ) :=
  letI := mBlock.structure₁ (L := mBase) ρ
  Formula.realize_inf

/-- A state of the walk *represents* a configuration. -/
def Represents (ρ : mBlock.Assignment A) (c : Config A) : Prop :=
  (∀ p a : A, mTape ρ p a ↔ c.tape p = a) ∧ (∀ q : A, mState ρ q ↔ q = c.state) ∧
    ∀ p : A, mHead ρ p ↔ p = c.head

omit [Language.turing.Structure A] [LinearOrder A] in
theorem represents_cfgAssign (c : Config A) : Represents (cfgAssign c) c :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

omit [Language.turing.Structure A] [LinearOrder A] in
theorem exists_represents {ρ : mBlock.Assignment A} (h : IsCfgOn ρ) : ∃ c, Represents ρ c :=
  ⟨cfgOf h, fun p a => mTape_cfgOf h p a, fun q => mState_cfgOf h q, fun p => mHead_cfgOf h p⟩

end Reading

/-! ### Correctness -/

section Correct

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

/-- One step of the machine, read off two states of the walk. -/
def StepOn (ρ σ : mBlock.Assignment A) : Prop :=
  ∃ τ : A, ((tmData A).Tr τ ∧
      ((∀ q : A, mState ρ q → (tmData A).Src τ q) ∧
        ∀ p a : A, mHead ρ p → mTape ρ p a → (tmData A).Read τ a)) ∧
    (((∀ q : A, mState σ q → (tmData A).Dst τ q) ∧
        ∀ p a : A, mHead ρ p → mTape σ p a → (tmData A).Write τ a) ∧
      ((∀ p a : A, ¬mHead ρ p → (mTape σ p a ↔ mTape ρ p a)) ∧
        (((tmData A).Right τ ∧ ∀ p p' : A, mHead ρ p → mHead σ p' →
            SuccPos (tmData A).Le (tmData A).Posn p p') ∨
          (¬(tmData A).Right τ ∧ ∀ p p' : A, mHead ρ p → mHead σ p' →
            SuccPos (tmData A).Le (tmData A).Posn p' p))))

theorem mSpec_isSrc_iff (ρ : mBlock.Assignment A) :
    mSpec.IsSrc ρ ↔ ((tmData A).WellFormed ∧ (IsCfgOn ρ ∧
      ((∀ q : A, mState ρ q → (tmData A).Start q) ∧
        ((∀ p : A, mHead ρ p → MinPos (tmData A).Le (tmData A).Posn p) ∧
          ∀ p a : A, mTape ρ p a → (tmData A).InitTape p a)))) := by
  change @Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) mSpec.src ↔ _
  simp only [mSpec, Sentence.Realize, Formula.realize_inf, realize_wfF, realize_cfgF,
    realize_markImpF, realize_minPosF, realize_initTapeF, relMap_mIn₁, relMap_mT₁,
    relMap_mS₁, relMap_mH₁]
  exact Iff.rfl

theorem mSpec_isTgt_iff (ρ : mBlock.Assignment A) :
    mSpec.IsTgt ρ ↔ ∀ q : A, mState ρ q → (tmData A).Acc q := by
  change @Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) mSpec.tgt ↔ _
  simp only [mSpec, Sentence.Realize, realize_markImpF, relMap_mIn₁, relMap_mS₁]
  exact Iff.rfl

theorem mSpec_step_iff (ρ σ : mBlock.Assignment A) :
    mSpec.Step ρ σ ↔ (StepOn ρ σ ∧ IsCfgOn σ) := by
  change @Sentence.Realize _ A (mBlock.structure₂ (L := mBase) ρ σ) mSpec.step ↔ _
  simp only [mSpec, Sentence.Realize, Formula.realize_inf, realize_stepF, realize_cfgF,
    relMap_mIn₂, relMap_mTc₂, relMap_mSc₂, relMap_mHc₂, relMap_mTn₂, relMap_mSn₂, relMap_mHn₂]
  exact Iff.rfl

omit [LinearOrder A] in
/-- **The transition sentence is one step of the machine**, on states that
represent configurations. -/
theorem stepOn_iff {ρ σ : mBlock.Assignment A} {c d : Config A}
    (hρ : Represents ρ c) (hσ : Represents σ d) :
    StepOn ρ σ ↔ (tmData A).Step c d := by
  rw [StepOn, TMData.Step]
  refine exists_congr fun τ => ?_
  constructor
  · rintro ⟨⟨htr, hsrc, hread⟩, ⟨hdst, hwr⟩, hframe, hmove⟩
    refine ⟨htr, hsrc c.state ((hρ.2.1 _).mpr rfl),
      hread c.head (c.tape c.head) ((hρ.2.2 _).mpr rfl) ((hρ.1 _ _).mpr rfl),
      hdst d.state ((hσ.2.1 _).mpr rfl),
      hwr c.head (d.tape c.head) ((hρ.2.2 _).mpr rfl) ((hσ.1 _ _).mpr rfl), fun p hp => ?_, ?_⟩
    · have := (hframe p (d.tape p) fun hh => hp ((hρ.2.2 p).mp hh)).mp ((hσ.1 p _).mpr rfl)
      exact ((hρ.1 p _).mp this).symm
    · exact hmove.imp
        (fun hh => ⟨hh.1, hh.2 c.head d.head ((hρ.2.2 _).mpr rfl) ((hσ.2.2 _).mpr rfl)⟩)
        (fun hh => ⟨hh.1, hh.2 c.head d.head ((hρ.2.2 _).mpr rfl) ((hσ.2.2 _).mpr rfl)⟩)
  · rintro ⟨htr, hsrc, hread, hdst, hwr, hframe, hmove⟩
    refine ⟨⟨htr, fun q hq => (hρ.2.1 q).mp hq ▸ hsrc,
        fun p a hp ha => ((hρ.2.2 p).mp hp ▸ (hρ.1 p a).mp ha : c.tape c.head = a) ▸ hread⟩,
      ⟨fun q hq => (hσ.2.1 q).mp hq ▸ hdst,
        fun p a hp ha => ?_⟩, fun p a hp => ?_, ?_⟩
    · have hpc : p = c.head := (hρ.2.2 p).mp hp
      exact (hpc ▸ (hσ.1 p a).mp ha : d.tape c.head = a) ▸ hwr
    · have hne : p ≠ c.head := fun hh => hp ((hρ.2.2 p).mpr hh)
      rw [hσ.1 p a, hρ.1 p a, hframe p hne]
    · exact hmove.imp
        (fun hh => ⟨hh.1, fun p p' hp hp' =>
          (hρ.2.2 p).mp hp ▸ (hσ.2.2 p').mp hp' ▸ hh.2⟩)
        (fun hh => ⟨hh.1, fun p p' hp hp' =>
          (hρ.2.2 p).mp hp ▸ (hσ.2.2 p').mp hp' ▸ hh.2⟩)

/-- Every state reachable from one representing a configuration represents one
too, and the walk is a run of the machine. -/
theorem mSpec_reach {ρ σ : mBlock.Assignment A} (h : mSpec.Reach ρ σ) {c : Config A}
    (hρ : Represents ρ c) :
    ∃ d : Config A, Represents σ d ∧ Relation.ReflTransGen (tmData A).Step c d := by
  induction h with
  | refl => exact ⟨c, hρ, Relation.ReflTransGen.refl⟩
  | @tail x y _ hxy ih =>
    obtain ⟨d, hd, hreach⟩ := ih
    obtain ⟨hstep, hcfg⟩ := (mSpec_step_iff x y).mp hxy
    obtain ⟨e, he⟩ := exists_represents hcfg
    exact ⟨e, he, hreach.tail ((stepOn_iff hd he).mp hstep)⟩

theorem mSpec_reach_of {c d : Config A} (h : Relation.ReflTransGen (tmData A).Step c d) :
    mSpec.Reach (cfgAssign c) (cfgAssign d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
    exact ih.tail ((mSpec_step_iff _ _).mpr
      ⟨(stepOn_iff (represents_cfgAssign x) (represents_cfgAssign y)).mpr hxy,
        isCfgOn_cfgAssign y⟩)

/-- **The specification is correct**: its walk accepts exactly the well-formed
instances whose machine accepts in bounded space. -/
theorem mSpec_accepts_iff :
    mSpec.Accepts A ↔ ((tmData A).WellFormed ∧ (tmData A).AcceptsSpace) := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    obtain ⟨hwf, hcfg, hstart, hmin, hinit⟩ := (mSpec_isSrc_iff ρ).mp hsrc
    obtain ⟨c, hc⟩ := exists_represents hcfg
    obtain ⟨d, hd, hr⟩ := mSpec_reach hreach hc
    exact ⟨hwf, c, d, ⟨hstart c.state ((hc.2.1 _).mpr rfl), hmin c.head ((hc.2.2 _).mpr rfl),
      fun p => hinit p (c.tape p) ((hc.1 _ _).mpr rfl)⟩, hr,
      (mSpec_isTgt_iff σ).mp htgt d.state ((hd.2.1 _).mpr rfl)⟩
  · rintro ⟨hwf, c, d, hinit, hr, hacc⟩
    exact ⟨cfgAssign c, cfgAssign d, (mSpec_isSrc_iff _).mpr ⟨hwf, isCfgOn_cfgAssign c,
      fun q hq => ((mState_cfgAssign c q).mp hq) ▸ hinit.1,
      fun p hp => ((mHead_cfgAssign c p).mp hp) ▸ hinit.2.1,
      fun p a ha => ((mTape_cfgAssign c p a).mp ha) ▸ hinit.2.2 p⟩,
      (mSpec_isTgt_iff _).mpr fun q hq => ((mState_cfgAssign d q).mp hq) ▸ hacc,
      mSpec_reach_of hr⟩

end Correct

section Det

variable {A : Type} [Language.turing.Structure A] [LinearOrder A]

theorem mSpecDet_isSrc_iff (ρ : mBlock.Assignment A) :
    mSpecDet.IsSrc ρ ↔ ((tmData A).Deterministic ∧ mSpec.IsSrc ρ) := by
  have h : mSpecDet.IsSrc ρ ↔
      (@Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ)
          (detF (mIn₁ tmTr) (mIn₁ tmStart) (mIn₁ tmSrc) (mIn₁ tmRead) (mIn₁ tmDst)
            (mIn₁ tmWrite)) ∧
        @Sentence.Realize _ A (mBlock.structure₁ (L := mBase) ρ) mSpec.src) :=
    mRealize_inf₁ ρ _ _
  rw [h]
  refine and_congr ?_ Iff.rfl
  letI := mBlock.structure₁ (L := mBase) ρ
  change Formula.Realize _ default ↔ _
  simp only [realize_detF, relMap_mIn₁]
  exact Iff.rfl

theorem mSpecDet_accepts_iff :
    mSpecDet.Accepts A ↔ ((tmData A).Deterministic ∧ mSpec.Accepts A) := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    obtain ⟨hdet, hsrc'⟩ := (mSpecDet_isSrc_iff ρ).mp hsrc
    exact ⟨hdet, ρ, σ, hsrc', htgt, hreach⟩
  · rintro ⟨hdet, ρ, σ, hsrc, htgt, hreach⟩
    exact ⟨ρ, σ, (mSpecDet_isSrc_iff ρ).mpr ⟨hdet, hsrc⟩, htgt, hreach⟩

end Det

end SpaceTM

open SpaceTM

/-! ### The two problems are in PSPACE -/

/-- **The space-bounded nondeterministic machine problem is in PSPACE**: a
configuration is an assignment of the block, a step is a first-order condition on
two of them, and an unbounded run is their transitive closure. -/
theorem ntmAcceptSpace_sotcDefinable : SOTCDefinable NTMAcceptSpace :=
  ⟨mSpec, fun _ _ _ _ _ => mSpec_accepts_iff.symm⟩

/-- **`NTMAcceptSpace ∈ PSPACE`.** -/
theorem ntmAcceptSpace_mem_PSPACE : NTMAcceptSpace ∈ PSPACE :=
  ntmAcceptSpace_sotcDefinable

/-- **The space-bounded deterministic machine problem is in PSPACE**: the same
walk, with determinism of the instance checked by the source sentence. -/
theorem dtmAcceptSpace_sotcDefinable : SOTCDefinable DTMAcceptSpace := by
  refine ⟨mSpecDet, fun A _ _ _ _ => ?_⟩
  rw [mSpecDet_accepts_iff, mSpec_accepts_iff]
  exact ⟨fun ⟨hwf, hdet, hacc⟩ => ⟨hdet, hwf, hacc⟩, fun ⟨hdet, hwf, hacc⟩ => ⟨hwf, hdet, hacc⟩⟩

/-- **`DTMAcceptSpace ∈ PSPACE`.** -/
theorem dtmAcceptSpace_mem_PSPACE : DTMAcceptSpace ∈ PSPACE :=
  dtmAcceptSpace_sotcDefinable

end DescriptiveComplexity
