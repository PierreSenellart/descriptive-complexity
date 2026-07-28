/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Set.Card
import DescriptiveComplexity.Problems.FinSat.Defs

/-!
# Satisfaction is the unique fixed point of the truth definition

The one lemma both halves of Trakhtenbrot's theorem rest on: on a well-formed
instance (`DescriptiveComplexity.FinSat.IsWF` – the parse DAG descends along
the order of the syntax) the least fixed point
`DescriptiveComplexity.FinSat.Gval` of the truth definition is its *only*
fixed point (`DescriptiveComplexity.FinSat.IsEval.iff_Gval`).

* the membership proof (`DescriptiveComplexity.FinSat.Membership`) guesses a
  relation and constrains it by the truth definition read as an equivalence;
  uniqueness is what forces the guess to *be* satisfaction, and is therefore
  what makes the `∃SO[new]` sentence say what it should;
* the hardness proof (`DescriptiveComplexity.FinSat.Hardness`) has to evaluate
  the sentence it builds; it exhibits its intended valuation and concludes by
  the same uniqueness, never touching the fuel counter.

The proofs all go through one lemma,
`DescriptiveComplexity.FinSat.gstep_mono_child`: the value of a node depends
only on the values of nodes *strictly below it in the order of the syntax*.
That is the only use well-formedness has here, and it is what replaces
well-founded recursion on a decoded parse tree.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

variable {A M : Type} [Language.finsat.Structure A]

/-! ### The rank of a node -/

/-- The rank of a node: how many nodes precede it in the order of the syntax.
It bounds the depth of the parse DAG below the node, and so the fuel its
evaluation needs. -/
noncomputable def orank (g : A) : ℕ := ({x : A | OrdLt x g} : Set A).ncard

theorem orank_lt [Finite A] (hwf : IsWF A) {c g : A} (h : OrdLt c g) : orank c < orank g := by
  have hsub : ({x : A | OrdLt x c} : Set A) ⊆ ({x : A | OrdLt x g} : Set A) := by
    intro x hx
    refine ⟨hwf.ord_trans _ _ _ hx.1 h.1, ?_⟩
    intro hxg
    exact h.2 (hwf.ord_antisymm _ _ h.1 (hxg ▸ hx.1))
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr
    ⟨c, h, fun hc => hc.2 rfl⟩) (Set.toFinite _)

theorem orank_child_lt [Finite A] (hwf : IsWF A) {g c : A} (h : ChildG g c) :
    orank c < orank g :=
  orank_lt hwf (hwf.child_lt g c h)

/-! ### Only the nodes below matter -/

/-- **The value of a node depends only on the values of the nodes strictly
below it**: every recursive occurrence in the truth definition is at a child,
and on a well-formed instance a child comes strictly earlier in the order of
the syntax. This is the whole use of well-formedness in the semantics. -/
theorem gstep_mono_child (I : A → (A → M) → Prop)
    {rec rec' : (A → M) → A → Prop} (v : A → M) (g : A)
    (h : ∀ (v' : A → M) (c : A), ChildG g c → rec v' c → rec' v' c) :
    gstep I rec v g → gstep I rec' v g := by
  intro hg
  simp only [gstep] at hg ⊢
  rcases hg with ⟨hk, hall⟩ | ⟨hk, c, hc, hv⟩ | ⟨hk, hall⟩ | ⟨hk, x, hx, d, c, hc, hv⟩ |
    hl | hl | hl | hl
  · exact Or.inl ⟨hk, fun c hc => h _ _ hc (hall c hc)⟩
  · exact Or.inr (Or.inl ⟨hk, c, hc, h _ _ hc hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hk, fun x hx d c hc => h _ _ hc (hall x hx d c hc)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, x, hx, d, c, hc, h _ _ hc hv⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hl))))))

/-- Rank many unfoldings suffice: whatever the fuel, a node that holds holds
already with the fuel its rank gives it. -/
theorem gval_orank [Finite A] (hwf : IsWF A) (I : A → (A → M) → Prop) :
    ∀ (k : ℕ) (v : A → M) (g : A), gval I k v g → gval I (orank g + 1) v g := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih =>
    intro v g hg
    refine gstep_mono_child I v g (fun v' c hc hrec => ?_) hg
    exact gval_of_le I (Nat.succ_le_of_lt (orank_child_lt hwf hc)) v' c (ih v' c hrec)

theorem Gval_iff_orank [Finite A] (hwf : IsWF A) (I : A → (A → M) → Prop) (v : A → M) (g : A) :
    Gval I v g ↔ gval I (orank g + 1) v g :=
  ⟨fun ⟨_, hk⟩ => gval_orank hwf I _ v g hk, fun h => ⟨_, h⟩⟩

/-! ### Fixed points of the truth definition -/

/-- A valuation of the nodes **satisfying the truth definition**: the value of
every node is what its clause says of the values of its children. -/
def IsEval (I : A → (A → M) → Prop) (V : (A → M) → A → Prop) : Prop :=
  ∀ (v : A → M) (g : A), V v g ↔ gstep I V v g

/-- **Satisfaction is a fixed point of the truth definition.** -/
theorem Gval_isEval [Finite A] (hwf : IsWF A) (I : A → (A → M) → Prop) :
    IsEval I (Gval I) := by
  intro v g
  constructor
  · intro hg
    have h := (Gval_iff_orank hwf I v g).mp hg
    exact gstep_mono_child I v g (fun v' c _ hrec => ⟨orank g, hrec⟩) h
  · intro hg
    refine (Gval_iff_orank hwf I v g).mpr ?_
    refine gstep_mono_child I v g (fun v' c hc hrec => ?_) hg
    exact gval_of_le I (Nat.succ_le_of_lt (orank_child_lt hwf hc)) v' c
      ((Gval_iff_orank hwf I v' c).mp hrec)

/-- Every approximant of satisfaction is below any fixed point of the truth
definition. -/
theorem gval_of_isEval {I : A → (A → M) → Prop} {V : (A → M) → A → Prop} (hV : IsEval I V) :
    ∀ (k : ℕ) (v : A → M) (g : A), gval I k v g → V v g := by
  intro k
  induction k with
  | zero => intro v g h; exact h.elim
  | succ k ih =>
    intro v g hk
    exact (hV v g).mpr (gstep_mono I (fun v' c hrec => ih v' c hrec) v g hk)

/-- **The fixed point is unique**: any valuation satisfying the truth
definition is satisfaction. On a well-formed instance the truth definition
determines the value of a node from the values of the nodes below it, and
there are no infinite descents. -/
theorem IsEval.iff_Gval [Finite A] (hwf : IsWF A) {I : A → (A → M) → Prop}
    {V : (A → M) → A → Prop} (hV : IsEval I V) (v : A → M) (g : A) :
    V v g ↔ Gval I v g := by
  constructor
  · -- downward: unfold `V` along the order, collecting the fuel from the ranks
    have key : ∀ n (g : A), orank g ≤ n → ∀ v : A → M, V v g → Gval I v g := by
      intro n
      induction n with
      | zero =>
        intro g hg v hVg
        refine (Gval_iff_orank hwf I v g).mpr ?_
        refine gstep_mono_child I v g (fun v' c hc hrec => ?_) ((hV v g).mp hVg)
        exact absurd (orank_child_lt hwf hc) (by omega)
      | succ n ih =>
        intro g hg v hVg
        refine (Gval_iff_orank hwf I v g).mpr ?_
        refine gstep_mono_child I v g (fun v' c hc hrec => ?_) ((hV v g).mp hVg)
        have hlt := orank_child_lt hwf hc
        exact gval_of_le I (Nat.succ_le_of_lt hlt) v' c
          ((Gval_iff_orank hwf I v' c).mp (ih c (by omega) v' hrec))
    exact key (orank g) g le_rfl v
  · -- upward: every approximant is below `V`, by induction on the fuel
    rintro ⟨k, hk⟩
    exact gval_of_isEval hV k v g hk

end FinSat

end DescriptiveComplexity
