/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Gadget
import DescriptiveComplexity.Problems.Hamilton.Cycle
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Vertex Cover from a Hamilton circuit

The reverse direction of the reduction reads a vertex cover off a Hamilton
circuit of the gadget graph. Its foundation is a precise characterization of the
neighbours of each gadget vertex (`DescriptiveComplexity.dgEdge_iff` /
`DescriptiveComplexity.IAdjRaw`).

## Structure

1. **Neighbour sets.** For each gadget vertex, the exact set of its
   `DescriptiveComplexity.DGEdge`-neighbours (by cases on the other vertex's tag, via
   `dgEdge_iff`). The **internal** vertices `⟨g1,(a,b)⟩` and `⟨g4,(a,b)⟩` have
   exactly two neighbours, `⟨g0/g2⟩` and `⟨g3/g5⟩` respectively.
2. **Forced edges.** In a Hamilton circuit each vertex has exactly two
   tour-neighbours, both adjacent to it. So a degree-two vertex uses *both* its
   edges, forcing the paths `g0-g1-g2` and `g3-g4-g5` in every gadget
   (`DescriptiveComplexity.forced_g1`, `DescriptiveComplexity.forced_g4`).
3. **The three traversals.** Propagating through `g2`, `g3` (degree three) shows
   each gadget is traversed through the `u`-side, the `v`-side, or both – never
   neither (which would isolate it as two 6-cycles): every edge has a *straight*
   side (`DescriptiveComplexity.side_straight`).
4. **Chain propagation.** A straight side `(b,a)` frees the entrance and exit
   slots of the opposite side `(a,b)` from the cross edges
   (`DescriptiveComplexity.g0_other`/`g5_other`); the freed slot is a selector at the
   ends of `a`'s chain, or a chain-link that straightens the walked side in turn
   (`DescriptiveComplexity.straight_of_chain_down`/`up`). Well-founded induction along
   `a`'s neighbour list puts a selector at both chain ends: `a` is *active*
   (`DescriptiveComplexity.active_of_straight`).
5. **The cover.** `C := {a | Active f a}` covers every edge
   (`DescriptiveComplexity.cover_property`), and `|C| ≤ |marked|` by the
   selector-slot injection (`DescriptiveComplexity.active_ncard_le`).

`DescriptiveComplexity.eq_gPt_of_val` below reconstructs a vertex from its tag and
coordinates (sidestepping a `simp`/subtype mismatch), the workhorse of step 1.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]

/-- A gadget vertex `⟨t,(a,b)⟩` (raw form). Reconstructing a neighbour from its
tag and coordinates uses this together with `Subtype.ext`. -/
theorem gPt_val {t : HTag} {ht : t ≠ .sel ∧ t ≠ .hub} {a b : A} (h : HEdge a b) :
    (gPt t ht h).1 = (t, ![a, b]) := rfl

/-- **Reconstruction**: an interpreted vertex with a gadget tag `t` and
coordinates `(a, b)` is the gadget vertex `gPt t _ h`. This is the workhorse of
the neighbour characterizations of step 1 (it sidesteps the subtype/`MapRel`
definitional mismatch that blocks `simp` on raw destructured vertices). -/
theorem eq_gPt_of_val {t : HTag} {ht : t ≠ .sel ∧ t ≠ .hub} {a b : A} (h : HEdge a b)
    {q : hamInterp.MapRel A} (hqt : q.1.1 = t) (h0 : q.1.2 0 = a) (h1 : q.1.2 1 = b) :
    q = gPt t ht h := by
  apply Subtype.ext
  rw [gPt_val]
  refine Prod.ext hqt ?_
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

section Tour

variable {H : Type} {N : ℕ}

/-- `nextIdx` on `Fin N` is Mathlib's cyclic rotation `finRotate N` (so it is a
bijection). -/
theorem nextIdx_eq_finRotate (i : Fin N) : nextIdx i = finRotate N i := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 :=
    ⟨N - 1, by have : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0); omega⟩
  apply Fin.ext
  simp only [nextIdx, coe_finRotate]
  by_cases h : i = Fin.last n
  · subst h; simp [Fin.val_last]
  · rw [if_neg h]
    exact Nat.mod_eq_of_lt (by have := Fin.val_lt_last h; omega)

/-- In a cyclic enumeration `nextIdx` applied twice returns a *different* index,
as soon as the cycle has length at least three. -/
theorem nextIdx_nextIdx_ne (hN : 3 ≤ N) (i : Fin N) : nextIdx (nextIdx i) ≠ i := by
  intro he
  have h1 : (nextIdx i : ℕ) = ((i : ℕ) + 1) % N := rfl
  have h2 : (nextIdx (nextIdx i) : ℕ) = ((nextIdx i : ℕ) + 1) % N := rfl
  have hval := congrArg Fin.val he
  rw [h2, h1] at hval
  have hi := i.isLt
  rcases Nat.lt_or_ge ((i : ℕ) + 1) N with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hval
    rcases Nat.lt_or_ge ((i : ℕ) + 2) N with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt2] at hval; omega
    · rw [show (i : ℕ) + 2 = N by omega, Nat.mod_self] at hval; omega
  · rw [show (i : ℕ) + 1 = N by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- The **tour successor** of a cyclic enumeration `f`, as a permutation of the
universe: the vertex one step further along the tour. -/
noncomputable def tourSucc (f : Fin N ≃ H) : Equiv.Perm H :=
  f.symm.trans ((finRotate N).trans f)

@[simp] theorem tourSucc_apply (f : Fin N ≃ H) (x : H) :
    tourSucc f x = f (nextIdx (f.symm x)) := by
  simp only [tourSucc, Equiv.trans_apply, nextIdx_eq_finRotate]

/-- Two vertices are **tour-adjacent** when one is the tour successor of the
other. This is symmetric, and every vertex has exactly two tour-neighbours. -/
def TAdj (f : Fin N ≃ H) (x y : H) : Prop := tourSucc f x = y ∨ tourSucc f y = x

/-- The **two tour-neighbours of `x` are distinct** once the cycle has length
`≥ 3`: the successor is not the predecessor. -/
theorem tourSucc_ne_symm (f : Fin N ≃ H) (hN : 3 ≤ N) (x : H) :
    tourSucc f x ≠ (tourSucc f).symm x := by
  intro he
  have he2 : tourSucc f (tourSucc f x) = x := by
    rw [he]; exact Equiv.apply_symm_apply _ x
  have hfx : f.symm (tourSucc f x) = nextIdx (f.symm x) := by
    rw [tourSucc_apply, Equiv.symm_apply_apply]
  rw [tourSucc_apply, hfx] at he2
  exact nextIdx_nextIdx_ne hN (f.symm x) (f.injective (he2.trans (f.apply_symm_apply x).symm))

/-- Tour-adjacency is symmetric. -/
theorem TAdj_symm {f : Fin N ≃ H} {x y : H} (h : TAdj f x y) : TAdj f y x := Or.symm h

/-- `x` is tour-adjacent to its successor and to its predecessor. -/
theorem tadj_succ (f : Fin N ≃ H) (x : H) : TAdj f x (tourSucc f x) := Or.inl rfl

theorem tadj_pred (f : Fin N ≃ H) (x : H) : TAdj f x ((tourSucc f).symm x) :=
  Or.inr (Equiv.apply_symm_apply _ x)

/-- Every tour-neighbour of `x` is its successor or its predecessor. -/
theorem tadj_eq {f : Fin N ≃ H} {x y : H} (h : TAdj f x y) :
    y = tourSucc f x ∨ y = (tourSucc f).symm x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [← h, Equiv.symm_apply_apply])

/-- A tour edge is a graph edge. -/
theorem tadj_dgEdge {f : Fin N ≃ H} {R : H → H → Prop} (hf : ∀ i, R (f i) (f (nextIdx i)))
    (hsymm : ∀ a b, R a b → R b a) {x y : H} (h : TAdj f x y) : R x y := by
  rcases h with h | h
  · have hx := hf (f.symm x); rwa [Equiv.apply_symm_apply, ← tourSucc_apply, h] at hx
  · have hy := hf (f.symm y)
    rw [Equiv.apply_symm_apply, ← tourSucc_apply, h] at hy
    exact hsymm _ _ hy

/-- The tour successor of `x` is one of its two known tour-neighbours. -/
theorem tourSucc_mem_of_tadj {f : Fin N ≃ H} {x p q : H}
    (hp : TAdj f x p) (hq : TAdj f x q) (hpq : p ≠ q) :
    tourSucc f x = p ∨ tourSucc f x = q := by
  rcases tadj_eq hp with hp' | hp'
  · exact Or.inl hp'.symm
  · rcases tadj_eq hq with hq' | hq'
    · exact Or.inr hq'.symm
    · exact absurd (hp'.trans hq'.symm) hpq

/-- **A vertex has only two tour-neighbours**: once two distinct ones are known,
every tour-neighbour is one of them. -/
theorem tadj_two {f : Fin N ≃ H} {x p q y : H} (hp : TAdj f x p) (hq : TAdj f x q)
    (hpq : p ≠ q) (hy : TAdj f x y) : y = p ∨ y = q := by
  rcases tadj_eq hy with hy' | hy'
  · rcases tadj_eq hp with hp' | hp'
    · exact Or.inl (hy'.trans hp'.symm)
    · rcases tadj_eq hq with hq' | hq'
      · exact Or.inr (hy'.trans hq'.symm)
      · exact absurd (hp'.trans hq'.symm) hpq
  · rcases tadj_eq hp with hp' | hp'
    · rcases tadj_eq hq with hq' | hq'
      · exact absurd (hp'.trans hq'.symm) hpq
      · exact Or.inr (hy'.trans hq'.symm)
    · exact Or.inl (hy'.trans hp'.symm)

open Fin.NatCast in
/-- **A successor-closed subset of `Fin N` is everything.** Starting from any
element, repeatedly adding one cycles through all of `Fin N`. -/
theorem all_of_succ_closed {N : ℕ} [NeZero N] (P : Fin N → Prop) (i₀ : Fin N) (h₀ : P i₀)
    (hs : ∀ i, P i → P (i + 1)) : ∀ j, P j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := NeZero.pos N; omega⟩
  have key : ∀ m : ℕ, P (i₀ + (m : Fin (n + 1))) := by
    intro m
    induction m with
    | zero => simpa using h₀
    | succ k ih => rw [Nat.cast_succ, ← add_assoc]; exact hs _ ih
  intro j
  have hj : i₀ + ((j - i₀).val : Fin (n + 1)) = j := by rw [Fin.cast_val_eq_self]; abel
  rw [← hj]; exact key (j - i₀).val

/-- **The tour is a single cycle.** Any nonempty subset of the universe closed
under the tour successor is the whole universe. (`tourSucc` is conjugate to the
`N`-cycle `finRotate N`, so it has no proper invariant subset.) -/
theorem tourSucc_closed_univ (f : Fin N ≃ H) {P : H → Prop} {x : H} (hx : P x)
    (hclosed : ∀ y, P y → P (tourSucc f y)) : ∀ z, P z := by
  haveI : NeZero N := ⟨by rintro rfl; exact (f.symm x).elim0⟩
  have hP' : ∀ i, P (f i) → P (f (i + 1)) := by
    intro i hi
    have h := hclosed _ hi
    rwa [tourSucc_apply, Equiv.symm_apply_apply, nextIdx_eq_finRotate, finRotate_apply] at h
  intro z
  have := all_of_succ_closed (fun i => P (f i)) (f.symm x) (by rwa [Equiv.apply_symm_apply]) hP'
  simpa using this (f.symm z)

/-- **Forced edges.** If a vertex `x` in a tour has at most two graph-neighbours
(every neighbour is `p` or `q`), then `p` and `q` are exactly its two
tour-neighbours: every one of `x`'s edges is used by the tour. (Distinctness of
the two tour-neighbours, from `3 ≤ N`, forces `p ≠ q` and that both occur.) -/
theorem tour_forced (f : Fin N ≃ H) {R : H → H → Prop}
    (hf : ∀ i, R (f i) (f (nextIdx i))) (hsymm : ∀ a b, R a b → R b a) (hN : 3 ≤ N)
    {x p q : H} (hnb : ∀ y, R x y → y = p ∨ y = q) : TAdj f x p ∧ TAdj f x q := by
  set S := tourSucc f with hS
  have hA : R x (S x) := by
    have h := hf (f.symm x); rwa [Equiv.apply_symm_apply, ← tourSucc_apply, ← hS] at h
  have hSsymm : S (S.symm x) = x := Equiv.apply_symm_apply S x
  have hB : R x (S.symm x) := by
    have h := hf (f.symm (S.symm x))
    rw [Equiv.apply_symm_apply, ← tourSucc_apply, ← hS, hSsymm] at h
    exact hsymm _ _ h
  have hC : S x ≠ S.symm x := by rw [hS]; exact tourSucc_ne_symm f hN x
  have hAx := hnb _ hA
  have hBx := hnb _ hB
  refine ⟨?_, ?_⟩
  · rcases hAx with h1 | h1
    · exact Or.inl h1
    · rcases hBx with h2 | h2
      · exact Or.inr (by rw [← h2]; exact hSsymm)
      · exact absurd (h1.trans h2.symm) hC
  · rcases hAx with h1 | h1
    · rcases hBx with h2 | h2
      · exact absurd (h1.trans h2.symm) hC
      · exact Or.inr (by rw [← h2]; exact hSsymm)
    · exact Or.inl h1

end Tour

/-- **The neighbours of the internal vertex `⟨g1,(a,b)⟩` are exactly `⟨g0,(a,b)⟩`
and `⟨g2,(a,b)⟩`.** So in a Hamilton circuit both its edges are forced. -/
theorem nbrs_gPt_g1 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g1 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g0 ⟨by decide, by decide⟩ h ∨ q = gPt .g2 ⟨by decide, by decide⟩ h := by
  constructor
  · intro hadj
    rw [dgEdge_iff] at hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;>
      simp only [IAdjRaw] at hadj <;>
      first
        | exact hadj.elim
        | exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
        | exact Or.inr (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
  · rintro (rfl | rfl) <;> rw [dgEdge_iff] <;> simp [IAdjRaw]

/-- **The neighbours of the internal vertex `⟨g4,(a,b)⟩` are exactly `⟨g3,(a,b)⟩`
and `⟨g5,(a,b)⟩`.** -/
theorem nbrs_gPt_g4 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g4 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g3 ⟨by decide, by decide⟩ h ∨ q = gPt .g5 ⟨by decide, by decide⟩ h := by
  constructor
  · intro hadj
    rw [dgEdge_iff] at hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;>
      simp only [IAdjRaw] at hadj <;>
      first
        | exact hadj.elim
        | exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
        | exact Or.inr (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
  · rintro (rfl | rfl) <;> rw [dgEdge_iff] <;> simp [IAdjRaw]

/-- **The neighbours of `⟨g2,(a,b)⟩` are `⟨g1,(a,b)⟩`, `⟨g3,(a,b)⟩` and the cross
neighbour `⟨g0,(b,a)⟩`.** -/
theorem nbrs_gPt_g2 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g2 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g1 ⟨by decide, by decide⟩ h ∨ q = gPt .g3 ⟨by decide, by decide⟩ h ∨
        q = gPt .g0 ⟨by decide, by decide⟩ (hEdge_symm h) := by
  constructor
  · intro hadj
    rw [dgEdge_iff] at hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;>
      simp only [IAdjRaw] at hadj <;>
      first
        | exact hadj.elim
        | exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
        | exact Or.inr (Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm))
        | exact Or.inr (Or.inr (eq_gPt_of_val (hEdge_symm h) rfl hadj.2.symm hadj.1.symm))
  · rintro (rfl | rfl | rfl) <;> rw [dgEdge_iff] <;> simp [IAdjRaw]

/-- **The neighbours of `⟨g3,(a,b)⟩` are `⟨g2,(a,b)⟩`, `⟨g4,(a,b)⟩` and the cross
neighbour `⟨g5,(b,a)⟩`.** -/
theorem nbrs_gPt_g3 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g3 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g2 ⟨by decide, by decide⟩ h ∨ q = gPt .g4 ⟨by decide, by decide⟩ h ∨
        q = gPt .g5 ⟨by decide, by decide⟩ (hEdge_symm h) := by
  constructor
  · intro hadj
    rw [dgEdge_iff] at hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;>
      simp only [IAdjRaw] at hadj <;>
      first
        | exact hadj.elim
        | exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
        | exact Or.inr (Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm))
        | exact Or.inr (Or.inr (eq_gPt_of_val (hEdge_symm h) rfl hadj.2.symm hadj.1.symm))
  · rintro (rfl | rfl | rfl) <;> rw [dgEdge_iff] <;> simp [IAdjRaw]

/-! ### From the tour to the forced gadget paths -/

/-- The gadget edge relation is symmetric (it is the *undirected* edge). -/
theorem dgEdge_symm {x y : hamInterp.MapRel A} (h : DGEdge x y) : DGEdge y x := Or.symm h

/-- Gadget vertices with distinct tags are distinct (local copy, so `Reverse`
stays independent of `Forward`). -/
theorem gPt_ne_tag {i j : HTag} (hij : i ≠ j) {hi hj} {a b a' b' : A}
    (h : HEdge a b) (h' : HEdge a' b') : gPt i hi h ≠ gPt j hj h' :=
  fun he => hij (by have := congrArg (fun p : hamInterp.MapRel A => p.1.1) he; simpa using this)

/-- A gadget vertex depends on the edge only through its endpoints, not the proof
(handy to normalize a doubly-symmetrized edge back to the original). -/
theorem gPt_edge_irrel {t : HTag} {ht} {a b : A} (h₁ h₂ : HEdge a b) :
    gPt t ht h₁ = gPt t ht h₂ := Subtype.ext rfl

/-- A vertex tagged `sel` is a selector `selPt hm` for a marked vertex. -/
theorem eq_selPt_of_tag {q : hamInterp.MapRel A} (hqt : q.1.1 = .sel) :
    ∃ (m : A) (hm : MGMarked m), q = selPt hm := by
  rcases point_cases q with ⟨t, ht, h, hq⟩ | ⟨hm, _, hq⟩ | hhub
  · rw [hq, gPt_tag] at hqt; exact absurd hqt ht.1
  · exact ⟨_, hm, hq⟩
  · exact absurd (hhub.symm.trans hqt) (by decide)

/-- **At least three vertices.** If the target universe carries an edge, its
gadget contributes twelve distinct vertices, so any cyclic enumeration has
length `≥ 3` – enough to run `tour_forced`. -/
theorem three_le_of_edge {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) {a b : A} (h : HEdge a b) :
    3 ≤ N := by
  classical
  haveI : Fintype (hamInterp.MapRel A) := Fintype.ofEquiv _ f
  have hcard : Fintype.card (hamInterp.MapRel A) = N := by
    rw [← Fintype.card_fin N]; exact (Fintype.card_congr f).symm
  have h2 : 2 < (Finset.univ : Finset (hamInterp.MapRel A)).card :=
    Finset.two_lt_card_iff.mpr
      ⟨gPt .g0 ⟨by decide, by decide⟩ h, gPt .g1 ⟨by decide, by decide⟩ h,
        gPt .g2 ⟨by decide, by decide⟩ h, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
        gPt_ne_tag (by decide) h h, gPt_ne_tag (by decide) h h, gPt_ne_tag (by decide) h h⟩
  rw [Finset.card_univ, hcard] at h2
  omega

/-- **Forced `u`-path.** The degree-two internal vertex `⟨g1,(a,b)⟩` uses both of
its edges: `⟨g0⟩` and `⟨g2⟩` are its two tour-neighbours. -/
theorem forced_g1 {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b) :
    TAdj f (gPt .g1 ⟨by decide, by decide⟩ h) (gPt .g0 ⟨by decide, by decide⟩ h) ∧
      TAdj f (gPt .g1 ⟨by decide, by decide⟩ h) (gPt .g2 ⟨by decide, by decide⟩ h) :=
  tour_forced f hf (fun _ _ => dgEdge_symm) (three_le_of_edge f h)
    (fun y hy => (nbrs_gPt_g1 h y).mp hy)

/-- **Forced `v`-path.** Symmetrically, `⟨g4,(a,b)⟩` uses both `⟨g3⟩` and `⟨g5⟩`. -/
theorem forced_g4 {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b) :
    TAdj f (gPt .g4 ⟨by decide, by decide⟩ h) (gPt .g3 ⟨by decide, by decide⟩ h) ∧
      TAdj f (gPt .g4 ⟨by decide, by decide⟩ h) (gPt .g5 ⟨by decide, by decide⟩ h) :=
  tour_forced f hf (fun _ _ => dgEdge_symm) (three_le_of_edge f h)
    (fun y hy => (nbrs_gPt_g4 h y).mp hy)

/-- **Propagation at `g2`.** With the forced `u`-path, `⟨g1⟩` is one of `⟨g2⟩`'s
two tour-neighbours; the other, being a graph-neighbour distinct from `⟨g1⟩`, is
either `⟨g3⟩` (traverse this side straight through) or the cross vertex
`⟨g0,(b,a)⟩` (hand the tour over to the other side). -/
theorem prop_g2 {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b) :
    TAdj f (gPt .g2 ⟨by decide, by decide⟩ h) (gPt .g3 ⟨by decide, by decide⟩ h) ∨
      TAdj f (gPt .g2 ⟨by decide, by decide⟩ h)
        (gPt .g0 ⟨by decide, by decide⟩ (hEdge_symm h)) := by
  have hsymm : ∀ x y : hamInterp.MapRel A, DGEdge x y → DGEdge y x := fun _ _ => dgEdge_symm
  have hne := tourSucc_ne_symm f (three_le_of_edge f h) (gPt .g2 ⟨by decide, by decide⟩ h)
  have h21 : TAdj f (gPt .g2 ⟨by decide, by decide⟩ h) (gPt .g1 ⟨by decide, by decide⟩ h) :=
    TAdj_symm (forced_g1 f hf h).2
  rcases tadj_eq h21 with h1 | h1
  · have hz := tadj_pred f (gPt .g2 ⟨by decide, by decide⟩ h)
    have hmem := (nbrs_gPt_g2 h _).mp (tadj_dgEdge hf hsymm hz)
    rcases hmem with hm | hm | hm
    · exact absurd (h1.symm.trans hm.symm) hne
    · exact Or.inl (hm ▸ hz)
    · exact Or.inr (hm ▸ hz)
  · have hz := tadj_succ f (gPt .g2 ⟨by decide, by decide⟩ h)
    have hmem := (nbrs_gPt_g2 h _).mp (tadj_dgEdge hf hsymm hz)
    rcases hmem with hm | hm | hm
    · exact absurd (hm.trans h1) hne
    · exact Or.inl (hm ▸ hz)
    · exact Or.inr (hm ▸ hz)

/-- **Propagation at `g3`.** Symmetrically, the tour leaves `⟨g3⟩` either straight
to `⟨g2⟩` or across to the cross vertex `⟨g5,(b,a)⟩`. -/
theorem prop_g3 {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b) :
    TAdj f (gPt .g3 ⟨by decide, by decide⟩ h) (gPt .g2 ⟨by decide, by decide⟩ h) ∨
      TAdj f (gPt .g3 ⟨by decide, by decide⟩ h)
        (gPt .g5 ⟨by decide, by decide⟩ (hEdge_symm h)) := by
  have hsymm : ∀ x y : hamInterp.MapRel A, DGEdge x y → DGEdge y x := fun _ _ => dgEdge_symm
  have hne := tourSucc_ne_symm f (three_le_of_edge f h) (gPt .g3 ⟨by decide, by decide⟩ h)
  have h34 : TAdj f (gPt .g3 ⟨by decide, by decide⟩ h) (gPt .g4 ⟨by decide, by decide⟩ h) :=
    TAdj_symm (forced_g4 f hf h).1
  rcases tadj_eq h34 with h1 | h1
  · have hz := tadj_pred f (gPt .g3 ⟨by decide, by decide⟩ h)
    have hmem := (nbrs_gPt_g3 h _).mp (tadj_dgEdge hf hsymm hz)
    rcases hmem with hm | hm | hm
    · exact Or.inl (hm ▸ hz)
    · exact absurd (h1.symm.trans hm.symm) hne
    · exact Or.inr (hm ▸ hz)
  · have hz := tadj_succ f (gPt .g3 ⟨by decide, by decide⟩ h)
    have hmem := (nbrs_gPt_g3 h _).mp (tadj_dgEdge hf hsymm hz)
    rcases hmem with hm | hm | hm
    · exact Or.inl (hm ▸ hz)
    · exact absurd (hm.trans h1) hne
    · exact Or.inr (hm ▸ hz)

/-- **Never neither.** A gadget cannot be traversed with *both* sides crossed:
that would close the six vertices `g0 g1 g2` of each side into a single
tour-invariant `6`-cycle, which (the tour being one cycle over `≥ 12` vertices)
must be the whole universe – impossible, as `⟨g3,(a,b)⟩` lies outside it. -/
theorem not_both_crossed {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b)
    (hAcross : TAdj f (gPt .g2 ⟨by decide, by decide⟩ h)
      (gPt .g0 ⟨by decide, by decide⟩ (hEdge_symm h)))
    (hBcross : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
      (gPt .g0 ⟨by decide, by decide⟩ h)) : False := by
  have h' := hEdge_symm h
  have fA := forced_g1 f hf h
  have fB := forced_g1 f hf h'
  -- The six vertices `g0 g1 g2` on each side.
  set P : hamInterp.MapRel A → Prop := fun y =>
    y = gPt .g0 ⟨by decide, by decide⟩ h ∨ y = gPt .g1 ⟨by decide, by decide⟩ h ∨
      y = gPt .g2 ⟨by decide, by decide⟩ h ∨ y = gPt .g0 ⟨by decide, by decide⟩ h' ∨
      y = gPt .g1 ⟨by decide, by decide⟩ h' ∨ y = gPt .g2 ⟨by decide, by decide⟩ h' with hP
  have hclosed : ∀ y, P y → P (tourSucc f y) := by
    rintro y (rfl | rfl | rfl | rfl | rfl | rfl)
    · rcases tourSucc_mem_of_tadj fA.1.symm hBcross.symm (gPt_ne_tag (by decide) h h') with hs | hs
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))
    · rcases tourSucc_mem_of_tadj fA.1 fA.2 (gPt_ne_tag (by decide) h h) with hs | hs
      · exact Or.inl hs
      · exact Or.inr (Or.inr (Or.inl hs))
    · rcases tourSucc_mem_of_tadj fA.2.symm hAcross (gPt_ne_tag (by decide) h h') with hs | hs
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · rcases tourSucc_mem_of_tadj fB.1.symm hAcross.symm (gPt_ne_tag (by decide) h' h) with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
      · exact Or.inr (Or.inr (Or.inl hs))
    · rcases tourSucc_mem_of_tadj fB.1 fB.2 (gPt_ne_tag (by decide) h' h') with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs))))
    · rcases tourSucc_mem_of_tadj fB.2.symm hBcross (gPt_ne_tag (by decide) h' h) with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
      · exact Or.inl hs
  have hall := tourSucc_closed_univ f (P := P) (x := gPt .g0 ⟨by decide, by decide⟩ h)
    (Or.inl rfl) hclosed
  rcases hall (gPt .g3 ⟨by decide, by decide⟩ h) with h3 | h3 | h3 | h3 | h3 | h3 <;>
    first
      | exact absurd h3 (gPt_ne_tag (by decide) h h)
      | exact absurd h3 (gPt_ne_tag (by decide) h h')

/-- **The neighbours of a general `⟨g0,(a,b)⟩`**: `⟨g1,(a,b)⟩`, the cross vertex
`⟨g2,(b,a)⟩`, the chain link `⟨g5,(a,c)⟩` back to the predecessor neighbour `c < b`
of `b`, and — when `b` is the least neighbour — every selector. -/
theorem nbrs_gPt_g0 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g0 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g1 ⟨by decide, by decide⟩ h ∨
        q = gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h) ∨
        (∃ (c : A) (hc : HEdge a c), c < b ∧ (∀ d, HEdge a d → d ≤ c ∨ b ≤ d) ∧
          q = gPt .g5 ⟨by decide, by decide⟩ hc) ∨
        ((∀ d, HEdge a d → b ≤ d) ∧ ∃ (m : A) (hm : MGMarked m), q = selPt hm) := by
  rw [dgEdge_iff]
  constructor
  · intro hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;> simp only [IAdjRaw] at hadj
    · exact hadj.elim
    · exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
    · exact Or.inr (Or.inl (eq_gPt_of_val (hEdge_symm h) rfl hadj.2.symm hadj.1.symm))
    · exact hadj.elim
    · exact hadj.elim
    · have hdom : HEdge (w 0) (w 1) := (dom_gadget .g5 ⟨by decide, by decide⟩ w).mp hq
      have hc : HEdge a (w 1) := by rw [show a = w 0 from hadj.1]; exact hdom
      exact Or.inr (Or.inr (Or.inl ⟨w 1, hc, hadj.2.2.1, hadj.2.2.2,
        eq_gPt_of_val hc rfl hadj.1.symm rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hadj, eq_selPt_of_tag rfl⟩))
    · exact hadj.elim
  · rintro (rfl | rfl | ⟨c, hc, hlt, hpred, rfl⟩ | ⟨hmin, m, hm, rfl⟩) <;> simp only [IAdjRaw]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, h, hlt, hpred⟩
    · exact hmin

/-- **The neighbours of a general `⟨g5,(a,b)⟩`**: `⟨g4,(a,b)⟩`, the cross vertex
`⟨g3,(b,a)⟩`, the chain link `⟨g0,(a,c)⟩` on to the successor neighbour `b < c`,
and — when `b` is the greatest neighbour — every selector. -/
theorem nbrs_gPt_g5 {a b : A} (h : HEdge a b) (q : hamInterp.MapRel A) :
    DGEdge (gPt .g5 ⟨by decide, by decide⟩ h) q ↔
      q = gPt .g4 ⟨by decide, by decide⟩ h ∨
        q = gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h) ∨
        (∃ (c : A) (hc : HEdge a c), b < c ∧ (∀ d, HEdge a d → d ≤ b ∨ c ≤ d) ∧
          q = gPt .g0 ⟨by decide, by decide⟩ hc) ∨
        ((∀ d, HEdge a d → d ≤ b) ∧ ∃ (m : A) (hm : MGMarked m), q = selPt hm) := by
  rw [dgEdge_iff]
  constructor
  · intro hadj
    obtain ⟨⟨t, w⟩, hq⟩ := q
    cases t <;> simp only [IAdjRaw] at hadj
    · exact Or.inr (Or.inr (Or.inl ⟨w 1, hadj.2.1, hadj.2.2.1, hadj.2.2.2,
        eq_gPt_of_val hadj.2.1 rfl hadj.1.symm rfl⟩))
    · exact hadj.elim
    · exact hadj.elim
    · exact Or.inr (Or.inl (eq_gPt_of_val (hEdge_symm h) rfl hadj.2.symm hadj.1.symm))
    · exact Or.inl (eq_gPt_of_val h rfl hadj.1.symm hadj.2.symm)
    · exact hadj.elim
    · exact Or.inr (Or.inr (Or.inr ⟨hadj, eq_selPt_of_tag rfl⟩))
    · exact hadj.elim
  · rintro (rfl | rfl | ⟨c, hc, hlt, hsucc, rfl⟩ | ⟨hmax, m, hm, rfl⟩) <;> simp only [IAdjRaw]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, hc, hlt, hsucc⟩
    · exact hmax

/-- **At least one side is straight.** Combining the `g2` case split
(`prop_g2`) on both sides with `not_both_crossed`: for every edge, the tour runs
straight through the `a`-side gadget (`g2-g3`) or through the `b`-side gadget. -/
theorem side_straight {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b) :
    TAdj f (gPt .g2 ⟨by decide, by decide⟩ h) (gPt .g3 ⟨by decide, by decide⟩ h) ∨
      TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h)) := by
  rcases prop_g2 f hf h with hA | hAcross
  · exact Or.inl hA
  · rcases prop_g2 f hf (hEdge_symm h) with hB | hBcross
    · exact Or.inr hB
    · rw [gPt_edge_irrel (hEdge_symm (hEdge_symm h)) h] at hBcross
      exact (not_both_crossed f hf h hAcross hBcross).elim

/-! ### Straightness propagates along the owner's chain -/

/-- Whether a vertex is a selector. -/
def isSel (q : hamInterp.MapRel A) : Prop := q.1.1 = HTag.sel

instance : DecidablePred (isSel (A := A)) := fun q => inferInstanceAs (Decidable (q.1.1 = _))

/-- **The entrance slot of a straight-opposite side.** When the `b`-side of the
edge `{a, b}` is straight, both tour-slots of `⟨g2,(b,a)⟩` are known, so the
cross edge into `⟨g0,(a,b)⟩` is unused: the tour-neighbour of `⟨g0,(a,b)⟩` other
than the forced `⟨g1,(a,b)⟩` is a selector (and `b` is `a`'s least neighbour) or
the chain-link from the predecessor side. -/
theorem g0_other {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b)
    (hS : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
      (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h))) :
    ((∀ d, HEdge a d → b ≤ d) ∧
        (isSel (tourSucc f (gPt .g0 ⟨by decide, by decide⟩ h)) ∨
          isSel ((tourSucc f).symm (gPt .g0 ⟨by decide, by decide⟩ h)))) ∨
      ∃ (c : A) (hc : HEdge a c), c < b ∧
        TAdj f (gPt .g0 ⟨by decide, by decide⟩ h) (gPt .g5 ⟨by decide, by decide⟩ hc) := by
  have hsymm : ∀ x y : hamInterp.MapRel A, DGEdge x y → DGEdge y x := fun _ _ => dgEdge_symm
  have hN := three_le_of_edge f h
  have h01 : TAdj f (gPt .g0 ⟨by decide, by decide⟩ h) (gPt .g1 ⟨by decide, by decide⟩ h) :=
    TAdj_symm (forced_g1 f hf h).1
  obtain ⟨X, hX, hXne⟩ :
      ∃ X, TAdj f (gPt .g0 ⟨by decide, by decide⟩ h) X ∧
        X ≠ gPt .g1 ⟨by decide, by decide⟩ h := by
    rcases tadj_eq h01 with h1 | h1
    · exact ⟨(tourSucc f).symm _, tadj_pred f _,
        fun he => tourSucc_ne_symm f hN _ (h1.symm.trans he.symm)⟩
    · exact ⟨tourSucc f _, tadj_succ f _, fun he => tourSucc_ne_symm f hN _ (he.trans h1)⟩
  rcases (nbrs_gPt_g0 h X).mp (tadj_dgEdge hf hsymm hX) with
    h1 | h2 | ⟨c, hc, hlt, -, rfl⟩ | ⟨hmin, m, hm, rfl⟩
  · exact absurd h1 hXne
  · exfalso
    have h2ta : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g0 ⟨by decide, by decide⟩ h) := TAdj_symm (h2 ▸ hX)
    have h21 : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g1 ⟨by decide, by decide⟩ (hEdge_symm h)) :=
      TAdj_symm (forced_g1 f hf (hEdge_symm h)).2
    rcases tadj_two h21 hS (gPt_ne_tag (by decide) _ _) h2ta with hE | hE
    · exact gPt_ne_tag (by decide) h (hEdge_symm h) hE
    · exact gPt_ne_tag (by decide) h (hEdge_symm h) hE
  · exact Or.inr ⟨c, hc, hlt, hX⟩
  · refine Or.inl ⟨hmin, ?_⟩
    rcases tadj_eq hX with h1 | h1
    · exact Or.inl (by rw [← h1]; rfl)
    · exact Or.inr (by rw [← h1]; rfl)

/-- **The exit slot of a straight-opposite side**, symmetrically: the
tour-neighbour of `⟨g5,(a,b)⟩` other than the forced `⟨g4,(a,b)⟩` is a selector
(and `b` is `a`'s greatest neighbour) or the chain-link to the successor side. -/
theorem g5_other {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b : A} (h : HEdge a b)
    (hS : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
      (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h))) :
    ((∀ d, HEdge a d → d ≤ b) ∧
        (isSel (tourSucc f (gPt .g5 ⟨by decide, by decide⟩ h)) ∨
          isSel ((tourSucc f).symm (gPt .g5 ⟨by decide, by decide⟩ h)))) ∨
      ∃ (c : A) (hc : HEdge a c), b < c ∧
        TAdj f (gPt .g5 ⟨by decide, by decide⟩ h) (gPt .g0 ⟨by decide, by decide⟩ hc) := by
  have hsymm : ∀ x y : hamInterp.MapRel A, DGEdge x y → DGEdge y x := fun _ _ => dgEdge_symm
  have hN := three_le_of_edge f h
  have h54 : TAdj f (gPt .g5 ⟨by decide, by decide⟩ h) (gPt .g4 ⟨by decide, by decide⟩ h) :=
    TAdj_symm (forced_g4 f hf h).2
  obtain ⟨X, hX, hXne⟩ :
      ∃ X, TAdj f (gPt .g5 ⟨by decide, by decide⟩ h) X ∧
        X ≠ gPt .g4 ⟨by decide, by decide⟩ h := by
    rcases tadj_eq h54 with h1 | h1
    · exact ⟨(tourSucc f).symm _, tadj_pred f _,
        fun he => tourSucc_ne_symm f hN _ (h1.symm.trans he.symm)⟩
    · exact ⟨tourSucc f _, tadj_succ f _, fun he => tourSucc_ne_symm f hN _ (he.trans h1)⟩
  rcases (nbrs_gPt_g5 h X).mp (tadj_dgEdge hf hsymm hX) with
    h1 | h2 | ⟨c, hc, hlt, -, rfl⟩ | ⟨hmax, m, hm, rfl⟩
  · exact absurd h1 hXne
  · exfalso
    have h2ta : TAdj f (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g5 ⟨by decide, by decide⟩ h) := TAdj_symm (h2 ▸ hX)
    have h34 : TAdj f (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g4 ⟨by decide, by decide⟩ (hEdge_symm h)) :=
      TAdj_symm (forced_g4 f hf (hEdge_symm h)).1
    rcases tadj_two h34 (TAdj_symm hS) (gPt_ne_tag (by decide) _ _) h2ta with hE | hE
    · exact gPt_ne_tag (by decide) h (hEdge_symm h) hE
    · exact gPt_ne_tag (by decide) h (hEdge_symm h) hE
  · exact Or.inr ⟨c, hc, hlt, hX⟩
  · refine Or.inl ⟨hmax, ?_⟩
    rcases tadj_eq hX with h1 | h1
    · exact Or.inl (by rw [← h1]; rfl)
    · exact Or.inr (by rw [← h1]; rfl)

/-- **A used chain-link straightens the earlier side.** If the tour uses the
chain edge `⟨g0,(a,b)⟩–⟨g5,(a,c)⟩`, both tour-slots of `⟨g5,(a,c)⟩` are known, so
its cross edge is unused and (by `prop_g3`) the side `(c,a)` is straight. -/
theorem straight_of_chain_down {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b c : A} (h : HEdge a b) (hc : HEdge a c)
    (hch : TAdj f (gPt .g0 ⟨by decide, by decide⟩ h) (gPt .g5 ⟨by decide, by decide⟩ hc)) :
    TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm hc))
      (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm hc)) := by
  have h54 : TAdj f (gPt .g5 ⟨by decide, by decide⟩ hc) (gPt .g4 ⟨by decide, by decide⟩ hc) :=
    TAdj_symm (forced_g4 f hf hc).2
  rcases prop_g3 f hf (hEdge_symm hc) with hstr | hcross
  · exact TAdj_symm hstr
  · exfalso
    rw [gPt_edge_irrel (hEdge_symm (hEdge_symm hc)) hc] at hcross
    rcases tadj_two h54 (TAdj_symm hch) (gPt_ne_tag (by decide) hc h)
        (TAdj_symm hcross) with hE | hE
    · exact gPt_ne_tag (by decide) (hEdge_symm hc) hc hE
    · exact gPt_ne_tag (by decide) (hEdge_symm hc) h hE

/-- **A used chain-link straightens the later side**, symmetrically: a tour edge
`⟨g5,(a,b)⟩–⟨g0,(a,c)⟩` fills both slots of `⟨g0,(a,c)⟩`, so its cross edge is
unused and (by `prop_g2`) the side `(c,a)` is straight. -/
theorem straight_of_chain_up {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a b c : A} (h : HEdge a b) (hc : HEdge a c)
    (hch : TAdj f (gPt .g5 ⟨by decide, by decide⟩ h) (gPt .g0 ⟨by decide, by decide⟩ hc)) :
    TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm hc))
      (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm hc)) := by
  have h01 : TAdj f (gPt .g0 ⟨by decide, by decide⟩ hc) (gPt .g1 ⟨by decide, by decide⟩ hc) :=
    TAdj_symm (forced_g1 f hf hc).1
  rcases prop_g2 f hf (hEdge_symm hc) with hstr | hcross
  · exact hstr
  · exfalso
    rw [gPt_edge_irrel (hEdge_symm (hEdge_symm hc)) hc] at hcross
    rcases tadj_two h01 (TAdj_symm hch) (gPt_ne_tag (by decide) hc h)
        (TAdj_symm hcross) with hE | hE
    · exact gPt_ne_tag (by decide) (hEdge_symm hc) hc hE
    · exact gPt_ne_tag (by decide) (hEdge_symm hc) h hE

/-! ### Counting: the active chains inject into the selectors -/

section Counting

variable [Fintype A]

open Classical in
/-- The neighbours of `a` as a finset. -/
noncomputable def nbrFinset (a : A) : Finset A := Finset.univ.filter (HEdge a)

omit [LinearOrder A] in
theorem mem_nbrFinset {a b : A} : b ∈ nbrFinset a ↔ HEdge a b := by simp [nbrFinset]

omit [LinearOrder A] in
theorem nbrFinset_nonempty {a : A} (h : ∃ b, HEdge a b) : (nbrFinset a).Nonempty := by
  obtain ⟨b, hb⟩ := h; exact ⟨b, mem_nbrFinset.mpr hb⟩

/-- The least neighbour of `a` (the second coordinate of its chain entrance). -/
noncomputable def minNbr {a : A} (h : ∃ b, HEdge a b) : A :=
  (nbrFinset a).min' (nbrFinset_nonempty h)

/-- The greatest neighbour of `a` (the second coordinate of its chain exit). -/
noncomputable def maxNbr {a : A} (h : ∃ b, HEdge a b) : A :=
  (nbrFinset a).max' (nbrFinset_nonempty h)

theorem hEdge_minNbr {a : A} (h : ∃ b, HEdge a b) : HEdge a (minNbr h) :=
  mem_nbrFinset.mp ((nbrFinset a).min'_mem _)

theorem hEdge_maxNbr {a : A} (h : ∃ b, HEdge a b) : HEdge a (maxNbr h) :=
  mem_nbrFinset.mp ((nbrFinset a).max'_mem _)

theorem minNbr_le {a : A} (h : ∃ b, HEdge a b) {d : A} (hd : HEdge a d) : minNbr h ≤ d :=
  (nbrFinset a).min'_le d (mem_nbrFinset.mpr hd)

theorem le_maxNbr {a : A} (h : ∃ b, HEdge a b) {d : A} (hd : HEdge a d) : d ≤ maxNbr h :=
  (nbrFinset a).le_max' d (mem_nbrFinset.mpr hd)

/-- The chain entrance of `a`: `⟨g0,(a, minNbr a)⟩`. -/
noncomputable def entrancePt {a : A} (h : ∃ b, HEdge a b) : hamInterp.MapRel A :=
  gPt .g0 ⟨by decide, by decide⟩ (hEdge_minNbr h)

/-- The chain exit of `a`: `⟨g5,(a, maxNbr a)⟩`. -/
noncomputable def exitPt {a : A} (h : ∃ b, HEdge a b) : hamInterp.MapRel A :=
  gPt .g5 ⟨by decide, by decide⟩ (hEdge_maxNbr h)

/-- Distinct owners give distinct entrances (so `a ↦ entrancePt a` is injective). -/
theorem entrancePt_inj {a a' : A} (h : ∃ b, HEdge a b) (h' : ∃ b, HEdge a' b)
    (he : entrancePt h = entrancePt h') : a = a' := by
  have := congrArg (fun p : hamInterp.MapRel A => p.1.2 0) he
  simpa [entrancePt] using this

theorem exitPt_inj {a a' : A} (h : ∃ b, HEdge a b) (h' : ∃ b, HEdge a' b)
    (he : exitPt h = exitPt h') : a = a' := by
  have := congrArg (fun p : hamInterp.MapRel A => p.1.2 0) he
  simpa [exitPt] using this

/-- Entrance and exit never coincide (different tags), even across owners. -/
theorem entrancePt_ne_exitPt {a a' : A} (h : ∃ b, HEdge a b) (h' : ∃ b, HEdge a' b) :
    entrancePt h ≠ exitPt h' := by
  have : (entrancePt h).1.1 ≠ (exitPt h').1.1 := by simp [entrancePt, exitPt]
  exact fun he => this (congrArg (fun p : hamInterp.MapRel A => p.1.1) he)

/-- The selector tour-neighbour of `v` (well-defined when `v` has one): the tour
successor if that is the selector, else the predecessor. -/
noncomputable def selOf {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) (v : hamInterp.MapRel A) :
    hamInterp.MapRel A :=
  if isSel (tourSucc f v) then tourSucc f v else (tourSucc f).symm v

/-- Which tour-slot direction of the selector `s` points back at the vertex. -/
noncomputable def bit {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) (v : hamInterp.MapRel A) : Bool :=
  decide (isSel (tourSucc f v))

/-- Recover a vertex from its selector-neighbour and the slot direction. -/
noncomputable def recover {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (s : hamInterp.MapRel A) (β : Bool) : hamInterp.MapRel A :=
  if β then (tourSucc f).symm s else tourSucc f s

omit [Fintype A] in
/-- The recovery is exact: `v` is read back from `selOf v` and `bit v`. -/
theorem recover_selOf {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) (v : hamInterp.MapRel A) :
    recover f (selOf f v) (bit f v) = v := by
  unfold recover selOf bit
  by_cases h : isSel (tourSucc f v)
  · rw [if_pos (decide_eq_true_eq.mpr h), if_pos h, Equiv.symm_apply_apply]
  · rw [if_neg (by rw [decide_eq_true_eq]; exact h), if_neg h, Equiv.apply_symm_apply]

omit [Fintype A] in
/-- When `v` has a selector tour-neighbour, `selOf v` is that selector. -/
theorem isSel_selOf {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) {v : hamInterp.MapRel A}
    (h : isSel (tourSucc f v) ∨ isSel ((tourSucc f).symm v)) : isSel (selOf f v) := by
  unfold selOf
  by_cases hs : isSel (tourSucc f v)
  · rwa [if_pos hs]
  · rw [if_neg hs]; exact h.resolve_left hs

/-- `a` is *active* in tour `f`: both its chain entrance and its chain exit are
tour-adjacent to a selector (so its whole chain is a selector-to-selector arc). -/
def Active {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A) (a : A) : Prop :=
  ∃ h : ∃ b, HEdge a b,
    (isSel (tourSucc f (entrancePt h)) ∨ isSel ((tourSucc f).symm (entrancePt h))) ∧
      (isSel (tourSucc f (exitPt h)) ∨ isSel ((tourSucc f).symm (exitPt h)))

open Classical in
/-- The entrance (`d = false`) or exit (`d = true`) of `a`; junk if `a` is isolated. -/
noncomputable def ptOf [Nonempty (hamInterp.MapRel A)] (a : A) (d : Bool) : hamInterp.MapRel A :=
  if ha : ∃ b, HEdge a b then (bif d then exitPt ha else entrancePt ha) else Classical.arbitrary _

/-- For an active vertex, `ptOf` really is the entrance/exit, which has a selector
tour-neighbour; hence `selOf (ptOf …)` is a selector. -/
theorem isSel_selOf_ptOf {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    [Nonempty (hamInterp.MapRel A)] {a : A} (ha : Active f a) (d : Bool) :
    isSel (selOf f (ptOf a d)) := by
  obtain ⟨h, hE, hX⟩ := ha
  have hpt : ptOf a d = bif d then exitPt h else entrancePt h := by
    rw [ptOf, dif_pos h]
  rw [hpt]
  cases d
  · exact isSel_selOf f hE
  · exact isSel_selOf f hX

/-- The mark carried by `selOf (ptOf …)` of an active vertex is marked. -/
theorem marked_of_active {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    [Nonempty (hamInterp.MapRel A)] {a : A} (ha : Active f a) (d : Bool) :
    MGMarked ((selOf f (ptOf a d)).1.2 0) := by
  obtain ⟨m, hm, hsel⟩ := eq_selPt_of_tag (isSel_selOf_ptOf f ha d)
  rw [hsel]; simpa using hm

/-- **The active vertices inject into the marked ones**: `|C| ≤ |marked|`. The map
`(a, entrance/exit) ↦ (selector, slot-direction)` is injective — the selector and
slot pin down the entrance/exit vertex (`recover_selOf`), whose owner and role
(g0 vs g5) pin down `a`. Two chain-endpoints per active chain, two slots per
selector, so `2|C| ≤ 2|marked|`. -/
theorem active_ncard_le {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    [Nonempty (hamInterp.MapRel A)] :
    {a | Active f a}.ncard ≤ {m : A | MGMarked m}.ncard := by
  classical
  set activeF : Finset A := Finset.univ.filter (Active f) with hactiveF
  set markedF : Finset A := Finset.univ.filter MGMarked with hmarkedF
  set φ : A × Bool → A × Bool :=
    fun p => ((selOf f (ptOf p.1 p.2)).1.2 0, bit f (ptOf p.1 p.2)) with hφ
  -- `selOf (ptOf …)` of an active vertex is pinned down by its mark.
  have hsel_eq : ∀ {a a' : A} {d d' : Bool}, Active f a → Active f a' →
      (selOf f (ptOf a d)).1.2 0 = (selOf f (ptOf a' d')).1.2 0 →
      selOf f (ptOf a d) = selOf f (ptOf a' d') := by
    intro a a' d d' ha ha' hmm
    obtain ⟨m1, hm1, h1⟩ := eq_selPt_of_tag (isSel_selOf_ptOf f ha d)
    obtain ⟨m2, hm2, h2⟩ := eq_selPt_of_tag (isSel_selOf_ptOf f ha' d')
    have k1 : (selOf f (ptOf a d)).1.2 0 = m1 := by rw [h1]; exact selPt_fst hm1
    have k2 : (selOf f (ptOf a' d')).1.2 0 = m2 := by rw [h2]; exact selPt_fst hm2
    have : m1 = m2 := k1.symm.trans (hmm.trans k2)
    rw [h1, h2]; subst this; rfl
  have hmaps : ∀ p ∈ activeF ×ˢ (Finset.univ : Finset Bool),
      φ p ∈ markedF ×ˢ (Finset.univ : Finset Bool) := by
    rintro ⟨a, d⟩ hp
    simp only [Finset.mem_product, hactiveF, hmarkedF, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true, hφ] at hp ⊢
    exact marked_of_active f hp d
  have hinj : Set.InjOn φ (↑(activeF ×ˢ (Finset.univ : Finset Bool)) : Set (A × Bool)) := by
    rintro ⟨a, d⟩ hp ⟨a', d'⟩ hq hpq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hactiveF, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp hq
    have hpq' := hpq
    simp only [hφ, Prod.mk.injEq] at hpq'
    obtain ⟨hmm, hbit⟩ := hpq'
    -- recover the entrance/exit vertex from (selector, slot)
    have hpt : ptOf a d = ptOf a' d' := by
      rw [← recover_selOf f (ptOf a d), ← recover_selOf f (ptOf a' d'),
        hsel_eq hp.1 hq.1 hmm, hbit]
    -- unfold ptOf for active vertices
    obtain ⟨hE, -⟩ := hp.1; obtain ⟨hE', -⟩ := hq.1
    rw [ptOf, dif_pos hE] at hpt; rw [ptOf, dif_pos hE'] at hpt
    cases d <;> cases d' <;> simp only [Bool.cond_true, Bool.cond_false] at hpt
    · exact Prod.ext (entrancePt_inj hE hE' hpt) rfl
    · exact absurd hpt (entrancePt_ne_exitPt hE hE')
    · exact absurd hpt.symm (entrancePt_ne_exitPt hE' hE)
    · exact Prod.ext (exitPt_inj hE hE' hpt) rfl
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool] at hcard
  have hle : activeF.card ≤ markedF.card := by omega
  have e1 : {a | Active f a} = (↑activeF : Set A) := by
    rw [hactiveF]; ext a; simp
  have e2 : {m : A | MGMarked m} = (↑markedF : Set A) := by
    rw [hmarkedF]; ext m; simp
  rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact hle

/-- **Straightness reaches the entrance.** If some side `(b,a)` of `a`'s chain
is straight, the entrance slot of `⟨g0,(a,b)⟩` is a selector or a chain-link
(`g0_other`); a chain-link keeps the walked side straight
(`straight_of_chain_down`), so by well-founded descent along `a`'s neighbour
list the chain entrance has a selector tour-neighbour. -/
theorem entrance_sel_of_straight {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a : A} :
    ∀ b : A, ∀ h : HEdge a b,
      TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h)) →
      isSel (tourSucc f (entrancePt ⟨b, h⟩)) ∨
        isSel ((tourSucc f).symm (entrancePt ⟨b, h⟩)) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
    intro h hS
    rcases g0_other f hf h hS with ⟨hmin, hsel⟩ | ⟨c, hc, hlt, hch⟩
    · have hb : minNbr (⟨b, h⟩ : ∃ d, HEdge a d) = b :=
        le_antisymm (minNbr_le ⟨b, h⟩ h) (hmin _ (hEdge_minNbr ⟨b, h⟩))
      have he : entrancePt (⟨b, h⟩ : ∃ d, HEdge a d) = gPt .g0 ⟨by decide, by decide⟩ h :=
        eq_gPt_of_val h rfl rfl hb
      rw [he]
      exact hsel
    · exact IH c hlt hc (straight_of_chain_down f hf h hc hch)

/-- **Straightness reaches the exit**, symmetrically: well-founded ascent along
`a`'s neighbour list through `g5_other` and `straight_of_chain_up`. -/
theorem exit_sel_of_straight {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {a : A} :
    ∀ b : A, ∀ h : HEdge a b,
      TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h))
        (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h)) →
      isSel (tourSucc f (exitPt ⟨b, h⟩)) ∨ isSel ((tourSucc f).symm (exitPt ⟨b, h⟩)) := by
  intro b
  induction b using WellFoundedGT.induction with
  | ind b IH =>
    intro h hS
    rcases g5_other f hf h hS with ⟨hmax, hsel⟩ | ⟨c, hc, hlt, hch⟩
    · have hb : maxNbr (⟨b, h⟩ : ∃ d, HEdge a d) = b :=
        le_antisymm (hmax _ (hEdge_maxNbr ⟨b, h⟩)) (le_maxNbr ⟨b, h⟩ h)
      have he : exitPt (⟨b, h⟩ : ∃ d, HEdge a d) = gPt .g5 ⟨by decide, by decide⟩ h :=
        eq_gPt_of_val h rfl rfl hb
      rw [he]
      exact hsel
    · exact IH c hlt hc (straight_of_chain_up f hf h hc hch)

/-- **A straight side makes the opposite owner active**: if the side `(u,v)` of
the edge `{u,v}` is traversed straight through `g2–g3`, then `v`'s chain runs
selector to selector, so `v` is active. -/
theorem active_of_straight {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i))) {u v : A} (h : HEdge u v)
    (hS : TAdj f (gPt .g2 ⟨by decide, by decide⟩ h) (gPt .g3 ⟨by decide, by decide⟩ h)) :
    Active f v := by
  have h' : HEdge v u := hEdge_symm h
  have hS' : TAdj f (gPt .g2 ⟨by decide, by decide⟩ (hEdge_symm h'))
      (gPt .g3 ⟨by decide, by decide⟩ (hEdge_symm h')) := hS
  exact ⟨⟨u, h'⟩, entrance_sel_of_straight f hf u h' hS', exit_sel_of_straight f hf u h' hS'⟩

/-- **Cover property**: every edge has an *active* endpoint. The gadget of
`{a,b}` is traversed straight on the `a`-side or the `b`-side (`side_straight`),
and a straight side activates the opposite owner (`active_of_straight`). -/
theorem cover_property {N : ℕ} (f : Fin N ≃ hamInterp.MapRel A)
    (hf : ∀ i, DGEdge (f i) (f (nextIdx i)))
    {a b : A} (h : HEdge a b) : Active f a ∨ Active f b := by
  rcases side_straight f hf h with hstr | hstr
  · exact Or.inr (active_of_straight f hf h hstr)
  · exact Or.inl (active_of_straight f hf (hEdge_symm h) hstr)

end Counting

end DescriptiveComplexity
