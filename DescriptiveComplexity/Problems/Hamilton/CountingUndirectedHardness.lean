/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.CountingUndirected
import DescriptiveComplexity.Problems.Hamilton.CountingHardness

/-!
# #Hamilton Circuit is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpHamCircuit_sharpP_parsimoniousComplete`, by a reduction from
the directed problem (`DescriptiveComplexity.sharpDirHamCircuit_parsimonious_sharpHamCircuit`),
order-free and without a domain formula.

The reduction of the library in the other direction, doubling each edge, is
not parsimonious for edge sets: an undirected circuit becomes its two
orientations. The classical reduction in this direction is. Each vertex `x`
is split into a path `(i, x) – (m, x) – (o, x)`, and an arc `x → y` becomes
the edge `(o, x) – (i, y)` (`DescriptiveComplexity.Split.SArc`).

The middle vertex has its two path neighbours and nothing else, so a circuit
passes through it, in one direction or the other. Entering a vertex by `i`
and leaving it by `o` forces the same at the next vertex – were it entered by
`o`, its `i` would be reached twice – and so, by induction along the circuit
(`DescriptiveComplexity.IsCircuit.induction`), at every vertex
(`DescriptiveComplexity.Split.forward_all`). An undirected circuit of the split graph
thus has an orientation in which every vertex is traversed `i, m, o`, and that
orientation is a directed circuit of the graph, read on the edges
`(o, x) – (i, y)`. Directed circuits and edge sets correspond bijectively
(`DescriptiveComplexity.Split.splitEquiv`).

Both directions of the correspondence build a circuit from a potential
(`DescriptiveComplexity.isCircuit_of_potential`): the position of the vertex in the
other circuit.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace Split

open Language Structure

/-- The three copies of a vertex. -/
inductive T3 : Type
  /-- The entry copy. -/
  | i
  /-- The middle copy. -/
  | m
  /-- The exit copy. -/
  | o
  deriving DecidableEq

instance : Fintype T3 := ⟨{.i, .m, .o}, by intro x; cases x <;> simp⟩

instance : Nonempty T3 := ⟨.m⟩

section Semantic

variable {A : Type}

/-- The arcs of the split graph of a relation: the path of each vertex, and
one arc from exit to entry per arc of the relation. -/
def SArc (R : A → A → Prop) : T3 × A → T3 × A → Prop
  | (.i, x), (.m, y) => x = y
  | (.m, x), (.o, y) => x = y
  | (.o, x), (.i, y) => R x y
  | _, _ => False

/-- The edges of the split graph. -/
def SEdge (R : A → A → Prop) (p q : T3 × A) : Prop := SArc R p q ∨ SArc R q p

theorem sedge_symm {R : A → A → Prop} {p q : T3 × A} (h : SEdge R p q) : SEdge R q p :=
  h.symm

theorem sedge_m {R : A → A → Prop} {x : A} {q : T3 × A} (h : SEdge R (.m, x) q) :
    q = (.i, x) ∨ q = (.o, x) := by
  obtain ⟨t, y⟩ := q
  rcases h with h | h <;> cases t <;> simp only [SArc] at h
  · exact Or.inr (by rw [h])
  · exact Or.inl (by rw [h])

theorem sedge_o {R : A → A → Prop} {x : A} {q : T3 × A} (h : SEdge R (.o, x) q) :
    q = (.m, x) ∨ ∃ y, q = (.i, y) ∧ R x y := by
  obtain ⟨t, y⟩ := q
  rcases h with h | h <;> cases t <;> simp only [SArc] at h
  · exact Or.inr ⟨y, rfl, h⟩
  · exact Or.inl (by rw [h])

theorem sedge_i {R : A → A → Prop} {y : A} {q : T3 × A} (h : SEdge R (.i, y) q) :
    q = (.m, y) ∨ ∃ x, q = (.o, x) ∧ R x y := by
  obtain ⟨t, x⟩ := q
  rcases h with h | h <;> cases t <;> simp only [SArc] at h
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨x, rfl, h⟩

variable [Finite A]

/-! ### From a directed circuit to a circuit of the split graph -/

/-- **A directed circuit, split, is a circuit of the split graph.** -/
theorem isCircuit_sarc [Nonempty A] {R Nxt : A → A → Prop} (h : IsCircuit R Nxt) :
    IsCircuit (SEdge R) (SArc Nxt) := by
  classical
  obtain ⟨htot, hfun, hsurj, -, hR, -⟩ := h.local
  obtain ⟨Le, hlin, hiff, -⟩ := h
  let : LinearOrder A := hlin.toLinearOrder
  obtain ⟨mx, hmx⟩ := Finite.exists_max (id : A → A)
  let idx : T3 → ℕ := fun t => match t with
    | .i => 0
    | .m => 1
    | .o => 2
  refine isCircuit_of_potential (K := A ×ₗ ℕ) (fun p => ?_) (fun p q q' hq hq' => ?_)
    (fun q => ?_) (fun p q hpq => ?_) (fun p => toLex (p.2, idx p.1)) (.o, mx)
    (fun p q hpq hne => ?_)
  · obtain ⟨t, x⟩ := p
    cases t
    · exact ⟨(.m, x), rfl⟩
    · exact ⟨(.o, x), rfl⟩
    · obtain ⟨y, hy⟩ := htot x
      exact ⟨(.i, y), hy⟩
  · obtain ⟨t, x⟩ := p
    obtain ⟨t₁, y₁⟩ := q
    obtain ⟨t₂, y₂⟩ := q'
    cases t <;> cases t₁ <;> simp only [SArc] at hq <;> cases t₂ <;> simp only [SArc] at hq'
    · rw [← hq, ← hq']
    · rw [← hq, ← hq']
    · rw [hfun _ _ _ hq hq']
  · obtain ⟨t, y⟩ := q
    cases t
    · obtain ⟨x, hx⟩ := hsurj y
      exact ⟨(.o, x), hx⟩
    · exact ⟨(.i, y), rfl⟩
    · exact ⟨(.m, y), rfl⟩
  · obtain ⟨t, x⟩ := p
    obtain ⟨t', y⟩ := q
    cases t <;> cases t' <;> simp only [SArc] at hpq
    · exact Or.inl hpq
    · exact Or.inl hpq
    · exact Or.inl (hR _ _ hpq)
  · obtain ⟨t, x⟩ := p
    obtain ⟨t', y⟩ := q
    rw [Prod.Lex.toLex_lt_toLex]
    cases t <;> cases t' <;> simp only [SArc] at hpq
    · exact Or.inr ⟨hpq, by simp [idx]⟩
    · exact Or.inr ⟨hpq, by simp [idx]⟩
    · rcases (hiff x y).mp hpq with hs | ⟨hmax, -⟩
      · exact Or.inl ⟨hs.1, fun hyx => hs.2.1 (hlin.2.2.1 _ _ hs.1 hyx)⟩
      · have hxm : x = mx := hlin.2.2.1 _ _ (hmx x) (hmax mx)
        exact absurd (by rw [hxm]) hne

/-! ### From a circuit of the split graph to a directed circuit -/

section Reverse

variable {R : A → A → Prop} {N : T3 × A → T3 × A → Prop}

/-- A circuit of the split graph does not go back and forth: the graph has
more than two vertices. -/
theorem no2 (hN : IsCircuit (SEdge R) N) (a : A) {u v : T3 × A} (h : N u v) (h' : N v u) :
    False := by
  have htwo := hN.local.2.2.2.2.2 u v h h'
  rcases htwo (.i, a) with h₁ | h₁ <;> rcases htwo (.m, a) with h₂ | h₂ <;>
    rcases htwo (.o, a) with h₃ | h₃ <;>
    first
      | exact absurd (h₁.trans h₂.symm) (by simp)
      | exact absurd (h₁.trans h₃.symm) (by simp)
      | exact absurd (h₂.trans h₃.symm) (by simp)

/-- The circuit passes through the middle copy of a vertex, one way or the
other. -/
theorem through_m (hN : IsCircuit (SEdge R) N) (x : A) :
    (N (.i, x) (.m, x) ∧ N (.m, x) (.o, x)) ∨ (N (.o, x) (.m, x) ∧ N (.m, x) (.i, x)) := by
  obtain ⟨htot, -, hsurj, -, hR, -⟩ := hN.local
  obtain ⟨v, hv⟩ := htot (.m, x)
  obtain ⟨v', hv'⟩ := hsurj (.m, x)
  rcases sedge_m (hR _ _ hv) with rfl | rfl <;>
    rcases sedge_m (sedge_symm (hR _ _ hv')) with rfl | rfl
  · exact (no2 hN x hv hv').elim
  · exact Or.inr ⟨hv', hv⟩
  · exact Or.inl ⟨hv', hv⟩
  · exact (no2 hN x hv hv').elim

/-- A vertex traversed forward is left for the entry of another vertex. -/
theorem exit_of_forward (hN : IsCircuit (SEdge R) N) {x : A} (hx : N (.m, x) (.o, x)) :
    ∃ y, N (.o, x) (.i, y) ∧ R x y := by
  obtain ⟨htot, -, -, -, hR, -⟩ := hN.local
  obtain ⟨v, hv⟩ := htot (.o, x)
  rcases sedge_o (hR _ _ hv) with rfl | ⟨y, rfl, hxy⟩
  · exact (no2 hN x hx hv).elim
  · exact ⟨y, hv, hxy⟩

/-- **If one vertex is traversed forward, all are.** -/
theorem forward_all (hN : IsCircuit (SEdge R) N) {x₀ : A} (h₀ : N (.i, x₀) (.m, x₀)) :
    ∀ x, N (.i, x) (.m, x) := by
  obtain ⟨-, hfun, -, hinj, hR, -⟩ := hN.local
  have key := hN.induction (P := fun p => N (.i, p.2) (.m, p.2)) (.i, x₀) h₀ (by
    rintro ⟨t, x⟩ ⟨t', y⟩ hpq hP
    have hP' : N (.i, x) (.m, x) := hP
    change N (.i, y) (.m, y)
    rcases hR _ _ hpq with h | h <;> cases t <;> cases t' <;> simp only [SArc] at h
    · exact h ▸ hP'
    · exact h ▸ hP'
    · -- `(o, x) → (i, y)`: were `y` traversed backward, `(i, y)` would be reached twice
      rcases through_m hN y with hf | hb
      · exact hf.1
      · exact absurd (hinj _ _ _ hpq hb.2) (by simp)
    · -- `(i, x) → (o, y)`: but `(i, x)` is left for `(m, x)`
      exact absurd (hfun _ _ _ hpq hP') (by simp)
    · exact h ▸ hP'
    · exact h ▸ hP')
  exact fun x => key (.i, x)

/-- **A forward circuit of the split graph is a split directed circuit.** -/
theorem exists_circuit_of_forward [Nonempty A] (hN : IsCircuit (SEdge R) N)
    (hfwd : ∀ x, N (.i, x) (.m, x)) :
    IsCircuit R (fun x y => N (.o, x) (.i, y)) ∧
      ∀ p q, N p q ↔ SArc (fun x y => N (.o, x) (.i, y)) p q := by
  classical
  obtain ⟨htot, hfun, hsurj, hinj, hR, -⟩ := hN.local
  have hmo : ∀ x, N (.m, x) (.o, x) := fun x => by
    rcases through_m hN x with h | h
    · exact h.2
    · exact (no2 hN x (hfwd x) h.2).elim
  have hrel : ∀ p q, N p q ↔ SArc (fun x y => N (.o, x) (.i, y)) p q := by
    rintro ⟨t, x⟩ ⟨t', y⟩
    constructor
    · intro h
      cases t
      · rw [hfun _ _ _ h (hfwd x)]
        rfl
      · rw [hfun _ _ _ h (hmo x)]
        rfl
      · obtain ⟨z, hz, -⟩ := exit_of_forward hN (hmo x)
        rw [hfun _ _ _ h hz]
        exact hz
    · intro h
      cases t <;> cases t' <;> simp only [SArc] at h
      · exact h ▸ hfwd x
      · exact h ▸ hmo x
      · exact h
  refine ⟨?_, hrel⟩
  have hN₀ := hN
  obtain ⟨Le, hlin, hiff, -⟩ := hN₀
  let : LinearOrder (T3 × A) := hlin.toLinearOrder
  obtain ⟨M, hM⟩ := Finite.exists_max (id : T3 × A → T3 × A)
  have hlt : ∀ p q : T3 × A, N p q → p.2 ≠ M.2 → p < q := by
    intro p q hpq hne
    rcases (hiff p q).mp hpq with hs | ⟨hmax, -⟩
    · exact ⟨hs.1, fun hqp => hs.2.1 (hlin.2.2.1 _ _ hs.1 hqp)⟩
    · exact absurd (congrArg Prod.snd (hlin.2.2.1 _ _ (hM p) (hmax M))).symm
        (fun h => hne h.symm)
  refine isCircuit_of_potential (fun x => ?_) (fun x y y' hy hy' => ?_) (fun y => ?_)
    (fun x y hxy => ?_) (fun x => ((.i, x) : T3 × A)) M.2 (fun x y hxy hne => ?_)
  · obtain ⟨y, hy, -⟩ := exit_of_forward hN (hmo x)
    exact ⟨y, hy⟩
  · exact congrArg Prod.snd (hfun _ _ _ hy hy')
  · obtain ⟨q, hq⟩ := hsurj (.i, y)
    rcases sedge_i (sedge_symm (hR _ _ hq)) with rfl | ⟨x, rfl, -⟩
    · exact (no2 hN y (hfwd y) hq).elim
    · exact ⟨x, hq⟩
  · rcases hR _ _ hxy with h | h
    · exact h
    · exact (h : False).elim
  · exact (hlt _ _ (hfwd x) hne).trans ((hlt _ _ (hmo x) hne).trans (hlt _ _ hxy hne))

end Reverse

/-! ### The correspondence -/

omit [Finite A] in
/-- A split relation is read back on its exit-to-entry arcs. -/
theorem sarc_sym_iff {Nxt : A → A → Prop} (x y : A) :
    (SArc Nxt (.o, x) (.i, y) ∨ SArc Nxt (.i, y) (.o, x)) ↔ Nxt x y :=
  ⟨fun h => h.elim id fun h => (h : False).elim, Or.inl⟩

/-- **The undirected circuits of the split graph are the directed circuits of
the graph**, bijectively. -/
noncomputable def splitEquiv [Nonempty A] (R : A → A → Prop) :
    {Nxt : A → A → Prop // IsCircuit R Nxt} ≃
      {E : T3 × A → T3 × A → Prop // IsUCircuit (SEdge R) E} :=
  Equiv.ofBijective
    (fun Nxt => ⟨fun p q => SArc Nxt.1 p q ∨ SArc Nxt.1 q p, SArc Nxt.1, isCircuit_sarc Nxt.2,
      fun _ _ => Iff.rfl⟩) (by
    constructor
    · intro Nxt Nxt' hval
      refine Subtype.ext (funext fun x => funext fun y => propext ?_)
      have h := congrFun (congrFun (congrArg Subtype.val hval) (.o, x)) (.i, y)
      exact (sarc_sym_iff x y).symm.trans ((iff_of_eq h).trans (sarc_sym_iff x y))
    · rintro ⟨E, N, hN, hE⟩
      obtain ⟨x₀⟩ := ‹Nonempty A›
      -- orient the circuit so that `x₀` is traversed forward
      obtain ⟨N', hN', hE', h₀⟩ : ∃ N', IsCircuit (SEdge R) N' ∧
          (∀ p q, E p q ↔ (N' p q ∨ N' q p)) ∧ N' (.i, x₀) (.m, x₀) := by
        rcases through_m hN x₀ with h | h
        · exact ⟨N, hN, hE, h.1⟩
        · exact ⟨fun p q => N q p, hN.reverse fun _ _ h => sedge_symm h,
            fun p q => (hE p q).trans or_comm, h.2⟩
      obtain ⟨hc, hrel⟩ := exists_circuit_of_forward hN' (forward_all hN' h₀)
      refine ⟨⟨_, hc⟩, Subtype.ext (funext fun p => funext fun q => propext ?_)⟩
      exact (or_congr (hrel p q).symm (hrel q p).symm).trans (hE' p q).symm)

end Semantic

/-! ### The interpretation -/

/-- The arc formulas of the split graph, by tags. -/
def splitF : T3 → T3 → Language.digraph.Formula (Fin 2 × Fin 1)
  | .i, .m => fo%⟨u, v⟩ u ≐ v
  | .m, .o => fo%⟨u, v⟩ u ≐ v
  | .o, .i => fo%⟨u, v⟩ dgArc(u, v)
  | _, _ => ⊥

/-- The interpretation splitting each vertex of a digraph in three. -/
def splitInterp : FOInterpretation Language.digraph Language.digraph T3 1 where
  relFormula {n} R :=
    match n, R with
    | _, .arc => fun t => splitF (t 0) (t 1)

section Interp

variable {A : Type} [Language.digraph.Structure A]

/-- The interpreted universe is three copies of the input. -/
def splitPts (A : Type) : splitInterp.Map A ≃ T3 × A where
  toFun p := (p.1, p.2 0)
  invFun q := (q.1, fun _ => q.2)
  left_inv p := Prod.ext rfl (funext fun j => congrArg p.2 (Subsingleton.elim 0 j))
  right_inv _ := rfl

theorem split_arc (t t' : T3) (w w' : Fin 1 → A) :
    RelMap (M := splitInterp.Map A) dgArc ![(t, w), (t', w')] ↔
      SArc (fun x y : A => DGArc x y) (t, w 0) (t', w' 0) := by
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [splitInterp, splitF, SArc, DGArc, Formula.realize_rel₂]

theorem dgArc_split (p q : splitInterp.Map A) :
    DGArc p q ↔ SArc (fun x y : A => DGArc x y) (splitPts A p) (splitPts A q) := by
  obtain ⟨t, w⟩ := p
  obtain ⟨t', w'⟩ := q
  exact split_arc t t' w w'

variable (A) [Finite A] [Nonempty A]

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpHamCircuit_split :
    SharpHamCircuit (splitInterp.Map A) = SharpDirHamCircuit A := by
  have := splitInterp.map_finite A
  have hW : Finite (T3 × A) := inferInstance
  rw [sharpHamCircuit_apply, sharpDirHamCircuit_apply]
  refine (Nat.card_congr (ucircuitEquiv (splitPts A)
    (RB := SEdge fun x y : A => DGArc x y)
    fun p q => or_congr (dgArc_split p q) (dgArc_split q p))).trans ?_
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hW)).trans ?_
  refine (Nat.card_congr (splitEquiv fun x y : A => DGArc x y)).symm.trans ?_
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right ‹Finite A›)).symm

end Interp

end Split

open Split in
/-- **#Directed Hamilton Circuit reduces parsimoniously to #Hamilton Circuit**,
by splitting each vertex in three; no order and no domain formula are
needed. -/
def sharpDirHamCircuit_parsimonious_sharpHamCircuit :
    SharpDirHamCircuit ≤ᵖ SharpHamCircuit where
  Tag := T3
  dim := 1
  toInterpretation := splitInterp
  correct A _ _ _ := (sharpHamCircuit_split A).symm

/-- #Hamilton Circuit is parsimoniously `#P`-hard. -/
theorem sharpHamCircuit_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpHamCircuit :=
  SharpP.parsimoniousHard_of_parsimonious sharpDirHamCircuit_parsimonious_sharpHamCircuit
    sharpDirHamCircuit_sharpP_parsimoniousHard

/-- **#Hamilton Circuit is parsimoniously `#P`-complete**: counting the Hamilton
circuits of an undirected graph, as sets of edges. -/
theorem sharpHamCircuit_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpHamCircuit :=
  ⟨sharpHamCircuit_mem_sharpP, sharpHamCircuit_sharpP_parsimoniousHard⟩

end DescriptiveComplexity
