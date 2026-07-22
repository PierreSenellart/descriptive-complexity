/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Defs
import DescriptiveComplexity.OccurrenceFormulas

/-!
# SAT reduces to Clique by an ordered FO reduction

The classical reduction from satisfiability to the clique threshold problem,
as a first-order interpretation over the ordered expansion of the language of
CNF instances:
`DescriptiveComplexity.sat_ordered_fo_reduction_clique : SAT ≤ᶠᵒ[≤] Clique`.

Vertices of the interpreted marked graph are tagged pairs of elements of the
CNF structure (`DescriptiveComplexity.SatCliqueTag`, dimension 2):

* `(pos, (c, x))` / `(neg, (c, x))`: a positive/negative occurrence of the
  variable `x` in the clause `c`; two occurrence vertices are adjacent iff
  both are genuine, they belong to *distinct* clauses, and they are not
  conflicting – the same variable with opposite signs
  (`DescriptiveComplexity.SatToClique.Compat`);
* `(cl, (c, c))`: one *marked* vertex per clause, isolated in the graph, so
  that the cardinality of the marked set is the number of clauses.

A clique at least as large as the marked set must pick one occurrence per
clause, pairwise non-conflicting, which is exactly a satisfying assignment;
conversely, choosing a true literal in each clause under a satisfying
assignment yields such a clique. Empty clauses – which make the CNF
unsatisfiable but carry no occurrence vertex – are handled by a spoiler in
the mark formula: if some clause is empty, *every* vertex is marked, and no
clique can be as large as the whole universe since clause vertices are
isolated.

The formulas do not mention the order. The reduction is nevertheless packaged
as an ordered one because `DescriptiveComplexity.Clique` folds finiteness of the
universe into its yes-instances, so correctness can only hold on finite
structures – exactly the correctness contract of
`DescriptiveComplexity.OrderedFOReduction` (a plain `FOReduction` would have to be
correct on infinite structures as well, where SAT can hold while no clique
instance is a yes-instance).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-- Tags of the clique instance interpreted in a CNF structure. -/
inductive SatCliqueTag : Type
  /-- Positive-occurrence vertex, at pairs `(c, x)`. -/
  | pos
  /-- Negative-occurrence vertex, at pairs `(c, x)`. -/
  | neg
  /-- Marked clause vertex, at diagonal pairs `(c, c)`. -/
  | cl
  deriving DecidableEq, Nonempty

instance : Fintype SatCliqueTag where
  elems := {.pos, .neg, .cl}
  complete x := by cases x <;> decide

/-- The occurrence tag of a sign. -/
def SatCliqueTag.ofSign : Bool → SatCliqueTag
  | true => .pos
  | false => .neg

namespace SatToClique

/-! ### The semantic side -/

section Semantics

variable {A : Type} [Language.sat.Structure A]

/-- Two genuine literal occurrences in distinct clauses that are not
conflicting (the same variable with opposite signs): the adjacency condition
between occurrence vertices, on the semantic side. -/
def Compat (s₁ s₂ : Bool) (w₁ w₂ : Fin 2 → A) : Prop :=
  OccIn (w₁ 0) (w₁ 1) s₁ ∧ OccIn (w₂ 0) (w₂ 1) s₂ ∧ w₁ 0 ≠ w₂ 0 ∧
    (s₁ = s₂ ∨ w₁ 1 ≠ w₂ 1)

/-- The adjacency condition of the interpreted graph: occurrence vertices are
adjacent iff compatible, clause vertices are isolated. -/
def AdjCore : SatCliqueTag → (Fin 2 → A) → SatCliqueTag → (Fin 2 → A) → Prop
  | .pos, w₁, .pos, w₂ => Compat true true w₁ w₂
  | .pos, w₁, .neg, w₂ => Compat true false w₁ w₂
  | .neg, w₁, .pos, w₂ => Compat false true w₁ w₂
  | .neg, w₁, .neg, w₂ => Compat false false w₁ w₂
  | _, _, _, _ => False

/-- The marking condition of the interpreted graph: diagonal clause vertices
– or every vertex, if some clause is empty. -/
def MarkedCore : SatCliqueTag → (Fin 2 → A) → Prop
  | .cl, w => (w 0 = w 1 ∧ IsCl (w 0)) ∨ ∃ c : A, EmptyCl c
  | _, _ => ∃ c : A, EmptyCl c

/-- A vertex stands for an actual literal occurrence of the CNF structure. -/
def Genuine : SatCliqueTag → (Fin 2 → A) → Prop
  | .pos, w => OccIn (w 0) (w 1) true
  | .neg, w => OccIn (w 0) (w 1) false
  | .cl, _ => False

theorem adjCore_ofSign {s₁ s₂ : Bool} {w₁ w₂ : Fin 2 → A} :
    AdjCore (.ofSign s₁) w₁ (.ofSign s₂) w₂ ↔ Compat s₁ s₂ w₁ w₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

theorem AdjCore.exists_sign {t₁ t₂ : SatCliqueTag} {w₁ w₂ : Fin 2 → A}
    (h : AdjCore t₁ w₁ t₂ w₂) :
    ∃ s₁ s₂, t₁ = .ofSign s₁ ∧ t₂ = .ofSign s₂ ∧ Compat s₁ s₂ w₁ w₂ := by
  cases t₁ <;> cases t₂ <;> try exact (h : False).elim
  · exact ⟨true, true, rfl, rfl, h⟩
  · exact ⟨true, false, rfl, rfl, h⟩
  · exact ⟨false, true, rfl, rfl, h⟩
  · exact ⟨false, false, rfl, rfl, h⟩

theorem AdjCore.genuine_right {t₁ t₂ : SatCliqueTag} {w₁ w₂ : Fin 2 → A}
    (h : AdjCore t₁ w₁ t₂ w₂) : Genuine t₂ w₂ := by
  obtain ⟨s₁, s₂, rfl, rfl, hc⟩ := h.exists_sign
  cases s₂ <;> exact hc.2.1

theorem AdjCore.ne_clause {t₁ t₂ : SatCliqueTag} {w₁ w₂ : Fin 2 → A}
    (h : AdjCore t₁ w₁ t₂ w₂) : w₁ 0 ≠ w₂ 0 := by
  obtain ⟨s₁, s₂, rfl, rfl, hc⟩ := h.exists_sign
  exact hc.2.2.1

theorem Genuine.isCl {t : SatCliqueTag} {w : Fin 2 → A} (h : Genuine t w) :
    IsCl (w 0) := by
  cases t
  · exact OccIn.isCl h
  · exact OccIn.isCl h
  · exact (h : False).elim

end Semantics

/-! ### The formulas and the interpretation -/

/-- The adjacency formula between occurrence vertices of signs `s₁`, `s₂`:
the FO counterpart of `DescriptiveComplexity.SatToClique.Compat`. The free variable
`(i, j)` is the `j`-th component of the `i`-th vertex. -/
def compatF (s₁ s₂ : Bool) : satOrd.Formula (Fin 2 × Fin 2) :=
  occF s₁ (0, 0) (0, 1) ⊓ occF s₂ (1, 0) (1, 1) ⊓ ∼(eqF (0, 0) (1, 0)) ⊓
    (if s₁ = s₂ then ⊤ else ∼(eqF (0, 1) (1, 1)))

/-- The adjacency formulas of the interpretation, by tag. -/
def adjF : SatCliqueTag → SatCliqueTag → satOrd.Formula (Fin 2 × Fin 2)
  | .pos, .pos => compatF true true
  | .pos, .neg => compatF true false
  | .neg, .pos => compatF false true
  | .neg, .neg => compatF false false
  | _, _ => ⊥

/-- The mark formulas of the interpretation, by tag: diagonal clause vertices
– or everything, if some clause is empty. -/
noncomputable def markedF : SatCliqueTag → satOrd.Formula (Fin 1 × Fin 2)
  | .cl => (eqF (0, 0) (0, 1) ⊓ clF (0, 0)) ⊔ exEmptyClF
  | _ => exEmptyClF

/-- The interpretation producing, from an ordered CNF structure, its clique
threshold instance. -/
noncomputable def satToClique :
    FOInterpretation satOrd Language.markedGraph SatCliqueTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => adjF (t 0) (t 1)
    | _, .marked => fun t => markedF (t 0)

/-! ### Characterizations of the interpreted relations -/

section Characterization

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem realize_compatF {s₁ s₂ : Bool} {v : Fin 2 × Fin 2 → A} :
    (compatF s₁ s₂).Realize v ↔
      Compat s₁ s₂ (fun j => v (0, j)) (fun j => v (1, j)) := by
  by_cases h : s₁ = s₂ <;> simp [compatF, Compat, h, and_assoc]

theorem realize_adjF {t₁ t₂ : SatCliqueTag} {v : Fin 2 × Fin 2 → A} :
    (adjF t₁ t₂).Realize v ↔
      AdjCore t₁ (fun j => v (0, j)) t₂ (fun j => v (1, j)) := by
  cases t₁ <;> cases t₂ <;>
    first
      | exact realize_compatF
      | simp [adjF, AdjCore]

theorem realize_markedF {t : SatCliqueTag} {v : Fin 1 × Fin 2 → A} :
    (markedF t).Realize v ↔ MarkedCore t (fun j => v (0, j)) := by
  cases t <;> simp [markedF, MarkedCore]

/-- Characterization of the interpreted adjacency relation. -/
theorem satToClique_adj (t₁ t₂ : SatCliqueTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := satToClique.Map A) mgAdj ![(t₁, w₁), (t₂, w₂)] ↔
      AdjCore t₁ w₁ t₂ w₂ := by
  rw [FOInterpretation.relMap_map]
  simp only [satToClique]
  rw [realize_adjF]
  simp

/-- Characterization of the interpreted mark relation. -/
theorem satToClique_marked (t : SatCliqueTag) (w : Fin 2 → A) :
    RelMap (M := satToClique.Map A) mgMarked ![(t, w)] ↔ MarkedCore t w := by
  rw [FOInterpretation.relMap_map]
  simp only [satToClique]
  rw [realize_markedF]
  simp

private theorem mgAdj_iff (v v' : satToClique.Map A) :
    MGAdj v v' ↔ AdjCore v.1 v.2 v'.1 v'.2 := by
  obtain ⟨t₁, w₁⟩ := v
  obtain ⟨t₂, w₂⟩ := v'
  exact satToClique_adj t₁ t₂ w₁ w₂

end Characterization

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- When no clause is empty, the marked vertices are exactly the diagonal
clause vertices, one per clause. -/
private def markedEquivClause (hne : ¬∃ c : A, EmptyCl c) :
    {v : satToClique.Map A // MGMarked v} ≃ {c : A // IsCl c} where
  toFun v := ⟨v.1.2 0, by
    obtain ⟨⟨t, w⟩, hm⟩ := v
    have hm' := (satToClique_marked t w).mp hm
    cases t with
    | pos => exact absurd hm' hne
    | neg => exact absurd hm' hne
    | cl => exact (hm'.resolve_right hne).2⟩
  invFun c := ⟨(SatCliqueTag.cl, ![c.1, c.1]),
    (satToClique_marked _ _).mpr (Or.inl ⟨rfl, c.2⟩)⟩
  left_inv := by
    rintro ⟨⟨t, w⟩, hm⟩
    have hm' := (satToClique_marked t w).mp hm
    cases t with
    | pos => exact absurd hm' hne
    | neg => exact absurd hm' hne
    | cl =>
      obtain ⟨hdiag, -⟩ := hm'.resolve_right hne
      refine Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩)
      fin_cases j
      · rfl
      · exact hdiag
  right_inv c := Subtype.ext rfl

variable (A) in
/-- Correctness of the reduction: a finite ordered CNF structure is
satisfiable iff its interpreted marked graph has a clique at least as large
as the marked set. -/
theorem satisfiable_iff_hasLargeClique [Finite A] [Nonempty A] :
    Satisfiable A ↔ HasLargeClique (satToClique.Map A) := by
  classical
  have hfin : Finite (satToClique.Map A) := satToClique.map_finite A
  unfold HasLargeClique
  rw [and_iff_right hfin, cliqueOn_iff_embedding]
  by_cases hne : ∃ c : A, EmptyCl c
  · -- Some clause is empty: the CNF is unsatisfiable, every vertex is
    -- marked, and no clique can be as large as the whole (≥ 2-element)
    -- universe since clause vertices are isolated.
    constructor
    · rintro ⟨ν, hν⟩
      obtain ⟨c, hc, hnocc⟩ := hne
      obtain ⟨x, ⟨hp, -⟩ | ⟨hn, -⟩⟩ := hν c hc
      · exact (hnocc x true ⟨hc, hp⟩).elim
      · exact (hnocc x false ⟨hc, hn⟩).elim
    · rintro ⟨S, hS, ⟨e⟩⟩
      have hmark : ∀ v : satToClique.Map A, MGMarked v := by
        rintro ⟨t, w⟩
        refine (satToClique_marked t w).mpr ?_
        cases t
        exacts [hne, hne, Or.inr hne]
      have emb : satToClique.Map A ↪ {v // S v} :=
        ⟨fun v => e ⟨v, hmark v⟩,
          fun v v' h => congrArg Subtype.val (e.injective h)⟩
      haveI := Fintype.ofFinite (satToClique.Map A)
      have hall : ∀ v, S v := by
        by_contra h
        push Not at h
        obtain ⟨v₀, hv₀⟩ := h
        exact absurd (Fintype.card_le_of_embedding emb)
          (not_le.mpr (Fintype.card_subtype_lt hv₀))
      obtain ⟨a₀⟩ := ‹Nonempty A›
      have hadj := hS (SatCliqueTag.cl, fun _ => a₀) (SatCliqueTag.pos, fun _ => a₀)
        (hall _) (hall _) (by
          intro h
          exact SatCliqueTag.noConfusion
            (show SatCliqueTag.cl = SatCliqueTag.pos from
              congrArg (fun v : satToClique.Map A => v.1) h))
      exact ((satToClique_adj SatCliqueTag.cl SatCliqueTag.pos
        (fun _ => a₀) (fun _ => a₀)).mp hadj : False).elim
  · -- No clause is empty: the marked set is one diagonal vertex per clause.
    constructor
    · -- From a satisfying assignment, pick one true literal per clause.
      rintro ⟨ν, hν⟩
      have hpick' : ∀ c : A, ∃ x s, IsCl c → OccIn c x s ∧ LitTrue ν x s := by
        intro c
        by_cases hc : IsCl c
        · obtain ⟨x, s, h1, h2⟩ := satClauses_occ hν c hc
          exact ⟨x, s, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨Classical.arbitrary A, true, fun h => absurd h hc⟩
      choose xw sg hpick using hpick'
      refine ⟨fun v => IsCl (v.2 0) ∧ v.1 = .ofSign (sg (v.2 0)) ∧ v.2 1 = xw (v.2 0),
        ?_, ⟨?_⟩⟩
      · rintro ⟨t, w⟩ ⟨t', w'⟩ hm hm' hvv'
        obtain ⟨hc, ht, hx⟩ :
            IsCl (w 0) ∧ t = .ofSign (sg (w 0)) ∧ w 1 = xw (w 0) := hm
        obtain ⟨hc', ht', hx'⟩ :
            IsCl (w' 0) ∧ t' = .ofSign (sg (w' 0)) ∧ w' 1 = xw (w' 0) := hm'
        have hcc' : w 0 ≠ w' 0 := by
          rintro heq
          have h1 : t = t' := by rw [ht, ht', heq]
          have h2 : w = w' := by
            funext j
            fin_cases j
            · exact heq
            · change w 1 = w' 1
              rw [hx, hx', heq]
          exact hvv' (by rw [h1, h2])
        refine (satToClique_adj t t' w w').mpr ?_
        rw [ht, ht', adjCore_ofSign]
        refine ⟨?_, ?_, hcc', ?_⟩
        · rw [hx]
          exact (hpick (w 0) hc).1
        · rw [hx']
          exact (hpick (w' 0) hc').1
        · by_cases hs : sg (w 0) = sg (w' 0)
          · exact Or.inl hs
          · refine Or.inr fun hxx => ?_
            have h1 := (hpick (w 0) hc).2
            have h2 := (hpick (w' 0) hc').2
            rw [← hx] at h1
            rw [← hx', ← hxx, hx] at h2
            have hs' : sg (w' 0) = !sg (w 0) := by
              cases hb : sg (w 0) <;> cases hb' : sg (w' 0) <;> simp_all
            rw [hs', ← hx, litTrue_not] at h2
            exact h2 h1
      · refine (markedEquivClause hne).toEmbedding.trans
          ⟨fun c => ⟨(SatCliqueTag.ofSign (sg c.1), ![c.1, xw c.1]), c.2, rfl, rfl⟩,
            fun c c' h => ?_⟩
        exact Subtype.ext (show c.1 = c'.1 from
          congrArg (fun v : satToClique.Map A => v.2 0) (congrArg Subtype.val h))
    · -- From a large clique, read off a satisfying assignment.
      rintro ⟨S, hS, ⟨e⟩⟩
      by_cases hjunk : ∃ v, S v ∧ ¬Genuine v.1 v.2
      · -- A non-genuine clique member forces the clique to be a singleton,
        -- so there is at most one clause; satisfy its first literal.
        obtain ⟨v₀, hv₀S, hv₀⟩ := hjunk
        have honly : ∀ v, S v → v = v₀ := by
          intro v hv
          by_contra hvne
          exact hv₀ ((mgAdj_iff v v₀).mp (hS v v₀ hv hv₀S hvne)).genuine_right
        have huniq : ∀ c c' : A, IsCl c → IsCl c' → c = c' := by
          intro c c' hc hc'
          have hm : ∀ d : A, IsCl d →
              MGMarked (A := satToClique.Map A) (SatCliqueTag.cl, ![d, d]) :=
            fun d hd => (satToClique_marked _ _).mpr (Or.inl ⟨rfl, hd⟩)
          have he : e ⟨_, hm c hc⟩ = e ⟨_, hm c' hc'⟩ :=
            Subtype.ext ((honly _ (e ⟨_, hm c hc⟩).2).trans
              (honly _ (e ⟨_, hm c' hc'⟩).2).symm)
          exact congrFun (congrArg (fun v : satToClique.Map A => v.2)
            (congrArg Subtype.val (e.injective he))) 0
        by_cases hcl : ∃ c : A, IsCl c
        · obtain ⟨c₀, hc₀⟩ := hcl
          have hnc₀ : ¬(IsCl c₀ ∧ ∀ x s, ¬OccIn c₀ x s) := fun h => hne ⟨c₀, h⟩
          push Not at hnc₀
          obtain ⟨x₀, s₀, hocc₀⟩ := hnc₀ hc₀
          refine ⟨fun x => s₀ = true ∧ x = x₀, fun c hc => ⟨x₀, ?_⟩⟩
          obtain rfl : c = c₀ := huniq c c₀ hc hc₀
          cases s₀ with
          | true => exact Or.inl ⟨hocc₀.2, rfl, rfl⟩
          | false => exact Or.inr ⟨hocc₀.2, fun h => by simp at h⟩
        · exact ⟨fun _ => True, fun c hc => absurd ⟨c, hc⟩ hcl⟩
      · -- Every clique member is a genuine occurrence; distinct members lie
        -- in distinct clauses, so by counting the clique covers every
        -- clause, and its literals form a consistent assignment.
        push Not at hjunk
        haveI := Fintype.ofFinite A
        haveI := Fintype.ofFinite (satToClique.Map A)
        have hφinj : Function.Injective (fun v : {v // S v} =>
            (⟨v.1.2 0, (hjunk v.1 v.2).isCl⟩ : {c : A // IsCl c})) := by
          rintro ⟨v, hv⟩ ⟨v', hv'⟩ h
          have hcc' : v.2 0 = v'.2 0 := congrArg Subtype.val h
          by_contra hne'
          have hvv' : v ≠ v' := fun h' => hne' (Subtype.ext h')
          exact ((mgAdj_iff v v').mp (hS v v' hv hv' hvv')).ne_clause hcc'
        have hcard : Fintype.card {c : A // IsCl c} = Fintype.card {v // S v} :=
          le_antisymm
            (Fintype.card_le_of_embedding
              ((markedEquivClause hne).symm.toEmbedding.trans e))
            (Fintype.card_le_of_injective _ hφinj)
        have hφsurj := ((Fintype.bijective_iff_injective_and_card _).mpr
          ⟨hφinj, hcard.symm⟩).2
        refine ⟨fun x => ∃ v : satToClique.Map A,
          S v ∧ v.1 = SatCliqueTag.pos ∧ v.2 1 = x, fun c hc => ?_⟩
        obtain ⟨⟨v, hvS⟩, hφv⟩ := hφsurj ⟨c, hc⟩
        obtain ⟨t, w⟩ := v
        have hvc : w 0 = c := congrArg Subtype.val hφv
        have hgen := hjunk (t, w) hvS
        refine ⟨w 1, ?_⟩
        cases t with
        | pos =>
          have hocc : OccIn (w 0) (w 1) true := hgen
          refine Or.inl ⟨?_, (SatCliqueTag.pos, w), hvS, rfl, rfl⟩
          rw [← hvc]
          exact hocc.2
        | neg =>
          have hocc : OccIn (w 0) (w 1) false := hgen
          refine Or.inr ⟨?_, ?_⟩
          · rw [← hvc]
            exact hocc.2
          · rintro ⟨v', hv'S, hv't, hv'x⟩
            obtain ⟨t', w'⟩ := v'
            obtain rfl : t' = SatCliqueTag.pos := hv't
            have hx : w' 1 = w 1 := hv'x
            have hvv' : ((SatCliqueTag.neg, w) : satToClique.Map A) ≠
                (SatCliqueTag.pos, w') := by
              intro h
              exact SatCliqueTag.noConfusion
                (show SatCliqueTag.neg = SatCliqueTag.pos from
                  congrArg (fun v : satToClique.Map A => v.1) h)
            have hadj : AdjCore SatCliqueTag.neg w SatCliqueTag.pos w' :=
              (satToClique_adj _ _ _ _).mp (hS _ _ hvS hv'S hvv')
            exact (hadj.2.2.2.resolve_left (by simp)) hx.symm
        | cl => exact ((hgen : False)).elim

end Correctness

end SatToClique

open SatToClique in
/-- **SAT FO-reduces to Clique on ordered structures**: the
one-vertex-per-literal-occurrence interpretation `SatToClique.satToClique`,
over the ordered expansion of the language of CNF instances, maps a finite
CNF structure to a yes-instance of Clique iff it is satisfiable. (The order
is never mentioned by the formulas; the ordered packaging only serves to
restrict correctness to finite structures, as required by the finiteness
conjunct of `DescriptiveComplexity.Clique`.) -/
noncomputable def sat_ordered_fo_reduction_clique : SAT ≤ᶠᵒ[≤] Clique where
  Tag := SatCliqueTag
  dim := 2
  toInterpretation := satToClique
  correct A _ _ _ _ := satisfiable_iff_hasLargeClique A

end DescriptiveComplexity
