/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SatUnsat
import DescriptiveComplexity.Problems.Sat.Hardness

/-!
# DP-hardness of SAT-UNSAT

The hardness half of the completeness of SAT-UNSAT
([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]): every
DP-definable problem admits an ordered first-order reduction to SAT-UNSAT
(`DescriptiveComplexity.satUnsat_hard_of_dpDefinable`), which with the membership half
`DescriptiveComplexity.satUnsat_mem_DP` makes it DP-complete
(`DescriptiveComplexity.SATUNSAT_DP_complete`).

A DP definition of `Q` is a `Σ₁`-definable `S` and a `Π₁`-definable `T` with
`Q ≡ S ⊓ T`. Complementing the second half, `Tᶜ` is `Σ₁`-definable, so the
Cook–Levin discharge `DescriptiveComplexity.sat_hard_of_sigmaSODefinable` applies to
*both* `S` and `Tᶜ` and yields two ordered reductions to SAT. Running them
side by side into one paired-CNF instance is what this file does: `Q` holds
iff the first CNF instance is satisfiable and the second is not, which is
exactly SAT-UNSAT of the pair.

## Pairing two interpretations

`DescriptiveComplexity.pairInterp` puts two interpretations into `Language.sat` together
into one interpretation into `Language.satPair`: tags `T₁ ⊕ T₂`, dimension
`max d₁ d₂`, and each of the six relations defined by its own side's formula on
its own tags – and by `⊥` as soon as one argument's tag belongs to the other
side, so that the two formulas never see each other's points.

The two sides now share a universe of tuples longer than either originally
used, and the extra coordinates must *not* be left free: a clause and its
variables would acquire `|A|^(dim−dᵢ)` copies each, every clause copy
containing every copy of each of its variables, and the blow-up of an
unsatisfiable instance can be satisfiable (`{x}, {¬x}` becomes
`(x₁ ∨ … ∨ xₖ) ∧ (¬x₁ ∨ … ∨ ¬xₖ)`). So each side's formulas are conjoined with
`DescriptiveComplexity.canonF`, pinning the spare coordinates to a minimum of the
order: the points of a side are then in bijection with the points of its own
interpretation (`DescriptiveComplexity.sidePt`), and everything else in the paired
universe is junk – neither a clause nor an occurrence, hence harmless by
`DescriptiveComplexity.satisfiable_iff_of_cover`.

Both sides are handled once, by a section generic in the tag injection
`inj : T → Tg` and its partial inverse `get : Tg → Option T`, instantiated at
`Sum.inl`/`Sum.getLeft?` and `Sum.inr`/`Sum.getRight?`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Satisfiability of one side, along a covering embedding

The `Language.satPair` counterpart of `DescriptiveComplexity.satisfiable_iff_of_cover`:
one side of a paired instance is satisfiable exactly when a plain CNF
structure covering its clauses and occurrences is. -/

section Cover

variable {A B : Type} [Language.satPair.Structure A] [Language.sat.Structure B]

/-- **Satisfiability of a side transfers along a clause-covering embedding**:
the elements of the paired instance outside the image of `j` are neither
clauses nor occurrences of that side, so they constrain nothing. -/
theorem satWith_iff_of_cover (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) (j : B → A) (hj : Function.Injective j)
    (hcl : ∀ b : B, RelMap isCl ![j b] ↔ RelMap satIsClause ![b])
    (hpos : ∀ b b' : B, RelMap pos ![j b, j b'] ↔ RelMap satPosIn ![b, b'])
    (hneg : ∀ b b' : B, RelMap neg ![j b, j b'] ↔ RelMap satNegIn ![b, b'])
    (hclImg : ∀ c : A, RelMap isCl ![c] → ∃ b : B, c = j b)
    (hoccImg : ∀ (b : B) (x : A),
      RelMap pos ![j b, x] ∨ RelMap neg ![j b, x] → ∃ b' : B, x = j b') :
    SatWith A isCl pos neg ↔ Satisfiable B := by
  rw [← satisfiable_sideInterp isCl pos neg]
  have hone : ∀ w : Fin 1 → A, (fun _ : Fin 1 => w 0) = w :=
    fun w => funext fun i => congrArg w (Subsingleton.elim 0 i)
  refine satisfiable_iff_of_cover (fun b => ((), fun _ => j b)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro b b' hb
    exact hj (congrFun (congrArg (fun p : (sideInterp isCl pos neg).Map A => p.2) hb) 0)
  · intro b
    exact (sideInterp_isClause isCl pos neg _).trans (hcl b)
  · intro b b'
    exact (sideInterp_posIn isCl pos neg _ _).trans (hpos b b')
  · intro b b'
    exact (sideInterp_negIn isCl pos neg _ _).trans (hneg b b')
  · rintro ⟨⟨⟩, w⟩ hc
    obtain ⟨b, hb⟩ := hclImg (w 0) ((sideInterp_isClause isCl pos neg w).mp hc)
    exact ⟨b, Prod.ext_iff.mpr
      ⟨rfl, (hone w).symm.trans (congrArg (fun (x : A) (_ : Fin 1) => x) hb)⟩⟩
  · rintro b ⟨⟨⟩, w⟩ hx
    have hx' : RelMap pos ![j b, w 0] ∨ RelMap neg ![j b, w 0] := by
      rcases hx with h | h
      · exact Or.inl ((sideInterp_posIn isCl pos neg _ w).mp h)
      · exact Or.inr ((sideInterp_negIn isCl pos neg _ w).mp h)
    obtain ⟨b', hb'⟩ := hoccImg b (w 0) hx'
    exact ⟨b', Prod.ext_iff.mpr
      ⟨rfl, (hone w).symm.trans (congrArg (fun (x : A) (_ : Fin 1) => x) hb')⟩⟩

end Cover

/-! ### One side of the paired instance

The defining formulas of one side, and the characterization of the relations
they interpret. Everything here is generic in the tag injection `inj` and its
partial inverse `get`, so that it serves both sides of the pair. -/

section Side

variable {L : Language.{0, 0}} {T Tg : Type} {dm d : ℕ}

/-- The defining formula of one side's relation `R` at a tuple `t` of tags:
this side's own formula, its coordinates re-read among the `d` available ones
and its argument tuples pinned to canonically padded ones – and `⊥` unless
every argument's tag belongs to this side. -/
noncomputable def sideFml (I : FOInterpretation (L.sum Language.order) Language.sat T dm)
    (hd : dm ≤ d) (get : Tg → Option T) {n : ℕ} (R : Language.sat.Relations n)
    (t : Fin n → Tg) : (L.sum Language.order).Formula (Fin n × Fin d) :=
  if h : ∀ i, (get (t i)).isSome then
    (I.relFormula R fun i => (get (t i)).get (h i)).relabel
        (fun p => (p.1, Fin.castLE hd p.2)) ⊓
      listInf ((List.finRange n).map fun i => canonF (L := L) dm fun j => (i, j))
  else ⊥

/-- A tag of the other side makes a side's defining formula `⊥`. -/
theorem sideFml_eq_bot (I : FOInterpretation (L.sum Language.order) Language.sat T dm)
    (hd : dm ≤ d) (get : Tg → Option T) {n : ℕ} (R : Language.sat.Relations n)
    (t : Fin n → Tg) (h : ¬∀ i, (get (t i)).isSome) : sideFml I hd get R t = ⊥ :=
  dif_neg h

/-- Realization of a side's defining formula at tags that all belong to it:
this side's own formula holds of the prefixes, and every argument tuple is
canonically padded. -/
theorem realize_sideFml (I : FOInterpretation (L.sum Language.order) Language.sat T dm)
    (hd : dm ≤ d) (get : Tg → Option T) {n : ℕ} (R : Language.sat.Relations n)
    (t : Fin n → Tg) (t' : Fin n → T) (ht : ∀ i, get (t i) = some (t' i))
    {A : Type} [L.Structure A] [LinearOrder A] (v : Fin n × Fin d → A) :
    (sideFml I hd get R t).Realize v ↔
      (I.relFormula R t').Realize (fun p => v (p.1, Fin.castLE hd p.2)) ∧
        ∀ i, Canon dm fun j => v (i, j) := by
  have hsome : ∀ i, (get (t i)).isSome := fun i => by rw [ht i]; rfl
  have hgt : (fun i => (get (t i)).get (hsome i)) = t' :=
    funext fun i => Option.some_injective _ ((Option.some_get (hsome i)).trans (ht i))
  rw [sideFml, dif_pos hsome, hgt, Formula.realize_inf, Formula.realize_relabel,
    realize_listInf]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h ψ hψ => ?_⟩
  · exact realize_canonF.mp (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact realize_canonF.mpr (h i)

end Side

/-! ### The points of one side

A tuple congruence for relations, then the injection of one side's own
interpretation into the paired universe and the characterization of the
interpreted relations along it. -/

private theorem relMap_congr_args {L' : Language.{0, 0}} {M : Type} [L'.Structure M] {n : ℕ}
    (R : L'.Relations n) {xs ys : Fin n → M} (h : xs = ys) : RelMap R xs ↔ RelMap R ys :=
  iff_of_eq (congrArg _ h)

section SideChar

variable {L : Language.{0, 0}} {T Tg : Type} {dm d : ℕ}
  {A : Type} [L.Structure A] [LinearOrder A]

/-- The point of the paired universe holding a point of one side's own
interpretation: its tag injected, its tuple canonically padded. -/
def sidePt (I : FOInterpretation (L.sum Language.order) Language.sat T dm)
    (inj : T → Tg) (J : FOInterpretation (L.sum Language.order) Language.satPair Tg d)
    (a₀ : A) (b : I.Map A) : J.Map A :=
  (inj b.1, pad a₀ b.2)

variable (I : FOInterpretation (L.sum Language.order) Language.sat T dm) (hd : dm ≤ d)
  (inj : T → Tg) (get : Tg → Option T)
  (J : FOInterpretation (L.sum Language.order) Language.satPair Tg d)
  (sym : ∀ n : ℕ, Language.sat.Relations n → Language.satPair.Relations n)

/-- **What a side's relations say**: at tags that all belong to the side, its
own relation of the prefixes, plus canonicity of every argument tuple. -/
theorem relMap_side
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R)
    {n : ℕ} (R : Language.sat.Relations n) (xs : Fin n → J.Map A) (t : Fin n → T)
    (ht : ∀ i, get (xs i).1 = some (t i)) :
    RelMap (M := J.Map A) (sym n R) xs ↔
      RelMap (M := I.Map A) R (fun i => (t i, pref hd (xs i).2)) ∧
        ∀ i, Canon dm (xs i).2 := by
  rw [FOInterpretation.relMap_map, hJ n R, realize_sideFml I hd get R _ t ht]
  exact and_congr (I.relMap_map A R fun i => (t i, pref hd (xs i).2)).symm Iff.rfl

/-- A side's relations only hold of tags belonging to it. -/
theorem isSome_of_relMap_side
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R)
    {n : ℕ} (R : Language.sat.Relations n) (xs : Fin n → J.Map A)
    (h : RelMap (M := J.Map A) (sym n R) xs) (i : Fin n) : (get (xs i).1).isSome := by
  by_contra hi
  rw [FOInterpretation.relMap_map, hJ n R,
    sideFml_eq_bot I hd get R _ fun hall => hi (hall i), Formula.realize_bot] at h
  exact h

/-- The tags of a tuple satisfying a side's relation, as a function. -/
theorem exists_tags_of_relMap_side
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R)
    {n : ℕ} (R : Language.sat.Relations n) (xs : Fin n → J.Map A)
    (h : RelMap (M := J.Map A) (sym n R) xs) :
    ∃ t : Fin n → T, ∀ i, get (xs i).1 = some (t i) :=
  ⟨fun i => (get (xs i).1).get (isSome_of_relMap_side I hd get J sym hJ R xs h i),
    fun i => (Option.some_get (isSome_of_relMap_side I hd get J sym hJ R xs h i)).symm⟩

/-- **A side's relations, read on its own points**: on the image of
`DescriptiveComplexity.sidePt`, the paired instance's side is a faithful copy of the
interpretation it came from. -/
theorem relMap_side_pad (hget : ∀ t, get (inj t) = some t)
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R)
    {a₀ : A} (ha₀ : IsBot a₀) {n : ℕ} (R : Language.sat.Relations n)
    (bs : Fin n → I.Map A) :
    RelMap (M := J.Map A) (sym n R) (fun i => sidePt I inj J a₀ (bs i)) ↔
      RelMap (M := I.Map A) R bs := by
  rw [relMap_side I hd get J sym hJ R _ (fun i => (bs i).1) fun i => hget (bs i).1]
  have he : (fun i => (((bs i).1, pref hd (sidePt I inj J a₀ (bs i)).2) : I.Map A)) = bs := by
    funext i
    change (((bs i).1, pref hd (pad a₀ (bs i).2)) : I.Map A) = bs i
    rw [pref_pad]
    rfl
  have h1 := relMap_congr_args (M := I.Map A) R he
  exact ⟨fun h => h1.mp h.1, fun h => ⟨h1.mpr h, fun i => canon_pad ha₀ _ _⟩⟩

/-- Every point a side's relations mention is one of its own points. -/
theorem exists_sidePt_of_relMap_side (hgetinv : ∀ (tg : Tg) (t : T), get tg = some t → tg = inj t)
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R)
    {a₀ : A} (ha₀ : IsBot a₀) {n : ℕ} (R : Language.sat.Relations n) (xs : Fin n → J.Map A)
    (h : RelMap (M := J.Map A) (sym n R) xs) (i : Fin n) :
    ∃ b : I.Map A, xs i = sidePt I inj J a₀ b := by
  obtain ⟨t, ht⟩ := exists_tags_of_relMap_side I hd get J sym hJ R xs h
  obtain ⟨-, hcanon⟩ := (relMap_side I hd get J sym hJ R xs t ht).mp h
  exact ⟨(t i, pref hd (xs i).2),
    Prod.ext_iff.mpr ⟨hgetinv _ _ (ht i), (pad_pref_of_canon ha₀ hd (hcanon i)).symm⟩⟩

/-- **One side of a paired instance is satisfiable exactly when the
interpretation it came from is.** The junk of the paired universe – points of
the other side, and tuples that are not canonically padded – is neither a
clause nor an occurrence of this side, so it constrains no assignment. -/
theorem satWith_side [Finite A] [Nonempty A] (hget : ∀ t, get (inj t) = some t)
    (hgetinv : ∀ (tg : Tg) (t : T), get tg = some t → tg = inj t)
    (hJ : ∀ (n : ℕ) (R : Language.sat.Relations n),
      J.relFormula (sym n R) = sideFml I hd get R) :
    SatWith (J.Map A) (sym 1 .isClause) (sym 2 .posIn) (sym 2 .negIn) ↔
      Satisfiable (I.Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have hpad₁ : ∀ (R : Language.sat.Relations 1) (b : I.Map A),
      RelMap (M := J.Map A) (sym 1 R) ![sidePt I inj J a₀ b] ↔
        RelMap (M := I.Map A) R ![b] := by
    intro R b
    refine Iff.trans (relMap_congr_args (M := J.Map A) (sym 1 R) ?_)
      (relMap_side_pad I hd inj get J sym hget hJ ha₀ R ![b])
    funext i
    rw [Matrix.cons_val_fin_one, Matrix.cons_val_fin_one]
  have hpad₂ : ∀ (R : Language.sat.Relations 2) (b b' : I.Map A),
      RelMap (M := J.Map A) (sym 2 R) ![sidePt I inj J a₀ b, sidePt I inj J a₀ b'] ↔
        RelMap (M := I.Map A) R ![b, b'] := by
    intro R b b'
    refine Iff.trans (relMap_congr_args (M := J.Map A) (sym 2 R) ?_)
      (relMap_side_pad I hd inj get J sym hget hJ ha₀ R ![b, b'])
    funext i
    fin_cases i <;> rfl
  refine satWith_iff_of_cover _ _ _ (sidePt I inj J a₀) ?_ (hpad₁ .isClause)
    (hpad₂ .posIn) (hpad₂ .negIn) ?_ ?_
  · intro b b' hb
    have h1 : inj b.1 = inj b'.1 := congrArg (fun p : J.Map A => p.1) hb
    have h2 : pad (D := d) a₀ b.2 = pad a₀ b'.2 := congrArg (fun p : J.Map A => p.2) hb
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · exact Option.some_injective _
        ((hget b.1).symm.trans ((congrArg get h1).trans (hget b'.1)))
    · have h3 := congrArg (pref (D := d) hd) h2
      rwa [pref_pad, pref_pad] at h3
  · intro c hc
    exact exists_sidePt_of_relMap_side I hd inj get J sym hgetinv hJ ha₀ .isClause ![c] hc 0
  · rintro b x (h | h)
    · exact exists_sidePt_of_relMap_side I hd inj get J sym hgetinv hJ ha₀ .posIn
        ![sidePt I inj J a₀ b, x] h 1
    · exact exists_sidePt_of_relMap_side I hd inj get J sym hgetinv hJ ha₀ .negIn
        ![sidePt I inj J a₀ b, x] h 1

end SideChar

/-! ### Pairing two interpretations into one -/

section Pairing

variable {L : Language.{0, 0}} {T₁ T₂ : Type} {d₁ d₂ : ℕ}
  (I₁ : FOInterpretation (L.sum Language.order) Language.sat T₁ d₁)
  (I₂ : FOInterpretation (L.sum Language.order) Language.sat T₂ d₂)

/-- The symbols of the first side of a paired CNF vocabulary. -/
def satPairL : ∀ n : ℕ, Language.sat.Relations n → Language.satPair.Relations n
  | _, .isClause => spIsCl₁
  | _, .posIn => spPos₁
  | _, .negIn => spNeg₁

/-- The symbols of the second side of a paired CNF vocabulary. -/
def satPairR : ∀ n : ℕ, Language.sat.Relations n → Language.satPair.Relations n
  | _, .isClause => spIsCl₂
  | _, .posIn => spPos₂
  | _, .negIn => spNeg₂

/-- **Two CNF interpretations, paired into one.** The tags of the two sides
are kept apart in a sum, the dimension is the larger of the two, and each of
the six relations is defined by its own side's formula on its own tags, at
canonically padded tuples – and by `⊥` as soon as an argument belongs to the
other side. -/
noncomputable def pairInterp :
    FOInterpretation (L.sum Language.order) Language.satPair (T₁ ⊕ T₂) (max d₁ d₂) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause₁ => sideFml I₁ (le_max_left d₁ d₂) Sum.getLeft? .isClause
    | _, .posIn₁ => sideFml I₁ (le_max_left d₁ d₂) Sum.getLeft? .posIn
    | _, .negIn₁ => sideFml I₁ (le_max_left d₁ d₂) Sum.getLeft? .negIn
    | _, .isClause₂ => sideFml I₂ (le_max_right d₁ d₂) Sum.getRight? .isClause
    | _, .posIn₂ => sideFml I₂ (le_max_right d₁ d₂) Sum.getRight? .posIn
    | _, .negIn₂ => sideFml I₂ (le_max_right d₁ d₂) Sum.getRight? .negIn

/-- The paired interpretation defines the first side's symbols by the first
interpretation's formulas. -/
theorem pairInterp_relFormula_left (n : ℕ) (R : Language.sat.Relations n) :
    (pairInterp I₁ I₂).relFormula (satPairL n R) =
      sideFml I₁ (le_max_left d₁ d₂) Sum.getLeft? R := by
  cases R <;> rfl

/-- The paired interpretation defines the second side's symbols by the second
interpretation's formulas. -/
theorem pairInterp_relFormula_right (n : ℕ) (R : Language.sat.Relations n) :
    (pairInterp I₁ I₂).relFormula (satPairR n R) =
      sideFml I₂ (le_max_right d₁ d₂) Sum.getRight? R := by
  cases R <;> rfl

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- **The first side of the paired instance is satisfiable exactly when the
first interpretation is.** -/
theorem satWith_pairInterp_left [Finite A] [Nonempty A] :
    SatWith ((pairInterp I₁ I₂).Map A) spIsCl₁ spPos₁ spNeg₁ ↔ Satisfiable (I₁.Map A) :=
  satWith_side I₁ (le_max_left d₁ d₂) Sum.inl Sum.getLeft? (pairInterp I₁ I₂) satPairL
    (fun _ => rfl) (fun tg t h => by cases tg <;> simp_all)
    (pairInterp_relFormula_left I₁ I₂)

/-- **The second side of the paired instance is satisfiable exactly when the
second interpretation is.** -/
theorem satWith_pairInterp_right [Finite A] [Nonempty A] :
    SatWith ((pairInterp I₁ I₂).Map A) spIsCl₂ spPos₂ spNeg₂ ↔ Satisfiable (I₂.Map A) :=
  satWith_side I₂ (le_max_right d₁ d₂) Sum.inr Sum.getRight? (pairInterp I₁ I₂) satPairR
    (fun _ => rfl) (fun tg t h => by cases tg <;> simp_all)
    (pairInterp_relFormula_right I₁ I₂)

end Pairing

/-! ### The reduction -/

/-- **Two reductions to SAT, paired into one reduction to SAT-UNSAT.** Given a
problem `Q` that is the conjunction of `S` and `T`, a reduction of `S` to SAT
and one of `Tᶜ` to SAT, the paired interpretation sends `A` to the pair of
their images: its first CNF instance is satisfiable iff `S` holds, and its
second is *un*satisfiable iff `T` does. -/
noncomputable def pairReduction {L : Language.{0, 0}} {S T Q : DecisionProblem L}
    (f₁ : S ≤ᶠᵒ[≤] SAT) (f₂ : Tᶜ ≤ᶠᵒ[≤] SAT)
    (hQ : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], Q A ↔ (S A ∧ T A)) :
    Q ≤ᶠᵒ[≤] SATUNSAT :=
  letI := f₁.tagFinite
  letI := f₂.tagFinite
  letI := f₁.tagNonempty
  letI := f₂.tagNonempty
  { Tag := f₁.Tag ⊕ f₂.Tag
    dim := max f₁.dim f₂.dim
    toInterpretation := pairInterp f₁.toInterpretation f₂.toInterpretation
    correct := fun A _ _ _ _ =>
      (hQ A).trans (and_congr
        ((f₁.correct A).trans (satWith_pairInterp_left _ _).symm)
        ((not_not.symm.trans (not_congr (f₂.correct A))).trans
          (not_congr (satWith_pairInterp_right _ _).symm))) }

/-! ### DP-completeness of SAT-UNSAT -/

/-- **The hardness half**: every DP-definable problem admits an ordered
first-order reduction to SAT-UNSAT. The `Σ₁` half and the complement of the
`Π₁` half are both discharged by Cook–Levin
(`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`), and the two CNF instances so
produced are paired into one. -/
theorem satUnsat_hard_of_dpDefinable {L : Language.{0, 0}} (Q : DecisionProblem L)
    (h : DPDefinable Q) : Nonempty (Q ≤ᶠᵒ[≤] SATUNSAT) := by
  obtain ⟨S, T, hS, hT, hST⟩ := h
  obtain ⟨f₁⟩ := sat_hard_of_sigmaSODefinable S hS
  obtain ⟨f₂⟩ := sat_hard_of_sigmaSODefinable Tᶜ ((piSODefinable_iff_compl 1 T).mp hT)
  exact ⟨pairReduction f₁ f₂ hST⟩

/-- **SAT-UNSAT is DP-hard.** -/
theorem satUnsat_DP_hard : DP.Hard SATUNSAT :=
  (hard_DP_iff SATUNSAT).mpr fun Q hQ =>
    (satUnsat_hard_of_dpDefinable Q hQ).map OrderedFOReduction.toRel

/-- **SAT-UNSAT is DP-complete** ([Papadimitriou & Yannakakis
1984][papadimitriou1984complexity]): membership is
`DescriptiveComplexity.satUnsat_mem_DP`, the shape of the problem itself; hardness is
`DescriptiveComplexity.satUnsat_hard_of_dpDefinable`, the two Cook–Levin discharges run
side by side into one paired instance. -/
theorem SATUNSAT_DP_complete : DP.Complete SATUNSAT :=
  ⟨satUnsat_mem_DP, satUnsat_DP_hard⟩

end DescriptiveComplexity
