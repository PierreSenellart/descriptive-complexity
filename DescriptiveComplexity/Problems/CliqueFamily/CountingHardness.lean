/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.Counting
import DescriptiveComplexity.Problems.CliqueFamily.FromSat
import DescriptiveComplexity.Problems.OneInSat.CountingFromSat
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Clique is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpClique_sharpP_parsimoniousComplete`, by a reduction from
#1-in-SAT (`DescriptiveComplexity.sharpOneInSat_ordered_parsimonious_sharpClique`).

The reduction of `DescriptiveComplexity.Problems.CliqueFamily.FromSat` is not
parsimonious: a clique picks one true literal in each clause, and a satisfying
assignment usually offers several. Under *exactly-one* satisfaction the choice
is forced, provided a vertex says all that choosing it entails. So an
occurrence vertex `(c, x, s)` here stands for “`(x, s)` is the true literal of
`c`, and every other literal of `c` is false”, which fixes the value of every
variable of `c` (`DescriptiveComplexity.OneInToClique.ForceAt`), and two occurrence
vertices of distinct clauses are adjacent when the values they fix agree
(`DescriptiveComplexity.OneInToClique.Clash`). A vertex whose own demands are
contradictory – its clause holds another variable with both signs – is adjacent
to nothing.

A singleton is a clique whatever the graph, so the threshold is kept away from
`1`: each clause `c` also has a *clause vertex* `(cl, (c, c))`, adjacent to
every other clause vertex and to every consistent occurrence vertex, and the
marked set has two elements per clause. A clique of that size holds every
clause vertex and one occurrence vertex per clause
(`DescriptiveComplexity.OneInToClique.clique_slots`), pairwise in agreement: an
exactly-one model, and each model arises once
(`DescriptiveComplexity.OneInToClique.solEquiv`). A clause with no literal has no
occurrence vertex, so the count is `0`, as it should be.

The formulas do not mention the order; as in the decision reduction, the
packaging is ordered because both counts are of finite structures only.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace OneInToClique

/-! ### The semantic side -/

section Semantics

variable {A : Type} [Language.sat.Structure A]

/-- Choosing `(x, s)` as the one true literal of the clause `c` gives the
variable `y` the value `b`, as read on the occurrence `(y, t)` of `c`: the
literal `(y, t)` is true exactly when it is the chosen one. -/
def ForceAt (c x : A) (s : Bool) (y : A) (t b : Bool) : Prop :=
  OccIn c y t ∧ (b = t ↔ (y = x ∧ t = s))

/-- The choices `(c, x, s)` and `(c', x', s')` disagree: some variable is made
true by the first and false by the second. -/
def Clash (c x : A) (s : Bool) (c' x' : A) (s' : Bool) : Prop :=
  ∃ y, (∃ t, ForceAt c x s y t true) ∧ ∃ t, ForceAt c' x' s' y t false

/-- The choice `(c, x, s)` is a literal occurrence whose demands are
consistent. -/
def Sound (c x : A) (s : Bool) : Prop :=
  OccIn c x s ∧ ¬Clash c x s c x s

/-- The vertices that have neighbours: consistent occurrences, and diagonal
clause vertices. -/
def Valid : SatCliqueTag → A → A → Prop
  | .pos, c, x => Sound c x true
  | .neg, c, x => Sound c x false
  | .cl, c, x => c = x ∧ IsCl c

/-- Two occurrences are of distinct clauses and agree. -/
def SepS (s₁ s₂ : Bool) (c₁ x₁ c₂ x₂ : A) : Prop :=
  c₁ ≠ c₂ ∧ ¬Clash c₁ x₁ s₁ c₂ x₂ s₂ ∧ ¬Clash c₂ x₂ s₂ c₁ x₁ s₁

/-- What adjacency asks of a pair of vertices beyond their validity: of two
occurrence vertices, that they be of distinct clauses and agree. -/
def Sep : SatCliqueTag → A → A → SatCliqueTag → A → A → Prop
  | .pos, c₁, x₁, .pos, c₂, x₂ => SepS true true c₁ x₁ c₂ x₂
  | .pos, c₁, x₁, .neg, c₂, x₂ => SepS true false c₁ x₁ c₂ x₂
  | .neg, c₁, x₁, .pos, c₂, x₂ => SepS false true c₁ x₁ c₂ x₂
  | .neg, c₁, x₁, .neg, c₂, x₂ => SepS false false c₁ x₁ c₂ x₂
  | _, _, _, _, _, _ => True

/-- The adjacency condition of the interpreted graph. -/
def AdjCore (t₁ : SatCliqueTag) (c₁ x₁ : A) (t₂ : SatCliqueTag) (c₂ x₂ : A) : Prop :=
  Valid t₁ c₁ x₁ ∧ Valid t₂ c₂ x₂ ∧ Sep t₁ c₁ x₁ t₂ c₂ x₂

/-- The marking condition of the interpreted graph: two vertices per
clause. -/
def MarkedCore : SatCliqueTag → A → A → Prop
  | .neg, _, _ => False
  | _, c, x => c = x ∧ IsCl c

theorem valid_ofSign {s : Bool} {c x : A} : Valid (.ofSign s) c x ↔ Sound c x s := by
  cases s <;> exact Iff.rfl

theorem sep_ofSign {s₁ s₂ : Bool} {c₁ x₁ c₂ x₂ : A} :
    Sep (.ofSign s₁) c₁ x₁ (.ofSign s₂) c₂ x₂ ↔ SepS s₁ s₂ c₁ x₁ c₂ x₂ := by
  cases s₁ <;> cases s₂ <;> exact Iff.rfl

theorem sep_cl_left {c₁ x₁ c₂ x₂ : A} {t : SatCliqueTag} : Sep .cl c₁ x₁ t c₂ x₂ := by
  cases t <;> trivial

theorem sep_cl_right {c₁ x₁ c₂ x₂ : A} {t : SatCliqueTag} : Sep t c₁ x₁ .cl c₂ x₂ := by
  cases t <;> trivial

theorem Valid.isCl {t : SatCliqueTag} {c x : A} (h : Valid t c x) : IsCl c := by
  cases t
  · exact OccIn.isCl h.1
  · exact OccIn.isCl h.1
  · exact h.2

omit [Language.sat.Structure A] in
/-- The value of a variable, read off the truth of one of its literals. -/
theorem iff_true_of_litTrue {ν : A → Prop} {y : A} {t b : Bool} {P : Prop}
    (h : LitTrue ν y t ↔ P) (hb : b = t ↔ P) : ν y ↔ b = true := by
  cases t <;> cases b <;> simp_all [LitTrue]

omit [Language.sat.Structure A] in
/-- The truth of a literal, read off the value of its variable. -/
theorem litTrue_iff_of_true {ν : A → Prop} {y : A} {t b : Bool} {P : Prop}
    (h : ν y ↔ b = true) (hb : b = t ↔ P) : LitTrue ν y t ↔ P := by
  cases t <;> cases b <;> simp_all [LitTrue]

/-- Some value is forced. -/
theorem exists_force (P : Prop) (t : Bool) : ∃ b : Bool, b = t ↔ P := by
  by_cases h : P
  · exact ⟨t, by simp [h]⟩
  · exact ⟨!t, by cases t <;> simp [h]⟩

theorem occIn_satOccurs {c y : A} {t : Bool} (h : OccIn c y t) : SatOccurs A y := by
  cases t
  · exact ⟨c, h.1, Or.inr h.2⟩
  · exact ⟨c, h.1, Or.inl h.2⟩

/-- Under an exactly-one assignment, the literals of a clause other than its
true one are false. -/
theorem litTrue_iff_chosen {ν : A → Prop} (hν : OneInProper ν) {c x : A} {s : Bool}
    (hx : OccIn c x s) (hT : LitTrue ν x s) {y : A} {t : Bool} (hy : OccIn c y t) :
    LitTrue ν y t ↔ (y = x ∧ t = s) := by
  obtain ⟨x₀, s₀, -, -, huniq⟩ := hν c (OccIn.isCl hx)
  obtain ⟨hx₀, hs₀⟩ := huniq x s hx hT
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := huniq y t hy h
    exact ⟨h₁.trans hx₀.symm, h₂.trans hs₀.symm⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    exact hT

/-- An exactly-one assignment gives every variable the value its true literals
force. -/
theorem forced_of_model {ν : A → Prop} (hν : OneInProper ν) {c x : A} {s : Bool}
    (hx : OccIn c x s) (hT : LitTrue ν x s) {y : A} {t b : Bool}
    (hf : ForceAt c x s y t b) : ν y ↔ b = true :=
  iff_true_of_litTrue (litTrue_iff_chosen hν hx hT hf.1) hf.2

/-- The true literals of an exactly-one assignment agree. -/
theorem not_clash_of_model {ν : A → Prop} (hν : OneInProper ν) {c x c' x' : A}
    {s s' : Bool} (hx : OccIn c x s) (hT : LitTrue ν x s) (hx' : OccIn c' x' s')
    (hT' : LitTrue ν x' s') : ¬Clash c x s c' x' s' := by
  rintro ⟨y, ⟨t, h₁⟩, t', h₂⟩
  have hy := (forced_of_model hν hx hT h₁).mpr rfl
  exact absurd ((forced_of_model hν hx' hT' h₂).mp hy) (by decide)

end Semantics

/-! ### The formulas and the interpretation -/

section Formulas

variable {α : Type}

/-- `DescriptiveComplexity.OneInToClique.ForceAt`, as a formula: the signs are
parameters. -/
def forceAtF (s t b : Bool) (c x y : α) : satOrd.Formula α :=
  occF t c y ⊓
    if b = t then (if t = s then eqF y x else ⊥) else (if t = s then ∼(eqF y x) else ⊤)

/-- `DescriptiveComplexity.OneInToClique.Clash`, as a formula. -/
noncomputable def clashF (s s' : Bool) (c x c' x' : α) : satOrd.Formula α :=
  ((forceAtF s false true (.inl c) (.inl x) (.inr ()) ⊔
        forceAtF s true true (.inl c) (.inl x) (.inr ())) ⊓
      (forceAtF s' false false (.inl c') (.inl x') (.inr ()) ⊔
        forceAtF s' true false (.inl c') (.inl x') (.inr ()))).iExs Unit

/-- `DescriptiveComplexity.OneInToClique.Sound`, as a formula. -/
noncomputable def soundF (s : Bool) (c x : α) : satOrd.Formula α :=
  occF s c x ⊓ ∼(clashF s s c x c x)

/-- `DescriptiveComplexity.OneInToClique.Valid`, as a formula. -/
noncomputable def validF : SatCliqueTag → α → α → satOrd.Formula α
  | .pos, c, x => soundF true c x
  | .neg, c, x => soundF false c x
  | .cl, c, x => eqF c x ⊓ clF c

/-- `DescriptiveComplexity.OneInToClique.SepS`, as a formula. The free variable
`(i, j)` is the `j`-th component of the `i`-th vertex. -/
noncomputable def sepSF (s₁ s₂ : Bool) : satOrd.Formula (Fin 2 × Fin 2) :=
  ∼(eqF (0, 0) (1, 0)) ⊓ ∼(clashF s₁ s₂ (0, 0) (0, 1) (1, 0) (1, 1)) ⊓
    ∼(clashF s₂ s₁ (1, 0) (1, 1) (0, 0) (0, 1))

/-- `DescriptiveComplexity.OneInToClique.Sep`, as a formula. -/
noncomputable def sepF : SatCliqueTag → SatCliqueTag → satOrd.Formula (Fin 2 × Fin 2)
  | .pos, .pos => sepSF true true
  | .pos, .neg => sepSF true false
  | .neg, .pos => sepSF false true
  | .neg, .neg => sepSF false false
  | _, _ => ⊤

/-- The adjacency formulas of the interpretation, by tag. -/
noncomputable def adjF (t₁ t₂ : SatCliqueTag) : satOrd.Formula (Fin 2 × Fin 2) :=
  validF t₁ (0, 0) (0, 1) ⊓ validF t₂ (1, 0) (1, 1) ⊓ sepF t₁ t₂

/-- The mark formulas of the interpretation, by tag. -/
def markedF : SatCliqueTag → satOrd.Formula (Fin 1 × Fin 2)
  | .neg => ⊥
  | _ => eqF (0, 0) (0, 1) ⊓ clF (0, 0)

end Formulas

/-- The interpretation producing, from an ordered CNF structure, the clique
instance whose threshold-size cliques are its exactly-one models. -/
noncomputable def oneInToClique :
    FOInterpretation satOrd Language.markedGraph SatCliqueTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => adjF (t 0) (t 1)
    | _, .marked => fun t => markedF (t 0)

/-! ### Characterizations of the interpreted relations -/

section Characterization

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

section Realize

variable {α : Type} {v : α → A}

theorem realize_forceAtF {s t b : Bool} {c x y : α} :
    (forceAtF s t b c x y).Realize v ↔ ForceAt (v c) (v x) s (v y) t b := by
  cases s <;> cases t <;> cases b <;> simp [forceAtF, ForceAt]

theorem realize_clashF {s s' : Bool} {c x c' x' : α} :
    (clashF s s' c x c' x').Realize v ↔ Clash (v c) (v x) s (v c') (v x') s' := by
  simp only [clashF, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_forceAtF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨i (), ?_, ?_⟩
    · rcases h₁ with h | h
      exacts [⟨false, h⟩, ⟨true, h⟩]
    · rcases h₂ with h | h
      exacts [⟨false, h⟩, ⟨true, h⟩]
  · rintro ⟨y, ⟨t, h₁⟩, t', h₂⟩
    refine ⟨fun _ => y, ?_, ?_⟩
    · cases t
      exacts [Or.inl h₁, Or.inr h₁]
    · cases t'
      exacts [Or.inl h₂, Or.inr h₂]

theorem realize_soundF {s : Bool} {c x : α} :
    (soundF s c x).Realize v ↔ Sound (v c) (v x) s := by
  simp [soundF, Sound, realize_clashF]

theorem realize_validF {t : SatCliqueTag} {c x : α} :
    (validF t c x).Realize v ↔ Valid t (v c) (v x) := by
  cases t <;> simp [validF, Valid, realize_soundF]

end Realize

theorem realize_sepSF {s₁ s₂ : Bool} {v : Fin 2 × Fin 2 → A} :
    (sepSF s₁ s₂).Realize v ↔ SepS s₁ s₂ (v (0, 0)) (v (0, 1)) (v (1, 0)) (v (1, 1)) := by
  simp [sepSF, SepS, realize_clashF, and_assoc]

theorem realize_sepF {t₁ t₂ : SatCliqueTag} {v : Fin 2 × Fin 2 → A} :
    (sepF t₁ t₂).Realize v ↔ Sep t₁ (v (0, 0)) (v (0, 1)) t₂ (v (1, 0)) (v (1, 1)) := by
  cases t₁ <;> cases t₂ <;>
    first
      | exact realize_sepSF
      | simp [sepF, Sep]

theorem realize_adjF {t₁ t₂ : SatCliqueTag} {v : Fin 2 × Fin 2 → A} :
    (adjF t₁ t₂).Realize v ↔
      AdjCore t₁ (v (0, 0)) (v (0, 1)) t₂ (v (1, 0)) (v (1, 1)) := by
  simp [adjF, AdjCore, realize_validF, realize_sepF, and_assoc]

theorem realize_markedF {t : SatCliqueTag} {v : Fin 1 × Fin 2 → A} :
    (markedF t).Realize v ↔ MarkedCore t (v (0, 0)) (v (0, 1)) := by
  cases t <;> simp [markedF, MarkedCore]

/-- Characterization of the interpreted adjacency relation. -/
theorem oneInToClique_adj (t₁ t₂ : SatCliqueTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := oneInToClique.Map A) mgAdj ![(t₁, w₁), (t₂, w₂)] ↔
      AdjCore t₁ (w₁ 0) (w₁ 1) t₂ (w₂ 0) (w₂ 1) := by
  rw [FOInterpretation.relMap_map]
  simp only [oneInToClique]
  rw [realize_adjF]
  simp

/-- Characterization of the interpreted mark relation. -/
theorem oneInToClique_marked (t : SatCliqueTag) (w : Fin 2 → A) :
    RelMap (M := oneInToClique.Map A) mgMarked ![(t, w)] ↔
      MarkedCore t (w 0) (w 1) := by
  rw [FOInterpretation.relMap_map]
  simp only [oneInToClique]
  rw [realize_markedF]
  simp

theorem adj_iff (p q : oneInToClique.Map A) :
    MGAdj p q ↔ AdjCore p.1 (p.2 0) (p.2 1) q.1 (q.2 0) (q.2 1) := by
  obtain ⟨t₁, w₁⟩ := p
  obtain ⟨t₂, w₂⟩ := q
  exact oneInToClique_adj t₁ t₂ w₁ w₂

theorem marked_iff (p : oneInToClique.Map A) :
    MGMarked p ↔ MarkedCore p.1 (p.2 0) (p.2 1) := by
  obtain ⟨t, w⟩ := p
  exact oneInToClique_marked t w

end Characterization

/-! ### Naming the vertices -/

section Points

variable {A : Type}

/-- The vertex of tag `t` at the pair `(c, x)`. -/
def mkPt (t : SatCliqueTag) (c x : A) : oneInToClique.Map A := (t, ![c, x])

theorem eq_mkPt (p : oneInToClique.Map A) : p = mkPt p.1 (p.2 0) (p.2 1) := by
  obtain ⟨t, w⟩ := p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  fin_cases j <;> rfl

theorem mkPt_inj {t t' : SatCliqueTag} {c x c' x' : A} (h : mkPt t c x = mkPt t' c' x') :
    t = t' ∧ c = c' ∧ x = x' :=
  ⟨congrArg (fun p : oneInToClique.Map A => p.1) h,
    congrArg (fun p : oneInToClique.Map A => p.2 0) h,
    congrArg (fun p : oneInToClique.Map A => p.2 1) h⟩

theorem ofSign_ne_cl (s : Bool) : SatCliqueTag.ofSign s ≠ .cl := by
  cases s <;> decide

theorem ofSign_inj {s s' : Bool} (h : SatCliqueTag.ofSign s = .ofSign s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact absurd h (by decide)

theorem tag_cases (t : SatCliqueTag) : t = .cl ∨ ∃ s, t = .ofSign s := by
  cases t
  exacts [Or.inr ⟨true, rfl⟩, Or.inr ⟨false, rfl⟩, Or.inl rfl]

end Points

/-! ### The two sides of the bijection -/

section Sets

variable {A : Type} [Language.sat.Structure A]

/-- The clique of an assignment: every clause vertex, and the occurrence
vertices of its true literals. -/
def cliqueOf (ν : A → Prop) (p : oneInToClique.Map A) : Prop :=
  (p.1 = .cl ∧ p.2 0 = p.2 1 ∧ IsCl (p.2 0)) ∨
    ∃ s, p.1 = .ofSign s ∧ OccIn (p.2 0) (p.2 1) s ∧ LitTrue ν (p.2 1) s

/-- The assignment of a clique: the variables some occurrence vertex of the
clique makes true. -/
def modelOf (S : oneInToClique.Map A → Prop) (y : A) : Prop :=
  ∃ c x s t, S (mkPt (.ofSign s) c x) ∧ ForceAt c x s y t true

/-- The slots of a clique of the threshold size: two per clause. -/
abbrev Slot (A : Type) [Language.sat.Structure A] : Type :=
  {c : A // IsCl c} ⊕ {c : A // IsCl c}

/-- The marked vertices, by slot. -/
def markEnum : Slot A → oneInToClique.Map A :=
  Sum.elim (fun c => mkPt .cl c.1 c.1) (fun c => mkPt .pos c.1 c.1)

theorem markEnum_injective : Function.Injective (markEnum (A := A)) := by
  rintro (a | a) (b | b) h <;> obtain ⟨ht, hc, -⟩ := mkPt_inj h
  · exact congrArg Sum.inl (Subtype.ext hc)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact congrArg Sum.inr (Subtype.ext hc)

/-- The vertices of the clique of an exactly-one assignment, by slot: the
clause vertex, and the occurrence vertex of the true literal. -/
noncomputable def occEnum {ν : A → Prop} (hν : OneInProper ν) :
    Slot A → oneInToClique.Map A :=
  Sum.elim (fun c => mkPt .cl c.1 c.1)
    (fun c => mkPt (.ofSign (hν c.1 c.2).choose_spec.choose) c.1 (hν c.1 c.2).choose)

theorem occEnum_injective {ν : A → Prop} (hν : OneInProper ν) :
    Function.Injective (occEnum hν) := by
  rintro (a | a) (b | b) h <;> obtain ⟨ht, hc, -⟩ := mkPt_inj h
  · exact congrArg Sum.inl (Subtype.ext hc)
  · exact absurd ht.symm (ofSign_ne_cl _)
  · exact absurd ht (ofSign_ne_cl _)
  · exact congrArg Sum.inr (Subtype.ext hc)

theorem range_occEnum {ν : A → Prop} (hν : OneInProper ν) :
    Set.range (occEnum hν) = {p | cliqueOf ν p} := by
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨rfl, rfl, i.2⟩
    · exact Or.inr ⟨_, rfl, (hν i.1 i.2).choose_spec.choose_spec.1,
        (hν i.1 i.2).choose_spec.choose_spec.2.1⟩
  · rintro (⟨ht, hd, hc⟩ | ⟨s, ht, ho, hT⟩)
    · exact ⟨.inl ⟨p.2 0, hc⟩, ((eq_mkPt p).trans (by rw [ht, ← hd]; rfl)).symm⟩
    · have h := (hν (p.2 0) (OccIn.isCl ho)).choose_spec.choose_spec.2.2 (p.2 1) s ho hT
      have he : occEnum hν (.inr ⟨p.2 0, OccIn.isCl ho⟩) =
          mkPt (.ofSign s) (p.2 0) (p.2 1) :=
        congr (congrArg (fun t => mkPt (SatCliqueTag.ofSign t) (p.2 0)) h.2.symm) h.1.symm
      exact ⟨.inr ⟨p.2 0, OccIn.isCl ho⟩, he.trans ((eq_mkPt p).trans (by rw [ht])).symm⟩

theorem ncard_cliqueOf {ν : A → Prop} (hν : OneInProper ν) :
    {p | cliqueOf ν p}.ncard = Nat.card (Slot A) := by
  rw [← range_occEnum hν]
  exact Set.ncard_range_of_injective (occEnum_injective hν)

end Sets

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem range_markEnum : Set.range (markEnum (A := A)) = {p | MGMarked p} := by
  have h : ∀ (t : SatCliqueTag) (c x : A), MarkedCore t c x →
      ∃ i, markEnum i = mkPt t c x := by
    intro t c x h
    cases t
    · obtain ⟨hcx, hc⟩ := h
      subst hcx
      exact ⟨.inr ⟨c, hc⟩, rfl⟩
    · exact (h : False).elim
    · obtain ⟨hcx, hc⟩ := h
      subst hcx
      exact ⟨.inl ⟨c, hc⟩, rfl⟩
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  rw [marked_iff]
  constructor
  · rintro ⟨i | i, rfl⟩
    exacts [⟨rfl, i.2⟩, ⟨rfl, i.2⟩]
  · intro hp
    obtain ⟨i, hi⟩ := h p.1 (p.2 0) (p.2 1) hp
    exact ⟨i, hi.trans (eq_mkPt p).symm⟩

theorem ncard_marked : {p : oneInToClique.Map A | MGMarked p}.ncard = Nat.card (Slot A) := by
  rw [← range_markEnum]
  exact Set.ncard_range_of_injective markEnum_injective

/-- The clique of an exactly-one assignment is one. -/
theorem adj_cliqueOf {ν : A → Prop} (hν : OneInProper ν) {p q : oneInToClique.Map A}
    (hp : cliqueOf ν p) (hq : cliqueOf ν q) (hpq : p ≠ q) : MGAdj p q := by
  rw [adj_iff]
  have hvalid : ∀ r : oneInToClique.Map A, cliqueOf ν r → Valid r.1 (r.2 0) (r.2 1) := by
    rintro r (⟨ht, hd, hc⟩ | ⟨s, ht, ho, hT⟩)
    · rw [ht]
      exact ⟨hd, hc⟩
    · rw [ht]
      exact valid_ofSign.mpr ⟨ho, not_clash_of_model hν ho hT ho hT⟩
  refine ⟨hvalid p hp, hvalid q hq, ?_⟩
  rcases hp with ⟨ht, -, -⟩ | ⟨s, ht, ho, hT⟩
  · rw [ht]
    exact sep_cl_left
  · rcases hq with ⟨ht', -, -⟩ | ⟨s', ht', ho', hT'⟩
    · rw [ht']
      exact sep_cl_right
    · rw [ht, ht']
      refine sep_ofSign.mpr ⟨fun hc => hpq ?_, not_clash_of_model hν ho hT ho' hT',
        not_clash_of_model hν ho' hT' ho hT⟩
      have ho'' : OccIn (p.2 0) (q.2 1) s' := by
        rw [hc]
        exact ho'
      obtain ⟨hx, hs⟩ := (litTrue_iff_chosen hν ho hT ho'').mp hT'
      exact (eq_mkPt p).trans (Eq.trans (by rw [ht, ht', hc, hx, hs]) (eq_mkPt q).symm)

/-- The clique of an exactly-one assignment has the threshold size. -/
theorem cliqueOfSize_cliqueOf [Finite A] {ν : A → Prop} (hν : OneInProper ν) :
    CliqueOfSize (oneInToClique.Map A) (cliqueOf ν) :=
  ⟨oneInToClique.map_finite A, fun _ _ hp hq hpq => adj_cliqueOf hν hp hq hpq,
    (ncard_cliqueOf hν).trans ncard_marked.symm⟩

section Clique

variable [Finite A] {S : oneInToClique.Map A → Prop}

/-- Every vertex of a clique of the threshold size has a neighbour in it, so
none is junk. -/
theorem valid_of_clique (hS : CliqueOfSize (oneInToClique.Map A) S)
    {p : oneInToClique.Map A} (hp : S p) : Valid p.1 (p.2 0) (p.2 1) := by
  obtain ⟨hfin, hadj, hcard⟩ := hS
  have hpos : 0 < {q | S q}.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨p, hp⟩
  have h2 : 1 < {q | S q}.ncard := by
    rw [hcard, ncard_marked, Nat.card_sum] at hpos ⊢
    omega
  obtain ⟨q, hq, hqp⟩ := Set.exists_ne_of_one_lt_ncard h2 p
  exact ((adj_iff p q).mp (hadj p q hp hq (Ne.symm hqp))).1

/-- The slot a vertex of a clique fills. -/
noncomputable def slot (hv : ∀ p : oneInToClique.Map A, S p → Valid p.1 (p.2 0) (p.2 1))
    (p : {p // S p}) : Slot A :=
  if p.1.1 = SatCliqueTag.cl then .inl ⟨p.1.2 0, (hv p.1 p.2).isCl⟩
  else .inr ⟨p.1.2 0, (hv p.1 p.2).isCl⟩

omit [Finite A] in
/-- Two vertices of a clique fill distinct slots. -/
theorem slot_injective (hadj : ∀ p q : oneInToClique.Map A, S p → S q → p ≠ q → MGAdj p q)
    (hv : ∀ p : oneInToClique.Map A, S p → Valid p.1 (p.2 0) (p.2 1)) :
    Function.Injective (slot hv) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  refine Subtype.ext ?_
  change p = q
  by_cases htp : p.1 = .cl <;> by_cases htq : q.1 = .cl <;>
    simp only [slot, htp, htq, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq,
      reduceCtorEq] at h
  · have hvp := hv p hp
    have hvq := hv q hq
    rw [htp] at hvp
    rw [htq] at hvq
    exact (eq_mkPt p).trans
      (Eq.trans (by rw [htp, htq, ← hvp.1, ← hvq.1, h]) (eq_mkPt q).symm)
  · by_contra hne
    have hsep := ((adj_iff p q).mp (hadj p q hp hq hne)).2.2
    obtain ⟨s₁, hs₁⟩ := (tag_cases p.1).resolve_left htp
    obtain ⟨s₂, hs₂⟩ := (tag_cases q.1).resolve_left htq
    rw [hs₁, hs₂] at hsep
    exact (sep_ofSign.mp hsep).1 h

/-- **A clique of the threshold size fills every slot**: it holds every clause
vertex, and an occurrence vertex of every clause. -/
theorem clique_slots (hS : CliqueOfSize (oneInToClique.Map A) S) (c : A) (hc : IsCl c) :
    S (mkPt .cl c c) ∧ ∃ x s, S (mkPt (.ofSign s) c x) := by
  have hv : ∀ p : oneInToClique.Map A, S p → Valid p.1 (p.2 0) (p.2 1) :=
    fun p hp => valid_of_clique hS hp
  have hcard : Nat.card {p // S p} = Nat.card (Slot A) :=
    (Nat.card_coe_set_eq {p | S p}).trans (hS.2.2.trans ncard_marked)
  have hsurj := ((slot_injective hS.2.1 hv).bijective_of_nat_card_le hcard.ge).2
  constructor
  · obtain ⟨⟨p, hp⟩, hpc⟩ := hsurj (.inl ⟨c, hc⟩)
    by_cases htp : p.1 = .cl <;>
      simp only [slot, htp, ↓reduceIte, Sum.inl.injEq, Subtype.mk.injEq, reduceCtorEq] at hpc
    have hvp := hv p hp
    rw [htp] at hvp
    have he : p = mkPt .cl c c := (eq_mkPt p).trans (by rw [htp, ← hvp.1, hpc])
    exact Eq.mp (congrArg S he) hp
  · obtain ⟨⟨p, hp⟩, hpc⟩ := hsurj (.inr ⟨c, hc⟩)
    by_cases htp : p.1 = .cl <;>
      simp only [slot, htp, ↓reduceIte, Sum.inr.injEq, Subtype.mk.injEq, reduceCtorEq] at hpc
    obtain ⟨s, hs⟩ := (tag_cases p.1).resolve_left htp
    have he : p = mkPt (.ofSign s) c (p.2 1) := (eq_mkPt p).trans (by rw [hs, hpc])
    exact ⟨p.2 1, s, Eq.mp (congrArg S he) hp⟩

theorem sound_of_mem (hS : CliqueOfSize (oneInToClique.Map A) S) {s : Bool} {c x : A}
    (h : S (mkPt (.ofSign s) c x)) : Sound c x s :=
  valid_ofSign.mp (valid_of_clique hS h)

/-- The assignment of a clique gives every variable the value an occurrence
vertex of the clique forces. -/
theorem forced_of_clique (hS : CliqueOfSize (oneInToClique.Map A) S) {s : Bool} {c x : A}
    (h : S (mkPt (.ofSign s) c x)) {y : A} {t b : Bool} (hf : ForceAt c x s y t b) :
    modelOf S y ↔ b = true := by
  cases b
  · refine iff_of_false ?_ (by decide)
    rintro ⟨c', x', s', t', h', hf'⟩
    by_cases heq : mkPt (.ofSign s') c' x' = mkPt (.ofSign s) c x
    · obtain ⟨hs, hc, hx⟩ := mkPt_inj heq
      have hs' := ofSign_inj hs
      subst hs' hc hx
      exact (sound_of_mem hS h).2 ⟨y, ⟨t', hf'⟩, t, hf⟩
    · have hadj := (adj_iff _ _).mp (hS.2.1 _ _ h' h heq)
      exact (sep_ofSign.mp hadj.2.2).2.1 ⟨y, ⟨t', hf'⟩, t, hf⟩
  · exact iff_of_true ⟨c, x, s, t, h, hf⟩ rfl

theorem litTrue_modelOf (hS : CliqueOfSize (oneInToClique.Map A) S) {s : Bool} {c x : A}
    (h : S (mkPt (.ofSign s) c x)) {y : A} {t : Bool} (hy : OccIn c y t) :
    LitTrue (modelOf S) y t ↔ (y = x ∧ t = s) := by
  obtain ⟨b, hb⟩ := exists_force (y = x ∧ t = s) t
  exact litTrue_iff_of_true (forced_of_clique hS h ⟨hy, hb⟩) hb

/-- The assignment of a clique of the threshold size is an exactly-one
model. -/
theorem oneInModel_modelOf (hS : CliqueOfSize (oneInToClique.Map A) S) :
    OneInModel A (modelOf S) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · obtain ⟨-, x, s, h⟩ := clique_slots hS c hc
    have ho := (sound_of_mem hS h).1
    exact ⟨x, s, ho, (litTrue_modelOf hS h ho).mpr ⟨rfl, rfl⟩,
      fun y t hy hT => (litTrue_modelOf hS h hy).mp hT⟩
  · rintro y ⟨c, x, s, t, -, hf⟩
    exact occIn_satOccurs hf.1

/-- A clique of the threshold size is the clique of its assignment. -/
theorem cliqueOf_modelOf (hS : CliqueOfSize (oneInToClique.Map A) S) :
    cliqueOf (modelOf S) = S := by
  have hmod := oneInModel_modelOf hS
  have := hS.1
  have hsub : {p | S p} ⊆ {p | cliqueOf (modelOf S) p} := by
    intro p hp
    have hv := valid_of_clique hS hp
    rcases tag_cases p.1 with ht | ⟨s, ht⟩
    · rw [ht] at hv
      exact Or.inl ⟨ht, hv.1, hv.2⟩
    · have hp' : S (mkPt (.ofSign s) (p.2 0) (p.2 1)) := by
        rw [← ht, ← eq_mkPt p]
        exact hp
      have ho := (sound_of_mem hS hp').1
      exact Or.inr ⟨s, ht, ho, (litTrue_modelOf hS hp' ho).mpr ⟨rfl, rfl⟩⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub
    ((ncard_cliqueOf hmod.1).trans (ncard_marked.symm.trans hS.2.2.symm)).le (Set.toFinite _)
  funext p
  exact propext (Set.ext_iff.mp heq p).symm

end Clique

omit [LinearOrder A] in
/-- An exactly-one model is the assignment of its clique. -/
theorem modelOf_cliqueOf {ν : A → Prop} (hν : OneInModel A ν) :
    modelOf (cliqueOf ν) = ν := by
  funext y
  refine propext ⟨?_, fun hy => ?_⟩
  · rintro ⟨c, x, s, t, hmem, hf⟩
    rcases hmem with ⟨ht, -, -⟩ | ⟨s', ht, ho, hT⟩
    · exact absurd ht (ofSign_ne_cl s)
    · have hs := ofSign_inj ht
      subst hs
      exact (forced_of_model hν.1 ho hT hf).mpr rfl
  · obtain ⟨c, hc, hocc⟩ := hν.2 y hy
    obtain ⟨t, hyt⟩ : ∃ t, OccIn c y t := by
      rcases hocc with h | h
      exacts [⟨true, hc, h⟩, ⟨false, hc, h⟩]
    obtain ⟨x, s, hx, hT, -⟩ := hν.1 c hc
    obtain ⟨b, hb⟩ := exists_force (y = x ∧ t = s) t
    have hf : ForceAt c x s y t b := ⟨hyt, hb⟩
    have hbt : b = true := (forced_of_model hν.1 hx hT hf).mp hy
    subst hbt
    exact ⟨c, x, s, t, Or.inr ⟨s, rfl, hx, hT⟩, hf⟩

variable (A) [Finite A]

/-- **The cliques of the threshold size of the interpreted graph are the
exactly-one models of the CNF formula**, bijectively. -/
noncomputable def solEquiv :
    {ν : A → Prop // OneInModel A ν} ≃
      {S : oneInToClique.Map A → Prop // CliqueOfSize (oneInToClique.Map A) S} where
  toFun ν := ⟨cliqueOf ν.1, cliqueOfSize_cliqueOf ν.2.1⟩
  invFun S := ⟨modelOf S.1, oneInModel_modelOf S.2⟩
  left_inv ν := Subtype.ext (modelOf_cliqueOf ν.2)
  right_inv S := Subtype.ext (cliqueOf_modelOf S.2)

/-- **Correctness of the interpretation, for counting.** -/
theorem sharpClique_map : SharpClique (oneInToClique.Map A) = SharpOneInSAT A := by
  rw [sharpClique_apply, sharpOneInSat_apply]
  exact (Nat.card_congr (solEquiv A)).symm

end Correctness

end OneInToClique

open OneInToClique in
/-- **#1-in-SAT reduces parsimoniously to #Clique.** -/
noncomputable def sharpOneInSat_ordered_parsimonious_sharpClique :
    SharpOneInSAT ≤ᵖ[≤] SharpClique where
  Tag := SatCliqueTag
  dim := 2
  toInterpretation := oneInToClique
  correct A _ _ _ _ := (sharpClique_map A).symm

/-- #Clique is parsimoniously `#P`-hard. -/
theorem sharpClique_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpClique :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpOneInSat_ordered_parsimonious_sharpClique sharpOneInSat_sharpP_parsimoniousHard

/-- **#Clique is parsimoniously `#P`-complete**, counting the cliques of exactly
the threshold size.
Registered in the Lax archive as
[`Lax280166.CliqueComplete.sharpClique_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.CliqueComplete.html#s-Lax280166.CliqueComplete.sharpClique_sharpP_parsimoniousComplete). -/
theorem sharpClique_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpClique :=
  ⟨sharpClique_mem_sharpP, sharpClique_sharpP_parsimoniousHard⟩

/-- `SharpClique` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpClique_sharpP_complete : SharpP.Complete SharpClique :=
  complete_sharpP_of_parsimoniousComplete sharpClique_sharpP_parsimoniousComplete

end DescriptiveComplexity
