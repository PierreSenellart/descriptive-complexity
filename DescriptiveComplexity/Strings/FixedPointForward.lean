/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import DescriptiveComplexity.FixedPoint
public import DescriptiveComplexity.Strings.FirstOrder
public import DescriptiveComplexity.Strings.Transport
public import Mathlib.ModelTheory.Order
import all DescriptiveComplexity.FixedPoint

/-!
# FO(LFP) of the library, in the syntax of the archive

A definition of the library (`DescriptiveComplexity.LFPDef`) computes one simultaneous
least fixed point of a block of relation variables, by rules. The syntax of the
archive has only single-relation fixed points, but they nest, and they may mention the
relation variables of the enclosing ones; Bekić's principle ([Bekić 1984][bekic1984definable])
then says that a simultaneous fixed point is a nesting of single ones.

## Bekić's principle

The nesting is defined as a recursion on the variables still to be bound
(`DescriptiveComplexity.Strings.Bekic.solve`): the value of a variable already bound is
read from the environment, and that of an unbound variable is the least fixed point of
its operator, in which every other variable is solved recursively, this variable being
now bound. `DescriptiveComplexity.Strings.Bekic.solve_spec` says that the outcome, once
enough variables have been bound, is the least family closed under the operators.

## The formula

`DescriptiveComplexity.Strings.atF` follows the same recursion on syntax, and a rule
reads an atom of the block through whatever formula it is handed
(`DescriptiveComplexity.Strings.ruleF`), so no substitution is ever defined. The body of
a fixed point is positive by construction
(`DescriptiveComplexity.Strings.atF_pos`): atoms occur under conjunctions, quantifiers,
and the two negations of a disjunction, and the first-order guards mention no relation
variable.
-/

@[expose] public section

namespace DescriptiveComplexity.Strings

open FirstOrder Language Structure
open Lax.OrderedStructures Lax.LeastFixedPoints Lax.FixedPointSyntax Lax.FixedPointSemantics

/-! ### Bekić's principle -/

namespace Bekic

variable {ι : Type} {X : ι → Type} (Op : (∀ i, Set (X i)) → ∀ j, Set (X j))

open Classical in
/-- The nesting of least fixed points: `E` holds the values of the variables in `bd`. -/
noncomputable def solve : ℕ → Set ι → (∀ i, Set (X i)) → ∀ j, Set (X j)
  | 0, bd, E, j => if j ∈ bd then E j else ∅
  | n + 1, bd, E, j =>
      if j ∈ bd then E j else
        leastFixedPoint fun R => Op (solve n (insert j bd) (Function.update E j R)) j

/-- A family closed under the operators of the variables outside `bd`, with the prescribed
values on `bd`. -/
def Pre (bd : Set ι) (E W : ∀ i, Set (X i)) : Prop :=
  (∀ i ∈ bd, W i = E i) ∧ ∀ k, k ∉ bd → Op W k ⊆ W k

variable {Op} (hOp : Monotone Op)
include hOp

/-- The nesting is monotone in its environment. -/
theorem solve_mono (n : ℕ) (bd : Set ι) {E E' : ∀ i, Set (X i)} (h : E ≤ E') :
    solve Op n bd E ≤ solve Op n bd E' := by
  classical
  induction n generalizing bd E E' with
  | zero =>
    intro j
    simp only [solve]
    split
    · exact h j
    · exact le_rfl
  | succ n ih =>
    intro j
    simp only [solve]
    split
    · exact h j
    · have hupd : ∀ {E₁ E₂ : ∀ i, Set (X i)} (_ : E₁ ≤ E₂) {R₁ R₂ : Set (X j)} (_ : R₁ ⊆ R₂),
          Function.update E₁ j R₁ ≤ Function.update E₂ j R₂ := by
        intro E₁ E₂ hE R₁ R₂ hR i
        by_cases hi : i = j
        · subst hi; simpa using hR
        · simpa [Function.update_of_ne hi] using hE i
      have hm : Monotone fun R => Op (solve Op n (insert j bd) (Function.update E' j R)) j := by
        intro R₁ R₂ hR
        exact hOp (ih _ (hupd le_rfl hR)) j
      refine least _ _ ?_
      intro a ha
      refine (fixedPoint _ hm).subset ?_
      exact hOp (ih _ (hupd h Set.Subset.rfl)) j ha

/-- **Bekić's principle**: once the variables outside `bd` are few enough, the nesting
is the least family closed under the operators, with the prescribed values on `bd`. -/
theorem solve_spec [Finite ι] (n : ℕ) (bd : Set ι) (E : ∀ i, Set (X i))
    (hn : (bdᶜ).ncard ≤ n) :
    Pre Op bd E (solve Op n bd E) ∧ ∀ W, Pre Op bd E W → solve Op n bd E ≤ W := by
  classical
  induction n generalizing bd E with
  | zero =>
    have hall : ∀ j, j ∈ bd := by
      intro j
      by_contra hj
      have : (bdᶜ).Nonempty := ⟨j, hj⟩
      have := (Set.ncard_pos (Set.toFinite _)).mpr this
      omega
    refine ⟨⟨fun i hi => by simp [solve, hi], fun k hk => absurd (hall k) hk⟩, fun W hW j => ?_⟩
    simp [solve, hall j, hW.1 j (hall j)]
  | succ n ih =>
    have hfuel : ∀ j, j ∉ bd → ((insert j bd)ᶜ).ncard ≤ n := by
      intro j hj
      have h₁ : (insert j bd)ᶜ ⊂ bdᶜ := by
        have hs : (insert j bd)ᶜ ⊆ bdᶜ := fun x hx hx' => hx (Set.mem_insert_of_mem _ hx')
        exact (Set.ssubset_iff_of_subset hs).mpr ⟨j, hj, fun h => h (Set.mem_insert _ _)⟩
      have := Set.ncard_lt_ncard h₁ (Set.toFinite _)
      omega
    have hupd : ∀ {E₁ : ∀ i, Set (X i)} (j : ι) {R₁ R₂ : Set (X j)} (_ : R₁ ⊆ R₂),
        Function.update E₁ j R₁ ≤ Function.update E₁ j R₂ := by
      intro E₁ j R₁ R₂ hR i
      by_cases hi : i = j
      · subst hi; simpa using hR
      · simp [Function.update_of_ne hi]
    have hm : ∀ j, Monotone fun R => Op (solve Op n (insert j bd) (Function.update E j R)) j :=
      fun j R₁ R₂ hR => hOp (solve_mono hOp _ _ (hupd j hR)) j
    have hval : ∀ j, j ∉ bd → solve Op (n + 1) bd E j =
        leastFixedPoint fun R => Op (solve Op n (insert j bd) (Function.update E j R)) j := by
      intro j hj
      simp [solve, hj]
    have hPreUp : ∀ (W : ∀ i, Set (X i)) (j : ι), j ∉ bd → Pre Op bd E W →
        Pre Op (insert j bd) (Function.update E j (W j)) W := by
      intro W j hj hW
      refine ⟨fun i hi => ?_, fun k hk => hW.2 k fun h => hk (Set.mem_insert_of_mem _ h)⟩
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact hW.1 i ((Set.mem_insert_iff.mp hi).resolve_left hij)
    have hleast : ∀ W, Pre Op bd E W → solve Op (n + 1) bd E ≤ W := by
      intro W hW j
      by_cases hj : j ∈ bd
      · simp [solve, hj, hW.1 j hj]
      · rw [hval j hj]
        refine least _ _ ?_
        refine (hOp ((ih _ _ (hfuel j hj)).2 W (hPreUp W j hj hW)) j).trans (hW.2 j hj)
    refine ⟨⟨fun i hi => by simp [solve, hi], fun k hk => ?_⟩, hleast⟩
    -- the family obtained by solving the others around the value of `k`
    set Z := solve Op (n + 1) bd E with hZ
    set W' := solve Op n (insert k bd) (Function.update E k (Z k)) with hW'
    have hsp := ih (insert k bd) (Function.update E k (Z k)) (hfuel k hk)
    have hfix : Op W' k = Z k := by
      have := fixedPoint _ (hm k)
      rw [← hval k hk] at this
      exact this
    have hW'pre : Pre Op bd E W' := by
      refine ⟨fun i hi => ?_, fun m hm' => ?_⟩
      · have hik : i ≠ k := fun h => hk (h ▸ hi)
        have := hsp.1.1 i (Set.mem_insert_of_mem _ hi)
        rwa [Function.update_of_ne hik] at this
      · by_cases hmk : m = k
        · subst hmk
          have := hsp.1.1 m (Set.mem_insert _ _)
          rw [Function.update_self] at this
          rw [show W' m = Z m from this]
          exact hfix.subset
        · exact hsp.1.2 m fun h => (Set.mem_insert_iff.mp h).elim hmk hm'
    exact (hOp (hleast W' hW'pre) k).trans hfix.subset

end Bekic

/-! ### The syntax -/

section Syntax

variable {σ : Vocabulary} {ρ : List ℕ}

/-- The false formula. -/
def falseF {m : ℕ} : RawFormula σ m ρ := .neg .truth

/-- A disjunction. -/
def orF {m : ℕ} (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ := .neg (.conj (.neg φ) (.neg ψ))

/-- The disjunction of a list. -/
def bigOr {m : ℕ} (l : List (RawFormula σ m ρ)) : RawFormula σ m ρ := l.foldr orF falseF

/-- The conjunction of a list. -/
def bigAnd {m : ℕ} (l : List (RawFormula σ m ρ)) : RawFormula σ m ρ := l.foldr .conj .truth

/-- `k` nested quantifiers. -/
def exV : (k : ℕ) → {m : ℕ} → RawFormula σ (m + k) ρ → RawFormula σ m ρ
  | 0, _, φ => φ
  | k + 1, _, φ => exV k (.exists' φ)

/-- The position of the `q`-th variable bound by `exV`. -/
def exPos {m k : ℕ} (q : Fin k) : Fin (m + k) := ⟨q, by omega⟩

/-- The position of a variable under `exV`. -/
def exLift {m : ℕ} (k : ℕ) (i : Fin m) : Fin (m + k) := ⟨i + k, by omega⟩

/-- The assignment of the variables of `exV`. -/
def exVal {N : Type} {m k : ℕ} (y : Fin k → N) (v : Fin m → N) (i : Fin (m + k)) : N :=
  if h : (i : ℕ) < k then y ⟨i, h⟩ else v ⟨i - k, by omega⟩

private theorem exVal_pos {N : Type} {m k : ℕ} (y : Fin k → N) (v : Fin m → N) (q : Fin k) :
    exVal y v (exPos q) = y q := by
  simp [exVal, exPos]

private theorem exVal_lift {N : Type} {m k : ℕ} (y : Fin k → N) (v : Fin m → N) (i : Fin m) :
    exVal y v (exLift k i) = v i := by
  simp [exVal, exLift]

variable (A : OrderedStructure σ)

private theorem eval_falseF {m : ℕ} (v : Fin m → Fin A.size) (η : RelationEnv A.size ρ) :
    ¬ eval (falseF : RawFormula σ m ρ) A v η := fun h => h trivial

private theorem eval_orF {m : ℕ} (φ ψ : RawFormula σ m ρ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : eval (orF φ ψ) A v η ↔ eval φ A v η ∨ eval ψ A v η := by
  change ¬ (¬ eval φ A v η ∧ ¬ eval ψ A v η) ↔ _
  tauto

private theorem eval_bigOr {m : ℕ} (l : List (RawFormula σ m ρ)) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : eval (bigOr l) A v η ↔ ∃ φ ∈ l, eval φ A v η := by
  induction l with
  | nil => exact ⟨fun h => (eval_falseF A v η h).elim, by simp⟩
  | cons φ l ih =>
    change eval (orF φ (bigOr l)) A v η ↔ _
    rw [eval_orF, ih]
    simp

private theorem eval_bigAnd {m : ℕ} (l : List (RawFormula σ m ρ)) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) : eval (bigAnd l) A v η ↔ ∀ φ ∈ l, eval φ A v η := by
  induction l with
  | nil => exact ⟨fun _ => by simp, fun _ => trivial⟩
  | cons φ l ih =>
    change (eval φ A v η ∧ eval (bigAnd l) A v η) ↔ _
    rw [ih]
    simp

private theorem eval_exV (k : ℕ) {m : ℕ} (φ : RawFormula σ (m + k) ρ) (v : Fin m → Fin A.size)
    (η : RelationEnv A.size ρ) :
    eval (exV k φ) A v η ↔ ∃ y : Fin k → Fin A.size, eval φ A (exVal y v) η := by
  induction k with
  | zero =>
    have hv : ∀ y : Fin 0 → Fin A.size, exVal y v = v := by
      intro y; funext i; simp [exVal]
    exact ⟨fun h => ⟨Fin.elim0, by rwa [hv]⟩, fun ⟨y, h⟩ => by rwa [hv] at h⟩
  | succ k ih =>
    refine (ih (.exists' φ)).trans ?_
    have hcons : ∀ (y : Fin k → Fin A.size) (a : Fin A.size),
        (Fin.cons a (exVal y v) : Fin (m + (k + 1)) → Fin A.size) = exVal (Fin.cons a y) v := by
      intro y a
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [exVal]
      · by_cases h : (j : ℕ) < k
        · simp [exVal, h, Fin.cons]
        · simp [exVal, h]
    constructor
    · rintro ⟨y, a, ha⟩
      exact ⟨Fin.cons a y, by rwa [hcons] at ha⟩
    · rintro ⟨y', hy'⟩
      refine ⟨Fin.tail y', y' 0, ?_⟩
      rw [hcons, Fin.cons_self_tail]
      exact hy'

/-- A formula positive in every relation variable. -/
def Pos {m : ℕ} (φ : RawFormula σ m ρ) : Prop :=
  φ.Admissible ∧ ∀ r, φ.positiveAt r true

/-- A formula that may be used at either polarity: it mentions no relation variable. -/
def Inert {m : ℕ} (φ : RawFormula σ m ρ) : Prop :=
  φ.Admissible ∧ ∀ r p, φ.positiveAt r p

private theorem Inert.pos {m : ℕ} {φ : RawFormula σ m ρ} (h : Inert φ) : Pos φ :=
  ⟨h.1, fun r => h.2 r true⟩

private theorem pos_falseF {m : ℕ} : Pos (falseF : RawFormula σ m ρ) :=
  ⟨trivial, fun _ => trivial⟩

/-- A disjunction, at any polarity. -/
private theorem orF_positiveAt {m : ℕ} {φ ψ : RawFormula σ m ρ} {r : Fin ρ.length} {p : Bool}
    (h₁ : φ.positiveAt r p) (h₂ : ψ.positiveAt r p) : (orF φ ψ).positiveAt r p := by
  change RawFormula.positiveAt (.conj (.neg φ) (.neg ψ)) r (!p)
  refine ⟨?_, ?_⟩ <;> change RawFormula.positiveAt _ r (!!p) <;> simpa

private theorem pos_orF {m : ℕ} {φ ψ : RawFormula σ m ρ} (h₁ : Pos φ) (h₂ : Pos ψ) : Pos (orF φ
    ψ) :=
  ⟨⟨h₁.1, h₂.1⟩, fun r => orF_positiveAt (h₁.2 r) (h₂.2 r)⟩

private theorem pos_bigOr {m : ℕ} {l : List (RawFormula σ m ρ)} (h : ∀ φ ∈ l, Pos φ) : Pos (bigOr
    l) := by
  induction l with
  | nil => exact pos_falseF
  | cons φ l ih =>
    exact pos_orF (h φ (by simp)) (ih fun ψ hψ => h ψ (by simp [hψ]))

private theorem pos_bigAnd {m : ℕ} {l : List (RawFormula σ m ρ)} (h : ∀ φ ∈ l, Pos φ) :
    Pos (bigAnd l) := by
  induction l with
  | nil => exact ⟨trivial, fun _ => trivial⟩
  | cons φ l ih =>
    have h₁ := h φ (by simp)
    have h₂ := ih fun ψ hψ => h ψ (by simp [hψ])
    exact ⟨⟨h₁.1, h₂.1⟩, fun r => ⟨h₁.2 r, h₂.2 r⟩⟩

private theorem pos_exV (k : ℕ) {m : ℕ} {φ : RawFormula σ (m + k) ρ} (h : Pos φ) : Pos (exV k φ)
    := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih ⟨h.1, h.2⟩

end Syntax

/-! ### First-order guards and rules -/

section Rules

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) {ρ : List ℕ}

/-- The atoms of the ordered expansion, in the syntax of the archive. Neither of them
mentions a relation variable. -/
def ordAtom {m n : ℕ} : (L.sum Language.order).Relations n → (Fin n → Fin m) →
    {φ : RawFormula V.σ m ρ // Inert φ}
  | .inl R, a => ⟨.relation (V.toSym R) (a ∘ Fin.cast (V.arity_toSym R)),
      trivial, fun _ _ => trivial⟩
  | .inr .le, a => ⟨.neg (.less (a 1) (a 0)), trivial, fun _ _ => trivial⟩

/-- The translation of a formula of the ordered expansion. -/
def guardAlg : FOAlg (L.sum Language.order) :=
  rawAlg V.σ ρ Inert
    ⟨trivial, fun _ _ => trivial⟩
    (fun _ _ => ⟨trivial, fun _ _ => trivial⟩)
    (fun h => ⟨h.1, fun r p => h.2 r (!p)⟩)
    (fun h₁ h₂ => ⟨⟨h₁.1, h₂.1⟩, fun r p => ⟨h₁.2 r p, h₂.2 r p⟩⟩)
    (fun h => ⟨h.1, h.2⟩)
    (ordAtom V)

variable (S : OrderedStructure V.σ)

/-- The ordered expansion of the structure a table reads as. -/
@[instance_reducible]
def ordStr : (L.sum Language.order).Structure (Fin S.size) :=
  @sumOrderStructure L (Fin S.size) (ofOrdered V S) _

/-- The semantics of `guardAlg`. -/
private theorem guardSem (η : RelationEnv S.size ρ) :
    letI := ordStr V S
    FOAlg.Sem (guardAlg V (ρ := ρ)) (Fin S.size) (fun φ w => eval φ.1 S w η) := by
  let := ordStr V S
  refine { truth := fun _ => trivial, equal := fun _ _ _ => Iff.rfl, atom := ?_,
           neg := fun _ _ => Iff.rfl, conj := fun _ _ _ => Iff.rfl, ex := ?_, ext := ?_ }
  · rintro m k (Q | Q) a w
    · exact Iff.rfl
    · cases Q
      change ¬ (w (a 1) < w (a 0)) ↔ w (a 0) ≤ w (a 1)
      exact not_lt
  · intro m φ w
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.cons a w, rfl, ha⟩
    · rintro ⟨w', rfl, ha⟩
      refine ⟨w' 0, ?_⟩
      have : (Fin.cons (w' 0) (w' ∘ Fin.succ) : Fin (m + 1) → _) = w' := Fin.cons_self_tail w'
      change eval φ.1 S (Fin.cons (w' 0) (w' ∘ Fin.succ)) η
      rw [this]
      exact ha
  · intro m a w
    exact ⟨Fin.cons a w, rfl, rfl⟩

variable {B : SOBlock} {kk : ℕ}

/-- The formula of a rule with head `a`, whose variable is `j`. -/
noncomputable def firedF (c : HornClause (L.sum Language.order) B kk) (a : SOAtom B kk) (j : B.ι)
    (h : a.idx = j) {m : ℕ} (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ) :
    RawFormula V.σ m ρ :=
  exV kk (.conj (.conj
    (bigAnd ((List.finRange _).map fun q =>
      .equal (exLift kk (x q)) (exPos (a.args (Fin.cast (congrArg B.arity h.symm) q)))))
    ((guardAlg V (ρ := ρ)).tr c.guard (Sum.elim exPos Fin.elim0)).1)
    (bigAnd (c.body.map fun b => atF b.idx (exPos ∘ b.args))))

open Classical in
/-- A rule, read as the formula saying it derives the tuple `x` of the variable `j`, an
atom of the block being read through `atF`. -/
noncomputable def ruleF (c : HornClause (L.sum Language.order) B kk) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ) :
    RawFormula V.σ m ρ :=
  match c.head with
  | none => falseF
  | some a => if h : a.idx = j then firedF V c a j h x atF else falseF

/-- The rules for a variable, as one disjunction. -/
noncomputable def bodyF (rules : List (HornClause (L.sum Language.order) B kk)) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ) :
    RawFormula V.σ m ρ :=
  bigOr (rules.map fun c => ruleF V c j x atF)

private theorem pos_firedF (c : HornClause (L.sum Language.order) B kk) (a : SOAtom B kk) (j : B.ι)
    (h : a.idx = j) {m : ℕ} (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m'), Pos (atF k a)) :
    Pos (firedF V c a j h x atF) := by
  refine pos_exV _ ?_
  have hE : Pos (bigAnd ((List.finRange _).map fun q => (.equal (exLift kk (x q))
      (exPos (a.args (Fin.cast (congrArg B.arity h.symm) q))) : RawFormula V.σ (m + kk) ρ))) := by
    refine pos_bigAnd fun φ hφ => ?_
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
    exact ⟨trivial, fun _ => trivial⟩
  have hG := (((guardAlg V (ρ := ρ)).tr c.guard
    (Sum.elim exPos Fin.elim0 : Fin kk ⊕ Fin 0 → Fin (m + kk))).2).pos
  have hB : Pos (bigAnd (c.body.map fun b => atF b.idx
      (exPos ∘ b.args : _ → Fin (m + kk)))) := by
    refine pos_bigAnd fun φ hφ => ?_
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hφ
    exact hAt _ _
  exact ⟨⟨⟨hE.1, hG.1⟩, hB.1⟩, fun r => ⟨⟨hE.2 r, hG.2 r⟩, hB.2 r⟩⟩

private theorem pos_ruleF (c : HornClause (L.sum Language.order) B kk) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m'), Pos (atF k a)) :
    Pos (ruleF V c j x atF) := by
  classical
  unfold ruleF
  split
  · exact pos_falseF
  · split
    · exact pos_firedF V c _ j _ x atF hAt
    · exact pos_falseF

private theorem pos_bodyF (rules : List (HornClause (L.sum Language.order) B kk)) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m'), Pos (atF k a)) :
    Pos (bodyF V rules j x atF) := by
  refine pos_bigOr fun φ hφ => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hφ
  exact pos_ruleF V c j x atF hAt

/-- A rule fires, in the shape of `DescriptiveComplexity.stepDerives`. -/
def RuleFires (c : HornClause (L.sum Language.order) B kk) (j : B.ι)
    (x : Fin (B.arity j) → Fin S.size) (T : BAtom B (Fin S.size) → Prop) : Prop :=
  letI := ordStr V S
  ∃ a : SOAtom B kk, c.head = some a ∧ ∃ y : Fin kk → Fin S.size,
    (⟨j, x⟩ : BAtom B (Fin S.size)) = ⟨a.idx, fun q => y (a.args q)⟩ ∧ c.guard.Realize y ∧
      ∀ b ∈ c.body, T ⟨b.idx, fun q => y (b.args q)⟩

private theorem eval_firedF (c : HornClause (L.sum Language.order) B kk) (a : SOAtom B kk) {m : ℕ}
    (x : Fin (B.arity a.idx) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (T : BAtom B (Fin S.size) → Prop) (η : RelationEnv S.size ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m') (w : Fin m' → Fin S.size),
      eval (atF k a) S w η ↔ T ⟨k, w ∘ a⟩)
    (v : Fin m → Fin S.size) :
    letI := ordStr V S
    eval (firedF V c a a.idx rfl x atF) S v η ↔ ∃ y : Fin kk → Fin S.size,
      (⟨a.idx, v ∘ x⟩ : BAtom B (Fin S.size)) = ⟨a.idx, fun q => y (a.args q)⟩ ∧
        c.guard.Realize y ∧ ∀ b ∈ c.body, T ⟨b.idx, fun q => y (b.args q)⟩ := by
  let := ordStr V S
  refine (eval_exV S kk _ v η).trans (exists_congr fun y => ?_)
  have hx : (∀ q, exVal y v (exLift kk (x q)) = exVal y v (exPos (a.args q))) ↔
      (⟨a.idx, v ∘ x⟩ : BAtom B (Fin S.size)) = ⟨a.idx, fun q => y (a.args q)⟩ := by
    constructor
    · intro h
      refine congrArg (Sigma.mk a.idx) (funext fun q => ?_)
      have := h q
      rwa [exVal_lift, exVal_pos] at this
    · intro h q
      rw [exVal_lift, exVal_pos]
      have := eq_of_heq (Sigma.mk.inj h).2
      exact congrFun this q
  have hE : eval (bigAnd ((List.finRange _).map fun q => (.equal (exLift kk (x q))
      (exPos (a.args (Fin.cast (congrArg B.arity rfl) q))) : RawFormula V.σ (m + kk) ρ))) S
      (exVal y v) η ↔
      (⟨a.idx, v ∘ x⟩ : BAtom B (Fin S.size)) = ⟨a.idx, fun q => y (a.args q)⟩ := by
    rw [eval_bigAnd, ← hx]
    constructor
    · intro h q
      exact h _ (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
    · intro h φ hφ
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
      exact h q
  have hG : eval ((guardAlg V (ρ := ρ)).tr c.guard
      (Sum.elim exPos Fin.elim0 : Fin kk ⊕ Fin 0 → Fin (m + kk))).1 S (exVal y v) η ↔
      c.guard.Realize y := by
    refine ((guardSem V S η).eval_tr c.guard _ (exVal y v)).trans ?_
    exact iff_of_eq (congrArg₂ _ (funext fun q => exVal_pos y v q) (Subsingleton.elim _ _))
  have hB : eval (bigAnd (c.body.map fun b => atF b.idx
      (exPos ∘ b.args : _ → Fin (m + kk)))) S (exVal y v) η ↔
      ∀ b ∈ c.body, T ⟨b.idx, fun q => y (b.args q)⟩ := by
    rw [eval_bigAnd]
    have hb : ∀ b : SOAtom B kk, eval (atF b.idx (exPos ∘ b.args : _ → Fin (m + kk))) S
        (exVal y v) η ↔ T ⟨b.idx, fun q => y (b.args q)⟩ := by
      intro b
      refine (hAt _ _ _).trans ?_
      have : exVal y v ∘ (exPos ∘ b.args : _ → Fin (m + kk)) = fun q => y (b.args q) :=
        funext fun q => exVal_pos y v _
      rw [this]
    constructor
    · intro h b hbm
      exact (hb b).mp (h _ (List.mem_map_of_mem hbm))
    · intro h φ hφ
      obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hφ
      exact (hb b).mpr (h b hbm)
  exact and_congr (and_congr hE hG) hB |>.trans (by tauto)

private theorem eval_ruleF (c : HornClause (L.sum Language.order) B kk) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (T : BAtom B (Fin S.size) → Prop) (η : RelationEnv S.size ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m') (w : Fin m' → Fin S.size),
      eval (atF k a) S w η ↔ T ⟨k, w ∘ a⟩)
    (v : Fin m → Fin S.size) :
    eval (ruleF V c j x atF) S v η ↔ RuleFires V S c j (v ∘ x) T := by
  classical
  let := ordStr V S
  unfold RuleFires
  cases hh : c.head with
  | none =>
    simp only [ruleF, hh]
    constructor
    · exact fun h => (eval_falseF S v η h).elim
    · rintro ⟨a, ha, -⟩
      simp at ha
  | some a =>
    simp only [ruleF, hh]
    by_cases h : a.idx = j
    · subst h
      rw [dite_eq_left rfl]
      refine (eval_firedF V S c a x atF T η hAt v).trans ?_
      constructor
      · intro h'
        exact ⟨a, rfl, h'⟩
      · rintro ⟨a', ha', h'⟩
        obtain rfl := Option.some.inj ha'
        exact h'
    · rw [dite_eq_right h]
      constructor
      · exact fun h' => (eval_falseF S v η h').elim
      · rintro ⟨a', ha', y, heq, -⟩
        obtain rfl := Option.some.inj ha'
        exact (h (congrArg Sigma.fst heq).symm).elim

private theorem eval_bodyF (rules : List (HornClause (L.sum Language.order) B kk)) (j : B.ι) {m : ℕ}
    (x : Fin (B.arity j) → Fin m)
    (atF : ∀ {m' : ℕ} (k : B.ι), (Fin (B.arity k) → Fin m') → RawFormula V.σ m' ρ)
    (T : BAtom B (Fin S.size) → Prop) (η : RelationEnv S.size ρ)
    (hAt : ∀ {m' : ℕ} (k : B.ι) (a : Fin (B.arity k) → Fin m') (w : Fin m' → Fin S.size),
      eval (atF k a) S w η ↔ T ⟨k, w ∘ a⟩)
    (v : Fin m → Fin S.size) :
    letI := ordStr V S
    eval (bodyF V rules j x atF) S v η ↔ stepDerives rules T ⟨j, v ∘ x⟩ := by
  let := ordStr V S
  refine (eval_bigOr S _ v η).trans ?_
  constructor
  · rintro ⟨φ, hφ, hev⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hφ
    obtain ⟨a, ha, y, heq, hg, hb⟩ := (eval_ruleF V S c j x atF T η hAt v).mp hev
    exact ⟨c, hc, a, ha, y, heq, hg, hb⟩
  · rintro ⟨c, hc, a, ha, y, heq, hg, hb⟩
    exact ⟨_, List.mem_map_of_mem hc,
      (eval_ruleF V S c j x atF T η hAt v).mpr ⟨a, ha, y, heq, hg, hb⟩⟩

end Rules

/-! ### The nested fixed points -/

section Nest

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) {B : SOBlock} {kk : ℕ}
variable (rules : List (HornClause (L.sum Language.order) B kk))

/-- Where a variable already bound lives among the relation variables. -/
abbrev Look (B : SOBlock) (ρ : List ℕ) : Type :=
  ∀ j : B.ι, Option {r : Fin ρ.length // ρ.get r = B.arity j}

open Classical in
/-- The positions under one more binder, for the variable `j₀`. -/
noncomputable def Look.push {ρ : List ℕ} (look : Look B ρ) (j₀ : B.ι) :
    Look B (B.arity j₀ :: ρ) := fun j =>
  if h : j = j₀ then some ⟨0, by subst h; rfl⟩ else
    (look j).map fun r => ⟨r.1.succ, r.2⟩

/-- The value of a variable of the block on the arguments `args`: read if it is bound, and
otherwise the least fixed point of its rules, the others being solved recursively. -/
noncomputable def atF : ℕ → ∀ {ρ : List ℕ}, Look B ρ → (j : B.ι) → ∀ {m : ℕ},
    (Fin (B.arity j) → Fin m) → RawFormula V.σ m ρ
  | 0, _, look, j, _, args =>
    match look j with
    | some r => .variable r.1 (args ∘ Fin.cast r.2)
    | none => falseF
  | n + 1, _, look, j, m, args =>
    match look j with
    | some r => .variable r.1 (args ∘ Fin.cast r.2)
    | none => .lfp (B.arity j)
        (bodyF V rules j (Fin.castAdd m) fun k a => atF n (look.push j) k a) args

/-- **The nested formula is positive in every relation variable, and admissible.** -/
theorem atF_pos (n : ℕ) {ρ : List ℕ} (look : Look B ρ) (j : B.ι) {m : ℕ}
    (args : Fin (B.arity j) → Fin m) : Pos (atF V rules n look j args) := by
  induction n generalizing ρ m j with
  | zero =>
    simp only [atF]
    split
    · exact ⟨trivial, fun _ _ => rfl⟩
    · exact pos_falseF
  | succ n ih =>
    simp only [atF]
    split
    · exact ⟨trivial, fun _ _ => rfl⟩
    · have hb := pos_bodyF V rules j (Fin.castAdd m)
        (fun k a => atF V rules n (look.push j) k a) fun k a => ih _ _ _
      exact ⟨⟨hb.1, hb.2 0⟩, fun r => hb.2 r.succ⟩

variable (S : OrderedStructure V.σ)

/-- The operators of the rules, for Bekić's principle. -/
def ruleOp : (∀ i : B.ι, Set (Fin (B.arity i) → Fin S.size)) →
    ∀ j : B.ι, Set (Fin (B.arity j) → Fin S.size) :=
  letI := ordStr V S
  fun W j x => stepDerives rules (fun q => W q.1 q.2) ⟨j, x⟩

private theorem ruleOp_mono : Monotone (ruleOp V rules S) := by
  let := ordStr V S
  rintro W W' h j x ⟨c, hc, a, ha, y, heq, hg, hb⟩
  exact ⟨c, hc, a, ha, y, heq, hg, fun b hbm => h _ (hb b hbm)⟩

/-- The environment of relation variables agrees with `E` on the bound variables. -/
def EnvMatch {ρ : List ℕ} (look : Look B ρ) (η : RelationEnv S.size ρ)
    (E : ∀ i : B.ι, Set (Fin (B.arity i) → Fin S.size)) : Prop :=
  ∀ (j : B.ι) (r : {r : Fin ρ.length // ρ.get r = B.arity j}), look j = some r →
    ∀ a : Fin (B.arity j) → Fin S.size, η r.1 (a ∘ Fin.cast r.2) ↔ a ∈ E j

/-- The variables bound by a list of positions. -/
def boundOf {ρ : List ℕ} (look : Look B ρ) : Set B.ι := {j | (look j).isSome}

private theorem boundOf_push {ρ : List ℕ} (look : Look B ρ) (j₀ : B.ι) :
    boundOf (look.push j₀) = insert j₀ (boundOf look) := by
  classical
  ext j
  by_cases h : j = j₀
  · subst h; simp [boundOf, Look.push]
  · simp [boundOf, Look.push, h]

omit [L.IsRelational] in
theorem EnvMatch.push {ρ : List ℕ} {look : Look B ρ} {η : RelationEnv S.size ρ}
    {E : ∀ i : B.ι, Set (Fin (B.arity i) → Fin S.size)} (h : EnvMatch V S look η E) (j₀ : B.ι)
    (R : Set (Fin (B.arity j₀) → Fin S.size)) :
    EnvMatch V S (look.push j₀) (extend R η) (by classical exact Function.update E j₀ R) := by
  classical
  intro j r hr a
  by_cases hj : j = j₀
  · subst hj
    simp only [Look.push, dite_true, Option.some.injEq] at hr
    subst hr
    rw [Function.update_self]
    exact Iff.rfl
  · simp only [Look.push, hj, dite_false, Option.map_eq_some_iff] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have := h j r₀ hr₀ a
    rw [Function.update_of_ne hj]
    exact this

/-- **The nested formula evaluates to the nesting of Bekić's principle.** -/
theorem eval_atF (n : ℕ) {ρ : List ℕ} (look : Look B ρ) (η : RelationEnv S.size ρ)
    (E : ∀ i : B.ι, Set (Fin (B.arity i) → Fin S.size)) (hE : EnvMatch V S look η E) (j : B.ι)
    {m : ℕ} (args : Fin (B.arity j) → Fin m) (v : Fin m → Fin S.size) :
    eval (atF V rules n look j args) S v η ↔
      v ∘ args ∈ Bekic.solve (ruleOp V rules S) n (boundOf look) E j := by
  classical
  let := ordStr V S
  induction n generalizing ρ m j E with
  | zero =>
    cases hl : look j with
    | some r =>
      have hm : j ∈ boundOf look := by simp [boundOf, hl]
      simp only [atF, hl, Bekic.solve, hm, ite_true]
      exact hE j r hl (v ∘ args)
    | none =>
      have hm : j ∉ boundOf look := by simp [boundOf, hl]
      simp only [atF, hl, Bekic.solve, hm, ite_false]
      exact ⟨fun h => (eval_falseF S v η h).elim, fun h => h.elim⟩
  | succ n ih =>
    cases hl : look j with
    | some r =>
      have hm : j ∈ boundOf look := by simp [boundOf, hl]
      simp only [atF, hl, Bekic.solve, hm, ite_true]
      exact hE j r hl (v ∘ args)
    | none =>
      have hm : j ∉ boundOf look := by simp [boundOf, hl]
      simp only [atF, hl, Bekic.solve, hm, ite_false]
      change leastFixedPoint _ (v ∘ args) ↔ _
      have hF : (fun R => {a | eval (bodyF V rules j (Fin.castAdd m)
            fun k a => atF V rules n (look.push j) k a) S (Fin.append a v) (extend R η)}) =
          fun R => ruleOp V rules S (Bekic.solve (ruleOp V rules S) n (insert j (boundOf look))
            (Function.update E j R)) j := by
        funext R
        ext a
        have hAt : ∀ {m' : ℕ} (k : B.ι) (a' : Fin (B.arity k) → Fin m') (w : Fin m' → Fin S.size),
            eval (atF V rules n (look.push j) k a') S w (extend R η) ↔
            (fun q : BAtom B (Fin S.size) => q.2 ∈ Bekic.solve (ruleOp V rules S) n
              (insert j (boundOf look)) (Function.update E j R) q.1) ⟨k, w ∘ a'⟩ := by
          intro m' k a' w
          have := ih (look.push j) (extend R η) (Function.update E j R) (hE.push V S j R) k a' w
          rwa [boundOf_push] at this
        refine (eval_bodyF V S rules j (Fin.castAdd m) _
          (fun q : BAtom B (Fin S.size) => q.2 ∈ Bekic.solve (ruleOp V rules S) n
            (insert j (boundOf look)) (Function.update E j R) q.1) _ (fun k a' w => hAt k a' w)
          (Fin.append a v)).trans ?_
        have : Fin.append a v ∘ Fin.castAdd m = a := funext fun q => Fin.append_left a v q
        rw [this]
        exact Iff.rfl
      rw [hF]
      exact Iff.rfl

/-- **Bekić's principle, for rules**: the nested formula evaluates to the least fixed
point of the rules. -/
theorem eval_atF_top {B : SOBlock} [Finite B.ι]
    (rules : List (HornClause (L.sum Language.order) B kk)) (j : B.ι) {m : ℕ}
    (args : Fin (B.arity j) → Fin m) (v : Fin m → Fin S.size)
    (η : RelationEnv S.size []) :
    letI := ordStr V S
    eval (atF V rules (Nat.card B.ι) (fun _ => none) j args) S v η ↔
      lfpAssign rules j (v ∘ args) := by
  classical
  let := ordStr V S
  let E : ∀ i : B.ι, Set (Fin (B.arity i) → Fin S.size) := fun _ => ∅
  have hE : EnvMatch V S (fun _ => none) η E := fun _ _ h => by simp at h
  refine (eval_atF V rules S _ _ η E hE j args v).trans ?_
  have hb : boundOf (fun _ => none : Look B []) = ∅ := by ext; simp [boundOf]
  rw [hb]
  obtain ⟨hpre, hleast⟩ := Bekic.solve_spec (ruleOp_mono V rules S) (Nat.card B.ι) ∅ E
    (by rw [Set.compl_empty, Set.ncard_univ])
  have h₁ : Bekic.Pre (ruleOp V rules S) ∅ E (fun i x => lfpAssign rules i x) := by
    refine ⟨fun i hi => hi.elim, fun k _ x hx => ?_⟩
    obtain ⟨c, hc, a, ha, y, heq, hg, hb⟩ := hx
    change Derives rules ⟨k, x⟩
    rw [heq]
    exact Derives.rule hc ha hg hb
  have h₂ : ∀ q : BAtom B (Fin S.size), Derives rules q →
      q.2 ∈ Bekic.solve (ruleOp V rules S) (Nat.card B.ι) ∅ E q.1 := by
    intro q hq
    refine lfpAssign_least_of_closed
      (ρ := fun i x => x ∈ Bekic.solve (ruleOp V rules S) (Nat.card B.ι) ∅ E i) ?_ hq
    intro c hc a ha y hg hb
    exact hpre.2 a.idx (by simp) ⟨c, hc, a, ha, y, rfl, hg, hb⟩
  exact ⟨fun h => hleast _ h₁ j h, fun h => h₂ ⟨j, _⟩ h⟩

end Nest

/-! ### The whole definition -/

section Whole

variable {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L) (d : LFPDef L)

/-- The atoms of the output of a definition. -/
noncomputable def outAtom {m n : ℕ} :
    ((L.sum Language.order).sum d.B.lang).Relations n → (Fin n → Fin m) →
      {φ : RawFormula V.σ m [] // φ.Admissible}
  | .inl Q, a => ⟨(ordAtom V Q a).1, (ordAtom V Q a).2.1⟩
  | .inr Q, a => ⟨atF V d.rules (Nat.card d.B.ι) (fun _ => none) Q.1 (a ∘ Fin.cast Q.2),
      (atF_pos V d.rules _ _ _ _).1⟩

/-- The translation of the output of a definition. -/
noncomputable def outAlg : FOAlg ((L.sum Language.order).sum d.B.lang) :=
  rawAlg V.σ [] (fun φ => φ.Admissible) trivial (fun _ _ => trivial) id
    (fun h₁ h₂ => ⟨h₁, h₂⟩) id (outAtom V d)

/-- A definition of the library, as a sentence of the archive; it is false on the empty
structure. -/
noncomputable def lfpSentence : Lax.FixedPointSyntax.Sentence V.σ :=
  ⟨.conj (.exists' .truth)
      ((outAlg V d).tr d.out (Sum.elim Empty.elim Fin.elim0 : Empty ⊕ Fin 0 → Fin 0)).1,
    trivial, ((outAlg V d).tr d.out (Sum.elim Empty.elim Fin.elim0 : Empty ⊕ Fin 0 → Fin 0)).2⟩

variable (S : OrderedStructure V.σ)

private theorem outSem (η : RelationEnv S.size []) :
    letI := ordStr V S
    letI : d.B.lang.Structure (Fin S.size) := d.B.structure (lfpAssign d.rules)
    FOAlg.Sem (outAlg V d) (Fin S.size) (fun φ w => eval φ.1 S w η) := by
  let := ordStr V S
  let : d.B.lang.Structure (Fin S.size) := d.B.structure (lfpAssign d.rules)
  refine { truth := fun _ => trivial, equal := fun _ _ _ => Iff.rfl, atom := ?_,
           neg := fun _ _ => Iff.rfl, conj := fun _ _ _ => Iff.rfl, ex := ?_, ext := ?_ }
  · rintro m k (Q | Q) a w
    · exact (guardSem V S η).atom Q a w
    · exact eval_atF_top V S d.rules Q.1 _ w η
  · intro m φ w
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.cons a w, rfl, ha⟩
    · rintro ⟨w', rfl, ha⟩
      refine ⟨w' 0, ?_⟩
      have : (Fin.cons (w' 0) (w' ∘ Fin.succ) : Fin (m + 1) → _) = w' := Fin.cons_self_tail w'
      change eval φ.1 S (Fin.cons (w' 0) (w' ∘ Fin.succ)) η
      rw [this]
      exact ha
  · intro m a w
    exact ⟨Fin.cons a w, rfl, rfl⟩

/-- The sentence of a definition holds exactly where the definition does, on a nonempty
structure. -/
theorem satisfies_lfpSentence (A : PointedStructure V.σ 0) (hA : 0 < A.structureValue.size) :
    Satisfies A (lfpSentence V d) ↔
      letI := ofOrdered V A.structureValue
      d.Holds (Fin A.structureValue.size) := by
  let S := A.structureValue
  let := ofOrdered V S
  let := ordStr V S
  let : d.B.lang.Structure (Fin S.size) := d.B.structure (lfpAssign d.rules)
  have hsem := (outSem V d S (fun r => Fin.elim0 r)).eval_tr d.out
    (Sum.elim Empty.elim Fin.elim0 : Empty ⊕ Fin 0 → Fin 0) A.tuple
  have hne : eval (.exists' .truth : RawFormula V.σ 0 []) S A.tuple (fun r => Fin.elim0 r) :=
    ⟨⟨0, hA⟩, trivial⟩
  refine (and_iff_right hne).trans (hsem.trans ?_)
  refine iff_of_eq (congrArg₂ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- **Every FO(LFP) definable problem reads as an FO(LFP) definable query of the
archive.** -/
theorem lfpDefinable_imp_definable {P : DecisionProblem L} (h : LFPDefinable P) :
    Definable (toQuery V P) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨lfpSentence V d, fun A => ?_⟩
  constructor
  · rintro ⟨hA, hP⟩
    let := ofOrdered V A.structureValue
    have : Nonempty (Fin A.structureValue.size) := Fin.pos_iff_nonempty.mp hA
    exact (satisfies_lfpSentence V d A hA).mpr ((hd _).mp hP)
  · intro hA
    have hpos : 0 < A.structureValue.size := by
      obtain ⟨⟨a, -⟩, -⟩ := hA
      exact Fin.pos a
    let := ofOrdered V A.structureValue
    have : Nonempty (Fin A.structureValue.size) := Fin.pos_iff_nonempty.mp hpos
    exact ⟨hpos, (hd _).mpr ((satisfies_lfpSentence V d A hpos).mp hA)⟩

end Whole

end DescriptiveComplexity.Strings
