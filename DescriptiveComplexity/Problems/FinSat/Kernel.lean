/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Nodes
import DescriptiveComplexity.SecondOrderNew

/-!
# Reading the kernel of an `∃SO[new]` definition, position by position

The encoded sentence the RE-hardness reduction produces has one node per
*(subformula position, polarity)* of the kernel `φ`, so the defining formulas of
the interpretation have to answer two questions about a position:

* **what does the kernel say there?** –
  `DescriptiveComplexity.FinSat.kernelNode`, which reads off the constructor at
  the position together with the data the node needs: the de Bruijn levels of
  the arguments (`DescriptiveComplexity.FinSat.termLevel`), the relation symbol
  of an atom, the level a quantifier binds;
* **which positions are its children, and does the polarity flip there?** –
  `DescriptiveComplexity.FinSat.kidOf`, `some true` at the premise of an
  implication (the one place negation normal form flips a polarity), `some
  false` at its conclusion and under a quantifier, `none` elsewhere.

Both are computed by recursion on `φ`, which is what a defining formula must do:
the positions of a *variable* formula cannot be matched on directly (the
`litF`/`isClauseF` idiom of `DescriptiveComplexity.Problems.Sat.TseitinFormulas`).
Neither mentions the instance, so both are pure syntax – the reduction reads the
instance only in the *tuple* coordinates of its tags.

`DescriptiveComplexity.FinSat.nodeSize_lt_of_kidOf` is what this buys for
well-formedness: a child position carries a strictly smaller subformula, so the
parse DAG of the image descends along the order of its syntax.

Levels are `ℕ`, not `Fin` of anything: an argument at a position of context
length `m` has level below `m ≤ maxCtx φ`, and the tag `dbvar l` carries
`l : Fin (maxCtx φ)`, so comparing the two as naturals is exactly right and
needs no cast through the changing bound of a recursion.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace FinSat

/-! ### The children of a position -/

section Kids

variable {L' : Language.{0, 0}}

/-- **The children of a position**, with the polarity flip: `some true` at the
premise of an implication – where negation normal form turns `f₁ → f₂` into
`¬f₁ ∨ f₂` – `some false` at its conclusion and at the body of a quantifier,
and `none` when `q` is not a child of `p` at all. -/
def kidOf : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, Tseitin.NodeAt f m →
    ∀ {m' : ℕ}, Tseitin.NodeAt f m' → Option Bool
  | _, .falsum, _, _, _, _ => none
  | _, .equal _ _, _, _, _, _ => none
  | _, .rel _ _, _, _, _, _ => none
  | _, .imp f₁ f₂, _, p, _, q =>
      match p, q with
      | Sum.inl _, Sum.inr (Sum.inl q₁) => if Tseitin.isRootB f₁ q₁ then some true else none
      | Sum.inl _, Sum.inr (Sum.inr q₂) => if Tseitin.isRootB f₂ q₂ then some false else none
      | Sum.inr (Sum.inl p₁), Sum.inr (Sum.inl q₁) => kidOf f₁ p₁ q₁
      | Sum.inr (Sum.inr p₂), Sum.inr (Sum.inr q₂) => kidOf f₂ p₂ q₂
      | _, _ => none
  | _, .all f, _, p, _, q =>
      match p, q with
      | Sum.inl _, Sum.inr q' => if Tseitin.isRootB f q' then some false else none
      | Sum.inr p', Sum.inr q' => kidOf f p' q'
      | _, _ => none

/-! The three children the translation actually uses. -/

theorem kidOf_imp_left {n : ℕ} (f₁ f₂ : L'.BoundedFormula Empty n) :
    kidOf (f₁.imp f₂) (Sum.inl ⟨rfl⟩) (Sum.inr (Sum.inl (Tseitin.rootAt f₁))) = some true := by
  have h : Tseitin.isRootB f₁ (Tseitin.rootAt f₁) = true :=
    (Tseitin.isRootB_iff f₁ _).mpr rfl
  change (if Tseitin.isRootB f₁ (Tseitin.rootAt f₁) then some true else none) = some true
  rw [h, if_pos rfl]

theorem kidOf_imp_right {n : ℕ} (f₁ f₂ : L'.BoundedFormula Empty n) :
    kidOf (f₁.imp f₂) (Sum.inl ⟨rfl⟩) (Sum.inr (Sum.inr (Tseitin.rootAt f₂))) = some false := by
  have h : Tseitin.isRootB f₂ (Tseitin.rootAt f₂) = true :=
    (Tseitin.isRootB_iff f₂ _).mpr rfl
  change (if Tseitin.isRootB f₂ (Tseitin.rootAt f₂) then some false else none) = some false
  rw [h, if_pos rfl]

theorem kidOf_all_body {n : ℕ} (f : L'.BoundedFormula Empty (n + 1)) :
    kidOf f.all (Sum.inl ⟨rfl⟩) (Sum.inr (Tseitin.rootAt f)) = some false := by
  have h : Tseitin.isRootB f (Tseitin.rootAt f) = true :=
    (Tseitin.isRootB_iff f _).mpr rfl
  change (if Tseitin.isRootB f (Tseitin.rootAt f) then some false else none) = some false
  rw [h, if_pos rfl]

/-! The children of a position of a subformula stay inside that subformula: what
lets an induction over subformulas see all the children a node of the *whole*
kernel has. -/

theorem kidOf_imp_left_range {n : ℕ} {f₁ f₂ : L'.BoundedFormula Empty n} {m : ℕ}
    {p₁ : Tseitin.NodeAt f₁ m} {m' : ℕ} {q : Tseitin.NodeAt (f₁.imp f₂) m'} {b : Bool}
    (h : kidOf (f₁.imp f₂) (Sum.inr (Sum.inl p₁)) q = some b) :
    ∃ q₁ : Tseitin.NodeAt f₁ m', q = Sum.inr (Sum.inl q₁) := by
  obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
  · exact absurd h (by simp [kidOf])
  · exact ⟨q₁, rfl⟩
  · exact absurd h (by simp [kidOf])

theorem kidOf_imp_right_range {n : ℕ} {f₁ f₂ : L'.BoundedFormula Empty n} {m : ℕ}
    {p₂ : Tseitin.NodeAt f₂ m} {m' : ℕ} {q : Tseitin.NodeAt (f₁.imp f₂) m'} {b : Bool}
    (h : kidOf (f₁.imp f₂) (Sum.inr (Sum.inr p₂)) q = some b) :
    ∃ q₂ : Tseitin.NodeAt f₂ m', q = Sum.inr (Sum.inr q₂) := by
  obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
  · exact absurd h (by simp [kidOf])
  · exact absurd h (by simp [kidOf])
  · exact ⟨q₂, rfl⟩

theorem kidOf_all_range {n : ℕ} {f : L'.BoundedFormula Empty (n + 1)} {m : ℕ}
    {p : Tseitin.NodeAt f m} {m' : ℕ} {q : Tseitin.NodeAt f.all m'} {b : Bool}
    (h : kidOf f.all (Sum.inr p) q = some b) :
    ∃ q' : Tseitin.NodeAt f m', q = Sum.inr q' := by
  obtain ⟨⟨rfl⟩⟩ | q' := q
  · exact absurd h (by simp [kidOf])
  · exact ⟨q', rfl⟩

/-- The children of the root of an implication are the roots of its two sides,
and the children of the root of a quantifier the root of its body: what an
induction over subformulas descends along. -/
theorem kidOf_imp_root_range {n : ℕ} {f₁ f₂ : L'.BoundedFormula Empty n} {m' : ℕ}
    {q : Tseitin.NodeAt (f₁.imp f₂) m'} {b : Bool}
    (h : kidOf (f₁.imp f₂) (Sum.inl ⟨rfl⟩) q = some b) :
    (∃ q₁ : Tseitin.NodeAt f₁ m', q = Sum.inr (Sum.inl q₁)) ∨
      ∃ q₂ : Tseitin.NodeAt f₂ m', q = Sum.inr (Sum.inr q₂) := by
  obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
  · exact absurd h (by simp [kidOf])
  · exact Or.inl ⟨q₁, rfl⟩
  · exact Or.inr ⟨q₂, rfl⟩

theorem kidOf_all_root_range {n : ℕ} {f : L'.BoundedFormula Empty (n + 1)} {m' : ℕ}
    {q : Tseitin.NodeAt f.all m'} {b : Bool} (h : kidOf f.all (Sum.inl ⟨rfl⟩) q = some b) :
    ∃ q' : Tseitin.NodeAt f m', q = Sum.inr q' := by
  obtain ⟨⟨rfl⟩⟩ | q' := q
  · exact absurd h (by simp [kidOf])
  · exact ⟨q', rfl⟩

/-- **A child carries a strictly smaller subformula.** This is what makes the
parse DAG of the image acyclic, and it is all the order of the syntax is asked
to witness (`DescriptiveComplexity.FinSat.IsWF.child_lt`). -/
theorem nodeSize_lt_of_kidOf :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ} (p : Tseitin.NodeAt f m) {m' : ℕ}
      (q : Tseitin.NodeAt f m') {b : Bool}, kidOf f p q = some b →
      nodeSize f q < nodeSize f p
  | _, .falsum, _, _, _, _, _, h => by simp [kidOf] at h
  | _, .equal _ _, _, _, _, _, _, h => by simp [kidOf] at h
  | _, .rel _ _, _, _, _, _, _, h => by simp [kidOf] at h
  | _, .imp f₁ f₂, _, p, _, q, _, h => by
      obtain ⟨⟨rfl⟩⟩ | p₁ | p₂ := p <;> obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
      · exact absurd h (by simp [kidOf])
      · exact nodeSize_imp_left f₁ f₂ q₁
      · exact nodeSize_imp_right f₁ f₂ q₂
      · exact absurd h (by simp [kidOf])
      · exact nodeSize_lt_of_kidOf f₁ p₁ q₁ h
      · exact absurd h (by simp [kidOf])
      · exact absurd h (by simp [kidOf])
      · exact absurd h (by simp [kidOf])
      · exact nodeSize_lt_of_kidOf f₂ p₂ q₂ h
  | _, .all f, _, p, _, q, _, h => by
      obtain ⟨⟨rfl⟩⟩ | p' := p <;> obtain ⟨⟨rfl⟩⟩ | q' := q
      · exact absurd h (by simp [kidOf])
      · exact nodeSize_all_body f q'
      · exact absurd h (by simp [kidOf])
      · exact nodeSize_lt_of_kidOf f p' q' h

end Kids

/-! ### What the kernel says at a position -/

section Reading

variable {L : Language.{0, 0}} {B : SOBlock}

/-- The de Bruijn level a term denotes, when it is a variable at all: `none` for
a function application, which the relational milestone of the reduction excludes
and the term layer translates by its graph (the junk-value hazard). -/
def termLevel {m : ℕ} : ∀ _ : ((newLang L).sum B.lang).Term (Empty ⊕ Fin m), Option ℕ
  | .var (Sum.inl e) => e.elim
  | .var (Sum.inr j) => some (j : ℕ)
  | .func _ _ => none

/-- **What the kernel says at a position**: the constructor there, with the data
the corresponding node of the encoded sentence needs. The three kinds of atom
are separated, because the encoded sentence may name only the relation
*variables* – an atom of the instance's vocabulary, and the marker `old`, are
translated away into a disjunction over the tuples where they hold. -/
inductive KernelNode (L : Language.{0, 0}) (B : SOBlock) : Type
  /-- Falsity. -/
  | fls
  /-- An equality of two terms. -/
  | eqLit (x y : Option ℕ)
  /-- An atom of a relation variable of the block: a genuine atom of the
  encoded sentence. -/
  | blockAtom {k : ℕ} (r : B.lang.Relations k) (args : Fin k → Option ℕ)
  /-- An atom of the instance's vocabulary, which the encoded sentence must not
  mention. -/
  | inputAtom {k : ℕ} (r : L.Relations k) (args : Fin k → Option ℕ)
  /-- The marker of the original elements, likewise. -/
  | oldAtom (x : Option ℕ)
  /-- An implication. -/
  | impl
  /-- A quantifier, binding the given de Bruijn level. -/
  | quant (lvl : ℕ)

/-- Reading a position of the kernel, by recursion on the kernel: a defining
formula cannot match on the positions of a variable formula. -/
def kernelNode : ∀ {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ},
    Tseitin.NodeAt f m → KernelNode L B
  | _, .falsum, _, _ => .fls
  | _, .equal t₁ t₂, _, _ => .eqLit (termLevel t₁) (termLevel t₂)
  | _, .rel R ts, _, _ =>
      match R with
      | Sum.inl (Sum.inl r) => .inputAtom r fun j => termLevel (ts j)
      | Sum.inl (Sum.inr o) => match o with | .old => .oldAtom (termLevel (ts 0))
      | Sum.inr r => .blockAtom r fun j => termLevel (ts j)
  | _, .imp f₁ f₂, _, p =>
      match p with
      | Sum.inl _ => .impl
      | Sum.inr (Sum.inl q) => kernelNode f₁ q
      | Sum.inr (Sum.inr q) => kernelNode f₂ q
  | n, .all f, _, p =>
      match p with
      | Sum.inl _ => .quant n
      | Sum.inr q => kernelNode f q

theorem kernelNode_imp {n : ℕ} (f₁ f₂ : ((newLang L).sum B.lang).BoundedFormula Empty n) :
    kernelNode (f₁.imp f₂) (Sum.inl ⟨rfl⟩) = .impl := rfl

theorem kernelNode_all {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty (n + 1)) :
    kernelNode f.all (Sum.inl ⟨rfl⟩) = .quant n := rfl

/-! ### The atoms of the relation variables

The three accessors an atom of the encoded sentence is read through – its
relation symbol, its arity, and the de Bruijn level of each of its arguments –
together with what the shape conditions of well-formedness ask of them: an
argument sits below the arity, the arity is the one the block declares, and (in
a relational vocabulary) every position below the arity does carry a level. -/

/-- The relation variable of the block a position carries, if it carries one. -/
def symOf {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f m) : Option B.ι :=
  match kernelNode f q with
  | .blockAtom r _ => some r.1
  | _ => none

/-- The arity of the atom a position carries, `0` when it carries none. -/
def arityOf {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f m) : ℕ :=
  match kernelNode f q with
  | .blockAtom (k := k) _ _ => k
  | _ => 0

/-- The de Bruijn level of the `j`-th argument of that atom. -/
def argOf {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f m) (j : ℕ) : Option ℕ :=
  match kernelNode f q with
  | .blockAtom (k := k) _ args => if h : j < k then args ⟨j, h⟩ else none
  | _ => none

/-- **The arity is the one the block declares**: the relation symbols of the
block are its indices, tagged by their arity. -/
theorem arityOf_eq {n : ℕ} {f : ((newLang L).sum B.lang).BoundedFormula Empty n} {m : ℕ}
    {q : Tseitin.NodeAt f m} {i : B.ι} (h : symOf f q = some i) :
    arityOf f q = B.arity i := by
  rw [symOf] at h
  rw [arityOf]
  split at h
  · next r _ _ => exact (Option.some_injective _ h ▸ r.2).symm
  · exact absurd h (by simp)

/-- **The dimension is wide enough for an atom of a relation variable too**: its
arity is one of the arities occurring in the kernel. -/
theorem arityOf_le :
    ∀ {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
      (q : Tseitin.NodeAt f m), arityOf f q ≤ maxArity f
  | _, .falsum, _, _ => by simp [arityOf, kernelNode, maxArity]
  | _, .equal _ _, _, _ => by simp [arityOf, kernelNode, maxArity]
  | _, .rel R ts, _, _ => by
      obtain (r | o) | r := R
      · simp [arityOf, kernelNode, maxArity]
      · cases o
        simp [arityOf, kernelNode, maxArity]
      · simp [arityOf, kernelNode, maxArity]
  | _, .imp f₁ f₂, _, q => by
      obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
      · simp [arityOf, kernelNode, maxArity]
      · exact (arityOf_le f₁ q₁).trans (le_max_left _ _)
      · exact (arityOf_le f₂ q₂).trans (le_max_right _ _)
  | _, .all f, _, q => by
      obtain ⟨⟨rfl⟩⟩ | q' := q
      · simp [arityOf, kernelNode, maxArity]
      · exact arityOf_le f q'

/-- **An argument sits below the arity**. -/
theorem lt_arityOf_of_argOf {n : ℕ} {f : ((newLang L).sum B.lang).BoundedFormula Empty n} {m : ℕ}
    {q : Tseitin.NodeAt f m} {j l : ℕ} (h : argOf f q j = some l) : j < arityOf f q := by
  rw [argOf] at h
  rw [arityOf]
  split at h
  · by_contra hj
    rw [dif_neg hj] at h
    exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The de Bruijn level a term denotes is one of the context: in a relational
vocabulary every term is a variable. -/
theorem termLevel_some [L.IsRelational] {m : ℕ}
    (t : ((newLang L).sum B.lang).Term (Empty ⊕ Fin m)) :
    ∃ l : ℕ, termLevel t = some l ∧ l < m := by
  cases t with
  | var x => cases x with
    | inl e => exact e.elim
    | inr j => exact ⟨(j : ℕ), rfl, j.isLt⟩
  | func f _ => exact isEmptyElim f

/-- The arity of an atom the encoded sentence must not mention: one of the
input vocabulary, or the marker `old`, both of which the translation replaces by
a disjunction over the tuples where they hold. -/
def inArityOf {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f m) : ℕ :=
  match kernelNode f q with
  | .inputAtom (k := k) _ _ => k
  | .oldAtom _ => 1
  | _ => 0

/-- **The dimension of the reduction is wide enough for such an atom**: its
arity is one of the arities occurring in the kernel. -/
theorem inArityOf_le :
    ∀ {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
      (q : Tseitin.NodeAt f m), inArityOf f q ≤ maxArity f
  | _, .falsum, _, _ => by simp [inArityOf, kernelNode, maxArity]
  | _, .equal _ _, _, _ => by simp [inArityOf, kernelNode, maxArity]
  | _, .rel R ts, _, _ => by
      obtain (r | o) | r := R
      · simp [inArityOf, kernelNode, maxArity]
      · cases o
        simp [inArityOf, kernelNode, maxArity]
      · simp [inArityOf, kernelNode, maxArity]
  | _, .imp f₁ f₂, _, q => by
      obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
      · simp [inArityOf, kernelNode, maxArity]
      · exact (inArityOf_le f₁ q₁).trans (le_max_left _ _)
      · exact (inArityOf_le f₂ q₂).trans (le_max_right _ _)
  | _, .all f, _, q => by
      obtain ⟨⟨rfl⟩⟩ | q' := q
      · simp [inArityOf, kernelNode, maxArity]
      · exact inArityOf_le f q'

/-- **Every position below the arity carries a level**, in a relational
vocabulary – and the level is one of the de Bruijn levels of the kernel. This is
what lets the image of the reduction give an atom an argument at each position
of its signature (`DescriptiveComplexity.FinSat.IsWF.arg_tot`). -/
theorem argOf_some [L.IsRelational] :
    ∀ {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) {m : ℕ}
      (q : Tseitin.NodeAt f m) (j : ℕ), j < arityOf f q →
      ∃ l : ℕ, argOf f q j = some l ∧ l < Tseitin.maxCtx f
  | _, .falsum, _, _, _, h => absurd h (by simp [arityOf, kernelNode])
  | _, .equal _ _, _, _, _, h => absurd h (by simp [arityOf, kernelNode])
  | n, .rel (l := k) R ts, _, _, j, h => by
      obtain (r | o) | r := R
      · exact absurd h (by simp [arityOf, kernelNode])
      · cases o
        exact absurd h (by simp [arityOf, kernelNode])
      · have hj : j < k := h
        obtain ⟨l, hl, hlt⟩ := termLevel_some (B := B) (ts ⟨j, hj⟩)
        refine ⟨l, ?_, hlt⟩
        simp only [argOf, kernelNode]
        rw [dif_pos hj]
        exact hl
  | _, .imp f₁ f₂, _, q, j, h => by
      obtain ⟨⟨rfl⟩⟩ | q₁ | q₂ := q
      · exact absurd h (by simp [arityOf, kernelNode])
      · obtain ⟨l, hl, hlt⟩ := argOf_some f₁ q₁ j h
        exact ⟨l, hl, lt_of_lt_of_le hlt (le_max_left _ _)⟩
      · obtain ⟨l, hl, hlt⟩ := argOf_some f₂ q₂ j h
        exact ⟨l, hl, lt_of_lt_of_le hlt (le_max_right _ _)⟩
  | _, .all f, _, q, j, h => by
      obtain ⟨⟨rfl⟩⟩ | q' := q
      · exact absurd h (by simp [arityOf, kernelNode])
      · exact argOf_some f q' j h

/-- The value of a term of the kernel, when it is a variable: the context tuple
at its de Bruijn level. -/
theorem realize_of_termLevel [L.IsRelational] {M : Type} [(newLang L).Structure M] {m : ℕ}
    {t : ((newLang L).sum B.lang).Term (Empty ⊕ Fin m)} {l : ℕ}
    (h : termLevel t = some l) (hl : l < m) (w : Fin m → M) :
    (Tseitin.termToL t).realize (Sum.elim isEmptyElim w) = w ⟨l, hl⟩ := by
  cases t with
  | var x => cases x with
    | inl e => exact e.elim
    | inr j =>
      have hlj : l = (j : ℕ) := (Option.some.inj h).symm
      subst hlj
      exact congrArg w (Fin.ext rfl)
  | func f _ => exact isEmptyElim f

/-! ### Subformulas, and their positions inside the kernel

`Tseitin.Gates` – the recursion the encoded sentence has to compute – is defined
by recursion on the formula *with the node valuation restricted along each
descent*. The induction that proves the image satisfies it must therefore be
generalized over an **embedding of a subformula's positions into the kernel's**,
carrying the three facts that make the kernel's reading of an embedded position
the same as the subformula's: what the kernel says there, which positions are
its children, and – the one with content – that those children are themselves
embedded, so that a clause quantifying over *all* the children a node has in the
kernel collapses to the subformula.

All three are definitional at each of the three descents, because that is
exactly how `DescriptiveComplexity.FinSat.kernelNode` and
`DescriptiveComplexity.FinSat.kidOf` are defined; the third rests on the range
lemmas above. -/

/-- **A subformula of the kernel, with its positions embedded in the kernel's.** -/
structure SubEmb {n₀ : ℕ} (φ : ((newLang L).sum B.lang).BoundedFormula Empty n₀)
    {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) : Type where
  /-- Where a position of the subformula sits in the kernel; the context length
  is the same. -/
  emb : ∀ {m : ℕ}, Tseitin.NodeAt f m → Tseitin.NodeAt φ m
  /-- The kernel says at an embedded position what the subformula says. -/
  node : ∀ {m : ℕ} (q : Tseitin.NodeAt f m), kernelNode φ (emb q) = kernelNode f q
  /-- The child relation is the same. -/
  kid : ∀ {m : ℕ} (q : Tseitin.NodeAt f m) {m' : ℕ} (q' : Tseitin.NodeAt f m'),
    kidOf φ (emb q) (emb q') = kidOf f q q'
  /-- Every child an embedded position has in the kernel is itself embedded. -/
  kid_range : ∀ {m : ℕ} (q : Tseitin.NodeAt f m) {m' : ℕ} (r : Tseitin.NodeAt φ m') {b : Bool},
    kidOf φ (emb q) r = some b → ∃ q' : Tseitin.NodeAt f m', r = emb q'

namespace SubEmb

variable {n₀ : ℕ} {φ : ((newLang L).sum B.lang).BoundedFormula Empty n₀}

/-- The kernel is a subformula of itself. -/
def refl (φ : ((newLang L).sum B.lang).BoundedFormula Empty n₀) : SubEmb φ φ where
  emb := fun {_} q => q
  node := fun {_} _ => rfl
  kid := fun {_} _ {_} _ => rfl
  kid_range := fun {_} _ {_} r {_} _ => ⟨r, rfl⟩

variable {n : ℕ}

/-- The premise of an implication. -/
def impL {f₁ f₂ : ((newLang L).sum B.lang).BoundedFormula Empty n}
    (E : SubEmb φ (f₁.imp f₂)) : SubEmb φ f₁ where
  emb := fun {_} q => E.emb (Sum.inr (Sum.inl q))
  node := fun {_} _ => E.node _
  kid := fun {_} _ {_} _ => E.kid _ _
  kid_range := fun {_} q {_} r {_} h => by
    obtain ⟨q'', rfl⟩ := E.kid_range _ r h
    obtain ⟨q₁, rfl⟩ := kidOf_imp_left_range ((E.kid _ _).symm.trans h)
    exact ⟨q₁, rfl⟩

/-- The conclusion of an implication. -/
def impR {f₁ f₂ : ((newLang L).sum B.lang).BoundedFormula Empty n}
    (E : SubEmb φ (f₁.imp f₂)) : SubEmb φ f₂ where
  emb := fun {_} q => E.emb (Sum.inr (Sum.inr q))
  node := fun {_} _ => E.node _
  kid := fun {_} _ {_} _ => E.kid _ _
  kid_range := fun {_} q {_} r {_} h => by
    obtain ⟨q'', rfl⟩ := E.kid_range _ r h
    obtain ⟨q₂, rfl⟩ := kidOf_imp_right_range ((E.kid _ _).symm.trans h)
    exact ⟨q₂, rfl⟩

/-- The body of a quantifier. -/
def allB {f : ((newLang L).sum B.lang).BoundedFormula Empty (n + 1)}
    (E : SubEmb φ f.all) : SubEmb φ f where
  emb := fun {_} q => E.emb (Sum.inr q)
  node := fun {_} _ => E.node _
  kid := fun {_} _ {_} _ => E.kid _ _
  kid_range := fun {_} q {_} r {_} h => by
    obtain ⟨q'', rfl⟩ := E.kid_range _ r h
    obtain ⟨q', rfl⟩ := kidOf_all_range ((E.kid _ _).symm.trans h)
    exact ⟨q', rfl⟩

/-! What the children of the root of an embedded subformula are, in the kernel:
the three facts the induction over subformulas needs, one per shape. -/

variable {n : ℕ}

/-- The root of an embedded leaf – falsity, an equality or an atom – has no
children in the kernel. -/
theorem no_children {f : ((newLang L).sum B.lang).BoundedFormula Empty n} (E : SubEmb φ f)
    (hnk : ∀ {m' : ℕ} (q' : Tseitin.NodeAt f m') {b : Bool},
      kidOf f (Tseitin.rootAt f) q' ≠ some b)
    {m' : ℕ} {q : Tseitin.NodeAt φ m'} {b : Bool}
    (h : kidOf φ (E.emb (Tseitin.rootAt f)) q = some b) : False := by
  obtain ⟨q'', rfl⟩ := E.kid_range _ q h
  exact hnk q'' ((E.kid _ _).symm.trans h)

/-- The children of the root of an embedded implication are the roots of its two
sides, the premise at `some true` – where negation normal form flips the
polarity – and the conclusion at `some false`. -/
theorem imp_children {f₁ f₂ : ((newLang L).sum B.lang).BoundedFormula Empty n}
    (E : SubEmb φ (f₁.imp f₂)) {m' : ℕ} {q : Tseitin.NodeAt φ m'} {b : Bool}
    (h : kidOf φ (E.emb (Tseitin.rootAt (f₁.imp f₂))) q = some b) :
    (b = true ∧ (⟨m', q⟩ : Σ m, Tseitin.NodeAt φ m) =
        ⟨n, E.impL.emb (Tseitin.rootAt f₁)⟩) ∨
      (b = false ∧ (⟨m', q⟩ : Σ m, Tseitin.NodeAt φ m) =
        ⟨n, E.impR.emb (Tseitin.rootAt f₂)⟩) := by
  obtain ⟨q'', rfl⟩ := E.kid_range _ q h
  have h' : kidOf (f₁.imp f₂) (Tseitin.rootAt (f₁.imp f₂)) q'' = some b :=
    (E.kid _ _).symm.trans h
  rcases kidOf_imp_root_range h' with ⟨q₁, rfl⟩ | ⟨q₂, rfl⟩
  · have h'' : (if Tseitin.isRootB f₁ q₁ then some true else none) = some b := h'
    split at h''
    · next hr =>
      obtain ⟨rfl⟩ : b = true := Option.some.inj h''.symm ▸ rfl
      refine Or.inl ⟨rfl, ?_⟩
      have hsig := (Tseitin.isRootB_iff f₁ q₁).mp hr
      injection hsig with h1 h2
      subst h1
      have hq : q₁ = Tseitin.rootAt f₁ := eq_of_heq h2
      subst hq
      rfl
    · exact absurd h'' (by simp)
  · have h'' : (if Tseitin.isRootB f₂ q₂ then some false else none) = some b := h'
    split at h''
    · next hr =>
      obtain ⟨rfl⟩ : b = false := Option.some.inj h''.symm ▸ rfl
      refine Or.inr ⟨rfl, ?_⟩
      have hsig := (Tseitin.isRootB_iff f₂ q₂).mp hr
      injection hsig with h1 h2
      subst h1
      have hq : q₂ = Tseitin.rootAt f₂ := eq_of_heq h2
      subst hq
      rfl
    · exact absurd h'' (by simp)

/-- The only child of the root of an embedded quantifier is the root of its
body. -/
theorem all_children {f : ((newLang L).sum B.lang).BoundedFormula Empty (n + 1)}
    (E : SubEmb φ f.all) {m' : ℕ} {q : Tseitin.NodeAt φ m'} {b : Bool}
    (h : kidOf φ (E.emb (Tseitin.rootAt f.all)) q = some b) :
    b = false ∧ (⟨m', q⟩ : Σ m, Tseitin.NodeAt φ m) = ⟨n + 1, E.allB.emb (Tseitin.rootAt f)⟩ := by
  obtain ⟨q'', rfl⟩ := E.kid_range _ q h
  have h' : kidOf f.all (Tseitin.rootAt f.all) q'' = some b := (E.kid _ _).symm.trans h
  obtain ⟨q', rfl⟩ := kidOf_all_root_range h'
  have h'' : (if Tseitin.isRootB f q' then some false else none) = some b := h'
  split at h''
  · next hr =>
    obtain ⟨rfl⟩ : b = false := Option.some.inj h''.symm ▸ rfl
    refine ⟨rfl, ?_⟩
    have hsig := (Tseitin.isRootB_iff f q').mp hr
    injection hsig with h1 h2
    subst h1
    have hq : q' = Tseitin.rootAt f := eq_of_heq h2
    subst hq
    rfl
  · exact absurd h'' (by simp)

end SubEmb

end Reading

end FinSat

end DescriptiveComplexity
