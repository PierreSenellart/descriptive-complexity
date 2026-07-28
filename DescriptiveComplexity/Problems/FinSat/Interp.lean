/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Kernel
import DescriptiveComplexity.Problems.FinSat.Defs
import DescriptiveComplexity.Ordered

/-!
# The sentence a reduction into FINSAT produces

The interpretation `σ_A` of `TRAKHTENBROT.md` §5: given the second-order block
`B` and the first-order kernel `φ` of an `∃SO[new]` definition, the encoded
sentence

```
∃x_{a₁} … ∃x_{aₙ} ( ⋀_{a ≠ b} x_a ≠ x_b  ∧  φ* )
```

defined inside an ordered input structure. Its vocabulary is `B.ι` and nothing
else: neither the symbols of the input nor the marker `old` occur in it, because
each of their atoms is translated into a disjunction over the tuples where it
holds, whose *defining formula* contains the atom – the Tseitin trick, so that
the input structure is read by the interpretation and never by the sentence.

## What each tag defines

The tags are `DescriptiveComplexity.FinSat.Tag`
(`DescriptiveComplexity.Problems.FinSat.Nodes`), the positions of the kernel are
read by `DescriptiveComplexity.FinSat.kernelNode` and
`DescriptiveComplexity.FinSat.kidOf`
(`DescriptiveComplexity.Problems.FinSat.Kernel`), and this file adds the
accessors those two are consumed through together with one defining formula per
relation symbol of `DescriptiveComplexity.FINSAT`:

* the **kinds** (`andN`, `orN`, `allN`, `exN`) are read off the constructor at a
  position and the polarity – falsity, an implication and a translated atom are
  a disjunction at polarity `true` and a conjunction at polarity `false`, an
  empty one in the case of falsity; a quantifier is `allN` at `true` and `exN`
  at `false`; and the prefix nodes are `exN`;
* `child` threads the prefix along the immediate successors of the input order,
  hands the last of them the top conjunction, gives that conjunction the
  distinctness literals and the root of the translated kernel, and inside the
  kernel follows `DescriptiveComplexity.FinSat.kidOf`. The one place the input
  structure is read is the child relation between a translated atom and its
  tuple nodes (`DescriptiveComplexity.FinSat.inAtomF`);
* `bind` binds `x_a` at the prefix node of `a` and the variable of a de Bruijn
  level at a quantifier node; `eqL`/`neqL` carry the equality literals of the
  kernel, of the diagram and of the translated atoms; `posL`/`negL`, `arg` and
  `sig` carry the atoms of the relation variables, which are the only genuine
  atoms of the sentence;
* `le` compares the tags by their key
  (`DescriptiveComplexity.FinSat.Tag.tagKey`) and, within one tag, the tuples
  lexicographically – **reversed inside the prefix**, whose chain descends as
  the input order grows;
* `root` marks the prefix node of the least element.

Every relation but `le` is guarded by canonicity
(`DescriptiveComplexity.FinSat.canonG`): a tag uses only its first
`DescriptiveComplexity.FinSat.tagDim` coordinates, and a tuple padded otherwise
is junk – an element of the encoded sentence that no node binds and no literal
reads. `le` carries no such guard, since it has to be a linear order on the
whole universe.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

section Interp

variable {L : Language.{0, 0}} (B : SOBlock) (φ : ((newLang L).sum B.lang).Sentence)

/-! ### The shape of the reduction -/

/-- The subformula positions of the kernel. -/
abbrev Pos : Type := Σ m, Tseitin.NodeAt φ m

/-- The root position of the kernel. -/
def rootPos : Pos B φ := ⟨0, Tseitin.rootAt φ⟩

/-- **The dimension of the reduction**: two coordinates for a distinctness
literal of the diagram, and one per argument of an atom of the input
vocabulary. Nothing needs a context tuple – the encoded sentence quantifies. -/
def finsatDim : ℕ := max 2 (maxArity φ)

theorem two_le_finsatDim : 2 ≤ finsatDim B φ := le_max_left _ _

theorem maxArity_le_finsatDim : maxArity φ ≤ finsatDim B φ := le_max_right _ _

/-- The first coordinate of a tuple of the reduction. -/
def c0 : Fin (finsatDim B φ) := ⟨0, lt_of_lt_of_le (by norm_num) (two_le_finsatDim B φ)⟩

/-- The second coordinate of a tuple of the reduction. -/
def c1 : Fin (finsatDim B φ) := ⟨1, lt_of_lt_of_le (by norm_num) (two_le_finsatDim B φ)⟩

/-- **The tags of the reduction.** -/
abbrev FTag : Type := Tag (Pos B φ) B.ι (Tseitin.maxCtx φ) (finsatDim B φ)

/-! ### Reading a position, through the accessors the formulas dispatch on -/

/-- The size of the subformula at a position: the layer the translation of that
position sits in, and what makes the parse DAG of the image descend. -/
def posSize (p : Pos B φ) : ℕ := nodeSize φ p.2

theorem posSize_le (p : Pos B φ) : posSize B φ p ≤ fmlSize φ := nodeSize_le φ p.2

theorem posSize_lt_of_kidOf {p q : Pos B φ} {b : Bool} (h : kidOf φ p.2 q.2 = some b) :
    posSize B φ q < posSize B φ p := nodeSize_lt_of_kidOf φ p.2 q.2 h

/-- The relation variable of a block atom at a position, if it is one. -/
def blockSym (p : Pos B φ) : Option B.ι := symOf φ p.2

/-- The de Bruijn level of the `j`-th argument of a block atom. -/
def blockArg (p : Pos B φ) (j : ℕ) : Option ℕ := argOf φ p.2 j

/-- **An argument of a block atom sits below the arity of its symbol.** -/
theorem lt_arity_of_blockArg {p : Pos B φ} {i : B.ι} {j l : ℕ}
    (hs : blockSym B φ p = some i) (ha : blockArg B φ p j = some l) : j < B.arity i :=
  arityOf_eq hs ▸ lt_arityOf_of_argOf ha

/-- **A block atom has an argument at every position of its signature**, and it
is the variable of one of the de Bruijn levels of the kernel. Relational: a
function symbol would have no level to give (`TRAKHTENBROT.md` §5). -/
theorem exists_blockArg [L.IsRelational] {p : Pos B φ} {i : B.ι} {j : ℕ}
    (hs : blockSym B φ p = some i) (hj : j < B.arity i) :
    ∃ l : ℕ, blockArg B φ p j = some l ∧ l < Tseitin.maxCtx φ :=
  argOf_some φ p.2 j (arityOf_eq hs ▸ hj)

/-- The two de Bruijn levels of an equality literal at a position. -/
def eqArgs (p : Pos B φ) : Option (ℕ × ℕ) :=
  match kernelNode φ p.2 with
  | .eqLit (some x) (some y) => some (x, y)
  | _ => none

/-- The de Bruijn level a quantifier at a position binds. -/
def qLevel (p : Pos B φ) : Option ℕ :=
  match kernelNode φ p.2 with
  | .quant l => some l
  | _ => none

/-- The arity of an atom the encoded sentence must not mention: one of the input
vocabulary, or the marker `old`. -/
def inArity (p : Pos B φ) : ℕ := inArityOf φ p.2

theorem inArity_le (p : Pos B φ) : inArity B φ p ≤ maxArity φ := inArityOf_le φ p.2

/-- The de Bruijn level of the `j`-th argument of such an atom. -/
def inArg (p : Pos B φ) (j : ℕ) : Option ℕ :=
  match kernelNode φ p.2 with
  | .inputAtom (k := k) _ args => if h : j < k then args ⟨j, h⟩ else none
  | .oldAtom x => if j = 0 then x else none
  | _ => none

/-- Whether the position carries such an atom. -/
def isInAtom (p : Pos B φ) : Prop :=
  match kernelNode φ p.2 with
  | .inputAtom _ _ => True
  | .oldAtom _ => True
  | _ => False

/-- Whether the translation turns the position into an n-ary connective: an
implication, falsity – the empty one – or an atom translated away. -/
def isConn (p : Pos B φ) : Prop :=
  match kernelNode φ p.2 with
  | .fls => True
  | .impl => True
  | .inputAtom _ _ => True
  | .oldAtom _ => True
  | _ => False

/-- The number of coordinates a tag uses; a tuple not padded with minima beyond
them is junk. -/
def tagDim : FTag B φ → ℕ
  | .body => 0
  | .pre => 1
  | .pvar => 1
  | .neq => 2
  | .dbvar _ => 0
  | .sym _ => 0
  | .apos _ => 0
  | .nd _ _ => 0
  | .atup p _ => inArity B φ p
  | .alit _ _ _ => 1

/-- **Every tag fits in the dimension**: the widest is a tuple node of a
translated atom, whose arity occurs in the kernel. -/
theorem tagDim_le_finsatDim (t : FTag B φ) : tagDim B φ t ≤ finsatDim B φ := by
  have h2 := two_le_finsatDim B φ
  cases t <;> simp only [tagDim] <;>
    first
      | omega
      | exact (inArity_le B φ _).trans (maxArity_le_finsatDim B φ)

/-- The sorting key of a tag: its layer, then its place in an arbitrary
enumeration. -/
noncomputable def fkey (t : FTag B φ) : ℕ ×ₗ ℕ :=
  Tag.tagKey (posSize B φ) (fmlSize φ) t

/-- The layer of a tag, which is what a child of a node descends by everywhere
but inside the existential prefix. -/
def frank (t : FTag B φ) : ℕ := Tag.tagRank (posSize B φ) (fmlSize φ) t

theorem fkey_lt_of_frank_lt {t t' : FTag B φ} (h : frank B φ t < frank B φ t') :
    fkey B φ t < fkey B φ t' := Tag.tagKey_lt_of_rank_lt h

/-! ### The defining formulas -/

/-- Every argument holds a canonically padded tuple of its tag's own length. -/
noncomputable def canonG {n : ℕ} (t : Fin n → FTag B φ) :
    (L.sum Language.order).Formula (Fin n × Fin (finsatDim B φ)) :=
  listInf ((List.finRange n).map fun i => canonF (tagDim B φ (t i)) fun j => (i, j))

/-- The comparison of the two tuples inside one tag: lexicographic, and
**reversed inside the prefix**, whose chain descends as the input order
grows. -/
noncomputable def tupLeF (t : FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  match t with
  | .pre => lexLeF (fun j => (1, j)) fun j => (0, j)
  | _ => lexLeF (fun j => (0, j)) fun j => (1, j)

open Classical in
/-- The order of the syntax: the tags by their key, and within one tag the
tuples by `DescriptiveComplexity.FinSat.tupLeF`. No canonicity guard: this has
to be a linear order on the whole universe, junk included. -/
noncomputable def leFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  if fkey B φ (t 0) < fkey B φ (t 1) then ⊤
  else if fkey B φ (t 1) < fkey B φ (t 0) then ⊥
  else tupLeF B φ (t 0)

/-! Every relation but `le` and the child relation is decided by the tags alone,
so its defining formula is `DescriptiveComplexity.FinSat.tagF` of a **named tag
predicate** – never an inline `match`, whose realization could only be proved by
casing on every tag combination at once. -/

open Classical in
/-- A defining formula decided by the tags: canonically padded tuples, and a
condition on the tags alone. -/
noncomputable def tagF {n : ℕ} (t : Fin n → FTag B φ) (P : Prop) :
    (L.sum Language.order).Formula (Fin n × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ (if P then ⊤ else ⊥)

/-- The tags of a conjunction node: the top conjunction of the sentence, a
connective at polarity `false`, and the tuple node of a positively translated
atom. -/
def andTag : FTag B φ → Prop
  | .body => True
  | .nd p pol => pol = false ∧ isConn B φ p
  | .atup p pol => pol = true ∧ isInAtom B φ p
  | _ => False

/-- The conjunction nodes. -/
noncomputable def andFml (t : Fin 1 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ)) :=
  tagF B φ t (andTag B φ (t 0))

/-- The tags of a disjunction node: a connective at polarity `true`, and the
tuple node of a negatively translated atom. -/
def orTag : FTag B φ → Prop
  | .nd p pol => pol = true ∧ isConn B φ p
  | .atup p pol => pol = false ∧ isInAtom B φ p
  | _ => False

/-- The disjunction nodes. -/
noncomputable def orFml (t : Fin 1 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ)) :=
  tagF B φ t (orTag B φ (t 0))

/-- The tags of a universal quantifier node: a quantifier of the kernel at
polarity `true`. -/
def allTag : FTag B φ → Prop
  | .nd p pol => pol = true ∧ (qLevel B φ p).isSome
  | _ => False

/-- The universal quantifier nodes. -/
noncomputable def allFml (t : Fin 1 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ)) :=
  tagF B φ t (allTag B φ (t 0))

/-- The tags of an existential quantifier node: the prefix, and a quantifier of
the kernel at polarity `false`. -/
def exTag : FTag B φ → Prop
  | .pre => True
  | .nd p pol => pol = false ∧ (qLevel B φ p).isSome
  | _ => False

/-- The existential quantifier nodes. -/
noncomputable def exFml (t : Fin 1 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ)) :=
  tagF B φ t (exTag B φ (t 0))

open Classical in
/-- **The one place the input structure is read**: the tuple nodes of a
translated atom are those where the atom holds, so the atom itself is a
*defining formula* and never a symbol of the encoded sentence. `old` holds of
every original element, so it filters nothing. -/
noncomputable def inAtomF (p : Pos B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  match kernelNode φ p.2 with
  | .inputAtom (k := k) r _ =>
      if h : k ≤ finsatDim B φ then
        Relations.formula (Sum.inl r) fun j => Term.var ((1 : Fin 2), Fin.castLE h j)
      else ⊥
  | .oldAtom _ => ⊤
  | _ => ⊥

open Classical in
/-- **What makes one tag a child of another**, as a named function of the two
tags: the prefix threads along the immediate successors of the input order and
hands the top conjunction to its last node, that conjunction takes the
distinctness literals and the root of the translated kernel, and inside the
kernel the child relation follows `DescriptiveComplexity.FinSat.kidOf`, with a
translated atom taking the tuple nodes where it holds and each of those its
equality literals. Named, rather than a `match` inside
`DescriptiveComplexity.FinSat.childFml`, so that its realization is one lemma
and each use cases only on the tags it needs. -/
noncomputable def childBodyF : FTag B φ → FTag B φ →
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ))
  | .pre, .pre => succF (0, c0 B φ) (1, c0 B φ)
  | .pre, .body => maxF (0, c0 B φ)
  | .body, .neq => ∼(Term.equal (Term.var (1, c0 B φ)) (Term.var (1, c1 B φ)))
  | .body, .nd p pol => if pol = true ∧ p = rootPos B φ then ⊤ else ⊥
  | .nd p pol, .nd q pol' => if kidOf φ p.2 q.2 = some (xor pol pol') then ⊤ else ⊥
  | .nd p pol, .atup q pol' => if p = q ∧ pol = pol' then inAtomF B φ p else ⊥
  | .atup p pol, .alit q pol' j =>
      if p = q ∧ pol = pol' ∧ (j : ℕ) < inArity B φ p then
        Term.equal (Term.var (0, j)) (Term.var (1, c0 B φ))
      else ⊥
  | _, _ => ⊥

/-- The child relation of the parse DAG. -/
noncomputable def childFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ childBodyF B φ (t 0) (t 1)

open Classical in
/-- **What a quantifier node binds**, as a named function of the two tags: `x_a`
at the prefix node of `a`, and the variable of its de Bruijn level at a
quantifier of the kernel. -/
noncomputable def bindBodyF : FTag B φ → FTag B φ →
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ))
  | .pre, .pvar => Term.equal (Term.var (0, c0 B φ)) (Term.var (1, c0 B φ))
  | .nd p _, .dbvar l => if qLevel B φ p = some (l : ℕ) then ⊤ else ⊥
  | _, _ => ⊥

/-- The variable a quantifier node binds. -/
noncomputable def bindFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ bindBodyF B φ (t 0) (t 1)

open Classical in
/-- **The positive equality literals**, as a named function of the three tags:
those of the kernel, and those of a positively translated atom. -/
noncomputable def eqBodyF : FTag B φ → FTag B φ → FTag B φ →
    (L.sum Language.order).Formula (Fin 3 × Fin (finsatDim B φ))
  | .nd p pol, .dbvar l₁, .dbvar l₂ =>
      if pol = true ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)) then ⊤ else ⊥
  | .alit p pol j, .dbvar l, .pvar =>
      if pol = true ∧ inArg B φ p (j : ℕ) = some (l : ℕ) then
        Term.equal (Term.var (0, c0 B φ)) (Term.var (2, c0 B φ))
      else ⊥
  | _, _, _ => ⊥

/-- The positive equality literals. -/
noncomputable def eqFml (t : Fin 3 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 3 × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ eqBodyF B φ (t 0) (t 1) (t 2)

open Classical in
/-- **The negative equality literals**, as a named function of the three tags:
those of the kernel, those of a negatively translated atom, and the distinctness
literals of the diagram. -/
noncomputable def neqBodyF : FTag B φ → FTag B φ → FTag B φ →
    (L.sum Language.order).Formula (Fin 3 × Fin (finsatDim B φ))
  | .nd p pol, .dbvar l₁, .dbvar l₂ =>
      if pol = false ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)) then ⊤ else ⊥
  | .alit p pol j, .dbvar l, .pvar =>
      if pol = false ∧ inArg B φ p (j : ℕ) = some (l : ℕ) then
        Term.equal (Term.var (0, c0 B φ)) (Term.var (2, c0 B φ))
      else ⊥
  | .neq, .pvar, .pvar =>
      Term.equal (Term.var (0, c0 B φ)) (Term.var (1, c0 B φ)) ⊓
        (Term.equal (Term.var (0, c1 B φ)) (Term.var (2, c0 B φ)) ⊓
          ∼(Term.equal (Term.var (0, c0 B φ)) (Term.var (0, c1 B φ))))
  | _, _, _ => ⊥

/-- The negative equality literals. -/
noncomputable def neqFml (t : Fin 3 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 3 × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ neqBodyF B φ (t 0) (t 1) (t 2)

/-- The tags of an atom of a relation variable at a polarity: a node of the
kernel carrying a block atom, and the symbol of its relation variable. -/
def atomTag (pol : Bool) : FTag B φ → FTag B φ → Prop
  | .nd p pol', .sym i => pol' = pol ∧ blockSym B φ p = some i
  | _, _ => False

/-- The positive atoms of the relation variables: the only genuine atoms of the
encoded sentence. -/
noncomputable def posFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  tagF B φ t (atomTag B φ true (t 0) (t 1))

/-- The negated atoms of the relation variables. -/
noncomputable def negFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  tagF B φ t (atomTag B φ false (t 0) (t 1))

/-- The de Bruijn level the argument of an atom at a given position takes, read
off the tags of the node and of the argument position. -/
def argTagLevel : FTag B φ → FTag B φ → Option ℕ
  | .nd p _, .apos j => blockArg B φ p (j : ℕ)
  | _, _ => none

/-- The tags of an argument of an atom: the node, an argument position, and the
variable of the de Bruijn level the corresponding term takes there. -/
def argTag (t t' : FTag B φ) : FTag B φ → Prop
  | .dbvar l => argTagLevel B φ t t' = some (l : ℕ)
  | _ => False

/-- The arguments of such an atom: at each argument position, the variable of
the de Bruijn level of the corresponding term. -/
noncomputable def argFml (t : Fin 3 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 3 × Fin (finsatDim B φ)) :=
  tagF B φ t (argTag B φ (t 0) (t 1) (t 2))

/-- The tags of an argument position of a relation symbol: the symbol of a
relation variable, and a position below its arity. -/
def sigTag : FTag B φ → FTag B φ → Prop
  | .sym i, .apos j => (j : ℕ) < B.arity i
  | _, _ => False

/-- The signature of the relation symbols: one argument position per argument of
the relation variable. -/
noncomputable def sigFml (t : Fin 2 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (finsatDim B φ)) :=
  tagF B φ t (sigTag B φ (t 0) (t 1))

/-- **The root of the encoded sentence**, as a named function of the tag: the
prefix node of the least element of the instance, the outermost existential. -/
noncomputable def rootBodyF : FTag B φ →
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ))
  | .pre => minF (0, c0 B φ)
  | _ => ⊥

/-- The root of the encoded sentence. -/
noncomputable def rootFml (t : Fin 1 → FTag B φ) :
    (L.sum Language.order).Formula (Fin 1 × Fin (finsatDim B φ)) :=
  canonG B φ t ⊓ rootBodyF B φ (t 0)

/-- **The interpretation**: the encoded sentence `σ_A`, defined inside an
ordered input structure. -/
noncomputable def finsatInterp :
    FOInterpretation (L.sum Language.order) Language.finsat (FTag B φ) (finsatDim B φ) where
  relFormula {n} R :=
    match n, R with
    | _, .le => leFml B φ
    | _, .andN => andFml B φ
    | _, .orN => orFml B φ
    | _, .allN => allFml B φ
    | _, .exN => exFml B φ
    | _, .child => childFml B φ
    | _, .bind => bindFml B φ
    | _, .eqL => eqFml B φ
    | _, .neqL => neqFml B φ
    | _, .posL => posFml B φ
    | _, .negL => negFml B φ
    | _, .arg => argFml B φ
    | _, .sig => sigFml B φ
    | _, .root => rootFml B φ

/-! ### The order of the image

The four order axioms of `DescriptiveComplexity.FinSat.IsWF`, which is what the
image has to satisfy before it is an encoded sentence at all. Nothing else in
this section depends on the shape of the kernel: the order is the lexicographic
product of the tag key with the tuples, and is linear because both are. -/

section Image

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The tuple comparison the order uses inside one tag, as a relation: the
lexicographic order, reversed inside the prefix. -/
def tupLe (t : FTag B φ) (u v : Fin (finsatDim B φ) → A) : Prop :=
  match t with
  | .pre => toLex v ≤ toLex u
  | _ => toLex u ≤ toLex v

omit [L.Structure A] in
theorem tupLe_refl (t : FTag B φ) (u : Fin (finsatDim B φ) → A) : tupLe B φ t u u := by
  cases t <;> simp only [tupLe] <;> exact le_rfl

omit [L.Structure A] in
theorem tupLe_total (t : FTag B φ) (u v : Fin (finsatDim B φ) → A) :
    tupLe B φ t u v ∨ tupLe B φ t v u := by
  cases t <;> simp only [tupLe] <;> exact le_total _ _

omit [L.Structure A] in
theorem tupLe_antisymm {t : FTag B φ} {u v : Fin (finsatDim B φ) → A}
    (h₁ : tupLe B φ t u v) (h₂ : tupLe B φ t v u) : u = v := by
  have h : toLex u = toLex v := by
    cases t <;> simp only [tupLe] at h₁ h₂ <;> first
      | exact le_antisymm h₁ h₂
      | exact le_antisymm h₂ h₁
  exact h

omit [L.Structure A] in
theorem tupLe_trans {t : FTag B φ} {u v w : Fin (finsatDim B φ) → A}
    (h₁ : tupLe B φ t u v) (h₂ : tupLe B φ t v w) : tupLe B φ t u w := by
  cases t <;> simp only [tupLe] at h₁ h₂ ⊢ <;> first
    | exact le_trans h₁ h₂
    | exact le_trans h₂ h₁

theorem realize_tupLeF (t : FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (tupLeF B φ t).Realize v ↔ tupLe B φ t (fun j => v (0, j)) fun j => v (1, j) := by
  cases t <;> simp only [tupLeF, tupLe, realize_lexLeF, Function.comp_def]

omit [L.Structure A] in
/-- Tags are determined by their key. -/
theorem tag_eq_of_fkey_eq {t t' : FTag B φ} (h : fkey B φ t = fkey B φ t') : t = t' :=
  Tag.tagKey_injective _ _ h

/-- Reading the order formula: the tags by their key, and within one tag the
tuples by `DescriptiveComplexity.FinSat.tupLe`. Stated at the raw type of tagged
tuples – `FOInterpretation.Map` is a non-reducible definition, so a rewrite
inside it is ill-typed at matching transparency. -/
theorem realize_leFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (leFml B φ t).Realize v ↔ fkey B φ (t 0) < fkey B φ (t 1) ∨
      (fkey B φ (t 0) = fkey B φ (t 1) ∧
        tupLe B φ (t 0) (fun j => v (0, j)) fun j => v (1, j)) := by
  classical
  simp only [leFml]
  by_cases h1 : fkey B φ (t 0) < fkey B φ (t 1)
  · rw [if_pos h1, Formula.realize_top]
    exact iff_of_true trivial (Or.inl h1)
  · rw [if_neg h1]
    by_cases h2 : fkey B φ (t 1) < fkey B φ (t 0)
    · rw [if_pos h2, Formula.realize_bot]
      refine iff_of_false not_false ?_
      rintro (hc | ⟨he, -⟩)
      · exact h1 hc
      · exact absurd he (ne_of_gt h2)
    · rw [if_neg h2]
      have hkey : fkey B φ (t 0) = fkey B φ (t 1) := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [realize_tupLeF]
      exact ⟨fun h => Or.inr ⟨hkey, h⟩, fun h => h.elim (fun hc => absurd hc h1) fun h => h.2⟩

/-- **The order of the syntax on the image.** -/
theorem ord_map_iff (x y : (finsatInterp B φ).Map A) :
    Ord x y ↔ fkey B φ x.1 < fkey B φ y.1 ∨
      (fkey B φ x.1 = fkey B φ y.1 ∧ tupLe B φ x.1 x.2 y.2) := by
  exact realize_leFml B φ (fun i => ((![x, y] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun p => ((![x, y] : Fin 2 → (finsatInterp B φ).Map A) p.1).2 p.2

/-! The first four fields of `DescriptiveComplexity.FinSat.IsWF`: the image is
linearly ordered, being the lexicographic product of the tag key with the
tuples. -/

theorem ord_map_refl (x : (finsatInterp B φ).Map A) : Ord x x :=
  (ord_map_iff B φ x x).mpr (Or.inr ⟨rfl, tupLe_refl B φ x.1 x.2⟩)

theorem ord_map_total (x y : (finsatInterp B φ).Map A) : Ord x y ∨ Ord y x := by
  rcases lt_trichotomy (fkey B φ x.1) (fkey B φ y.1) with h | h | h
  · exact Or.inl ((ord_map_iff B φ x y).mpr (Or.inl h))
  · have htag : x.1 = y.1 := tag_eq_of_fkey_eq B φ h
    rcases tupLe_total B φ x.1 x.2 y.2 with ht | ht
    · exact Or.inl ((ord_map_iff B φ x y).mpr (Or.inr ⟨h, ht⟩))
    · refine Or.inr ((ord_map_iff B φ y x).mpr (Or.inr ⟨h.symm, ?_⟩))
      rw [← htag]
      exact ht
  · exact Or.inr ((ord_map_iff B φ y x).mpr (Or.inl h))

theorem ord_map_antisymm (x y : (finsatInterp B φ).Map A) (h₁ : Ord x y) (h₂ : Ord y x) :
    x = y := by
  rcases (ord_map_iff B φ x y).mp h₁ with h | ⟨he, ht⟩
  · rcases (ord_map_iff B φ y x).mp h₂ with h' | ⟨he', -⟩
    · exact absurd h (asymm h')
    · exact absurd he' (ne_of_gt h)
  · rcases (ord_map_iff B φ y x).mp h₂ with h' | ⟨-, ht'⟩
    · exact absurd he (ne_of_gt h')
    · have htag : x.1 = y.1 := tag_eq_of_fkey_eq B φ he
      have ht'' : tupLe B φ x.1 y.2 x.2 := by rw [htag]; exact ht'
      exact Prod.ext_iff.mpr ⟨htag, tupLe_antisymm B φ ht ht''⟩

theorem ord_map_trans (x y z : (finsatInterp B φ).Map A) (h₁ : Ord x y) (h₂ : Ord y z) :
    Ord x z := by
  refine (ord_map_iff B φ x z).mpr ?_
  rcases (ord_map_iff B φ x y).mp h₁ with h | ⟨he, ht⟩ <;>
    rcases (ord_map_iff B φ y z).mp h₂ with h' | ⟨he', ht'⟩
  · exact Or.inl (lt_trans h h')
  · exact Or.inl (lt_of_lt_of_le h (le_of_eq he'))
  · exact Or.inl (lt_of_le_of_lt (le_of_eq he) h')
  · refine Or.inr ⟨he.trans he', ?_⟩
    have htag : x.1 = y.1 := tag_eq_of_fkey_eq B φ he
    have ht'' : tupLe B φ x.1 y.2 z.2 := by rw [htag]; exact ht'
    exact tupLe_trans B φ ht ht''

/-! ### Canonicity, and the shape of an atom

A tag uses only its first `DescriptiveComplexity.FinSat.tagDim` coordinates, so
the tuple of a tag of dimension zero – a node, a symbol, an argument position, a
de Bruijn variable – is forced to be all minima, hence unique. That is what
makes the shape conditions of `DescriptiveComplexity.FinSat.IsWF` hold on the
image: the objects those conditions compare are determined by their tags. -/

omit [L.Structure A] in
/-- Two tuples all of whose coordinates are minima are equal. -/
theorem eq_of_canon_zero {u v : Fin (finsatDim B φ) → A} (hu : Canon 0 u) (hv : Canon 0 v) :
    u = v :=
  funext fun j => le_antisymm (hu j (Nat.zero_le _) (v j)) (hv j (Nat.zero_le _) (u j))

theorem realize_canonG {n : ℕ} (t : Fin n → FTag B φ) (v : Fin n × Fin (finsatDim B φ) → A) :
    (canonG B φ t).Realize v ↔ ∀ i : Fin n, Canon (tagDim B φ (t i)) fun j => v (i, j) := by
  rw [canonG, realize_listInf]
  constructor
  · intro h i
    have hi := h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    rwa [realize_canonF] at hi
  · intro h ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    exact realize_canonF.mpr (h i)

/-- The realization of a defining formula that carries a formula of the input
structure: canonicity, and that formula. -/
theorem realize_canonInf {n : ℕ} (t : Fin n → FTag B φ)
    (F : (L.sum Language.order).Formula (Fin n × Fin (finsatDim B φ)))
    (v : Fin n × Fin (finsatDim B φ) → A) :
    (canonG B φ t ⊓ F).Realize v ↔
      (∀ i : Fin n, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ F.Realize v := by
  rw [Formula.realize_inf, realize_canonG]

open Classical in
/-- **The realization of a defining formula decided by the tags** – one lemma
for the eight relations that are, each of whose uses then cases only on the tags
it needs. -/
theorem realize_tagF {n : ℕ} (t : Fin n → FTag B φ) (P : Prop)
    (v : Fin n × Fin (finsatDim B φ) → A) :
    (tagF B φ t P).Realize v ↔
      (∀ i : Fin n, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ P := by
  rw [tagF, realize_canonInf]
  refine and_congr Iff.rfl ?_
  by_cases h : P
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

theorem realize_andFml (t : Fin 1 → FTag B φ) (v : Fin 1 × Fin (finsatDim B φ) → A) :
    (andFml B φ t).Realize v ↔
      (∀ i : Fin 1, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ andTag B φ (t 0) := by
  rw [andFml, realize_tagF]

theorem realize_orFml (t : Fin 1 → FTag B φ) (v : Fin 1 × Fin (finsatDim B φ) → A) :
    (orFml B φ t).Realize v ↔
      (∀ i : Fin 1, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ orTag B φ (t 0) := by
  rw [orFml, realize_tagF]

theorem realize_allFml (t : Fin 1 → FTag B φ) (v : Fin 1 × Fin (finsatDim B φ) → A) :
    (allFml B φ t).Realize v ↔
      (∀ i : Fin 1, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ allTag B φ (t 0) := by
  rw [allFml, realize_tagF]

theorem realize_exFml (t : Fin 1 → FTag B φ) (v : Fin 1 × Fin (finsatDim B φ) → A) :
    (exFml B φ t).Realize v ↔
      (∀ i : Fin 1, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ exTag B φ (t 0) := by
  rw [exFml, realize_tagF]

theorem realize_bindFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (bindFml B φ t).Realize v ↔
      (∀ i : Fin 2, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        (bindBodyF B φ (t 0) (t 1)).Realize v := by
  rw [bindFml, realize_canonInf]

theorem realize_eqFml (t : Fin 3 → FTag B φ) (v : Fin 3 × Fin (finsatDim B φ) → A) :
    (eqFml B φ t).Realize v ↔
      (∀ i : Fin 3, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        (eqBodyF B φ (t 0) (t 1) (t 2)).Realize v := by
  rw [eqFml, realize_canonInf]

theorem realize_neqFml (t : Fin 3 → FTag B φ) (v : Fin 3 × Fin (finsatDim B φ) → A) :
    (neqFml B φ t).Realize v ↔
      (∀ i : Fin 3, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        (neqBodyF B φ (t 0) (t 1) (t 2)).Realize v := by
  rw [neqFml, realize_canonInf]

theorem realize_rootFml (t : Fin 1 → FTag B φ) (v : Fin 1 × Fin (finsatDim B φ) → A) :
    (rootFml B φ t).Realize v ↔
      (∀ i : Fin 1, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        (rootBodyF B φ (t 0)).Realize v := by
  rw [rootFml, realize_canonInf]

theorem realize_posFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (posFml B φ t).Realize v ↔
      (∀ i : Fin 2, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        atomTag B φ true (t 0) (t 1) := by
  rw [posFml, realize_tagF]

theorem realize_negFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (negFml B φ t).Realize v ↔
      (∀ i : Fin 2, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        atomTag B φ false (t 0) (t 1) := by
  rw [negFml, realize_tagF]

omit [L.Structure A] [LinearOrder A] in
/-- An atom's symbol tag is determined by its node tag – so an atom of the image
carries at most one relation symbol. -/
theorem atomTag_unique {pol pol' : Bool} {t t₁ t₂ : FTag B φ}
    (h₁ : atomTag B φ pol t t₁) (h₂ : atomTag B φ pol' t t₂) :
    t₁ = t₂ ∧ tagDim B φ t₁ = 0 := by
  cases t <;> cases t₁ <;> cases t₂ <;> simp_all [atomTag, tagDim]

omit [L.Structure A] [LinearOrder A] in
/-- The tags of an atom of a relation variable, read out: a node carrying a
block atom of the kernel, and the symbol of that block variable. -/
theorem atomTag_cases {pol : Bool} {t t' : FTag B φ} (h : atomTag B φ pol t t') :
    ∃ (p : Pos B φ) (i : B.ι),
      t = Tag.nd p pol ∧ t' = Tag.sym i ∧ blockSym B φ p = some i := by
  cases t <;> cases t' <;> simp only [atomTag] at h
  obtain ⟨he, hs⟩ := h
  subst he
  exact ⟨_, _, rfl, rfl, hs⟩

omit [L.Structure A] [LinearOrder A] in
/-- Both tags of an atom use no coordinate: their tuples are all minima. -/
theorem atomTag_dims {pol : Bool} {t t' : FTag B φ} (h : atomTag B φ pol t t') :
    tagDim B φ t = 0 ∧ tagDim B φ t' = 0 := by
  obtain ⟨p, i, rfl, rfl, -⟩ := atomTag_cases B φ h
  exact ⟨rfl, rfl⟩

theorem realize_argFml (t : Fin 3 → FTag B φ) (v : Fin 3 × Fin (finsatDim B φ) → A) :
    (argFml B φ t).Realize v ↔
      (∀ i : Fin 3, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        argTag B φ (t 0) (t 1) (t 2) := by
  rw [argFml, realize_tagF]

omit [L.Structure A] [LinearOrder A] in
/-- An argument of an atom of the image is determined by the node and the
argument position – so an atom has at most one argument at each position. -/
theorem argTag_unique {t t' t₁ t₂ : FTag B φ}
    (h₁ : argTag B φ t t' t₁) (h₂ : argTag B φ t t' t₂) :
    t₁ = t₂ ∧ tagDim B φ t₁ = 0 := by
  cases t₁ <;> cases t₂ <;> simp_all [argTag, tagDim, Fin.ext_iff]

omit [L.Structure A] [LinearOrder A] in
/-- The tags of an argument of an atom, read out: the node, the argument
position and the variable are each of their own kind, and the de Bruijn level is
the one the term at that position takes. -/
theorem argTag_cases {t t' t₁ : FTag B φ} (h : argTag B φ t t' t₁) :
    ∃ (pos : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ)) (l : Fin (Tseitin.maxCtx φ)),
      t = Tag.nd pos pol ∧ t' = Tag.apos j ∧ t₁ = Tag.dbvar l ∧
        blockArg B φ pos (j : ℕ) = some (l : ℕ) := by
  cases t₁ <;> simp only [argTag] at h
  cases t <;> cases t' <;> first
    | exact ⟨_, _, _, _, rfl, rfl, rfl, h⟩
    | simp [argTagLevel] at h

omit [L.Structure A] [LinearOrder A] in
/-- All three tags of an argument use no coordinate. -/
theorem argTag_dims {t t' t₁ : FTag B φ} (h : argTag B φ t t' t₁) :
    tagDim B φ t = 0 ∧ tagDim B φ t' = 0 ∧ tagDim B φ t₁ = 0 := by
  obtain ⟨p, pol, j, l, rfl, rfl, rfl, -⟩ := argTag_cases B φ h
  exact ⟨rfl, rfl, rfl⟩

omit [L.Structure A] [LinearOrder A] in
/-- The tags of an argument position of a relation symbol, read out. -/
theorem sigTag_cases {t t' : FTag B φ} (h : sigTag B φ t t') :
    ∃ (i : B.ι) (j : Fin (finsatDim B φ)),
      t = Tag.sym i ∧ t' = Tag.apos j ∧ (j : ℕ) < B.arity i := by
  cases t <;> cases t' <;> simp only [sigTag] at h
  exact ⟨_, _, rfl, rfl, h⟩

omit [L.Structure A] [LinearOrder A] in
/-- Both tags of a signature entry use no coordinate. -/
theorem sigTag_dims {t t' : FTag B φ} (h : sigTag B φ t t') :
    tagDim B φ t = 0 ∧ tagDim B φ t' = 0 := by
  obtain ⟨i, j, rfl, rfl, -⟩ := sigTag_cases B φ h
  exact ⟨rfl, rfl⟩

/-! ### The shape conditions, read on the image

The bridge from `DescriptiveComplexity.FinSat.PosG` and its companions to the
tag predicates: `FOInterpretation.Map` is not reducible, so the arguments of the
realization lemma have to be supplied explicitly – unification will not find
them – and the tuple of a tag of dimension zero is extracted at the index it
sits at. -/

theorem shape_of_posG (g s : (finsatInterp B φ).Map A) (h : PosG g s) :
    Canon 0 g.2 ∧ Canon 0 s.2 ∧ atomTag B φ true g.1 s.1 := by
  have h' := (realize_posFml B φ
    (fun i => ((![g, s] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun p => ((![g, s] : Fin 2 → (finsatInterp B φ).Map A) p.1).2 p.2).mp h
  obtain ⟨hd, hd'⟩ := atomTag_dims B φ h'.2
  have h0 : Canon (tagDim B φ g.1) g.2 := h'.1 0
  have h1 : Canon (tagDim B φ s.1) s.2 := h'.1 1
  exact ⟨hd ▸ h0, hd' ▸ h1, h'.2⟩

theorem shape_of_negG (g s : (finsatInterp B φ).Map A) (h : NegG g s) :
    Canon 0 g.2 ∧ Canon 0 s.2 ∧ atomTag B φ false g.1 s.1 := by
  have h' := (realize_negFml B φ
    (fun i => ((![g, s] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun p => ((![g, s] : Fin 2 → (finsatInterp B φ).Map A) p.1).2 p.2).mp h
  obtain ⟨hd, hd'⟩ := atomTag_dims B φ h'.2
  have h0 : Canon (tagDim B φ g.1) g.2 := h'.1 0
  have h1 : Canon (tagDim B φ s.1) s.2 := h'.1 1
  exact ⟨hd ▸ h0, hd' ▸ h1, h'.2⟩

theorem shape_of_posOrNeg (g s : (finsatInterp B φ).Map A) (h : PosG g s ∨ NegG g s) :
    ∃ pol : Bool, Canon 0 g.2 ∧ Canon 0 s.2 ∧ atomTag B φ pol g.1 s.1 :=
  h.elim (fun h => ⟨true, shape_of_posG B φ g s h⟩) fun h => ⟨false, shape_of_negG B φ g s h⟩

theorem shape_of_argG (g p x : (finsatInterp B φ).Map A) (h : ArgG g p x) :
    Canon 0 g.2 ∧ Canon 0 p.2 ∧ Canon 0 x.2 ∧ argTag B φ g.1 p.1 x.1 := by
  have h' := (realize_argFml B φ
    (fun i => ((![g, p, x] : Fin 3 → (finsatInterp B φ).Map A) i).1)
    fun q => ((![g, p, x] : Fin 3 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
  obtain ⟨hd, hd', hd''⟩ := argTag_dims B φ h'.2
  have h0 : Canon (tagDim B φ g.1) g.2 := h'.1 0
  have h1 : Canon (tagDim B φ p.1) p.2 := h'.1 1
  have h2 : Canon (tagDim B φ x.1) x.2 := h'.1 2
  exact ⟨hd ▸ h0, hd' ▸ h1, hd'' ▸ h2, h'.2⟩

/-- **Building** an argument relation of the image: the tags say what the
argument is, and the tuples only have to be canonically padded. -/
theorem argG_of (g p x : (finsatInterp B φ).Map A)
    (hg : Canon (tagDim B φ g.1) g.2) (hp : Canon (tagDim B φ p.1) p.2)
    (hx : Canon (tagDim B φ x.1) x.2) (h : argTag B φ g.1 p.1 x.1) : ArgG g p x := by
  refine (realize_argFml B φ
    (fun i => ((![g, p, x] : Fin 3 → (finsatInterp B φ).Map A) i).1)
    fun q => ((![g, p, x] : Fin 3 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h⟩
  intro i
  fin_cases i
  · exact hg
  · exact hp
  · exact hx

theorem realize_sigFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (sigFml B φ t).Realize v ↔
      (∀ i : Fin 2, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧ sigTag B φ (t 0) (t 1) := by
  rw [sigFml, realize_tagF]

/-- **Building** a relation of the image, rather than reading one: the tags say
what holds, and the tuples only have to be canonically padded. This is the
direction `DescriptiveComplexity.FinSat.IsWF.arg_sig` and
`DescriptiveComplexity.FinSat.IsWF.arg_tot` need. -/
theorem shape_of_sigG (s p : (finsatInterp B φ).Map A) (h : SigG s p) :
    Canon 0 s.2 ∧ Canon 0 p.2 ∧ sigTag B φ s.1 p.1 := by
  have h' := (realize_sigFml B φ
    (fun i => ((![s, p] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun q => ((![s, p] : Fin 2 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
  obtain ⟨hd, hd'⟩ := sigTag_dims B φ h'.2
  have h0 : Canon (tagDim B φ s.1) s.2 := h'.1 0
  have h1 : Canon (tagDim B φ p.1) p.2 := h'.1 1
  exact ⟨hd ▸ h0, hd' ▸ h1, h'.2⟩

theorem sigG_of (s p : (finsatInterp B φ).Map A)
    (hs : Canon (tagDim B φ s.1) s.2) (hp : Canon (tagDim B φ p.1) p.2)
    (h : sigTag B φ s.1 p.1) : SigG s p := by
  refine (realize_sigFml B φ
    (fun i => ((![s, p] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun q => ((![s, p] : Fin 2 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h⟩
  intro i
  fin_cases i
  · exact hs
  · exact hp

/-- **An atom of the image carries at most one relation symbol**
(`DescriptiveComplexity.FinSat.IsWF.atom_sym`). -/
theorem atom_sym_map (g s s' : (finsatInterp B φ).Map A)
    (h : PosG g s ∨ NegG g s) (h' : PosG g s' ∨ NegG g s') : s = s' := by
  obtain ⟨_, -, hc, ha⟩ := shape_of_posOrNeg B φ g s h
  obtain ⟨_, -, hc', ha'⟩ := shape_of_posOrNeg B φ g s' h'
  exact Prod.ext_iff.mpr ⟨(atomTag_unique B φ ha ha').1, eq_of_canon_zero B φ hc hc'⟩

/-- **An atom of the image has at most one argument at each position**
(`DescriptiveComplexity.FinSat.IsWF.arg_fun`). -/
theorem arg_fun_map (g p x x' : (finsatInterp B φ).Map A)
    (h : ArgG g p x) (h' : ArgG g p x') : x = x' := by
  obtain ⟨-, -, hc, ha⟩ := shape_of_argG B φ g p x h
  obtain ⟨-, -, hc', ha'⟩ := shape_of_argG B φ g p x' h'
  exact Prod.ext_iff.mpr ⟨(argTag_unique B φ ha ha').1, eq_of_canon_zero B φ hc hc'⟩

/-- **An atom of the image only has arguments at the positions of its symbol's
signature** (`DescriptiveComplexity.FinSat.IsWF.arg_sig`): an argument of a block
atom sits below the arity of its relation variable. -/
theorem arg_sig_map (g s p x : (finsatInterp B φ).Map A)
    (h : PosG g s ∨ NegG g s) (h' : ArgG g p x) : SigG s p := by
  obtain ⟨pol, -, hcs, ha⟩ := shape_of_posOrNeg B φ g s h
  obtain ⟨-, hcp, -, harg⟩ := shape_of_argG B φ g p x h'
  obtain ⟨q, i, hg, hs, hsym⟩ := atomTag_cases B φ ha
  obtain ⟨q', pol', j, l, hg', hp, -, hbl⟩ := argTag_cases B φ harg
  have hq : (Tag.nd q pol : FTag B φ) = Tag.nd q' pol' := by rw [← hg, hg']
  injection hq with hqq hpp
  subst hqq
  refine sigG_of B φ s p ?_ ?_ ?_
  · rw [hs]; exact hcs
  · rw [hp]; exact hcp
  · rw [hs, hp]
    exact lt_arity_of_blockArg B φ hsym hbl

/-- **An atom of the image has an argument at every position of its symbol's
signature** (`DescriptiveComplexity.FinSat.IsWF.arg_tot`): the variable of the de
Bruijn level the corresponding term takes, which exists because the source
vocabulary is relational – a function symbol would have no level to give
(`TRAKHTENBROT.md` §5, the junk-value hazard). -/
theorem arg_tot_map [L.IsRelational] [Finite A] [Nonempty A]
    (g s p : (finsatInterp B φ).Map A) (h : PosG g s ∨ NegG g s) (hsig : SigG s p) :
    ∃ x, ArgG g p x := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  obtain ⟨pol, hcg, -, ha⟩ := shape_of_posOrNeg B φ g s h
  obtain ⟨-, hcp, hst⟩ := shape_of_sigG B φ s p hsig
  obtain ⟨q, i, hg, hs, hsym⟩ := atomTag_cases B φ ha
  obtain ⟨i', j, hs', hp, hj⟩ := sigTag_cases B φ hst
  have hii : (Tag.sym i : FTag B φ) = Tag.sym i' := by rw [← hs, hs']
  injection hii with hi
  subst hi
  obtain ⟨l, hbl, hlt⟩ := exists_blockArg B φ hsym hj
  refine ⟨((Tag.dbvar ⟨l, hlt⟩ : FTag B φ), (fun _ => a₀ : Fin (finsatDim B φ) → A)),
    argG_of B φ _ _ _ ?_ ?_ ?_ ?_⟩
  · rw [hg]; exact hcg
  · rw [hp]; exact hcp
  · exact fun _ _ => ha₀
  · rw [hg, hp]
    exact hbl

/-! ### The parse DAG descends along the order

The last field of `DescriptiveComplexity.FinSat.IsWF`. Everywhere but inside the
existential prefix a child sits in a strictly lower layer of the tag order, so
its key is smaller; inside the prefix the two tags are equal and the chain
descends because the tuple order is *reversed* there – which is what the prefix
case of `DescriptiveComplexity.FinSat.tupLeF` is for. -/

theorem realize_childFml (t : Fin 2 → FTag B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (childFml B φ t).Realize v ↔
      (∀ i : Fin 2, Canon (tagDim B φ (t i)) fun j => v (i, j)) ∧
        (childBodyF B φ (t 0) (t 1)).Realize v := by
  rw [childFml, realize_canonInf]

/-- **Every child edge descends**: a child either sits in a strictly lower layer
of the tag order, or the edge is one step of the existential prefix. -/
theorem childBody_tags {t t' : FTag B φ} {v : Fin 2 × Fin (finsatDim B φ) → A}
    (h : (childBodyF B φ t t').Realize v) :
    (v (0, c0 B φ) < v (1, c0 B φ) ∧ t = Tag.pre ∧ t' = Tag.pre) ∨
      frank B φ t' < frank B φ t := by
  classical
  cases t <;> cases t' <;> simp only [childBodyF, Formula.realize_bot] at h
  · right
    simp only [frank, Tag.tagRank]
    omega
  · next p pol =>
    right
    have := posSize_le B φ p
    simp only [frank, Tag.tagRank]
    omega
  · right
    simp only [frank, Tag.tagRank]
    omega
  · rw [realize_succF] at h
    exact Or.inl ⟨h.1, rfl, rfl⟩
  · next p pol q pol' =>
    split at h
    · next hk =>
      right
      have := posSize_lt_of_kidOf B φ hk
      simp only [frank, Tag.tagRank]
      omega
    · exact absurd h (by simp)
  · right
    simp only [frank, Tag.tagRank]
    omega
  · right
    simp only [frank, Tag.tagRank]
    omega

/-- **Children come strictly earlier in the order of the syntax**
(`DescriptiveComplexity.FinSat.IsWF.child_lt`), so the parse DAG of the image is
acyclic. -/
theorem child_lt_map (g c : (finsatInterp B φ).Map A) (h : ChildG g c) : OrdLt c g := by
  have h' := (realize_childFml B φ
    (fun i => ((![g, c] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    fun q => ((![g, c] : Fin 2 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
  rcases childBody_tags B φ h'.2 with ⟨hv, hg, hc⟩ | hr
  · have hg' : g.1 = Tag.pre := hg
    have hc' : c.1 = Tag.pre := hc
    have hlt : g.2 (c0 B φ) < c.2 (c0 B φ) := hv
    have hlex : toLex g.2 < toLex c.2 := by
      refine lex_lt_iff.mpr ⟨c0 B φ, fun j hj => ?_, hlt⟩
      simp [c0, Fin.lt_def] at hj
    refine ⟨(ord_map_iff B φ c g).mpr (Or.inr ⟨by rw [hg', hc'], ?_⟩), ?_⟩
    · rw [hc']
      exact le_of_lt hlex
    · intro he
      rw [he] at hlex
      exact absurd hlex (lt_irrefl _)
  · have hkey : fkey B φ c.1 < fkey B φ g.1 := fkey_lt_of_frank_lt B φ hr
    refine ⟨(ord_map_iff B φ c g).mpr (Or.inl hkey), ?_⟩
    intro he
    exact absurd (congrArg (fun z : (finsatInterp B φ).Map A => fkey B φ z.1) he)
      (ne_of_lt hkey)

/-! ### The kinds of a node of the image

Each of the four kinds, read as a condition on the tag and the tuple: the
interface the correctness proof of the reduction works against, and the reason
the defining formulas dispatch on named predicates. A junk tuple – one not
canonically padded – is a node of no kind at all, so it is read by nothing. -/

theorem andG_map_iff (x : (finsatInterp B φ).Map A) :
    AndG x ↔ Canon (tagDim B φ x.1) x.2 ∧ andTag B φ x.1 := by
  constructor
  · intro h
    have h' := (realize_andFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
    exact ⟨h'.1 0, h'.2⟩
  · intro h
    refine (realize_andFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h.2⟩
    intro i
    fin_cases i
    exact h.1

theorem orG_map_iff (x : (finsatInterp B φ).Map A) :
    OrG x ↔ Canon (tagDim B φ x.1) x.2 ∧ orTag B φ x.1 := by
  constructor
  · intro h
    have h' := (realize_orFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
    exact ⟨h'.1 0, h'.2⟩
  · intro h
    refine (realize_orFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h.2⟩
    intro i
    fin_cases i
    exact h.1

theorem allG_map_iff (x : (finsatInterp B φ).Map A) :
    AllG x ↔ Canon (tagDim B φ x.1) x.2 ∧ allTag B φ x.1 := by
  constructor
  · intro h
    have h' := (realize_allFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
    exact ⟨h'.1 0, h'.2⟩
  · intro h
    refine (realize_allFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h.2⟩
    intro i
    fin_cases i
    exact h.1

theorem exG_map_iff (x : (finsatInterp B φ).Map A) :
    ExG x ↔ Canon (tagDim B φ x.1) x.2 ∧ exTag B φ x.1 := by
  constructor
  · intro h
    have h' := (realize_exFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mp h
    exact ⟨h'.1 0, h'.2⟩
  · intro h
    refine (realize_exFml B φ
      (fun i => ((![x] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2).mpr ⟨?_, h.2⟩
    intro i
    fin_cases i
    exact h.1

/-- **The image of the reduction is a well-formed encoded sentence**: the order
of its syntax is linear, its parse DAG descends along that order, and its atoms
carry one relation symbol and exactly one argument at each position of that
symbol's signature. This is what makes `σ_A` an instance of
`DescriptiveComplexity.FINSAT` at all – junk tags are elements no node reads,
and well-formedness asks nothing of them. -/
theorem image_isWF [L.IsRelational] [Finite A] [Nonempty A] :
    IsWF ((finsatInterp B φ).Map A) where
  ord_refl := ord_map_refl B φ
  ord_trans := ord_map_trans B φ
  ord_antisymm := ord_map_antisymm B φ
  ord_total := ord_map_total B φ
  child_lt := child_lt_map B φ
  arg_fun := arg_fun_map B φ
  atom_sym := atom_sym_map B φ
  arg_sig := arg_sig_map B φ
  arg_tot := arg_tot_map B φ

end Image

end Interp

end FinSat

end DescriptiveComplexity
