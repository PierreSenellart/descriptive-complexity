/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat.Tseitin
import DescriptiveComplexity.OrderWalk

/-!
# Positions and tags of the FINSAT reduction

The combinatorial skeleton of the RE-hardness reduction: what the *elements*
of the encoded sentence are, and in what order they come. The reduction itself
(the defining formulas) and its correctness live in the sibling files; nothing
here mentions `DescriptiveComplexity.FINSAT`.

## Positions

The kernel `φ` of an `∃SO[new]` definition is traversed by the *subformula
positions* of `DescriptiveComplexity.Tseitin.NodeAt`, reused verbatim from the
Cook–Levin reduction – as is the whole semantic layer of
`DescriptiveComplexity.Problems.Sat.Tseitin`, whose
`DescriptiveComplexity.Tseitin.Gates` is exactly the recursion the encoded
sentence has to compute (see `TRAKHTENBROT.md` §5). What that layer does not
carry, and this file adds, is a *size*: `DescriptiveComplexity.FinSat.nodeSize`,
the size of the subformula at a position, which is what makes the parse DAG of
the image descend along the order of the syntax
(`DescriptiveComplexity.FinSat.IsWF.child_lt`).

## Tags

`DescriptiveComplexity.FinSat.Tag` is the tag type of the interpretation. Its
elements are of three kinds:

* the *syntax the kernel does not see*: the existential prefix `pre` binding one
  variable `pvar` per element of the instance, the distinctness literals `neq`
  of the diagram, and the top conjunction `body`;
* the *translation of the kernel*: one node `nd p π` per subformula position `p`
  and polarity `π` – negation normal form is a polarity flag, nothing more –
  together with, for an atom of the instance's vocabulary (or the marker `old`),
  the tuple nodes `atup p π` and their equality literals `alit p π j`, which are
  what replaces an atom the encoded sentence is not allowed to mention;
* the *vocabulary of the encoded sentence*: one symbol `sym i` per relation
  variable of the second-order block, its argument positions `apos j`, and one
  variable `dbvar l` per de Bruijn level of the kernel. There is no need for a
  variable per position: a level is bound by at most one quantifier on any
  branch, so the levels can be named once and for all.

**The order.** Well-formedness of the image demands a linear order in which
every child comes strictly earlier, so the tags are ranked
(`DescriptiveComplexity.FinSat.tagRank`) by the layer they sit in – leaves
lowest, the prefix highest, the translated kernel ordered by the size of its
subformula – and ties are broken by an arbitrary enumeration of the (finite)
tag type. The resulting key `DescriptiveComplexity.FinSat.tagKey` is injective,
so the reduction may compare two tags by trichotomy and emit `⊤`, `⊥` or a
comparison of the tuples. That last comparison,
`DescriptiveComplexity.FinSat.lexLtF` / `DescriptiveComplexity.FinSat.lexLeF`, is
the one order guard `DescriptiveComplexity.OrderWalk` does not carry: it *walks*
the lexicographic order (`succTupF`) where a reduction defining the order of its
image has to *decide* it. It is written here rather than there only so that this
work in progress adds files instead of changing one the whole library depends
on; it belongs next to `succTupF`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace FinSat

/-! ### The size of a subformula -/

section Sizes

variable {L' : Language.{0, 0}}

/-- The size of a formula: one for each of its nodes. -/
def fmlSize : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp f₁ f₂ => fmlSize f₁ + fmlSize f₂ + 1
  | _, .all f => fmlSize f + 1

theorem fmlSize_pos : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), 0 < fmlSize f
  | _, .falsum => Nat.one_pos
  | _, .equal _ _ => Nat.one_pos
  | _, .rel _ _ => Nat.one_pos
  | _, .imp _ _ => Nat.succ_pos _
  | _, .all _ => Nat.succ_pos _

/-- **The size of the subformula at a position.** It is what the order of the
syntax of the image is built from: a child position carries a strictly smaller
subformula. -/
def nodeSize : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, Tseitin.NodeAt f m → ℕ
  | _, .falsum, _, _ => 1
  | _, .equal _ _, _, _ => 1
  | _, .rel _ _, _, _ => 1
  | _, .imp f₁ f₂, _, p =>
      match p with
      | Sum.inl _ => fmlSize f₁ + fmlSize f₂ + 1
      | Sum.inr (Sum.inl q) => nodeSize f₁ q
      | Sum.inr (Sum.inr q) => nodeSize f₂ q
  | _, .all f, _, p =>
      match p with
      | Sum.inl _ => fmlSize f + 1
      | Sum.inr q => nodeSize f q

@[simp]
theorem nodeSize_rootAt :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), nodeSize f (Tseitin.rootAt f) = fmlSize f
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp _ _ => rfl
  | _, .all _ => rfl

/-- Every position of a formula carries a subformula no larger than it. -/
theorem nodeSize_le :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ} (p : Tseitin.NodeAt f m),
      nodeSize f p ≤ fmlSize f
  | _, .falsum, _, _ => le_rfl
  | _, .equal _ _, _, _ => le_rfl
  | _, .rel _ _, _, _ => le_rfl
  | _, .imp f₁ f₂, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · exact le_rfl
      · exact le_trans (nodeSize_le f₁ q) (by simp [fmlSize]; omega)
      · exact le_trans (nodeSize_le f₂ q) (by simp [fmlSize]; omega)
  | _, .all f, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · exact le_rfl
      · exact le_trans (nodeSize_le f q) (by simp [fmlSize])

/-! The three descent facts the image needs: at an implication every position
of either side is smaller than the implication itself, and at a quantifier so is
every position of the body. -/

theorem nodeSize_imp_left {n : ℕ} (f₁ f₂ : L'.BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f₁ m) :
    nodeSize (f₁.imp f₂) (Sum.inr (Sum.inl q)) < nodeSize (f₁.imp f₂) (Sum.inl ⟨rfl⟩) := by
  have h1 : nodeSize (f₁.imp f₂) (Sum.inr (Sum.inl q)) = nodeSize f₁ q := rfl
  have h2 : nodeSize (f₁.imp f₂) (Sum.inl ⟨rfl⟩) = fmlSize f₁ + fmlSize f₂ + 1 := rfl
  have h3 := nodeSize_le f₁ q
  rw [h1, h2]
  omega

theorem nodeSize_imp_right {n : ℕ} (f₁ f₂ : L'.BoundedFormula Empty n) {m : ℕ}
    (q : Tseitin.NodeAt f₂ m) :
    nodeSize (f₁.imp f₂) (Sum.inr (Sum.inr q)) < nodeSize (f₁.imp f₂) (Sum.inl ⟨rfl⟩) := by
  have h1 : nodeSize (f₁.imp f₂) (Sum.inr (Sum.inr q)) = nodeSize f₂ q := rfl
  have h2 : nodeSize (f₁.imp f₂) (Sum.inl ⟨rfl⟩) = fmlSize f₁ + fmlSize f₂ + 1 := rfl
  have h3 := nodeSize_le f₂ q
  rw [h1, h2]
  omega

theorem nodeSize_all_body {n : ℕ} (f : L'.BoundedFormula Empty (n + 1)) {m : ℕ}
    (q : Tseitin.NodeAt f m) :
    nodeSize f.all (Sum.inr q) < nodeSize f.all (Sum.inl ⟨rfl⟩) := by
  have h1 : nodeSize f.all (Sum.inr q) = nodeSize f q := rfl
  have h2 : nodeSize f.all (Sum.inl ⟨rfl⟩) = fmlSize f + 1 := rfl
  have h3 := nodeSize_le f q
  rw [h1, h2]
  omega

/-! ### The arity of the atoms -/

/-- A bound on the arities of the relation symbols occurring in a formula: the
dimension of the reduction must be large enough to hold one element per
argument of an atom of the instance's vocabulary. -/
def maxArity : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel (l := l) _ _ => l
  | _, .imp f₁ f₂ => max (maxArity f₁) (maxArity f₂)
  | _, .all f => maxArity f

end Sizes

/-! ### Comparing two tuples lexicographically -/

section LexCompare

variable {D : ℕ} {L : Language.{0, 0}} {γ : Type}

/-- The tuple held by `sel` is lexicographically strictly below the one held by
`sel'`: the two agree before some coordinate, at which the first is strictly
smaller. -/
noncomputable def lexLtF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  listSup ((List.finRange D).map fun p =>
    listInf (((List.finRange D).filter fun j => j < p).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j))) ⊓
    ltF (Term.var (sel p)) (Term.var (sel' p)))

/-- The tuple held by `sel` is lexicographically below or equal to the one held
by `sel'`. -/
noncomputable def lexLeF (sel sel' : Fin D → γ) : (L.sum Language.order).Formula γ :=
  lexLtF sel sel' ⊔
    listInf ((List.finRange D).map fun j =>
      Term.equal (Term.var (sel j)) (Term.var (sel' j)))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp]
theorem realize_lexLtF (sel sel' : Fin D → γ) :
    (lexLtF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) < toLex (v ∘ sel') := by
  rw [lexLtF, realize_listSup, lex_lt_iff]
  constructor
  · rintro ⟨φ, hφ, hr⟩
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_inf, realize_listInf, realize_ltF] at hr
    refine ⟨p, fun j hj => ?_, hr.2⟩
    have := hr.1 _ (List.mem_map.mpr
      ⟨j, List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hj⟩, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · rintro ⟨p, hag, hp⟩
    refine ⟨_, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩, ?_⟩
    rw [Formula.realize_inf, realize_listInf, realize_ltF]
    refine ⟨fun φ hφ => ?_, hp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact hag j (by simpa using (List.mem_filter.mp hj).2)

@[simp]
theorem realize_lexLeF (sel sel' : Fin D → γ) :
    (lexLeF (L := L) sel sel').Realize v ↔ toLex (v ∘ sel) ≤ toLex (v ∘ sel') := by
  rw [lexLeF, Formula.realize_sup, realize_lexLtF, realize_listInf, le_iff_lt_or_eq]
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    refine funext fun j => ?_
    have := h _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h φ hφ
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact congrFun h j

/-- The comparison is total, so a reduction may define the order of its image
by emitting `DescriptiveComplexity.FinSat.lexLeF` at equal tags. -/
theorem lexLeF_total (sel sel' : Fin D → γ) :
    (lexLeF (L := L) sel sel').Realize v ∨ (lexLeF (L := L) sel' sel).Realize v := by
  rw [realize_lexLeF, realize_lexLeF]
  exact le_total _ _

end LexCompare

/-! ### The tags -/

/-- **The tags of the FINSAT reduction.** See the module docstring for what
each of them stands for; `P` is the type of subformula positions of the kernel,
`ι` the index type of the second-order block, `c` the number of de Bruijn levels
and `d` the dimension. -/
inductive Tag (P ι : Type) (c d : ℕ) : Type
  /-- The top conjunction: the diagram of the instance and the translated
  kernel. -/
  | body
  /-- An existential of the prefix, one per element of the instance; the tuple
  holds that element. -/
  | pre
  /-- The variable that existential binds, one per element of the instance. -/
  | pvar
  /-- A distinctness literal `x_a ≠ x_b` of the diagram; the tuple holds the
  pair. -/
  | neq
  /-- The variable naming one de Bruijn level of the kernel. -/
  | dbvar (l : Fin c)
  /-- A relation symbol of the encoded sentence: one per relation variable of
  the block. -/
  | sym (i : ι)
  /-- An argument position of the relation symbols. -/
  | apos (j : Fin d)
  /-- The translation of the subformula at a position, at a polarity. -/
  | nd (p : P) (pol : Bool)
  /-- One tuple of the translation of an atom of the instance's vocabulary (or
  of the marker `old`); the tuple holds the arguments. -/
  | atup (p : P) (pol : Bool)
  /-- One equality literal inside such a tuple; the tuple holds the argument. -/
  | alit (p : P) (pol : Bool) (j : Fin d)
  deriving DecidableEq

namespace Tag

variable {P ι : Type} {c d : ℕ}

/-- The tags, mapped injectively into a sum of finite types: how they are seen
to be finitely many. -/
def toSum : Tag P ι c d →
    Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Fin c ⊕ ι ⊕ Fin d ⊕
      (P × Bool) ⊕ (P × Bool) ⊕ (P × Bool × Fin d)
  | .body => .inl ()
  | .pre => .inr (.inl ())
  | .pvar => .inr (.inr (.inl ()))
  | .neq => .inr (.inr (.inr (.inl ())))
  | .dbvar l => .inr (.inr (.inr (.inr (.inl l))))
  | .sym i => .inr (.inr (.inr (.inr (.inr (.inl i)))))
  | .apos j => .inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))
  | .nd p pol => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (p, pol))))))))
  | .atup p pol => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (p, pol)))))))))
  | .alit p pol j => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (p, pol, j)))))))))

theorem toSum_injective : Function.Injective (toSum (P := P) (ι := ι) (c := c) (d := d)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [toSum]

instance [Finite P] [Finite ι] : Finite (Tag P ι c d) :=
  Finite.of_injective _ toSum_injective

instance : Nonempty (Tag P ι c d) :=
  ⟨.body⟩

/-! ### The order of the syntax

The parse DAG of the image has to descend along the order, so the tags are
ranked by the layer they sit in. Children of a node always sit in a strictly
lower layer, except among the translated kernel, where the layer is the size of
the subformula – strictly decreasing from a position to its children by
`DescriptiveComplexity.FinSat.nodeSize_imp_left` and its two companions. -/

/-- The layer of a tag, given the size `sz` of the subformula at a position and
a bound `S` on it: the variables and symbols lowest, then the literals of an
atom, the distinctness literals, the tuple nodes, the translated kernel by
increasing subformula size, the top conjunction, and the prefix. -/
def tagRank (sz : P → ℕ) (S : ℕ) : Tag P ι c d → ℕ
  | .pvar => 0
  | .dbvar _ => 0
  | .sym _ => 0
  | .apos _ => 0
  | .alit _ _ _ => 1
  | .neq => 2
  | .atup _ _ => 3
  | .nd p _ => 4 + sz p
  | .body => 5 + S
  | .pre => 6 + S

variable [Finite P] [Finite ι]

/-- An enumeration of the tags, used only to break ties between tags of the
same layer: which of two such tags comes first is immaterial, since no two of
them are ever parent and child. -/
noncomputable def enum :
    Tag P ι c d ≃ Fin (Classical.choose (Finite.exists_equiv_fin (Tag P ι c d))) :=
  Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Tag P ι c d)))

/-- The sorting key of a tag: its layer, then its place in the enumeration. -/
noncomputable def tagKey (sz : P → ℕ) (S : ℕ) (t : Tag P ι c d) : ℕ ×ₗ ℕ :=
  toLex (tagRank sz S t, (enum t : ℕ))

theorem tagKey_injective (sz : P → ℕ) (S : ℕ) :
    Function.Injective (tagKey (P := P) (ι := ι) (c := c) (d := d) sz S) := by
  intro a b h
  have h2 : ((enum a : ℕ)) = ((enum b : ℕ)) := congrArg (fun x => (ofLex x).2) h
  exact enum.injective (Fin.val_injective h2)

/-- A tag of a lower layer comes strictly earlier: this is what makes the parse
DAG of the image descend along the order. -/
theorem tagKey_lt_of_rank_lt {sz : P → ℕ} {S : ℕ} {t t' : Tag P ι c d}
    (h : tagRank sz S t < tagRank sz S t') : tagKey sz S t < tagKey sz S t' :=
  Prod.Lex.left _ _ h

end Tag

end FinSat

end DescriptiveComplexity
