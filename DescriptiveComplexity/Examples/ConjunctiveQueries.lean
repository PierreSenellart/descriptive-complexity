/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import DescriptiveComplexity.Problems.ThreeColorability

/-!
# Worked example: Boolean conjunctive queries – evaluation and containment

This file is a *tutorial*: it walks, step by step, through the addition of a
new problem domain to the library, with NP-completeness proofs at the end. It
is meant to be read top to bottom, and to serve as a template for formalizing
further problems. The domain is database theory: **Boolean conjunctive
queries** (BCQs) over relational databases with set semantics, and the two
classical decision problems about them, both NP-complete by the results of
Chandra and Merlin (STOC 1977):

* **evaluation** (combined complexity): given a query `q` and a database `D`,
  does `q` hold in `D`?
* **containment**: given queries `q₁` and `q₂`, is every database satisfying
  `q₁` also a model of `q₂`?

To keep the tutorial focused we fix the schema to a single binary relation
`E` – graph databases. This loses no complexity-theoretic generality (both
problems are already NP-hard for this schema) and everything below extends
mechanically to any fixed relational schema. A BCQ is then an expression
`∃ x₁ … xₖ, E(t₁, t₁') ∧ … ∧ E(tₘ, tₘ')` where each term `tᵢ` is a variable
or a constant.

The recipe, common to every problem in the library:

1. **Vocabulary**: a relational `FirstOrder.Language` whose finite structures
   are the problem instances.
2. **Semantics**: a `Prop`-valued predicate on structures of that vocabulary,
   total on *all* structures (also the meaningless “junk” ones), with the
   convention for junk made explicit.
3. **Invariance**: the predicate is isomorphism-invariant, giving a bundled
   `DecisionProblem`.
4. **Membership**: the problem is in NP, either by exhibiting a `Σ₁`
   second-order definition (`SigmaSODefinable`) or by an FO reduction *to* a
   problem already in NP.
5. **Hardness**: an FO reduction *from* an NP-hard problem of the catalog.
6. **Completeness**: combine 4 and 5.

Evaluation goes through steps 1–6 directly; containment then reuses
evaluation on both sides – its membership is an FO reduction *to* evaluation
and its hardness an FO reduction *from* evaluation – with the classical
Chandra–Merlin homomorphism theorem (`DescriptiveComplexity.queryContained_iff_hom`)
as the bridge. The reductions are all order-free and quantifier-free.

Main results:

* `DescriptiveComplexity.CQEval`, `DescriptiveComplexity.CQContainment`: the two bundled
  decision problems;
* `DescriptiveComplexity.queryContained_iff_hom`: the Chandra–Merlin theorem –
  containment holds iff there is a homomorphism from the right query to the
  canonical database of the left one;
* `DescriptiveComplexity.concreteQueryHolds_iff_queryHolds`: faithfulness of the
  encoding – on instances built (by `DescriptiveComplexity.queryDbStructure`) from a
  concrete query (a list of atoms) and a concrete database (a list of
  facts), the abstract semantics agrees with the textbook one;
* `DescriptiveComplexity.threeCol_fo_reduction_cqEval : ThreeCol ≤ᶠᵒ CQEval`;
* `DescriptiveComplexity.cqContainment_fo_reduction_cqEval : CQContainment ≤ᶠᵒ CQEval`;
* `DescriptiveComplexity.cqEval_fo_reduction_cqContainment : CQEval ≤ᶠᵒ CQContainment`;
* **`DescriptiveComplexity.cqEval_NP_complete`** and
  **`DescriptiveComplexity.cqContainment_NP_complete`**.
-/

/-!
### Step 1: the vocabulary of evaluation instances

An instance of the evaluation problem is a query *and* a database, packaged
in a single finite structure. Elements of the structure play three roles:
query variables (distinguished by a unary predicate), database elements, and
constants – a constant is simply an element that is not marked as a variable
and can appear both in query atoms and in database facts, which is how the
two halves of the instance share constants. Two binary relations record the
query atoms and the database facts.

As everywhere in the library, the language lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` and
`Language.order` (a project-local `Language` namespace would shadow Mathlib's
under `open Language`).
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the language of BCQ evaluation instances. -/
inductive queryDbRel : ℕ → Type
  /-- `isVar x`: the element `x` is a variable of the query. -/
  | isVar : queryDbRel 1
  /-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
  | atom : queryDbRel 2
  /-- `fact a b`: the database contains the fact `E(a, b)`. -/
  | fact : queryDbRel 2
  deriving DecidableEq

/-- The relational language of BCQ evaluation instances: a query and a
database over a shared universe, with a unary predicate singling out the
query variables and binary predicates for query atoms and database facts. -/
protected def queryDb : Language :=
  ⟨fun _ => Empty, queryDbRel⟩
  deriving IsRelational

/-- The symbol for “is a query variable”. -/
abbrev qdbIsVar : Language.queryDb.Relations 1 := .isVar

/-- The symbol for “is an atom of the query”. -/
abbrev qdbAtom : Language.queryDb.Relations 2 := .atom

/-- The symbol for “is a fact of the database”. -/
abbrev qdbFact : Language.queryDb.Relations 2 := .fact

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

/-!
### Step 2: semantics

`RelMap`-based shorthands first: they keep every later statement readable
(compare `MGAdj` and `MGMarked` in `Problems/CliqueFamily/Defs.lean`).
-/

section EvalShorthands

variable {A : Type} [Language.queryDb.Structure A]

/-- `x` is a variable of the query. -/
def QVar (x : A) : Prop := RelMap qdbIsVar ![x]

/-- `E(x, y)` is an atom of the query. -/
def QAtom (x y : A) : Prop := RelMap qdbAtom ![x, y]

/-- `E(a, b)` is a fact of the database (raw: no constraint on `a`, `b`). -/
def DbFact (x y : A) : Prop := RelMap qdbFact ![x, y]

/-- A genuine database edge: a fact both of whose endpoints are database
elements (i.e. not query variables). Facts violating this are representation
junk and are ignored by the semantics. -/
def DbEdge (x y : A) : Prop := DbFact x y ∧ ¬QVar x ∧ ¬QVar y

end EvalShorthands

/-!
The semantic core is *satisfaction of a conjunctive query in a database*,
which we set up generically – for an arbitrary “variable” predicate and
“atom” relation on the instance, and an arbitrary external database – because
the very same notion drives evaluation (database inside the instance),
containment (database quantified over), and the homomorphism criterion
(database = canonical instance). Factoring it out is what will later make the
Chandra–Merlin theorem a ten-line proof.

A *database* over a universe `U` is a binary relation `F` on `U`; since
instance elements that are not variables (the constants) must denote fixed
database values, a database additionally comes with an interpretation
`ι : A → U` of the instance elements (only its values on non-variables ever
matter). A *valuation* witnessing satisfaction maps every element to `U`,
agreeing with `ι` on non-variables and sending every atom to an `F`-edge.

Note the standing conventions of this formalization, both harmless for
instances that faithfully encode actual queries:

* valuations are total, so a query variable that occurs in no atom is mapped
  somewhere but unconstrained (in a real BCQ every variable occurs in an
  atom, so this is a junk-only concern);
* `ι` being total forces the database universe to be nonempty as soon as the
  instance is – the usual nonempty-universe convention of finite model
  theory, applied to the quantified databases as well.
-/

section GenericCore

variable {A B : Type}

/-- The conjunctive query with variables `VarP` and atoms `AtomP` (over
instance elements `A`) is satisfied in the database `F` on universe `U`,
where `ι` fixes the denotation of the non-variables: some valuation extends
`ι` and maps every atom to a database edge. -/
def SatisfiedIn (VarP : A → Prop) (AtomP : A → A → Prop) {U : Type}
    (F : U → U → Prop) (ι : A → U) : Prop :=
  ∃ v : A → U, (∀ x, ¬VarP x → v x = ι x) ∧ ∀ x y, AtomP x y → F (v x) (v y)

/-- The homomorphism condition: satisfaction in a database carried by the
instance's own universe, with every non-variable denoting itself. This single
notion underlies both problems below. -/
def CQHom (VarP : A → Prop) (AtomP FactP : A → A → Prop) : Prop :=
  SatisfiedIn VarP AtomP FactP id

/-- The homomorphism condition transports along an equivalence commuting with
the three predicates. This is the generic workhorse for the
isomorphism-invariance proofs (step 3) and for the dimension-1, single-tag
reduction of step 9. -/
theorem CQHom.of_equiv (u : A ≃ B) {VarA : A → Prop} {AtomA FactA : A → A → Prop}
    {VarB : B → Prop} {AtomB FactB : B → B → Prop}
    (hVar : ∀ a, VarA a ↔ VarB (u a))
    (hAtom : ∀ a a', AtomA a a' ↔ AtomB (u a) (u a'))
    (hFact : ∀ a a', FactA a a' ↔ FactB (u a) (u a'))
    (h : CQHom VarA AtomA FactA) : CQHom VarB AtomB FactB := by
  obtain ⟨f, hfix, hatom⟩ := h
  refine ⟨fun b => u (f (u.symm b)), fun b hb => ?_, fun b b' hbb' => ?_⟩
  · have hnv : ¬VarA (u.symm b) := fun hv => hb (by simpa using (hVar _).mp hv)
    change u (f (u.symm b)) = b
    rw [hfix _ hnv]
    simp
  · have h' : AtomA (u.symm b) (u.symm b') := by
      rw [hAtom]
      simpa using hbb'
    exact (hFact _ _).mp (hatom _ _ h')

/-- The homomorphism condition transports along an equivalence, iff
version. -/
theorem CQHom.equiv_iff (u : A ≃ B) {VarA : A → Prop} {AtomA FactA : A → A → Prop}
    {VarB : B → Prop} {AtomB FactB : B → B → Prop}
    (hVar : ∀ a, VarA a ↔ VarB (u a))
    (hAtom : ∀ a a', AtomA a a' ↔ AtomB (u a) (u a'))
    (hFact : ∀ a a', FactA a a' ↔ FactB (u a) (u a')) :
    CQHom VarA AtomA FactA ↔ CQHom VarB AtomB FactB := by
  refine ⟨CQHom.of_equiv u hVar hAtom hFact,
    CQHom.of_equiv u.symm (fun b => ?_) (fun b b' => ?_) (fun b b' => ?_)⟩
  · rw [hVar (u.symm b), Equiv.apply_symm_apply]
  · rw [hAtom (u.symm b) (u.symm b'), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rw [hFact (u.symm b) (u.symm b'), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end GenericCore

/-- The query of an evaluation instance holds in its database: there is a
valuation of the elements, fixing the non-variables, that maps every query
atom to a genuine database edge. This is the classical semantics of Boolean
conjunctive queries, phrased as a homomorphism into the database half of the
instance. -/
def QueryHolds (A : Type) [Language.queryDb.Structure A] : Prop :=
  CQHom (QVar (A := A)) (QAtom (A := A)) (DbEdge (A := A))

/-!
### Step 3: isomorphism-invariance and the bundled problem

A `DecisionProblem` requires isomorphism-invariance. Thanks to the generic
transport lemma this is a matter of transporting the three `RelMap`
predicates along the isomorphism, for which the library provides
`DescriptiveComplexity.relMap_equiv₁` / `relMap_equiv₂` (in `Interpretation.lean`).
-/

/-- Query evaluation is isomorphism-invariant. -/
theorem queryHolds_iso {A B : Type} [Language.queryDb.Structure A]
    [Language.queryDb.Structure B] (e : A ≃[Language.queryDb] B) :
    QueryHolds A ↔ QueryHolds B :=
  CQHom.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e qdbIsVar a)
    (fun a a' => relMap_equiv₂ e qdbAtom a a')
    (fun a a' => and_congr (relMap_equiv₂ e qdbFact a a')
      (and_congr (not_congr (relMap_equiv₁ e qdbIsVar a))
        (not_congr (relMap_equiv₁ e qdbIsVar a'))))

/-- **BCQ evaluation**, as a decision problem on `Language.queryDb`-structures:
does the query of the instance hold in its database? -/
def CQEval : DecisionProblem Language.queryDb where
  Holds := fun A inst => @QueryHolds A inst
  iso_invariant := fun e => queryHolds_iso e

/-!
### Step 4: membership in NP

NP is *defined* in this library as `Σ₁` second-order definability (Fagin's
theorem), so membership means exhibiting a second-order sentence: guess an
object-level certificate, check it with a first-order kernel. The natural
certificate here is (the graph of) the valuation: a single binary relation
variable `H`, with `H x u` read as “`x` is mapped to `u`”.

Since a raw guessed relation need not be the graph of a function, the kernel
does not try to say so; it checks instead that

1. every *possible image pair* of every atom is a database edge, where `u` is
   a possible image of `x` if `H x u` holds and `x` is a variable, or `u = x`
   and `x` is not (so non-variables are their own images and `H` junk on
   non-variables is ignored); and
2. every variable has at least one `H`-image;

which is equivalent to the existence of a valuation (pick any image for each
variable: by 1 *all* image choices work). This “all images are good, and
images exist” trick avoids expressing functionality in the kernel and is a
reusable pattern for guessing functions by relations.

The construction mirrors `sat_sigmaSODefinable` (`Problems/Sat.lean`): a
`SOBlock` for the quantifier block, an object-level kernel over the sum
vocabulary, one realization lemma, and the definability theorem.
-/

section Membership

/-- The single existential second-order block of the `Σ₁` definition of BCQ
evaluation: one binary relation variable, the (graph of the) valuation. -/
def cqHomBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2

/-- The symbol of the guessed-valuation relation variable. -/
def cqHomSym : cqHomBlock.lang.Relations 2 := ⟨(), rfl⟩

/-- The vocabulary of the kernel: evaluation instances together with the
guessed-valuation relation variable. -/
abbrev cqSOLang : Language := Language.queryDb.sum cqHomBlock.lang

/-- The symbol for “is a query variable” in the kernel's vocabulary. -/
abbrev kQVar : cqSOLang.Relations 1 := Sum.inl qdbIsVar

/-- The symbol for “is an atom of the query” in the kernel's vocabulary. -/
abbrev kQAtom : cqSOLang.Relations 2 := Sum.inl qdbAtom

/-- The symbol for “is a fact of the database” in the kernel's vocabulary. -/
abbrev kDbFact : cqSOLang.Relations 2 := Sum.inl qdbFact

/-- The guessed-valuation symbol in the kernel's vocabulary. -/
abbrev kHom : cqSOLang.Relations 2 := Sum.inr cqHomSym

/-- Shorthand for the `i`-th universally quantified variable of the main
kernel conjunct. -/
private def kv (i : Fin 4) : cqSOLang.Term (Empty ⊕ Fin 4) := Term.var (Sum.inr i)

/-- The kernel formula “`kv j` is a possible image of `kv i`”: an `H`-image
if `kv i` is a query variable, `kv i` itself otherwise. -/
def cqImgFormula (i j : Fin 4) : cqSOLang.Formula (Empty ⊕ Fin 4) :=
  (Relations.formula₁ kQVar (kv i) ⊓ Relations.formula₂ kHom (kv i) (kv j)) ⊔
    (∼(Relations.formula₁ kQVar (kv i)) ⊓ Term.equal (kv i) (kv j))

/-- First kernel conjunct: for all `x y u v`, if `E(x, y)` is an atom and
`u`, `v` are possible images of `x`, `y`, then `E(u, v)` is a fact between
two database elements. -/
noncomputable def cqKernelAtoms : cqSOLang.Sentence :=
  ((Relations.formula₂ kQAtom (kv 0) (kv 1) ⊓ (cqImgFormula 0 2 ⊓ cqImgFormula 1 3)).imp
    ((Relations.formula₂ kDbFact (kv 2) (kv 3) ⊓ ∼(Relations.formula₁ kQVar (kv 2))) ⊓
      ∼(Relations.formula₁ kQVar (kv 3)))).iAlls (Fin 4)

/-- Second kernel conjunct: every query variable has at least one
`H`-image. -/
noncomputable def cqKernelTotal : cqSOLang.Sentence :=
  ((Relations.formula₁ kQVar (Term.var (Sum.inr 0))).imp
    ((Relations.formula₂ kHom (Term.var (Sum.inl (Sum.inr 0)))
      (Term.var (Sum.inr ()))).iExs Unit)).iAlls (Fin 1)

/-- The first-order kernel of the `Σ₁` definition of BCQ evaluation. -/
noncomputable def cqKernel : cqSOLang.Sentence := cqKernelAtoms ⊓ cqKernelTotal

variable {A : Type} [Language.queryDb.Structure A]

/-- Lean-level counterpart of `cqImgFormula` under an assignment `ρ` of the
relation variable. -/
private def PossibleImage (ρ : cqHomBlock.Assignment A) (x u : A) : Prop :=
  (QVar x ∧ ρ () ![x, u]) ∨ (¬QVar x ∧ x = u)

/-- Realization of the kernel under an assignment of the guessed-valuation
variable, in Lean-level terms. -/
private theorem realize_cqKernel (ρ : cqHomBlock.Assignment A) :
    (@Sentence.Realize cqSOLang A
        (@sumStructure _ _ A _ (cqHomBlock.structure ρ)) cqKernel) ↔
      (∀ x y u v : A, QAtom x y → PossibleImage ρ x u → PossibleImage ρ y v →
          DbEdge u v) ∧
        ∀ x : A, QVar x → ∃ u : A, ρ () ![x, u] := by
  letI := cqHomBlock.structure ρ
  have hsub : ∀ w : Fin 2 → A,
      RelMap (L := cqSOLang) (M := A) kHom w ↔ ρ () ![w 0, w 1] := by
    intro w
    change ρ cqHomSym.1 _ ↔ _
    refine iff_of_eq (congrArg _ (funext fun j => ?_))
    fin_cases j <;> rfl
  rw [cqKernel]
  simp only [Sentence.Realize, Formula.realize_inf]
  apply and_congr
  · rw [cqKernelAtoms]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
      Formula.realize_sup, Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
      Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hsub,
      cqImgFormula, kv, PossibleImage, QAtom, QVar, DbFact, DbEdge]
    constructor
    · intro hker x y u v hxy hxu hyv
      have h := hker ![x, y, u, v]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h
      obtain ⟨⟨hf, hnu⟩, hnv⟩ := h ⟨hxy, hxu, hyv⟩
      exact ⟨hf, hnu, hnv⟩
    · rintro hsem i ⟨hxy, hxu, hyv⟩
      obtain ⟨hf, hnu, hnv⟩ := hsem (i 0) (i 1) (i 2) (i 3) hxy hxu hyv
      exact ⟨⟨hf, hnu⟩, hnv⟩
  · rw [cqKernelTotal]
    simp only [Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs,
      Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Sum.elim_inl, Language.relMap_sumInl, hsub, QVar]
    constructor
    · intro h x hx
      obtain ⟨u, hu⟩ := h (fun _ => x) hx
      exact ⟨u (), hu⟩
    · intro h i hi
      obtain ⟨u, hu⟩ := h (i 0) hi
      exact ⟨fun _ => u, hu⟩

/-- **BCQ evaluation is `Σ₁`-definable**: existentially quantify the graph of
a valuation and check it first-order. Since NP is defined as
`Σ₁`-definability, this is membership in NP. -/
theorem cqEval_sigmaSODefinable : SigmaSODefinable 1 CQEval := by
  refine ⟨[cqHomBlock], rfl, cqKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨h, hfix, hatom⟩
    refine ⟨fun _ (w : Fin 2 → A) => h (w 0) = w 1, (realize_cqKernel _).mpr ⟨?_, ?_⟩⟩
    · intro x y u v hxy hxu hyv
      simp only [PossibleImage] at hxu hyv
      have hu : u = h x := by
        rcases hxu with ⟨-, hxu⟩ | ⟨hnx, rfl⟩
        · exact hxu.symm
        · exact (hfix x hnx).symm
      have hv : v = h y := by
        rcases hyv with ⟨-, hyv⟩ | ⟨hny, rfl⟩
        · exact hyv.symm
        · exact (hfix y hny).symm
      rw [hu, hv]
      exact hatom x y hxy
    · exact fun x _ => ⟨h x, rfl⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hmain, htotal⟩ := (realize_cqKernel ρ).mp hρ
    classical
    choose f hf using htotal
    refine ⟨fun x => if hx : QVar x then f x hx else x, fun x hx => dif_neg hx,
      fun x y hxy => ?_⟩
    have himg : ∀ z : A, PossibleImage ρ z (if hz : QVar z then f z hz else z) := by
      intro z
      by_cases hz : QVar z
      · exact Or.inl ⟨hz, by rw [dif_pos hz]; exact hf z hz⟩
      · refine Or.inr ⟨hz, ?_⟩
        rw [dif_neg hz]
    exact hmain x y _ _ hxy (himg x) (himg y)

/-- BCQ evaluation is in NP. -/
theorem cqEval_mem_NP : CQEval ∈ NP := cqEval_sigmaSODefinable

end Membership

/-!
### Step 5: NP-hardness, by reduction from 3-colorability

The hardness half is a first-order reduction *from* a problem the catalog
already knows to be NP-hard. The classical source for evaluation is graph
coloring: a graph `G` is 3-colorable iff there is a graph homomorphism
`G → K₃`, i.e. iff the *canonical query of `G`* (one variable per vertex, one
atom per edge) holds in the database `K₃`.

The interpretation must build both halves of the evaluation instance from the
single input graph, which is exactly what the *tags* of the framework are
for: a tag `qvtx` for the query side (one variable per vertex) and one tag
per color for the database side. There is a wrinkle worth internalizing: the
interpreted universe is `Tag × V`, so the database side consists of `|V|`
copies of each color, not of `K₃` itself. Junk of this kind is unavoidable in
a tagged interpretation, and the standard cure is to make it *harmless*
rather than to eliminate it: connecting all copies of distinct colors yields
a complete tripartite graph, which is hom-equivalent to `K₃`, so the query
holds iff `G` is 3-colorable all the same.

All defining formulas are quantifier-free, so the reduction is a
quantifier-free (and order-free) one, the weakest reduction notion in common
use in descriptive complexity.
-/

/-- Tags for the interpretation of evaluation instances in graphs. -/
inductive ColEvalTag : Type
  /-- `(qvtx, u)`: the query variable associated to the vertex `u`. -/
  | qvtx : ColEvalTag
  /-- `(color c, u)`: a database element of color `c` (one copy per vertex;
  all copies of distinct colors are connected by facts). -/
  | color : Fin 3 → ColEvalTag
  deriving DecidableEq, Fintype, Nonempty

/-- Defining formula for `isVar`: exactly the `qvtx`-tagged elements. -/
def cevIsVarFormula : ColEvalTag → Language.graph.Formula (Fin 1 × Fin 1)
  | .qvtx => ⊤
  | .color _ => ⊥

/-- Defining formula for `atom`: the canonical query of the graph – one atom
per (directed) edge, between the corresponding query variables. -/
def cevAtomFormula : ColEvalTag → ColEvalTag → Language.graph.Formula (Fin 2 × Fin 1)
  | .qvtx, .qvtx => adj.formula₂ (Term.var (0, 0)) (Term.var (1, 0))
  | _, _ => ⊥

/-- Defining formula for `fact`: all pairs of database elements of distinct
colors (a complete tripartite graph, hom-equivalent to `K₃`). -/
def cevFactFormula : ColEvalTag → ColEvalTag → Language.graph.Formula (Fin 2 × Fin 1)
  | .color c, .color c' => if c = c' then ⊥ else ⊤
  | _, _ => ⊥

/-- The first-order interpretation producing, from a graph, the evaluation
instance “does the canonical query of the graph hold in `K₃`?”. -/
def threeColToCQEval : FOInterpretation Language.graph Language.queryDb ColEvalTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isVar => fun t => cevIsVarFormula (t 0)
    | _, .atom => fun t => cevAtomFormula (t 0) (t 1)
    | _, .fact => fun t => cevFactFormula (t 0) (t 1)

section Characterizations

variable {V : Type} [Language.graph.Structure V]

@[simp]
theorem cev_isVar_iff (t : ColEvalTag) (w : Fin 1 → V) :
    QVar (A := threeColToCQEval.Map V) (t, w) ↔ t = .qvtx := by
  change RelMap (M := threeColToCQEval.Map V) qdbIsVar ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [threeColToCQEval, cevIsVarFormula]

@[simp]
theorem cev_atom_iff (t t' : ColEvalTag) (w w' : Fin 1 → V) :
    QAtom (A := threeColToCQEval.Map V) (t, w) (t', w') ↔
      t = .qvtx ∧ t' = .qvtx ∧ RelMap adj ![w 0, w' 0] := by
  change RelMap (M := threeColToCQEval.Map V) qdbAtom ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;> simp [threeColToCQEval, cevAtomFormula, Formula.realize_rel₂]

@[simp]
theorem cev_fact_iff (t t' : ColEvalTag) (w w' : Fin 1 → V) :
    DbFact (A := threeColToCQEval.Map V) (t, w) (t', w') ↔
      ∃ c c', t = .color c ∧ t' = .color c' ∧ c ≠ c' := by
  change RelMap (M := threeColToCQEval.Map V) qdbFact ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t with
  | qvtx => cases t' <;> simp [threeColToCQEval, cevFactFormula]
  | color c =>
    cases t' with
    | qvtx => simp [threeColToCQEval, cevFactFormula]
    | color c' =>
      rcases eq_or_ne c c' with rfl | hcc
      · simp [threeColToCQEval, cevFactFormula]
      · simp [threeColToCQEval, cevFactFormula, hcc]

end Characterizations

/-- The color carried by a database-side tag (junk value `0` on the
query-side tag). -/
def tagColor : ColEvalTag → Fin 3
  | .qvtx => 0
  | .color c => c

/-- Correctness of the reduction: a graph is 3-colorable iff the canonical
query holds in the interpreted database. -/
theorem threeColorable_iff_map_queryHolds (V : Type) [Language.graph.Structure V] :
    ThreeColorable V ↔ QueryHolds (threeColToCQEval.Map V) := by
  constructor
  · -- a proper coloring induces a valuation: send each vertex variable to a
    -- database element of its color
    rintro ⟨col, hcol⟩
    refine ⟨fun p => match p with
      | (.qvtx, w) => (.color (col (w 0)), w)
      | (.color c, w) => (.color c, w), fun p hp => ?_, fun p q hpq => ?_⟩
    · obtain ⟨t, w⟩ := p
      cases t with
      | qvtx => exact absurd (by simp) hp
      | color c => rfl
    · obtain ⟨t, w⟩ := p
      obtain ⟨t', w'⟩ := q
      rw [cev_atom_iff] at hpq
      obtain ⟨rfl, rfl, hadj⟩ := hpq
      change DbEdge (A := threeColToCQEval.Map V) (ColEvalTag.color (col (w 0)), w)
        (ColEvalTag.color (col (w' 0)), w')
      exact ⟨(cev_fact_iff _ _ _ _).mpr ⟨_, _, rfl, rfl, hcol _ _ hadj⟩, by simp, by simp⟩
  · -- a valuation induces a coloring: read off the color of each vertex's
    -- image (edges force the image onto the database side, where the tag
    -- carries a color)
    rintro ⟨h, hfix, hatom⟩
    refine ⟨fun u => tagColor (h (ColEvalTag.qvtx, fun _ => u)).1, fun x y hadj => ?_⟩
    have hq : QAtom (A := threeColToCQEval.Map V) (ColEvalTag.qvtx, fun _ => x)
        (ColEvalTag.qvtx, fun _ => y) := by
      rw [cev_atom_iff]
      exact ⟨rfl, rfl, hadj⟩
    obtain ⟨hfact, -, -⟩ := hatom _ _ hq
    obtain ⟨c, c', hc, hc', hcc⟩ := (cev_fact_iff _ _ _ _).mp hfact
    intro hxy
    refine hcc ?_
    have h1 : tagColor (h (ColEvalTag.qvtx, fun _ => x)).1 = c := by
      rw [hc]
      rfl
    have h2 : tagColor (h (ColEvalTag.qvtx, fun _ => y)).1 = c' := by
      rw [hc']
      rfl
    rw [← h1, ← h2]
    exact hxy

/-- **3-colorability FO-reduces to BCQ evaluation** – the `fo_reduction`
theorem for the hardness half. -/
def threeCol_fo_reduction_cqEval : ThreeCol ≤ᶠᵒ CQEval where
  Tag := ColEvalTag
  dim := 1
  toInterpretation := threeColToCQEval
  correct A _ _ := threeColorable_iff_map_queryHolds A

/-- The reduction is even quantifier-free. -/
theorem threeColToCQEval_isQuantifierFree : threeColToCQEval.IsQuantifierFree := by
  intro n R t
  cases R with
  | isVar =>
    change (cevIsVarFormula (t 0)).IsQF
    cases t 0 with
    | qvtx => exact isQF_bot.imp isQF_bot
    | color c => exact isQF_bot
  | atom =>
    change (cevAtomFormula (t 0) (t 1)).IsQF
    cases t 0 <;> cases t 1 <;>
      first
        | exact isQF_bot
        | exact (IsAtomic.rel _ _).isQF
  | fact =>
    change (cevFactFormula (t 0) (t 1)).IsQF
    cases t 0 <;> cases t 1 <;> try exact isQF_bot
    simp only [cevFactFormula]
    split
    · exact isQF_bot
    · exact isQF_bot.imp isQF_bot

/-!
### Step 6: completeness of evaluation

Membership and hardness combine into the completeness theorem. This is the
end of the recipe for a single problem; the remaining steps treat containment
by *reusing* evaluation instead of repeating steps 4 and 5 from scratch.
-/

/-- BCQ evaluation is NP-hard: 3-colorability, which is NP-hard, FO-reduces
to it. -/
theorem cqEval_NP_hard : NP.Hard CQEval :=
  NP.hard_of_foReduction threeCol_fo_reduction_cqEval threeCol_NP_hard

/-- **BCQ evaluation (combined complexity) is NP-complete** (Chandra–Merlin).
-/
theorem cqEval_NP_complete : NP.Complete CQEval :=
  ⟨cqEval_mem_NP, cqEval_NP_hard⟩

/-!
### Interlude: tying the encoding to concrete queries and databases

So far “a query and a database” has meant “a `Language.queryDb`-structure”,
and one should not take on faith that this abstraction encodes the real
thing. This interlude closes the loop: a *concrete* Boolean conjunctive
query over variables `V` and constants `C` is a list of atoms – each
argument a variable or a constant, i.e. an element of `V ⊕ C` – and a
concrete graph database is a list of facts over the constants. Their
textbook semantics (`DescriptiveComplexity.ConcreteQueryHolds`) is: some assignment of
the variables to constants sends every atom to a fact.

Any such pair is encoded as a structure on the universe `V ⊕ C`
(`DescriptiveComplexity.queryDbStructure`), and the round-trip theorem
(`DescriptiveComplexity.concreteQueryHolds_iff_queryHolds`) shows that the abstract
semantics of step 2 agrees with the textbook one on every encoded instance.
The `Nonempty C` hypothesis is this file's junk conventions surfacing one
last time: a variable occurring in no atom is unconstrained in the abstract
semantics but must still be assigned a constant in the concrete one – for
genuine BCQs (every variable occurs in an atom) over a nonempty database
domain, nothing is lost.
-/

section Concrete

variable {V C : Type}

/-- The textbook semantics of a concrete Boolean conjunctive query `q` (a
list of binary atoms with arguments in `V ⊕ C`: variables to the left,
constants to the right) on a concrete graph database `D` (a list of facts
over the constants): some assignment of the variables to constants sends
every atom to a fact. -/
def ConcreteQueryHolds (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) : Prop :=
  ∃ v : V → C, ∀ p ∈ q, (Sum.elim v id p.1, Sum.elim v id p.2) ∈ D

/-- The `Language.queryDb`-structure encoding a concrete instance: universe
`V ⊕ C`, the variables being the left summands, with the atoms of `q` and
the facts of `D`. -/
@[instance_reducible]
def queryDbStructure (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) :
    Language.queryDb.Structure (V ⊕ C) where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .isVar => fun x =>
      match x 0 with
      | Sum.inl _ => True
      | Sum.inr _ => False
    | _, .atom => fun x => (x 0, x 1) ∈ q
    | _, .fact => fun x =>
      match x 0, x 1 with
      | Sum.inr a, Sum.inr b => (a, b) ∈ D
      | _, _ => False

/-- The concrete assignment read off a structural valuation: the constant
the valuation sends a variable to (or a default for the junk case of a
variable mapped to a variable, possible only for variables in no atom). -/
private noncomputable def concreteVal [Nonempty C] (h : V ⊕ C → V ⊕ C) (x : V) : C :=
  match h (Sum.inl x) with
  | Sum.inr c => c
  | Sum.inl _ => Classical.arbitrary C

private theorem concreteVal_eq [Nonempty C] {h : V ⊕ C → V ⊕ C} {x : V} {c : C}
    (hs : h (Sum.inl x) = Sum.inr c) : concreteVal h x = c := by
  simp only [concreteVal]
  rw [hs]

/-- **The encoding is faithful**: the abstract semantics `QueryHolds` of the
encoded structure agrees with the textbook semantics of the concrete query
on the concrete database. -/
theorem concreteQueryHolds_iff_queryHolds [Nonempty C]
    (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) :
    ConcreteQueryHolds q D ↔ @QueryHolds (V ⊕ C) (queryDbStructure q D) := by
  letI := queryDbStructure q D
  constructor
  · -- an assignment becomes a valuation, sending `Sum.inl x` to
    -- `Sum.inr (v x)` and fixing the constants
    rintro ⟨v, hv⟩
    refine ⟨Sum.elim (fun x => Sum.inr (v x)) Sum.inr, fun t ht => ?_, fun t t' hat => ?_⟩
    · rcases t with x | c
      · exact absurd trivial ht
      · rfl
    · have hq : (t, t') ∈ q := hat
      have hf := hv (t, t') hq
      rcases t with x | c <;> rcases t' with x' | c' <;>
        exact ⟨hf, fun hh => hh, fun hh => hh⟩
  · -- a valuation becomes an assignment: atoms force every variable's image
    -- onto the constant side, where its value can be read off
    rintro ⟨h, hfix, hatom⟩
    have himg : ∀ t t' : V ⊕ C, (t, t') ∈ q →
        ∃ a b : C, h t = Sum.inr a ∧ h t' = Sum.inr b ∧ (a, b) ∈ D := by
      intro t t' hq
      obtain ⟨hf, hnv, hnv'⟩ := hatom t t' hq
      rcases hht : h t with x | a
      · rw [hht] at hnv
        exact absurd trivial hnv
      rcases hht' : h t' with x' | b
      · rw [hht'] at hnv'
        exact absurd trivial hnv'
      rw [hht, hht'] at hf
      exact ⟨a, b, rfl, rfl, hf⟩
    have hval : ∀ (s : V ⊕ C) (e : C), h s = Sum.inr e →
        Sum.elim (concreteVal h) id s = e := by
      intro s e hs
      rcases s with x | c'
      · exact concreteVal_eq hs
      · have hfix' : h (Sum.inr c') = Sum.inr c' := hfix (Sum.inr c') fun hh => hh
        rw [hfix'] at hs
        exact Sum.inr.inj hs
    refine ⟨concreteVal h, ?_⟩
    rintro ⟨t, t'⟩ hp
    obtain ⟨a, b, ha, hb, hab⟩ := himg t t' hp
    change (Sum.elim (concreteVal h) id t, Sum.elim (concreteVal h) id t') ∈ D
    rw [hval t a ha, hval t' b hb]
    exact hab

/-- A concrete worked instance: the query `∃ x, E(x, c₀) ∧ E(c₀, x)` (one
variable, one constant `c₀`) holds in the two-fact database
`{E(c₁, c₀), E(c₀, c₁)}`, witnessed by `x ↦ c₁`. -/
example :
    ConcreteQueryHolds (V := Fin 1) (C := Fin 2)
      [(Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inl 0)]
      [(1, 0), (0, 1)] :=
  ⟨fun _ => 1, by decide⟩

end Concrete

end DescriptiveComplexity

/-!
### Step 7: containment – vocabulary, semantics, and the Chandra–Merlin
theorem

An instance of the containment problem is a *pair* of queries over a shared
universe: unary predicates mark the variables of the left and of the right
query, binary relations record their atoms, and the remaining elements are
shared constants. The problem asks whether the left query is contained in the
right one: every database satisfying the left query satisfies the right one.

Unlike evaluation, the defining property quantifies over *all* databases –
this is where the generic `SatisfiedIn` with an external database pays off.
Note the junk convention it implies: in an atom of one query, an element
marked only as a variable of the *other* query is not a constant, so it acts
as an existential variable of both queries. Well-formed instances (where each
query's atoms only involve its own variables and constants) are unaffected.

The key structural result is the **Chandra–Merlin theorem**: containment
holds iff there is a homomorphism from the right query into the *canonical
database* of the left one – the instance universe itself, with the left
atoms as facts and every element denoting itself. Both directions are short:
the canonical database trivially satisfies the left query, and conversely a
homomorphism composes with any satisfying valuation. This theorem is what
turns the ∀-databases semantics into an ∃-certificate condition, i.e. into
something NP-shaped.
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the language of query pairs. -/
inductive queryPairRel : ℕ → Type
  /-- `leftVar x`: the element `x` is a variable of the left query. -/
  | leftVar : queryPairRel 1
  /-- `rightVar x`: the element `x` is a variable of the right query. -/
  | rightVar : queryPairRel 1
  /-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
  | leftAtom : queryPairRel 2
  /-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
  | rightAtom : queryPairRel 2
  deriving DecidableEq

/-- The relational language of pairs of conjunctive queries over a shared
universe of variables and constants. -/
protected def queryPair : Language :=
  ⟨fun _ => Empty, queryPairRel⟩
  deriving IsRelational

/-- The symbol for “is a variable of the left query”. -/
abbrev qpLeftVar : Language.queryPair.Relations 1 := .leftVar

/-- The symbol for “is a variable of the right query”. -/
abbrev qpRightVar : Language.queryPair.Relations 1 := .rightVar

/-- The symbol for “is an atom of the left query”. -/
abbrev qpLeftAtom : Language.queryPair.Relations 2 := .leftAtom

/-- The symbol for “is an atom of the right query”. -/
abbrev qpRightAtom : Language.queryPair.Relations 2 := .rightAtom

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

section PairShorthands

variable {A : Type} [Language.queryPair.Structure A]

/-- `x` is a variable of the left query. -/
def LVar (x : A) : Prop := RelMap qpLeftVar ![x]

/-- `x` is a variable of the right query. -/
def RVar (x : A) : Prop := RelMap qpRightVar ![x]

/-- `E(x, y)` is an atom of the left query. -/
def LAtom (x y : A) : Prop := RelMap qpLeftAtom ![x, y]

/-- `E(x, y)` is an atom of the right query. -/
def RAtom (x y : A) : Prop := RelMap qpRightAtom ![x, y]

/-- `x` is a variable of either query; the non-`PairVar` elements are the
shared constants, whose denotation every database fixes. -/
def PairVar (x : A) : Prop := LVar x ∨ RVar x

end PairShorthands

/-- The left query is contained in the right one: every database (over any
universe, with any interpretation of the constants) satisfying the left query
satisfies the right query. -/
def QueryContained (A : Type) [Language.queryPair.Structure A] : Prop :=
  ∀ (U : Type) (F : U → U → Prop) (ι : A → U),
    SatisfiedIn (PairVar (A := A)) (LAtom (A := A)) F ι →
      SatisfiedIn (PairVar (A := A)) (RAtom (A := A)) F ι

/-- **The Chandra–Merlin theorem**: containment holds iff there is a
homomorphism from the right query to the canonical database of the left one –
i.e. a map of the universe to itself, fixing the constants, that sends every
right atom to a left atom. The forward direction instantiates containment at
the canonical database (which satisfies the left query via the identity
valuation); the backward direction composes the homomorphism with any
satisfying valuation. -/
theorem queryContained_iff_hom (A : Type) [Language.queryPair.Structure A] :
    QueryContained A ↔ CQHom (PairVar (A := A)) (RAtom (A := A)) (LAtom (A := A)) := by
  constructor
  · intro hc
    exact hc A (LAtom (A := A)) id ⟨id, fun x _ => rfl, fun x y hxy => hxy⟩
  · rintro ⟨h, hfix, hatom⟩ U F ι ⟨v, hvfix, hvatom⟩
    refine ⟨v ∘ h, fun x hx => ?_, fun x y hxy => hvatom _ _ (hatom x y hxy)⟩
    rw [Function.comp_apply, hfix x hx]
    exact hvfix x hx

/-- Containment is isomorphism-invariant: via the Chandra–Merlin theorem, it
suffices to transport the homomorphism criterion, which the generic transport
lemma of step 2 does. (Transporting the ∀-databases definition directly would
also work, but reusing the homomorphism form is shorter.) -/
theorem queryContained_iso {A B : Type} [Language.queryPair.Structure A]
    [Language.queryPair.Structure B] (e : A ≃[Language.queryPair] B) :
    QueryContained A ↔ QueryContained B := by
  rw [queryContained_iff_hom, queryContained_iff_hom]
  exact CQHom.equiv_iff e.toEquiv
    (fun a => or_congr (relMap_equiv₁ e qpLeftVar a) (relMap_equiv₁ e qpRightVar a))
    (fun a a' => relMap_equiv₂ e qpRightAtom a a')
    (fun a a' => relMap_equiv₂ e qpLeftAtom a a')

/-- **BCQ containment**, as a decision problem on
`Language.queryPair`-structures: is the left query contained in the right
one? -/
def CQContainment : DecisionProblem Language.queryPair where
  Holds := fun A inst => @QueryContained A inst
  iso_invariant := fun e => queryContained_iso e

/-!
### Step 8: containment is in NP, by reduction to evaluation

By Chandra–Merlin, containment is evaluation of the right query in the
canonical database of the left one – so containment FO-reduces to
evaluation, and membership in NP follows from `cqEval_mem_NP` through
`ComplexityClass.mem_of_foReduction`. No second kernel needed.

The interpretation must produce a *well-formed* evaluation instance from an
arbitrary query-pair structure, and this forces a design decision worth
dwelling on, because it recurs in every reduction between problems whose
semantics have different junk conventions. In the homomorphism criterion the
canonical database consists of *all* elements (frozen variables and
constants alike), while in an evaluation instance the database elements are
exactly the non-variables. A single copy of the universe cannot be split
both ways, so the interpretation uses two tags – a query side and a database
side – and *routes* each atom endpoint to the query side if it is a variable
of either query (recall the junk convention of step 7) and to the database
side otherwise. The database side carries the left atoms as facts, on all
elements. All formulas remain quantifier-free.
-/

/-- Tags for the interpretation of evaluation instances in query pairs:
a query side and a database side (the canonical database of the left
query). -/
inductive PairTag : Type
  /-- `(query, x)`: the element `x` viewed as part of the right query. -/
  | query : PairTag
  /-- `(db, x)`: the element `x` viewed as part of the canonical database of
  the left query. -/
  | db : PairTag
  deriving DecidableEq, Nonempty

instance : Fintype PairTag :=
  ⟨{.query, .db}, fun t => by cases t <;> simp⟩

/-- Formula: argument `i` is a variable of the left query. -/
private def lvarF {n : ℕ} (i : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  qpLeftVar.formula₁ (Term.var (i, 0))

/-- Formula: argument `i` is a variable of the right query. -/
private def rvarF {n : ℕ} (i : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  qpRightVar.formula₁ (Term.var (i, 0))

/-- Formula: argument `i` is a variable of either query. -/
private def pairVarF {n : ℕ} (i : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  lvarF i ⊔ rvarF i

/-- Formula: argument `i` is a shared constant. -/
private def constF {n : ℕ} (i : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  ∼(lvarF i) ⊓ ∼(rvarF i)

/-- Formula: `E(i, j)` is an atom of the left query. -/
private def latomF {n : ℕ} (i j : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  qpLeftAtom.formula₂ (Term.var (i, 0)) (Term.var (j, 0))

/-- Formula: `E(i, j)` is an atom of the right query. -/
private def ratomF {n : ℕ} (i j : Fin n) : Language.queryPair.Formula (Fin n × Fin 1) :=
  qpRightAtom.formula₂ (Term.var (i, 0)) (Term.var (j, 0))

/-- Defining formula for `isVar`: on the query side, the variables of either
query; nothing on the database side. -/
def ctevIsVarFormula : PairTag → Language.queryPair.Formula (Fin 1 × Fin 1)
  | .query => pairVarF 0
  | .db => ⊥

/-- Defining formula for `atom`: the right atoms, each endpoint routed to the
query side if it is a variable and to the database side if it is a
constant. -/
def ctevAtomFormula : PairTag → PairTag → Language.queryPair.Formula (Fin 2 × Fin 1)
  | .query, .query => ratomF 0 1 ⊓ (pairVarF 0 ⊓ pairVarF 1)
  | .query, .db => ratomF 0 1 ⊓ (pairVarF 0 ⊓ constF 1)
  | .db, .query => ratomF 0 1 ⊓ (constF 0 ⊓ pairVarF 1)
  | .db, .db => ratomF 0 1 ⊓ (constF 0 ⊓ constF 1)

/-- Defining formula for `fact`: the left atoms, on the database side. -/
def ctevFactFormula : PairTag → PairTag → Language.queryPair.Formula (Fin 2 × Fin 1)
  | .db, .db => latomF 0 1
  | _, _ => ⊥

/-- The first-order interpretation producing, from a query pair, the
evaluation instance “does the right query hold in the canonical database of
the left one?”. -/
def containmentToEval :
    FOInterpretation Language.queryPair Language.queryDb PairTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isVar => fun t => ctevIsVarFormula (t 0)
    | _, .atom => fun t => ctevAtomFormula (t 0) (t 1)
    | _, .fact => fun t => ctevFactFormula (t 0) (t 1)

section Characterizations

variable {A : Type} [Language.queryPair.Structure A]

@[simp]
theorem ctev_isVar_iff (t : PairTag) (w : Fin 1 → A) :
    QVar (A := containmentToEval.Map A) (t, w) ↔ t = .query ∧ PairVar (w 0) := by
  change RelMap (M := containmentToEval.Map A) qdbIsVar ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;>
    simp [containmentToEval, ctevIsVarFormula, pairVarF, lvarF, rvarF, PairVar, LVar, RVar,
      Formula.realize_rel₁]

@[simp]
theorem ctev_atom_iff (t t' : PairTag) (w w' : Fin 1 → A) :
    QAtom (A := containmentToEval.Map A) (t, w) (t', w') ↔
      RAtom (w 0) (w' 0) ∧ (t = .query ↔ PairVar (w 0)) ∧
        (t' = .query ↔ PairVar (w' 0)) := by
  change RelMap (M := containmentToEval.Map A) qdbAtom ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [containmentToEval, ctevAtomFormula, ratomF, pairVarF, constF, lvarF, rvarF,
      PairVar, LVar, RVar, RAtom, Formula.realize_rel₂, not_or]

@[simp]
theorem ctev_fact_iff (t t' : PairTag) (w w' : Fin 1 → A) :
    DbFact (A := containmentToEval.Map A) (t, w) (t', w') ↔
      t = .db ∧ t' = .db ∧ LAtom (w 0) (w' 0) := by
  change RelMap (M := containmentToEval.Map A) qdbFact ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [containmentToEval, ctevFactFormula, latomF, LAtom, Formula.realize_rel₂]

end Characterizations

open Classical in
/-- The valuation on the interpreted evaluation instance induced by a
containment homomorphism `h`: move each query-side variable to the
database-side copy of its `h`-image, fix everything else. (A top-level
definition rather than a `fun` inside the proof, so that its defining
equations are available to `simp` – a trick worth remembering whenever a
witness is defined by cases.) -/
private noncomputable def routedVal {A : Type} [Language.queryPair.Structure A]
    (h : A → A) : containmentToEval.Map A → containmentToEval.Map A
  | (.query, w) => if PairVar (w 0) then (.db, fun _ => h (w 0)) else (.query, w)
  | (.db, w) => (.db, w)

/-- On any atom endpoint (whose tag matches its variable status, as the
interpretation guarantees), the routed valuation lands on the database-side
copy of the `h`-image. -/
private theorem routedVal_spec {A : Type} [Language.queryPair.Structure A]
    {h : A → A} (hfix : ∀ x, ¬PairVar x → h x = x) (s : PairTag) (ws : Fin 1 → A)
    (hTs : s = PairTag.query ↔ PairVar (ws 0)) :
    routedVal h (s, ws) = (PairTag.db, fun _ => h (ws 0)) := by
  cases s with
  | query =>
    simp only [routedVal]
    exact if_pos (hTs.mp rfl)
  | db =>
    have hnv : ¬PairVar (ws 0) := fun hpv => by simpa using hTs.mpr hpv
    simp only [routedVal]
    refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
    rw [hfix _ hnv]
    exact congrArg ws (Subsingleton.elim j 0)

/-- Correctness of `containmentToEval`: containment holds iff the interpreted
evaluation instance is a yes-instance. Both sides are homomorphism
conditions (containment via the Chandra–Merlin theorem), and the proof
translates homomorphisms back and forth across the routing of the
interpretation. -/
theorem queryContained_iff_map_queryHolds (A : Type) [Language.queryPair.Structure A] :
    QueryContained A ↔ QueryHolds (containmentToEval.Map A) := by
  rw [queryContained_iff_hom]
  constructor
  · -- a containment homomorphism `h` becomes a valuation on the interpreted
    -- instance: the routed valuation above
    rintro ⟨h, hfix, hatom⟩
    refine ⟨routedVal h, fun p hp => ?_, fun p q hpq => ?_⟩
    · obtain ⟨t, w⟩ := p
      cases t with
      | query =>
        have hnv : ¬PairVar (w 0) := fun hv => hp ((ctev_isVar_iff _ _).mpr ⟨rfl, hv⟩)
        simp only [routedVal]
        exact if_neg hnv
      | db => rfl
    · obtain ⟨t, w⟩ := p
      obtain ⟨t', w'⟩ := q
      rw [ctev_atom_iff] at hpq
      obtain ⟨hR, hT, hT'⟩ := hpq
      rw [routedVal_spec (fun z hz => hfix z hz) t w hT,
        routedVal_spec (fun z hz => hfix z hz) t' w' hT']
      refine ⟨(ctev_fact_iff _ _ _ _).mpr ⟨rfl, rfl, ?_⟩, ?_, ?_⟩
      · exact hatom _ _ hR
      · simp
      · simp
  · -- a valuation `H` on the interpreted instance becomes a containment
    -- homomorphism: read off the value of the query-side copy of each
    -- variable
    rintro ⟨H, hfix, hatom⟩
    classical
    refine ⟨fun z => if PairVar z then (H (PairTag.query, fun _ => z)).2 0 else z,
      fun z hz => if_neg hz, fun x y hxy => ?_⟩
    have route : ∀ z : A, ∃ p : containmentToEval.Map A,
        (p.1 = PairTag.query ↔ PairVar (p.2 0)) ∧ p.2 0 = z ∧
          (H p).2 0 = if PairVar z then (H (PairTag.query, fun _ => z)).2 0 else z := by
      intro z
      by_cases hz : PairVar z
      · refine ⟨(PairTag.query, fun _ => z), by simp [hz], rfl, ?_⟩
        rw [if_pos hz]
      · refine ⟨(PairTag.db, fun _ => z), by simp [hz], rfl, ?_⟩
        have hnq : ¬QVar (A := containmentToEval.Map A) (PairTag.db, fun _ => z) := by
          simp
        rw [hfix _ hnq]
        exact (if_neg hz).symm
    obtain ⟨p, hp1, hp2, hp3⟩ := route x
    obtain ⟨q, hq1, hq2, hq3⟩ := route y
    have hpq : QAtom p q := by
      refine (ctev_atom_iff _ _ _ _).mpr ⟨?_, hp1, hq1⟩
      rw [hp2, hq2]
      exact hxy
    obtain ⟨hfact, -, -⟩ := hatom _ _ hpq
    obtain ⟨-, -, hL⟩ := (ctev_fact_iff _ _ _ _).mp hfact
    change LAtom (if PairVar x then (H (PairTag.query, fun _ => x)).2 0 else x)
      (if PairVar y then (H (PairTag.query, fun _ => y)).2 0 else y)
    rw [← hp3, ← hq3]
    exact hL

/-- **BCQ containment FO-reduces to BCQ evaluation** – the Chandra–Merlin
theorem, in reduction form: evaluate the right query in the canonical
database of the left one. -/
def cqContainment_fo_reduction_cqEval : CQContainment ≤ᶠᵒ CQEval where
  Tag := PairTag
  dim := 1
  toInterpretation := containmentToEval
  correct A _ _ := queryContained_iff_map_queryHolds A

/-- BCQ containment is in NP: it FO-reduces to BCQ evaluation, which is in
NP. -/
theorem cqContainment_mem_NP : CQContainment ∈ NP :=
  NP.mem_of_foReduction cqContainment_fo_reduction_cqEval cqEval_mem_NP

/-!
### Step 9: containment is NP-hard, by reduction from evaluation

The reverse reduction expresses the other classical half of the
correspondence: *a database is just a conjunctive query with no variables*.
An evaluation instance `(q, D)` becomes the pair “(the canonical query of
`D`) ⊆ `q`”: the left query has no variables and one atom per genuine
database edge, the right query is `q` itself. Every element keeps its role,
so a single tag and dimension 1 suffice, and correctness reduces – through
Chandra–Merlin on the interpreted side – to comparing two homomorphism
conditions over universes identified by `FOInterpretation.mapEquivSelf`.
-/

/-- The first-order interpretation producing, from an evaluation instance,
the containment instance “(the database, viewed as a variable-free query)
is contained in the query”. -/
def evalToContainment : FOInterpretation Language.queryDb Language.queryPair Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .leftVar => fun _ => ⊥
    | _, .rightVar => fun _ => qdbIsVar.formula₁ (Term.var (0, 0))
    | _, .leftAtom => fun _ =>
        (qdbFact.formula₂ (Term.var (0, 0)) (Term.var (1, 0)) ⊓
          ∼(qdbIsVar.formula₁ (Term.var (0, 0)))) ⊓
          ∼(qdbIsVar.formula₁ (Term.var (1, 0)))
    | _, .rightAtom => fun _ => qdbAtom.formula₂ (Term.var (0, 0)) (Term.var (1, 0))

section Characterizations

variable {A : Type} [Language.queryDb.Structure A]

@[simp]
theorem etc_leftVar (w : Fin 1 → A) :
    ¬LVar (A := evalToContainment.Map A) ((), w) := by
  change ¬RelMap (M := evalToContainment.Map A) qpLeftVar ![((), w)]
  rw [FOInterpretation.relMap_map]
  simp [evalToContainment]

@[simp]
theorem etc_rightVar (w : Fin 1 → A) :
    RVar (A := evalToContainment.Map A) ((), w) ↔ QVar (w 0) := by
  change RelMap (M := evalToContainment.Map A) qpRightVar ![((), w)] ↔ _
  rw [FOInterpretation.relMap_map]
  simp [evalToContainment, QVar, Formula.realize_rel₁]

@[simp]
theorem etc_leftAtom (w w' : Fin 1 → A) :
    LAtom (A := evalToContainment.Map A) ((), w) ((), w') ↔ DbEdge (w 0) (w' 0) := by
  change RelMap (M := evalToContainment.Map A) qpLeftAtom ![((), w), ((), w')] ↔ _
  rw [FOInterpretation.relMap_map]
  simp [evalToContainment, DbEdge, DbFact, QVar, Formula.realize_rel₁,
    Formula.realize_rel₂, and_assoc]

@[simp]
theorem etc_rightAtom (w w' : Fin 1 → A) :
    RAtom (A := evalToContainment.Map A) ((), w) ((), w') ↔ QAtom (w 0) (w' 0) := by
  change RelMap (M := evalToContainment.Map A) qpRightAtom ![((), w), ((), w')] ↔ _
  rw [FOInterpretation.relMap_map]
  simp [evalToContainment, QAtom, Formula.realize_rel₂]

end Characterizations

section Correctness

variable (A : Type) [Language.queryDb.Structure A]

private theorem etc_hvar : ∀ b : evalToContainment.Map A,
    PairVar b ↔ QVar (evalToContainment.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  change _ ↔ QVar (w 0)
  simp [PairVar]

private theorem etc_hatom : ∀ b b' : evalToContainment.Map A,
    RAtom b b' ↔ QAtom (evalToContainment.mapEquivSelf A b)
      (evalToContainment.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  change _ ↔ QAtom (w 0) (w' 0)
  simp

private theorem etc_hfact : ∀ b b' : evalToContainment.Map A,
    LAtom b b' ↔ DbEdge (evalToContainment.mapEquivSelf A b)
      (evalToContainment.mapEquivSelf A b') := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  change _ ↔ DbEdge (w 0) (w' 0)
  simp

/-- Correctness of `evalToContainment`: the query holds in the database iff
the interpreted containment instance is a yes-instance. -/
theorem queryHolds_iff_map_queryContained :
    QueryHolds A ↔ QueryContained (evalToContainment.Map A) := by
  rw [queryContained_iff_hom]
  exact (CQHom.equiv_iff (evalToContainment.mapEquivSelf A) (etc_hvar A) (etc_hatom A)
    (etc_hfact A)).symm

end Correctness

/-- **BCQ evaluation FO-reduces to BCQ containment**: a database is a
variable-free conjunctive query. -/
def cqEval_fo_reduction_cqContainment : CQEval ≤ᶠᵒ CQContainment where
  Tag := Unit
  dim := 1
  toInterpretation := evalToContainment
  correct A _ _ := queryHolds_iff_map_queryContained A

/-- BCQ containment is NP-hard: BCQ evaluation, which is NP-hard, FO-reduces
to it. -/
theorem cqContainment_NP_hard : NP.Hard CQContainment :=
  NP.hard_of_foReduction cqEval_fo_reduction_cqContainment cqEval_NP_hard

/-- **BCQ containment is NP-complete** (Chandra–Merlin). -/
theorem cqContainment_NP_complete : NP.Complete CQContainment :=
  ⟨cqContainment_mem_NP, cqContainment_NP_hard⟩

/-!
### Where to go from here

The two problems above, with their four reductions, exercise every part of
the recipe; a few directions the reader can take next, in rough order of
effort:

* *other schemas*: redo the development for a schema with several relations
  of higher arity – the vocabulary grows, the proofs do not change shape
  (atoms of arity `k` need interpreted elements of dimension `k`, i.e.
  `dim > 1` interpretations as in `Problems/ThreeColorability/ToSat.lean`);
* *quantifier-free status of the containment reductions*: state and prove
  `IsQuantifierFree` for `containmentToEval` and `evalToContainment`, in the
  style of `threeColToCQEval_isQuantifierFree`;
* *a concrete bridge for containment*: encode a concrete *pair* of queries as
  a `Language.queryPair`-structure and prove the analogue of
  `concreteQueryHolds_iff_queryHolds`, tying `QueryContained` to a
  list-of-atoms statement of containment;
* *query equivalence*: two-sided containment; its NP-completeness follows
  from this file's results with a pair of FO reductions;
* *acyclic-query evaluation*: the tractable fragment (Yannakakis); its
  membership statement needs a logic for PTIME first (see the roadmap, §3).
-/

end DescriptiveComplexity
