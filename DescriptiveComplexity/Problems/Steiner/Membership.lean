/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Steiner.Defs
import DescriptiveComplexity.SecondOrder

/-!
# Steiner Tree is existential second-order definable

The membership half of its NP-completeness
(`DescriptiveComplexity.steinerTree_sigmaSODefinable`). The existential block guesses
four relations – the chosen set, a root, a strict partial order certifying
connectivity, and an injection of the chosen non-terminals into the marked set
– and the first-order kernel checks the eight conditions of
`DescriptiveComplexity.steinerOn_iff_certificate`.

The interesting one is connectivity, which is a transitive-closure condition
and hence not first-order. What is guessed instead is a *root* – as a relation
constrained to hold of at most one element, since the empty set is connected
and has no root – together with an order in which every other chosen vertex
has a chosen neighbour strictly below it. Walking down the order reaches the
root; that is the same certificate idea as for acyclicity in
`DescriptiveComplexity.Problems.Feedback`, run in the opposite direction.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

/-- The four relation variables guessed by the `Σ₁` definition of Steiner
Tree. -/
inductive SteinerGuess
  /-- The chosen set of vertices. -/
  | set
  /-- The root of the chosen set. -/
  | root
  /-- The order certifying connectivity. -/
  | order
  /-- The injection witnessing the threshold. -/
  | inj
  deriving DecidableEq

instance : Fintype SteinerGuess := ⟨{.set, .root, .order, .inj}, fun t => by cases t <;> decide⟩

/-- The single existential block of the `Σ₁` definition of Steiner Tree. -/
def steinerGuessBlock : SOBlock where
  ι := SteinerGuess
  arity := fun i => match i with
    | .set => 1
    | .root => 1
    | .order => 2
    | .inj => 2

/-- The symbol of the chosen-set relation variable. -/
def sgSetRel : steinerGuessBlock.lang.Relations 1 := ⟨.set, rfl⟩

/-- The symbol of the root relation variable. -/
def sgRootRel : steinerGuessBlock.lang.Relations 1 := ⟨.root, rfl⟩

/-- The symbol of the order relation variable. -/
def sgOrderRel : steinerGuessBlock.lang.Relations 2 := ⟨.order, rfl⟩

/-- The symbol of the injection relation variable. -/
def sgInjRel : steinerGuessBlock.lang.Relations 2 := ⟨.inj, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev steinerSOLang : Language := Language.steinerGraph.sum steinerGuessBlock.lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev kStAdjSym : steinerSOLang.Relations 2 := Sum.inl stAdj

/-- The terminal symbol in the kernel's vocabulary. -/
abbrev kStTermSym : steinerSOLang.Relations 1 := Sum.inl stTerminal

/-- The mark symbol in the kernel's vocabulary. -/
abbrev kStMarkedSym : steinerSOLang.Relations 1 := Sum.inl stMarked

/-- The chosen-set symbol in the kernel's vocabulary. -/
abbrev kStSetSym : steinerSOLang.Relations 1 := Sum.inr sgSetRel

/-- The root symbol in the kernel's vocabulary. -/
abbrev kStRootSym : steinerSOLang.Relations 1 := Sum.inr sgRootRel

/-- The order symbol in the kernel's vocabulary. -/
abbrev kStLtSym : steinerSOLang.Relations 2 := Sum.inr sgOrderRel

/-- The injection symbol in the kernel's vocabulary. -/
abbrev kStInjSym : steinerSOLang.Relations 2 := Sum.inr sgInjRel

/-! ### The clauses -/

/-- Kernel clause: every terminal is chosen. -/
private noncomputable def stTermClause : steinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kStTermSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kStSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: the root is chosen. -/
private noncomputable def stRootInClause : steinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kStRootSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kStSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: there is at most one root. -/
private noncomputable def stRootUniqueClause : steinerSOLang.Sentence :=
  ((Relations.formula₁ kStRootSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ kStRootSym (Term.var (Sum.inr 1))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel clause: the guessed order is transitive. -/
private noncomputable def stTransClause : steinerSOLang.Sentence :=
  ((Relations.formula₂ kStLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ kStLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ kStLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel clause: the guessed order is irreflexive. -/
private noncomputable def stIrreflClause : steinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ kStLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel clause: every chosen non-root has a chosen neighbour strictly below
it. -/
private noncomputable def stStepClause : steinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kStSetSym (Term.var (Sum.inr 0)) ⊓
        ∼(Relations.formula₁ kStRootSym (Term.var (Sum.inr 0)))).imp
      ((Relations.formula₁ kStSetSym (Term.var (Sum.inr ())) ⊓
        (Relations.formula₂ kStAdjSym (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr ())) ⊔
          Relations.formula₂ kStAdjSym (Term.var (Sum.inr ()))
            (Term.var (Sum.inl (Sum.inr 0)))) ⊓
        Relations.formula₂ kStLtSym (Term.var (Sum.inr ()))
          (Term.var (Sum.inl (Sum.inr 0)))).iExs Unit))

/-- Kernel clause: the guessed injection maps every chosen non-terminal to a
marked element. -/
private noncomputable def stTotalClause : steinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kStSetSym (Term.var (Sum.inr 0)) ⊓
        ∼(Relations.formula₁ kStTermSym (Term.var (Sum.inr 0)))).imp
      ((Relations.formula₂ kStInjSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ kStMarkedSym (Term.var (Sum.inr ()))).iExs Unit))

/-- Kernel clause: the guessed injection is injective. -/
private noncomputable def stInjClause : steinerSOLang.Sentence :=
  ((Relations.formula₂ kStInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ kStInjSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The first-order kernel of the `Σ₁` definition of Steiner Tree. -/
noncomputable def steinerKernel : steinerSOLang.Sentence :=
  stTermClause ⊓ (stRootInClause ⊓ (stRootUniqueClause ⊓ (stTransClause ⊓
    (stIrreflClause ⊓ (stStepClause ⊓ (stTotalClause ⊓ stInjClause))))))

/-! ### Realization -/

section Realize

variable {A : Type} [Language.steinerGraph.Structure A]
  (ρ : steinerGuessBlock.Assignment A)

/-- Realization at a structure expanded by an assignment of the block. -/
private abbrev SRealize (φ : steinerSOLang.Sentence) : Prop :=
  @Sentence.Realize steinerSOLang A
    (@sumStructure _ _ A _ (steinerGuessBlock.structure ρ)) φ

private theorem realize_stTermClause :
    SRealize ρ stTermClause ↔ ∀ x : A, STTerminal x → ρ .set ![x] := by
  letI := steinerGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  rw [stTermClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hS]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩

private theorem realize_stRootInClause :
    SRealize ρ stRootInClause ↔ ∀ x : A, ρ .root ![x] → ρ .set ![x] := by
  letI := steinerGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  rw [stRootInClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, hS, hR]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩

private theorem realize_stRootUniqueClause :
    SRealize ρ stRootUniqueClause ↔ ∀ x y : A, ρ .root ![x] → ρ .root ![y] → x = y := by
  letI := steinerGuessBlock.structure ρ
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  rw [stRootUniqueClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, hR]
  exact ⟨fun h x y hx hy => h ![x, y] ⟨hx, hy⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

private theorem realize_stTransClause :
    SRealize ρ stTransClause ↔
      ∀ x y z : A, ρ .order ![x, y] → ρ .order ![y, z] → ρ .order ![x, z] := by
  letI := steinerGuessBlock.structure ρ
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := steinerSOLang) (M := A) kStLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [stTransClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hL]
  exact ⟨fun h x y z h₁ h₂ => h ![x, y, z] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

private theorem realize_stIrreflClause :
    SRealize ρ stIrreflClause ↔ ∀ x : A, ¬ρ .order ![x, x] := by
  letI := steinerGuessBlock.structure ρ
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := steinerSOLang) (M := A) kStLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [stIrreflClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hL]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

private theorem realize_stStepClause :
    SRealize ρ stStepClause ↔ ∀ x : A, ρ .set ![x] → ¬ρ .root ![x] →
      ∃ y : A, (ρ .set ![y] ∧ (STAdj x y ∨ STAdj y x)) ∧ ρ .order ![y, x] := by
  letI := steinerGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := steinerSOLang) (M := A) kStLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [stStepClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hS, hR, hL]
  constructor
  · intro h x hx hnr
    obtain ⟨y, hy⟩ := h (fun _ => x) ⟨hx, hnr⟩
    exact ⟨y (), hy⟩
  · intro h i hi
    obtain ⟨y, hy⟩ := h (i 0) hi.1 hi.2
    exact ⟨fun _ => y, hy⟩

private theorem realize_stTotalClause :
    SRealize ρ stTotalClause ↔ ∀ x : A, ρ .set ![x] → ¬STTerminal x →
      ∃ y : A, ρ .inj ![x, y] ∧ STMarked y := by
  letI := steinerGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := steinerSOLang) (M := A) kStSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hI : ∀ (w : Fin 2 → A),
      RelMap (L := steinerSOLang) (M := A) kStInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [stTotalClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hS, hI]
  constructor
  · intro h x hx hnt
    obtain ⟨y, hy⟩ := h (fun _ => x) ⟨hx, hnt⟩
    exact ⟨y (), hy⟩
  · intro h i hi
    obtain ⟨y, hy⟩ := h (i 0) hi.1 hi.2
    exact ⟨fun _ => y, hy⟩

private theorem realize_stInjClause :
    SRealize ρ stInjClause ↔ ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  letI := steinerGuessBlock.structure ρ
  have hI : ∀ (w : Fin 2 → A),
      RelMap (L := steinerSOLang) (M := A) kStInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [stInjClause]
  simp only [SRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, hI]
  exact ⟨fun h x x' y h₁ h₂ => h ![x, x', y] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

private theorem realize_steinerKernel :
    SRealize ρ steinerKernel ↔
      (∀ x : A, STTerminal x → ρ .set ![x]) ∧
      (∀ x : A, ρ .root ![x] → ρ .set ![x]) ∧
      (∀ x y : A, ρ .root ![x] → ρ .root ![y] → x = y) ∧
      (∀ x y z : A, ρ .order ![x, y] → ρ .order ![y, z] → ρ .order ![x, z]) ∧
      (∀ x : A, ¬ρ .order ![x, x]) ∧
      (∀ x : A, ρ .set ![x] → ¬ρ .root ![x] →
        ∃ y : A, (ρ .set ![y] ∧ (STAdj x y ∨ STAdj y x)) ∧ ρ .order ![y, x]) ∧
      (∀ x : A, ρ .set ![x] → ¬STTerminal x → ∃ y : A, ρ .inj ![x, y] ∧ STMarked y) ∧
      ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  rw [steinerKernel]
  simp only [SRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_stTermClause ρ)
    (and_congr (realize_stRootInClause ρ)
      (and_congr (realize_stRootUniqueClause ρ)
        (and_congr (realize_stTransClause ρ)
          (and_congr (realize_stIrreflClause ρ)
            (and_congr (realize_stStepClause ρ)
              (and_congr (realize_stTotalClause ρ) (realize_stInjClause ρ)))))))

end Realize

/-- **Steiner Tree is `Σ₁`-definable**: guess the chosen set, its root, an
order certifying that it is connected, and an injection of its non-terminals
into the marked set, then check the eight conditions first-order. -/
theorem steinerTree_sigmaSODefinable : SigmaSODefinable 1 SteinerTree := by
  refine ⟨[steinerGuessBlock], rfl, steinerKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hst⟩
    obtain ⟨S, hterms, ⟨Rt, hRtS, huniq, Lt, htrans, hirr, hstep⟩, ⟨e⟩⟩ :=
      (steinerOn_iff_certificate _ _ _).mp hst
    refine ⟨fun i => match i with
      | .set => fun w : Fin 1 → A => S (w 0)
      | .root => fun w : Fin 1 → A => Rt (w 0)
      | .order => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : S (w 0) ∧ ¬STTerminal (w 0),
            (e ⟨w 0, h⟩ : {x // STMarked x}).1 = w 1, ?_⟩
    refine (realize_steinerKernel _).mpr ⟨hterms, hRtS, huniq, htrans, hirr, ?_,
      fun x hx hnt => ⟨(e ⟨x, hx, hnt⟩).1, ⟨⟨hx, hnt⟩, rfl⟩, (e ⟨x, hx, hnt⟩).2⟩, ?_⟩
    · intro x hx hnr
      obtain ⟨y, hlink, hlt⟩ := hstep x hx hnr
      exact ⟨y, ⟨hlink.2.1, hlink.2.2⟩, hlt⟩
    · rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
      exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hterms, hRtS, huniq, htrans, hirr, hstep, htot, hinj⟩ :=
      (realize_steinerKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ .set ![x] ∧ ¬STTerminal x},
        ∃ y : A, ρ .inj ![x.1, y] ∧ STMarked y := fun x => htot x.1 x.2.1 x.2.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (steinerOn_iff_certificate _ _ _).mpr
      ⟨fun x => ρ .set ![x], hterms,
        ⟨fun x => ρ .root ![x], hRtS, huniq, fun x y => ρ .order ![x, y], htrans, hirr, ?_⟩,
        ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    · intro x hx hnr
      obtain ⟨y, ⟨hy, hadj⟩, hlt⟩ := hstep x hx hnr
      exact ⟨y, ⟨hx, hy, hadj⟩, hlt⟩
    · have hval : f x = f x' := congrArg Subtype.val hxx'
      refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
      rw [hval]
      exact hf1 x'

/-! ### The edge-weighted variant

The same certificate, plus the edge set itself, and with the threshold
injection mapping *pairs* to *elements* – hence a ternary relation variable,
for which `DescriptiveComplexity.realize_rel₃` plays the role Mathlib's
`Formula.realize_rel₁`/`₂` play at lower arity. -/

/-- Realization of an atom of arity 3. -/
theorem realize_rel₃ {L : Language} {α M : Type} [L.Structure M] {R : L.Relations 3}
    {t₁ t₂ t₃ : L.Term α} {v : α → M} :
    (R.formula ![t₁, t₂, t₃]).Realize v ↔
      RelMap R ![t₁.realize v, t₂.realize v, t₃.realize v] := by
  rw [Formula.realize_rel, iff_eq_eq]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The five relation variables guessed by the `Σ₁` definition of the
edge-weighted Steiner tree. -/
inductive EdgeSteinerGuess
  /-- The chosen set of edges. -/
  | tree
  /-- The chosen set of vertices. -/
  | set
  /-- The root of the chosen set. -/
  | root
  /-- The order certifying connectivity. -/
  | order
  /-- The injection witnessing the threshold. -/
  | inj
  deriving DecidableEq

instance : Fintype EdgeSteinerGuess :=
  ⟨{.tree, .set, .root, .order, .inj}, fun t => by cases t <;> decide⟩

/-- The single existential block of the `Σ₁` definition of the edge-weighted
Steiner tree. -/
def edgeSteinerGuessBlock : SOBlock where
  ι := EdgeSteinerGuess
  arity := fun i => match i with
    | .tree => 2
    | .set => 1
    | .root => 1
    | .order => 2
    | .inj => 3

/-- The symbol of the edge-set relation variable. -/
def esTreeRel : edgeSteinerGuessBlock.lang.Relations 2 := ⟨.tree, rfl⟩

/-- The symbol of the chosen-set relation variable. -/
def esSetRel : edgeSteinerGuessBlock.lang.Relations 1 := ⟨.set, rfl⟩

/-- The symbol of the root relation variable. -/
def esRootRel : edgeSteinerGuessBlock.lang.Relations 1 := ⟨.root, rfl⟩

/-- The symbol of the order relation variable. -/
def esOrderRel : edgeSteinerGuessBlock.lang.Relations 2 := ⟨.order, rfl⟩

/-- The symbol of the injection relation variable. -/
def esInjRel : edgeSteinerGuessBlock.lang.Relations 3 := ⟨.inj, rfl⟩

/-- The vocabulary of the edge-weighted kernel. -/
abbrev edgeSteinerSOLang : Language := Language.steinerGraph.sum edgeSteinerGuessBlock.lang

/-- The adjacency symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsAdjSym : edgeSteinerSOLang.Relations 2 := Sum.inl stAdj

/-- The terminal symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsTermSym : edgeSteinerSOLang.Relations 1 := Sum.inl stTerminal

/-- The mark symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsMarkedSym : edgeSteinerSOLang.Relations 1 := Sum.inl stMarked

/-- The edge-set symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsTreeSym : edgeSteinerSOLang.Relations 2 := Sum.inr esTreeRel

/-- The chosen-set symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsSetSym : edgeSteinerSOLang.Relations 1 := Sum.inr esSetRel

/-- The root symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsRootSym : edgeSteinerSOLang.Relations 1 := Sum.inr esRootRel

/-- The order symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsLtSym : edgeSteinerSOLang.Relations 2 := Sum.inr esOrderRel

/-- The injection symbol in the edge-weighted kernel's vocabulary. -/
abbrev kEsInjSym : edgeSteinerSOLang.Relations 3 := Sum.inr esInjRel

/-- Kernel clause: the chosen pairs are edges. -/
private noncomputable def esAdjClause : edgeSteinerSOLang.Sentence :=
  ((Relations.formula₂ kEsTreeSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
    (Relations.formula₂ kEsAdjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel clause: every terminal is spanned. -/
private noncomputable def esTermClause : edgeSteinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kEsTermSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kEsSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: the root is spanned. -/
private noncomputable def esRootInClause : edgeSteinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kEsRootSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kEsSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: there is at most one root. -/
private noncomputable def esRootUniqueClause : edgeSteinerSOLang.Sentence :=
  ((Relations.formula₁ kEsRootSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ kEsRootSym (Term.var (Sum.inr 1))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel clause: the guessed order is transitive. -/
private noncomputable def esTransClause : edgeSteinerSOLang.Sentence :=
  ((Relations.formula₂ kEsLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ kEsLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ kEsLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel clause: the guessed order is irreflexive. -/
private noncomputable def esIrreflClause : edgeSteinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ kEsLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel clause: every spanned non-root steps down along a chosen edge. -/
private noncomputable def esStepClause : edgeSteinerSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kEsSetSym (Term.var (Sum.inr 0)) ⊓
        ∼(Relations.formula₁ kEsRootSym (Term.var (Sum.inr 0)))).imp
      ((Relations.formula₁ kEsSetSym (Term.var (Sum.inr ())) ⊓
        (Relations.formula₂ kEsTreeSym (Term.var (Sum.inl (Sum.inr 0)))
            (Term.var (Sum.inr ())) ⊔
          Relations.formula₂ kEsTreeSym (Term.var (Sum.inr ()))
            (Term.var (Sum.inl (Sum.inr 0)))) ⊓
        Relations.formula₂ kEsLtSym (Term.var (Sum.inr ()))
          (Term.var (Sum.inl (Sum.inr 0)))).iExs Unit))

/-- Kernel clause: the guessed injection maps every chosen edge to a marked
element. -/
private noncomputable def esTotalClause : edgeSteinerSOLang.Sentence :=
  Formula.iAlls (Fin 2)
    ((Relations.formula₂ kEsTreeSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).imp
      ((Relations.formula kEsInjSym ![Term.var (Sum.inl (Sum.inr 0)),
            Term.var (Sum.inl (Sum.inr 1)), Term.var (Sum.inr ())] ⊓
        Relations.formula₁ kEsMarkedSym (Term.var (Sum.inr ()))).iExs Unit))

/-- Kernel clause: the guessed injection is injective. -/
private noncomputable def esInjClause : edgeSteinerSOLang.Sentence :=
  ((Relations.formula kEsInjSym ![Term.var (Sum.inr 0), Term.var (Sum.inr 1),
        Term.var (Sum.inr 4)] ⊓
      Relations.formula kEsInjSym ![Term.var (Sum.inr 2), Term.var (Sum.inr 3),
        Term.var (Sum.inr 4)]).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Term.equal (Term.var (Sum.inr 1)) (Term.var (Sum.inr 3)))).iAlls (Fin 5)

/-- The first-order kernel of the `Σ₁` definition of the edge-weighted Steiner
tree. -/
noncomputable def edgeSteinerKernel : edgeSteinerSOLang.Sentence :=
  esAdjClause ⊓ (esTermClause ⊓ (esRootInClause ⊓ (esRootUniqueClause ⊓ (esTransClause ⊓
    (esIrreflClause ⊓ (esStepClause ⊓ (esTotalClause ⊓ esInjClause)))))))

/-- Realization of the edge-weighted kernel. -/
private theorem realize_edgeSteinerKernel {A : Type} [Language.steinerGraph.Structure A]
    (ρ : edgeSteinerGuessBlock.Assignment A) :
    (@Sentence.Realize edgeSteinerSOLang A
        (@sumStructure _ _ A _ (edgeSteinerGuessBlock.structure ρ)) edgeSteinerKernel) ↔
      (∀ a b : A, ρ .tree ![a, b] → STAdj a b) ∧
      (∀ x : A, STTerminal x → ρ .set ![x]) ∧
      (∀ x : A, ρ .root ![x] → ρ .set ![x]) ∧
      (∀ x y : A, ρ .root ![x] → ρ .root ![y] → x = y) ∧
      (∀ x y z : A, ρ .order ![x, y] → ρ .order ![y, z] → ρ .order ![x, z]) ∧
      (∀ x : A, ¬ρ .order ![x, x]) ∧
      (∀ x : A, ρ .set ![x] → ¬ρ .root ![x] →
        ∃ y : A, (ρ .set ![y] ∧ (ρ .tree ![x, y] ∨ ρ .tree ![y, x])) ∧ ρ .order ![y, x]) ∧
      (∀ a b : A, ρ .tree ![a, b] → ∃ y : A, ρ .inj ![a, b, y] ∧ STMarked y) ∧
      (∀ a b a' b' y : A, ρ .inj ![a, b, y] → ρ .inj ![a', b', y] → a = a' ∧ b = b') := by
  letI := edgeSteinerGuessBlock.structure ρ
  have hT : ∀ (w : Fin 2 → A),
      RelMap (L := edgeSteinerSOLang) (M := A) kEsTreeSym w ↔ ρ .tree w := fun _ => Iff.rfl
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := edgeSteinerSOLang) (M := A) kEsSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := edgeSteinerSOLang) (M := A) kEsRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := edgeSteinerSOLang) (M := A) kEsLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  have hI : ∀ (w : Fin 3 → A),
      RelMap (L := edgeSteinerSOLang) (M := A) kEsInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [edgeSteinerKernel]
  simp only [esAdjClause, esTermClause, esRootInClause, esRootUniqueClause, esTransClause,
    esIrreflClause, esStepClause, esTotalClause, esInjClause, Sentence.Realize,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_not, realize_rel₃,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hT, hS, hR, hL, hI]
  refine and_congr ⟨fun h a b hab => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h x y hx hy => ?_, fun h i hi => ?_⟩
          (and_congr ⟨fun h x y z h₁ h₂ => ?_, fun h i hi => ?_⟩
            (and_congr ⟨fun h x => ?_, fun h i => ?_⟩
              (and_congr ⟨fun h x hx hnr => ?_, fun h i hi => ?_⟩
                (and_congr ⟨fun h a b hab => ?_, fun h i hi => ?_⟩
                  ⟨fun h a b a' b' y h₁ h₂ => ?_, fun h i hi => ?_⟩)))))))
  · exact h ![a, b] hab
  · exact h (i 0) (i 1) hi
  · exact h (fun _ => x) hx
  · exact h (i 0) hi
  · exact h (fun _ => x) hx
  · exact h (i 0) hi
  · exact h ![x, y] ⟨hx, hy⟩
  · exact h (i 0) (i 1) hi.1 hi.2
  · exact h ![x, y, z] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) hi.1 hi.2
  · exact h fun _ => x
  · exact h (i 0)
  · obtain ⟨y, hy⟩ := h (fun _ => x) ⟨hx, hnr⟩
    exact ⟨y (), hy⟩
  · obtain ⟨y, hy⟩ := h (i 0) hi.1 hi.2
    exact ⟨fun _ => y, hy⟩
  · obtain ⟨y, hy⟩ := h ![a, b] hab
    exact ⟨y (), hy⟩
  · obtain ⟨y, hy⟩ := h (i 0) (i 1) hi
    exact ⟨fun _ => y, hy⟩
  · exact h ![a, b, a', b', y] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2

/-- **The edge-weighted Steiner Tree is `Σ₁`-definable**: guess the edge set,
the vertices it spans, a root, an order certifying connectivity, and an
injection of the chosen edges into the marked set. -/
theorem edgeSteinerTree_sigmaSODefinable : SigmaSODefinable 1 EdgeSteinerTree := by
  refine ⟨[edgeSteinerGuessBlock], rfl, edgeSteinerKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hst⟩
    obtain ⟨T, S, hsub, hterms, ⟨Rt, hRtS, huniq, Lt, htrans, hirr, hstep⟩, ⟨e⟩⟩ :=
      (steinerEdgeOn_iff_certificate _ _ _).mp hst
    refine ⟨fun i => match i with
      | .tree => fun w : Fin 2 → A => T (w 0) (w 1)
      | .set => fun w : Fin 1 → A => S (w 0)
      | .root => fun w : Fin 1 → A => Rt (w 0)
      | .order => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | .inj => fun w : Fin 3 → A =>
          ∃ h : T (w 0) (w 1), (e ⟨(w 0, w 1), h⟩ : {x // STMarked x}).1 = w 2, ?_⟩
    refine (realize_edgeSteinerKernel _).mpr
      ⟨hsub, hterms, hRtS, huniq, htrans, hirr, ?_,
        fun a b hab => ⟨(e ⟨(a, b), hab⟩).1, ⟨hab, rfl⟩, (e ⟨(a, b), hab⟩).2⟩, ?_⟩
    · intro x hx hnr
      obtain ⟨y, hlink, hlt⟩ := hstep x hx hnr
      exact ⟨y, ⟨hlink.2.1, hlink.2.2⟩, hlt⟩
    · rintro a b a' b' y ⟨h, hy⟩ ⟨h', hy'⟩
      have heq := e.injective (Subtype.ext (hy.trans hy'.symm) :
        (e ⟨(a, b), h⟩ : {x // STMarked x}) = e ⟨(a', b'), h'⟩)
      exact ⟨congrArg Prod.fst (congrArg Subtype.val heq),
        congrArg Prod.snd (congrArg Subtype.val heq)⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hsub, hterms, hRtS, huniq, htrans, hirr, hstep, htot, hinj⟩ :=
      (realize_edgeSteinerKernel ρ).mp hρ
    have hch : ∀ p : {p : A × A // ρ .tree ![p.1, p.2]},
        ∃ y : A, ρ .inj ![p.1.1, p.1.2, y] ∧ STMarked y := by
      rintro ⟨⟨a, b⟩, hab⟩
      exact htot a b hab
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (steinerEdgeOn_iff_certificate _ _ _).mpr
      ⟨fun a b => ρ .tree ![a, b], fun x => ρ .set ![x], hsub, hterms,
        ⟨fun x => ρ .root ![x], hRtS, huniq, fun x y => ρ .order ![x, y], htrans, hirr, ?_⟩,
        ⟨⟨fun p => ⟨f p, hf2 p⟩, fun p p' hpp' => ?_⟩⟩⟩⟩
    · intro x hx hnr
      obtain ⟨y, ⟨hy, hlink⟩, hlt⟩ := hstep x hx hnr
      exact ⟨y, ⟨hx, hy, hlink⟩, hlt⟩
    · have hval : f p = f p' := congrArg Subtype.val hpp'
      obtain ⟨h₁, h₂⟩ := hinj p.1.1 p.1.2 p'.1.1 p'.1.2 (f p) (hf1 p)
        (by rw [hval]; exact hf1 p')
      exact Subtype.ext (Prod.ext h₁ h₂)

end SigmaOne

end DescriptiveComplexity
