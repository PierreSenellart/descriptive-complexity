/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.ParamFormula
import DescriptiveComplexity.Exponential.Block
import DescriptiveComplexity.Ordered

/-!
# Reading an expansion's defining sentences through the meanings

A defining sentence of an exponential expansion – the sentence that says whether
a relation of the expanded vocabulary holds of `k` points – is written over the
ordered base vocabulary expanded by `k` copies of the expansion's block
(`DescriptiveComplexity.ExpExpansion.relSentence`). Value invention holds those
`k` points as `k` invented values of one extended universe, each standing for an
assignment of the block through a guessed **meaning relation**. So the sentence
has to be read with:

* its base symbols passing through untouched, but among the *original* elements
  only;
* its order symbol at a **guessed** linear order, the extended universe having
  none of its own;
* the block symbol of copy `i` and variable `j` read as `Mⱼ vᵢ ·`, the meaning
  relation of `j` at the value the copy holds.

That is a `DescriptiveComplexity.ParamHom` – the third item changes a symbol's
arity and puts a free variable in front of its arguments – followed by
relativization to the original elements, which
`DescriptiveComplexity.ParamHom.relOnSentenceF` performs in one step.

What this file adds is the map itself (`DescriptiveComplexity.readHom`) and what
it is worth (`DescriptiveComplexity.realize_readHom`): the structure the map
induces on the original elements *is* the base structure expanded by the `k`
copies of the block, interpreted by the assignments the values mean. The three
hypotheses that buy it name the three items above, each as a plain statement
about the target structure rather than about a formula.

The target vocabulary is left abstract, a
`DescriptiveComplexity.ReadSyms` naming only the symbols the translation uses:
the assembly that puts the order, the meanings, the tag bits and a guessed
certificate into one block chooses where each of them sits, and nothing here
needs to know.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L Lt : Language.{0, 0}} {B : SOBlock}

/-! ### The symbols the translation uses -/

/-- The symbols a translation through the meanings needs in the target
vocabulary: the base vocabulary's own, a binary symbol for the guessed order,
and one meaning symbol per variable of the block, of that variable's arity plus
one. -/
structure ReadSyms (L : Language.{0, 0}) (B : SOBlock) (Lt : Language.{0, 0}) where
  /-- The image of a base symbol. -/
  base : ∀ {n : ℕ}, L.Relations n → Lt.Relations n
  /-- The symbol the guessed order is read at. -/
  ord : Lt.Relations 2
  /-- The meaning relation of a variable: its arity, plus the value it belongs
  to. -/
  mean : ∀ i : B.ι, Lt.Relations (B.arity i + 1)

/-! ### The map -/

variable (S : ReadSyms L B Lt) (k : ℕ)

/-- **The translation**: base symbols through, the order symbol at the guessed
order, and the block symbol of copy `i` at the meaning relation of its variable,
with the value of copy `i` as first argument. -/
def readHom [L.IsRelational] :
    ParamHom ((L.sum Language.order).sum (B.replicate k).lang) Lt (Fin k) where
  ar {n} r :=
    match r with
    | Sum.inl _ => n
    | Sum.inr s => B.arity s.1.2 + 1
  sym {_} r :=
    match r with
    | Sum.inl (Sum.inl r') => S.base r'
    | Sum.inl (Sum.inr .le) => S.ord
    | Sum.inr s => S.mean s.1.2
  args {_} r :=
    match r with
    | Sum.inl _ => Sum.inl
    | Sum.inr s => Fin.cases (Sum.inr s.1.1) fun j => Sum.inl (Fin.cast s.2 j)

/-- **The same at a single copy**, which is the shape a *domain* sentence has:
`DescriptiveComplexity.ExpExpansion.dom` speaks of one assignment, so its block
symbols are the block's own and there is one value to read them at. -/
def readHom₁ [L.IsRelational] :
    ParamHom ((L.sum Language.order).sum B.lang) Lt Unit where
  ar {n} r :=
    match r with
    | Sum.inl _ => n
    | Sum.inr s => B.arity s.1 + 1
  sym {_} r :=
    match r with
    | Sum.inl (Sum.inl r') => S.base r'
    | Sum.inl (Sum.inr .le) => S.ord
    | Sum.inr s => S.mean s.1
  args {_} r :=
    match r with
    | Sum.inl _ => Sum.inl
    | Sum.inr s => Fin.cases (Sum.inr ()) fun j => Sum.inl (Fin.cast s.2 j)

/-! ### What it is worth -/

section Realize

variable {S k} {M A : Type} [Lt.Structure M] [L.IsRelational] [L.Structure A] [LinearOrder A]
variable (e : A → M) (means : M → B.Assignment A)

/-- The three readings the translation promises, as statements about the target
structure: base symbols hold of original elements as they do in the instance,
the order symbol is the instance's order, and the meaning symbol of a variable,
at a value, is the assignment that value means. -/
structure ReadOn (S : ReadSyms L B Lt) (e : A → M) (means : M → B.Assignment A) : Prop where
  /-- A base symbol holds of original elements exactly as it does in the
  instance. -/
  base : ∀ {n : ℕ} (r : L.Relations n) (ts : Fin n → A),
    RelMap (S.base r) (fun i => e (ts i)) ↔ RelMap r ts
  /-- The order symbol is the instance's order. -/
  ord : ∀ ts : Fin 2 → A, RelMap S.ord (fun i => e (ts i)) ↔ ts 0 ≤ ts 1
  /-- The meaning symbol of a variable, at a value, is the assignment that value
  means. -/
  mean : ∀ (v : M) (i : B.ι) (ts : Fin (B.arity i) → A),
    RelMap (S.mean i) (Fin.cases v fun j => e (ts j)) ↔ means v i ts

variable {e means}

/-- The structure the translation induces on the original elements agrees,
symbol by symbol, with the base structure expanded by the `k` copies of the
block interpreted by the assignments the values mean. -/
theorem readEquiv_rel (h : ReadOn S e means) (vs : Fin k → M) {n : ℕ}
    (r : ((L.sum Language.order).sum (B.replicate k).lang).Relations n) (x : Fin n → A) :
    @RelMap _ A ((readHom S k).strucOn e vs) n r x ↔
      @RelMap _ A
        ((B.replicate k).structure₁ (L := L.sum Language.order)
          (B.replicateAssign fun i => means (vs i))) n r x := by
  cases r with
  | inl r' =>
    cases r' with
    | inl r'' => exact h.base r'' _
    | inr o =>
      cases o
      exact h.ord _
  | inr s =>
    refine Iff.trans (iff_of_eq (congrArg (RelMap (S.mean s.1.2)) (funext fun i => ?_)))
      (h.mean (vs s.1.1) s.1.2 fun j => x (Fin.cast s.2 j))
    induction i using Fin.cases <;> rfl

/-- **The structure the translation induces on the original elements is the one
the defining sentence is meant to be read in**: the base structure, its order,
and one copy of the block per value, interpreted by the assignment that value
means. -/
def readEquiv (h : ReadOn S e means) (vs : Fin k → M) :
    @Language.Equiv ((L.sum Language.order).sum (B.replicate k).lang) A A
      ((readHom S k).strucOn e vs)
      ((B.replicate k).structure₁ (L := L.sum Language.order)
        (B.replicateAssign fun i => means (vs i))) :=
  @Language.Equiv.mk _ A A ((readHom S k).strucOn e vs)
    ((B.replicate k).structure₁ (L := L.sum Language.order)
      (B.replicateAssign fun i => means (vs i)))
    (Equiv.refl A) (fun {_} f _ => isEmptyElim f) fun {_} r x => (readEquiv_rel h vs r x).symm

/-- **The translation, read among the original elements, says what the defining
sentence says**: the guarded image of a sentence holds of `k` invented values
exactly when the sentence holds in the instance, with the `k` copies of the
block interpreted by the assignments those values mean. -/
theorem realize_readHom (h : ReadOn S e means) {R : Lt.Relations 1}
    (hinj : Function.Injective e) (hR : ∀ x : M, RelMap R ![x] ↔ ∃ a : A, e a = x)
    (vs : Fin k → M)
    (φ : ((L.sum Language.order).sum (B.replicate k).lang).Sentence) :
    ((readHom S k).relOnSentenceF R φ).Realize vs ↔
      @Sentence.Realize _ A
        ((B.replicate k).structure₁ (L := L.sum Language.order)
          (B.replicateAssign fun i => means (vs i))) φ :=
  ((readHom S k).realize_relOnSentenceF R hinj hR φ).trans
    (realize_sentence_of_equiv (readEquiv h vs) φ)

/-! ### The same at a single copy -/

/-- The single-copy reading of
`DescriptiveComplexity.readEquiv_rel`. -/
theorem readEquiv₁_rel (h : ReadOn S e means) (v : M) {n : ℕ}
    (r : ((L.sum Language.order).sum B.lang).Relations n) (x : Fin n → A) :
    @RelMap _ A ((readHom₁ S).strucOn e fun _ => v) n r x ↔
      @RelMap _ A (B.structure₁ (L := L.sum Language.order) (means v)) n r x := by
  cases r with
  | inl r' =>
    cases r' with
    | inl r'' => exact h.base r'' _
    | inr o =>
      cases o
      exact h.ord _
  | inr s =>
    refine Iff.trans (iff_of_eq (congrArg (RelMap (S.mean s.1)) (funext fun i => ?_)))
      (h.mean v s.1 fun j => x (Fin.cast s.2 j))
    induction i using Fin.cases <;> rfl

/-- The single-copy reading of `DescriptiveComplexity.readEquiv`. -/
def readEquiv₁ (h : ReadOn S e means) (v : M) :
    @Language.Equiv ((L.sum Language.order).sum B.lang) A A
      ((readHom₁ S).strucOn e fun _ => v)
      (B.structure₁ (L := L.sum Language.order) (means v)) :=
  @Language.Equiv.mk _ A A ((readHom₁ S).strucOn e fun _ => v)
    (B.structure₁ (L := L.sum Language.order) (means v))
    (Equiv.refl A) (fun {_} f _ => isEmptyElim f) fun {_} r x => (readEquiv₁_rel h v r x).symm

/-- The single-copy reading of `DescriptiveComplexity.realize_readHom`: the
guarded image of a domain sentence holds of an invented value exactly when the
sentence holds in the instance, the block interpreted by the assignment that
value means. -/
theorem realize_readHom₁ (h : ReadOn S e means) {R : Lt.Relations 1}
    (hinj : Function.Injective e) (hR : ∀ x : M, RelMap R ![x] ↔ ∃ a : A, e a = x) (v : M)
    (φ : ((L.sum Language.order).sum B.lang).Sentence) :
    ((readHom₁ S).relOnSentenceF R φ).Realize (fun _ => v) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L.sum Language.order) (means v)) φ :=
  ((readHom₁ S).realize_relOnSentenceF R hinj hR φ).trans
    (realize_sentence_of_equiv (readEquiv₁ h v) φ)


end Realize

end DescriptiveComplexity
