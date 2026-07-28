/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Interp
import DescriptiveComplexity.Problems.FinSat.Fixpoint

/-!
# Reading the encoded sentence off the image

`DescriptiveComplexity.FinSat.Interp` builds the sentence `σ_A` and proves it
well formed (`DescriptiveComplexity.FinSat.image_isWF`); this file reads it back
as a *sentence* – what its nodes are, and which of them are children, binders and
literals of which – which is what the correctness of the reduction is then
stated and proved against (`TRAKHTENBROT.md` §5).

## The elements are points

Every relation of the image but the order demands canonically padded tuples
(`DescriptiveComplexity.FinSat.canonG`), and a canonical tuple *is* the padding
of its own prefix (`DescriptiveComplexity.pad_pref_of_canon`). So the elements
the sentence actually reads are exactly the
`DescriptiveComplexity.FinSat.ptOf a₀ t w`: a tag together with a tuple of the
tag's own length, padded with the least element. Elements that are not of that
form are junk – variables of the encoded sentence that no node binds and no
literal reads – and `DescriptiveComplexity.FinSat.eq_ptOf` says they are the
only ones, so every case analysis may assume a point.

This is the idiom the library uses wherever tagged tuples are compared: a `def`
for the element, an iff lemma for each relation it takes part in, and an
inversion lemma putting an arbitrary element in that form. Matching on a pair
literal at the type `FOInterpretation.Map` is ill-typed at the transparency
`rw` and `simp` work at, so the named constructor is not a convenience but a
requirement.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

section Hardness

variable {L : Language.{0, 0}} (B : SOBlock) (φ : ((newLang L).sum B.lang).Sentence)
variable {A : Type} [L.Structure A] [LinearOrder A]

/-! ### The points of the image -/

/-- **An element of the encoded sentence**: a tag, and a tuple of the tag's own
length padded with the least element `a₀`. -/
def ptOf (a₀ : A) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) : (finsatInterp B φ).Map A :=
  (t, pad a₀ w)

variable {a₀ : A}

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem ptOf_fst (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    (ptOf B φ a₀ t w).1 = t := rfl

omit [L.Structure A] [LinearOrder A] in
@[simp]
theorem ptOf_snd (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    (ptOf B φ a₀ t w).2 = pad a₀ w := rfl

omit [L.Structure A] in
theorem canon_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    Canon (tagDim B φ (ptOf B φ a₀ t w).1) (ptOf B φ a₀ t w).2 :=
  canon_pad ha₀ _ _

omit [L.Structure A] in
/-- **Junk is the only thing that is not a point**: an element whose tuple is
canonically padded for its tag is the point of its own prefix. -/
theorem eq_ptOf (ha₀ : IsBot a₀) {x : (finsatInterp B φ).Map A}
    (h : Canon (tagDim B φ x.1) x.2) :
    x = ptOf B φ a₀ x.1 (pref (tagDim_le_finsatDim B φ x.1) x.2) :=
  Prod.ext_iff.mpr ⟨rfl, (pad_pref_of_canon ha₀ _ h).symm⟩

omit [L.Structure A] [LinearOrder A] in
theorem ptOf_inj {t : FTag B φ} {w w' : Fin (tagDim B φ t) → A}
    (h : ptOf B φ a₀ t w = ptOf B φ a₀ t w') : w = w' := by
  have h2 : pad (D := finsatDim B φ) a₀ w = pad a₀ w' := congrArg Prod.snd h
  funext j
  have hj : (Fin.castLE (tagDim_le_finsatDim B φ t) j : ℕ) < tagDim B φ t := j.isLt
  have := congrFun h2 (Fin.castLE (tagDim_le_finsatDim B φ t) j)
  rwa [pad, pad, dif_pos hj, dif_pos hj, show (⟨(Fin.castLE (tagDim_le_finsatDim B φ t) j : ℕ),
    hj⟩ : Fin (tagDim B φ t)) = j from Fin.ext rfl] at this

omit [L.Structure A] [LinearOrder A] in
/-- The first coordinate of a point, which is where a tag of dimension one – the
prefix, its variable, a literal of a translated atom – holds its element. -/
theorem ptOf_c0 {t : FTag B φ} (hd : 0 < tagDim B φ t) (w : Fin (tagDim B φ t) → A) :
    (ptOf B φ a₀ t w).2 (c0 B φ) = w ⟨0, hd⟩ := by
  rw [ptOf_snd, pad, dif_pos (show ((c0 B φ : Fin (finsatDim B φ)) : ℕ) < tagDim B φ t from hd)]
  exact congrArg w (Fin.ext rfl)

omit [L.Structure A] [LinearOrder A] in
/-- The second coordinate of a point: where a distinctness literal of the
diagram holds the second of its two elements. -/
theorem ptOf_c1 {t : FTag B φ} (hd : 1 < tagDim B φ t) (w : Fin (tagDim B φ t) → A) :
    (ptOf B φ a₀ t w).2 (c1 B φ) = w ⟨1, hd⟩ := by
  rw [ptOf_snd, pad, dif_pos (show ((c1 B φ : Fin (finsatDim B φ)) : ℕ) < tagDim B φ t from hd)]
  exact congrArg w (Fin.ext rfl)

/-! ### The kinds of a node, at a point

The four kinds are decided by the tag alone
(`DescriptiveComplexity.FinSat.andTag` and its companions), so at a point they
are read off the tag and nothing else. -/

theorem andG_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    AndG (ptOf B φ a₀ t w) ↔ andTag B φ t :=
  ⟨fun h => ((andG_map_iff B φ _).mp h).2,
    fun h => (andG_map_iff B φ _).mpr ⟨canon_ptOf B φ ha₀ t w, h⟩⟩

theorem orG_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    OrG (ptOf B φ a₀ t w) ↔ orTag B φ t :=
  ⟨fun h => ((orG_map_iff B φ _).mp h).2,
    fun h => (orG_map_iff B φ _).mpr ⟨canon_ptOf B φ ha₀ t w, h⟩⟩

theorem allG_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    AllG (ptOf B φ a₀ t w) ↔ allTag B φ t :=
  ⟨fun h => ((allG_map_iff B φ _).mp h).2,
    fun h => (allG_map_iff B φ _).mpr ⟨canon_ptOf B φ ha₀ t w, h⟩⟩

theorem exG_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    ExG (ptOf B φ a₀ t w) ↔ exTag B φ t :=
  ⟨fun h => ((exG_map_iff B φ _).mp h).2,
    fun h => (exG_map_iff B φ _).mpr ⟨canon_ptOf B φ ha₀ t w, h⟩⟩

/-! ### The nodes of the encoded sentence, by name

One definition per tag, so that a statement about the sentence never mentions a
tuple that has to be reduced to be typed. Each is a
`DescriptiveComplexity.FinSat.ptOf`, definitionally, which is how the lemmas
below are proved: the work is done at `ptOf` – where the tags are literal
constructors, so `simp` can reduce the body of a defining formula – and
transported to the named node by `exact`, which unfolds at the transparency the
matching tactics do not. -/

variable {a₀ : A}

/-- The top conjunction of the sentence: the diagram and the translated
kernel. -/
def bodyPt (a₀ : A) : (finsatInterp B φ).Map A := ptOf B φ a₀ Tag.body fun _ => a₀

/-- The existential of the prefix binding the variable of `a`. -/
def prePt (a₀ a : A) : (finsatInterp B φ).Map A := ptOf B φ a₀ Tag.pre fun _ => a

/-- The variable that existential binds. -/
def pvarPt (a₀ a : A) : (finsatInterp B φ).Map A := ptOf B φ a₀ Tag.pvar fun _ => a

/-- The distinctness literal `x_a ≠ x_b` of the diagram. -/
def neqPt (a₀ a b : A) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b

/-- The variable naming a de Bruijn level of the kernel. -/
def dbvarPt (a₀ : A) (l : Fin (Tseitin.maxCtx φ)) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.dbvar l) fun _ => a₀

/-- The relation symbol of a relation variable of the block. -/
def symPt (a₀ : A) (i : B.ι) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.sym i) fun _ => a₀

/-- An argument position of the relation symbols. -/
def aposPt (a₀ : A) (j : Fin (finsatDim B φ)) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.apos j) fun _ => a₀

/-- The translation of the subformula at a position, at a polarity. -/
def ndPt (a₀ : A) (p : Pos B φ) (pol : Bool) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.nd p pol) fun _ => a₀

/-- One tuple of the translation of an atom the sentence may not mention. -/
def atupPt (a₀ : A) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) : (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.atup p pol) w

/-- One equality literal inside such a tuple. -/
def alitPt (a₀ : A) (p : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ)) (a : A) :
    (finsatInterp B φ).Map A :=
  ptOf B φ a₀ (Tag.alit p pol j) fun _ => a

/-! ### The relations that read the tuples

`child`, `bind` and the two equality literals are not decided by the tags alone:
their bodies compare the elements the tuples hold. Each is bridged to its named
body (`DescriptiveComplexity.FinSat.childBodyF` and its companions) read at the
valuation the interpretation supplies, and then computed at the tags it is
defined for.

The bridge is stated **at points**, not at two arbitrary elements projected with
`.1`: a projection out of `FOInterpretation.Map` is ill-typed at the
transparency `simp` matches at, so `childBodyF B φ g.1 c.1` would never reduce
even with both tags known. At a point the tag is syntactically there. -/

/-- The valuation a unary defining formula of the image is read at. -/
def val₁ (x : (finsatInterp B φ).Map A) : Fin 1 × Fin (finsatDim B φ) → A :=
  fun q => ((![x] : Fin 1 → (finsatInterp B φ).Map A) q.1).2 q.2

/-- The valuation a binary defining formula of the image is read at. -/
def val₂ (x y : (finsatInterp B φ).Map A) : Fin 2 × Fin (finsatDim B φ) → A :=
  fun q => ((![x, y] : Fin 2 → (finsatInterp B φ).Map A) q.1).2 q.2

/-- The valuation a ternary defining formula of the image is read at. -/
def val₃ (x y z : (finsatInterp B φ).Map A) : Fin 3 × Fin (finsatDim B φ) → A :=
  fun q => ((![x, y, z] : Fin 3 → (finsatInterp B φ).Map A) q.1).2 q.2

/-- The child relation at a pair of points: canonicity is automatic, so only the
body is left. -/
theorem childG_ptOf_iff (ha₀ : IsBot a₀) (t t' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    ChildG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') ↔
      (childBodyF B φ t t').Realize (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w')) := by
  constructor
  · intro h
    exact ((realize_childFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
        Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mp h).2
  · intro h
    refine (realize_childFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
        Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mpr ⟨?_, h⟩
    intro i
    fin_cases i
    · exact canon_ptOf B φ ha₀ t w
    · exact canon_ptOf B φ ha₀ t' w'

/-! ### The child relation, node by node -/

/-- **The existential prefix is a chain**: the node of `a` has the node of the
next element of the input order as its child. -/
theorem childG_pre_pre (ha₀ : IsBot a₀) (a b : A) :
    ChildG (prePt B φ a₀ a) (prePt B φ a₀ b) ↔ a < b ∧ ∀ x : A, ¬(a < x ∧ x < b) := by
  have key := childG_ptOf_iff B φ ha₀ Tag.pre Tag.pre (fun _ => a) (fun _ => b)
  simp only [childBodyF, realize_succF] at key
  have h0 : val₂ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (ptOf B φ a₀ Tag.pre fun _ => b)
      (0, c0 B φ) = a := ptOf_c0 B φ (t := Tag.pre) Nat.one_pos _
  have h1 : val₂ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (ptOf B φ a₀ Tag.pre fun _ => b)
      (1, c0 B φ) = b := ptOf_c0 B φ (t := Tag.pre) Nat.one_pos _
  rw [h0, h1] at key
  exact key

/-- **The last node of the prefix hands over the top conjunction**: the node of
the greatest element of the input order. -/
theorem childG_pre_body (ha₀ : IsBot a₀) (a : A) :
    ChildG (prePt B φ a₀ a) (bodyPt B φ a₀) ↔ ∀ x : A, x ≤ a := by
  have key := childG_ptOf_iff B φ ha₀ Tag.pre Tag.body (fun _ => a) (fun _ => a₀)
  simp only [childBodyF, realize_maxF] at key
  have h0 : val₂ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (ptOf B φ a₀ Tag.body fun _ => a₀)
      (0, c0 B φ) = a := ptOf_c0 B φ (t := Tag.pre) Nat.one_pos _
  rw [h0] at key
  exact key

/-- **The top conjunction takes the distinctness literals of the diagram** – and
only those of *distinct* pairs: the literal of `(a, a)` says `x_a ≠ x_a`, which
no environment satisfies, so it must not be a conjunct. -/
theorem childG_body_neq (ha₀ : IsBot a₀) (a b : A) :
    ChildG (bodyPt B φ a₀) (neqPt B φ a₀ a b) ↔ a ≠ b := by
  have key := childG_ptOf_iff B φ ha₀ Tag.body Tag.neq (fun _ => a₀)
    (fun j => if (j : ℕ) = 0 then a else b)
  simp only [childBodyF, Formula.realize_not, Formula.realize_equal, Term.realize_var] at key
  have h1 : val₂ B φ (ptOf B φ a₀ Tag.body fun _ => a₀)
      (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b) (1, c0 B φ) = a :=
    ptOf_c0 B φ (t := Tag.neq) (by norm_num : (0 : ℕ) < 2) _
  have h2 : val₂ B φ (ptOf B φ a₀ Tag.body fun _ => a₀)
      (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b) (1, c1 B φ) = b :=
    ptOf_c1 B φ (t := Tag.neq) (by norm_num : (1 : ℕ) < 2) _
  rw [h1, h2] at key
  exact key

/-- The top conjunction takes the root of the translated kernel, and nothing
else of the kernel. -/
theorem childG_body_nd (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool) :
    ChildG (bodyPt B φ a₀) (ndPt B φ a₀ p pol) ↔ pol = true ∧ p = rootPos B φ := by
  classical
  have key := childG_ptOf_iff B φ ha₀ Tag.body (Tag.nd p pol) (fun _ => a₀) (fun _ => a₀)
  simp only [childBodyF] at key
  refine key.trans ?_
  by_cases h : pol = true ∧ p = rootPos B φ
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

/-- **Inside the translated kernel the child relation follows
`DescriptiveComplexity.FinSat.kidOf`**, the polarity flipping exactly at the
premise of an implication. -/
theorem childG_nd_nd (ha₀ : IsBot a₀) (p q : Pos B φ) (pol pol' : Bool) :
    ChildG (ndPt B φ a₀ p pol) (ndPt B φ a₀ q pol') ↔ kidOf φ p.2 q.2 = some (xor pol pol') := by
  classical
  have key := childG_ptOf_iff B φ ha₀ (Tag.nd p pol) (Tag.nd q pol') (fun _ => a₀) (fun _ => a₀)
  simp only [childBodyF] at key
  refine key.trans ?_
  by_cases h : kidOf φ p.2 q.2 = some (xor pol pol')
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

/-- A translated atom takes the tuple nodes where it holds: **the one place the
reduction reads the input structure**, and the reason the encoded sentence never
mentions a symbol of the input vocabulary. -/
theorem childG_nd_atup (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) :
    ChildG (ndPt B φ a₀ p pol) (atupPt B φ a₀ p pol w) ↔
      (inAtomF B φ p).Realize
        (val₂ B φ (ptOf B φ a₀ (Tag.nd p pol) fun _ => a₀) (ptOf B φ a₀ (Tag.atup p pol) w)) := by
  classical
  have key := childG_ptOf_iff B φ ha₀ (Tag.nd p pol) (Tag.atup p pol) (fun _ => a₀) w
  rw [childBodyF] at key
  refine key.trans ?_
  rw [if_pos ⟨rfl, rfl⟩]

/-- Each tuple node takes one equality literal per argument position, binding
that argument to the variable of the corresponding element. -/
theorem childG_atup_alit (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) (j : Fin (finsatDim B φ)) (a : A) :
    ChildG (atupPt B φ a₀ p pol w) (alitPt B φ a₀ p pol j a) ↔
      (j : ℕ) < inArity B φ p ∧ pad a₀ w j = a := by
  classical
  have key := childG_ptOf_iff B φ ha₀ (Tag.atup p pol) (Tag.alit p pol j) w (fun _ => a)
  rw [childBodyF] at key
  refine key.trans ?_
  by_cases h : (j : ℕ) < inArity B φ p
  · rw [if_pos ⟨rfl, rfl, h⟩, Formula.realize_equal, Term.realize_var, Term.realize_var]
    have h1 : val₂ B φ (ptOf B φ a₀ (Tag.atup p pol) w)
        (ptOf B φ a₀ (Tag.alit p pol j) fun _ => a) (1, c0 B φ) = a :=
      ptOf_c0 B φ (t := Tag.alit p pol j) Nat.one_pos _
    rw [h1]
    exact ⟨fun hv => ⟨h, hv⟩, fun hv => hv.2⟩
  · rw [if_neg (fun hc => h hc.2.2), Formula.realize_bot]
    exact iff_of_false not_false fun hc => h hc.1

/-! ### The binders, the literals and the root -/

theorem bindG_ptOf_iff (ha₀ : IsBot a₀) (t t' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    BindG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') ↔
      (bindBodyF B φ t t').Realize (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w')) := by
  constructor
  · intro h
    exact ((realize_bindFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
        Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mp h).2
  · intro h
    refine (realize_bindFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
        Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mpr ⟨?_, h⟩
    intro i
    fin_cases i
    · exact canon_ptOf B φ ha₀ t w
    · exact canon_ptOf B φ ha₀ t' w'

/-- Each node of the prefix binds its own variable. -/
theorem bindG_pre_pvar (ha₀ : IsBot a₀) (a b : A) :
    BindG (prePt B φ a₀ a) (pvarPt B φ a₀ b) ↔ a = b := by
  have key := bindG_ptOf_iff B φ ha₀ Tag.pre Tag.pvar (fun _ => a) (fun _ => b)
  simp only [bindBodyF, Formula.realize_equal, Term.realize_var] at key
  have h0 : val₂ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (0, c0 B φ) = a := ptOf_c0 B φ (t := Tag.pre) Nat.one_pos _
  have h1 : val₂ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (1, c0 B φ) = b := ptOf_c0 B φ (t := Tag.pvar) Nat.one_pos _
  rw [h0, h1] at key
  exact key

/-- A quantifier of the kernel binds the variable of the de Bruijn level it
introduces. -/
theorem bindG_nd_dbvar (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (l : Fin (Tseitin.maxCtx φ)) :
    BindG (ndPt B φ a₀ p pol) (dbvarPt B φ a₀ l) ↔ qLevel B φ p = some (l : ℕ) := by
  classical
  have key := bindG_ptOf_iff B φ ha₀ (Tag.nd p pol) (Tag.dbvar l) (fun _ => a₀) (fun _ => a₀)
  simp only [bindBodyF] at key
  refine key.trans ?_
  by_cases h : qLevel B φ p = some (l : ℕ)
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

theorem neqG_ptOf_iff (ha₀ : IsBot a₀) (t t' t'' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) (w'' : Fin (tagDim B φ t'') → A) :
    NeqG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'') ↔
      (neqBodyF B φ t t' t'').Realize
        (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'')) := by
  constructor
  · intro h
    exact ((realize_neqFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
        Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mp h).2
  · intro h
    refine (realize_neqFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
        Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mpr ⟨?_, h⟩
    intro i
    fin_cases i
    · exact canon_ptOf B φ ha₀ t w
    · exact canon_ptOf B φ ha₀ t' w'
    · exact canon_ptOf B φ ha₀ t'' w''

/-- **The diagram**: the literal of the pair `(a, b)` says that the variables of
`a` and of `b` are distinct, and it exists only for `a ≠ b`. -/
theorem neqG_neq_pvar (ha₀ : IsBot a₀) (a b x y : A) :
    NeqG (neqPt B φ a₀ a b) (pvarPt B φ a₀ x) (pvarPt B φ a₀ y) ↔ a = x ∧ b = y ∧ a ≠ b := by
  have key := neqG_ptOf_iff B φ ha₀ Tag.neq Tag.pvar Tag.pvar
    (fun j => if (j : ℕ) = 0 then a else b) (fun _ => x) (fun _ => y)
  simp only [neqBodyF, Formula.realize_inf, Formula.realize_equal, Formula.realize_not,
    Term.realize_var] at key
  have h0 : val₃ B φ (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b)
      (ptOf B φ a₀ Tag.pvar fun _ => x) (ptOf B φ a₀ Tag.pvar fun _ => y) (0, c0 B φ) = a :=
    ptOf_c0 B φ (t := Tag.neq) (by norm_num : (0 : ℕ) < 2) _
  have h0' : val₃ B φ (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b)
      (ptOf B φ a₀ Tag.pvar fun _ => x) (ptOf B φ a₀ Tag.pvar fun _ => y) (0, c1 B φ) = b :=
    ptOf_c1 B φ (t := Tag.neq) (by norm_num : (1 : ℕ) < 2) _
  have h1 : val₃ B φ (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b)
      (ptOf B φ a₀ Tag.pvar fun _ => x) (ptOf B φ a₀ Tag.pvar fun _ => y) (1, c0 B φ) = x :=
    ptOf_c0 B φ (t := Tag.pvar) Nat.one_pos _
  have h2 : val₃ B φ (ptOf B φ a₀ Tag.neq fun j => if (j : ℕ) = 0 then a else b)
      (ptOf B φ a₀ Tag.pvar fun _ => x) (ptOf B φ a₀ Tag.pvar fun _ => y) (2, c0 B φ) = y :=
    ptOf_c0 B φ (t := Tag.pvar) Nat.one_pos _
  rw [h0, h0', h1, h2] at key
  exact key

theorem rootG_ptOf_iff (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A) :
    RootG (ptOf B φ a₀ t w) ↔
      (rootBodyF B φ t).Realize (val₁ B φ (ptOf B φ a₀ t w)) := by
  constructor
  · intro h
    exact ((realize_rootFml B φ
      (fun i => ((![ptOf B φ a₀ t w] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      (val₁ B φ (ptOf B φ a₀ t w))).mp h).2
  · intro h
    refine (realize_rootFml B φ
      (fun i => ((![ptOf B φ a₀ t w] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      (val₁ B φ (ptOf B φ a₀ t w))).mpr ⟨?_, h⟩
    intro i
    fin_cases i
    exact canon_ptOf B φ ha₀ t w

/-- **The root of the encoded sentence** is the node of the prefix binding the
least element of the input order: the outermost existential. -/
theorem rootG_pre (ha₀ : IsBot a₀) (a : A) :
    RootG (prePt B φ a₀ a) ↔ ∀ x : A, a ≤ x := by
  have key := rootG_ptOf_iff B φ ha₀ Tag.pre (fun _ => a)
  simp only [rootBodyF, realize_minF] at key
  have h0 : val₁ B φ (ptOf B φ a₀ Tag.pre fun _ => a) (0, c0 B φ) = a :=
    ptOf_c0 B φ (t := Tag.pre) Nat.one_pos _
  rw [h0] at key
  exact key

/-! ### Inversion: these are the only children

The truth definition quantifies over *all* the children of a node, so reading
`σ_A` needs the converse of the lemmas above: which elements of the image are
children of a given node, and no others. Everything rests on canonicity – a
relation of the image holds only of canonically padded tuples, and those are the
points – so an arbitrary element can always be replaced by a point, after which
the tag alone decides. -/

omit [L.Structure A] in
/-- Every canonically padded element is a point. -/
theorem exists_ptOf (ha₀ : IsBot a₀) {x : (finsatInterp B φ).Map A}
    (h : Canon (tagDim B φ x.1) x.2) :
    ∃ (t : FTag B φ) (w : Fin (tagDim B φ t) → A), x = ptOf B φ a₀ t w :=
  ⟨x.1, _, eq_ptOf B φ ha₀ h⟩

theorem canon_of_childG_right {g c : (finsatInterp B φ).Map A} (h : ChildG g c) :
    Canon (tagDim B φ c.1) c.2 :=
  ((realize_childFml B φ (fun i => ((![g, c] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    (val₂ B φ g c)).mp h).1 1

theorem canon_of_bindG_right {g x : (finsatInterp B φ).Map A} (h : BindG g x) :
    Canon (tagDim B φ x.1) x.2 :=
  ((realize_bindFml B φ (fun i => ((![g, x] : Fin 2 → (finsatInterp B φ).Map A) i).1)
    (val₂ B φ g x)).mp h).1 1

/-- **A child is a point**: the child relation of the image never leaves the
elements the sentence reads. -/
theorem childG_iff_pt (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (c : (finsatInterp B φ).Map A) :
    ChildG (ptOf B φ a₀ t w) c ↔ ∃ (t' : FTag B φ) (w' : Fin (tagDim B φ t') → A),
      c = ptOf B φ a₀ t' w' ∧ ChildG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') := by
  constructor
  · intro h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ (canon_of_childG_right B φ h)
    exact ⟨t', w', rfl, h⟩
  · rintro ⟨t', w', rfl, h⟩
    exact h

/-- A tag pair the child relation is not defined at has no edge. -/
theorem not_childG_ptOf (ha₀ : IsBot a₀) (t t' : FTag B φ)
    (hb : childBodyF B φ t t' = ⊥) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    ¬ChildG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') := by
  rw [childG_ptOf_iff B φ ha₀, hb]
  exact not_false

/-! The tuples of the tags of dimension zero, one and two, read out: what the
inversion lemmas put an arbitrary tuple back into. -/

omit [L.Structure A] [LinearOrder A] in
theorem tup_zero_eq {t : FTag B φ} (h : tagDim B φ t = 0) (w w' : Fin (tagDim B φ t) → A) :
    w = w' :=
  funext fun j => absurd (lt_of_lt_of_le j.isLt (le_of_eq h)) (Nat.not_lt_zero _)

omit [L.Structure A] [LinearOrder A] in
theorem tup_one_eq {t : FTag B φ} (h : tagDim B φ t = 1) (w : Fin (tagDim B φ t) → A)
    (h0 : 0 < tagDim B φ t) : w = fun _ => w ⟨0, h0⟩ := by
  funext j
  have hj := lt_of_lt_of_le j.isLt (le_of_eq h)
  have hj0 : (j : ℕ) = 0 := by omega
  exact congrArg w (Fin.ext hj0)

omit [L.Structure A] [LinearOrder A] in
theorem tup_two_eq {t : FTag B φ} (h : tagDim B φ t = 2) (w : Fin (tagDim B φ t) → A)
    (h0 : 0 < tagDim B φ t) (h1 : 1 < tagDim B φ t) :
    w = fun j : Fin (tagDim B φ t) => if (j : ℕ) = 0 then w ⟨0, h0⟩ else w ⟨1, h1⟩ := by
  funext j
  have hj := lt_of_lt_of_le j.isLt (le_of_eq h)
  by_cases hj0 : (j : ℕ) = 0
  · rw [if_pos hj0]
    exact congrArg w (Fin.ext hj0)
  · rw [if_neg hj0]
    have hj1 : (j : ℕ) = 1 := by omega
    exact congrArg w (Fin.ext hj1)

/-- **The children of the top conjunction**: every distinctness literal of the
diagram, and the root of the translated kernel at polarity `true`. -/
theorem childG_body_iff (ha₀ : IsBot a₀) (c : (finsatInterp B φ).Map A) :
    ChildG (bodyPt B φ a₀) c ↔
      (∃ a b : A, a ≠ b ∧ c = neqPt B φ a₀ a b) ∨ c = ndPt B φ a₀ (rootPos B φ) true := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (childG_iff_pt B φ ha₀ Tag.body (fun _ => a₀) c).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨p, pol⟩ | ⟨p, pol⟩ | ⟨p, pol, j⟩ <;>
      try exact absurd h (not_childG_ptOf B φ ha₀ _ _ rfl _ _)
    · have hw := tup_two_eq B φ (t := Tag.neq) rfl w' (by norm_num : (0 : ℕ) < 2)
        (by norm_num : (1 : ℕ) < 2)
      rw [hw] at h
      exact Or.inl ⟨_, _, (childG_body_neq B φ ha₀ _ _).mp h,
        congrArg (ptOf B φ a₀ Tag.neq) hw⟩
    · have hw : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
      subst hw
      obtain ⟨rfl, rfl⟩ := (childG_body_nd B φ ha₀ p pol).mp h
      exact Or.inr rfl
  · rintro (⟨a, b, hab, rfl⟩ | rfl)
    · exact (childG_body_neq B φ ha₀ a b).mpr hab
    · exact (childG_body_nd B φ ha₀ (rootPos B φ) true).mpr ⟨rfl, rfl⟩

/-- **The children of a node of the existential prefix**: the node of the next
element of the input order, and – at the greatest element – the top
conjunction. -/
theorem childG_pre_iff (ha₀ : IsBot a₀) (a : A) (c : (finsatInterp B φ).Map A) :
    ChildG (prePt B φ a₀ a) c ↔
      (∃ b : A, c = prePt B φ a₀ b ∧ a < b ∧ ∀ x : A, ¬(a < x ∧ x < b)) ∨
        (c = bodyPt B φ a₀ ∧ ∀ x : A, x ≤ a) := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (childG_iff_pt B φ ha₀ Tag.pre (fun _ => a) c).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨p, pol⟩ | ⟨p, pol⟩ | ⟨p, pol, j⟩ <;>
      try exact absurd h (not_childG_ptOf B φ ha₀ _ _ rfl _ _)
    · have hw : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
      subst hw
      exact Or.inr ⟨rfl, (childG_pre_body B φ ha₀ a).mp h⟩
    · have hw := tup_one_eq B φ (t := Tag.pre) rfl w' (by norm_num : (0 : ℕ) < 1)
      rw [hw] at h
      exact Or.inl ⟨_, congrArg (ptOf B φ a₀ Tag.pre) hw, (childG_pre_pre B φ ha₀ a _).mp h⟩
  · rintro (⟨b, rfl, hb⟩ | ⟨rfl, hm⟩)
    · exact (childG_pre_pre B φ ha₀ a b).mpr hb
    · exact (childG_pre_body B φ ha₀ a).mpr hm

/-! ### The literals and the atoms, node by node

The remaining clauses of the truth definition: the equality literals of the
kernel and of the translated atoms, and the atoms of the relation variables –
the only genuine atoms of the encoded sentence – with their symbols, their
argument positions and their signature. All but the literals of a translated
atom are decided by the tags. -/

theorem eqG_ptOf_iff (ha₀ : IsBot a₀) (t t' t'' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) (w'' : Fin (tagDim B φ t'') → A) :
    EqG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'') ↔
      (eqBodyF B φ t t' t'').Realize
        (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'')) := by
  constructor
  · intro h
    exact ((realize_eqFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
        Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mp h).2
  · intro h
    refine (realize_eqFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
        Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mpr ⟨?_, h⟩
    intro i
    fin_cases i
    · exact canon_ptOf B φ ha₀ t w
    · exact canon_ptOf B φ ha₀ t' w'
    · exact canon_ptOf B φ ha₀ t'' w''

/-- A positive equality of the kernel, between the variables of two de Bruijn
levels. -/
theorem eqG_nd_dbvar (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (l₁ l₂ : Fin (Tseitin.maxCtx φ)) :
    EqG (ndPt B φ a₀ p pol) (dbvarPt B φ a₀ l₁) (dbvarPt B φ a₀ l₂) ↔
      pol = true ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)) := by
  classical
  have key := eqG_ptOf_iff B φ ha₀ (Tag.nd p pol) (Tag.dbvar l₁) (Tag.dbvar l₂)
    (fun _ => a₀) (fun _ => a₀) (fun _ => a₀)
  simp only [eqBodyF] at key
  refine key.trans ?_
  by_cases h : pol = true ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ))
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

/-- A negated equality of the kernel. -/
theorem neqG_nd_dbvar (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (l₁ l₂ : Fin (Tseitin.maxCtx φ)) :
    NeqG (ndPt B φ a₀ p pol) (dbvarPt B φ a₀ l₁) (dbvarPt B φ a₀ l₂) ↔
      pol = false ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)) := by
  classical
  have key := neqG_ptOf_iff B φ ha₀ (Tag.nd p pol) (Tag.dbvar l₁) (Tag.dbvar l₂)
    (fun _ => a₀) (fun _ => a₀) (fun _ => a₀)
  simp only [neqBodyF] at key
  refine key.trans ?_
  by_cases h : pol = false ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ))
  · rw [if_pos h, Formula.realize_top]
    exact iff_of_true trivial h
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false h

/-- **A literal of a translated atom**: the argument of the atom at one position
is the variable of the element that tuple holds there. -/
theorem eqG_alit (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ))
    (a b : A) (l : Fin (Tseitin.maxCtx φ)) :
    EqG (alitPt B φ a₀ p pol j a) (dbvarPt B φ a₀ l) (pvarPt B φ a₀ b) ↔
      (pol = true ∧ inArg B φ p (j : ℕ) = some (l : ℕ)) ∧ a = b := by
  classical
  have key := eqG_ptOf_iff B φ ha₀ (Tag.alit p pol j) (Tag.dbvar l) Tag.pvar
    (fun _ => a) (fun _ => a₀) (fun _ => b)
  simp only [eqBodyF] at key
  have h0 : val₃ B φ (ptOf B φ a₀ (Tag.alit p pol j) fun _ => a)
      (ptOf B φ a₀ (Tag.dbvar l) fun _ => a₀) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (0, c0 B φ) = a := ptOf_c0 B φ (t := Tag.alit p pol j) Nat.one_pos _
  have h2 : val₃ B φ (ptOf B φ a₀ (Tag.alit p pol j) fun _ => a)
      (ptOf B φ a₀ (Tag.dbvar l) fun _ => a₀) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (2, c0 B φ) = b := ptOf_c0 B φ (t := Tag.pvar) Nat.one_pos _
  refine key.trans ?_
  by_cases h : pol = true ∧ inArg B φ p (j : ℕ) = some (l : ℕ)
  · rw [if_pos h, Formula.realize_equal, Term.realize_var, Term.realize_var, h0, h2]
    exact ⟨fun hv => ⟨h, hv⟩, fun hv => hv.2⟩
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false fun hc => h hc.1

/-- The same, negated: what a tuple of a *negatively* translated atom asks. -/
theorem neqG_alit (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ))
    (a b : A) (l : Fin (Tseitin.maxCtx φ)) :
    NeqG (alitPt B φ a₀ p pol j a) (dbvarPt B φ a₀ l) (pvarPt B φ a₀ b) ↔
      (pol = false ∧ inArg B φ p (j : ℕ) = some (l : ℕ)) ∧ a = b := by
  classical
  have key := neqG_ptOf_iff B φ ha₀ (Tag.alit p pol j) (Tag.dbvar l) Tag.pvar
    (fun _ => a) (fun _ => a₀) (fun _ => b)
  simp only [neqBodyF] at key
  have h0 : val₃ B φ (ptOf B φ a₀ (Tag.alit p pol j) fun _ => a)
      (ptOf B φ a₀ (Tag.dbvar l) fun _ => a₀) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (0, c0 B φ) = a := ptOf_c0 B φ (t := Tag.alit p pol j) Nat.one_pos _
  have h2 : val₃ B φ (ptOf B φ a₀ (Tag.alit p pol j) fun _ => a)
      (ptOf B φ a₀ (Tag.dbvar l) fun _ => a₀) (ptOf B φ a₀ Tag.pvar fun _ => b)
      (2, c0 B φ) = b := ptOf_c0 B φ (t := Tag.pvar) Nat.one_pos _
  refine key.trans ?_
  by_cases h : pol = false ∧ inArg B φ p (j : ℕ) = some (l : ℕ)
  · rw [if_pos h, Formula.realize_equal, Term.realize_var, Term.realize_var, h0, h2]
    exact ⟨fun hv => ⟨h, hv⟩, fun hv => hv.2⟩
  · rw [if_neg h, Formula.realize_bot]
    exact iff_of_false not_false fun hc => h hc.1

/-! The atoms of the relation variables, which the encoded sentence does name:
all four relations are decided by the tags. -/

theorem posG_ptOf (ha₀ : IsBot a₀) (t t' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    PosG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') ↔ atomTag B φ true t t' := by
  refine ⟨fun h => ((realize_posFml B φ (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
      Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mp h).2, fun h => ?_⟩
  refine (realize_posFml B φ (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
    Fin 2 → (finsatInterp B φ).Map A) i).1)
    (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mpr ⟨?_, h⟩
  intro i
  fin_cases i
  · exact canon_ptOf B φ ha₀ t w
  · exact canon_ptOf B φ ha₀ t' w'

theorem negG_ptOf (ha₀ : IsBot a₀) (t t' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    NegG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') ↔ atomTag B φ false t t' := by
  refine ⟨fun h => ((realize_negFml B φ (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
      Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mp h).2, fun h => ?_⟩
  refine (realize_negFml B φ (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
    Fin 2 → (finsatInterp B φ).Map A) i).1)
    (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mpr ⟨?_, h⟩
  intro i
  fin_cases i
  · exact canon_ptOf B φ ha₀ t w
  · exact canon_ptOf B φ ha₀ t' w'

theorem argG_ptOf (ha₀ : IsBot a₀) (t t' t'' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) (w'' : Fin (tagDim B φ t'') → A) :
    ArgG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'') ↔
      argTag B φ t t' t'' := by
  refine ⟨fun h => ((realize_argFml B φ
      (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
        Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mp h).2,
    fun h => ?_⟩
  refine (realize_argFml B φ
    (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w', ptOf B φ a₀ t'' w''] :
      Fin 3 → (finsatInterp B φ).Map A) i).1)
    (val₃ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w''))).mpr ⟨?_, h⟩
  intro i
  fin_cases i
  · exact canon_ptOf B φ ha₀ t w
  · exact canon_ptOf B φ ha₀ t' w'
  · exact canon_ptOf B φ ha₀ t'' w''

theorem sigG_ptOf (ha₀ : IsBot a₀) (t t' : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    SigG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') ↔ sigTag B φ t t' := by
  refine ⟨fun h => ((realize_sigFml B φ (fun i => ((![ptOf B φ a₀ t w, ptOf B φ a₀ t' w'] :
      Fin 2 → (finsatInterp B φ).Map A) i).1)
      (val₂ B φ (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w'))).mp h).2, fun h => ?_⟩
  exact sigG_of B φ _ _ (canon_ptOf B φ ha₀ t w) (canon_ptOf B φ ha₀ t' w') h

/-! ### The children of the translated kernel

Inside the kernel a node takes the nodes of its children positions – the
polarity flipping exactly at the premise of an implication – and, where the
kernel carries an atom the sentence may not mention, the tuple nodes of that
atom, each of which takes one equality literal per argument. A tuple node of
*another* position is never a child, which is what makes the translation of two
atoms independent. -/

/-- A kernel node only takes tuple nodes of its own position and polarity. -/
theorem eq_of_childG_nd_atup (ha₀ : IsBot a₀) {p q : Pos B φ} {pol pol' : Bool}
    (w : Fin (tagDim B φ (Tag.atup q pol')) → A)
    (h : ChildG (ptOf B φ a₀ (Tag.nd p pol) (fun _ => a₀))
      (ptOf B φ a₀ (Tag.atup q pol') w)) : p = q ∧ pol = pol' := by
  classical
  by_contra hc
  rw [childG_ptOf_iff B φ ha₀, childBodyF, if_neg hc] at h
  exact h

/-- A tuple node only takes literals of its own position and polarity. -/
theorem eq_of_childG_atup_alit (ha₀ : IsBot a₀) {p q : Pos B φ} {pol pol' : Bool}
    {j : Fin (finsatDim B φ)} (w : Fin (tagDim B φ (Tag.atup p pol)) → A)
    (w' : Fin (tagDim B φ (Tag.alit q pol' j)) → A)
    (h : ChildG (ptOf B φ a₀ (Tag.atup p pol) w) (ptOf B φ a₀ (Tag.alit q pol' j) w')) :
    p = q ∧ pol = pol' := by
  classical
  by_contra hc
  rw [childG_ptOf_iff B φ ha₀, childBodyF,
    if_neg (fun hcond : p = q ∧ pol = pol' ∧ (j : ℕ) < inArity B φ p =>
      hc ⟨hcond.1, hcond.2.1⟩)] at h
  exact h

/-- **The children of a node of the translated kernel.** -/
theorem childG_nd_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (c : (finsatInterp B φ).Map A) :
    ChildG (ndPt B φ a₀ p pol) c ↔
      (∃ (q : Pos B φ) (pol' : Bool), kidOf φ p.2 q.2 = some (xor pol pol') ∧
        c = ndPt B φ a₀ q pol') ∨
      (∃ w : Fin (tagDim B φ (Tag.atup p pol)) → A,
        ChildG (ndPt B φ a₀ p pol) (atupPt B φ a₀ p pol w) ∧ c = atupPt B φ a₀ p pol w) := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (childG_iff_pt B φ ha₀ (Tag.nd p pol) (fun _ => a₀) c).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
      try exact absurd h (not_childG_ptOf B φ ha₀ _ _ rfl _ _)
    · have hw : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
      subst hw
      exact Or.inl ⟨q, pol', (childG_nd_nd B φ ha₀ p q pol pol').mp h, rfl⟩
    · obtain ⟨rfl, rfl⟩ := eq_of_childG_nd_atup B φ ha₀ w' h
      exact Or.inr ⟨w', h, rfl⟩
  · rintro (⟨q, pol', hk, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact (childG_nd_nd B φ ha₀ p q pol pol').mpr hk
    · exact hw

/-- **The children of a tuple node**: one equality literal per argument
position, binding that argument to the variable of the element the tuple holds
there. -/
theorem childG_atup_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) (c : (finsatInterp B φ).Map A) :
    ChildG (atupPt B φ a₀ p pol w) c ↔
      ∃ j : Fin (finsatDim B φ), (j : ℕ) < inArity B φ p ∧
        c = alitPt B φ a₀ p pol j (pad a₀ w j) := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (childG_iff_pt B φ ha₀ (Tag.atup p pol) w c).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
      try exact absurd h (not_childG_ptOf B φ ha₀ _ _ rfl _ _)
    obtain ⟨rfl, rfl⟩ := eq_of_childG_atup_alit B φ ha₀ w w' h
    have hw := tup_one_eq B φ (t := Tag.alit p pol j) rfl w' (by norm_num : (0 : ℕ) < 1)
    rw [hw] at h
    obtain ⟨hj, hv⟩ := (childG_atup_alit B φ ha₀ p pol w j _).mp h
    exact ⟨j, hj, by rw [hw, ← hv]; rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact (childG_atup_alit B φ ha₀ p pol w j (pad a₀ w j)).mpr ⟨hj, rfl⟩

/-! ### The binders of a quantifier node

The quantifier clauses of the truth definition quantify over the variables a
node binds, so they need the converse of
`DescriptiveComplexity.FinSat.bindG_nd_dbvar`: a quantifier of the kernel binds
the variable of the de Bruijn level it introduces, and nothing else. -/

/-- **A binder is a point.** -/
theorem bindG_iff_pt (ha₀ : IsBot a₀) (t : FTag B φ) (w : Fin (tagDim B φ t) → A)
    (x : (finsatInterp B φ).Map A) :
    BindG (ptOf B φ a₀ t w) x ↔ ∃ (t' : FTag B φ) (w' : Fin (tagDim B φ t') → A),
      x = ptOf B φ a₀ t' w' ∧ BindG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') := by
  constructor
  · intro h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ (canon_of_bindG_right B φ h)
    exact ⟨t', w', rfl, h⟩
  · rintro ⟨t', w', rfl, h⟩
    exact h

/-- A tag pair the binding relation is not defined at binds nothing. -/
theorem not_bindG_ptOf (ha₀ : IsBot a₀) (t t' : FTag B φ)
    (hb : bindBodyF B φ t t' = ⊥) (w : Fin (tagDim B φ t) → A)
    (w' : Fin (tagDim B φ t') → A) :
    ¬BindG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') := by
  rw [bindG_ptOf_iff B φ ha₀, hb]
  exact not_false

/-- **What a quantifier of the kernel binds**: the variable of the de Bruijn
level it introduces, and nothing else. -/
theorem bindG_nd_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (x : (finsatInterp B φ).Map A) :
    BindG (ndPt B φ a₀ p pol) x ↔ ∃ l : Fin (Tseitin.maxCtx φ),
      qLevel B φ p = some (l : ℕ) ∧ x = dbvarPt B φ a₀ l := by
  constructor
  · intro h
    obtain ⟨t', w', rfl, h⟩ := (bindG_iff_pt B φ ha₀ (Tag.nd p pol) (fun _ => a₀) x).mp h
    rcases t' with _ | _ | _ | _ | l | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
      try exact absurd h (not_bindG_ptOf B φ ha₀ _ _ rfl _ _)
    have hw : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
    subst hw
    exact ⟨l, (bindG_nd_dbvar B φ ha₀ p pol l).mp h, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (bindG_nd_dbvar B φ ha₀ p pol l).mpr hl

/-! ### The environment, as a de Bruijn context

An environment of the encoded sentence assigns a model element to every element
of the image; what the kernel's own recursion reads is only its restriction to
the variables of the de Bruijn levels. Passing under a quantifier updates the
environment at one variable, and that is exactly `Fin.snoc` on the context
tuple – the one calculation the quantifier case of the kernel recursion
needs. -/

omit [L.Structure A] [LinearOrder A] in
/-- The variables of two distinct de Bruijn levels are distinct elements. -/
theorem dbvarPt_inj {l l' : Fin (Tseitin.maxCtx φ)}
    (h : dbvarPt B φ a₀ l = dbvarPt B φ a₀ l') : l = l' := by
  have := congrArg Prod.fst h
  exact Tag.dbvar.inj this

variable {M : Type}

/-- The de Bruijn context an environment carries. -/
def envOf (a₀ : A) (v : (finsatInterp B φ).Map A → M) : Fin (Tseitin.maxCtx φ) → M :=
  fun l => v (dbvarPt B φ a₀ l)

omit [L.Structure A] [LinearOrder A] in
/-- **Passing under a quantifier is `Fin.snoc`**: updating the environment at
the variable of level `n` extends the context tuple of length `n` by the value
bound there. -/
theorem pref_envOf_upd (v : (finsatInterp B φ).Map A → M) {n : ℕ} (hn : n < Tseitin.maxCtx φ)
    (d : M) :
    pref (Nat.succ_le_of_lt hn) (envOf B φ a₀ (upd v (dbvarPt B φ a₀ ⟨n, hn⟩) d)) =
      Fin.snoc (pref (le_of_lt hn) (envOf B φ a₀ v)) d := by
  classical
  refine funext fun j => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hj | hj
  · have hj' : (j : ℕ) < n := hj
    rw [show j = Fin.castSucc ⟨(j : ℕ), hj'⟩ from Fin.ext rfl, Fin.snoc_castSucc]
    rw [pref, pref, envOf, envOf,
      upd_of_ne _ _ (fun hc => absurd (congrArg Fin.val (dbvarPt_inj B φ hc)) (by simp [hj'.ne]))]
    exact congrArg (fun z => v (dbvarPt B φ a₀ z)) (Fin.ext rfl)
  · rw [show j = Fin.last n from Fin.ext hj, Fin.snoc_last]
    rw [pref, envOf, show (Fin.castLE (Nat.succ_le_of_lt hn) (Fin.last n) :
      Fin (Tseitin.maxCtx φ)) = ⟨n, hn⟩ from Fin.ext rfl]
    exact upd_self _ _ _

/-! ### The equality literals of the kernel, inverted

The truth definition's literal clauses quantify over the two elements an
equality relates, so, as with the children, an arbitrary pair has to be put back
into points and the tags then decide. -/

theorem canon_of_eqG {g x y : (finsatInterp B φ).Map A} (h : EqG g x y) :
    Canon (tagDim B φ x.1) x.2 ∧ Canon (tagDim B φ y.1) y.2 :=
  ⟨((realize_eqFml B φ (fun i => ((![g, x, y] : Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ g x y)).mp h).1 1,
    ((realize_eqFml B φ (fun i => ((![g, x, y] : Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ g x y)).mp h).1 2⟩

theorem canon_of_neqG {g x y : (finsatInterp B φ).Map A} (h : NeqG g x y) :
    Canon (tagDim B φ x.1) x.2 ∧ Canon (tagDim B φ y.1) y.2 :=
  ⟨((realize_neqFml B φ (fun i => ((![g, x, y] : Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ g x y)).mp h).1 1,
    ((realize_neqFml B φ (fun i => ((![g, x, y] : Fin 3 → (finsatInterp B φ).Map A) i).1)
      (val₃ B φ g x y)).mp h).1 2⟩

theorem not_eqG_ptOf (ha₀ : IsBot a₀) (t t' t'' : FTag B φ) (hb : eqBodyF B φ t t' t'' = ⊥)
    (w : Fin (tagDim B φ t) → A) (w' : Fin (tagDim B φ t') → A)
    (w'' : Fin (tagDim B φ t'') → A) :
    ¬EqG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'') := by
  rw [eqG_ptOf_iff B φ ha₀, hb]
  exact not_false

theorem not_neqG_ptOf (ha₀ : IsBot a₀) (t t' t'' : FTag B φ) (hb : neqBodyF B φ t t' t'' = ⊥)
    (w : Fin (tagDim B φ t) → A) (w' : Fin (tagDim B φ t') → A)
    (w'' : Fin (tagDim B φ t'') → A) :
    ¬NeqG (ptOf B φ a₀ t w) (ptOf B φ a₀ t' w') (ptOf B φ a₀ t'' w'') := by
  rw [neqG_ptOf_iff B φ ha₀, hb]
  exact not_false

/-- **The positive equality literals of a kernel node**: the variables of the two
de Bruijn levels the kernel compares there, at polarity `true`. -/
theorem eqG_nd_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (x y : (finsatInterp B φ).Map A) :
    EqG (ndPt B φ a₀ p pol) x y ↔ ∃ l₁ l₂ : Fin (Tseitin.maxCtx φ),
      (pol = true ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ))) ∧
        x = dbvarPt B φ a₀ l₁ ∧ y = dbvarPt B φ a₀ l₂ := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := canon_of_eqG B φ h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
    obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
    rcases t' with _ | _ | _ | _ | l₁ | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
      rcases t'' with _ | _ | _ | _ | l₂ | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
      try exact absurd h (not_eqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)
    have hw' : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
    have hw'' : w'' = fun _ => a₀ := tup_zero_eq B φ rfl w'' _
    subst hw'
    subst hw''
    exact ⟨l₁, l₂, (eqG_nd_dbvar B φ ha₀ p pol l₁ l₂).mp h, rfl, rfl⟩
  · rintro ⟨l₁, l₂, hc, rfl, rfl⟩
    exact (eqG_nd_dbvar B φ ha₀ p pol l₁ l₂).mpr hc

/-- The same for the negated equalities. -/
theorem neqG_nd_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (x y : (finsatInterp B φ).Map A) :
    NeqG (ndPt B φ a₀ p pol) x y ↔ ∃ l₁ l₂ : Fin (Tseitin.maxCtx φ),
      (pol = false ∧ eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ))) ∧
        x = dbvarPt B φ a₀ l₁ ∧ y = dbvarPt B φ a₀ l₂ := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := canon_of_neqG B φ h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
    obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
    rcases t' with _ | _ | _ | _ | l₁ | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
      rcases t'' with _ | _ | _ | _ | l₂ | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
      try exact absurd h (not_neqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)
    have hw' : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
    have hw'' : w'' = fun _ => a₀ := tup_zero_eq B φ rfl w'' _
    subst hw'
    subst hw''
    exact ⟨l₁, l₂, (neqG_nd_dbvar B φ ha₀ p pol l₁ l₂).mp h, rfl, rfl⟩
  · rintro ⟨l₁, l₂, hc, rfl, rfl⟩
    exact (neqG_nd_dbvar B φ ha₀ p pol l₁ l₂).mpr hc

/-! ### The existential prefix, evaluated

The prefix is the one chain of the encoded sentence, and the one place the proof
walks the input order. Its evaluation needs nothing about the kernel: given that
the top conjunction holds under the environment sending each variable `x_b` to
its intended value, every node of the prefix holds – by downward induction, from
the greatest element of the input order, where the child is the top conjunction,
to the least, which is the root of the sentence. -/

omit [L.Structure A] [LinearOrder A] in
/-- The variables of the prefix are pairwise distinct: they are the elements the
sentence's diagram forces apart. -/
theorem pvarPt_inj {b c : A} (h : pvarPt B φ a₀ b = pvarPt B φ a₀ c) : b = c :=
  congrFun (ptOf_inj B φ h) ⟨0, (by norm_num : (0 : ℕ) < 1)⟩

variable {M : Type}

/-- **The prefix holds**: at every element of the input order, provided the top
conjunction holds once every variable has been given its intended value. -/
theorem gval_prePt [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop) (ι : A → M)
    (hbody : ∀ v : (finsatInterp B φ).Map A → M,
      (∀ b : A, v (pvarPt B φ a₀ b) = ι b) → Gval I v (bodyPt B φ a₀)) (a : A) :
    ∀ v : (finsatInterp B φ).Map A → M,
      (∀ b : A, b < a → v (pvarPt B φ a₀ b) = ι b) → Gval I v (prePt B φ a₀ a) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  induction a using order_induction_down with
  | hmax z hz =>
    intro v hv
    refine (Gval_isEval hwf I v _).mpr ?_
    simp only [gstep]
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(exG_ptOf B φ ha₀ Tag.pre _).mpr trivial, pvarPt B φ a₀ z,
        (bindG_pre_pvar B φ ha₀ z z).mpr rfl, ι z, bodyPt B φ a₀,
        (childG_pre_body B φ ha₀ z).mpr hz, ?_⟩)))
    refine hbody _ fun b => ?_
    by_cases hb : b = z
    · subst hb
      exact upd_self _ _ _
    · rw [upd_of_ne _ _ (fun hc => hb (pvarPt_inj B φ hc))]
      exact hv b (lt_of_le_of_ne (hz b) hb)
  | hstep w z hwz hnb ih =>
    intro v hv
    refine (Gval_isEval hwf I v _).mpr ?_
    simp only [gstep]
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(exG_ptOf B φ ha₀ Tag.pre _).mpr trivial, pvarPt B φ a₀ w,
        (bindG_pre_pvar B φ ha₀ w w).mpr rfl, ι w, prePt B φ a₀ z,
        (childG_pre_pre B φ ha₀ w z).mpr ⟨hwz, hnb⟩, ?_⟩)))
    refine ih _ fun b hbz => ?_
    by_cases hb : b = w
    · subst hb
      exact upd_self _ _ _
    · rw [upd_of_ne _ _ (fun hc => hb (pvarPt_inj B φ hc))]
      refine hv b ?_
      rcases lt_trichotomy b w with h' | h' | h'
      · exact h'
      · exact absurd h' hb
      · exact absurd ⟨h', hbz⟩ (hnb b)

/-- A tag the root marker is not defined at marks nothing. -/
theorem not_rootG_ptOf (ha₀ : IsBot a₀) (t : FTag B φ) (hb : rootBodyF B φ t = ⊥)
    (w : Fin (tagDim B φ t) → A) : ¬RootG (ptOf B φ a₀ t w) := by
  rw [rootG_ptOf_iff B φ ha₀, hb]
  exact not_false

/-- **The root of the encoded sentence holds**, which is what finite
satisfiability asks: the root is the prefix node of the least element, and no
variable is bound outside it. -/
theorem gval_rootG [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop) (ι : A → M)
    (hbody : ∀ v : (finsatInterp B φ).Map A → M,
      (∀ b : A, v (pvarPt B φ a₀ b) = ι b) → Gval I v (bodyPt B φ a₀))
    (v : (finsatInterp B φ).Map A → M) (g : (finsatInterp B φ).Map A) (hg : RootG g) :
    Gval I v g := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  obtain ⟨t, w, rfl⟩ := exists_ptOf B φ ha₀
    (((realize_rootFml B φ (fun i => ((![g] : Fin 1 → (finsatInterp B φ).Map A) i).1)
      (val₁ B φ g)).mp hg).1 0)
  rcases t with _ | _ | _ | _ | l | i | j | ⟨p, pol⟩ | ⟨p, pol⟩ | ⟨p, pol, j⟩ <;>
    try exact absurd hg (not_rootG_ptOf B φ ha₀ _ rfl w)
  have hw := tup_one_eq B φ (t := Tag.pre) rfl w (by norm_num : (0 : ℕ) < 1)
  rw [hw] at hg ⊢
  exact gval_prePt B φ ha₀ I ι hbody _ v fun b hb =>
    absurd hb (not_lt.mpr ((rootG_pre B φ ha₀ _).mp hg b))

/-! ### The diagram, evaluated

What is left of the ⟹ direction, once the prefix is walked: the top conjunction.
Its children are the distinctness literals and the root of the translated
kernel, so it holds as soon as the environment separates the variables of
distinct elements – which the intended assignment does, being injective – and
the kernel holds. -/

/-- **The top conjunction holds** when the environment separates the variables
of distinct elements and the root of the translated kernel holds. -/
theorem gval_bodyPt [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M)
    (hdiag : ∀ a b : A, a ≠ b → v (pvarPt B φ a₀ a) ≠ v (pvarPt B φ a₀ b))
    (hker : Gval I v (ndPt B φ a₀ (rootPos B φ) true)) :
    Gval I v (bodyPt B φ a₀) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  refine (Gval_isEval hwf I v _).mpr ?_
  simp only [gstep]
  refine Or.inl ⟨(andG_ptOf B φ ha₀ Tag.body _).mpr trivial, fun c hc => ?_⟩
  rcases (childG_body_iff B φ ha₀ c).mp hc with ⟨a, b, hab, rfl⟩ | rfl
  · refine (Gval_isEval hwf I v _).mpr ?_
    simp only [gstep]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨pvarPt B φ a₀ a, pvarPt B φ a₀ b, (neqG_neq_pvar B φ ha₀ a b a b).mpr ⟨rfl, rfl, hab⟩,
        hdiag a b hab⟩)))))
  · exact hker

/-- **The encoded sentence holds, modulo its kernel**: the whole of the ⟹
direction that does not depend on `φ`. An injective intended assignment `ι` of
the prefix variables satisfies the diagram, the prefix chain carries it to the
root, and what is left to prove of `σ_A` is that the root of the translated
kernel holds under every environment giving the prefix variables their intended
values. -/
theorem gval_of_kernel [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop) (ι : A → M)
    (hinj : Function.Injective ι)
    (hker : ∀ v : (finsatInterp B φ).Map A → M, (∀ b : A, v (pvarPt B φ a₀ b) = ι b) →
      Gval I v (ndPt B φ a₀ (rootPos B φ) true))
    (v : (finsatInterp B φ).Map A → M) (g : (finsatInterp B φ).Map A) (hg : RootG g) :
    Gval I v g :=
  gval_rootG B φ ha₀ I ι
    (fun v' hv' => gval_bodyPt B φ ha₀ I v'
      (fun a b hab hc => hab (hinj (by rw [← hv' a, ← hv' b]; exact hc))) (hker v' hv'))
    v g hg

/-! ### The model side: an interpretation from an assignment of the block

`DescriptiveComplexity.FinSat.FinSatOn` asks for a model together with a *local*
interpretation – one that reads a symbol only at the argument positions of its
own signature. The relation variables of the block give one: the symbol of a
variable is interpreted by that variable's relation, read at the argument
positions. Locality is what makes it a relation of the symbol's own arity rather
than of the whole universe, and it is the condition the truth definition's atom
clauses are stated against. -/

omit [L.Structure A] [LinearOrder A] in
/-- Distinct relation variables get distinct symbols. -/
theorem symPt_inj {i i' : B.ι} (h : symPt B φ a₀ i = symPt B φ a₀ i') : i = i' :=
  Tag.sym.inj (congrArg Prod.fst h)

/-- The arguments an assignment of the argument positions gives to a relation
variable. A variable of the block whose arity exceeds the dimension cannot occur
in the kernel, so the sentence never reads it; the value taken there is
immaterial, and reading it at the first position keeps the whole tuple inside
the symbol's signature, which is what locality asks. -/
noncomputable def argTup (a₀ : A) (i : B.ι) (w : (finsatInterp B φ).Map A → M) :
    Fin (B.arity i) → M :=
  fun j => if h : (j : ℕ) < finsatDim B φ then w (aposPt B φ a₀ ⟨(j : ℕ), h⟩)
    else w (aposPt B φ a₀ (c0 B φ))

/-- **The interpretation determined by an assignment of the block.** -/
noncomputable def blockI (a₀ : A) (μ : B.Assignment M) :
    (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop :=
  fun s w => ∃ i : B.ι, s = symPt B φ a₀ i ∧ μ i (argTup B φ a₀ i w)

/-- The arguments of a relation variable are read inside its signature. -/
theorem argTup_congr (ha₀ : IsBot a₀) (i : B.ι) {w w' : (finsatInterp B φ).Map A → M}
    (hag : ∀ p, SigG (symPt B φ a₀ i) p → w p = w' p) :
    argTup B φ a₀ i w = argTup B φ a₀ i w' := by
  classical
  have hsig : ∀ k : Fin (finsatDim B φ), (k : ℕ) < B.arity i →
      SigG (symPt B φ a₀ i) (aposPt B φ a₀ k) :=
    fun k hk => (sigG_ptOf B φ ha₀ (Tag.sym i) (Tag.apos k) _ _).mpr hk
  funext j
  by_cases hj : (j : ℕ) < finsatDim B φ
  · rw [argTup, argTup, dif_pos hj, dif_pos hj]
    exact hag _ (hsig ⟨(j : ℕ), hj⟩ j.isLt)
  · rw [argTup, argTup, dif_neg hj, dif_neg hj]
    refine hag _ (hsig (c0 B φ) ?_)
    change (0 : ℕ) < B.arity i
    have h2 := two_le_finsatDim B φ
    have hjj := j.isLt
    omega

/-- **The interpretation is local**, so it is a genuine interpretation of the
encoded sentence's vocabulary. -/
theorem local_blockI (ha₀ : IsBot a₀) (μ : B.Assignment M) :
    Local (blockI B φ a₀ μ) := by
  rintro s w w' hag
  constructor
  · rintro ⟨i, rfl, hμ⟩
    exact ⟨i, rfl, argTup_congr B φ ha₀ i hag ▸ hμ⟩
  · rintro ⟨i, rfl, hμ⟩
    exact ⟨i, rfl, (argTup_congr B φ ha₀ i hag).symm ▸ hμ⟩

omit [L.Structure A] [LinearOrder A] in
/-- The atom of a relation variable, read on the image: at a node carrying a
block atom of the kernel, the interpretation holds of an assignment exactly when
the variable's relation holds of the arguments that assignment gives. -/
theorem blockI_symPt (a₀ : A) (μ : B.Assignment M) (i : B.ι)
    (w : (finsatInterp B φ).Map A → M) :
    blockI B φ a₀ μ (symPt B φ a₀ i) w ↔ μ i (argTup B φ a₀ i w) :=
  ⟨fun ⟨_, hs, hμ⟩ => symPt_inj B φ hs ▸ hμ, fun h => ⟨i, rfl, h⟩⟩

/-! ### The atom clause does not depend on the assignment it is read at

The truth definition reads an atom at *some* assignment of the argument
positions matching the environment on the atom's arguments. Two such assignments
agree on every position of the symbol's signature – that is what
`DescriptiveComplexity.FinSat.IsWF.arg_tot` gives – so a local interpretation
cannot tell them apart, and the clause may always be read at the canonical
assignment below. This is the one place the shape conditions of well-formedness
are used for something other than being proved. -/

open Classical in
/-- The canonical assignment of the argument positions of a node: the value of
the argument sitting there, and anything at all elsewhere. -/
noncomputable def argAssign (v : (finsatInterp B φ).Map A → M)
    (g : (finsatInterp B φ).Map A) (junk : M) : (finsatInterp B φ).Map A → M :=
  fun q => if h : ∃ x, ArgG g q x then v h.choose else junk

/-- It does match the environment on the arguments – the atom of the image has
at most one argument at each position. -/
theorem argAssign_spec (v : (finsatInterp B φ).Map A → M) (g : (finsatInterp B φ).Map A)
    (junk : M) (q x : (finsatInterp B φ).Map A) (hx : ArgG g q x) :
    argAssign B φ v g junk q = v x := by
  classical
  rw [argAssign, dif_pos ⟨x, hx⟩]
  exact congrArg v (arg_fun_map B φ g q _ x (Exists.choose_spec ⟨x, hx⟩) hx)

/-- **Any matching assignment gives the atom the same value** as the canonical
one: they agree on the signature of the symbol, and the interpretation is
local. -/
theorem interp_matching_iff [L.IsRelational] [Finite A] [Nonempty A]
    {I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop} (hloc : Local I)
    (v : (finsatInterp B φ).Map A → M) (g s : (finsatInterp B φ).Map A)
    (hs : PosG g s ∨ NegG g s) (w : (finsatInterp B φ).Map A → M) (junk : M)
    (hw : ∀ p x, ArgG g p x → w p = v x) :
    I s w ↔ I s (argAssign B φ v g junk) := by
  refine hloc s w _ fun p hp => ?_
  obtain ⟨x, hx⟩ := arg_tot_map B φ g s p hs hp
  rw [hw p x hx, argAssign_spec B φ v g junk p x hx]

/-! ### The atoms of the relation variables, evaluated

Putting the last three pieces together: at a node of the kernel carrying an atom
of a relation variable, the atom clause of the truth definition says exactly
that the variable's relation holds of the values its arguments take. This is the
one clause of the kernel recursion that mentions the model at all. -/

omit [L.Structure A] in
/-- An element canonical at dimension zero carrying the tag of a symbol *is*
that symbol. -/
theorem eq_symPt (ha₀ : IsBot a₀) {x : (finsatInterp B φ).Map A} {i : B.ι}
    (ht : x.1 = Tag.sym i) (h : Canon 0 x.2) : x = symPt B φ a₀ i :=
  Prod.ext_iff.mpr ⟨ht, eq_of_canon_zero B φ h (canon_ptOf B φ ha₀ (Tag.sym i) _)⟩

/-- **The symbol of an atom of the image**: a node of the kernel carries a
positive atom exactly when it sits at polarity `true` on a block atom, and then
the symbol is that of its relation variable. -/
theorem posG_ndPt_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (s : (finsatInterp B φ).Map A) :
    PosG (ndPt B φ a₀ p pol) s ↔
      ∃ i : B.ι, pol = true ∧ blockSym B φ p = some i ∧ s = symPt B φ a₀ i := by
  constructor
  · intro h
    obtain ⟨-, hc, ha⟩ := shape_of_posG B φ _ s h
    obtain ⟨q, i, hq, hs, hsym⟩ := atomTag_cases B φ ha
    have hq' : (Tag.nd p pol : FTag B φ) = Tag.nd q true := hq
    injection hq' with h1 h2
    subst h1
    subst h2
    exact ⟨i, rfl, hsym, eq_symPt B φ ha₀ hs hc⟩
  · rintro ⟨i, rfl, hsym, rfl⟩
    exact (posG_ptOf B φ ha₀ (Tag.nd p true) (Tag.sym i) _ _).mpr ⟨rfl, hsym⟩

/-- The same at polarity `false`: a negated atom. -/
theorem negG_ndPt_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (s : (finsatInterp B φ).Map A) :
    NegG (ndPt B φ a₀ p pol) s ↔
      ∃ i : B.ι, pol = false ∧ blockSym B φ p = some i ∧ s = symPt B φ a₀ i := by
  constructor
  · intro h
    obtain ⟨-, hc, ha⟩ := shape_of_negG B φ _ s h
    obtain ⟨q, i, hq, hs, hsym⟩ := atomTag_cases B φ ha
    have hq' : (Tag.nd p pol : FTag B φ) = Tag.nd q false := hq
    injection hq' with h1 h2
    subst h1
    subst h2
    exact ⟨i, rfl, hsym, eq_symPt B φ ha₀ hs hc⟩
  · rintro ⟨i, rfl, hsym, rfl⟩
    exact (negG_ptOf B φ ha₀ (Tag.nd p false) (Tag.sym i) _ _).mpr ⟨rfl, hsym⟩

/-- **The positive-atom clause of the truth definition, evaluated.** -/
theorem posAtom_clause_iff [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (μ : B.Assignment M) (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (i : B.ι)
    (hi : blockSym B φ p = some i) (junk : M) :
    (∃ s, PosG (ndPt B φ a₀ p true) s ∧ ∃ w : (finsatInterp B φ).Map A → M,
        (∀ q x, ArgG (ndPt B φ a₀ p true) q x → w q = v x) ∧ blockI B φ a₀ μ s w) ↔
      μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p true) junk)) := by
  constructor
  · rintro ⟨s, hs, w, hw, hI⟩
    obtain ⟨i', -, hi', rfl⟩ := (posG_ndPt_iff B φ ha₀ p true s).mp hs
    have hii : (some i' : Option B.ι) = some i := by rw [← hi', ← hi]
    have hii' : i' = i := Option.some.inj hii
    subst hii'
    exact (blockI_symPt B φ a₀ μ i' _).mp
      ((interp_matching_iff B φ (local_blockI B φ ha₀ μ) v _ _ (Or.inl hs) w junk hw).mp hI)
  · intro h
    exact ⟨symPt B φ a₀ i, (posG_ndPt_iff B φ ha₀ p true _).mpr ⟨i, rfl, hi, rfl⟩,
      argAssign B φ v (ndPt B φ a₀ p true) junk,
      fun q x hx => argAssign_spec B φ v _ junk q x hx,
      (blockI_symPt B φ a₀ μ i _).mpr h⟩

/-- **The negated-atom clause**, the same at polarity `false`. -/
theorem negAtom_clause_iff [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (μ : B.Assignment M) (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (i : B.ι)
    (hi : blockSym B φ p = some i) (junk : M) :
    (∃ s, NegG (ndPt B φ a₀ p false) s ∧ ∃ w : (finsatInterp B φ).Map A → M,
        (∀ q x, ArgG (ndPt B φ a₀ p false) q x → w q = v x) ∧ ¬blockI B φ a₀ μ s w) ↔
      ¬μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p false) junk)) := by
  constructor
  · rintro ⟨s, hs, w, hw, hI⟩
    obtain ⟨i', -, hi', rfl⟩ := (negG_ndPt_iff B φ ha₀ p false s).mp hs
    have hii : (some i' : Option B.ι) = some i := by rw [← hi', ← hi]
    have hii' : i' = i := Option.some.inj hii
    subst hii'
    exact fun hc => hI ((interp_matching_iff B φ (local_blockI B φ ha₀ μ) v _ _
      (Or.inr hs) w junk hw).mpr ((blockI_symPt B φ a₀ μ i' _).mpr hc))
  · intro h
    exact ⟨symPt B φ a₀ i, (negG_ndPt_iff B φ ha₀ p false _).mpr ⟨i, rfl, hi, rfl⟩,
      argAssign B φ v (ndPt B φ a₀ p false) junk,
      fun q x hx => argAssign_spec B φ v _ junk q x hx,
      fun hc => h ((blockI_symPt B φ a₀ μ i _).mp hc)⟩

/-! ### The nodes of a translated atom

An atom the sentence may not mention becomes a disjunction over the tuples where
it holds, each tuple a conjunction of equality literals pinning one argument to a
prefix variable. Those two node kinds need the same treatment as the kernel's:
which clause of the truth definition fires, and which elements it relates. -/

/-- A node that is not a translation of a kernel position carries no atom. -/
theorem not_posG_of_ne_nd (t : FTag B φ)
    (ht : ∀ (q : Pos B φ) (pol : Bool), t ≠ Tag.nd q pol) (w : Fin (tagDim B φ t) → A)
    (s : (finsatInterp B φ).Map A) : ¬PosG (ptOf B φ a₀ t w) s := by
  intro h
  obtain ⟨-, -, ha⟩ := shape_of_posG B φ _ s h
  obtain ⟨q, i, hq, -, -⟩ := atomTag_cases B φ ha
  exact ht q true hq

theorem not_negG_of_ne_nd (t : FTag B φ)
    (ht : ∀ (q : Pos B φ) (pol : Bool), t ≠ Tag.nd q pol) (w : Fin (tagDim B φ t) → A)
    (s : (finsatInterp B φ).Map A) : ¬NegG (ptOf B φ a₀ t w) s := by
  intro h
  obtain ⟨-, -, ha⟩ := shape_of_negG B φ _ s h
  obtain ⟨q, i, hq, -, -⟩ := atomTag_cases B φ ha
  exact ht q false hq

/-- A tuple node of a translated atom carries no equality literal: it is a
conjunction of them, not one itself. -/
theorem not_eqG_atup (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) (x y : (finsatInterp B φ).Map A) :
    ¬EqG (atupPt B φ a₀ p pol w) x y := by
  intro h
  obtain ⟨hx, hy⟩ := canon_of_eqG B φ h
  obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
  obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
  rcases t' with _ | _ | _ | _ | l₁ | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
    rcases t'' with _ | _ | _ | _ | l₂ | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
    exact absurd h (not_eqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)

theorem not_neqG_atup (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool)
    (w : Fin (tagDim B φ (Tag.atup p pol)) → A) (x y : (finsatInterp B φ).Map A) :
    ¬NeqG (atupPt B φ a₀ p pol w) x y := by
  intro h
  obtain ⟨hx, hy⟩ := canon_of_neqG B φ h
  obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
  obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
  rcases t' with _ | _ | _ | _ | l₁ | i | j | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', j⟩ <;>
    rcases t'' with _ | _ | _ | _ | l₂ | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
    exact absurd h (not_neqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)

/-- **The equality literal of a translated atom, inverted**: it relates the
variable of the argument's de Bruijn level to the prefix variable of the element
its tuple holds there. -/
theorem eqG_alit_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ))
    (a : A) (x y : (finsatInterp B φ).Map A) :
    EqG (alitPt B φ a₀ p pol j a) x y ↔ ∃ (l : Fin (Tseitin.maxCtx φ)) (b : A),
      (pol = true ∧ inArg B φ p (j : ℕ) = some (l : ℕ)) ∧ a = b ∧
        x = dbvarPt B φ a₀ l ∧ y = pvarPt B φ a₀ b := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := canon_of_eqG B φ h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
    obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
    rcases t' with _ | _ | _ | _ | l | i | jj | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', jj⟩ <;>
      rcases t'' with _ | _ | _ | _ | l' | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
      try exact absurd h (not_eqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)
    have hw' : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
    have hw'' := tup_one_eq B φ (t := Tag.pvar) rfl w'' (by norm_num : (0 : ℕ) < 1)
    subst hw'
    rw [hw''] at h
    obtain ⟨hc, hab⟩ := (eqG_alit B φ ha₀ p pol j a _ l).mp h
    exact ⟨l, _, hc, hab, rfl, congrArg (ptOf B φ a₀ Tag.pvar) hw''⟩
  · rintro ⟨l, b, hc, rfl, rfl, rfl⟩
    exact (eqG_alit B φ ha₀ p pol j a a l).mpr ⟨hc, rfl⟩

/-- The same for a negatively translated atom. -/
theorem neqG_alit_iff (ha₀ : IsBot a₀) (p : Pos B φ) (pol : Bool) (j : Fin (finsatDim B φ))
    (a : A) (x y : (finsatInterp B φ).Map A) :
    NeqG (alitPt B φ a₀ p pol j a) x y ↔ ∃ (l : Fin (Tseitin.maxCtx φ)) (b : A),
      (pol = false ∧ inArg B φ p (j : ℕ) = some (l : ℕ)) ∧ a = b ∧
        x = dbvarPt B φ a₀ l ∧ y = pvarPt B φ a₀ b := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := canon_of_neqG B φ h
    obtain ⟨t', w', rfl⟩ := exists_ptOf B φ ha₀ hx
    obtain ⟨t'', w'', rfl⟩ := exists_ptOf B φ ha₀ hy
    rcases t' with _ | _ | _ | _ | l | i | jj | ⟨q, pol'⟩ | ⟨q, pol'⟩ | ⟨q, pol', jj⟩ <;>
      rcases t'' with _ | _ | _ | _ | l' | i' | j' | ⟨q', pol''⟩ | ⟨q', pol''⟩ | ⟨q', pol'', j'⟩ <;>
      try exact absurd h (not_neqG_ptOf B φ ha₀ _ _ _ rfl _ _ _)
    have hw' : w' = fun _ => a₀ := tup_zero_eq B φ rfl w' _
    have hw'' := tup_one_eq B φ (t := Tag.pvar) rfl w'' (by norm_num : (0 : ℕ) < 1)
    subst hw'
    rw [hw''] at h
    obtain ⟨hc, hab⟩ := (neqG_alit B φ ha₀ p pol j a _ l).mp h
    exact ⟨l, _, hc, hab, rfl, congrArg (ptOf B φ a₀ Tag.pvar) hw''⟩
  · rintro ⟨l, b, hc, rfl, rfl, rfl⟩
    exact (neqG_alit B φ ha₀ p pol j a a l).mpr ⟨hc, rfl⟩

/-! ### The one place the input structure is read

The tuple nodes of a translated atom are selected by a *defining formula*, so
reading them off the image means realizing that formula: for an atom of the
input vocabulary it is the atom itself, at the tuple the node holds; for the
marker `old` it is `⊤`, since every original element is old. The `kernelNode`
equation is a hypothesis to *rewrite with* – its arity is an implicit argument,
so destructing it would land in `HEq`. -/

theorem realize_inAtomF_input {p : Pos B φ} {k : ℕ} {r : L.Relations k}
    {args : Fin k → Option ℕ} (hk : kernelNode φ p.2 = .inputAtom r args)
    (h : k ≤ finsatDim B φ) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (inAtomF B φ p).Realize v ↔ RelMap r fun j => v (1, Fin.castLE h j) := by
  rw [inAtomF, hk]
  dsimp only
  rw [dif_pos h]
  exact Formula.realize_rel.trans (relMap_sumInl r _)

theorem realize_inAtomF_old {p : Pos B φ} {x : Option ℕ}
    (hk : kernelNode φ p.2 = .oldAtom x) (v : Fin 2 × Fin (finsatDim B φ) → A) :
    (inAtomF B φ p).Realize v := by
  rw [inAtomF, hk]
  exact Formula.realize_top.mpr trivial

/-! ### The truth definition at a node of the kernel

What the kernel says at a position decides which clause of the truth definition
can fire there, and the other seven are then vacuous. These two lemmas do that
bookkeeping once: at a node translating an *n*-ary connective – falsity, an
implication or an atom the sentence may not mention – the value is the
disjunction of the children's at polarity `true` and their conjunction at
polarity `false`. -/

theorem gstep_conn_true (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p true) ↔
      ∃ c, ChildG (ndPt B φ a₀ p true) c ∧ rec v c := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨-, hex⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (true : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · exact hex
    · have h : (true : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · have h : (true : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p true x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p true x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (posG_ndPt_iff B φ ha₀ p true s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
    · obtain ⟨i, hpol, -, -⟩ := (negG_ndPt_iff B φ ha₀ p true s).mp hps
      exact absurd hpol (by simp)
  · intro h
    exact Or.inr (Or.inl ⟨(orG_ptOf B φ ha₀ _ _).mpr ⟨rfl, hcn⟩, h⟩)

theorem gstep_conn_false (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p false) ↔
      ∀ c, ChildG (ndPt B φ a₀ p false) c → rec v c := by
  simp only [gstep]
  constructor
  · rintro (⟨-, hall⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact hall
    · have h : (false : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p false x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p false x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨i, hpol, -, -⟩ := (posG_ndPt_iff B φ ha₀ p false s).mp hps
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (negG_ndPt_iff B φ ha₀ p false s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
  · intro h
    exact Or.inl ⟨(andG_ptOf B φ ha₀ _ _).mpr ⟨rfl, hcn⟩, h⟩

/-! At a quantifier node the value is the conjunction (respectively the
disjunction) over the model of the child's, the bound variable of the level the
quantifier introduces taking each value in turn. -/

theorem gstep_quant_true (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (l : Fin (Tseitin.maxCtx φ))
    (hq : qLevel B φ p = some (l : ℕ)) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : ¬isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p true) ↔
      ∀ d : M, ∀ c, ChildG (ndPt B φ a₀ p true) c → rec (upd v (dbvarPt B φ a₀ l) d) c := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, hall⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (true : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (true : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · exact hall _ ((bindG_nd_iff B φ ha₀ p true _).mpr ⟨l, hq, rfl⟩)
    · have h : (true : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p true x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p true x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (posG_ndPt_iff B φ ha₀ p true s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
    · obtain ⟨i, hpol, -, -⟩ := (negG_ndPt_iff B φ ha₀ p true s).mp hps
      exact absurd hpol (by simp)
  · intro h
    refine Or.inr (Or.inr (Or.inl ⟨(allG_ptOf B φ ha₀ _ _).mpr ⟨rfl, by rw [hq]; rfl⟩,
      fun x hx => ?_⟩))
    obtain ⟨l', hl', rfl⟩ := (bindG_nd_iff B φ ha₀ p true x).mp hx
    have : l' = l := by
      rw [hq] at hl'
      exact Fin.ext (Option.some.inj hl'.symm)
    subst this
    exact h

theorem gstep_quant_false (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (l : Fin (Tseitin.maxCtx φ))
    (hq : qLevel B φ p = some (l : ℕ)) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : ¬isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p false) ↔
      ∃ d : M, ∃ c, ChildG (ndPt B φ a₀ p false) c ∧ rec (upd v (dbvarPt B φ a₀ l) d) c := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, x, hx, hex⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (false : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · have h : (false : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · obtain ⟨l', hl', rfl⟩ := (bindG_nd_iff B φ ha₀ p false x).mp hx
      have : l' = l := by
        rw [hq] at hl'
        exact Fin.ext (Option.some.inj hl'.symm)
      subst this
      exact hex
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p false x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p false x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨i, hpol, -, -⟩ := (posG_ndPt_iff B φ ha₀ p false s).mp hps
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (negG_ndPt_iff B φ ha₀ p false s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
  · rintro ⟨d, c, hc, hrec⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(exG_ptOf B φ ha₀ _ _).mpr ⟨rfl, by rw [hq]; rfl⟩, dbvarPt B φ a₀ l,
        (bindG_nd_iff B φ ha₀ p false _).mpr ⟨l, hq, rfl⟩, d, c, hc, hrec⟩)))

/-! At a node translating an equality of the kernel the value is that
equality, read at the variables of the two de Bruijn levels. -/

theorem gstep_eqLit_true (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (l₁ l₂ : Fin (Tseitin.maxCtx φ))
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)))
    (hs : blockSym B φ p = none) (hcn : ¬isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p true) ↔
      v (dbvarPt B φ a₀ l₁) = v (dbvarPt B φ a₀ l₂) := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, hv⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (true : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (true : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · have h : (true : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · have h : (true : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · obtain ⟨l₁', l₂', ⟨-, hl⟩, rfl, rfl⟩ := (eqG_nd_iff B φ ha₀ p true x y).mp hxy
      rw [he] at hl
      obtain ⟨e₁, e₂⟩ := Prod.mk.injEq .. ▸ Option.some.inj hl
      rw [Fin.ext e₁, Fin.ext e₂]
      exact hv
    · obtain ⟨l₁', l₂', ⟨hpol, -⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p true x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (posG_ndPt_iff B φ ha₀ p true s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
    · obtain ⟨i, hpol, -, -⟩ := (negG_ndPt_iff B φ ha₀ p true s).mp hps
      exact absurd hpol (by simp)
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨dbvarPt B φ a₀ l₁, dbvarPt B φ a₀ l₂,
        (eqG_nd_iff B φ ha₀ p true _ _).mpr ⟨l₁, l₂, ⟨rfl, he⟩, rfl, rfl⟩, h⟩))))

theorem gstep_eqLit_false (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (l₁ l₂ : Fin (Tseitin.maxCtx φ))
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)))
    (hs : blockSym B φ p = none) (hcn : ¬isConn B φ p) :
    gstep I rec v (ndPt B φ a₀ p false) ↔
      v (dbvarPt B φ a₀ l₁) ≠ v (dbvarPt B φ a₀ l₂) := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, hv⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (false : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · have h : (false : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · obtain ⟨l₁', l₂', ⟨hpol, -⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p false x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨l₁', l₂', ⟨-, hl⟩, rfl, rfl⟩ := (neqG_nd_iff B φ ha₀ p false x y).mp hxy
      rw [he] at hl
      obtain ⟨e₁, e₂⟩ := Prod.mk.injEq .. ▸ Option.some.inj hl
      rw [Fin.ext e₁, Fin.ext e₂]
      exact hv
    · obtain ⟨i, hpol, -, -⟩ := (posG_ndPt_iff B φ ha₀ p false s).mp hps
      exact absurd hpol (by simp)
    · obtain ⟨i, -, hi, -⟩ := (negG_ndPt_iff B φ ha₀ p false s).mp hps
      rw [hs] at hi
      exact absurd hi (by simp)
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨dbvarPt B φ a₀ l₁, dbvarPt B φ a₀ l₂,
        (neqG_nd_iff B φ ha₀ p false _ _).mpr ⟨l₁, l₂, ⟨rfl, he⟩, rfl, rfl⟩, h⟩)))))

/-! At a node translating an atom of a relation variable – the only genuine
atoms of the encoded sentence – the value is that relation, read at the values
of the atom's arguments. -/

theorem gstep_blockAtom_true [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (μ : B.Assignment M)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (i : B.ι) (junk : M)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = some i)
    (hcn : ¬isConn B φ p) :
    gstep (blockI B φ a₀ μ) rec v (ndPt B φ a₀ p true) ↔
      μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p true) junk)) := by
  rw [← posAtom_clause_iff B φ ha₀ μ v p i hs junk]
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, hw⟩ | ⟨s, hps, -⟩)
    · have h : (true : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (true : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · have h : (true : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · have h : (true : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p true x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p true x y).mp hxy
      exact absurd hpol (by simp)
    · exact ⟨s, hps, hw⟩
    · obtain ⟨i', hpol, -, -⟩ := (negG_ndPt_iff B φ ha₀ p true s).mp hps
      exact absurd hpol (by simp)
  · rintro ⟨s, hps, hw⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hps, hw⟩))))))

theorem gstep_blockAtom_false [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (μ : B.Assignment M)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (i : B.ι) (junk : M)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = some i)
    (hcn : ¬isConn B φ p) :
    gstep (blockI B φ a₀ μ) rec v (ndPt B φ a₀ p false) ↔
      ¬μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p false) junk)) := by
  rw [← negAtom_clause_iff B φ ha₀ μ v p i hs junk]
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, hw⟩)
    · have h : (false : Bool) = false ∧ isConn B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.2 hcn
    · have h : (false : Bool) = true ∧ isConn B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = true ∧ (qLevel B φ p).isSome = true :=
        (allG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · have h : (false : Bool) = false ∧ (qLevel B φ p).isSome = true :=
        (exG_ptOf B φ ha₀ _ _).mp hk
      rw [hq] at h
      exact absurd h.2 (by simp)
    · obtain ⟨l₁, l₂, ⟨hpol, -⟩, -, -⟩ := (eqG_nd_iff B φ ha₀ p false x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨l₁, l₂, ⟨-, hl⟩, -, -⟩ := (neqG_nd_iff B φ ha₀ p false x y).mp hxy
      rw [he] at hl
      exact absurd hl (by simp)
    · obtain ⟨i', hpol, -, -⟩ := (posG_ndPt_iff B φ ha₀ p false s).mp hps
      exact absurd hpol (by simp)
    · exact ⟨s, hps, hw⟩
  · rintro ⟨s, hps, hw⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hps, hw⟩))))))

/-! ### The kernel, position by position

The cases of the induction §5 of `TRAKHTENBROT.md` designs, each stated for a
subformula of the kernel embedded by a `DescriptiveComplexity.FinSat.SubEmb`:
the shape facts come from `SubEmb.node`, the children from `SubEmb.kid` and
`SubEmb.kid_range` through
`DescriptiveComplexity.FinSat.childG_nd_iff`. -/

/-- **A node translating falsity** has no children at all: at polarity `true` it
is the empty disjunction, which is false, and at `false` the empty conjunction,
which is true. -/
theorem gval_nd_falsum [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) {n : ℕ}
    (E : SubEmb φ (BoundedFormula.falsum : ((newLang L).sum B.lang).BoundedFormula Empty n)) :
    ¬Gval I v (ndPt B φ a₀ ⟨n, E.emb (Tseitin.rootAt _)⟩ true) ∧
      Gval I v (ndPt B φ a₀ ⟨n, E.emb (Tseitin.rootAt _)⟩ false) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  set p : Pos B φ := ⟨n, E.emb (Tseitin.rootAt _)⟩ with hp
  have hk : kernelNode φ p.2 = .fls := E.node _
  have hq : qLevel B φ p = none := by rw [qLevel, hk]
  have he : eqArgs B φ p = none := by rw [eqArgs, hk]
  have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
  have hcn : isConn B φ p := by rw [isConn, hk]; trivial
  have hno : ∀ (pol : Bool) (c : (finsatInterp B φ).Map A),
      ¬ChildG (ndPt B φ a₀ p pol) c := by
    intro pol c hc
    rcases (childG_nd_iff B φ ha₀ p pol c).mp hc with ⟨q, pol', hkid, -⟩ | ⟨w, hw, -⟩
    · obtain ⟨q'', hq''⟩ := E.kid_range _ q.2 hkid
      rw [hq''] at hkid
      rw [E.kid] at hkid
      exact absurd hkid (by simp [kidOf])
    · rw [childG_nd_atup B φ ha₀ p pol w, inAtomF, hk] at hw
      exact hw
  constructor
  · intro h
    obtain ⟨c, hc, -⟩ := (gstep_conn_true B φ ha₀ I (Gval I) v p hq he hs hcn).mp
      ((Gval_isEval hwf I v _).mp h)
    exact hno true c hc
  · exact (Gval_isEval hwf I v _).mpr
      ((gstep_conn_false B φ ha₀ I (Gval I) v p hq he hs hcn).mpr
        fun c hc => absurd hc (hno false c))

/-- **A node translating an implication**: at polarity `true` it is the
disjunction of the negated premise and the conclusion, at `false` the
conjunction of the premise and the negated conclusion – negation normal form,
as a polarity flag on the premise. -/
theorem gval_nd_impl [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p p₁ p₂ : Pos B φ)
    (hk : kernelNode φ p.2 = .impl)
    (h1 : kidOf φ p.2 p₁.2 = some true) (h2 : kidOf φ p.2 p₂.2 = some false)
    (henum : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 = some b →
      (b = true ∧ q = p₁) ∨ (b = false ∧ q = p₂)) :
    (Gval I v (ndPt B φ a₀ p true) ↔
        Gval I v (ndPt B φ a₀ p₁ false) ∨ Gval I v (ndPt B φ a₀ p₂ true)) ∧
      (Gval I v (ndPt B φ a₀ p false) ↔
        Gval I v (ndPt B φ a₀ p₁ true) ∧ Gval I v (ndPt B φ a₀ p₂ false)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  have hq : qLevel B φ p = none := by rw [qLevel, hk]
  have he : eqArgs B φ p = none := by rw [eqArgs, hk]
  have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
  have hcn : isConn B φ p := by rw [isConn, hk]; trivial
  have hchild : ∀ (pol : Bool) (c : (finsatInterp B φ).Map A),
      ChildG (ndPt B φ a₀ p pol) c ↔
        c = ndPt B φ a₀ p₁ (!pol) ∨ c = ndPt B φ a₀ p₂ pol := by
    intro pol c
    constructor
    · intro hc
      rcases (childG_nd_iff B φ ha₀ p pol c).mp hc with ⟨q, pol', hkid, rfl⟩ | ⟨w, hw, -⟩
      · rcases henum q _ hkid with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
        · refine Or.inl ?_
          have hpp : pol' = !pol := by cases pol <;> cases pol' <;> simp_all
          rw [hpp]
        · refine Or.inr ?_
          have hpp : pol' = pol := by cases pol <;> cases pol' <;> simp_all
          rw [hpp]
      · rw [childG_nd_atup B φ ha₀ p pol w, inAtomF, hk] at hw
        exact hw.elim
    · rintro (rfl | rfl)
      · exact (childG_nd_nd B φ ha₀ p p₁ pol (!pol)).mpr (by cases pol <;> simpa using h1)
      · exact (childG_nd_nd B φ ha₀ p p₂ pol pol).mpr (by cases pol <;> simpa using h2)
  constructor
  · rw [Gval_isEval hwf I v _, gstep_conn_true B φ ha₀ I (Gval I) v p hq he hs hcn]
    constructor
    · rintro ⟨c, hc, hv⟩
      rcases (hchild true c).mp hc with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    · rintro (h | h)
      · exact ⟨_, (hchild true _).mpr (Or.inl rfl), h⟩
      · exact ⟨_, (hchild true _).mpr (Or.inr rfl), h⟩
  · rw [Gval_isEval hwf I v _, gstep_conn_false B φ ha₀ I (Gval I) v p hq he hs hcn]
    constructor
    · intro h
      exact ⟨h _ ((hchild false _).mpr (Or.inl rfl)), h _ ((hchild false _).mpr (Or.inr rfl))⟩
    · rintro ⟨hA, hB⟩ c hc
      rcases (hchild false c).mp hc with rfl | rfl
      · exact hA
      · exact hB

/-- **A node translating a quantifier**: at polarity `true` it is the
conjunction over the model of the body's values, at `false` the disjunction –
the variable of the de Bruijn level the quantifier introduces taking each value
of the model in turn. -/
theorem gval_nd_quant [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p p' : Pos B φ) (l : Fin (Tseitin.maxCtx φ))
    (hk : kernelNode φ p.2 = .quant (l : ℕ))
    (h1 : kidOf φ p.2 p'.2 = some false)
    (henum : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 = some b → b = false ∧ q = p') :
    (Gval I v (ndPt B φ a₀ p true) ↔
        ∀ d : M, Gval I (upd v (dbvarPt B φ a₀ l) d) (ndPt B φ a₀ p' true)) ∧
      (Gval I v (ndPt B φ a₀ p false) ↔
        ∃ d : M, Gval I (upd v (dbvarPt B φ a₀ l) d) (ndPt B φ a₀ p' false)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  have hq : qLevel B φ p = some (l : ℕ) := by rw [qLevel, hk]
  have he : eqArgs B φ p = none := by rw [eqArgs, hk]
  have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
  have hcn : ¬isConn B φ p := by rw [isConn, hk]; exact not_false
  have hchild : ∀ (pol : Bool) (c : (finsatInterp B φ).Map A),
      ChildG (ndPt B φ a₀ p pol) c ↔ c = ndPt B φ a₀ p' pol := by
    intro pol c
    constructor
    · intro hc
      rcases (childG_nd_iff B φ ha₀ p pol c).mp hc with ⟨q, pol', hkid, rfl⟩ | ⟨w, hw, -⟩
      · obtain ⟨hb, rfl⟩ := henum q _ hkid
        have hpp : pol' = pol := by cases pol <;> cases pol' <;> simp_all
        rw [hpp]
      · rw [childG_nd_atup B φ ha₀ p pol w, inAtomF, hk] at hw
        exact hw.elim
    · rintro rfl
      exact (childG_nd_nd B φ ha₀ p p' pol pol).mpr (by cases pol <;> simpa using h1)
  constructor
  · rw [Gval_isEval hwf I v _, gstep_quant_true B φ ha₀ I (Gval I) v p l hq he hs hcn]
    exact ⟨fun h d => h d _ ((hchild true _).mpr rfl),
      fun h d c hc => by rw [(hchild true c).mp hc]; exact h d⟩
  · rw [Gval_isEval hwf I v _, gstep_quant_false B φ ha₀ I (Gval I) v p l hq he hs hcn]
    constructor
    · rintro ⟨d, c, hc, hv⟩
      rw [(hchild false c).mp hc] at hv
      exact ⟨d, hv⟩
    · rintro ⟨d, hv⟩
      exact ⟨d, _, (hchild false _).mpr rfl, hv⟩

/-- **A node translating an equality of the kernel**: the equality of the values
of the two variables, negated at polarity `false`. -/
theorem gval_nd_eqLit [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (l₁ l₂ : Fin (Tseitin.maxCtx φ))
    (hk : kernelNode φ p.2 = .eqLit (some (l₁ : ℕ)) (some (l₂ : ℕ))) :
    (Gval I v (ndPt B φ a₀ p true) ↔ v (dbvarPt B φ a₀ l₁) = v (dbvarPt B φ a₀ l₂)) ∧
      (Gval I v (ndPt B φ a₀ p false) ↔ v (dbvarPt B φ a₀ l₁) ≠ v (dbvarPt B φ a₀ l₂)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  have hq : qLevel B φ p = none := by rw [qLevel, hk]
  have he : eqArgs B φ p = some ((l₁ : ℕ), (l₂ : ℕ)) := by rw [eqArgs, hk]
  have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
  have hcn : ¬isConn B φ p := by rw [isConn, hk]; exact not_false
  exact ⟨(Gval_isEval hwf I v _).trans
      (gstep_eqLit_true B φ ha₀ I (Gval I) v p l₁ l₂ hq he hs hcn),
    (Gval_isEval hwf I v _).trans
      (gstep_eqLit_false B φ ha₀ I (Gval I) v p l₁ l₂ hq he hs hcn)⟩

/-- **A node translating an atom of a relation variable**: the relation the
assignment gives that variable, read at the values of the atom's arguments. -/
theorem gval_nd_blockAtom [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (μ : B.Assignment M) (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (i : B.ι)
    (junk : M) (hq : qLevel B φ p = none) (he : eqArgs B φ p = none)
    (hs : blockSym B φ p = some i) (hcn : ¬isConn B φ p) :
    (Gval (blockI B φ a₀ μ) v (ndPt B φ a₀ p true) ↔
        μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p true) junk))) ∧
      (Gval (blockI B φ a₀ μ) v (ndPt B φ a₀ p false) ↔
        ¬μ i (argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p false) junk))) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  exact ⟨(Gval_isEval hwf _ v _).trans
      (gstep_blockAtom_true B φ ha₀ μ (Gval (blockI B φ a₀ μ)) v p i junk hq he hs hcn),
    (Gval_isEval hwf _ v _).trans
      (gstep_blockAtom_false B φ ha₀ μ (Gval (blockI B φ a₀ μ)) v p i junk hq he hs hcn)⟩

/-! The truth definition at the two node kinds of a translated atom: a tuple
node is the conjunction of its literals (the disjunction, at a negatively
translated atom), and a literal is the equality it carries. -/

theorem gstep_atup_true (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (w : Fin (tagDim B φ (Tag.atup p true)) → A) (hin : isInAtom B φ p) :
    gstep I rec v (atupPt B φ a₀ p true w) ↔
      ∀ c, ChildG (atupPt B φ a₀ p true w) c → rec v c := by
  simp only [gstep]
  constructor
  · rintro (⟨-, hall⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact hall
    · have h : (true : Bool) = false ∧ isInAtom B φ p := (orG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact absurd hxy (not_eqG_atup B φ ha₀ p true w x y)
    · exact absurd hxy (not_neqG_atup B φ ha₀ p true w x y)
    · exact absurd hps (not_posG_of_ne_nd B φ _ (by simp) w s)
    · exact absurd hps (not_negG_of_ne_nd B φ _ (by simp) w s)
  · intro h
    exact Or.inl ⟨(andG_ptOf B φ ha₀ _ _).mpr ⟨rfl, hin⟩, h⟩

theorem gstep_atup_false (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (w : Fin (tagDim B φ (Tag.atup p false)) → A) (hin : isInAtom B φ p) :
    gstep I rec v (atupPt B φ a₀ p false w) ↔
      ∃ c, ChildG (atupPt B φ a₀ p false w) c ∧ rec v c := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨-, hex⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · have h : (false : Bool) = true ∧ isInAtom B φ p := (andG_ptOf B φ ha₀ _ _).mp hk
      exact absurd h.1 (by simp)
    · exact hex
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact absurd hxy (not_eqG_atup B φ ha₀ p false w x y)
    · exact absurd hxy (not_neqG_atup B φ ha₀ p false w x y)
    · exact absurd hps (not_posG_of_ne_nd B φ _ (by simp) w s)
    · exact absurd hps (not_negG_of_ne_nd B φ _ (by simp) w s)
  · intro h
    exact Or.inr (Or.inl ⟨(orG_ptOf B φ ha₀ _ _).mpr ⟨rfl, hin⟩, h⟩)

theorem gstep_alit_true (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (j : Fin (finsatDim B φ)) (a : A)
    (l : Fin (Tseitin.maxCtx φ)) (hl : inArg B φ p (j : ℕ) = some (l : ℕ)) :
    gstep I rec v (alitPt B φ a₀ p true j a) ↔
      v (dbvarPt B φ a₀ l) = v (pvarPt B φ a₀ a) := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, hv⟩ | ⟨x, y, hxy, -⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact ((andG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((orG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · obtain ⟨l', b, ⟨-, hl'⟩, rfl, rfl, rfl⟩ := (eqG_alit_iff B φ ha₀ p true j a x y).mp hxy
      rw [hl] at hl'
      rw [Fin.ext (Option.some.inj hl')]
      exact hv
    · obtain ⟨l', b, ⟨hpol, -⟩, -, -, -⟩ := (neqG_alit_iff B φ ha₀ p true j a x y).mp hxy
      exact absurd hpol (by simp)
    · exact absurd hps (not_posG_of_ne_nd B φ _ (by simp) _ s)
    · exact absurd hps (not_negG_of_ne_nd B φ _ (by simp) _ s)
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨dbvarPt B φ a₀ l, pvarPt B φ a₀ a,
        (eqG_alit_iff B φ ha₀ p true j a _ _).mpr ⟨l, a, ⟨rfl, hl⟩, rfl, rfl, rfl⟩, h⟩))))

theorem gstep_alit_false (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (rec : ((finsatInterp B φ).Map A → M) → (finsatInterp B φ).Map A → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (j : Fin (finsatDim B φ)) (a : A)
    (l : Fin (Tseitin.maxCtx φ)) (hl : inArg B φ p (j : ℕ) = some (l : ℕ)) :
    gstep I rec v (alitPt B φ a₀ p false j a) ↔
      v (dbvarPt B φ a₀ l) ≠ v (pvarPt B φ a₀ a) := by
  simp only [gstep]
  constructor
  · rintro (⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨x, y, hxy, -⟩ | ⟨x, y, hxy, hv⟩ |
      ⟨s, hps, -⟩ | ⟨s, hps, -⟩)
    · exact ((andG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((orG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((allG_ptOf B φ ha₀ _ _).mp hk).elim
    · exact ((exG_ptOf B φ ha₀ _ _).mp hk).elim
    · obtain ⟨l', b, ⟨hpol, -⟩, -, -, -⟩ := (eqG_alit_iff B φ ha₀ p false j a x y).mp hxy
      exact absurd hpol (by simp)
    · obtain ⟨l', b, ⟨-, hl'⟩, rfl, rfl, rfl⟩ := (neqG_alit_iff B φ ha₀ p false j a x y).mp hxy
      rw [hl] at hl'
      rw [Fin.ext (Option.some.inj hl')]
      exact hv
    · exact absurd hps (not_posG_of_ne_nd B φ _ (by simp) _ s)
    · exact absurd hps (not_negG_of_ne_nd B φ _ (by simp) _ s)
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨dbvarPt B φ a₀ l, pvarPt B φ a₀ a,
        (neqG_alit_iff B φ ha₀ p false j a _ _).mpr ⟨l, a, ⟨rfl, hl⟩, rfl, rfl, rfl⟩, h⟩)))))

/-- **A tuple node of a translated atom** is the conjunction of its literals, one
per argument position. -/
theorem gval_atup_true [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (w : Fin (tagDim B φ (Tag.atup p true)) → A) (hin : isInAtom B φ p) :
    Gval I v (atupPt B φ a₀ p true w) ↔
      ∀ j : Fin (finsatDim B φ), (j : ℕ) < inArity B φ p →
        Gval I v (alitPt B φ a₀ p true j (pad a₀ w j)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  rw [Gval_isEval hwf I v _, gstep_atup_true B φ ha₀ I (Gval I) v p w hin]
  constructor
  · intro h j hj
    exact h _ ((childG_atup_iff B φ ha₀ p true w _).mpr ⟨j, hj, rfl⟩)
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := (childG_atup_iff B φ ha₀ p true w c).mp hc
    exact h j hj

/-- At a negatively translated atom the tuple node is the disjunction of its
literals: negation normal form has pushed the negation to the leaves. -/
theorem gval_atup_false [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (w : Fin (tagDim B φ (Tag.atup p false)) → A) (hin : isInAtom B φ p) :
    Gval I v (atupPt B φ a₀ p false w) ↔
      ∃ j : Fin (finsatDim B φ), (j : ℕ) < inArity B φ p ∧
        Gval I v (alitPt B φ a₀ p false j (pad a₀ w j)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  rw [Gval_isEval hwf I v _, gstep_atup_false B φ ha₀ I (Gval I) v p w hin]
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨j, hj, rfl⟩ := (childG_atup_iff B φ ha₀ p false w c).mp hc
    exact ⟨j, hj, hv⟩
  · rintro ⟨j, hj, hv⟩
    exact ⟨_, (childG_atup_iff B φ ha₀ p false w _).mpr ⟨j, hj, rfl⟩, hv⟩

/-- **A node translating an atom the sentence may not mention**: the disjunction,
over the tuples where the atom holds, of the conjunctions of its literals – and
dually at polarity `false`. This is the Tseitin trick: the tuples are selected by
a *defining formula*, so the input structure is read by the interpretation and
never by the encoded sentence. -/
theorem gval_nd_inAtom [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : isConn B φ p)
    (hnokid : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 ≠ some b) :
    (Gval I v (ndPt B φ a₀ p true) ↔
        ∃ w : Fin (tagDim B φ (Tag.atup p true)) → A,
          (inAtomF B φ p).Realize
            (val₂ B φ (ptOf B φ a₀ (Tag.nd p true) fun _ => a₀)
              (ptOf B φ a₀ (Tag.atup p true) w)) ∧
            Gval I v (atupPt B φ a₀ p true w)) ∧
      (Gval I v (ndPt B φ a₀ p false) ↔
        ∀ w : Fin (tagDim B φ (Tag.atup p false)) → A,
          (inAtomF B φ p).Realize
            (val₂ B φ (ptOf B φ a₀ (Tag.nd p false) fun _ => a₀)
              (ptOf B φ a₀ (Tag.atup p false) w)) →
            Gval I v (atupPt B φ a₀ p false w)) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  have hchild : ∀ (pol : Bool) (c : (finsatInterp B φ).Map A),
      ChildG (ndPt B φ a₀ p pol) c ↔
        ∃ w : Fin (tagDim B φ (Tag.atup p pol)) → A,
          (inAtomF B φ p).Realize
            (val₂ B φ (ptOf B φ a₀ (Tag.nd p pol) fun _ => a₀)
              (ptOf B φ a₀ (Tag.atup p pol) w)) ∧ c = atupPt B φ a₀ p pol w := by
    intro pol c
    constructor
    · intro hc
      rcases (childG_nd_iff B φ ha₀ p pol c).mp hc with ⟨q, pol', hkid, -⟩ | ⟨w, hw, rfl⟩
      · exact absurd hkid (hnokid q _)
      · exact ⟨w, (childG_nd_atup B φ ha₀ p pol w).mp hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact (childG_nd_atup B φ ha₀ p pol w).mpr hw
  constructor
  · rw [Gval_isEval hwf I v _, gstep_conn_true B φ ha₀ I (Gval I) v p hq he hs hcn]
    constructor
    · rintro ⟨c, hc, hv⟩
      obtain ⟨w, hw, rfl⟩ := (hchild true c).mp hc
      exact ⟨w, hw, hv⟩
    · rintro ⟨w, hw, hv⟩
      exact ⟨_, (hchild true _).mpr ⟨w, hw, rfl⟩, hv⟩
  · rw [Gval_isEval hwf I v _, gstep_conn_false B φ ha₀ I (Gval I) v p hq he hs hcn]
    constructor
    · intro h w hw
      exact h _ ((hchild false _).mpr ⟨w, hw, rfl⟩)
    · intro h c hc
      obtain ⟨w, hw, rfl⟩ := (hchild false c).mp hc
      exact h w hw

/-- **A literal of a translated atom, evaluated**: it pins the argument at its
position to the prefix variable of the element the tuple holds there. -/
theorem gval_alit_true [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (j : Fin (finsatDim B φ)) (a : A)
    (l : Fin (Tseitin.maxCtx φ)) (hl : inArg B φ p (j : ℕ) = some (l : ℕ)) :
    Gval I v (alitPt B φ a₀ p true j a) ↔
      v (dbvarPt B φ a₀ l) = v (pvarPt B φ a₀ a) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  exact (Gval_isEval hwf I v _).trans (gstep_alit_true B φ ha₀ I (Gval I) v p j a l hl)

theorem gval_alit_false [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (p : Pos B φ) (j : Fin (finsatDim B φ)) (a : A)
    (l : Fin (Tseitin.maxCtx φ)) (hl : inArg B φ p (j : ℕ) = some (l : ℕ)) :
    Gval I v (alitPt B φ a₀ p false j a) ↔
      v (dbvarPt B φ a₀ l) ≠ v (pvarPt B φ a₀ a) := by
  haveI : Finite ((finsatInterp B φ).Map A) := FOInterpretation.map_finite _ _
  have hwf := image_isWF B φ (A := A)
  exact (Gval_isEval hwf I v _).trans (gstep_alit_false B φ ha₀ I (Gval I) v p j a l hl)

/-! ### The kernel, by induction on the formula

The node lemmas above are stated about a *position*; tying them together is an
induction on the kernel itself, carried by a
`DescriptiveComplexity.FinSat.SubEmb` – a subformula together with an embedding
of its positions into the kernel's – so that the clause of a node, which
quantifies over all the children it has *in the kernel*, collapses to the
subformula (`SubEmb.no_children`, `SubEmb.imp_children`, `SubEmb.all_children`).

Two things fall out of the same induction rather than being assumed: negation
normal form, as the second half of each statement, and the quantifier step,
where updating the environment at the variable of the level bound there is
`Fin.snoc` on the context tuple (`pref_envOf_upd`).

The model is any structure over `DescriptiveComplexity.newLang L` whose
relations are read *through* an injection `ι` of the instance – the shape an
extended universe `A ⊕ Fin m` has (`DescriptiveComplexity.relMap_ext_iff`), and
the only thing about it the translation uses. -/

/-- **The arguments of an atom of a relation variable**: the canonical
assignment of the argument positions gives, at each of them, the value of the
variable of that argument's de Bruijn level. -/
theorem argTup_argAssign (ha₀ : IsBot a₀) (v : (finsatInterp B φ).Map A → M)
    (p : Pos B φ) (pol : Bool) (i : B.ι) (hs : blockSym B φ p = some i) (junk : M)
    (j : Fin (B.arity i)) (l : Fin (Tseitin.maxCtx φ))
    (hl : blockArg B φ p (j : ℕ) = some (l : ℕ)) :
    argTup B φ a₀ i (argAssign B φ v (ndPt B φ a₀ p pol) junk) j = v (dbvarPt B φ a₀ l) := by
  classical
  have harity : B.arity i ≤ finsatDim B φ := by
    rw [← arityOf_eq (f := φ) hs]
    exact (arityOf_le φ p.2).trans (maxArity_le_finsatDim B φ)
  have hlt : (j : ℕ) < finsatDim B φ := lt_of_lt_of_le j.isLt harity
  rw [argTup, dif_pos hlt]
  exact argAssign_spec B φ v _ junk _ _
    ((argG_ptOf B φ ha₀ (Tag.nd p pol) (Tag.apos ⟨(j : ℕ), hlt⟩) (Tag.dbvar l)
      _ _ _).mpr hl)

omit [L.Structure A] [LinearOrder A] in
/-- The second point a binary defining formula of the image is read at. -/
theorem val₂_one (x y : (finsatInterp B φ).Map A) (c : Fin (finsatDim B φ)) :
    val₂ B φ x y (1, c) = y.2 c := rfl

omit [L.Structure A] [LinearOrder A] in
/-- **The de Bruijn levels of the arguments of a translated atom**, and the
values its terms take: in a relational vocabulary every argument is a variable,
so it has a level, and the value of the term is the context tuple there. -/
theorem inAtom_levels [L.IsRelational] [(newLang L).Structure M] {n k : ℕ}
    (hn : n ≤ Tseitin.maxCtx φ) (v : (finsatInterp B φ).Map A → M)
    (ts : Fin k → ((newLang L).sum B.lang).Term (Empty ⊕ Fin n)) {p : Pos B φ}
    (hia : ∀ (j : ℕ) (h : j < k), inArg B φ p j = termLevel (ts ⟨j, h⟩)) :
    ∃ lev : Fin k → Fin (Tseitin.maxCtx φ),
      (∀ j : Fin k, inArg B φ p (j : ℕ) = some ((lev j : Fin (Tseitin.maxCtx φ)) : ℕ)) ∧
        ∀ j : Fin k, (Tseitin.termToL (ts j)).realize
          (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) = v (dbvarPt B φ a₀ (lev j)) := by
  classical
  have h : ∀ j : Fin k, ∃ l : Fin (Tseitin.maxCtx φ),
      inArg B φ p (j : ℕ) = some (l : ℕ) ∧
        (Tseitin.termToL (ts j)).realize (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) =
          v (dbvarPt B φ a₀ l) := by
    intro j
    obtain ⟨l, hl, hlt⟩ := termLevel_some (B := B) (ts j)
    refine ⟨⟨l, lt_of_lt_of_le hlt hn⟩, ?_, ?_⟩
    · rw [hia (j : ℕ) j.isLt, show (⟨(j : ℕ), j.isLt⟩ : Fin k) = j from Fin.ext rfl]
      exact hl
    · rw [realize_of_termLevel hl hlt]
      exact congrArg (fun z => v (dbvarPt B φ a₀ z)) (Fin.ext rfl)
  choose lev h₁ h₂ using h
  exact ⟨lev, h₁, h₂⟩

/-- **A node translating an atom the sentence may not mention, evaluated**: the
disjunction over the tuples the defining formula selects, of the conjunctions of
the literals pinning each argument to a prefix variable, *is* the atom – read at
the values the environment gives the arguments' de Bruijn levels, through the
intended assignment `ι` of the prefix variables.

Stated once for the two shapes it serves: an atom of the input vocabulary, where
the filter `Filt` is the atom itself, and the marker `old`, where it is `⊤`. -/
theorem atom_translation [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    (I : (finsatInterp B φ).Map A → ((finsatInterp B φ).Map A → M) → Prop)
    (v : (finsatInterp B φ).Map A → M) (ι : A → M)
    (hv : ∀ b : A, v (pvarPt B φ a₀ b) = ι b) (p : Pos B φ)
    (hq : qLevel B φ p = none) (he : eqArgs B φ p = none) (hs : blockSym B φ p = none)
    (hcn : isConn B φ p) (hin : isInAtom B φ p)
    (hnokid : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 ≠ some b)
    {k : ℕ} (hdim : inArity B φ p = k) (hkd : k ≤ finsatDim B φ)
    (lev : Fin k → Fin (Tseitin.maxCtx φ))
    (hlev : ∀ j : Fin k, inArg B φ p (j : ℕ) = some ((lev j : Fin (Tseitin.maxCtx φ)) : ℕ))
    (Filt : (Fin k → A) → Prop) {Q : Prop}
    (hRW : Q ↔ ∃ y : Fin k → A, Filt y ∧ ∀ j : Fin k, v (dbvarPt B φ a₀ (lev j)) = ι (y j))
    (hfilt : ∀ (pol : Bool) (w : Fin (tagDim B φ (Tag.atup p pol)) → A),
      ((inAtomF B φ p).Realize
        (val₂ B φ (ptOf B φ a₀ (Tag.nd p pol) fun _ => a₀)
          (ptOf B φ a₀ (Tag.atup p pol) w)) ↔
        Filt fun j => pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩)) :
    (Gval I v (ndPt B φ a₀ p true) ↔ Q) ∧ (Gval I v (ndPt B φ a₀ p false) ↔ ¬Q) := by
  classical
  obtain ⟨hpos, hneg⟩ := gval_nd_inAtom B φ ha₀ I v p hq he hs hcn hnokid
  have hjt : ∀ (pol : Bool) (j : Fin k), (j : ℕ) < tagDim B φ (Tag.atup p pol) := by
    intro pol j
    rw [show tagDim B φ (Tag.atup p pol) = k from hdim]
    exact j.isLt
  -- every tuple of the atom's arity is the tuple of a tuple node
  have hofY : ∀ (pol : Bool) (y : Fin k → A),
      ∃ w : Fin (tagDim B φ (Tag.atup p pol)) → A,
        ∀ j : Fin k, pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩ = y j := by
    intro pol y
    refine ⟨fun jj => y ⟨(jj : ℕ), by rw [← hdim]; exact jj.isLt⟩, fun j => ?_⟩
    rw [pad, dif_pos (hjt pol j)]
  -- what a tuple node says, at both polarities
  have htup_true : ∀ w : Fin (tagDim B φ (Tag.atup p true)) → A,
      (Gval I v (atupPt B φ a₀ p true w) ↔
        ∀ j : Fin k, v (dbvarPt B φ a₀ (lev j)) =
          ι (pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩)) := by
    intro w
    rw [gval_atup_true B φ ha₀ I v p w hin]
    constructor
    · intro h j
      have hj : ((⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩ : Fin (finsatDim B φ)) : ℕ) <
          inArity B φ p := by rw [hdim]; exact j.isLt
      have hg := h ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩ hj
      rw [gval_alit_true B φ ha₀ I v p _ _ (lev j) (hlev j)] at hg
      rw [hg]
      exact hv _
    · intro h j hj
      have hjk : (j : ℕ) < k := by rw [← hdim]; exact hj
      rw [gval_alit_true B φ ha₀ I v p j _ (lev ⟨(j : ℕ), hjk⟩) (hlev ⟨(j : ℕ), hjk⟩), hv]
      exact (h ⟨(j : ℕ), hjk⟩).trans (congrArg (fun z => ι (pad a₀ w z)) (Fin.ext rfl))
  have htup_false : ∀ w : Fin (tagDim B φ (Tag.atup p false)) → A,
      (Gval I v (atupPt B φ a₀ p false w) ↔
        ∃ j : Fin k, v (dbvarPt B φ a₀ (lev j)) ≠
          ι (pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩)) := by
    intro w
    rw [gval_atup_false B φ ha₀ I v p w hin]
    constructor
    · rintro ⟨j, hj, hg⟩
      have hjk : (j : ℕ) < k := by rw [← hdim]; exact hj
      rw [gval_alit_false B φ ha₀ I v p j _ (lev ⟨(j : ℕ), hjk⟩) (hlev ⟨(j : ℕ), hjk⟩), hv] at hg
      exact ⟨⟨(j : ℕ), hjk⟩, fun hc =>
        hg (hc.trans (congrArg (fun z => ι (pad a₀ w z)) (Fin.ext rfl)))⟩
    · rintro ⟨j, hj⟩
      have hjd : ((⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩ : Fin (finsatDim B φ)) : ℕ) <
          inArity B φ p := by rw [hdim]; exact j.isLt
      refine ⟨⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩, hjd, ?_⟩
      rw [gval_alit_false B φ ha₀ I v p _ _ (lev j) (hlev j), hv]
      exact hj
  constructor
  · rw [hpos, hRW]
    constructor
    · rintro ⟨w, hw, hg⟩
      exact ⟨_, (hfilt true w).mp hw, (htup_true w).mp hg⟩
    · rintro ⟨y, hy, hj⟩
      obtain ⟨w, hwy⟩ := hofY true y
      have hwy' : (fun j : Fin k => pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩) = y :=
        funext hwy
      refine ⟨w, (hfilt true w).mpr ?_, (htup_true w).mpr fun j => ?_⟩
      · rw [hwy']; exact hy
      · rw [hwy j]; exact hj j
  · rw [hneg, hRW]
    constructor
    · rintro h ⟨y, hy, hj⟩
      obtain ⟨w, hwy⟩ := hofY false y
      have hwy' : (fun j : Fin k => pad a₀ w ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkd⟩) = y :=
        funext hwy
      obtain ⟨j, hjne⟩ := (htup_false w).mp (h w ((hfilt false w).mpr (by rw [hwy']; exact hy)))
      exact hjne (by rw [hwy j]; exact hj j)
    · intro h w hw
      refine (htup_false w).mpr ?_
      by_contra hc
      push Not at hc
      exact h ⟨_, (hfilt false w).mp hw, hc⟩

/-- **The translated kernel computes the kernel**: at every position of the
kernel the node of the encoded sentence at polarity `true` holds exactly when
the subformula there does, and the node at polarity `false` exactly when it does
not.

The environment gives the prefix variables their intended values `ι` and the
variables of the de Bruijn levels the context tuple; the model reads the
relations of the instance through `ι`, which is what an extended universe
does. -/
theorem gval_kernel [L.IsRelational] [Finite A] [Nonempty A] (ha₀ : IsBot a₀)
    [(newLang L).Structure M] [Nonempty M] (μ : B.Assignment M) (ι : A → M)
    (hrel : ∀ {k : ℕ} (r : L.Relations k) (u : Fin k → M),
      RelMap (L := newLang L) (Sum.inl r) u ↔
        ∃ y : Fin k → A, RelMap r y ∧ ∀ j, u j = ι (y j))
    (hold : ∀ u : Fin 1 → M,
      RelMap (L := newLang L) (Sum.inr Language.oldSym) u ↔ ∃ a : A, u 0 = ι a) :
    ∀ {n : ℕ} (f : ((newLang L).sum B.lang).BoundedFormula Empty n) (_ : SubEmb φ f)
      (hn : n ≤ Tseitin.maxCtx φ) (v : (finsatInterp B φ).Map A → M),
      (∀ b : A, v (pvarPt B φ a₀ b) = ι b) →
      (Gval (blockI B φ a₀ μ) v (ndPt B φ a₀ ⟨n, ‹SubEmb φ f›.emb (Tseitin.rootAt f)⟩ true) ↔
          Tseitin.RealizeWith μ f (pref hn (envOf B φ a₀ v))) ∧
        (Gval (blockI B φ a₀ μ) v (ndPt B φ a₀ ⟨n, ‹SubEmb φ f›.emb (Tseitin.rootAt f)⟩ false) ↔
          ¬Tseitin.RealizeWith μ f (pref hn (envOf B φ a₀ v)))
  | _, .falsum, E, hn, v, _ => by
      obtain ⟨h1, h2⟩ := gval_nd_falsum B φ ha₀ (blockI B φ a₀ μ) v E
      exact ⟨iff_of_false h1 (Tseitin.realizeWith_falsum μ _),
        iff_of_true h2 (Tseitin.realizeWith_falsum μ _)⟩
  | n, .equal t₁ t₂, E, hn, v, _ => by
      obtain ⟨l₁, hl₁, hlt₁⟩ := termLevel_some (B := B) t₁
      obtain ⟨l₂, hl₂, hlt₂⟩ := termLevel_some (B := B) t₂
      have hk : kernelNode φ (E.emb (Tseitin.rootAt (BoundedFormula.equal t₁ t₂))) =
          .eqLit (some ((⟨l₁, lt_of_lt_of_le hlt₁ hn⟩ : Fin (Tseitin.maxCtx φ)) : ℕ))
            (some ((⟨l₂, lt_of_lt_of_le hlt₂ hn⟩ : Fin (Tseitin.maxCtx φ)) : ℕ)) := by
        rw [E.node]
        change KernelNode.eqLit (termLevel t₁) (termLevel t₂) = _
        rw [hl₁, hl₂]
      obtain ⟨h1, h2⟩ := gval_nd_eqLit B φ ha₀ (blockI B φ a₀ μ) v
        ⟨n, E.emb (Tseitin.rootAt (BoundedFormula.equal t₁ t₂))⟩ _ _ hk
      have e₁ : (Tseitin.termToL t₁).realize
          (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) =
          v (dbvarPt B φ a₀ ⟨l₁, lt_of_lt_of_le hlt₁ hn⟩) := by
        rw [realize_of_termLevel hl₁ hlt₁]
        exact congrArg (fun z => v (dbvarPt B φ a₀ z)) (Fin.ext rfl)
      have e₂ : (Tseitin.termToL t₂).realize
          (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) =
          v (dbvarPt B φ a₀ ⟨l₂, lt_of_lt_of_le hlt₂ hn⟩) := by
        rw [realize_of_termLevel hl₂ hlt₂]
        exact congrArg (fun z => v (dbvarPt B φ a₀ z)) (Fin.ext rfl)
      have hval : Tseitin.RealizeWith μ (BoundedFormula.equal t₁ t₂)
          (pref hn (envOf B φ a₀ v)) ↔
          v (dbvarPt B φ a₀ ⟨l₁, lt_of_lt_of_le hlt₁ hn⟩) =
            v (dbvarPt B φ a₀ ⟨l₂, lt_of_lt_of_le hlt₂ hn⟩) := by
        rw [Tseitin.realizeWith_equal, Tseitin.eqGuard, e₁, e₂]
      exact ⟨h1.trans hval.symm, h2.trans (not_congr hval).symm⟩
  | n, .rel (l := k) R ts, E, hn, v, hv => by
      classical
      obtain ⟨p, hp⟩ : ∃ p : Pos B φ,
          p = ⟨n, E.emb (Tseitin.rootAt (BoundedFormula.rel R ts))⟩ := ⟨_, rfl⟩
      have hnode : kernelNode φ p.2 =
          kernelNode (BoundedFormula.rel R ts) (Tseitin.rootAt (BoundedFormula.rel R ts)) := by
        rw [hp]; exact E.node _
      have hnokid : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 ≠ some b := by
        rw [hp]
        intro q b hc
        exact E.no_children (fun {_} _ {_} => by simp [kidOf]) hc
      rw [← hp]
      obtain (r | o) | r := R
      · -- an atom of the instance's vocabulary: the Tseitin trick, one tuple node
        -- per tuple where the atom holds
        have hk : kernelNode φ p.2 = .inputAtom r fun j => termLevel (ts j) := hnode
        have hdim : inArity B φ p = k := by rw [inArity, inArityOf, hk]
        have hkd : k ≤ finsatDim B φ := by
          rw [← hdim]; exact (inArity_le B φ p).trans (maxArity_le_finsatDim B φ)
        have hq : qLevel B φ p = none := by rw [qLevel, hk]
        have he : eqArgs B φ p = none := by rw [eqArgs, hk]
        have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
        have hcn : isConn B φ p := by rw [isConn, hk]; trivial
        have hin : isInAtom B φ p := by rw [isInAtom, hk]; trivial
        have hia : ∀ (j : ℕ) (h : j < k), inArg B φ p j = termLevel (ts ⟨j, h⟩) := by
          intro j h
          rw [inArg, hk]
          dsimp only
          rw [dif_pos h]
        obtain ⟨lev, hlev₁, hlev₂⟩ := inAtom_levels B φ hn v ts hia
        refine atom_translation B φ ha₀ (blockI B φ a₀ μ) v ι hv p hq he hs hcn hin hnokid
          hdim hkd lev hlev₁ (RelMap r) ?_ ?_
        · refine (Tseitin.realizeWith_rel μ (Sum.inl (Sum.inl r)) ts _).trans ?_
          change Tseitin.relGuard (Sum.inl r) ts _ ↔ _
          refine (hrel r _).trans (exists_congr fun y => and_congr_right fun _ => ?_)
          exact forall_congr' fun j =>
            (by rw [hlev₂ j] : ((Tseitin.termToL (ts j)).realize
                (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) = ι (y j)) ↔
              (v (dbvarPt B φ a₀ (lev j)) = ι (y j)))
        · intro pol w
          exact realize_inAtomF_input B φ hk hkd _
      · -- the marker of the original elements: every tuple of one original element
        cases o
        have hk : kernelNode φ p.2 = .oldAtom (termLevel (ts 0)) := hnode
        have hdim : inArity B φ p = 1 := by rw [inArity, inArityOf, hk]
        have hkd : 1 ≤ finsatDim B φ := le_trans (by norm_num) (two_le_finsatDim B φ)
        have hq : qLevel B φ p = none := by rw [qLevel, hk]
        have he : eqArgs B φ p = none := by rw [eqArgs, hk]
        have hs : blockSym B φ p = none := by rw [blockSym, symOf, hk]
        have hcn : isConn B φ p := by rw [isConn, hk]; trivial
        have hin : isInAtom B φ p := by rw [isInAtom, hk]; trivial
        have hia : ∀ (j : ℕ) (h : j < 1), inArg B φ p j = termLevel (ts ⟨j, h⟩) := by
          intro j h
          rw [inArg, hk]
          dsimp only
          rw [if_pos (Nat.lt_one_iff.mp h)]
          exact congrArg (fun z : Fin 1 => termLevel (ts z)) (Subsingleton.elim _ _)
        obtain ⟨lev, hlev₁, hlev₂⟩ := inAtom_levels B φ hn v ts hia
        refine atom_translation B φ ha₀ (blockI B φ a₀ μ) v ι hv p hq he hs hcn hin hnokid
          hdim hkd lev hlev₁ (fun _ => True) ?_ ?_
        · refine (Tseitin.realizeWith_rel μ (Sum.inl (Sum.inr Language.oldSym)) ts _).trans ?_
          change Tseitin.relGuard (Sum.inr Language.oldSym) ts _ ↔ _
          refine (hold _).trans ?_
          constructor
          · rintro ⟨a, ha⟩
            refine ⟨fun _ => a, trivial, fun j => ?_⟩
            rw [show j = 0 from Subsingleton.elim _ _, ← hlev₂ 0]
            exact ha
          · rintro ⟨y, -, hy⟩
            exact ⟨y 0, (hlev₂ 0).trans (hy 0)⟩
        · intro pol w
          exact iff_of_true (realize_inAtomF_old B φ hk _) trivial
      · -- an atom of a relation variable: the only genuine atom of the sentence
        have hk : kernelNode φ p.2 = .blockAtom r fun j => termLevel (ts j) := hnode
        have hq : qLevel B φ p = none := by rw [qLevel, hk]
        have he : eqArgs B φ p = none := by rw [eqArgs, hk]
        have hs : blockSym B φ p = some r.1 := by rw [blockSym, symOf, hk]
        have hcn : ¬isConn B φ p := by rw [isConn, hk]; exact not_false
        have hba : ∀ (pol : Bool),
            argTup B φ a₀ r.1 (argAssign B φ v (ndPt B φ a₀ p pol) (Classical.arbitrary M)) =
              fun j => (Tseitin.termToL (ts (Fin.cast r.2 j))).realize
                (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) := by
          intro pol
          funext j
          have hjk : (j : ℕ) < k := lt_of_lt_of_le j.isLt r.2.le
          obtain ⟨l, hl, hlt⟩ := termLevel_some (B := B) (ts (Fin.cast r.2 j))
          have harg : blockArg B φ p (j : ℕ) =
              some ((⟨l, lt_of_lt_of_le hlt hn⟩ : Fin (Tseitin.maxCtx φ)) : ℕ) := by
            rw [blockArg, argOf, hk]
            dsimp only
            rw [dif_pos hjk]
            exact hl
          rw [argTup_argAssign B φ ha₀ v p pol r.1 hs _ j _ harg,
            realize_of_termLevel hl hlt]
          exact (congrArg (fun z => v (dbvarPt B φ a₀ z)) (Fin.ext rfl)).symm
        obtain ⟨hpos, hneg⟩ := gval_nd_blockAtom B φ ha₀ μ v p r.1 (Classical.arbitrary M)
          hq he hs hcn
        have hR : Tseitin.RealizeWith μ (BoundedFormula.rel (Sum.inr r) ts)
            (pref hn (envOf B φ a₀ v)) ↔
            μ r.1 fun j => (Tseitin.termToL (ts (Fin.cast r.2 j))).realize
              (Sum.elim isEmptyElim (pref hn (envOf B φ a₀ v))) :=
          (Tseitin.realizeWith_rel μ (Sum.inr r) ts _).trans Iff.rfl
        rw [hR]
        rw [hba true] at hpos
        rw [hba false] at hneg
        exact ⟨hpos, hneg⟩
  | n, .imp f₁ f₂, E, hn, v, hv => by
      classical
      set p : Pos B φ := ⟨n, E.emb (Tseitin.rootAt (f₁.imp f₂))⟩ with hp
      set p₁ : Pos B φ := ⟨n, E.impL.emb (Tseitin.rootAt f₁)⟩ with hp₁
      set p₂ : Pos B φ := ⟨n, E.impR.emb (Tseitin.rootAt f₂)⟩ with hp₂
      have hk : kernelNode φ p.2 = .impl := (E.node _).trans (kernelNode_imp f₁ f₂)
      have h1 : kidOf φ p.2 p₁.2 = some true :=
        (E.kid (Tseitin.rootAt (f₁.imp f₂)) (Sum.inr (Sum.inl (Tseitin.rootAt f₁)))).trans
          (kidOf_imp_left f₁ f₂)
      have h2 : kidOf φ p.2 p₂.2 = some false :=
        (E.kid (Tseitin.rootAt (f₁.imp f₂)) (Sum.inr (Sum.inr (Tseitin.rootAt f₂)))).trans
          (kidOf_imp_right f₁ f₂)
      have henum : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 = some b →
          (b = true ∧ q = p₁) ∨ (b = false ∧ q = p₂) :=
        fun q b hq => E.imp_children (q := q.2) hq
      obtain ⟨hpos, hneg⟩ :=
        gval_nd_impl B φ ha₀ (blockI B φ a₀ μ) v p p₁ p₂ hk h1 h2 henum
      obtain ⟨i₁, i₂⟩ := gval_kernel ha₀ μ ι hrel hold f₁ E.impL hn v hv
      obtain ⟨j₁, j₂⟩ := gval_kernel ha₀ μ ι hrel hold f₂ E.impR hn v hv
      rw [Tseitin.realizeWith_imp]
      refine ⟨hpos.trans ?_, hneg.trans ?_⟩
      · rw [i₂, j₁]
        constructor
        · rintro (hc | hc) h₁
          · exact absurd h₁ hc
          · exact hc
        · intro h
          by_cases hc : Tseitin.RealizeWith μ f₁ (pref hn (envOf B φ a₀ v))
          · exact Or.inr (h hc)
          · exact Or.inl hc
      · rw [i₁, j₂]
        constructor
        · rintro ⟨h₁, h₂⟩ hc
          exact h₂ (hc h₁)
        · intro h
          by_cases hc : Tseitin.RealizeWith μ f₁ (pref hn (envOf B φ a₀ v))
          · exact ⟨hc, fun h₂ => h fun _ => h₂⟩
          · exact absurd (fun h₁ => absurd h₁ hc) h
  | n, .all f, E, hn, v, hv => by
      classical
      set p : Pos B φ := ⟨n, E.emb (Tseitin.rootAt f.all)⟩ with hp
      set p' : Pos B φ := ⟨n + 1, E.allB.emb (Tseitin.rootAt f)⟩ with hp'
      have hn1 : n + 1 ≤ Tseitin.maxCtx φ := Tseitin.nodeAt_le_maxCtx φ p'.2
      have hnlt : n < Tseitin.maxCtx φ := hn1
      have hk : kernelNode φ p.2 =
          .quant ((⟨n, hnlt⟩ : Fin (Tseitin.maxCtx φ)) : ℕ) := (E.node _).trans (kernelNode_all f)
      have h1 : kidOf φ p.2 p'.2 = some false :=
        (E.kid (Tseitin.rootAt f.all) (Sum.inr (Tseitin.rootAt f))).trans (kidOf_all_body f)
      have henum : ∀ (q : Pos B φ) (b : Bool), kidOf φ p.2 q.2 = some b → b = false ∧ q = p' :=
        fun q b hq => E.all_children (q := q.2) hq
      obtain ⟨hpos, hneg⟩ :=
        gval_nd_quant B φ ha₀ (blockI B φ a₀ μ) v p p' ⟨n, hnlt⟩ hk h1 henum
      have hupd : ∀ (d : M) (b : A),
          upd v (dbvarPt B φ a₀ ⟨n, hnlt⟩) d (pvarPt B φ a₀ b) = ι b := by
        intro d b
        refine (upd_of_ne _ _ ?_).trans (hv b)
        intro hc
        have h1 : (Tag.pvar : FTag B φ) = Tag.dbvar ⟨n, hnlt⟩ := congrArg Prod.fst hc
        exact absurd h1 (by simp)
      have hbody : ∀ d : M,
          (Gval (blockI B φ a₀ μ) (upd v (dbvarPt B φ a₀ ⟨n, hnlt⟩) d)
              (ndPt B φ a₀ p' true) ↔
            Tseitin.RealizeWith μ f (Fin.snoc (pref hn (envOf B φ a₀ v)) d)) ∧
          (Gval (blockI B φ a₀ μ) (upd v (dbvarPt B φ a₀ ⟨n, hnlt⟩) d)
              (ndPt B φ a₀ p' false) ↔
            ¬Tseitin.RealizeWith μ f (Fin.snoc (pref hn (envOf B φ a₀ v)) d)) := by
        intro d
        obtain ⟨i₁, i₂⟩ := gval_kernel ha₀ μ ι hrel hold f E.allB hn1
          (upd v (dbvarPt B φ a₀ ⟨n, hnlt⟩) d) (hupd d)
        rw [pref_envOf_upd B φ v hnlt d] at i₁ i₂
        exact ⟨i₁, i₂⟩
      rw [Tseitin.realizeWith_all]
      refine ⟨hpos.trans (forall_congr' fun d => (hbody d).1), hneg.trans ?_⟩
      constructor
      · rintro ⟨d, hd⟩ hc
        exact ((hbody d).2.mp hd) (hc d)
      · intro h
        obtain ⟨d, hd⟩ : ∃ d : M, ¬Tseitin.RealizeWith μ f
            (Fin.snoc (pref hn (envOf B φ a₀ v)) d) := by
          by_contra hc
          exact h fun d => not_not.mp fun hd => hc ⟨d, hd⟩
        exact ⟨d, (hbody d).2.mpr hd⟩

end Hardness

end FinSat

end DescriptiveComplexity
