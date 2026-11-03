/-
Mirror of `Lax751879.StructureEncoding`: lax-751879, “The Immerman–Vardi theorem”, formalized by
Szymon Toruńczyk with GPT 6, https://github.com/szymtor/immerman-vardi at commit
9fa09900c827396420a8bcfd22bc624e5c980a53. Released under Apache 2.0 license.
-/
import DescriptiveComplexity.Strings.Lax.OrderedStructures
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Action.Defs

/-!
# Binary encodings of ordered structures and tuples

Encode a structure of size `n` by `n` one-bits and a zero-bit, followed by the
characteristic tables of its relations in vocabulary order, each listing tuples
in lexicographic order. The distinguished order is determined by `n` and needs
no table. Each coordinate `a` of the query tuple is appended as `a` one-bits and
a zero-bit.

The fixed vocabulary and query arity determine all table boundaries, so the
encoding is injective (`encodeInjective`), and its length is computed by
`encodeLength`.
-/

namespace DescriptiveComplexity.Strings.Lax.StructureEncoding

open OrderedStructures

/-- All tuples, with the first coordinate varying slowest. -/
def tuples (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (tuples n k).map (Fin.cons a)

/-- The unary code of a natural number. -/
def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

/-- The binary encoding of a pointed structure. -/
def encode {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) : List Bool :=
  unary A.structureValue.size ++
    (List.finRange σ.length).flatMap (fun r =>
      (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)) ++
    (List.finRange k).flatMap (fun i => unary (A.tuple i).val)

private theorem length_tuples (n k : Nat) : (tuples n k).length = n ^ k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
    simp only [tuples, List.length_flatMap, List.length_map, ih, List.map_const',
      List.length_finRange, List.sum_replicate, smul_eq_mul]
    exact (Nat.pow_succ' ..).symm

private theorem mem_tuples {n k : Nat} (t : Fin k → Fin n) : t ∈ tuples n k := by
  induction k with
  | zero => simpa [tuples] using Subsingleton.elim _ _
  | succ k ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨t 0, Fin.tail t, ih _, Fin.cons_self_tail t⟩

/-- A list starting with a unary code gives the coded number away. -/
private theorem unary_append_inj {a b : Nat} {l l' : List Bool}
    (h : unary a ++ l = unary b ++ l') : a = b ∧ l = l' := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [unary] using h
    | succ b => simp [unary, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [unary, List.replicate_succ] at h
    | succ b =>
      simp only [unary, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hab, hl⟩ := ih (b := b) (by simpa [unary] using h)
      exact ⟨by omega, hl⟩

/-- Tables of equal shapes that agree as concatenated lists agree table by table. -/
private theorem flatMap_append_inj {ι : Type} {α : Type} (is : List ι) (f g : ι → List α)
    {l l' : List α}
    (hlen : ∀ i ∈ is, (f i).length = (g i).length)
    (h : is.flatMap f ++ l = is.flatMap g ++ l') :
    (∀ i ∈ is, f i = g i) ∧ l = l' := by
  induction is with
  | nil => simpa using h
  | cons i is ih =>
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (hlen i (by simp))
    obtain ⟨h₃, h₄⟩ := ih (fun j hj => hlen j (by simp [hj])) h₂
    refine ⟨fun j hj => ?_, h₄⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h₁
    · exact h₃ j hj

/-- The unary coordinates of two tuples determine the tuples. -/
private theorem flatMap_unary_inj {ι : Type} (is : List ι) (f g : ι → Nat)
    (h : is.flatMap (fun i => unary (f i)) = is.flatMap (fun i => unary (g i))) :
    ∀ i ∈ is, f i = g i := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := unary_append_inj h
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h₁
    · exact ih h₂ j hj

theorem encodeInjective (σ : Vocabulary) (k : Nat) :
    Function.Injective (@encode σ k) := by
  rintro ⟨⟨n, R⟩, t⟩ ⟨⟨n', R'⟩, t'⟩ h
  simp only [encode, List.append_assoc] at h
  obtain ⟨rfl, h⟩ := unary_append_inj h
  obtain ⟨hR, ht⟩ := flatMap_append_inj _ _ _ (by simp) h
  have hR' : R = R' := by
    funext r a
    have h₁ := hR r (List.mem_finRange r)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_tuples a)
    have h₂ := List.getElem_of_eq h₁ (by simpa using hi)
    simpa using h₂
  have ht' : t = t' := by
    funext i
    exact Fin.ext (flatMap_unary_inj _ _ _ ht i (List.mem_finRange i))
  subst hR' ht'
  rfl

theorem encodeLength {σ : Vocabulary} {k : Nat} (A : PointedStructure σ k) :
    (encode A).length = A.structureValue.size + 1 +
      (σ.map (fun r => A.structureValue.size ^ r)).sum +
      ((List.finRange k).map (fun i => (A.tuple i).val + 1)).sum := by
  have h₁ : ((List.finRange σ.length).flatMap (fun r =>
      (tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r))).length =
      (σ.map (fun r => A.structureValue.size ^ r)).sum := by
    rw [List.length_flatMap]
    have : (List.finRange σ.length).map (fun r =>
        ((tuples A.structureValue.size (σ.get r)).map (A.structureValue.relation r)).length) =
        σ.map (fun r => A.structureValue.size ^ r) := by
      apply List.ext_getElem <;> simp [length_tuples]
    rw [this]
  have h₂ : ((List.finRange k).flatMap (fun i => unary (A.tuple i).val)).length =
      ((List.finRange k).map (fun i => (A.tuple i).val + 1)).sum := by
    rw [List.length_flatMap]
    simp [unary]
  rw [encode, List.length_append, List.length_append, h₁, h₂]
  simp [unary]

end DescriptiveComplexity.Strings.Lax.StructureEncoding
