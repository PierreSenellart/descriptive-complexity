/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.RE
import Mathlib.Computability.PartrecBasis
import DescriptiveComplexity.Problems.Machine.HaltHard.Bridge
import DescriptiveComplexity.Computability.Eval

/-!
# The input chain: getting the instance into the machine

`Turing.ToPartrec.Code.exists_code` gives codes for fixed-arity functions
only, so the machine cannot be started on the variable-length bit table of
the instance. The continuation stack solves this: since a `comp` frame
applies its code to the value below it, a **chain of `comp` frames** applies
a fixed code once per frame – one frame per bit
(`DescriptiveComplexity.HaltHard.inputChain`). Each bit frame pushes its bit
(`Turing.ToPartrec.Code.zero'`, or the three-node
`DescriptiveComplexity.HaltHard.pushOne`), the next frame folds it into the
accumulator (`2·acc + b`, by a code `exists_code` supplies), and the last
frame runs the semi-decision procedure on the folded number and the universe
size.

The number the chain folds is the flattened relation table of the instance
read back one binary digit at a time
(`DescriptiveComplexity.HaltHard.structOfBits`, with
`DescriptiveComplexity.HaltHard.structOfBits_flatten` the roundtrip): a
`FirstOrder.Language.FinStruct` *is* a size and a table, so decoding owes
only digit arithmetic, and it is primitive recursive
(`DescriptiveComplexity.HaltHard.primrec_structOfBits`) – which is what lets
the `Part.assert` trick of `orderedReduction_codehalt` run behind
`Nat.Partrec'.part_iff₂`. The bits enter the chain most significant first,
i.e. the flattened table reversed
(`DescriptiveComplexity.HaltHard.foldl_two_reverse`).

The chain is pure `comp` frames, so its frame region is a run of bare
headers (`DescriptiveComplexity.HaltHard.frameSeg_inputChain`), and its
evaluation is total until the final procedure
(`DescriptiveComplexity.HaltHard.inputChain_dom_iff`).
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec FirstOrder Language Structure

/-! ### Bits, numbers and flattened tables -/

/-- The number whose binary digits are the listed bits, least significant
first. -/
def natOfBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * natOfBits l

/-- The digits of `natOfBits` are the listed bits. -/
theorem digitAt_natOfBits : ∀ (l : List Bool) (j : ℕ),
    digitAt 2 (natOfBits l) j = (l.getD j false).toNat := by
  intro l
  induction l with
  | nil => intro j; simp [natOfBits, digitAt]
  | cons b l ih =>
    intro j
    cases j with
    | zero =>
      change (b.toNat + 2 * natOfBits l) / 2 ^ 0 % 2 = _
      rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      cases b <;> rfl
    | succ j =>
      change (b.toNat + 2 * natOfBits l) / 2 ^ (j + 1) % 2 = _
      have hdiv : (b.toNat + 2 * natOfBits l) / 2 ^ (j + 1) = natOfBits l / 2 ^ j := by
        rw [pow_succ, mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
        congr 1
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
        cases b <;> simp
      rw [hdiv]
      exact ih j

/-- Folding bits most significant first computes `natOfBits` of their
reversal. -/
theorem foldl_two_reverse : ∀ (l : List Bool) (acc : ℕ),
    List.foldl (fun a b => 2 * a + b.toNat) acc l.reverse =
      acc * 2 ^ l.length + natOfBits l := by
  intro l
  induction l with
  | nil => intro acc; simp [natOfBits]
  | cons b l ih =>
    intro acc
    rw [List.reverse_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, natOfBits, List.length_cons]
    ring

/-- Reading a flattened list of rows at a prefix-sum offset reads inside the
row. -/
theorem flatten_getD {α : Type} (d : α) : ∀ (l : List (List α)) (i : ℕ)
    (_ : i < l.length) {t : ℕ}, t < (l.getD i []).length →
    l.flatten.getD ((((l.take i).map List.length).sum) + t) d = (l.getD i []).getD t d := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi t ht
    cases i with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
      simp only [List.getD_cons_zero] at ht ⊢
      exact List.getD_append _ _ _ _ ht
    | succ i =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      simp only [List.getD_cons_succ] at ht ⊢
      rw [Nat.add_assoc, List.getD_append_right _ _ _ _ (by omega),
        Nat.add_sub_cancel_left]
      exact ih i (by simpa using hi) ht

/-- Reading every position of a list back through `getD` is the list. -/
theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun t => l.getD t d) = l := by
  refine List.ext_getElem (by simp) ?_
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem l d (by simpa using h2)]

/-! ### Decoding a number into a structure -/

variable {L : Language.{0, 0}} (V : FinVocab L)

/-- The offset of the row of symbol `i` inside the flattened table, over a
universe of size `c`. -/
def offB (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => offB c i + (if h : i < V.numSyms then c ^ V.arity ⟨i, h⟩ else 0)

/-- The offsets are the prefix sums of the row lengths. -/
theorem offB_eq_sum (c : ℕ) : ∀ i : ℕ, i ≤ V.numSyms →
    offB V c i = (((List.finRange V.numSyms).take i).map fun i' => c ^ V.arity i').sum := by
  intro i
  induction i with
  | zero => intro; simp [offB]
  | succ i ih =>
    intro hi
    have hlt : i < V.numSyms := by omega
    rw [offB, ih (by omega), dif_pos hlt, List.take_add_one]
    have hget : (List.finRange V.numSyms)[i]? = some ⟨i, hlt⟩ := by
      rw [List.getElem?_eq_getElem (by simpa using hlt)]
      simp
    rw [hget]
    simp

/-- **Decoding a number into a concrete structure**: the universe has size
`k + 1`, and the relation tables read the binary digits of `N`, row by row at
the offsets of `DescriptiveComplexity.HaltHard.offB`. -/
def structOfBits (k N : ℕ) : FinStruct V :=
  ⟨k, List.ofFn fun i : Fin V.numSyms =>
    (List.range ((k + 1) ^ V.arity i)).map fun t =>
      decide (digitAt 2 N (offB V (k + 1) i + t) = 1)⟩

/-- Reading a Boolean digit back. -/
theorem decide_toNat_eq_one (b : Bool) : decide (b.toNat = 1) = b := by
  cases b <;> rfl

/-- **The roundtrip**: decoding the number of the flattened table of a
well-shaped concrete structure gives the structure back. -/
theorem structOfBits_flatten (s : FinStruct V)
    (hlen : s.table.length = V.numSyms)
    (hrow : ∀ i : Fin V.numSyms, (s.table.getD i []).length = s.card ^ V.arity i) :
    structOfBits V s.univSize (natOfBits s.table.flatten) = s := by
  obtain ⟨k, table⟩ := s
  simp only [FinStruct.card] at hrow
  simp only at hlen
  simp only [structOfBits, FinStruct.mk.injEq, true_and]
  refine List.ext_getElem (by simp [hlen]) ?_
  intro i h1 h2
  have hi : i < V.numSyms := by simpa using h1
  simp only [List.getElem_ofFn]
  have hoff : offB V (k + 1) i =
      (((table.take i).map List.length).sum) := by
    rw [offB_eq_sum V _ i (by omega)]
    congr 1
    refine List.ext_getElem (by simp [hlen]) ?_
    intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_take]
    have hj : j < V.numSyms := by
      simp only [List.length_map, List.length_take, List.length_finRange] at hj1
      omega
    rw [List.getElem_finRange, ← List.getD_eq_getElem table ([] : List Bool)
      (by omega : j < table.length)]
    exact (hrow ⟨j, hj⟩).symm
  have hrow' : table.getD i ([] : List Bool) = table[i] :=
    List.getD_eq_getElem _ _ (by omega)
  have hlen' : (table.getD i []).length = (k + 1) ^ V.arity ⟨i, hi⟩ := hrow ⟨i, hi⟩
  rw [← hrow']
  conv_rhs => rw [← range_map_getD (table.getD i []) false]
  rw [hlen']
  refine List.map_congr_left ?_
  intro t ht
  have htlt : t < (table.getD i []).length := by
    rw [hlen']
    simpa using ht
  rw [digitAt_natOfBits, hoff]
  rw [flatten_getD false table i (by omega) htlt]
  exact decide_toNat_eq_one _

/-- The tables of `FirstOrder.Language.FinStruct.ofEquiv` are well-shaped:
one row per symbol. -/
theorem length_table_ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (k : ℕ) (e : Fin (k + 1) ≃ A) :
    (FinStruct.ofEquiv V k e).table.length = V.numSyms := by
  simp [FinStruct.ofEquiv, FinStruct.ofTable]

/-- The rows of `FirstOrder.Language.FinStruct.ofEquiv` have the lengths the
offsets expect. -/
theorem length_row_ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (k : ℕ) (e : Fin (k + 1) ≃ A) (i : Fin V.numSyms) :
    ((FinStruct.ofEquiv V k e).table.getD i []).length =
      (FinStruct.ofEquiv V k e).card ^ V.arity i := by
  have hget : (FinStruct.ofEquiv V k e).table.getD i [] =
      (List.range ((k + 1) ^ V.arity i)).map fun t =>
        decide (RelMap (V.sym i) fun j =>
          e ⟨digitAt (k + 1) t j, digitAt_lt (Nat.succ_pos k) t j⟩) := by
    change (FinStruct.ofTable V k _).table.getD i [] = _
    rw [FinStruct.ofTable, List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [hget]
  simp [FinStruct.ofEquiv, FinStruct.ofTable, FinStruct.card]

/-- **Decoding the folded table of an instance gives the instance's concrete
presentation.** -/
theorem structOfBits_ofEquiv [L.IsRelational] {A : Type} [L.Structure A]
    [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
    (k : ℕ) (e : Fin (k + 1) ≃ A) :
    structOfBits V k (natOfBits (FinStruct.ofEquiv V k e).table.flatten) =
      FinStruct.ofEquiv V k e :=
  structOfBits_flatten V _ (length_table_ofEquiv V k e) (length_row_ofEquiv V k e)

/-! ### The decoder is primitive recursive -/

theorem primrec_offB (i : ℕ) : Primrec fun c : ℕ => offB V c i := by
  induction i with
  | zero => exact Primrec.const 0
  | succ i ih =>
    by_cases h : i < V.numSyms
    · have : (fun c : ℕ => offB V c (i + 1)) =
          fun c : ℕ => offB V c i + c ^ V.arity ⟨i, h⟩ := by
        funext c
        rw [offB, dif_pos h]
      rw [this]
      exact Primrec.nat_add.comp ih (primrec_pow_const _)
    · have : (fun c : ℕ => offB V c (i + 1)) = fun c : ℕ => offB V c i := by
        funext c
        rw [offB, dif_neg h]
        omega
      rw [this]
      exact ih

/-- Powers of two are primitive recursive in the exponent. -/
theorem primrec_two_pow : Primrec fun x : ℕ => 2 ^ x := by
  have h : Primrec fun x : ℕ => (fun y : ℕ => 2 * y)^[x] 1 :=
    Primrec.nat_iterate Primrec.id (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂)
  refine h.of_eq fun x => ?_
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    ring

/-- **The decoder is primitive recursive**, as a function of the pair –
what the `Part.assert` code needs. -/
theorem primrec_structOfBits : Primrec fun p : ℕ × ℕ => structOfBits V p.1 p.2 := by
  have hmk := FinStruct.primrec_mk (V := V)
  refine (hmk.comp Primrec.fst ?_).of_eq fun p => rfl
  refine Primrec.list_ofFn fun i => ?_
  have hrange : Primrec fun p : ℕ × ℕ => List.range ((p.1 + 1) ^ V.arity i) :=
    Primrec.list_range.comp
      ((primrec_pow_const (V.arity i)).comp (Primrec.succ.comp Primrec.fst))
  refine (Primrec.list_map hrange ?_).of_eq fun p => rfl
  have hpos : Primrec fun q : (ℕ × ℕ) × ℕ => offB V (q.1.1 + 1) i + q.2 :=
    Primrec.nat_add.comp
      ((primrec_offB V i).comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  have hdigit : Primrec fun q : (ℕ × ℕ) × ℕ =>
      digitAt 2 q.1.2 (offB V (q.1.1 + 1) i + q.2) :=
    Primrec.nat_mod.comp
      (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst) (primrec_two_pow.comp hpos))
      (Primrec.const 2)
  exact (((Primrec.eq.comp hdigit (Primrec.const 1)).decide).of_eq fun _ => rfl).to₂

/-! ### The pushed bits, and the fold -/

/-- The code pushing a `1` in front of the value: `v ↦ 1 :: v`. -/
def pushOne : Code := .cons (.comp .succ .zero') Code.id

theorem eval_pushOne (v : List ℕ) : pushOne.eval v = pure (1 :: v) := by
  simp [pushOne, Code.eval]

/-- The code pushing a bit. -/
def pushBit (b : Bool) : Code := if b then pushOne else .zero'

theorem eval_pushBit (b : Bool) (v : List ℕ) : (pushBit b).eval v = pure (b.toNat :: v) := by
  cases b
  · simp [pushBit]
  · rw [pushBit, if_pos rfl, eval_pushOne]
    rfl

section Codes

/-- The fold specification: `2·acc + b`, of the vector `[b, acc, n]`. -/
def foldSpec : List.Vector ℕ 3 →. ℕ := fun v => Part.some (2 * v.get 1 + v.get 0)

variable (cF : Code) (hF : ∀ v : List.Vector ℕ 3, cF.eval v.1 = pure <$> foldSpec v)

/-- The fold code: replace the pushed bit and the accumulator by their fold,
keep the rest of the value. -/
def foldCode : Code := .cons cF (.comp .tail .tail)

include hF in
theorem eval_foldCode (b acc n : ℕ) :
    (foldCode cF).eval [b, acc, n] = pure [2 * acc + b, n] := by
  have hcf := hF ⟨[b, acc, n], rfl⟩
  simp only [foldSpec] at hcf
  have hget : (2 : ℕ) * List.Vector.get (⟨[b, acc, n], rfl⟩ : List.Vector ℕ 3) 1 +
      List.Vector.get (⟨[b, acc, n], rfl⟩ : List.Vector ℕ 3) 0 = 2 * acc + b := rfl
  rw [hget] at hcf
  simp [foldCode, Code.eval, hcf]

/-! ### The chain -/

variable (cP : Code)

/-- The global code the machine simulates: a container for the two bit
pushes, the fold, and the semi-decision procedure. It is never dispatched at
its root – only the positions of its four components are. -/
def allCode : Code := .cons (.zero') (.cons pushOne (.cons (foldCode cF) cP))

/-- The position of `Turing.ToPartrec.Code.zero'` in the container. -/
def posBit0 : CPos (allCode cF cP) := Sum.inr (Sum.inl ())

/-- The position of the one-push in the container. -/
def posBit1 : CPos (allCode cF cP) :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (cRoot pushOne))))

/-- The position of a bit push. -/
def posBit (b : Bool) : CPos (allCode cF cP) := if b then posBit1 cF cP else posBit0 cF cP

/-- The position of the fold in the container. -/
def posFold : CPos (allCode cF cP) :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (cRoot (foldCode cF)))))))

/-- The position of the semi-decision procedure in the container. -/
def posProc : CPos (allCode cF cP) :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (cRoot cP))))))

@[simp] theorem codeAt_posBit0 : codeAt (posBit0 cF cP) = Code.zero' := rfl

@[simp] theorem codeAt_posBit1 : codeAt (posBit1 cF cP) = pushOne := rfl

@[simp] theorem codeAt_posFold : codeAt (posFold cF cP) = foldCode cF := rfl

@[simp] theorem codeAt_posProc : codeAt (posProc cF cP) = cP := by
  change codeAt (cRoot cP) = cP
  exact codeAt_cRoot cP

@[simp] theorem codeAt_posBit (b : Bool) : codeAt (posBit cF cP b) = pushBit b := by
  cases b
  · rw [posBit, if_neg (by simp), pushBit, if_neg (by simp)]
    exact codeAt_posBit0 cF cP
  · rw [posBit, if_pos rfl, pushBit, if_pos rfl]
    exact codeAt_posBit1 cF cP

/-- **The input chain**: one `comp` frame pushing each bit, one folding it
in, and a last frame running the procedure. -/
def inputChain : List Bool → PCont (allCode cF cP)
  | [] => .comp (posProc cF cP) .halt
  | b :: bits => .comp (posBit cF cP b) (.comp (posFold cF cP) (inputChain bits))

/-- Evaluating a pending composition is composing the evaluations. -/
theorem cont_eval_comp (f : Code) (k : Cont) (v : List ℕ) :
    (Cont.comp f k).eval v = f.eval v >>= fun w => k.eval w := rfl

/-- The frame region of the chain: a run of bare `comp` headers. -/
theorem frameSeg_inputChain : ∀ bits : List Bool,
    FrameSeg (inputChain cF cP bits)
      (bits.flatMap (fun b => [SimSym.hComp (posBit cF cP b), SimSym.hComp (posFold cF cP)]) ++
        [SimSym.hComp (posProc cF cP)])
  | [] => by
    simpa [inputChain] using FrameSeg.comp FrameSeg.halt
  | b :: bits => by
    simpa [inputChain] using FrameSeg.comp (FrameSeg.comp (frameSeg_inputChain bits))

include hF in
/-- Evaluating the chain folds the bits and hands the result to the
procedure. -/
theorem cont_eval_inputChain : ∀ (bits : List Bool) (acc n : ℕ),
    (inputChain cF cP bits).toCont.eval [acc, n] =
      cP.eval [bits.foldl (fun a b => 2 * a + b.toNat) acc, n] := by
  intro bits
  induction bits with
  | nil =>
    intro acc n
    have h0 : (inputChain cF cP []).toCont = Cont.comp cP Cont.halt := by
      change Cont.comp (codeAt (posProc cF cP)) Cont.halt = _
      rw [codeAt_posProc]
    rw [h0, cont_eval_comp]
    have hh : Cont.eval Cont.halt = pure := rfl
    rw [hh, bind_pure]
    rfl
  | cons b bits ih =>
    intro acc n
    have h1 : (inputChain cF cP (b :: bits)).toCont =
        Cont.comp (pushBit b) (Cont.comp (foldCode cF) (inputChain cF cP bits).toCont) := by
      change Cont.comp (codeAt (posBit cF cP b))
        (Cont.comp (codeAt (posFold cF cP)) (inputChain cF cP bits).toCont) = _
      rw [codeAt_posBit, codeAt_posFold]
    rw [h1, cont_eval_comp, eval_pushBit, pure_bind, cont_eval_comp,
      eval_foldCode cF hF, pure_bind, ih]
    rfl

end Codes

/-! ### The procedure, and the whole chain -/

variable {V}

open Nat.Partrec' in
/-- **The two codes of the chain exist**: a fold code, and a code whose
halting on the folded number and the size decides the problem. -/
theorem exists_chain_codes [L.IsRelational] (P : DecisionProblem L)
    (h : REPred (P.toPred V)) :
    ∃ cF cP : Code, (∀ v : List.Vector ℕ 3, cF.eval v.1 = pure <$> foldSpec v) ∧
      ∀ N n : ℕ, ((cP.eval [N, n]).Dom ↔ P.toPred V (structOfBits V (n - 1) N)) := by
  obtain ⟨cF, hcF⟩ := Code.exists_code (n := 3) (f := foldSpec) (by
    rw [part_iff]
    refine Computable.partrec ?_
    have h1 : Computable fun v : List.Vector ℕ 3 => v.get 1 :=
      Primrec.to_comp (Primrec.vector_get.comp .id (.const 1))
    have h0 : Computable fun v : List.Vector ℕ 3 => v.get 0 :=
      Primrec.to_comp (Primrec.vector_get.comp .id (.const 0))
    exact Primrec.to_comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (.const 2) (Primrec.vector_get.comp .id (.const 1)))
      (Primrec.vector_get.comp .id (.const 0))))
  have hpart : Partrec₂ fun N n : ℕ =>
      (Part.assert (P.toPred V (structOfBits V (n - 1) N)) fun _ => Part.some ()).map
        fun _ => (0 : ℕ) := by
    have hs : Computable fun p : ℕ × ℕ => structOfBits V (p.2 - 1) p.1 :=
      Primrec.to_comp ((primrec_structOfBits V).comp
        (Primrec.pair (Primrec.pred.comp Primrec.snd) Primrec.fst))
    exact (h.comp hs).map ((Computable.const (0 : ℕ)).comp Computable.fst).to₂
  have hpart' := part_iff₂.mpr hpart
  obtain ⟨cP, hcP⟩ := Code.exists_code hpart'
  refine ⟨cF, cP, hcF, fun N n => ?_⟩
  have h2 := hcP ⟨[N, n], rfl⟩
  change ((cP.eval (⟨[N, n], rfl⟩ : List.Vector ℕ 2).1).Dom ↔ _)
  rw [h2]
  simp only [Part.map, Part.assert]
  exact ⟨fun hh => hh.1, fun hp => ⟨hp, trivial⟩⟩

/-- **What the chain decides**: started on `[0, n]` under the chain of the
reversed flattened table, the machine's abstract evaluation terminates
exactly when the decoded instance is a yes-instance. -/
theorem inputChain_dom_iff [L.IsRelational] (P : DecisionProblem L) {cF cP : Code}
    (hF : ∀ v : List.Vector ℕ 3, cF.eval v.1 = pure <$> foldSpec v)
    (hP : ∀ N n : ℕ, ((cP.eval [N, n]).Dom ↔ P.toPred V (structOfBits V (n - 1) N)))
    (bits : List Bool) (n : ℕ) :
    ((inputChain cF cP bits.reverse).toCont.eval [0, n]).Dom ↔
      P.toPred V (structOfBits V (n - 1) (natOfBits bits)) := by
  rw [cont_eval_inputChain cF hF cP, foldl_two_reverse]
  simp only [Nat.zero_mul, Nat.zero_add]
  exact hP _ n

end HaltHard

end DescriptiveComplexity
