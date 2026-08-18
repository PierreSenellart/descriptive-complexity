/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Interp
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Draw
import DescriptiveComplexity.Problems.Machine.Halt

/-!
# The drawn instance is a well-formed machine embedding the simulator

The semantic half of the correctness of the drawing: the drawn structure's
machine data is well-formed (`DescriptiveComplexity.HaltHard.wellFormed_halt`),
and its machine predicates are exactly the images of
`DescriptiveComplexity.HaltHard.simTM`'s along the embedding that places each
machine element on the canonically padded bottom tuple
(`DescriptiveComplexity.HaltHard.tmEmbed_halt`). The enumeration of the
cells and the initial tape are the next file's business; this one only
speaks about tags and tuples.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec FirstOrder Language Structure

variable {L : Language.{0, 0}} {V : FinVocab L} {cF cP : Code}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### Canonical tuples -/

omit [L.Structure A] in
/-- A tuple canonical at `0` is the bottom tuple. -/
theorem eq_botTup_of_canon0 {w : Fin (dimOf V) → A} (h : Canon 0 w) : w = botTup V A := by
  funext j
  exact le_antisymm (h j (Nat.zero_le _) _) (isBot_botA _)

/-- The machine element `u`, as the point of the drawn instance with the
bottom tuple. -/
noncomputable def mEl (u : SimU (allCode cF cP)) : (haltTuringInterp V cF cP).Map A :=
  hPt (Sum.inl u) (botTup V A)

/-! ### The embedding of the simulating machine -/

theorem unary_embed_iff (Q : SimU (allCode cF cP) → Prop) (R : Language.turingRel 1)
    (hR : ∀ ts : Fin 1 → HTag V cF cP,
      (haltTuringInterp V cF cP).relFormula R ts = mUnaryF V cF cP Q (ts 0))
    (b : (haltTuringInterp V cF cP).Map A) :
    (RelMap (show Language.turing.Relations 1 from R) ![b] : Prop) ↔ ∃ u, b = mEl u ∧ Q u := by
  obtain ⟨t, w, rfl⟩ := exists_hPt b
  rw [relMap_unary Q R hR t w]
  constructor
  · rintro ⟨⟨u, rfl, hu⟩, hc⟩
    refine ⟨u, ?_, hu⟩
    rw [mEl, eq_botTup_of_canon0 hc]
  · rintro ⟨u, heq, hu⟩
    have h1 : t = Sum.inl u := congrArg Prod.fst heq
    have h2 : w = botTup V A := congrArg Prod.snd heq
    exact ⟨⟨u, h1, hu⟩, h2 ▸ canon_botTup 0⟩

theorem binary_embed_iff (Q : SimU (allCode cF cP) → SimU (allCode cF cP) → Prop)
    (R : Language.turingRel 2)
    (hR : ∀ ts : Fin 2 → HTag V cF cP,
      (haltTuringInterp V cF cP).relFormula R ts = mBinaryF V cF cP Q (ts 0) (ts 1))
    (b b' : (haltTuringInterp V cF cP).Map A) :
    (RelMap (show Language.turing.Relations 2 from R) ![b, b'] : Prop) ↔
      ∃ u u', b = mEl u ∧ b' = mEl u' ∧ Q u u' := by
  obtain ⟨t, w, rfl⟩ := exists_hPt b
  obtain ⟨t', w', rfl⟩ := exists_hPt b'
  rw [relMap_binary Q R hR t t' w w']
  constructor
  · rintro ⟨⟨u, u', rfl, rfl, hu⟩, hc, hc'⟩
    refine ⟨u, u', ?_, ?_, hu⟩
    · rw [mEl, eq_botTup_of_canon0 hc]
    · rw [mEl, eq_botTup_of_canon0 hc']
  · rintro ⟨u, u', heq, heq', hu⟩
    have h1 : t = Sum.inl u := congrArg Prod.fst heq
    have h2 : w = botTup V A := congrArg Prod.snd heq
    have h1' : t' = Sum.inl u' := congrArg Prod.fst heq'
    have h2' : w' = botTup V A := congrArg Prod.snd heq'
    exact ⟨⟨u, u', h1, h1', hu⟩, h2 ▸ canon_botTup 0, h2' ▸ canon_botTup 0⟩

/-- **The drawn machine embeds the simulating machine**: every machine
predicate of the drawn structure is the image of `simTM`'s along `mEl`. -/
theorem tmEmbed_halt :
    TMEmbed (mEl (V := V) (cF := cF) (cP := cP) (A := A)) (simTM (allCode cF cP))
      (tmData ((haltTuringInterp V cF cP).Map A)) := by
  constructor
  · intro u u' h
    have h1 : Sum.inl (β := CellTag V) u = Sum.inl u' := congrArg Prod.fst h
    simpa using h1
  · exact unary_embed_iff (simTM (allCode cF cP)).Tr .tr fun _ => rfl
  · exact unary_embed_iff (simTM (allCode cF cP)).Start .start fun _ => rfl
  · exact unary_embed_iff (simTM (allCode cF cP)).Acc .acc fun _ => rfl
  · exact unary_embed_iff (simTM (allCode cF cP)).Blank .blank fun _ => rfl
  · exact unary_embed_iff (simTM (allCode cF cP)).Right .right fun _ => rfl
  · intro b b'
    exact binary_embed_iff (simTM (allCode cF cP)).Src .tsrc (fun _ => rfl) b b'
  · intro b b'
    exact binary_embed_iff (simTM (allCode cF cP)).Read .tread (fun _ => rfl) b b'
  · intro b b'
    exact binary_embed_iff (simTM (allCode cF cP)).Dst .tdst (fun _ => rfl) b b'
  · intro b b'
    exact binary_embed_iff (simTM (allCode cF cP)).Write .twrite (fun _ => rfl) b b'

/-! ### The letter of a cell is unique -/

omit [Finite A] [Nonempty A] in
/-- The letter `DescriptiveComplexity.HaltHard.InpOn` relates to a cell is
unique. -/
theorem inpOn_functional {c : CellTag V} {u u' : SimU (allCode cF cP)}
    {w : Fin (dimOf V) → A} (h : InpOn V cF cP c u w) (h' : InpOn V cF cP c u' w) :
    u = u' := by
  rcases c with - | i | i | - | - | - | - | - | - | - <;>
    simp only [InpOn] at h h'
  case cBit i =>
    rcases h with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;> rcases h' with ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ <;>
      first
      | rfl
      | exact absurd hb' hb
      | exact absurd hb hb'
  all_goals rw [h, h']

/-! ### The drawn machine is well-formed -/

/-- **The drawn machine data is well-formed.** -/
theorem wellFormed_halt :
    (tmData ((haltTuringInterp V cF cP).Map A)).WellFormed := by
  refine ⟨?_, ⟨hPt (Sum.inr .cEndL) (botTup V A), ?_⟩, ?_, ⟨mEl (sts .bk), ?_⟩, ?_⟩
  · refine IsLinOrd.of_equiv (Equiv.refl _) (fun b b' => ?_) (isLinOrd_hLe V cF cP)
    obtain ⟨t, w, rfl⟩ := exists_hPt b
    obtain ⟨t', w', rfl⟩ := exists_hPt b'
    exact (relMap_le t t' w w').symm
  · exact (relMap_posn _ _).mpr ⟨.cEndL, rfl, canon_botTup _⟩
  · intro p a b ha hb
    obtain ⟨tp, wp, rfl⟩ := exists_hPt p
    obtain ⟨ta, wa, rfl⟩ := exists_hPt a
    obtain ⟨tb, wb, rfl⟩ := exists_hPt b
    obtain ⟨c, u, hc, hu, -, hcan0, hio⟩ := (relMap_inp _ _ _ _).mp ha
    obtain ⟨c', u', hc', hu', -, hcan0', hio'⟩ := (relMap_inp _ _ _ _).mp hb
    have hcc : c' = c := by
      rw [hc] at hc'
      simpa using hc'.symm
    rw [hcc] at hio'
    have huu : u = u' := inpOn_functional hio hio'
    rw [hu, hu', huu, eq_botTup_of_canon0 hcan0, eq_botTup_of_canon0 hcan0']
  · exact (unary_embed_iff (simTM (allCode cF cP)).Blank .blank (fun _ => rfl) _).mpr
      ⟨sts .bk, rfl, rfl⟩
  · intro a b ha hb
    obtain ⟨u, rfl, hu⟩ := (unary_embed_iff (simTM (allCode cF cP)).Blank .blank
      (fun _ => rfl) a).mp ha
    obtain ⟨u', rfl, hu'⟩ := (unary_embed_iff (simTM (allCode cF cP)).Blank .blank
      (fun _ => rfl) b).mp hb
    obtain rfl : u = sts SimSym.bk := hu
    obtain rfl : u' = sts SimSym.bk := hu'
    rfl

/-! ### Tuple numbers

The reversed lexicographic order on tuples is comparison of their numbers –
the little-endian `DescriptiveComplexity.tupleIdx` of the coordinates read
through the numbering. One direction is proved arithmetically; the other
falls out of trichotomy and injectivity. -/

section TupleNumbers

variable (k : ℕ) (e : Fin (k + 1) ≃o A)

/-- Splitting the number of a concatenation. -/
theorem tupleIdx_append (c : ℕ) : ∀ l₁ l₂ : List ℕ,
    tupleIdx c (l₁ ++ l₂) = tupleIdx c l₁ + c ^ l₁.length * tupleIdx c l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a l ih =>
    intro l₂
    simp only [List.cons_append, tupleIdx_cons, ih, List.length_cons, pow_succ]
    ring

/-- The number of a tuple, read through the numbering. -/
noncomputable def tupN (w : Fin (dimOf V) → A) : ℕ :=
  tupleIdx (k + 1) (List.ofFn fun j => (e.symm (w j) : ℕ))

omit [L.Structure A] [Finite A] [Nonempty A] in
/-- **Reversed lexicographic comparison is comparison of the numbers.** -/
theorem tupN_lt_of_revLexLt {u w : Fin (dimOf V) → A} (h : RevLexLt u w) :
    tupN k e u < tupN k e w := by
  obtain ⟨j, hj, htl⟩ := h
  have hkey : ∀ P Tu Tw au aw X : ℕ, Tu < P → Tw < P → au < aw →
      Tu + P * (au + X) < Tw + P * (aw + X) := by
    intro P Tu Tw au aw X hTu hTw haw
    calc Tu + P * (au + X) < P + P * (au + X) := by omega
      _ = P * (au + X + 1) := by ring
      _ ≤ P * (aw + X) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ Tw + P * (aw + X) := Nat.le_add_left _ _
  have hsplit : ∀ v : Fin (dimOf V) → A,
      tupN k e v = tupleIdx (k + 1) ((List.ofFn fun j' => (e.symm (v j') : ℕ)).take j) +
        (k + 1) ^ (j : ℕ) *
          ((e.symm (v j) : ℕ) + (k + 1) *
            tupleIdx (k + 1) ((List.ofFn fun j' => (e.symm (v j') : ℕ)).drop ((j : ℕ) + 1))) := by
    intro v
    have hlen : (j : ℕ) < (List.ofFn fun j' => (e.symm (v j') : ℕ)).length := by
      simp
    have hdrop : (List.ofFn fun j' => (e.symm (v j') : ℕ)).drop (j : ℕ) =
        (e.symm (v j) : ℕ) :: (List.ofFn fun j' => (e.symm (v j') : ℕ)).drop ((j : ℕ) + 1) := by
      rw [List.drop_eq_getElem_cons hlen]
      simp
    have htake := List.take_append_drop (j : ℕ) (List.ofFn fun j' => (e.symm (v j') : ℕ))
    calc tupN k e v = tupleIdx (k + 1)
          ((List.ofFn fun j' => (e.symm (v j') : ℕ)).take (j : ℕ) ++
            (List.ofFn fun j' => (e.symm (v j') : ℕ)).drop (j : ℕ)) := by
            rw [htake]; rfl
      _ = _ := by
        rw [tupleIdx_append, hdrop, tupleIdx_cons, List.length_take_of_le (by omega)]
  have hdropeq : (List.ofFn fun j' => (e.symm (u j') : ℕ)).drop ((j : ℕ) + 1) =
      (List.ofFn fun j' => (e.symm (w j') : ℕ)).drop ((j : ℕ) + 1) := by
    refine List.ext_getElem (by simp) ?_
    intro m h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    have hm : (j : ℕ) < (j : ℕ) + 1 + m := by omega
    congr 1
    refine congrArg _ (htl _ ?_)
    exact hm
  rw [hsplit u, hsplit w, hdropeq]
  refine hkey _ _ _ _ _ _ ?_ ?_ ?_
  · have h := tupleIdx_lt (c := k + 1)
      (l := (List.ofFn fun j' => (e.symm (u j') : ℕ)).take (j : ℕ)) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ : ∃ j', a = (e.symm (u j') : ℕ) := by
          have := List.mem_of_mem_take ha
          obtain ⟨j', rfl⟩ := List.mem_ofFn.mp this
          exact ⟨j', rfl⟩
        exact (e.symm (u b)).isLt)
    have hlen : ((List.ofFn fun j' => (e.symm (u j') : ℕ)).take (j : ℕ)).length = (j : ℕ) := by
      simp only [List.length_take, List.length_ofFn]
      omega
    rwa [hlen] at h
  · have h := tupleIdx_lt (c := k + 1)
      (l := (List.ofFn fun j' => (e.symm (w j') : ℕ)).take (j : ℕ)) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ : ∃ j', a = (e.symm (w j') : ℕ) := by
          have := List.mem_of_mem_take ha
          obtain ⟨j', rfl⟩ := List.mem_ofFn.mp this
          exact ⟨j', rfl⟩
        exact (e.symm (w b)).isLt)
    have hlen : ((List.ofFn fun j' => (e.symm (w j') : ℕ)).take (j : ℕ)).length = (j : ℕ) := by
      simp only [List.length_take, List.length_ofFn]
      omega
    rwa [hlen] at h
  · exact e.symm.strictMono hj

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem tupN_inj {u w : Fin (dimOf V) → A} (h : tupN k e u = tupN k e w) : u = w := by
  funext j
  have hu := digitAt_tupleIdx (c := k + 1)
    (l := List.ofFn fun j' => (e.symm (u j') : ℕ)) (by
      intro a ha
      obtain ⟨j', rfl⟩ := List.mem_ofFn.mp ha
      exact (e.symm (u j')).isLt) (j := (j : ℕ)) (by simp)
  have hw := digitAt_tupleIdx (c := k + 1)
    (l := List.ofFn fun j' => (e.symm (w j') : ℕ)) (by
      intro a ha
      obtain ⟨j', rfl⟩ := List.mem_ofFn.mp ha
      exact (e.symm (w j')).isLt) (j := (j : ℕ)) (by simp)
  rw [show tupleIdx (k + 1) (List.ofFn fun j' => (e.symm (u j') : ℕ)) = tupN k e u from rfl] at hu
  rw [show tupleIdx (k + 1) (List.ofFn fun j' => (e.symm (w j') : ℕ)) = tupN k e w from rfl] at hw
  rw [h] at hu
  have heq : ((e.symm (u j) : ℕ)) = ((e.symm (w j) : ℕ)) := by
    have h1 : (List.ofFn fun j' => (e.symm (u j') : ℕ)).getD (j : ℕ) 0 = (e.symm (u j) : ℕ) := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have h2 : (List.ofFn fun j' => (e.symm (w j') : ℕ)).getD (j : ℕ) 0 = (e.symm (w j) : ℕ) := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [← h1, ← h2, ← hu, ← hw]
  have := congrArg e (Fin.ext heq : e.symm (u j) = e.symm (w j))
  simpa using this

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem revLexLt_of_tupN_lt {u w : Fin (dimOf V) → A} (h : tupN k e u < tupN k e w) :
    RevLexLt u w := by
  rcases revLexLt_trichotomy u w with h1 | rfl | h1
  · exact h1
  · omega
  · exact absurd (tupN_lt_of_revLexLt k e h1) (by omega)

end TupleNumbers

/-! ### The cells of the input page -/

section Cells

variable (V cF cP)
variable (k : ℕ) (e : Fin (k + 1) ≃o A)

omit [L.Structure A] in
theorem eSymm_botOrd : e.symm (botOrd A) = 0 := by
  have hall : ∀ y : Fin (k + 1), e.symm (botOrd A) ≤ y := by
    intro y
    have h := isBot_botA (A := A) (e y)
    have h2 := e.symm.monotone h
    simpa using h2
  exact le_antisymm (hall 0) (Fin.zero_le _)

/-- The tuple of the bit cell numbered `t` in the block of symbol `i`. -/
noncomputable def tupOf (i : Fin V.numSyms) (t : ℕ) : Fin (dimOf V) → A :=
  pad (botOrd A) fun j : Fin (V.arity i) =>
    e ⟨digitAt (k + 1) t (j : ℕ), digitAt_lt (Nat.succ_pos k) t _⟩

omit [L.Structure A] in
theorem canon_tupOf (i : Fin V.numSyms) (t : ℕ) : Canon (V.arity i) (tupOf V k e i t) :=
  canon_pad isBot_botA _ _

omit [L.Structure A] in
/-- The number of a bit cell's tuple is its index. -/
theorem tupN_tupOf (i : Fin V.numSyms) {t : ℕ} (ht : t < (k + 1) ^ V.arity i) :
    tupN k e (tupOf V k e i t) = t := by
  have harl : V.arity i ≤ dimOf V := arity_le_dimOf V i
  have hofn : (List.ofFn fun j => (e.symm (tupOf V k e i t j) : ℕ)) =
      List.ofFn fun j : Fin (dimOf V) => digitAt (k + 1) t (j : ℕ) := by
    refine congrArg List.ofFn (funext fun j => ?_)
    by_cases hj : (j : ℕ) < V.arity i
    · rw [tupOf, pad, dif_pos hj]
      simp
    · rw [tupOf, pad, dif_neg hj]
      rw [eSymm_botOrd]
      have hdig : digitAt (k + 1) t (j : ℕ) = 0 := by
        rw [digitAt, Nat.div_eq_of_lt, Nat.zero_mod]
        exact ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hdig]
      rfl
  rw [tupN, hofn, tupleIdx_ofFn_digitAt]
  exact Nat.mod_eq_of_lt (ht.trans_le (Nat.pow_le_pow_right (by omega) harl))

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem tupleIdx_eq_zero {c : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a = 0) → tupleIdx c l = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [tupleIdx_cons, h a (by simp), tupleIdx_eq_zero fun b hb => h b (by simp [hb])]
    simp

omit [L.Structure A] in
/-- The number of a tuple canonical at an arity stays below the block cap. -/
theorem tupN_lt_cap_of_canon {i : Fin V.numSyms} {w : Fin (dimOf V) → A}
    (hcan : Canon (V.arity i) w) : tupN k e w < (k + 1) ^ V.arity i := by
  have harl : V.arity i ≤ dimOf V := arity_le_dimOf V i
  have hsplit : tupN k e w =
      tupleIdx (k + 1) ((List.ofFn fun j => (e.symm (w j) : ℕ)).take (V.arity i)) +
        (k + 1) ^ V.arity i * tupleIdx (k + 1)
          ((List.ofFn fun j => (e.symm (w j) : ℕ)).drop (V.arity i)) := by
    rw [tupN]
    conv_lhs => rw [← List.take_append_drop (V.arity i)
      (List.ofFn fun j => (e.symm (w j) : ℕ))]
    rw [tupleIdx_append, List.length_take_of_le (by simp [harl])]
  have hdrop0 : tupleIdx (k + 1)
      ((List.ofFn fun j => (e.symm (w j) : ℕ)).drop (V.arity i)) = 0 := by
    refine tupleIdx_eq_zero fun a ha => ?_
    rw [List.mem_drop_iff_getElem] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    simp only [List.getElem_ofFn]
    have hidx : V.arity i + m < dimOf V := by
      simp only [List.length_ofFn] at hm
      omega
    have hbotm := hcan ⟨V.arity i + m, hidx⟩ (by simp)
    have hwm : w ⟨V.arity i + m, hidx⟩ = botOrd A :=
      le_antisymm (hbotm _) (isBot_botA _)
    rw [hwm, eSymm_botOrd]
    rfl
  rw [hsplit, hdrop0, Nat.mul_zero, Nat.add_zero]
  have hb := tupleIdx_lt (c := k + 1)
    (l := (List.ofFn fun j => (e.symm (w j) : ℕ)).take (V.arity i)) (by
      intro a ha
      have hmem := List.mem_of_mem_take ha
      obtain ⟨j', rfl⟩ := List.mem_ofFn.mp hmem
      exact (e.symm (w j')).isLt)
  have hlen : ((List.ofFn fun j => (e.symm (w j) : ℕ)).take (V.arity i)).length =
      V.arity i := by
    simp [harl]
  rwa [hlen] at hb

omit [L.Structure A] in
/-- A tuple canonical at an arity is the tuple of its number's bit cell. -/
theorem eq_tupOf_of_canon {i : Fin V.numSyms} {w : Fin (dimOf V) → A}
    (hcan : Canon (V.arity i) w) : w = tupOf V k e i (tupN k e w) :=
  (tupN_inj k e (by rw [tupN_tupOf V k e i (tupN_lt_cap_of_canon V k e hcan)])).symm

/-- The chain indices, in tape order: symbols descending, tuple numbers
descending inside each block. -/
def bitIdx : List (Fin V.numSyms × ℕ) :=
  (List.finRange V.numSyms).reverse.flatMap fun i =>
    ((List.range ((k + 1) ^ V.arity i)).reverse).map fun t => (i, t)

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem mem_bitIdx {p : Fin V.numSyms × ℕ} :
    p ∈ bitIdx V k ↔ p.2 < (k + 1) ^ V.arity p.1 := by
  rcases p with ⟨i, t⟩
  simp [bitIdx]

/-- The two chain cells of a bit. -/
noncomputable def pairCells (p : Fin V.numSyms × ℕ) :
    List ((haltTuringInterp V cF cP).Map A) :=
  [hPt (Sum.inr (.cBit p.1)) (tupOf V k e p.1 p.2),
   hPt (Sum.inr (.cFold p.1)) (tupOf V k e p.1 p.2)]

/-- The chain cells, in tape order. -/
noncomputable def chainCells : List ((haltTuringInterp V cF cP).Map A) :=
  (bitIdx V k).flatMap (pairCells V cF cP k e)

/-- The digit cells of the spelled size, in tape order – elements
descending. -/
noncomputable def oneCells : List ((haltTuringInterp V cF cP).Map A) :=
  ((List.finRange (k + 1)).reverse).map fun a =>
    hPt (Sum.inr .cOne) (pad (botOrd A) fun _ : Fin 1 => e a)

/-- **The cells of the drawn instance, in tape order.** -/
noncomputable def psH : List ((haltTuringInterp V cF cP).Map A) :=
  hPt (Sum.inr .cEndL) (botTup V A) ::
    (chainCells V cF cP k e ++
      hPt (Sum.inr .cProc) (botTup V A) :: hPt (Sum.inr .cMid) (botTup V A) ::
      hPt (Sum.inr .cGap) (botTup V A) :: hPt (Sum.inr .cComL) (botTup V A) ::
      (oneCells V cF cP k e ++
        [hPt (Sum.inr .cComR) (botTup V A), hPt (Sum.inr .cEndR) (botTup V A)]))

/-! ### Membership: the cells are exactly the positions -/

/-- Every listed cell is a position. -/
theorem posn_of_mem_psH {p : (haltTuringInterp V cF cP).Map A} (hp : p ∈ psH V cF cP k e) :
    (tmData ((haltTuringInterp V cF cP).Map A)).Posn p := by
  change TMPosn p
  simp only [psH, List.mem_cons, List.mem_append, List.mem_cons] at hp
  rcases hp with rfl | hp | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  · rw [chainCells, List.mem_flatMap] at hp
    obtain ⟨q, -, hq⟩ := hp
    simp only [pairCells, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_tupOf V k e q.1 q.2⟩
    · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_tupOf V k e q.1 q.2⟩
  rcases hp with rfl | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  rcases hp with rfl | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  rcases hp with rfl | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  rcases hp with rfl | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  rcases hp with hp | hp
  · rw [oneCells, List.mem_map] at hp
    obtain ⟨a, -, rfl⟩ := hp
    exact (relMap_posn _ _).mpr ⟨_, rfl, canon_pad isBot_botA _ _⟩
  rcases hp with rfl | hp
  · exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩
  obtain rfl : p = hPt (Sum.inr .cEndR) (botTup V A) := by simpa using hp
  exact (relMap_posn _ _).mpr ⟨_, rfl, canon_botTup _⟩

/-- Every position is a listed cell. -/
theorem mem_psH_of_posn {p : (haltTuringInterp V cF cP).Map A}
    (hp : (tmData ((haltTuringInterp V cF cP).Map A)).Posn p) : p ∈ psH V cF cP k e := by
  obtain ⟨t, w, rfl⟩ := exists_hPt p
  obtain ⟨c, rfl, hcan⟩ := (relMap_posn t w).mp hp
  have hbot : ∀ _ : CellTag.used V c = 0, w = botTup V A := fun h0 =>
    eq_botTup_of_canon0 (h0 ▸ hcan)
  rcases c with - | i | i | - | - | - | - | - | - | -
  · rw [hbot rfl]
    simp [psH]
  · rw [eq_tupOf_of_canon V k e hcan]
    refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    rw [chainCells, List.mem_flatMap]
    refine ⟨(i, tupN k e w), ?_, ?_⟩
    · rw [mem_bitIdx]
      exact tupN_lt_cap_of_canon V k e hcan
    · rw [pairCells]
      simp
  · rw [eq_tupOf_of_canon V k e hcan]
    refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    rw [chainCells, List.mem_flatMap]
    refine ⟨(i, tupN k e w), ?_, ?_⟩
    · rw [mem_bitIdx]
      exact tupN_lt_cap_of_canon V k e hcan
    · rw [pairCells]
      simp
  · rw [hbot rfl]
    simp [psH]
  · rw [hbot rfl]
    simp [psH]
  · rw [hbot rfl]
    simp [psH]
  · rw [hbot rfl]
    simp [psH]
  · -- a digit cell
    have h1d : 1 ≤ dimOf V := dimOf_pos V
    have hpadw : pad (botOrd A) (pref h1d w) = w := pad_pref_of_canon isBot_botA h1d hcan
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))))
    rw [oneCells, List.mem_map]
    refine ⟨e.symm (w ⟨0, h1d⟩), by simp, ?_⟩
    have hfun : (fun _ : Fin 1 => e (e.symm (w ⟨0, h1d⟩))) = pref h1d w := by
      funext j
      simp only [OrderIso.apply_symm_apply, pref]
      exact congrArg w (Fin.ext (by simp))
    rw [hfun, hpadw]
  · rw [hbot rfl]
    simp [psH]
  · rw [hbot rfl]
    simp [psH]

/-! ### The initial letters -/

variable [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]

/-- The bit drawn at a bit cell: the table entry of the presentation. -/
noncomputable def bitAt (i : Fin V.numSyms) (t : ℕ) : Bool :=
  decide (RelMap (V.sym i) fun j : Fin (V.arity i) =>
    e ⟨digitAt (k + 1) t (j : ℕ), digitAt_lt (Nat.succ_pos k) t _⟩)

/-- The drawn bit reads the source relation at the cell's tuple. -/
theorem bitAt_iff_bitOf (i : Fin V.numSyms) (t : ℕ) :
    bitAt V k e i t = true ↔ bitOf V i (tupOf V k e i t) := by
  rw [bitAt, decide_eq_true_iff, bitOf]
  refine iff_of_eq (congrArg _ (funext fun j => ?_))
  rw [tupOf, pad, dif_pos (show ((Fin.castLE (arity_le_dimOf V i) j : Fin (dimOf V)) : ℕ) <
    V.arity i from j.isLt)]
  exact congrArg _ (Fin.ext rfl)

/-- **The initial letters, cell by cell.** -/
noncomputable def inpH : List ((haltTuringInterp V cF cP).Map A) :=
  mEl (sts .endL) ::
    ((bitIdx V k).flatMap (fun p =>
      [mEl (sts (.hComp (posBit cF cP (bitAt V k e p.1 p.2)))),
       mEl (sts (.hComp (posFold cF cP)))]) ++
      mEl (sts (.hComp (posProc cF cP))) :: mEl (sts .mid) :: mEl (sts .bk) ::
      mEl (sts .com) ::
      (List.replicate (k + 1) (mEl (sts .one)) ++ [mEl (sts .com), mEl (sts .endR)]))

end Cells

/-! ### The enumeration is strictly ordered -/

section Enumeration

variable (V cF cP)
variable (k : ℕ) (e : Fin (k + 1) ≃o A)

/-- The strict order of the drawn machine. -/
def SLt (p q : (haltTuringInterp V cF cP).Map A) : Prop :=
  (tmData ((haltTuringInterp V cF cP).Map A)).Le p q ∧ p ≠ q

omit [Finite A] [Nonempty A] in
theorem sLt_intro {t t' : HTag V cF cP} {w w' : Fin (dimOf V) → A}
    (hle : HLe V cF cP (t, w) (t', w')) (hne : t ≠ t' ∨ w ≠ w') :
    SLt V cF cP (hPt t w) (hPt t' w') := by
  refine ⟨(relMap_le t t' w w').mpr hle, fun heq => ?_⟩
  have h1 : t = t' := congrArg Prod.fst heq
  have h2 : w = w' := congrArg Prod.snd heq
  rcases hne with h | h
  · exact h h1
  · exact h h2

omit [Finite A] [Nonempty A] in
theorem sLt_of_blockLt {t t' : HTag V cF cP} (h : blockIdx V cF cP t < blockIdx V cF cP t')
    (w w' : Fin (dimOf V) → A) : SLt V cF cP (hPt t w) (hPt t' w') :=
  sLt_intro V cF cP (Or.inl h)
    (Or.inl fun heq => absurd h (by rw [heq]; exact lt_irrefl _))

omit [Finite A] [Nonempty A] in
theorem sLt_of_revLex {t t' : HTag V cF cP} (hb : blockIdx V cF cP t = blockIdx V cF cP t')
    {w w' : Fin (dimOf V) → A} (h : RevLexLt w' w) :
    SLt V cF cP (hPt t w) (hPt t' w') :=
  sLt_intro V cF cP (Or.inr ⟨hb, Or.inl h⟩)
    (Or.inr fun heq => RevLexLt.irrefl (heq ▸ h))

omit [Finite A] [Nonempty A] in
theorem sLt_bit_fold (i : Fin V.numSyms) (w : Fin (dimOf V) → A) :
    SLt V cF cP (hPt (Sum.inr (.cBit i)) w) (hPt (Sum.inr (.cFold i)) w) :=
  sLt_intro V cF cP (Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.zero_le _⟩⟩) (Or.inl (by simp))

theorem sLt_one {a a' : Fin (k + 1)} (h : a' < a) :
    SLt V cF cP (hPt (Sum.inr .cOne) (pad (botOrd A) fun _ : Fin 1 => e a))
      (hPt (Sum.inr .cOne) (pad (botOrd A) fun _ : Fin 1 => e a')) := by
  refine sLt_of_revLex V cF cP rfl ⟨⟨0, dimOf_pos V⟩, ?_, ?_⟩
  · rw [pad, dif_pos (by simp : ((⟨0, dimOf_pos V⟩ : Fin (dimOf V)) : ℕ) < 1),
      pad, dif_pos (by simp : ((⟨0, dimOf_pos V⟩ : Fin (dimOf V)) : ℕ) < 1)]
    exact e.strictMono h
  · intro j' hj'
    have hj1 : ¬((j' : ℕ) < 1) := by
      have : (0 : ℕ) < (j' : ℕ) := hj'
      omega
    rw [pad, dif_neg hj1, pad, dif_neg hj1]

/-- Pairwise over a `flatMap`, from pairwise inside each image and pairwise
across the images. -/
theorem pairwise_flatMap {α β : Type} {R : β → β → Prop} {f : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).Pairwise R) →
      l.Pairwise (fun a b => ∀ x ∈ f a, ∀ y ∈ f b, R x y) →
      (l.flatMap f).Pairwise R
  | [], _, _ => by simp
  | a :: l, hin, hcross => by
    rw [List.flatMap_cons, List.pairwise_append]
    rw [List.pairwise_cons] at hcross
    refine ⟨hin a (by simp), pairwise_flatMap (fun b hb => hin b (by simp [hb])) hcross.2,
      fun x hx y hy => ?_⟩
    rw [List.mem_flatMap] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    exact hcross.1 b hb x hx y hyb

/-- Later chain indices are smaller: symbols descending, tuple numbers
descending inside a symbol. -/
def BitLt (p q : Fin V.numSyms × ℕ) : Prop :=
  (q.1 : ℕ) < (p.1 : ℕ) ∨ (q.1 = p.1 ∧ q.2 < p.2)

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem pairwise_bitIdx : (bitIdx V k).Pairwise (BitLt V) := by
  rw [bitIdx]
  refine pairwise_flatMap (fun i _ => ?_) ?_
  · rw [List.pairwise_map, List.pairwise_reverse]
    refine (List.pairwise_lt_range).imp ?_
    intro a b h
    exact Or.inr ⟨rfl, h⟩
  · rw [List.pairwise_reverse]
    have hfin : (List.finRange V.numSyms).Pairwise (· < ·) := by
      have h := List.pairwise_lt_range (n := V.numSyms)
      have hmap : (List.finRange V.numSyms).map Fin.val = List.range V.numSyms := by
        simp
      rw [← hmap, List.pairwise_map] at h
      exact h.imp fun hab => hab
    refine hfin.imp ?_
    intro i i' h p hp q hq
    rw [List.mem_map] at hp hq
    obtain ⟨t, -, rfl⟩ := hp
    obtain ⟨t', -, rfl⟩ := hq
    exact Or.inl h

theorem pairwise_chainCells : (chainCells V cF cP k e).Pairwise (SLt V cF cP) := by
  rw [chainCells]
  refine pairwise_flatMap (fun p _ => ?_) ?_
  · rw [pairCells]
    refine List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)
    obtain rfl : y = hPt (Sum.inr (.cFold p.1)) (tupOf V k e p.1 p.2) := by simpa using hy
    exact sLt_bit_fold V cF cP p.1 _
  · refine List.Pairwise.imp_of_mem ?_ (pairwise_bitIdx V k)
    intro p q hp hq hpq x hx y hy
    simp only [pairCells, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hpq with h | ⟨h1, h2⟩
    · have hb : ∀ cp cq : CellTag V,
          (cp = .cBit p.1 ∨ cp = .cFold p.1) → (cq = .cBit q.1 ∨ cq = .cFold q.1) →
          blockIdx V cF cP (Sum.inr cp) < blockIdx V cF cP (Sum.inr cq) := by
        have hpl := p.1.isLt
        rintro cp cq (rfl | rfl) (rfl | rfl) <;> simp only [blockIdx] <;> omega
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        exact sLt_of_blockLt V cF cP (hb _ _ (by simp) (by simp)) _ _
    · have hrev : RevLexLt (tupOf V k e q.1 q.2) (tupOf V k e p.1 p.2) := by
        refine revLexLt_of_tupN_lt k e ?_
        have hcapp : p.2 < (k + 1) ^ V.arity p.1 := (mem_bitIdx V k).mp hp
        have hcapq : q.2 < (k + 1) ^ V.arity q.1 := (mem_bitIdx V k).mp hq
        rw [h1] at hcapq ⊢
        rw [tupN_tupOf V k e _ hcapq, tupN_tupOf V k e _ hcapp]
        exact h2
      have hbeq : ∀ cp cq : CellTag V,
          (cp = .cBit p.1 ∨ cp = .cFold p.1) → (cq = .cBit q.1 ∨ cq = .cFold q.1) →
          blockIdx V cF cP (Sum.inr cp) = blockIdx V cF cP (Sum.inr cq) := by
        rintro cp cq (rfl | rfl) (rfl | rfl) <;> simp only [blockIdx] <;> rw [h1]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        exact sLt_of_revLex V cF cP (hbeq _ _ (by simp) (by simp)) hrev

theorem pairwise_oneCells : (oneCells V cF cP k e).Pairwise (SLt V cF cP) := by
  rw [oneCells]
  rw [List.pairwise_map, List.pairwise_reverse]
  have hfin : (List.finRange (k + 1)).Pairwise (· < ·) := by
    have h := List.pairwise_lt_range (n := k + 1)
    have hmap : (List.finRange (k + 1)).map Fin.val = List.range (k + 1) := by
      simp
    rw [← hmap, List.pairwise_map] at h
    exact h.imp fun hab => hab
  exact hfin.imp fun h => sLt_one V cF cP k e h

omit [L.Structure A] in
theorem tag_of_mem_chainCells {x : (haltTuringInterp V cF cP).Map A}
    (hx : x ∈ chainCells V cF cP k e) :
    ∃ (i : Fin V.numSyms) (w : Fin (dimOf V) → A),
      x = hPt (Sum.inr (.cBit i)) w ∨ x = hPt (Sum.inr (.cFold i)) w := by
  rw [chainCells, List.mem_flatMap] at hx
  obtain ⟨p, -, hp⟩ := hx
  simp only [pairCells, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact ⟨p.1, tupOf V k e p.1 p.2, hp⟩

omit [L.Structure A] in
theorem tag_of_mem_oneCells {x : (haltTuringInterp V cF cP).Map A}
    (hx : x ∈ oneCells V cF cP k e) : ∃ w, x = hPt (Sum.inr .cOne) w := by
  rw [oneCells, List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact ⟨_, rfl⟩

section BlockIdxValues

theorem blockIdx_cEndL : blockIdx V cF cP (Sum.inr .cEndL) = 0 := rfl

theorem blockIdx_cBit (i : Fin V.numSyms) :
    blockIdx V cF cP (Sum.inr (.cBit i)) = 1 + (V.numSyms - 1 - i) := rfl

theorem blockIdx_cFold (i : Fin V.numSyms) :
    blockIdx V cF cP (Sum.inr (.cFold i)) = 1 + (V.numSyms - 1 - i) := rfl

theorem blockIdx_cProc : blockIdx V cF cP (Sum.inr .cProc) = V.numSyms + 1 := rfl

theorem blockIdx_cMid : blockIdx V cF cP (Sum.inr .cMid) = V.numSyms + 2 := rfl

theorem blockIdx_cGap : blockIdx V cF cP (Sum.inr .cGap) = V.numSyms + 3 := rfl

theorem blockIdx_cComL : blockIdx V cF cP (Sum.inr .cComL) = V.numSyms + 4 := rfl

theorem blockIdx_cOne : blockIdx V cF cP (Sum.inr .cOne) = V.numSyms + 5 := rfl

theorem blockIdx_cComR : blockIdx V cF cP (Sum.inr .cComR) = V.numSyms + 6 := rfl

theorem blockIdx_cEndR : blockIdx V cF cP (Sum.inr .cEndR) = V.numSyms + 7 := rfl

end BlockIdxValues

/-- **The cells are strictly ordered as listed.** -/
theorem pairwise_psH : (psH V cF cP k e).Pairwise (SLt V cF cP) := by
  have htail : ∀ y ∈ hPt (Sum.inr (CellTag.cProc (V := V))) (botTup V A) ::
      hPt (Sum.inr .cMid) (botTup V A) :: hPt (Sum.inr .cGap) (botTup V A) ::
      hPt (Sum.inr .cComL) (botTup V A) ::
      (oneCells V cF cP k e ++
        [hPt (Sum.inr .cComR) (botTup V A), hPt (Sum.inr .cEndR) (botTup V A)]),
      ∃ (c : CellTag V) (w : Fin (dimOf V) → A),
        y = hPt (Sum.inr c) w ∧ V.numSyms + 1 ≤ blockIdx V cF cP (Sum.inr c) := by
    intro y hy
    simp only [List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | rfl | rfl | rfl | hy | rfl | hy
    · exact ⟨.cProc, _, rfl, by rw [blockIdx_cProc]⟩
    · exact ⟨.cMid, _, rfl, by rw [blockIdx_cMid]; omega⟩
    · exact ⟨.cGap, _, rfl, by rw [blockIdx_cGap]; omega⟩
    · exact ⟨.cComL, _, rfl, by rw [blockIdx_cComL]; omega⟩
    · obtain ⟨w, rfl⟩ := tag_of_mem_oneCells V cF cP k e hy
      exact ⟨.cOne, _, rfl, by rw [blockIdx_cOne]; omega⟩
    · exact ⟨.cComR, _, rfl, by rw [blockIdx_cComR]; omega⟩
    · obtain rfl : y = hPt (Sum.inr .cEndR) (botTup V A) := by simpa using hy
      exact ⟨.cEndR, _, rfl, by rw [blockIdx_cEndR]; omega⟩
  have hone : ∀ y ∈ oneCells V cF cP k e ++
      [hPt (Sum.inr (CellTag.cComR (V := V))) (botTup V A),
       hPt (Sum.inr .cEndR) (botTup V A)],
      ∃ (c : CellTag V) (w : Fin (dimOf V) → A),
        y = hPt (Sum.inr c) w ∧ V.numSyms + 5 ≤ blockIdx V cF cP (Sum.inr c) := by
    intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · obtain ⟨w, rfl⟩ := tag_of_mem_oneCells V cF cP k e hy
      exact ⟨.cOne, _, rfl, by rw [blockIdx_cOne]⟩
    · exact ⟨.cComR, _, rfl, by rw [blockIdx_cComR]; omega⟩
    · obtain rfl : y = hPt (Sum.inr .cEndR) (botTup V A) := by simpa using hy
      exact ⟨.cEndR, _, rfl, by rw [blockIdx_cEndR]; omega⟩
  rw [psH]
  refine List.Pairwise.cons ?_ ?_
  · intro y hy
    simp only [List.mem_append, List.mem_cons] at hy
    have hy' : y ∈ chainCells V cF cP k e ∨ ∃ (c : CellTag V) (w : Fin (dimOf V) → A),
        y = hPt (Sum.inr c) w ∧ V.numSyms + 1 ≤ blockIdx V cF cP (Sum.inr c) := by
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (htail y (by simpa using hy))
    rcases hy' with hy | ⟨c, w, rfl, hc⟩
    · obtain ⟨i, w, hxx⟩ := tag_of_mem_chainCells V cF cP k e hy
      rcases hxx with rfl | rfl
      · exact sLt_of_blockLt V cF cP
          (by rw [blockIdx_cEndL, blockIdx_cBit]; omega) _ _
      · exact sLt_of_blockLt V cF cP
          (by rw [blockIdx_cEndL, blockIdx_cFold]; omega) _ _
    · exact sLt_of_blockLt V cF cP (by rw [blockIdx_cEndL]; omega) _ _
  · rw [List.pairwise_append]
    refine ⟨pairwise_chainCells V cF cP k e, ?_, ?_⟩
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
        (List.Pairwise.cons ?_ ?_)))
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | rfl | hy
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cProc, blockIdx_cMid]; omega) _ _
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cProc, blockIdx_cGap]; omega) _ _
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cProc, blockIdx_cComL]; omega) _ _
        · obtain ⟨c, w, rfl, hc⟩ := hone y hy
          exact sLt_of_blockLt V cF cP (by rw [blockIdx_cProc]; omega) _ _
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | hy
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cMid, blockIdx_cGap]; omega) _ _
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cMid, blockIdx_cComL]; omega) _ _
        · obtain ⟨c, w, rfl, hc⟩ := hone y hy
          exact sLt_of_blockLt V cF cP (by rw [blockIdx_cMid]; omega) _ _
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cGap, blockIdx_cComL]; omega) _ _
        · obtain ⟨c, w, rfl, hc⟩ := hone y hy
          exact sLt_of_blockLt V cF cP (by rw [blockIdx_cGap]; omega) _ _
      · intro y hy
        obtain ⟨c, w, rfl, hc⟩ := hone y hy
        exact sLt_of_blockLt V cF cP (by rw [blockIdx_cComL]; omega) _ _
      · rw [List.pairwise_append]
        refine ⟨pairwise_oneCells V cF cP k e, ?_, ?_⟩
        · refine List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)
          obtain rfl : y = hPt (Sum.inr .cEndR) (botTup V A) := by simpa using hy
          exact sLt_of_blockLt V cF cP
            (by rw [blockIdx_cComR, blockIdx_cEndR]; omega) _ _
        · intro x hx y hy
          obtain ⟨w, rfl⟩ := tag_of_mem_oneCells V cF cP k e hx
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact sLt_of_blockLt V cF cP
              (by rw [blockIdx_cOne, blockIdx_cComR]; omega) _ _
          · obtain rfl : y = hPt (Sum.inr .cEndR) (botTup V A) := by simpa using hy
            exact sLt_of_blockLt V cF cP
              (by rw [blockIdx_cOne, blockIdx_cEndR]; omega) _ _
    · intro x hx y hy
      obtain ⟨i, w, hxx⟩ := tag_of_mem_chainCells V cF cP k e hx
      obtain ⟨c, w', rfl, hc⟩ := htail y hy
      rcases hxx with rfl | rfl
      · exact sLt_of_blockLt V cF cP (by rw [blockIdx_cBit]; omega) _ _
      · exact sLt_of_blockLt V cF cP (by rw [blockIdx_cFold]; omega) _ _

end Enumeration

/-! ### The enumeration and the initial tape -/

section Tape

open HaltPcp

variable (V cF cP)
variable [L.IsRelational]
variable [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)]
variable (k : ℕ) (e : Fin (k + 1) ≃o A)

omit [L.IsRelational]
  [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)] in
/-- **The listed cells enumerate the positions in the machine's order.** -/
theorem isPosEnum_psH :
    IsPosEnum (tmData ((haltTuringInterp V cF cP).Map A)) (psH V cF cP k e) := by
  refine ⟨(pairwise_psH V cF cP k e).imp fun h => h, fun p => ?_⟩
  exact ⟨fun hp => posn_of_mem_psH V cF cP k e hp, fun hp => mem_psH_of_posn V cF cP k e hp⟩

omit [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)] in
theorem forall₂_flatMap {α β γ : Type} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    ∀ {l : List α}, (∀ a ∈ l, List.Forall₂ R (f a) (g a)) →
      List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a (by simp))
      (forall₂_flatMap fun b hb => h b (by simp [hb]))

omit [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)] in
theorem forall₂_map_replicate {α β γ : Type} {R : β → γ → Prop} {F : α → β} {c : γ} :
    ∀ {l : List α}, (∀ a ∈ l, R (F a) c) →
      List.Forall₂ R (l.map F) (List.replicate l.length c)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp))
      (forall₂_map_replicate fun b hb => h b (by simp [hb]))

omit [L.IsRelational] in
/-- **The listed letters are the initial tape of the listed cells.** -/
theorem forall₂_initTape :
    List.Forall₂ (tmData ((haltTuringInterp V cF cP).Map A)).InitTape
      (psH V cF cP k e) (inpH V cF cP k e) := by
  have hcell : ∀ (c : CellTag V) (w : Fin (dimOf V) → A) (u : SimU (allCode cF cP)),
      Canon (CellTag.used V c) w → InpOn V cF cP c u w →
      (tmData ((haltTuringInterp V cF cP).Map A)).InitTape (hPt (Sum.inr c) w) (mEl u) :=
    fun c w u hcan hio =>
      Or.inl ((relMap_inp _ _ _ _).mpr ⟨c, u, rfl, rfl, hcan, canon_botTup 0, hio⟩)
  rw [psH, inpH]
  refine List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) ?_
  refine List.rel_append ?_ ?_
  · rw [chainCells]
    refine forall₂_flatMap fun p hp => ?_
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · refine hcell _ _ _ (canon_tupOf V k e p.1 p.2) ?_
      rcases hb : bitAt V k e p.1 p.2 with - | -
      · refine Or.inr ⟨rfl, fun hcon => ?_⟩
        rw [← bitAt_iff_bitOf V k e p.1 p.2, hb] at hcon
        exact Bool.noConfusion hcon
      · exact Or.inl ⟨rfl, (bitAt_iff_bitOf V k e p.1 p.2).mp hb⟩
    · exact hcell _ _ _ (canon_tupOf V k e p.1 p.2) rfl
  refine List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) ?_
  refine List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) ?_
  refine List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) ?_
  refine List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) ?_
  refine List.rel_append ?_ ?_
  · rw [oneCells]
    have hlen : ((List.finRange (k + 1)).reverse).length = k + 1 := by simp
    have hrep : List.replicate (k + 1)
        (mEl (V := V) (cF := cF) (cP := cP) (A := A) (sts SimSym.one)) =
        List.replicate ((List.finRange (k + 1)).reverse).length (mEl (sts SimSym.one)) := by
      rw [hlen]
    rw [hrep]
    refine forall₂_map_replicate fun a _ => ?_
    exact hcell _ _ _ (canon_pad isBot_botA _ _) rfl
  · exact List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl)
      (List.Forall₂.cons (hcell _ _ _ (canon_botTup _) rfl) List.Forall₂.nil)

omit [Finite A] [Nonempty A]
  [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)] in
theorem reverse_flatMap {α β : Type} (f : α → List β) :
    ∀ l : List α, (l.flatMap f).reverse = l.reverse.flatMap fun a => (f a).reverse
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.reverse_append, reverse_flatMap f l, List.reverse_cons,
      List.flatMap_append]
    simp

omit [Finite A] [Nonempty A] in
/-- The reversed flattened table is the drawn bit sequence. -/
theorem table_flatten_reverse_eq :
    (FinStruct.ofEquiv V k e.toEquiv).table.flatten.reverse =
      (bitIdx V k).map fun p => bitAt V k e p.1 p.2 := by
  have htab : (FinStruct.ofEquiv V k e.toEquiv).table =
      List.ofFn fun i : Fin V.numSyms =>
        (List.range ((k + 1) ^ V.arity i)).map fun t => bitAt V k e i t := by
    change (FinStruct.ofTable V k _).table = _
    rw [FinStruct.ofTable]
    refine congrArg List.ofFn (funext fun i => ?_)
    refine List.map_congr_left fun t _ => ?_
    rw [bitAt]
    rfl
  rw [htab, List.ofFn_eq_map, ← List.flatMap_def, reverse_flatMap, bitIdx]
  rw [List.map_flatMap]
  refine congrArg (fun f => List.flatMap f (List.finRange V.numSyms).reverse)
    (funext fun i => ?_)
  rw [← List.map_reverse, List.map_map]
  rfl

omit [Finite A] [Nonempty A] in
theorem replicate_rotate {α : Type} (a : α) (n : ℕ) (l : List α) :
    List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, ih]
    rfl

omit [L.IsRelational] in
/-- **The listed letters are the image of the spelled initial word.** -/
theorem inpH_eq :
    inpH V cF cP k e =
      ((SimSym.endL :: ((((bitIdx V k).map fun p => bitAt V k e p.1 p.2).flatMap
            (fun b => [SimSym.hComp (posBit cF cP b), SimSym.hComp (posFold cF cP)]) ++
          [SimSym.hComp (posProc cF cP)]) ++
        SimSym.mid :: valR [0, k + 1] 0 0)).map sts).map
        (mEl (V := V) (cF := cF) (cP := cP) (A := A)) := by
  simp only [inpH, valR, encVal, encNum, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_append, List.map_flatMap, List.flatMap_map, List.map_replicate,
    List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc, List.map_nil,
    List.replicate_succ, List.replicate_zero, replicate_rotate]

include k e in
omit [∀ (n : ℕ) (R : L.Relations n) (x : Fin n → A), Decidable (RelMap R x)] in
/-- **Correctness of the drawing**: the drawn instance is a yes-instance of
the halting problem exactly when the source structure is one. -/
theorem holds_haltMap_iff {P : DecisionProblem L}
    (hF : ∀ v : List.Vector ℕ 3, cF.eval v.1 = pure <$> foldSpec v)
    (hP : ∀ N n : ℕ, (cP.eval [N, n]).Dom ↔ P.toPred V (structOfBits V (n - 1) N)) :
    HALT ((haltTuringInterp V cF cP).Map A) ↔ P A := by
  classical
  haveI : Finite ((haltTuringInterp V cF cP).Map A) :=
    FOInterpretation.map_finite _ _
  rw [halt_holds_iff]
  rw [and_iff_right wellFormed_halt]
  rw [acceptsU_iff_derives wellFormed_halt (isPosEnum_psH V cF cP k e)
    (forall₂_initTape V cF cP k e)]
  rw [inpH_eq V cF cP k e]
  rw [TMEmbed.derives_iff_evalDom tmEmbed_halt
    (frameSeg_inputChain cF cP ((bitIdx V k).map fun p => bitAt V k e p.1 p.2))
    [0, k + 1] 0 0]
  rw [← table_flatten_reverse_eq V k e]
  rw [inputChain_dom_iff (P := P) hF hP ((FinStruct.ofEquiv V k e.toEquiv).table.flatten)
    (k + 1)]
  rw [show k + 1 - 1 = k from rfl]
  rw [structOfBits_ofEquiv V k e.toEquiv]
  exact toPred_ofEquiv P V k e.toEquiv

end Tape

end HaltHard

end DescriptiveComplexity
