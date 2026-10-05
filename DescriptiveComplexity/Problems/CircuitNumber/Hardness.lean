/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CircuitNumber.Draw
import DescriptiveComplexity.Counting.DigitDefinable

/-!
# Every digit-definable function reduces to the number written by a circuit

`DescriptiveComplexity.DigitLFPDef.orderedParsimonious`: a function whose binary
digits are relations of a least fixed point
(`DescriptiveComplexity.DigitDefinable`) reduces to
`DescriptiveComplexity.CircuitNumber` by an ordered parsimonious reduction, the
circuit being the one drawn from the rules
(`DescriptiveComplexity.CircNum.drawInterp`).

* **The circuit evaluates the fixed point**
  (`DescriptiveComplexity.CircNum.gateVal_atom_iff`): the gate of an atom
  derives `1` exactly when the rules derive the atom. One direction rebuilds a
  derivation of the rules as a derivation of the gates, link by link along a
  conjunction chain (`DescriptiveComplexity.CircNum.gateVal_of_derives`); the
  other inverts a derivation of the gates, every rule that can fire at a gate
  of the drawn circuit firing for the intended reason
  (`DescriptiveComplexity.CircNum.val_of_gateVal`).
* **The outputs are the digits**: the output gates are the canonically padded
  atoms of the relations holding the digits, and padding preserves the
  lexicographic order (`DescriptiveComplexity.CircNum.tupLeLex_pad`), so the
  rank of an output among the outputs is the rank of its position
  (`DescriptiveComplexity.CircNum.outRank_bitPt`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace CircNum

/-! ### Padding and the lexicographic order -/

section Pad

variable {A : Type} {D m : ℕ}

theorem pad_of_lt (a₀ : A) (w : Fin m → A) {j : Fin D} (hj : (j : ℕ) < m) :
    pad a₀ w j = w ⟨j, hj⟩ := by
  rw [pad, dite_eq_left hj]

theorem pad_of_le (a₀ : A) (w : Fin m → A) {j : Fin D} (hj : m ≤ (j : ℕ)) :
    pad a₀ w j = a₀ := by
  rw [pad, dite_eq_right (not_lt.mpr hj)]

theorem pad_castLE (a₀ : A) (h : m ≤ D) (w : Fin m → A) (j : Fin m) :
    pad a₀ w (Fin.castLE h j) = w j :=
  congrFun (pref_pad a₀ h w) j

theorem pad_injective (a₀ : A) (h : m ≤ D) :
    Function.Injective (pad (D := D) a₀ : (Fin m → A) → Fin D → A) := fun x y hxy => by
  rw [← pref_pad a₀ h x, ← pref_pad a₀ h y, hxy]

/-- **Padding preserves the lexicographic order.** -/
theorem tupLeLex_pad [LinearOrder A] (a₀ : A) (h : m ≤ D) (y x : Fin m → A) :
    tupLeLex (pad (D := D) a₀ y) (pad a₀ x) ↔ tupLeLex y x := by
  constructor
  · rintro (he | ⟨j, hj, hlt⟩)
    · exact Or.inl (pad_injective a₀ h he)
    · have hjm : (j : ℕ) < m := by
        by_contra hjm
        rw [pad_of_le a₀ y (not_lt.mp hjm), pad_of_le a₀ x (not_lt.mp hjm)] at hlt
        exact lt_irrefl _ hlt
      refine Or.inr ⟨⟨j, hjm⟩, fun i hi => ?_, ?_⟩
      · have := hj (Fin.castLE h i) hi
        rwa [pad_castLE, pad_castLE] at this
      · rwa [pad_of_lt a₀ y hjm, pad_of_lt a₀ x hjm] at hlt
  · rintro (rfl | ⟨j, hj, hlt⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨Fin.castLE h j, fun i hi => ?_, ?_⟩
      · have him : (i : ℕ) < m := lt_trans hi j.isLt
        rw [pad_of_lt a₀ y him, pad_of_lt a₀ x him]
        exact hj ⟨i, him⟩ hi
      · rwa [pad_castLE, pad_castLE]

end Pad

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}
variable {A : Type} [L.Structure A] [LinearOrder A]
variable {prog : HornProgram (L.sum Language.order) B k} {c : ℕ} {bit : Fin c → B.ι}

/-! ### What the gates derive -/

/-- What a gate deriving `1` means: an atom is canonically padded and derived
by the rules; a link of a conjunction chain has every body atom from its
position on derived. -/
def Val (p : (drawInterp prog bit).Map A) : Prop :=
  match p.1 with
  | Sum.inl i => Canon (B.arity i) p.2 ∧
      Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) p.2⟩
  | Sum.inr ⟨c, j⟩ => ∀ (n : ℕ) (a : SOAtom B k), (j : ℕ) ≤ n →
      (clauseAt prog c).body[n]? = some a →
        Derives prog ⟨a.idx, fun q => p.2 (atomIdx a q)⟩

/-- An atom read through a canonically padded occurrence. -/
theorem pref_eq_of_padTup {a : SOAtom B k} {u w : Fin (clauseDim B k) → A}
    (h : PadTup (atomIdx a) u w) :
    pref (arity_le_clauseDim (k := k) a.idx) w = fun q => u (atomIdx a q) :=
  funext fun q => h.2 (Fin.castLE (arity_le_clauseDim a.idx) q) q.isLt

/-- **Nothing else evaluates to `1`.** By induction on the derivation of the
gates: every rule that can fire at a gate of the drawn circuit fires for the
intended reason. The false rail carries no information and is not tracked. -/
theorem val_of_gateVal :
    ∀ {b : Bool} {p : (drawInterp prog bit).Map A}, GateVal b p → b = true → Val p := by
  intro b p h
  induction h with
  | @constTrue g hg =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_isTrue_atom i w hg).elim
    · intro n a hn ha
      have hlen : (clauseAt prog c).body.length ≤ n := ((isTrue_step c j w).mp hg) ▸ hn
      rw [List.getElem?_eq_none hlen] at ha
      exact absurd ha (by simp)
  | @constFalse g hg => simp
  | @andTrue g l r hg hl hr _ _ ihl ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_isAnd_atom i w hg).elim
    · obtain ⟨tl, wl⟩ := l
      rcases tl with il | ⟨cl, jl⟩
      swap
      · exact (not_left_step_step c cl j jl w wl hl).elim
      obtain ⟨a, ha, rfl, hpad⟩ := (left_step_atom c j w _ wl).mp hl
      have hcur : Derives prog ⟨a.idx, fun q => w (atomIdx a q)⟩ := by
        have := (ihl rfl).2
        rwa [pref_eq_of_padTup hpad] at this
      obtain ⟨tr, wr⟩ := r
      rcases tr with ir | ⟨cr, jr⟩
      · exact (not_right_step_atom c j w ir wr hr).elim
      obtain ⟨⟨rfl, hj⟩, rfl⟩ := (right_step_step c cr j jr w wr).mp hr
      intro n a' hn ha'
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
        exact hcur
      · exact ihr rfl n a' (hj ▸ hlt) ha'
  | @andFalseLeft g l hg hl _ ihl => simp
  | @andFalseRight g r hg hr _ ihr => simp
  | @orTrueLeft g l hg hl _ ihl =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    swap
    · exact (not_isOr_step c j w hg).elim
    obtain ⟨tl, u⟩ := l
    rcases tl with il | ⟨c, j⟩
    · exact (not_left_atom_atom i il w u hl).elim
    obtain ⟨hj, hguard, a, ha, rfl, hpad⟩ := (left_atom_step _ w c j u).mp hl
    refine ⟨hpad.1, ?_⟩
    have hbody : ∀ b ∈ (clauseAt prog c).body,
        Derives prog ⟨b.idx, fun q => pref (le_clauseDim (B := B)) u (b.args q)⟩ := by
      intro b hb
      obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hb
      exact ihl rfl n b (hj ▸ Nat.zero_le n) hn
    rw [pref_eq_of_padTup hpad]
    exact Derives.rule (List.getElem_mem c.isLt) (Option.mem_def.mp ha) hguard hbody
  | @orTrueRight g r hg hr _ ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_right_atom i w r hr).elim
    · exact (not_isOr_step c j w hg).elim
  | @orFalse g l r hg hl hr _ _ ihl ihr => simp
  | @notTrue g i hg hi _ ihi => exact fun _ => (not_isNot g hg).elim
  | @notFalse g i hg hi _ ihi => simp

/-- **Every atom the rules derive has its gate deriving `1`**: a derivation of
the rules is rebuilt as a derivation of the gates, the conjunction chain of
each rule instance being climbed from its end. -/
theorem gateVal_of_derives {a₀ : A} (h₀ : IsBot a₀) :
    ∀ q : Σ i : B.ι, Fin (B.arity i) → A, Derives prog q →
      GateVal (A := (drawInterp prog bit).Map A) true (atomTag q.1, pad a₀ q.2) := by
  intro q h
  induction h with
  | @rule c hc a ha v hg _ ih =>
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
    let ci : Fin prog.length := ⟨n, hn⟩
    let u : Fin (clauseDim B k) → A := pad a₀ v
    have hu : ∀ b : SOAtom B k, (fun q => u (atomIdx b q)) = fun q => v (b.args q) :=
      fun b => funext fun q => pad_castLE a₀ le_clauseDim v (b.args q)
    -- the conjunction chain of this rule instance, climbed from its end
    have chain : ∀ (d n' : ℕ) (hn' : n' ≤ (clauseAt prog ci).body.length),
        (clauseAt prog ci).body.length - n' = d →
          GateVal (A := (drawInterp prog bit).Map A) true
            (stepTag ci ⟨n', Nat.lt_succ_of_le hn'⟩, u) := by
      intro d
      induction d with
      | zero =>
        intro n' hn' hd
        exact .constTrue ((isTrue_step ci _ u).mpr (by simp only; omega))
      | succ d ihd =>
        intro n' hn' hd
        have hlt : n' < (clauseAt prog ci).body.length := by omega
        let b : SOAtom B k := (clauseAt prog ci).body[n']
        have hb : (clauseAt prog ci).body[n']? = some b := List.getElem?_eq_getElem hlt
        refine .andTrue (l := (atomTag b.idx, pad a₀ fun q => v (b.args q)))
          (r := (stepTag ci ⟨n' + 1, Nat.succ_lt_succ hlt⟩, u))
          ((isAnd_step ci _ u).mpr hlt) ?_ ?_ (ih b (List.getElem_mem hlt))
          (ihd (n' + 1) hlt (by omega))
        · refine (left_step_atom ci _ u b.idx _).mpr ⟨b, hb, rfl, ?_⟩
          rw [← hu b]
          exact padTup_pad h₀ (atomIdx b) u
        · exact (right_step_step ci ci _ _ u u).mpr ⟨⟨rfl, rfl⟩, rfl⟩
    refine .orTrueLeft (l := (stepTag ci ⟨0, Nat.succ_pos _⟩, u)) (isOr_atom _ _) ?_
      (chain _ 0 (Nat.zero_le _) rfl)
    refine (left_atom_step a.idx _ ci _ u).mpr ⟨rfl, ?_, a, Option.mem_def.mpr ha, rfl, ?_⟩
    · rwa [pref_pad]
    · rw [← hu a]
      exact padTup_pad h₀ (atomIdx a) u

/-- **The circuit evaluates the fixed point**: the gate of an atom derives `1`
exactly when it is canonically padded and the rules derive the atom. -/
theorem gateVal_atom_iff {a₀ : A} (h₀ : IsBot a₀) (i : B.ι) (w : Fin (clauseDim B k) → A) :
    GateVal (A := (drawInterp prog bit).Map A) true (atomTag i, w) ↔
      Canon (B.arity i) w ∧ Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) w⟩ := by
  refine ⟨fun h => val_of_gateVal h rfl, fun h => ?_⟩
  have := gateVal_of_derives (bit := bit) h₀ _ h.2
  rwa [pad_pref_of_canon h₀ (arity_le_clauseDim i) h.1] at this

/-! ### The outputs are the digits -/

section Count

variable {a₀ : A} {ℓ : ℕ}

omit [L.Structure A] in
/-- The lexicographic order does not depend on how the coordinates are
numbered. -/
theorem tupLeLex_cast {m : ℕ} (h : m = ℓ) (y x : Fin ℓ → A) :
    tupLeLex (fun k : Fin m => y (Fin.cast h k)) (fun k => x (Fin.cast h k)) ↔ tupLeLex y x := by
  subst h
  exact Iff.rfl

omit [L.Structure A] in
theorem tupLeLex_iff_le {m : ℕ} (y x : Fin m → A) : tupLeLex y x ↔ toLex y ≤ toLex x := by
  rw [le_iff_lt_or_eq, or_comm]
  exact or_congr ⟨fun h => congrArg toLex h, fun h => h⟩ Iff.rfl

variable (prog bit) in
/-- The output gate of a position: the atom of its tuple in the relation
variable of its group, canonically padded. -/
noncomputable def bitPt (hℓ : ∀ τ, B.arity (bit τ) = ℓ) (a₀ : A)
    (q : Fin c ×ₗ Lex (Fin ℓ → A)) : (drawInterp prog bit).Map A :=
  (atomTag (bit (ofLex q).1), pad a₀ fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k))

variable (hinj : Function.Injective bit) (hℓ : ∀ τ, B.arity (bit τ) = ℓ)

omit [L.Structure A] [LinearOrder A] in
include hinj in
theorem bitPt_injective (a₀ : A) : Function.Injective (bitPt prog bit hℓ a₀) := by
  rintro ⟨τ, y⟩ ⟨τ', y'⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain rfl : τ = τ' := hinj (Sum.inl.inj h1)
  have h3 := pad_injective a₀ (arity_le_clauseDim (bit τ)) h2
  have : y = y' := funext fun k => congrFun h3 (Fin.cast (hℓ τ).symm k)
  rw [this]

/-- The output gates are the gates of the positions. -/
theorem out_iff_bitPt (h₀ : IsBot a₀) (p : (drawInterp prog bit).Map A) :
    RelMap (M := (drawInterp prog bit).Map A) ncOut ![p] ↔ ∃ q, p = bitPt prog bit hℓ a₀ q := by
  obtain ⟨t, w⟩ := p
  rcases t with i | ⟨c', j⟩
  · rw [out_atom]
    constructor
    · rintro ⟨⟨τ, rfl⟩, hc⟩
      exact ⟨toLex (τ, toLex fun n =>
          pref (arity_le_clauseDim (k := k) (bit τ)) w (Fin.cast (hℓ τ).symm n)),
        congrArg (Prod.mk _) (pad_pref_of_canon h₀ (arity_le_clauseDim (bit τ)) hc).symm⟩
    · rintro ⟨q, hq⟩
      obtain ⟨hi, hw⟩ := Prod.mk.inj hq
      obtain rfl := Sum.inl.inj hi
      exact ⟨⟨_, rfl⟩, hw ▸ canon_pad h₀ _ _⟩
  · refine iff_of_false (not_out_step c' j w) ?_
    rintro ⟨q, hq⟩
    exact absurd (Prod.mk.inj hq).1 (by simp)

/-- **An output gate holds the digit of its position.** -/
theorem outBit_bitPt (h₀ : IsBot a₀) (q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    OutBit (bitPt prog bit hℓ a₀ q) ↔
      lfpAssign prog (bit (ofLex q).1)
        fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k) := by
  constructor
  · rintro ⟨-, hv⟩
    have := ((gateVal_atom_iff h₀ (bit (ofLex q).1) _).mp hv).2
    rwa [pref_pad] at this
  · intro h
    exact ⟨(out_atom _ _).mpr ⟨⟨_, rfl⟩, canon_pad h₀ _ _⟩, gateVal_of_derives h₀ ⟨_, _⟩ h⟩

include hinj in
/-- The outputs strictly below the gate of a position are the gates of the
positions strictly below it. -/
theorem lowerOut_bitPt (h₀ : IsBot a₀) (q : Fin c ×ₗ Lex (Fin ℓ → A))
    (p : (drawInterp prog bit).Map A) :
    LowerOut (bitPt prog bit hℓ a₀ q) p ↔ ∃ q', p = bitPt prog bit hℓ a₀ q' ∧ q' < q := by
  have hbelow : ∀ q' : Fin c ×ₗ Lex (Fin ℓ → A),
      RelMap (M := (drawInterp prog bit).Map A) ncBelow
          ![bitPt prog bit hℓ a₀ q', bitPt prog bit hℓ a₀ q] ↔ q' ≤ q := by
    rintro ⟨τ', y'⟩
    obtain ⟨τ, y⟩ := q
    refine (below_bit_bit hinj τ' τ _ _).trans (Iff.trans ?_ prodLex_le_iff.symm)
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, (tupLeLex_iff_le _ _).mp ((tupLeLex_cast (hℓ τ') _ _).mp
        ((tupLeLex_pad a₀ (arity_le_clauseDim (bit τ')) _ _).mp h))⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, (tupLeLex_pad a₀ (arity_le_clauseDim (bit τ')) _ _).mpr
        ((tupLeLex_cast (hℓ τ') _ _).mpr ((tupLeLex_iff_le _ _).mpr h))⟩
  constructor
  · rintro ⟨ho, hne, hb⟩
    obtain ⟨q', rfl⟩ := (out_iff_bitPt hℓ h₀ p).mp ho
    exact ⟨q', rfl, lt_of_le_of_ne ((hbelow q').mp hb) fun h => hne (congrArg _ h)⟩
  · rintro ⟨q', rfl, hlt⟩
    exact ⟨(out_iff_bitPt hℓ h₀ _).mpr ⟨q', rfl⟩,
      fun h => ne_of_lt hlt (bitPt_injective hinj hℓ a₀ h), (hbelow q').mpr hlt.le⟩

include hinj in
/-- **The rank of an output among the outputs is the rank of its position.** -/
theorem outRank_bitPt (h₀ : IsBot a₀) (q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    outRank (bitPt prog bit hℓ a₀ q) = orank q := by
  rw [outRank, orank, ← Nat.card_coe_set_eq]
  symm
  refine Nat.card_eq_of_bijective
    (fun q' => ⟨bitPt prog bit hℓ a₀ q'.1,
      (lowerOut_bitPt hinj hℓ h₀ q _).mpr ⟨q'.1, rfl, q'.2⟩⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (bitPt_injective hinj hℓ a₀ (congrArg Subtype.val h))
  · rintro ⟨p, hp⟩
    obtain ⟨q', rfl, hq'⟩ := (lowerOut_bitPt hinj hℓ h₀ q p).mp hp
    exact ⟨⟨q', hq'⟩, rfl⟩

include hinj in
open Classical in
/-- **The drawn circuit writes the number whose digits are the relations
`bit τ` of the least fixed point.** -/
theorem circuitNumber_drawInterp (h₀ : IsBot a₀) :
    circuitNumber ((drawInterp prog bit).Map A) =
      ∑ᶠ q : Fin c ×ₗ Lex (Fin ℓ → A),
        if lfpAssign prog (bit (ofLex q).1)
            (fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k)) then 2 ^ orank q
        else 0 := by
  have hsupp : ∀ g ∈ Function.support
      (fun g : (drawInterp prog bit).Map A => if OutBit g then 2 ^ outRank g else 0),
      g ∈ Set.univ ↔ g ∈ Set.range (bitPt prog bit hℓ a₀) := by
    intro g hg
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    have hbit : OutBit g := by
      by_contra h
      exact hg (ite_eq_right h)
    obtain ⟨q, hq⟩ := (out_iff_bitPt hℓ h₀ g).mp hbit.1
    exact ⟨q, hq.symm⟩
  rw [circuitNumber, ← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ hsupp,
    finsum_mem_range (bitPt_injective hinj hℓ a₀)]
  refine finsum_congr fun q => ?_
  rw [outRank_bitPt hinj hℓ h₀ q, if_congr (outBit_bitPt hℓ h₀ q) rfl rfl]

end Count

end CircNum

/-! ### The reduction -/

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L}

/-- **A function whose binary digits are relations of a least fixed point
reduces to the number written by a circuit**, by drawing the circuit of the
rules inside the instance. -/
noncomputable def DigitLFPDef.orderedParsimonious (d : DigitLFPDef L)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = d.value A) : C ≤ᵖ[≤] CircuitNumber where
  Tag := CircNum.DrawTag d.rules
  tagNonempty := ⟨Sum.inl (d.bit ⟨0, d.c_pos⟩)⟩
  dim := clauseDim d.B d.k
  toInterpretation := CircNum.drawInterp d.rules d.bit
  correct := fun A _ _ _ _ => by
    obtain ⟨a₀, h₀⟩ := Finite.exists_min (id : A → A)
    exact (h A).trans
      (CircNum.circuitNumber_drawInterp (a₀ := a₀) d.bit_injective d.arity_bit h₀).symm

/-- **Every digit-definable problem parsimoniously reduces to the number
written by a circuit.** -/
theorem DigitDefinable.nonempty_orderedParsimonious (h : DigitDefinable C) :
    Nonempty (C ≤ᵖ[≤] CircuitNumber) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d.orderedParsimonious hd⟩

end Reduction

end DescriptiveComplexity
