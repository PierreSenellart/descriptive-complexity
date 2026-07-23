/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.OneInSat.Slots
import DescriptiveComplexity.Problems.ThreeSat.Defs

/-!
# 3SAT ordered-FO-reduces to 1-in-SAT

The classical gadget, with the width case analysis removed by the three slots
of `DescriptiveComplexity.Problems.OneInSat.Slots`. Every clause `c` of the input gets

* three *slot* variables `slot i c`, tied to its occurrences by the *link*
  clauses `link i c = {¬ slot i c} ∪ {the i-th literal of c, if there is one}`
  – read as exactly-one clauses these say `slot i c ↔ (i-th literal)` when the
  occurrence exists and `slot i c = false` when it does not, *the same clause
  description in both cases*, one literal shorter;
* four fresh variables `fresh j c` and the three gadget clauses
  `piece one c = {¬ slot one c, d, e}`, `piece two c = {slot two c, e, f}`,
  `piece three c = {¬ slot three c, f, g}`, which are exactly-one satisfiable
  iff some slot of `c` is true.

Since a slot is true exactly when the corresponding literal is
(`DescriptiveComplexity.OneInRed.exists_litTrue_iff_slot`), the output is exactly-one
satisfiable iff the input is satisfiable. Clauses of width 0, 1 and 2 need no
special treatment: their missing slots are false, and an empty clause
correctly yields an unsatisfiable gadget.

The whole construction is gated on the width check `ThreeSatToSat.wideOrdF`,
as the reduction of 3SAT to SAT is: on a wide input every element becomes a
clause with no literal at all, and a clause with no literal has no true
literal, let alone exactly one. The order is used only to say *`i`-th
occurrence*, so this is an ordered reduction; the dimension is 1, all the
fresh variables being carried by tags.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace OneInRed

open Language Structure SatOcc

/-- Tags of the gadget: the copy of a variable, the three slots and four fresh
variables of a clause, and its three link and three gadget clauses. -/
inductive OITag : Type
  /-- The copy of a propositional variable. -/
  | var
  /-- The `i`-th slot variable of a clause. -/
  | slot (i : Ix3)
  /-- The `j`-th fresh variable of a clause. -/
  | fresh (j : Ix4)
  /-- The `i`-th link clause of a clause. -/
  | link (i : Ix3)
  /-- The `i`-th gadget clause of a clause. -/
  | piece (i : Ix3)
  deriving DecidableEq

instance : Fintype OITag where
  elems :=
    {OITag.var, OITag.slot .one, OITag.slot .two, OITag.slot .three,
      OITag.fresh .d, OITag.fresh .e, OITag.fresh .f, OITag.fresh .g,
      OITag.link .one, OITag.link .two, OITag.link .three,
      OITag.piece .one, OITag.piece .two, OITag.piece .three}
  complete := by
    intro t
    cases t with
    | var => decide
    | slot i => cases i <;> decide
    | fresh j => cases j <;> decide
    | link i => cases i <;> decide
    | piece i => cases i <;> decide

instance : Nonempty OITag := ⟨OITag.var⟩

/-- The tags carrying a clause of the output. -/
def clauseTag : OITag → Bool
  | .link _ => true
  | .piece _ => true
  | _ => false

/-- The pairs of tags joined by a *positive* literal, on the same element: the
gadget clauses containing a fresh variable, and the second gadget clause
containing its slot. -/
def posPair : OITag → OITag → Bool
  | .piece .one, .fresh .d => true
  | .piece .one, .fresh .e => true
  | .piece .two, .slot .two => true
  | .piece .two, .fresh .e => true
  | .piece .two, .fresh .f => true
  | .piece .three, .fresh .f => true
  | .piece .three, .fresh .g => true
  | _, _ => false

/-- The pairs of tags joined by a *negative* literal, on the same element: the
first and third gadget clauses contain their slot negatively, and so does
every link clause. -/
def negPair : OITag → OITag → Bool
  | .piece .one, .slot .one => true
  | .piece .three, .slot .three => true
  | .link .one, .slot .one => true
  | .link .two, .slot .two => true
  | .link .three, .slot .three => true
  | _, _ => false

/-! ### The interpretation -/

section Builders

/-- The literal joining two tags on the same element, if there is one. -/
noncomputable def samePtF (b : Bool) : satOrd.Formula (Fin 2 × Fin 1) :=
  if b then eqF (0, 0) (1, 0) else ⊥

/-- The literal of a link clause coming from the `i`-th occurrence of its
clause, with sign `s`. -/
noncomputable def linkLitF (t₁ t₂ : OITag) (s : Bool) : satOrd.Formula (Fin 2 × Fin 1) :=
  Formula.iSup fun i : Ix3 =>
    if t₁ = .link i ∧ t₂ = .var then nthF i s (0, 0) (1, 0) else ⊥

/-- Defining formula for “is a clause”: link and gadget clauses sit on the
clauses of the input, and on a wide input everything is a clause. -/
noncomputable def isClauseF (t : OITag) : satOrd.Formula (Fin 1 × Fin 1) :=
  (if clauseTag t then clF (0, 0) else ⊥) ⊔ ThreeSatToSat.wideOrdF

/-- Defining formula for “occurs positively in”. -/
noncomputable def posInF (t₁ t₂ : OITag) : satOrd.Formula (Fin 2 × Fin 1) :=
  (samePtF (posPair t₁ t₂) ⊔ linkLitF t₁ t₂ true) ⊓ ∼ThreeSatToSat.wideOrdF

/-- Defining formula for “occurs negatively in”. -/
noncomputable def negInF (t₁ t₂ : OITag) : satOrd.Formula (Fin 2 × Fin 1) :=
  (samePtF (negPair t₁ t₂) ⊔ linkLitF t₁ t₂ false) ⊓ ∼ThreeSatToSat.wideOrdF

/-- The interpretation of 1-in-SAT instances in ordered CNF instances. -/
noncomputable def oiInterp : FOInterpretation satOrd Language.sat OITag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => isClauseF (t 0)
    | _, .posIn => fun t => posInF (t 0) (t 1)
    | _, .negIn => fun t => negInF (t 0) (t 1)

end Builders

/-! ### The vertices of the gadget -/

section Points

variable {A : Type}

/-- The point of tag `t` over the element `x`. -/
def pt (t : OITag) (x : A) : oiInterp.Map A := (t, fun _ => x)

theorem pt_eq_iff {t t' : OITag} {x x' : A} : pt t x = pt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [pt] using congrArg (fun p : oiInterp.Map A => p.1) h,
      by simpa [pt] using congrArg (fun p : oiInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pt_eta {t : OITag} {w : Fin 1 → A} : ((t, w) : oiInterp.Map A) = pt t (w 0) :=
  Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg w (Subsingleton.elim i 0)⟩

theorem pt_surj (q : oiInterp.Map A) : ∃ t x, q = pt t x :=
  ⟨q.1, q.2 0, pt_eta⟩

end Points

/-! ### Characterization of the three relations -/

section Characterizations

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

private theorem realize_samePtF {b : Bool} {v : Fin 2 × Fin 1 → A} :
    (samePtF b).Realize v ↔ b = true ∧ v (0, 0) = v (1, 0) := by
  cases b <;> simp [samePtF]

private theorem realize_linkLitF {t₁ t₂ : OITag} {s : Bool} {v : Fin 2 × Fin 1 → A} :
    (linkLitF t₁ t₂ s).Realize v ↔
      ∃ i, (t₁ = .link i ∧ t₂ = .var) ∧ NthOcc i (v (0, 0)) (v (1, 0)) s := by
  simp only [linkLitF, Formula.realize_iSup]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : t₁ = .link i ∧ t₂ = .var
    · rw [if_pos h] at hi
      exact ⟨i, h, realize_nthF.mp hi⟩
    · rw [if_neg h] at hi
      exact absurd hi (by simp)
  · rintro ⟨i, h, hn⟩
    exact ⟨i, by rw [if_pos h]; exact realize_nthF.mpr hn⟩

/-- The clauses of the gadget. -/
theorem isCl_pt (t : OITag) (x : A) :
    IsCl (pt t x) ↔ (clauseTag t = true ∧ IsCl x) ∨ ThreeSatToSat.Wide A := by
  rw [IsCl, pt, FOInterpretation.relMap_map]
  cases h : clauseTag t <;>
    simp [oiInterp, isClauseF, h, IsCl]

/-- The positive literals of the gadget. -/
theorem posIn_pt (t₁ t₂ : OITag) (x y : A) :
    PosIn (pt t₁ x) (pt t₂ y) ↔ ¬ThreeSatToSat.Wide A ∧
      ((posPair t₁ t₂ = true ∧ x = y) ∨
        ∃ i, (t₁ = .link i ∧ t₂ = .var) ∧ NthOcc i x y true) := by
  rw [PosIn, pt, pt, FOInterpretation.relMap_map]
  simp only [oiInterp, posInF, Formula.realize_inf, Formula.realize_not,
    Formula.realize_sup, realize_samePtF, realize_linkLitF,
    ThreeSatToSat.realize_wideOrdF]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The negative literals of the gadget. -/
theorem negIn_pt (t₁ t₂ : OITag) (x y : A) :
    NegIn (pt t₁ x) (pt t₂ y) ↔ ¬ThreeSatToSat.Wide A ∧
      ((negPair t₁ t₂ = true ∧ x = y) ∨
        ∃ i, (t₁ = .link i ∧ t₂ = .var) ∧ NthOcc i x y false) := by
  rw [NegIn, pt, pt, FOInterpretation.relMap_map]
  simp only [oiInterp, negInF, Formula.realize_inf, Formula.realize_not,
    Formula.realize_sup, realize_samePtF, realize_linkLitF,
    ThreeSatToSat.realize_wideOrdF]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end Characterizations

/-! ### The literals of a gadget clause -/

section Enumeration

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- Every literal of a gadget clause is either prescribed by the pair of tags,
on the same element, or is the copy of the `i`-th literal of the clause of a
link clause. -/
theorem occIn_pt_cases {tc : OITag} {c : A} {q : oiInterp.Map A} {u : Bool}
    (h : OccIn (pt tc c) q u) :
    (∃ t, (if u then posPair tc t else negPair tc t) = true ∧ q = pt t c) ∨
      ∃ i y, tc = .link i ∧ NthOcc i c y u ∧ q = pt .var y := by
  obtain ⟨t, y, rfl⟩ := pt_surj q
  cases u with
  | true =>
    obtain ⟨-, hcase⟩ := (posIn_pt _ _ _ _).mp h.2
    rcases hcase with ⟨hp, rfl⟩ | ⟨i, ⟨hi, rfl⟩, hn⟩
    · exact Or.inl ⟨t, by simpa using hp, rfl⟩
    · exact Or.inr ⟨i, y, hi, hn, rfl⟩
  | false =>
    obtain ⟨-, hcase⟩ := (negIn_pt _ _ _ _).mp h.2
    rcases hcase with ⟨hp, rfl⟩ | ⟨i, ⟨hi, rfl⟩, hn⟩
    · exact Or.inl ⟨t, by simpa using hp, rfl⟩
    · exact Or.inr ⟨i, y, hi, hn, rfl⟩

/-- The link and gadget clauses of a clause of the input are clauses. -/
theorem isCl_gadget {t : OITag} {c : A} (ht : clauseTag t = true)
    (hc : IsCl c) : IsCl (pt t c) :=
  (isCl_pt t c).mpr (Or.inl ⟨ht, hc⟩)

/-- A same-element positive literal of a gadget clause. -/
theorem occIn_same_pos {t₁ t₂ : OITag} {c : A} (hw : ¬ThreeSatToSat.Wide A)
    (ht : clauseTag t₁ = true) (hc : IsCl c) (hp : posPair t₁ t₂ = true) :
    OccIn (pt t₁ c) (pt t₂ c) true :=
  ⟨isCl_gadget ht hc, (posIn_pt _ _ _ _).mpr ⟨hw, Or.inl ⟨hp, rfl⟩⟩⟩

/-- A same-element negative literal of a gadget clause. -/
theorem occIn_same_neg {t₁ t₂ : OITag} {c : A} (hw : ¬ThreeSatToSat.Wide A)
    (ht : clauseTag t₁ = true) (hc : IsCl c) (hp : negPair t₁ t₂ = true) :
    OccIn (pt t₁ c) (pt t₂ c) false :=
  ⟨isCl_gadget ht hc, (negIn_pt _ _ _ _).mpr ⟨hw, Or.inl ⟨hp, rfl⟩⟩⟩

/-- The literal of a link clause coming from the occurrence it links. -/
theorem occIn_link_lit {i : Ix3} {c x : A} {s : Bool} (hw : ¬ThreeSatToSat.Wide A)
    (hc : IsCl c) (hn : NthOcc i c x s) : OccIn (pt (.link i) c) (pt .var x) s := by
  refine ⟨isCl_gadget rfl hc, ?_⟩
  cases s with
  | true => exact (posIn_pt _ _ _ _).mpr ⟨hw, Or.inr ⟨i, ⟨rfl, rfl⟩, hn⟩⟩
  | false => exact (negIn_pt _ _ _ _).mpr ⟨hw, Or.inr ⟨i, ⟨rfl, rfl⟩, hn⟩⟩

end Enumeration

/-! ### The assignment carried by the gadget -/

section Assignment

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- The assignment of the gadget induced by an assignment of the input: the
slots take the values of the literals they link, and the four fresh variables
of a clause are the explicit witnesses of the gadget. -/
def oiAssign (ν : A → Prop) (p : oiInterp.Map A) : Prop :=
  match p.1 with
  | .var => ν (p.2 0)
  | .slot i => SlotVal ν i (p.2 0)
  | .fresh .d => SlotVal ν .one (p.2 0) ∧ SlotVal ν .two (p.2 0)
  | .fresh .e => SlotVal ν .one (p.2 0) ∧ ¬SlotVal ν .two (p.2 0)
  | .fresh .f => ¬SlotVal ν .one (p.2 0) ∧ ¬SlotVal ν .two (p.2 0)
  | .fresh .g => (SlotVal ν .one (p.2 0) ∨ SlotVal ν .two (p.2 0)) ∧ SlotVal ν .three (p.2 0)
  | .link _ => False
  | .piece _ => False

@[simp] theorem oiAssign_var (ν : A → Prop) (x : A) :
    oiAssign ν (pt .var x) ↔ ν x := Iff.rfl

@[simp] theorem oiAssign_slot (ν : A → Prop) (i : Ix3) (c : A) :
    oiAssign ν (pt (.slot i) c) ↔ SlotVal ν i c := Iff.rfl

@[simp] theorem oiAssign_d (ν : A → Prop) (c : A) :
    oiAssign ν (pt (.fresh .d) c) ↔ SlotVal ν .one c ∧ SlotVal ν .two c := Iff.rfl

@[simp] theorem oiAssign_e (ν : A → Prop) (c : A) :
    oiAssign ν (pt (.fresh .e) c) ↔ SlotVal ν .one c ∧ ¬SlotVal ν .two c := Iff.rfl

@[simp] theorem oiAssign_f (ν : A → Prop) (c : A) :
    oiAssign ν (pt (.fresh .f) c) ↔ ¬SlotVal ν .one c ∧ ¬SlotVal ν .two c := Iff.rfl

@[simp] theorem oiAssign_g (ν : A → Prop) (c : A) :
    oiAssign ν (pt (.fresh .g) c) ↔
      (SlotVal ν .one c ∨ SlotVal ν .two c) ∧ SlotVal ν .three c := Iff.rfl

theorem litTrue_var (ν : A → Prop) (x : A) (s : Bool) :
    LitTrue (oiAssign ν) (pt .var x) s ↔ LitTrue ν x s := by
  cases s <;> simp [LitTrue]

end Assignment

/-! ### Which tags carry which literals -/

section TagFacts

theorem posPair_link (i : Ix3) (t : OITag) : posPair (.link i) t = false := by
  revert i t
  decide

theorem negPair_link_iff (i : Ix3) (t : OITag) : negPair (.link i) t = true ↔ t = .slot i := by
  revert i t
  decide

theorem posPair_piece_one (t : OITag) :
    posPair (.piece .one) t = true ↔ t = .fresh .d ∨ t = .fresh .e := by
  revert t
  decide

theorem negPair_piece_one (t : OITag) :
    negPair (.piece .one) t = true ↔ t = .slot .one := by
  revert t
  decide

theorem posPair_piece_two (t : OITag) :
    posPair (.piece .two) t = true ↔ t = .slot .two ∨ t = .fresh .e ∨ t = .fresh .f := by
  revert t
  decide

theorem negPair_piece_two (t : OITag) : negPair (.piece .two) t = false := by
  revert t
  decide

theorem posPair_piece_three (t : OITag) :
    posPair (.piece .three) t = true ↔ t = .fresh .f ∨ t = .fresh .g := by
  revert t
  decide

theorem negPair_piece_three (t : OITag) :
    negPair (.piece .three) t = true ↔ t = .slot .three := by
  revert t
  decide

theorem clauseTag_cases {t : OITag} (h : clauseTag t = true) :
    (∃ i, t = .link i) ∨ ∃ i, t = .piece i := by
  revert t
  decide

end TagFacts

/-! ### Correctness -/

section Correctness

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- A clause with three literals of known values, exactly one of them true. -/
private theorem oneIn_of_three {M : Type} [Language.sat.Structure M] {μ : M → Prop} {P : M}
    (q₁ : M) (u₁ : Bool) (q₂ : M) (u₂ : Bool) (q₃ : M) (u₃ : Bool)
    (henum : ∀ y u, OccIn P y u → (y = q₁ ∧ u = u₁) ∨ (y = q₂ ∧ u = u₂) ∨ (y = q₃ ∧ u = u₃))
    (h₁ : OccIn P q₁ u₁) (hv₁ : LitTrue μ q₁ u₁)
    (hv₂ : ¬LitTrue μ q₂ u₂) (hv₃ : ¬LitTrue μ q₃ u₃) :
    ∃ x s, OccIn P x s ∧ LitTrue μ x s ∧
      ∀ y t, OccIn P y t → LitTrue μ y t → y = x ∧ t = s := by
  refine ⟨q₁, u₁, h₁, hv₁, fun y u hy hTy => ?_⟩
  rcases henum y u hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd hTy hv₂
  · exact absurd hTy hv₃

omit [Finite A] in
/-- The literals of the `i`-th link clause of `c`. -/
theorem enum_link {i : Ix3} {c : A} {y : oiInterp.Map A} {u : Bool}
    (h : OccIn (pt (.link i) c) y u) :
    (y = pt (.slot i) c ∧ u = false) ∨ ∃ x s, NthOcc i c x s ∧ y = pt .var x ∧ u = s := by
  rcases occIn_pt_cases h with ⟨t, ht, rfl⟩ | ⟨j, x, hj, hn, rfl⟩
  · cases u with
    | true => simp [posPair_link] at ht
    | false =>
      rw [if_neg (by simp)] at ht
      exact Or.inl ⟨by rw [(negPair_link_iff i t).mp ht], rfl⟩
  · obtain rfl : j = i := by simpa using hj.symm
    exact Or.inr ⟨x, u, hn, rfl, rfl⟩

omit [Finite A] in
/-- The literals of the `i`-th gadget clause of `c`. -/
theorem enum_piece {i : Ix3} {c : A} {y : oiInterp.Map A} {u : Bool}
    (h : OccIn (pt (.piece i) c) y u) :
    ∃ t, (if u then posPair (.piece i) t else negPair (.piece i) t) = true ∧ y = pt t c := by
  rcases occIn_pt_cases h with ⟨t, ht, rfl⟩ | ⟨j, x, hj, -, -⟩
  · exact ⟨t, ht, rfl⟩
  · exact absurd hj (by simp)

/-- **The gadget of a satisfiable input is exactly-one satisfiable.** -/
theorem oneInProper_oiAssign (hw : ¬ThreeSatToSat.Wide A) (hwidth : WidthAtMostThree A)
    {ν : A → Prop} (hν : ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s) :
    OneInProper (oiAssign ν) := by
  intro P hP
  obtain ⟨t, c, rfl⟩ := pt_surj P
  obtain ⟨htag, hc⟩ : clauseTag t = true ∧ IsCl c := by
    rcases (isCl_pt t c).mp hP with h | h
    · exact h
    · exact absurd h hw
  rcases clauseTag_cases htag with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- a link clause: the negated slot and, if there is one, the linked literal
    have hslotOcc : OccIn (pt (.link i) c) (pt (.slot i) c) false :=
      occIn_same_neg hw rfl hc ((negPair_link_iff i _).mpr rfl)
    by_cases hex : ∃ x s, NthOcc i c x s
    · obtain ⟨x, s, hn⟩ := hex
      have hsl : SlotVal ν i c ↔ LitTrue ν x s := slotVal_of_nth hn
      by_cases hv : LitTrue ν x s
      · refine ⟨pt .var x, s, occIn_link_lit hw hc hn, (litTrue_var ν x s).mpr hv,
          fun y u hy hTy => ?_⟩
        rcases enum_link hy with ⟨rfl, rfl⟩ | ⟨x', s', hn', rfl, rfl⟩
        · exact absurd hTy (by simpa [LitTrue] using hsl.mpr hv)
        · obtain ⟨rfl, rfl⟩ := nthOcc_unique hn' hn
          exact ⟨rfl, rfl⟩
      · refine ⟨pt (.slot i) c, false, hslotOcc, by simpa [LitTrue] using fun h => hv (hsl.mp h),
          fun y u hy hTy => ?_⟩
        rcases enum_link hy with ⟨rfl, rfl⟩ | ⟨x', s', hn', rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := nthOcc_unique hn' hn
          exact absurd ((litTrue_var ν _ _).mp hTy) hv
    · have hsl : ¬SlotVal ν i c := by
        rintro ⟨x, s, hn, -⟩
        exact hex ⟨x, s, hn⟩
      refine ⟨pt (.slot i) c, false, hslotOcc, by simpa [LitTrue] using hsl,
        fun y u hy hTy => ?_⟩
      rcases enum_link hy with ⟨rfl, rfl⟩ | ⟨x', s', hn', -, -⟩
      · exact ⟨rfl, rfl⟩
      · exact absurd ⟨x', s', hn'⟩ hex
  · -- a gadget clause
    have hsome : SlotVal ν .one c ∨ SlotVal ν .two c ∨ SlotVal ν .three c :=
      (exists_litTrue_iff_slot hwidth).mp (hν c hc)
    cases i with
    | one =>
      have henum : ∀ y u, OccIn (pt (.piece .one) c) y u →
          (y = pt (.slot .one) c ∧ u = false) ∨ (y = pt (.fresh .d) c ∧ u = true) ∨
            (y = pt (.fresh .e) c ∧ u = true) := by
        intro y u hy
        obtain ⟨t, ht, rfl⟩ := enum_piece hy
        cases u with
        | true =>
          simp only [if_true] at ht
          rcases (posPair_piece_one t).mp ht with rfl | rfl
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        | false =>
          simp only [Bool.false_eq_true, if_false] at ht
          rw [(negPair_piece_one t).mp ht]
          exact Or.inl ⟨rfl, rfl⟩
      have hslot : OccIn (pt (.piece .one) c) (pt (.slot .one) c) false :=
        occIn_same_neg hw rfl hc ((negPair_piece_one _).mpr rfl)
      have hd : OccIn (pt (.piece .one) c) (pt (.fresh .d) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_one _).mpr (Or.inl rfl))
      have he : OccIn (pt (.piece .one) c) (pt (.fresh .e) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_one _).mpr (Or.inr rfl))
      by_cases ha : SlotVal ν .one c
      · by_cases hb : SlotVal ν .two c
        · exact oneIn_of_three (pt (.fresh .d) c) true
            (pt (.slot .one) c) false (pt (.fresh .e) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hd (⟨ha, hb⟩) (not_not_intro ha) (fun h => h.2 hb)
        · exact oneIn_of_three (pt (.fresh .e) c) true
            (pt (.slot .one) c) false (pt (.fresh .d) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            he (⟨ha, hb⟩) (not_not_intro ha) (fun h => hb h.2)
      · exact oneIn_of_three (pt (.slot .one) c) false
          (pt (.fresh .d) c) true (pt (.fresh .e) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hslot (ha) (fun h => ha h.1) (fun h => ha h.1)
    | two =>
      have henum : ∀ y u, OccIn (pt (.piece .two) c) y u →
          (y = pt (.slot .two) c ∧ u = true) ∨ (y = pt (.fresh .e) c ∧ u = true) ∨
            (y = pt (.fresh .f) c ∧ u = true) := by
        intro y u hy
        obtain ⟨t, ht, rfl⟩ := enum_piece hy
        cases u with
        | true =>
          simp only [if_true] at ht
          rcases (posPair_piece_two t).mp ht with rfl | rfl | rfl
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        | false =>
          simp only [Bool.false_eq_true, if_false, negPair_piece_two] at ht
      have hslot : OccIn (pt (.piece .two) c) (pt (.slot .two) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_two _).mpr (Or.inl rfl))
      have he : OccIn (pt (.piece .two) c) (pt (.fresh .e) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_two _).mpr (Or.inr (Or.inl rfl)))
      have hf : OccIn (pt (.piece .two) c) (pt (.fresh .f) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_two _).mpr (Or.inr (Or.inr rfl)))
      by_cases hb : SlotVal ν .two c
      · exact oneIn_of_three (pt (.slot .two) c) true
          (pt (.fresh .e) c) true (pt (.fresh .f) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hslot (hb) (fun h => h.2 hb) (fun h => h.2 hb)
      · by_cases ha : SlotVal ν .one c
        · exact oneIn_of_three (pt (.fresh .e) c) true
            (pt (.slot .two) c) true (pt (.fresh .f) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            he (⟨ha, hb⟩) (hb) (fun h => h.1 ha)
        · exact oneIn_of_three (pt (.fresh .f) c) true
            (pt (.slot .two) c) true (pt (.fresh .e) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hf (⟨ha, hb⟩) (hb) (fun h => ha h.1)
    | three =>
      have henum : ∀ y u, OccIn (pt (.piece .three) c) y u →
          (y = pt (.slot .three) c ∧ u = false) ∨ (y = pt (.fresh .f) c ∧ u = true) ∨
            (y = pt (.fresh .g) c ∧ u = true) := by
        intro y u hy
        obtain ⟨t, ht, rfl⟩ := enum_piece hy
        cases u with
        | true =>
          simp only [if_true] at ht
          rcases (posPair_piece_three t).mp ht with rfl | rfl
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        | false =>
          simp only [Bool.false_eq_true, if_false] at ht
          rw [(negPair_piece_three t).mp ht]
          exact Or.inl ⟨rfl, rfl⟩
      have hslot : OccIn (pt (.piece .three) c) (pt (.slot .three) c) false :=
        occIn_same_neg hw rfl hc ((negPair_piece_three _).mpr rfl)
      have hf : OccIn (pt (.piece .three) c) (pt (.fresh .f) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_three _).mpr (Or.inl rfl))
      have hg : OccIn (pt (.piece .three) c) (pt (.fresh .g) c) true :=
        occIn_same_pos hw rfl hc ((posPair_piece_three _).mpr (Or.inr rfl))
      by_cases hab : SlotVal ν .one c ∨ SlotVal ν .two c
      · by_cases hcc : SlotVal ν .three c
        · exact oneIn_of_three (pt (.fresh .g) c) true
            (pt (.slot .three) c) false (pt (.fresh .f) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hg (⟨hab, hcc⟩) (not_not_intro hcc) (fun h => hab.elim h.1 h.2)
        · exact oneIn_of_three (pt (.slot .three) c) false
            (pt (.fresh .f) c) true (pt (.fresh .g) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hslot (hcc) (fun h => hab.elim h.1 h.2) (fun h => hcc h.2)
      · -- neither of the first two slots is true, so the third one is
        have hcc : SlotVal ν .three c := by tauto
        exact oneIn_of_three (pt (.fresh .f) c) true
            (pt (.slot .three) c) false (pt (.fresh .g) c) true
            (fun y u hy => by rcases henum y u hy with h | h | h <;> tauto)
            hf ⟨fun h => hab (Or.inl h), fun h => hab (Or.inr h)⟩ (not_not_intro hcc)
            (fun h => hab h.1)

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] in
theorem litTrue_var_gen {μ : oiInterp.Map A → Prop} (x : A) (s : Bool) :
    LitTrue (fun z => μ (pt .var z)) x s ↔ LitTrue μ (pt .var x) s := by
  cases s <;> exact Iff.rfl

omit [Finite A] in
/-- **A gadget that is exactly-one satisfiable comes from a satisfiable
input.** -/
theorem satisfiable_of_oneInProper (hw : ¬ThreeSatToSat.Wide A)
    {μ : oiInterp.Map A → Prop} (hμ : OneInProper μ) (c : A) (hc : IsCl c) :
    ∃ x s, OccIn c x s ∧ LitTrue (fun z => μ (pt .var z)) x s := by
  -- the slots carry the values of the literals they link
  have hslot : ∀ i : Ix3,
      μ (pt (.slot i) c) ↔ SlotVal (fun z => μ (pt .var z)) i c := by
    intro i
    obtain ⟨q, u, hq, hTq, huniq⟩ := hμ (pt (.link i) c) (isCl_gadget rfl hc)
    have hslotOcc : OccIn (pt (.link i) c) (pt (.slot i) c) false :=
      occIn_same_neg hw rfl hc ((negPair_link_iff i _).mpr rfl)
    by_cases hex : ∃ x s, NthOcc i c x s
    · obtain ⟨x, s, hn⟩ := hex
      have hlitOcc : OccIn (pt (.link i) c) (pt .var x) s := occIn_link_lit hw hc hn
      have hne : (pt (.slot i) c : oiInterp.Map A) ≠ pt .var x := by simp [pt_eq_iff]
      rw [slotVal_of_nth hn, litTrue_var_gen]
      constructor
      · intro hs
        rcases enum_link hq with ⟨rfl, rfl⟩ | ⟨x', s', hn', rfl, rfl⟩
        · exact absurd hs hTq
        · obtain ⟨rfl, rfl⟩ := nthOcc_unique hn' hn
          exact hTq
      · intro hlit
        by_contra hs
        obtain ⟨e1, -⟩ := huniq _ _ hslotOcc hs
        obtain ⟨e2, -⟩ := huniq (pt .var x) s hlitOcc hlit
        exact hne (e1.trans e2.symm)
    · have hsl : ¬SlotVal (fun z => μ (pt .var z)) i c := by
        rintro ⟨x, s, hn, -⟩
        exact hex ⟨x, s, hn⟩
      refine iff_of_false ?_ hsl
      rcases enum_link hq with ⟨rfl, rfl⟩ | ⟨x', s', hn', -, -⟩
      · exact hTq
      · exact absurd ⟨x', s', hn'⟩ hex
  -- the gadget clauses force one of the slots to be true
  have hsome : SlotVal (fun z => μ (pt .var z)) .one c ∨
      SlotVal (fun z => μ (pt .var z)) .two c ∨
      SlotVal (fun z => μ (pt .var z)) .three c := by
    by_contra hno
    push Not at hno
    obtain ⟨hn1, hn2, hn3⟩ := hno
    have h1 : ¬μ (pt (.slot .one) c) := fun h => hn1 ((hslot _).mp h)
    have h2 : ¬μ (pt (.slot .two) c) := fun h => hn2 ((hslot _).mp h)
    have h3 : ¬μ (pt (.slot .three) c) := fun h => hn3 ((hslot _).mp h)
    -- the first gadget clause forces `d` and `e` false
    obtain ⟨q1, u1, -, -, huniq1⟩ := hμ (pt (.piece .one) c) (isCl_gadget rfl hc)
    have hdf : ¬μ (pt (.fresh .d) c) := by
      intro hdt
      obtain ⟨e1, -⟩ := huniq1 _ _
        (occIn_same_neg hw rfl hc ((negPair_piece_one _).mpr rfl)) h1
      obtain ⟨e2, -⟩ := huniq1 _ _
        (occIn_same_pos hw rfl hc ((posPair_piece_one _).mpr (Or.inl rfl))) hdt
      exact absurd (e1.trans e2.symm) (by simp [pt_eq_iff])
    have hef : ¬μ (pt (.fresh .e) c) := by
      intro het
      obtain ⟨e1, -⟩ := huniq1 _ _
        (occIn_same_neg hw rfl hc ((negPair_piece_one _).mpr rfl)) h1
      obtain ⟨e2, -⟩ := huniq1 _ _
        (occIn_same_pos hw rfl hc ((posPair_piece_one _).mpr (Or.inr rfl))) het
      exact absurd (e1.trans e2.symm) (by simp [pt_eq_iff])
    -- the second one then forces `f` true
    obtain ⟨q2, u2, hq2, hT2, -⟩ := hμ (pt (.piece .two) c) (isCl_gadget rfl hc)
    have hff : μ (pt (.fresh .f) c) := by
      obtain ⟨t, ht, rfl⟩ := enum_piece hq2
      cases u2 with
      | true =>
        simp only [if_true] at ht
        rcases (posPair_piece_two t).mp ht with rfl | rfl | rfl
        · exact absurd hT2 h2
        · exact absurd hT2 hef
        · exact hT2
      | false => simp only [Bool.false_eq_true, if_false, negPair_piece_two] at ht
    -- and the third one now has two true literals
    obtain ⟨q3, u3, -, -, huniq3⟩ := hμ (pt (.piece .three) c) (isCl_gadget rfl hc)
    obtain ⟨e1, -⟩ := huniq3 _ _
      (occIn_same_neg hw rfl hc ((negPair_piece_three _).mpr rfl)) h3
    obtain ⟨e2, -⟩ := huniq3 _ _
      (occIn_same_pos hw rfl hc ((posPair_piece_three _).mpr (Or.inl rfl))) hff
    exact absurd (e1.trans e2.symm) (by simp [pt_eq_iff])
  rcases hsome with ⟨x, s, hn, hT⟩ | ⟨x, s, hn, hT⟩ | ⟨x, s, hn, hT⟩ <;>
    exact ⟨x, s, hn.occIn, hT⟩

/-- Correctness of the reduction: a CNF structure is a yes-instance of 3SAT
iff its gadget is exactly-one satisfiable. -/
theorem threeSatisfiable_iff_oneInSatisfiable_map :
    ThreeSatisfiable A ↔ OneInSatisfiable (oiInterp.Map A) := by
  by_cases hw : ThreeSatToSat.Wide A
  · -- on a wide input every element is a clause, and none has a literal
    refine iff_of_false
      (fun h => (ThreeSatToSat.wide_iff_not_widthAtMostThree A).mp hw h.1) ?_
    rintro ⟨μ, hμ⟩
    obtain ⟨c, -, -, -, -⟩ := id hw
    obtain ⟨q, u, hq, -, -⟩ := hμ (pt .var c) ((isCl_pt _ _).mpr (Or.inr hw))
    obtain ⟨t, y, rfl⟩ := pt_surj q
    cases u with
    | true => exact ((posIn_pt _ _ _ _).mp hq.2).1 hw
    | false => exact ((negIn_pt _ _ _ _).mp hq.2).1 hw
  · have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hw ((ThreeSatToSat.wide_iff_not_widthAtMostThree A).mpr h)
    rw [ThreeSatisfiable, and_iff_right hwidth]
    constructor
    · rintro ⟨ν, hν⟩
      exact ⟨oiAssign ν, oneInProper_oiAssign hw hwidth (satClauses_occ hν)⟩
    · rintro ⟨μ, hμ⟩
      refine ⟨fun z => μ (pt .var z), fun c hc => ?_⟩
      obtain ⟨x, s, hocc, hT⟩ := satisfiable_of_oneInProper hw hμ c hc
      cases s with
      | true => exact ⟨x, Or.inl ⟨hocc.2, hT⟩⟩
      | false => exact ⟨x, Or.inr ⟨hocc.2, hT⟩⟩

end Correctness

/-- **3SAT ordered-FO-reduces to 1-in-SAT**: the three-slot gadget. -/
noncomputable def threeSat_ordered_fo_reduction_oneInSat : ThreeSAT ≤ᶠᵒ[≤] OneInSAT where
  Tag := OITag
  dim := 1
  toInterpretation := oiInterp
  correct _A _ _ _ _ := threeSatisfiable_iff_oneInSatisfiable_map

end OneInRed

end DescriptiveComplexity
