/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MachineNumber.Defs
import DescriptiveComplexity.Problems.HornSat.Number
import DescriptiveComplexity.Problems.Machine.HornInterp

/-!
# The number written by unit propagation reduces to the number written by a machine

`DescriptiveComplexity.MachNum.hornNumber_ordered_parsimonious_dtmNumber`: the
ordered parsimonious reduction `HornNumber ≤ᵖ[≤] DTMNumber`.

The machine is the unit-propagation machine of deterministic machine
acceptance (`DescriptiveComplexity.hornMachine`), unchanged: it keeps one cell
per element of the instance, marked when the element is forced, and on a
satisfiable Horn formula it accepts with the propagation closure on its tape
(`DescriptiveComplexity.hornMachine_final`). What the reduction adds is the
reading of the number: the output cells are the cells of the output variables,
the symbols read as `1` are the marked ones, and the cells are compared as
their variables are (`DescriptiveComplexity.MachNum.numTuringInterp`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure HornTM SatOcc

namespace MachNum

/-! ### The interpretation -/

/-- The vocabulary of ordered CNF instances, read in the one of ordered Horn
formulas writing a number. -/
def satOutHom : satOrd →ᴸ Language.satOut.sum Language.order :=
  LHom.sumMap LHom.sumInl (LHom.id Language.order)

instance satOutHom_isExpansionOn (A : Type) [Language.satOut.Structure A] [LinearOrder A] :
    satOutHom.IsExpansionOn A where
  map_onFunction := fun {_} f _ => isEmptyElim f
  map_onRelation := fun {_} R _ => by cases R <;> rfl

/-- “Is an output variable”, over the ordered vocabulary. -/
abbrev oOutSym : (Language.satOut.sum Language.order).Relations 1 := Sum.inl hnOut

/-- The comparison of the output variables, over the ordered vocabulary. -/
abbrev oBelowSym : (Language.satOut.sum Language.order).Relations 2 := Sum.inl hnBelow

/-- **The unit-propagation machine, with its output**: the machine of
`DescriptiveComplexity.HornTM.hornTuringInterp`, the cells of the output
variables as output cells, the marked symbols read as `1`. -/
noncomputable def numTuringInterp :
    FOInterpretation (Language.satOut.sum Language.order) Language.turingOut UPTag 3 where
  relFormula {n} R :=
    match R with
    | Sum.inl r => fun t => satOutHom.onFormula (hornTuringInterp.relFormula r t)
    | Sum.inr s =>
      match n, s with
      | _, .out => fun t =>
          match t 0 with
          | .pCell =>
              (minF (L := Language.satOut) ((0 : Fin 1), (1 : Fin 3)) ⊓
                minF (L := Language.satOut) ((0 : Fin 1), (2 : Fin 3))) ⊓
              Relations.formula₁ oOutSym (Term.var ((0 : Fin 1), (0 : Fin 3)))
          | _ => ⊥
      | _, .one => fun t =>
          match t 0 with
          | .sM => ⊤
          | _ => ⊥
      | _, .below => fun t =>
          match t 0, t 1 with
          | .pCell, .pCell =>
              Relations.formula₂ oBelowSym (Term.var ((0 : Fin 2), (0 : Fin 3)))
                (Term.var ((1 : Fin 2), (0 : Fin 3)))
          | _, _ => ⊥

section Correct

variable {A : Type} [Language.satOut.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- The machine part of the interpreted structure is the unit-propagation
machine's. -/
theorem relMap_inl {n : ℕ} (r : Language.turing.Relations n) (xs : Fin n → HV A) :
    RelMap (M := numTuringInterp.Map A) (L := Language.turing) r xs ↔
      RelMap (M := hornTuringInterp.Map A) r xs :=
  LHom.realize_onFormula satOutHom _

/-- The universe of the interpreted structure is the tagged triples. -/
def numMapEquiv : HV A ≃ numTuringInterp.Map A := Equiv.refl (HV A)

/-- **The interpreted structure describes the unit-propagation machine.** -/
theorem agree_num :
    TMData.Agree (numMapEquiv (A := A)) (hornMachine A) (tmData (numTuringInterp.Map A)) := by
  have h : TMData.Agree (Equiv.refl (HV A)) (tmData (hornTuringInterp.Map A))
      (tmData (numTuringInterp.Map A)) :=
    { posn := fun b => (relMap_inl tmPosn ![b]).symm
      le := fun b b' => (relMap_inl tmLe ![b, b']).symm
      tr := fun b => (relMap_inl tmTr ![b]).symm
      start := fun b => (relMap_inl tmStart ![b]).symm
      acc := fun b => (relMap_inl tmAcc ![b]).symm
      blank := fun b => (relMap_inl tmBlank ![b]).symm
      right := fun b => (relMap_inl tmRight ![b]).symm
      src := fun b b' => (relMap_inl tmSrc ![b, b']).symm
      read := fun b b' => (relMap_inl tmRead ![b, b']).symm
      dst := fun b b' => (relMap_inl tmDst ![b, b']).symm
      write := fun b b' => (relMap_inl tmWrite ![b, b']).symm
      inp := fun b b' => (relMap_inl tmInp ![b, b']).symm }
  exact (agree_hornMachine (A := A)).trans h

/-- The cell of an element. -/
noncomputable def cellPt (x : A) : numTuringInterp.Map A :=
  numMapEquiv (posHCell x)

omit [Finite A] [Nonempty A] in
theorem relMap_out (p : HV A) :
    RelMap (M := numTuringInterp.Map A) mnOut ![numMapEquiv p] ↔
      p.1 = UPTag.pCell ∧ ((∀ a : A, p.2 1 ≤ a) ∧ ∀ a : A, p.2 2 ≤ a) ∧ RelMap hnOut ![p.2 0] := by
  obtain ⟨t, w⟩ := p
  rw [FOInterpretation.relMap_map]
  cases t <;>
    first
      | exact iff_of_false id (fun h => by simp at h)
      | exact (Formula.realize_inf.trans (and_congr (Formula.realize_inf.trans
          (and_congr (realize_minF _) (realize_minF _))) Formula.realize_rel₁)).trans
          (and_iff_right rfl).symm

omit [Finite A] [Nonempty A] in
theorem relMap_one (a : HV A) :
    RelMap (M := numTuringInterp.Map A) mnOne ![numMapEquiv a] ↔ a.1 = UPTag.sM := by
  obtain ⟨t, w⟩ := a
  rw [FOInterpretation.relMap_map]
  cases t <;>
    first
      | exact iff_of_false id (fun h => by simp at h)
      | exact iff_of_true (Formula.realize_top.mpr trivial) rfl

theorem relMap_below_cell (y x : A) :
    RelMap (M := numTuringInterp.Map A) mnBelow ![cellPt y, cellPt x] ↔
      RelMap hnBelow ![y, x] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₂

/-- The output cells are the cells of the output variables. -/
theorem out_iff (p : numTuringInterp.Map A) :
    RelMap (M := numTuringInterp.Map A) mnOut ![p] ↔ ∃ x : A, p = cellPt x ∧ RelMap hnOut ![x] := by
  refine (relMap_out (A := A) p).trans ⟨?_, ?_⟩
  · rintro ⟨htag, hmin, hout⟩
    exact ⟨p.2 0, eq_posHCell_of_posn (p := p) (by
      obtain ⟨t, w⟩ := p
      cases htag
      exact hmin) htag, hout⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨rfl, ⟨fun a => botA_le a, fun a => botA_le a⟩, hx⟩

omit [Language.satOut.Structure A] in
theorem cellPt_injective : Function.Injective (cellPt (A := A)) := fun _ _ h =>
  congrFun (congrArg Prod.snd h) 0

/-- **The digits of the machine are the forced output variables** of a
satisfiable Horn formula. -/
theorem outDigit_iff (hs : HornSatisfiable A) (p : numTuringInterp.Map A) :
    OutDigit p ↔ ∃ x : A, p = cellPt x ∧ ForcedDigit x := by
  have hag := agree_num (A := A)
  obtain ⟨cfin, n, M', hn, hrun, hacc, htape, hM'⟩ := hornMachine_final hs.1 hs.2
  have hhalt : (hornMachine A).Halts cfin :=
    ⟨confHInit, n, isInit_confHInit, hn, hrun, fun e ⟨τ, hτ, hsrc, _⟩ =>
      hTag_no_stateTag_qAcc τ.1 (hTr_isHTrTag hτ) ((hSrc_tag hsrc).symm.trans hacc)⟩
  have hone : ∀ x : A, RelMap (M := numTuringInterp.Map A) mnOne
      ![(cfin.map numMapEquiv).tape (cellPt x)] ↔ Forced x := by
    intro x
    change RelMap (M := numTuringInterp.Map A) mnOne ![numMapEquiv (cfin.tape (posHCell x))] ↔ _
    rw [relMap_one, htape, hTape_posHCell, ← hM']
    cases M' x <;> simp [oneH]
  constructor
  · rintro ⟨hout, c, hc, -, h1⟩
    obtain ⟨x, rfl, hx⟩ := (out_iff p).mp hout
    obtain ⟨d, rfl⟩ := Config.map_surjective numMapEquiv c
    obtain rfl := TMData.halts_unique hornMachine_wellFormed hornMachine_deterministic
      ((hag.halts d).mpr hc) hhalt
    exact ⟨x, rfl, hx, (hone x).mp h1⟩
  · rintro ⟨x, rfl, hx, hf⟩
    exact ⟨(out_iff _).mpr ⟨x, rfl, hx⟩, cfin.map numMapEquiv, (hag.halts cfin).mp hhalt,
      (hag.acc _).mp hacc, (hone x).mpr hf⟩

/-- A machine that writes a digit accepts. -/
theorem hornSatisfiable_of_outDigit {p : numTuringInterp.Map A} (h : OutDigit p) :
    HornSatisfiable A := by
  have hag := agree_num (A := A)
  obtain ⟨-, c, hc, hacc, -⟩ := h
  obtain ⟨d, rfl⟩ := Config.map_surjective numMapEquiv c
  obtain ⟨c₀, n, hinit, hn, hrun, -⟩ := (hag.halts d).mpr hc
  exact (hornMachine_accepts_iff (A := A)).mp ⟨c₀, d, n, hinit, hn, hrun, (hag.acc _).mpr hacc⟩

/-- The output cells strictly below the cell of a variable are the cells of
the output variables strictly below it. -/
theorem lowerCell_iff (x : A) (q : numTuringInterp.Map A) :
    LowerCell (cellPt x) q ↔ ∃ y : A, q = cellPt y ∧ LowerVar x y := by
  constructor
  · rintro ⟨ho, hne, hb⟩
    obtain ⟨y, rfl, hy⟩ := (out_iff q).mp ho
    exact ⟨y, rfl, hy, fun h => hne (congrArg cellPt h), (relMap_below_cell y x).mp hb⟩
  · rintro ⟨y, rfl, hy, hne, hb⟩
    exact ⟨(out_iff _).mpr ⟨y, rfl, hy⟩, fun h => hne (cellPt_injective h),
      (relMap_below_cell y x).mpr hb⟩

theorem cellRank_cellPt (x : A) : cellRank (cellPt x) = varRank x := by
  rw [cellRank, varRank]
  symm
  refine Nat.card_eq_of_bijective
    (fun y => ⟨cellPt y.1, (lowerCell_iff x _).mpr ⟨y.1, rfl, y.2⟩⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (cellPt_injective (congrArg Subtype.val h))
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl, hy⟩ := (lowerCell_iff x q).mp hq
    exact ⟨⟨y, hy⟩, rfl⟩

open Classical in
/-- **The machine writes the number written by unit propagation.** -/
theorem machineNumber_numTuringInterp :
    machineNumber (numTuringInterp.Map A) = hornNumber A := by
  have hag := agree_num (A := A)
  have hwd : (tmData (numTuringInterp.Map A)).WellFormed ∧
      (tmData (numTuringInterp.Map A)).Deterministic :=
    ⟨hag.wellFormed.mp hornMachine_wellFormed, hag.deterministic.mp hornMachine_deterministic⟩
  rw [machineNumber, hornNumber, ite_eq_left hwd]
  by_cases hs : HornSatisfiable A
  · rw [ite_eq_left hs]
    have hsupp : ∀ g ∈ Function.support
        (fun g : numTuringInterp.Map A => if OutDigit g then 2 ^ cellRank g else 0),
        g ∈ Set.univ ↔ g ∈ Set.range (cellPt (A := A)) := by
      intro g hg
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      have hd : OutDigit g := by
        by_contra h
        exact hg (ite_eq_right h)
      obtain ⟨x, hx, -⟩ := (outDigit_iff hs g).mp hd
      exact ⟨x, hx.symm⟩
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ hsupp,
      finsum_mem_range cellPt_injective]
    refine finsum_congr fun x => ?_
    rw [cellRank_cellPt x]
    refine if_congr ((outDigit_iff hs _).trans ⟨?_, fun h => ⟨x, rfl, h⟩⟩) rfl rfl
    rintro ⟨y, hy, h⟩
    rwa [cellPt_injective hy]
  · rw [ite_eq_right hs]
    refine (finsum_congr fun g => ?_).trans finsum_zero
    exact ite_eq_right fun h => hs (hornSatisfiable_of_outDigit h)

end Correct

/-- **The number written by unit propagation reduces to the number written by
a machine**: the unit-propagation machine, with the cells of the output
variables as its output. -/
noncomputable def hornNumber_ordered_parsimonious_dtmNumber : HornNumber ≤ᵖ[≤] DTMNumber where
  Tag := UPTag
  dim := 3
  toInterpretation := numTuringInterp
  correct _ _ _ _ _ := machineNumber_numTuringInterp.symm

end MachNum

end DescriptiveComplexity
