/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MachineNumber.Defs
import DescriptiveComplexity.Problems.HornSat.Number
import DescriptiveComplexity.Problems.Machine.HornInterp
import DescriptiveComplexity.OrderedReorder
import DescriptiveComplexity.Syntax

/-!
# The number written by unit propagation reduces to the number written by a machine

`DescriptiveComplexity.MachNum.hornNumber_ordered_parsimonious_dtmNumber`: the
ordered parsimonious reduction `HornNumber ≤ᵖ[≤] DTMNumber`.

The machine is the unit-propagation machine of deterministic machine
acceptance (`DescriptiveComplexity.hornMachine`), unchanged: it keeps one cell
per element of the instance, in the order of the instance, marked when the
element is forced, and on a satisfiable Horn formula it accepts with the
propagation closure on its tape (`DescriptiveComplexity.hornMachine_final`).
What the reduction adds is the reading of the number: the output cells are
the cells of the output variables and the symbols read as `1` are the marked
ones (`DescriptiveComplexity.MachNum.numTuringInterp`).

The machine reads its digits in tape order, while the Horn formula compares
its output variables by a relation of the instance, `below`. The reduction
reconciles the two by **reordering its input** first
(`DescriptiveComplexity.FOInterpretation.reorder`): when `below` linearly
orders the output variables, the new order puts them first, in that order,
and the other elements after, in the order given
(`DescriptiveComplexity.MachNum.newOrder`); the machine then lays its cells
out in the new order, and the cells of the output variables come in the order
of significance. When `below` is not such an order the number written by the
formula is `0`, and the reduction marks no output cell.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure HornTM SatOcc

namespace MachNum

/-! ### The vocabulary -/

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

/-! ### The order of the output variables, as a sentence -/

/-- “The comparison of the output variables is a linear order on them”
(`DescriptiveComplexity.VarOrder`), as a sentence. -/
noncomputable def varOrdS : (Language.satOut.sum Language.order).Sentence :=
  fo% ((∀ p, oOutSym(p) → oBelowSym(p, p)) ∧
      ∀ p, ∀ q, ∀ r, oOutSym(p) → oOutSym(q) → oOutSym(r) → oBelowSym(p, q) → oBelowSym(q, r) →
        oBelowSym(p, r)) ∧
    (∀ p, ∀ q, oOutSym(p) → oOutSym(q) → oBelowSym(p, q) → oBelowSym(q, p) → p ≐ q) ∧
    ∀ p, ∀ q, oOutSym(p) → oOutSym(q) → oBelowSym(p, q) ∨ oBelowSym(q, p)

/-- The sentence, as a formula over any set of free variables. -/
noncomputable def varOrdF (α : Type) : (Language.satOut.sum Language.order).Formula α :=
  Formula.relabel (fun e : Empty => e.elim) varOrdS

section VarOrd

variable {A : Type} [Language.satOut.Structure A] [LinearOrder A]

theorem realize_varOrdS : A ⊨ varOrdS ↔ VarOrder A := by
  rw [varOrdS, VarOrder, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, relMap_sumInl]
  refine and_assoc.trans (and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩
    (and_congr ⟨fun h a b c => h (fun _ => a) (fun _ => b) fun _ => c,
        fun h i j k => h (i 0) (j 0) (k 0)⟩
      (and_congr ⟨fun h a b => h (fun _ => a) fun _ => b, fun h i j => h (i 0) (j 0)⟩
        ⟨fun h a b => h (fun _ => a) fun _ => b, fun h i j => h (i 0) (j 0)⟩)))

theorem realize_varOrdF {α : Type} (v : α → A) : (varOrdF α).Realize v ↔ VarOrder A := by
  rw [varOrdF, Formula.realize_relabel]
  exact (iff_of_eq (congrArg _ (Subsingleton.elim _ default))).trans realize_varOrdS

end VarOrd

/-! ### Reordering the instance -/

/-- The new order of the instance, as a formula of its two arguments: when
the output variables are linearly ordered by `below`, they come first, in
that order, and the other elements after, in the order given; otherwise the
order given. -/
noncomputable def reordF : (Language.satOut.sum Language.order).Formula (Fin 2 × Fin 1) :=
  fo%⟨u, v⟩ (!(varOrdF (Fin 2 × Fin 1)) ∧
      ((oOutSym(u) ∧ oOutSym(v) ∧ oBelowSym(u, v)) ∨ (oOutSym(u) ∧ ¬oOutSym(v)) ∨
        (¬oOutSym(u) ∧ ¬oOutSym(v) ∧ leSymb(u, v)))) ∨
    (¬!(varOrdF (Fin 2 × Fin 1)) ∧ leSymb(u, v))

section Reorder

variable {A : Type} [Language.satOut.Structure A] [LinearOrder A]

variable (A) in
open Classical in
/-- The new order, as a relation. -/
def NewLe (x y : A) : Prop :=
  if VarOrder A then
    (RelMap hnOut ![x] ∧ RelMap hnOut ![y] ∧ RelMap hnBelow ![x, y]) ∨
      (RelMap hnOut ![x] ∧ ¬RelMap hnOut ![y]) ∨
        (¬RelMap hnOut ![x] ∧ ¬RelMap hnOut ![y] ∧ x ≤ y)
  else x ≤ y

theorem realize_reordF (v : Fin 2 × Fin 1 → A) :
    reordF.Realize v ↔ NewLe A (v (0, 0)) (v (1, 0)) := by
  classical
  rw [reordF, NewLe]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not, realize_varOrdF,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, relMap_sumInl]
  by_cases hv : VarOrder A
  · simp only [hv, true_and, not_true_eq_false, false_and, or_false]
    exact Iff.rfl
  · simp only [hv, false_and, not_false_eq_true, true_and, false_or]
    exact Iff.rfl

variable (A) in
theorem isLinOrd_newLe : IsLinOrd (NewLe A) := by
  classical
  unfold IsLinOrd NewLe
  by_cases hv : VarOrder A
  · simp only [ite_eq_left hv]
    obtain ⟨hr, ht, ha, hl⟩ := hv
    refine ⟨fun x => ?_, fun x y z hxy hyz => ?_, fun x y hxy hyx => ?_, fun x y => ?_⟩
    · by_cases hx : RelMap hnOut ![x]
      · exact Or.inl ⟨hx, hx, hr x hx⟩
      · exact Or.inr (Or.inr ⟨hx, hx, le_rfl⟩)
    · rcases hxy with ⟨hx, hy, hxy⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hxy⟩ <;>
        rcases hyz with ⟨hy', hz, hyz⟩ | ⟨hy', hz⟩ | ⟨hy', hz, hyz⟩
      · exact Or.inl ⟨hx, hz, ht x y z hx hy hz hxy hyz⟩
      · exact Or.inr (Or.inl ⟨hx, hz⟩)
      · exact absurd hy hy'
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact Or.inr (Or.inl ⟨hx, hz⟩)
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact Or.inr (Or.inr ⟨hx, hz, le_trans hxy hyz⟩)
    · rcases hxy with ⟨hx, hy, hxy⟩ | ⟨hx, hy⟩ | ⟨hx, hy, hxy⟩ <;>
        rcases hyx with ⟨hy', hx', hyx⟩ | ⟨hy', hx'⟩ | ⟨hy', hx', hyx⟩
      · exact ha x y hx hy hxy hyx
      · exact absurd hx hx'
      · exact absurd hx hx'
      · exact absurd hy' hy
      · exact absurd hy' hy
      · exact absurd hx hx'
      · exact absurd hx' hx
      · exact absurd hy' hy
      · exact le_antisymm hxy hyx
    · by_cases hx : RelMap hnOut ![x] <;> by_cases hy : RelMap hnOut ![y]
      · exact (hl x y hx hy).imp (fun h => Or.inl ⟨hx, hy, h⟩) fun h => Or.inl ⟨hy, hx, h⟩
      · exact Or.inl (Or.inr (Or.inl ⟨hx, hy⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
      · exact (le_total x y).imp (fun h => Or.inr (Or.inr ⟨hx, hy, h⟩))
          fun h => Or.inr (Or.inr ⟨hy, hx, h⟩)
  · simp only [ite_eq_right hv]
    exact isLinOrd_le

variable (A) in
/-- **The new order of the instance.** -/
@[instance_reducible]
noncomputable def newOrder : LinearOrder A :=
  (isLinOrd_newLe A).toLinearOrder

/-- Under the new order, the output variables compare as `below` says, when
`below` linearly orders them. -/
theorem newLe_out (hv : VarOrder A) {x y : A} (hx : RelMap hnOut ![x]) (hy : RelMap hnOut ![y]) :
    NewLe A y x ↔ RelMap hnBelow ![y, x] := by
  classical
  simp only [NewLe, hv, ite_true, hx, hy, true_and, not_true_eq_false, and_false, false_and,
    or_false]

end Reorder

/-! ### The interpretation -/

/-- **The unit-propagation machine, with its output**: the machine of
`DescriptiveComplexity.HornTM.hornTuringInterp`, the cells of the output
variables as output cells – when the output variables are linearly ordered –
and the marked symbols read as `1`. -/
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
              ((minF (L := Language.satOut) ((0 : Fin 1), (1 : Fin 3)) ⊓
                minF (L := Language.satOut) ((0 : Fin 1), (2 : Fin 3))) ⊓
              Relations.formula₁ oOutSym (Term.var ((0 : Fin 1), (0 : Fin 3)))) ⊓
              varOrdF (Fin 1 × Fin 3)
          | _ => ⊥
      | _, .one => fun t =>
          match t 0 with
          | .sM => ⊤
          | _ => ⊥

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
      p.1 = UPTag.pCell ∧ (((∀ a : A, p.2 1 ≤ a) ∧ ∀ a : A, p.2 2 ≤ a) ∧ RelMap hnOut ![p.2 0]) ∧
        VarOrder A := by
  obtain ⟨t, w⟩ := p
  rw [FOInterpretation.relMap_map]
  cases t <;>
    first
      | exact iff_of_false id (fun h => by simp at h)
      | exact (Formula.realize_inf.trans (and_congr (Formula.realize_inf.trans (and_congr
          (Formula.realize_inf.trans (and_congr (realize_minF _) (realize_minF _)))
          Formula.realize_rel₁)) (realize_varOrdF _))).trans (and_iff_right rfl).symm

omit [Finite A] [Nonempty A] in
theorem relMap_one (a : HV A) :
    RelMap (M := numTuringInterp.Map A) mnOne ![numMapEquiv a] ↔ a.1 = UPTag.sM := by
  obtain ⟨t, w⟩ := a
  rw [FOInterpretation.relMap_map]
  cases t <;>
    first
      | exact iff_of_false id (fun h => by simp at h)
      | exact iff_of_true (Formula.realize_top.mpr trivial) rfl

/-- The cells of the variables are in the order of the variables. -/
theorem relMap_le_cell (y x : A) :
    RelMap (M := numTuringInterp.Map A) mnLe ![cellPt y, cellPt x] ↔ y ≤ x :=
  ((agree_num (A := A)).le (posHCell y) (posHCell x)).symm.trans posHCell_le_iff

/-- The output cells are the cells of the output variables, when these are
linearly ordered. -/
theorem out_iff (p : numTuringInterp.Map A) :
    RelMap (M := numTuringInterp.Map A) mnOut ![p] ↔
      VarOrder A ∧ ∃ x : A, p = cellPt x ∧ RelMap hnOut ![x] := by
  refine (relMap_out (A := A) p).trans ⟨?_, ?_⟩
  · rintro ⟨htag, ⟨hmin, hout⟩, hv⟩
    exact ⟨hv, p.2 0, eq_posHCell_of_posn (p := p) (by
      obtain ⟨t, w⟩ := p
      cases htag
      exact hmin) htag, hout⟩
  · rintro ⟨hv, x, rfl, hx⟩
    exact ⟨rfl, ⟨⟨fun a => botA_le a, fun a => botA_le a⟩, hx⟩, hv⟩

/-- A machine with an output cell has its output variables linearly
ordered. -/
theorem varOrder_of_out {p : numTuringInterp.Map A}
    (h : RelMap (M := numTuringInterp.Map A) mnOut ![p]) : VarOrder A :=
  ((out_iff p).mp h).1

omit [Language.satOut.Structure A] in
theorem cellPt_injective : Function.Injective (cellPt (A := A)) := fun _ _ h =>
  congrFun (congrArg Prod.snd h) 0

/-- **The digits of the machine are the forced output variables** of a
satisfiable Horn formula whose output variables are linearly ordered. -/
theorem outDigit_iff (hs : HornSatisfiable A) (hv : VarOrder A) (p : numTuringInterp.Map A) :
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
    obtain ⟨-, x, rfl, hx⟩ := (out_iff p).mp hout
    obtain ⟨d, rfl⟩ := Config.map_surjective numMapEquiv c
    obtain rfl := TMData.halts_unique hornMachine_wellFormed hornMachine_deterministic
      ((hag.halts d).mpr hc) hhalt
    exact ⟨x, rfl, hx, (hone x).mp h1⟩
  · rintro ⟨x, rfl, hx, hf⟩
    exact ⟨(out_iff _).mpr ⟨hv, x, rfl, hx⟩, cfin.map numMapEquiv, (hag.halts cfin).mp hhalt,
      (hag.acc _).mp hacc, (hone x).mpr hf⟩

/-- A machine that writes a digit accepts. -/
theorem hornSatisfiable_of_outDigit {p : numTuringInterp.Map A} (h : OutDigit p) :
    HornSatisfiable A := by
  have hag := agree_num (A := A)
  obtain ⟨-, c, hc, hacc, -⟩ := h
  obtain ⟨d, rfl⟩ := Config.map_surjective numMapEquiv c
  obtain ⟨c₀, n, hinit, hn, hrun, -⟩ := (hag.halts d).mpr hc
  exact (hornMachine_accepts_iff (A := A)).mp ⟨c₀, d, n, hinit, hn, hrun, (hag.acc _).mpr hacc⟩

/-- The output cells before the cell of a variable are the cells of the
output variables before it, when the output variables are linearly
ordered. -/
theorem lowerCell_iff (hv : VarOrder A) (x : A) (q : numTuringInterp.Map A) :
    LowerCell (cellPt x) q ↔ ∃ y : A, q = cellPt y ∧ RelMap hnOut ![y] ∧ y ≠ x ∧ y ≤ x := by
  constructor
  · rintro ⟨ho, hne, hb⟩
    obtain ⟨-, y, rfl, hy⟩ := (out_iff q).mp ho
    exact ⟨y, rfl, hy, fun h => hne (congrArg cellPt h), (relMap_le_cell y x).mp hb⟩
  · rintro ⟨y, rfl, hy, hne, hb⟩
    exact ⟨(out_iff _).mpr ⟨hv, y, rfl, hy⟩, fun h => hne (cellPt_injective h),
      (relMap_le_cell y x).mpr hb⟩

/-- **The rank of the cell of an output variable is the rank of the
variable**, when the order of the instance compares the output variables as
`below` does. -/
theorem cellRank_cellPt (hv : VarOrder A)
    (hB : ∀ x y : A, RelMap hnOut ![x] → RelMap hnOut ![y] → (RelMap hnBelow ![y, x] ↔ y ≤ x))
    {x : A} (hx : RelMap hnOut ![x]) : cellRank (cellPt x) = varRank x := by
  rw [cellRank, varRank]
  symm
  refine Nat.card_eq_of_bijective
    (fun y => ⟨cellPt y.1, (lowerCell_iff hv x _).mpr
      ⟨y.1, rfl, y.2.1, y.2.2.1, (hB x y.1 hx y.2.1).mp y.2.2.2⟩⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (cellPt_injective (congrArg Subtype.val h))
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl, hy, hne, hle⟩ := (lowerCell_iff hv x q).mp hq
    exact ⟨⟨y, hy, hne, (hB x y hx hy).mpr hle⟩, rfl⟩

open Classical in
/-- **The machine writes the number written by unit propagation**, when the
order of the instance compares the output variables as `below` does. -/
theorem machineNumber_numTuringInterp
    (hB : VarOrder A → ∀ x y : A, RelMap hnOut ![x] → RelMap hnOut ![y] →
      (RelMap hnBelow ![y, x] ↔ y ≤ x)) :
    machineNumber (numTuringInterp.Map A) = hornNumber A := by
  have hag := agree_num (A := A)
  have hwd : (tmData (numTuringInterp.Map A)).WellFormed ∧
      (tmData (numTuringInterp.Map A)).Deterministic :=
    ⟨hag.wellFormed.mp hornMachine_wellFormed, hag.deterministic.mp hornMachine_deterministic⟩
  rw [machineNumber, hornNumber, ite_eq_left hwd]
  by_cases hs : HornSatisfiable A ∧ VarOrder A
  · rw [ite_eq_left hs]
    have hsupp : ∀ g ∈ Function.support
        (fun g : numTuringInterp.Map A => if OutDigit g then 2 ^ cellRank g else 0),
        g ∈ Set.univ ↔ g ∈ Set.range (cellPt (A := A)) := by
      intro g hg
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      have hd : OutDigit g := by
        by_contra h
        exact hg (ite_eq_right h)
      obtain ⟨x, hx, -⟩ := (outDigit_iff hs.1 hs.2 g).mp hd
      exact ⟨x, hx.symm⟩
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ hsupp,
      finsum_mem_range cellPt_injective]
    refine finsum_congr fun x => ?_
    have hdig : OutDigit (cellPt x) ↔ ForcedDigit x := by
      refine (outDigit_iff hs.1 hs.2 _).trans ⟨?_, fun h => ⟨x, rfl, h⟩⟩
      rintro ⟨y, hy, h⟩
      rwa [cellPt_injective hy]
    by_cases hx : RelMap hnOut ![x]
    · rw [cellRank_cellPt hs.2 (hB hs.2) hx]
      exact if_congr hdig rfl rfl
    · rw [ite_eq_right fun h => hx (hdig.mp h).1, ite_eq_right fun h => hx h.1]
  · rw [ite_eq_right hs]
    refine (finsum_congr fun g => ?_).trans finsum_zero
    exact ite_eq_right fun h => hs ⟨hornSatisfiable_of_outDigit h, varOrder_of_out h.1⟩

end Correct

/-- **The number written by unit propagation reduces to the number written by
a machine**: the instance reordered so that its output variables come first,
in the order of significance, then the unit-propagation machine with the
cells of the output variables as its output. -/
noncomputable def hornNumber_ordered_parsimonious_dtmNumber : HornNumber ≤ᵖ[≤] DTMNumber where
  Tag := UPTag × (Fin 3 → Unit)
  dim := 3 * 1
  toInterpretation := numTuringInterp.comp (FOInterpretation.reorder reordF)
  correct := fun B _ _ _ _ => by
    have e1 := numTuringInterp.compLEquiv (FOInterpretation.reorder reordF) B
    have e2 := FOInterpretation.reorderLEquiv reordF B (isLinOrd_newLe B) (realize_reordF (A := B))
    have e3 := @FOInterpretation.mapLEquiv _ _ _ _ _ numTuringInterp _ B _
      (letI := newOrder B; sumOrderStructure Language.satOut B) e2
    have key := @machineNumber_numTuringInterp B _ (newOrder B) _ _
      fun hv x y hx hy => (newLe_out hv hx hy).symm
    exact ((machineNumber_iso e1).trans ((@machineNumber_iso _ _ _
      (@FOInterpretation.mapStructure _ _ _ _ numTuringInterp B
        (letI := newOrder B; sumOrderStructure Language.satOut B) _) e3).trans key)).symm

end MachNum

end DescriptiveComplexity
