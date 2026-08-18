/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameExp
import DescriptiveComplexity.Exponential.GamePlayBack
import DescriptiveComplexity.Problems.MachineAltSpace.Membership

/-!
# The machine, written in first-order logic

`DescriptiveComplexity.Exponential.GameMachine` builds the machine of a
specification as an `DescriptiveComplexity.ATMData` on tagged tuples; this file
writes it *down*, as an `DescriptiveComplexity.FOInterpretation` of the
alternating-machine vocabulary in the ordered source vocabulary.

## Why the reduction is not relativized

One might expect the unused coordinates of a tagged tuple to be pinned by a
*domain formula*. The machine as built does not need that: its `Posn` is
`machPosn ∧ machDom`, so the junk tuples are already excluded by a **relation**
rather than by the universe, and every promise – the order is linear, the input
is functional, there is one blank – was proved on the *whole* tagged-tuple type.
So the interpretation is an ordinary one, and
`DescriptiveComplexity.OrderedFOReduction.toRel` widens it at the very end.

## What is static and what is not

A defining formula receives the **tags** of its arguments, so anything decided
by a tag is decided when the formula is built: that is `posn`, `acc`, `right`,
`blank`, `start`, the block marks, and the family of every transition rule. What
is left is small:

* the order, which is `DescriptiveComplexity.lexLeF`;
* `Canon` and `Agree` on the coordinates, which are
  `DescriptiveComplexity.canonF` and `DescriptiveComplexity.agreeF`;
* an address read off a transition's tuple, which is
  `DescriptiveComplexity.padTupF`;
* and the two hooks into the source structure, `concOk` and `isTarget`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace GameProg

/-! ### Side conditions decided by the tags -/

section Side

variable {L : Language.{0, 0}} {γ : Type}

open Classical in
/-- A condition decided when the formula is built. -/
noncomputable def sideF (γ : Type) (p : Prop) : (L.sum Language.order).Formula γ :=
  if p then ⊤ else ⊥

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

@[simp] theorem realize_sideF {p : Prop} : (sideF (L := L) γ p).Realize v ↔ p := by
  classical
  rw [sideF]
  by_cases h : p
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

end Side

/-! ### The formulas -/

section Formulas

variable {L : Language.{0, 0}} {B : SOBlock} {V M : ℕ}
  (prog : GameProg (L.sum Language.order) B V M)

/-- The coordinates of the `i`-th argument. -/
abbrev argVar (n : ℕ) (i : Fin n) : Fin (gameDim B V) → Fin n × Fin (gameDim B V) :=
  fun j => (i, j)

/-- **Being a position**: a tape tag whose coordinates beyond its own arity are
pinned. -/
noncomputable def posnF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (MachTag.IsPos t) ⊓
    canonF (MachTag.arity (ctrlArity prog.vars) t) (argVar 1 0)

/-- **Being an accepting state**: decided by the tag. -/
noncomputable def accF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (∃ ph : MachPh V M, t = Sum.inr (Sum.inl ph) ∧ ph.kind = .acc)

/-- **Moving the head right**: decided by the tag. -/
noncomputable def rightF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (∃ tr : TrTag B V M, t = Sum.inr (Sum.inr tr) ∧ tr.right = true)

/-- **Being the blank**: the left mark, at the constant tuple. -/
noncomputable def blankF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (t = Sum.inl (TapeTag.mark false)) ⊓ canonF 0 (argVar 1 0)

/-- **Being the start state**: the initial sweep, at the constant tuple. -/
noncomputable def startF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (t = Sum.inr (Sum.inl (startPh V M))) ⊓ canonF 0 (argVar 1 0)

/-- **The `i`-th block mark**: which player owns a state is a function of its
tag. -/
noncomputable def blkF (i : Fin 2) (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  sideF _ (((i : ℕ) = 1 ∧ ∃ ph : MachPh V M, t = Sum.inr (Sum.inl ph) ∧
      MachPh.IsUniv prog.pol ph = true) ∨
    ((i : ℕ) = 0 ∧ ¬ ∃ ph : MachPh V M, t = Sum.inr (Sum.inl ph) ∧
      MachPh.IsUniv prog.pol ph = true))

/-- **The state a transition applies in**: the tags name it, and the tuple must
agree with the transition's below the arity the phase declares. -/
noncomputable def tsrcF (t t' : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)) :=
  match t with
  | Sum.inr (Sum.inr tr) =>
      sideF _ (t' = Sum.inr (Sum.inl tr.src)) ⊓
        canonF (MachPh.arity prog.vars tr.src) (argVar 2 1) ⊓
        agreeF (MachPh.arity prog.vars tr.src) (argVar 2 0) (argVar 2 1)
  | _ => ⊥

/-- **The state a transition moves to**, the same with `dst`. -/
noncomputable def tdstF (t t' : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)) :=
  match t with
  | Sum.inr (Sum.inr tr) =>
      sideF _ (t' = Sum.inr (Sum.inl tr.dst)) ⊓
        canonF (MachPh.arity prog.vars tr.dst) (argVar 2 1) ⊓
        agreeF (MachPh.arity prog.vars tr.dst) (argVar 2 0) (argVar 2 1)
  | _ => ⊥

/-- The coordinates of a transition's tuple that hold the address of a cell of
the relation variable `i`. -/
noncomputable def addrIx (i : B.ι) : Fin (B.arity i) → Fin (gameDim B V) := fun l =>
  ⟨V + (l : ℕ), by
    have h1 := l.isLt
    have h2 := arity_le_blockArityBound B i
    simp only [gameDim]
    omega⟩

/-- The coordinates of a cell's own tuple that hold its address. -/
noncomputable def cellIx (i : B.ι) : Fin (B.arity i) → Fin (gameDim B V) :=
  Fin.castLE ((arity_le_blockArityBound B i).trans (blockArityBound_le_gameDim B V))

/-- **The symbol a transition reads**: a mark, or a cell's symbol at the address
the transition's own tuple carries. -/
noncomputable def treadF (t t' : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)) :=
  match t with
  | Sum.inr (Sum.inr tr) =>
      match tr.rd with
      | SymTag.mark b => sideF _ (t' = Sum.inl (TapeTag.mark b)) ⊓ canonF 0 (argVar 2 1)
      | SymTag.val b r i => sideF _ (t' = Sum.inl (TapeTag.val b r i)) ⊓
          padTupF (addrIx i) (argVar 2 0) (argVar 2 1)
  | _ => ⊥

/-- **The symbol a transition writes**, the same with `wr`. -/
noncomputable def twriteF (t t' : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)) :=
  match t with
  | Sum.inr (Sum.inr tr) =>
      match tr.wr with
      | SymTag.mark b => sideF _ (t' = Sum.inl (TapeTag.mark b)) ⊓ canonF 0 (argVar 2 1)
      | SymTag.val b r i => sideF _ (t' = Sum.inl (TapeTag.val b r i)) ⊓
          padTupF (addrIx i) (argVar 2 0) (argVar 2 1)
  | _ => ⊥

/-- **The initial contents of a cell**: every cell starts empty, carrying its
own address, and the sentinels carry their marks. -/
noncomputable def inpF (t t' : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)) :=
  match t with
  | Sum.inl (TapeTag.left _) =>
      sideF _ (t' = Sum.inl (TapeTag.mark false)) ⊓ canonF 0 (argVar 2 1)
  | Sum.inl TapeTag.right =>
      sideF _ (t' = Sum.inl (TapeTag.mark true)) ⊓ canonF 0 (argVar 2 1)
  | Sum.inl (TapeTag.cell r i) =>
      sideF _ (t' = Sum.inl (TapeTag.val false r i)) ⊓
        padTupF (cellIx i) (argVar 2 0) (argVar 2 1)
  | _ => ⊥

/-- Two families of coordinates of the same argument are equal, as a
formula. -/
def eqIxF {γ : Type} {m : ℕ} (f g : Fin m → Fin (gameDim B V))
    (u : Fin (gameDim B V) → γ) : (L.sum Language.order).Formula γ :=
  listInf ((List.finRange m).map fun l =>
    Term.equal (Term.var (u (f l))) (Term.var (u (g l))))

/-- **The guard of a concluding transition**: the residual formula of the
question, relabelled onto the coordinates the phase declares. This is the one
place a defining formula reads the *source structure*. -/
noncomputable def concOkF (p : MachPh V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  Formula.relabel
    (Sum.elim (fun e : Empty => e.elim)
      (fun l => ((0 : Fin 1), Fin.castLE (prog.vars_le_gameDim p.q) l)))
    ((prog.data p.q).sub fun j => p.claims (Fin.castLE (prog.natoms_le p.q) j)).toFormula

open Classical in
/-- **The test a seek makes**: the symbol is the one the challenged atom
addresses, and the address is the atom's arguments at the valuation. -/
noncomputable def isTargetF (p : MachPh V M) (s : SymTag B) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  if h : (p.k : ℕ) < (prog.data p.q).natoms then
    (if s = SymTag.val (p.claims (Fin.castLE (prog.natoms_le p.q) ⟨(p.k : ℕ), h⟩))
        (if ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).copy then !p.r else p.r)
        ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).var then
      eqIxF (addrIx ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).var)
        (fun l => Fin.castLE (prog.vars_le_gameDim p.q)
          (((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).args l)) (argVar 1 0)
    else ⊥)
  else ⊥

open Classical in
/-- **The nine rule families**, written down: seven of them are decided by the
transition's tag, and the two hooks into the source structure are the guard of
a concluding transition and the seek's test. -/
noncomputable def ruleF (tr : TrTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  (sideF _ (tr.rd = SymTag.mark false ∧ tr.wr = SymTag.mark false ∧
      tr.right = !tr.src.par ∧ MachPh.CtrlStep prog.vars prog.natoms tr.src tr.dst) ⊓
    (if tr.src.kind = PhKind.conc then concOkF prog tr.src else ⊤))
  ⊔ sideF _ (tr.src.kind = PhKind.sweep ∧ tr.dst = tr.src ∧ tr.rd = SymTag.mark false ∧
      tr.wr = SymTag.mark false ∧ tr.right = true)
  ⊔ sideF _ (tr.src.kind = PhKind.sweep ∧ tr.dst = tr.src ∧ tr.right = true ∧
      ∃ (b b' rr : Bool) (i : B.ι), tr.rd = SymTag.val b rr i ∧
        tr.wr = SymTag.val b' rr i ∧ (rr = tr.src.tgt ∨ b' = b))
  ⊔ sideF _ (tr.src.kind = PhKind.sweep ∧
      tr.dst = MachPh.rewindPh tr.src.r tr.src.tgt tr.src.cont false ∧
      tr.rd = SymTag.mark true ∧ tr.wr = SymTag.mark true ∧ tr.right = false)
  ⊔ sideF _ (tr.src.kind = PhKind.rewind ∧ tr.dst = tr.src ∧ tr.rd = tr.wr ∧
      tr.right = false ∧ ∃ (b rr : Bool) (i : B.ι), tr.rd = SymTag.val b rr i)
  ⊔ sideF _ (tr.src.kind = PhKind.rewind ∧ tr.dst = MachPh.rewindTarget tr.src ∧
      tr.rd = SymTag.mark false ∧ tr.wr = SymTag.mark false ∧ tr.right = false)
  ⊔ sideF _ (tr.src.kind = PhKind.seek ∧ tr.dst = tr.src ∧ tr.rd = SymTag.mark false ∧
      tr.wr = SymTag.mark false ∧ tr.right = true)
  ⊔ (sideF _ (tr.src.kind = PhKind.seek ∧ tr.dst = tr.src ∧ tr.rd = tr.wr ∧
        tr.right = true ∧ ∃ (b rr : Bool) (i : B.ι), tr.rd = SymTag.val b rr i) ⊓
      ∼(isTargetF prog tr.src tr.rd))
  ⊔ (sideF _ (tr.src.kind = PhKind.seek ∧ tr.dst = MachPh.accPh false ∧ tr.rd = tr.wr ∧
        tr.right = true) ⊓ isTargetF prog tr.src tr.rd)

/-- **Being a transition**: a transition tag whose rule fires. -/
noncomputable def trF (t : GameTag B V M) :
    (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V)) :=
  match t with
  | Sum.inr (Sum.inr tr) => ruleF prog tr
  | _ => ⊥

end Formulas

/-! ### Their realization -/

section Realize

variable {L : Language.{0, 0}} {B : SOBlock} {V M : ℕ}
  {prog : GameProg (L.sum Language.order) B V M}
  {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

@[simp] theorem realize_posnF {t : GameTag B V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (posnF prog t).Realize v ↔
      machPosn ((t, fun j => v (0, j)) : GamePt B V M A) ∧
        machDom (ctrlArity prog.vars) ((t, fun j => v (0, j)) : GamePt B V M A) := by
  rw [posnF]
  simp only [Formula.realize_inf, realize_sideF, realize_canonF]
  exact Iff.rfl

@[simp] theorem realize_accF {t : GameTag B V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (accF (L := L) (V := V) (M := M) t).Realize v ↔
      ∃ ph : MachPh V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inl ph) ∧
        ph.kind = .acc := by
  rw [accF, realize_sideF]

@[simp] theorem realize_rightF {t : GameTag B V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (rightF (L := L) (V := V) (M := M) t).Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        tr.right = true := by
  rw [rightF, realize_sideF]

theorem realize_blankF (h₀ : IsBot a₀) {t : GameTag B V M}
    {v : Fin 1 × Fin (gameDim B V) → A} :
    (blankF (L := L) (V := V) (M := M) t).Realize v ↔
      ((t, fun j => v (0, j)) : GamePt B V M A) = markPt a₀ false := by
  rw [blankF]
  simp only [Formula.realize_inf, realize_sideF, realize_canonF]
  constructor
  · rintro ⟨rfl, hc⟩
    exact Prod.ext rfl (funext fun j => le_antisymm (hc j (Nat.zero_le _) a₀) (h₀ _))
  · intro h
    refine ⟨congrArg Prod.fst h, fun j _ => ?_⟩
    have hj : v (0, j) = a₀ := congrFun (congrArg Prod.snd h) j
    change IsBot (v (0, j))
    rw [hj]
    exact h₀

theorem realize_startF (h₀ : IsBot a₀) {t : GameTag B V M}
    {v : Fin 1 × Fin (gameDim B V) → A} :
    (startF (L := L) (V := V) (M := M) t).Realize v ↔
      ((t, fun j => v (0, j)) : GamePt B V M A) = phasePt (startPh V M) (fun _ => a₀) := by
  rw [startF]
  simp only [Formula.realize_inf, realize_sideF, realize_canonF]
  constructor
  · rintro ⟨rfl, hc⟩
    exact Prod.ext rfl (funext fun j => le_antisymm (hc j (Nat.zero_le _) a₀) (h₀ _))
  · intro h
    refine ⟨congrArg Prod.fst h, fun j _ => ?_⟩
    have hj : v (0, j) = a₀ := congrFun (congrArg Prod.snd h) j
    change IsBot (v (0, j))
    rw [hj]
    exact h₀

@[simp] theorem realize_blkF {i : Fin 2} {t : GameTag B V M}
    {v : Fin 1 × Fin (gameDim B V) → A} :
    (blkF prog i t).Realize v ↔
      (((i : ℕ) = 1 ∧ isUnivPt prog.pol ((t, fun j => v (0, j)) : GamePt B V M A)) ∨
        ((i : ℕ) = 0 ∧ ¬ isUnivPt prog.pol ((t, fun j => v (0, j)) : GamePt B V M A))) := by
  rw [blkF, realize_sideF]
  have hiff : (∃ ph : MachPh V M, t = Sum.inr (Sum.inl ph) ∧
      MachPh.IsUniv prog.pol ph = true) ↔
      isUnivPt prog.pol ((t, fun j => v (0, j)) : GamePt B V M A) := by
    cases t with
    | inl s => exact ⟨fun ⟨_, hh, _⟩ => absurd hh (by simp), fun h => h.elim⟩
    | inr c =>
      cases c with
      | inl ph => exact ⟨fun ⟨_, hh, hu⟩ => (Sum.inl.inj (Sum.inr.inj hh)) ▸ hu,
          fun h => ⟨ph, rfl, h⟩⟩
      | inr tr => exact ⟨fun ⟨_, hh, _⟩ => absurd hh (by simp), fun h => h.elim⟩
  rw [hiff]

@[simp] theorem realize_tsrcF {t t' : GameTag B V M} {v : Fin 2 × Fin (gameDim B V) → A} :
    (tsrcF prog t t').Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        ((t', fun j => v (1, j)) : GamePt B V M A).1 = Sum.inr (Sum.inl tr.src) ∧
          Canon (MachPh.arity prog.vars tr.src) (fun j => v (1, j)) ∧
            Agree (MachPh.arity prog.vars tr.src) (fun j => v (0, j)) fun j => v (1, j) := by
  cases t with
  | inl s => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
  | inr c =>
    cases c with
    | inl ph => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
    | inr tr =>
      rw [tsrcF]
      simp only [Formula.realize_inf, realize_sideF, realize_canonF, realize_agreeF]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨tr, rfl, h1, h2, h3⟩,
        fun ⟨tr', h0, h1, h2, h3⟩ => by
          obtain rfl : tr' = tr := (Sum.inr.inj (Sum.inr.inj h0)).symm
          exact ⟨⟨h1, h2⟩, h3⟩⟩

@[simp] theorem realize_tdstF {t t' : GameTag B V M} {v : Fin 2 × Fin (gameDim B V) → A} :
    (tdstF prog t t').Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        ((t', fun j => v (1, j)) : GamePt B V M A).1 = Sum.inr (Sum.inl tr.dst) ∧
          Canon (MachPh.arity prog.vars tr.dst) (fun j => v (1, j)) ∧
            Agree (MachPh.arity prog.vars tr.dst) (fun j => v (0, j)) fun j => v (1, j) := by
  cases t with
  | inl s => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
  | inr c =>
    cases c with
    | inl ph => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
    | inr tr =>
      rw [tdstF]
      simp only [Formula.realize_inf, realize_sideF, realize_canonF, realize_agreeF]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨tr, rfl, h1, h2, h3⟩,
        fun ⟨tr', h0, h1, h2, h3⟩ => by
          obtain rfl : tr' = tr := (Sum.inr.inj (Sum.inr.inj h0)).symm
          exact ⟨⟨h1, h2⟩, h3⟩⟩

/-- **A tag and a constant tuple**: the shape every mark and every phase of the
game has. -/
theorem realize_constF (h₀ : IsBot a₀) {n : ℕ} {i : Fin n} {t' τ : GameTag B V M}
    {v : Fin n × Fin (gameDim B V) → A} :
    ((sideF (L := L) _ (t' = τ) ⊓ canonF 0 (argVar n i)).Realize v) ↔
      ((t', fun j => v (i, j)) : GamePt B V M A) = (τ, fun _ => a₀) := by
  simp only [Formula.realize_inf, realize_sideF, realize_canonF]
  constructor
  · rintro ⟨rfl, hc⟩
    exact Prod.ext rfl (funext fun j => le_antisymm (hc j (Nat.zero_le _) a₀) (h₀ _))
  · intro h
    refine ⟨congrArg Prod.fst h, fun j _ => ?_⟩
    have hj : v (i, j) = a₀ := congrFun (congrArg Prod.snd h) j
    change IsBot (v (i, j))
    rw [hj]
    exact h₀

/-- A tuple satisfies `DescriptiveComplexity.PadTup` exactly when it is the
padding it names. -/
theorem padTup_iff_eq_pad (h₀ : IsBot a₀) {m D : ℕ} (f : Fin m → Fin D)
    (u x : Fin D → A) : PadTup f u x ↔ x = pad a₀ fun l => u (f l) := by
  constructor
  · rintro ⟨hc, he⟩
    funext j
    by_cases hj : (j : ℕ) < m
    · rw [pad, dif_pos hj]
      exact he j hj
    · rw [pad, dif_neg hj]
      exact le_antisymm (hc j (by omega) a₀) (h₀ _)
  · rintro rfl
    exact padTup_pad h₀ f u

omit [LinearOrder A] in
/-- The address a symbol reads is the second half of a transition's tuple. -/
theorem argsOf_addrIx (i : B.ι) (w : Fin (gameDim B V) → A) :
    (fun l => w (addrIx i l)) = argsOf i (addrOf w) := by
  funext l
  rw [argsOf, addrOf]
  exact congrArg w (Fin.ext rfl)

omit [LinearOrder A] in
/-- And a cell's own address is the first half of its tuple. -/
theorem pref_cellIx (i : B.ι) (w : Fin (gameDim B V) → A) :
    (fun l => w (cellIx i l)) =
      pref ((arity_le_blockArityBound B i).trans (blockArityBound_le_gameDim B V)) w := rfl

theorem realize_symF (h₀ : IsBot a₀) {s : SymTag B} {t' : GameTag B V M}
    {v : Fin 2 × Fin (gameDim B V) → A} :
    ((match s with
      | SymTag.mark b => sideF (L := L) _ (t' = Sum.inl (TapeTag.mark b)) ⊓ canonF 0 (argVar 2 1)
      | SymTag.val b r i => sideF _ (t' = Sum.inl (TapeTag.val b r i)) ⊓
          padTupF (addrIx i) (argVar 2 0) (argVar 2 1) :
      (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V)))).Realize v ↔
      ((t', fun j => v (1, j)) : GamePt B V M A) =
        gameSymPt a₀ s (addrOf fun j => v (0, j)) := by
  cases s with
  | mark b =>
    simp only [Formula.realize_inf, realize_sideF, realize_canonF, gameSymPt_mark]
    constructor
    · rintro ⟨rfl, hc⟩
      exact Prod.ext rfl (funext fun j => le_antisymm (hc j (Nat.zero_le _) a₀) (h₀ _))
    · intro h
      refine ⟨congrArg Prod.fst h, fun j _ => ?_⟩
      have hj : v (1, j) = a₀ := congrFun (congrArg Prod.snd h) j
      change IsBot (v (1, j))
      rw [hj]
      exact h₀
  | val b r i =>
    simp only [Formula.realize_inf, realize_sideF, realize_padTupF, gameSymPt_val]
    have hargs : (fun l => v (argVar 2 0 (addrIx i l))) =
        argsOf i (addrOf fun j => v (0, j)) := argsOf_addrIx i (fun j => v (0, j))
    rw [padTup_iff_eq_pad h₀, hargs]
    constructor
    · rintro ⟨rfl, hp⟩
      exact Prod.ext rfl hp
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

@[simp] theorem realize_treadF {t t' : GameTag B V M} {v : Fin 2 × Fin (gameDim B V) → A}
    (h₀ : IsBot a₀) :
    (treadF (L := L) (V := V) (M := M) t t').Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        ((t', fun j => v (1, j)) : GamePt B V M A) =
          gameSymPt a₀ tr.rd (addrOf fun j => v (0, j)) := by
  cases t with
  | inl s => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
  | inr c =>
    cases c with
    | inl ph => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
    | inr tr =>
      rw [treadF, realize_symF h₀]
      exact ⟨fun h => ⟨tr, rfl, h⟩, fun ⟨tr', h0, h1⟩ => by
        obtain rfl : tr' = tr := (Sum.inr.inj (Sum.inr.inj h0)).symm
        exact h1⟩

@[simp] theorem realize_twriteF {t t' : GameTag B V M} {v : Fin 2 × Fin (gameDim B V) → A}
    (h₀ : IsBot a₀) :
    (twriteF (L := L) (V := V) (M := M) t t').Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        ((t', fun j => v (1, j)) : GamePt B V M A) =
          gameSymPt a₀ tr.wr (addrOf fun j => v (0, j)) := by
  cases t with
  | inl s => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
  | inr c =>
    cases c with
    | inl ph => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
    | inr tr =>
      rw [twriteF, realize_symF h₀]
      exact ⟨fun h => ⟨tr, rfl, h⟩, fun ⟨tr', h0, h1⟩ => by
        obtain rfl : tr' = tr := (Sum.inr.inj (Sum.inr.inj h0)).symm
        exact h1⟩

@[simp] theorem realize_inpF {t t' : GameTag B V M} {v : Fin 2 × Fin (gameDim B V) → A}
    (h₀ : IsBot a₀) (hdim : blockArityBound B ≤ gameDim B V) :
    (inpF (L := L) (V := V) (M := M) t t').Realize v ↔
      machInp a₀ hdim ((t, fun j => v (0, j)) : GamePt B V M A) (t', fun j => v (1, j)) := by
  classical
  cases t with
  | inr c => exact ⟨fun h => h.elim, fun h => h.1.elim⟩
  | inl s =>
    cases s with
    | val b r i => exact ⟨fun h => h.elim, fun h => h.1.elim⟩
    | mark b => exact ⟨fun h => h.elim, fun h => h.1.elim⟩
    | left b =>
      rw [inpF, realize_constF h₀, machInp]
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    | right =>
      rw [inpF, realize_constF h₀, machInp]
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    | cell r i =>
      rw [inpF, machInp]
      simp only [Formula.realize_inf, realize_sideF, realize_padTupF]
      have hpref : (fun l => v (argVar 2 0 (cellIx i l))) =
          pref ((arity_le_blockArityBound B i).trans (blockArityBound_le_gameDim B V))
            (fun j => v (0, j)) := pref_cellIx i (fun j => v (0, j))
      rw [padTup_iff_eq_pad h₀, hpref]
      have hinit : gameInitTape a₀ hdim
          ((Sum.inl (TapeTag.cell r i), fun j => v (0, j)) : GamePt B V M A) =
          valPt a₀ false r i (pref ((arity_le_blockArityBound B i).trans hdim)
            (fun j => v (0, j))) := by
        rw [gameInitTape, tapeOfAssign]
        simp [emptyAssign]
      rw [hinit]
      constructor
      · rintro ⟨rfl, hp⟩
        exact ⟨trivial, Prod.ext rfl hp⟩
      · rintro ⟨-, h⟩
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem realize_eqIxF {γ : Type} {m : ℕ} {f g : Fin m → Fin (gameDim B V)}
    {u : Fin (gameDim B V) → γ} {v : γ → A} :
    (eqIxF (L := L) f g u).Realize v ↔ (fun l => v (u (f l))) = fun l => v (u (g l)) := by
  rw [eqIxF, realize_listInf, funext_iff]
  constructor
  · intro h l
    have := h _ (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)
    rwa [Formula.realize_equal, Term.realize_var, Term.realize_var] at this
  · intro h ψ hψ
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var]
    exact h l

theorem realize_concOkF {p : MachPh V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (concOkF prog p).Realize v ↔ prog.concOk p (fun j => v (0, j)) := by
  rw [concOkF, Formula.realize_relabel, BoundedFormula.realize_toFormula, GameProg.concOk]
  exact iff_of_eq (congrArg
    (fun d : Empty → A => BoundedFormula.Realize
      ((prog.data p.q).sub fun j => p.claims (Fin.castLE (prog.natoms_le p.q) j)) d
      (prog.valOf p.q fun j => v (0, j))) (Subsingleton.elim _ _))

theorem realize_isTargetF {p : MachPh V M} {s : SymTag B}
    {v : Fin 1 × Fin (gameDim B V) → A} :
    (isTargetF prog p s).Realize v ↔ prog.isTarget p s (fun j => v (0, j)) := by
  classical
  rw [isTargetF, GameProg.isTarget]
  by_cases h : (p.k : ℕ) < (prog.data p.q).natoms
  · rw [dif_pos h]
    by_cases hs : s = SymTag.val (p.claims (Fin.castLE (prog.natoms_le p.q) ⟨(p.k : ℕ), h⟩))
        (if ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).copy then !p.r else p.r)
        ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).var
    · rw [if_pos hs, realize_eqIxF]
      have hargs : (fun l => v (argVar 1 0 (addrIx
          ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).var l))) =
          argsOf ((prog.data p.q).atoms ⟨(p.k : ℕ), h⟩).var (addrOf fun j => v (0, j)) :=
        argsOf_addrIx _ (fun j => v (0, j))
      rw [hargs]
      exact ⟨fun he => ⟨h, hs, he⟩, fun he => he.2.2⟩
    · rw [if_neg hs]
      simp only [Formula.realize_bot, false_iff]
      rintro ⟨h', hs', -⟩
      exact hs hs'
  · rw [dif_neg h]
    simp only [Formula.realize_bot, false_iff]
    rintro ⟨h', -, -⟩
    exact h h'

theorem realize_ruleF {tr : TrTag B V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (ruleF prog tr).Realize v ↔
      gameRule prog.vars prog.natoms prog.concOk prog.isTarget tr (fun j => v (0, j)) := by
  classical
  rw [ruleF, gameRule]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not, realize_sideF,
    realize_isTargetF]
  by_cases hc : tr.src.kind = PhKind.conc
  · rw [if_pos hc, realize_concOkF]
    constructor
    · rintro ((((((((⟨h1, h2⟩ | h) | h) | h) | h) | h) | h) | h) | h)
      · exact Or.inl ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, fun _ => h2⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2, h.2⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩)))))))
    · rintro (⟨h1, h2, h3, h4, h5⟩ | h | h | h | h | h | h | h | h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          ⟨⟨h1, h2, h3, h4⟩, h5 hc⟩)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩)
      · exact Or.inr ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩
  · rw [if_neg hc]
    simp only [Formula.realize_top, and_true]
    constructor
    · rintro ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
      · exact Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, fun hcc => absurd hcc hc⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2, h.2⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩)))))))
    · rintro (⟨h1, h2, h3, h4, -⟩ | h | h | h | h | h | h | h | h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          ⟨h1, h2, h3, h4⟩)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩)
      · exact Or.inr ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

@[simp] theorem realize_trF {t : GameTag B V M} {v : Fin 1 × Fin (gameDim B V) → A} :
    (trF prog t).Realize v ↔
      ∃ tr : TrTag B V M, ((t, fun j => v (0, j)) : GamePt B V M A).1 = Sum.inr (Sum.inr tr) ∧
        gameRule prog.vars prog.natoms prog.concOk prog.isTarget tr (fun j => v (0, j)) := by
  cases t with
  | inl s => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
  | inr c =>
    cases c with
    | inl ph => exact ⟨fun h => h.elim, fun ⟨_, hh, _⟩ => absurd hh (by simp)⟩
    | inr tr =>
      rw [trF, realize_ruleF]
      exact ⟨fun h => ⟨tr, rfl, h⟩, fun ⟨tr', h0, h1⟩ => by
        obtain rfl : tr' = tr := (Sum.inr.inj (Sum.inr.inj h0)).symm
        exact h1⟩

end Realize

/-! ### The interpretation, and the machines agree -/

section Interp

variable {L : Language.{0, 0}} {B : SOBlock} {V M : ℕ}
  (prog : GameProg (L.sum Language.order) B V M)

open Classical in
/-- **The machine of a program, written down**: an interpretation of the
alternating-machine vocabulary in the ordered source vocabulary, tagged by the
machine's own tags. -/
noncomputable def gameInterp :
    FOInterpretation (L.sum Language.order) (Language.turingAlt 2)
      (GameTag B V M) (gameDim B V) where
  relFormula {n} R :=
    match n, R with
    | _, .base .posn => fun t => posnF prog (t 0)
    | _, .base .tr => fun t => trF prog (t 0)
    | _, .base .start => fun t => startF (t 0)
    | _, .base .acc => fun t => accF (t 0)
    | _, .base .blank => fun t => blankF (t 0)
    | _, .base .right => fun t => rightF (t 0)
    | _, .base .le => fun t =>
        @lexLeF L (GameTag B V M) machTagOrder (gameDim B V) (t 0) (t 1)
    | _, .base .tsrc => fun t => tsrcF prog (t 0) (t 1)
    | _, .base .tread => fun t => treadF (t 0) (t 1)
    | _, .base .tdst => fun t => tdstF prog (t 0) (t 1)
    | _, .base .twrite => fun t => twriteF (t 0) (t 1)
    | _, .base .inp => fun t => inpF (t 0) (t 1)
    | _, .blk i => fun t => blkF prog i (t 0)

variable {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

/-- The interpreted universe is the machine's own, with nothing added. -/
def gameMapEquiv : GamePt B V M A ≃ (gameInterp prog).Map A := Equiv.refl _

omit [L.Structure A] [LinearOrder A] in
@[simp] theorem gameMapEquiv_apply (p : GamePt B V M A) : gameMapEquiv prog p = p := rfl

/-- The valuation a unary relation's argument supplies. -/
theorem relMap_one {R : (Language.turingAlt 2).Relations 1} {p : GamePt B V M A}
    {φ : GameTag B V M → (L.sum Language.order).Formula (Fin 1 × Fin (gameDim B V))}
    (hR : (gameInterp prog).relFormula R = fun t => φ (t 0)) :
    RelMap R ![gameMapEquiv prog p] ↔ (φ p.1).Realize fun q => p.2 q.2 := by
  rw [FOInterpretation.relMap_map, hR]
  simp only [Matrix.cons_val_fin_one]
  rfl

/-- The valuation a binary relation's arguments supply. -/
theorem relMap_two {R : (Language.turingAlt 2).Relations 2} {p q : GamePt B V M A}
    {φ : GameTag B V M → GameTag B V M →
      (L.sum Language.order).Formula (Fin 2 × Fin (gameDim B V))}
    (hR : (gameInterp prog).relFormula R = fun t => φ (t 0) (t 1)) :
    RelMap R ![gameMapEquiv prog p, gameMapEquiv prog q] ↔
      (φ p.1 q.1).Realize fun x => (if x.1 = 0 then p.2 else q.2) x.2 := by
  rw [FOInterpretation.relMap_map, hR]
  refine iff_of_eq (congrArg _ (funext fun x => ?_))
  obtain ⟨i, j⟩ := x
  fin_cases i <;> rfl

/-! ### The machines agree -/

variable {hdim : blockArityBound B ≤ gameDim B V}

theorem relMap_posn (p : GamePt B V M A) :
    ATMPosn (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Posn p := by
  rw [ATMPosn, relMap_one prog (φ := fun t => posnF prog t) rfl, realize_posnF]
  rfl

theorem relMap_tr (p : GamePt B V M A) :
    ATMTr (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Tr p := by
  rw [ATMTr, relMap_one prog (φ := fun t => trF prog t) rfl, realize_trF]
  rfl

theorem relMap_start (h₀ : IsBot a₀) (p : GamePt B V M A) :
    ATMStart (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Start p := by
  rw [ATMStart, relMap_one prog (φ := fun t => startF (L := L) (V := V) (M := M) t) rfl,
    realize_startF h₀]
  rfl

theorem relMap_acc (p : GamePt B V M A) :
    ATMAcc (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Acc p := by
  rw [ATMAcc, relMap_one prog (φ := fun t => accF (L := L) (V := V) (M := M) t) rfl,
    realize_accF]
  rfl

theorem relMap_blank (h₀ : IsBot a₀) (p : GamePt B V M A) :
    ATMBlank (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Blank p := by
  rw [ATMBlank, relMap_one prog (φ := fun t => blankF (L := L) (V := V) (M := M) t) rfl,
    realize_blankF h₀]
  rfl

theorem relMap_right (p : GamePt B V M A) :
    ATMRight (k := 2) (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Right p := by
  rw [ATMRight, relMap_one prog (φ := fun t => rightF (L := L) (V := V) (M := M) t) rfl,
    realize_rightF]
  rfl

theorem relMap_le (p q : GamePt B V M A) :
    ATMLe (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Le p q := by
  let := machTagOrder (B := B) (C := GameCtrlTag B V M)
  rw [ATMLe, relMap_two prog
      (φ := fun t t' => @lexLeF L (GameTag B V M) machTagOrder (gameDim B V) t t') rfl,
    realize_lexLeF (L := L) (A := A) (Tag := GameTag B V M) (d := gameDim B V)]
  rfl

theorem relMap_tsrc (p q : GamePt B V M A) :
    ATMSrc (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Src p q := by
  rw [ATMSrc, relMap_two prog (φ := fun t t' => tsrcF prog t t') rfl, realize_tsrcF]
  rfl

theorem relMap_tdst (p q : GamePt B V M A) :
    ATMDst (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Dst p q := by
  rw [ATMDst, relMap_two prog (φ := fun t t' => tdstF prog t t') rfl, realize_tdstF]
  rfl

theorem relMap_tread (h₀ : IsBot a₀) (p q : GamePt B V M A) :
    ATMRead (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Read p q := by
  rw [ATMRead, relMap_two prog (φ := fun t t' => treadF (L := L) (V := V) (M := M) t t') rfl,
    realize_treadF h₀]
  rfl

theorem relMap_twrite (h₀ : IsBot a₀) (p q : GamePt B V M A) :
    ATMWrite (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Write p q := by
  rw [ATMWrite, relMap_two prog (φ := fun t t' => twriteF (L := L) (V := V) (M := M) t t') rfl,
    realize_twriteF h₀]
  rfl

theorem relMap_inp (h₀ : IsBot a₀) (p q : GamePt B V M A) :
    ATMInp (k := 2) (gameMapEquiv prog p) (gameMapEquiv prog q) ↔
      (prog.machine a₀ hdim).Inp p q := by
  rw [ATMInp, relMap_two prog (φ := fun t t' => inpF (L := L) (V := V) (M := M) t t') rfl,
    realize_inpF h₀ hdim]
  rfl

theorem relMap_blk (j : ℕ) (p : GamePt B V M A) :
    ATMBlk (k := 2) j (gameMapEquiv prog p) ↔ (prog.machine a₀ hdim).Blk j p := by
  rw [GameProg.machine]
  constructor
  · rintro ⟨hj, hb⟩
    rw [relMap_one prog (φ := fun t => blkF prog ⟨j, hj⟩ t) rfl, realize_blkF] at hb
    exact hb
  · intro hb
    have hj : j < 2 := by rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    refine ⟨hj, ?_⟩
    rw [relMap_one prog (φ := fun t => blkF prog ⟨j, hj⟩ t) rfl, realize_blkF]
    exact hb

/-- **The interpreted structure describes the machine**: every field of
`DescriptiveComplexity.atmData` on it agrees, along the identity, with the
machine of the program. -/
theorem altAgree_gameMachine (h₀ : IsBot a₀) :
    ATMData.AltAgree (gameMapEquiv (A := A) prog) (prog.machine a₀ hdim)
      (atmData 2 ((gameInterp prog).Map A)) where
  base :=
    { posn := fun p => (relMap_posn prog p).symm
      le := fun p q => (relMap_le prog p q).symm
      tr := fun p => (relMap_tr prog p).symm
      start := fun p => (relMap_start prog h₀ p).symm
      acc := fun p => (relMap_acc prog p).symm
      blank := fun p => (relMap_blank prog h₀ p).symm
      right := fun p => (relMap_right prog p).symm
      src := fun p q => (relMap_tsrc prog p q).symm
      read := fun p q => (relMap_tread prog h₀ p q).symm
      dst := fun p q => (relMap_tdst prog p q).symm
      write := fun p q => (relMap_twrite prog h₀ p q).symm
      inp := fun p q => (relMap_inp prog h₀ p q).symm }
  blk := fun j p => (relMap_blk prog j p).symm

/-- The agreement in the other direction, along the same identity. -/
theorem altAgree_gameMachine' (h₀ : IsBot a₀) :
    ATMData.AltAgree (gameMapEquiv (A := A) prog).symm
      (atmData 2 ((gameInterp prog).Map A)) (prog.machine a₀ hdim) where
  base :=
    { posn := fun p => relMap_posn prog p
      le := fun p q => relMap_le prog p q
      tr := fun p => relMap_tr prog p
      start := fun p => relMap_start prog h₀ p
      acc := fun p => relMap_acc prog p
      blank := fun p => relMap_blank prog h₀ p
      right := fun p => relMap_right prog p
      src := fun p q => relMap_tsrc prog p q
      read := fun p q => relMap_tread prog h₀ p q
      dst := fun p q => relMap_tdst prog p q
      write := fun p q => relMap_twrite prog h₀ p q
      inp := fun p q => relMap_inp prog h₀ p q }
  blk := fun j p => relMap_blk prog j p

end Interp

/-! ### The instance, and the reduction -/

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {spec : SOGameSpec L} {V M : ℕ}
  (prog : GameProg (L.sum Language.order) spec.B V M)

omit [L.IsRelational] in
/-- **The interpreted structure is a yes-instance exactly when the game is
won.** The machine is well formed and its marks split its states by
construction, so the only content is the simulation
`DescriptiveComplexity.altAcceptsSpace_iff_accepts`, carried across the
identity by `DescriptiveComplexity.ATMData.AltAgree`. The bottom element the
machine is built over is the structure's own minimum, which exists because the
universe is finite and nonempty. -/
theorem atmAcceptSpace_map_iff (hplays : ∀ q, (prog.data q).Plays (spec.question q))
    (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    ATMAcceptSpace ((gameInterp prog).Map A) ↔ spec.Accepts A := by
  obtain ⟨a₀, h₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have hdim : blockArityBound spec.B ≤ gameDim spec.B V := blockArityBound_le_gameDim spec.B V
  have hag := altAgree_gameMachine (a₀ := a₀) (hdim := hdim) prog h₀
  have hag' := altAgree_gameMachine' (a₀ := a₀) (hdim := hdim) prog h₀
  rw [atmAcceptSpace_holds_iff]
  constructor
  · rintro ⟨-, -, hacc⟩
    exact (altAcceptsSpace_iff_accepts h₀ hplays).mp (hag'.altAcceptsSpace_mp true hacc)
  · intro h
    exact ⟨hag.base.wellFormed.mp (prog.machine_wellFormed a₀ hdim h₀),
      hag.blocksSplit_mp (prog.machine_blocksSplit a₀ hdim),
      hag.altAcceptsSpace_mp true ((altAcceptsSpace_iff_accepts h₀ hplays).mpr h)⟩

/-- **A second-order alternating game reduces to alternating acceptance in
bounded space**: the machine of the program, written down. -/
noncomputable def soGame_ordered_fo_reduction_atmAcceptSpace {P : DecisionProblem L}
    (hspec : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A)
    (hplays : ∀ q, (prog.data q).Plays (spec.question q)) :
    P ≤ᶠᵒ[≤] ATMAcceptSpace where
  Tag := GameTag spec.B V M
  dim := gameDim spec.B V
  toInterpretation := gameInterp prog
  correct := fun A _ _ _ _ => (hspec A).trans (atmAcceptSpace_map_iff prog hplays A).symm

end Reduction

end GameProg

/-! ### EXPTIME-hardness -/

/-- **Every SO-GAME definable problem reduces to alternating acceptance in
bounded space.** -/
theorem SOGameDefinable.ordered_fo_reduction_atmAcceptSpace {L : Language.{0, 0}}
    [L.IsRelational] {P : DecisionProblem L} (h : SOGameDefinable P) :
    Nonempty (P ≤ᶠᵒ[≤] ATMAcceptSpace) := by
  obtain ⟨spec, hspec⟩ := h
  obtain ⟨V, M, prog, hplays⟩ := exists_gameProg spec
  exact ⟨GameProg.soGame_ordered_fo_reduction_atmAcceptSpace prog (fun A => hspec A) hplays⟩

/-- **Alternating acceptance in bounded space is EXPTIME-hard.** Every SO(≤, LFP)
definable problem is a second-order alternating game
(`DescriptiveComplexity.SOLFPDefinable.soGameDefinable`), every such game has a
program (`DescriptiveComplexity.exists_gameProg`), and the machine of that
program is first-order definable in the instance. -/
theorem atmAcceptSpace_EXPTIME_hard : EXPTIME.Hard ATMAcceptSpace := by
  refine EXPTIME_hard_of_solfpDefinable _ fun {_} _ Q hQ => ?_
  exact (SOGameDefinable.ordered_fo_reduction_atmAcceptSpace
    (SOLFPDefinable.soGameDefinable hQ)).map OrderedFOReduction.toRel

/-- **Alternating acceptance in bounded space is EXPTIME-complete**, which is
Chandra, Kozen and Stockmeyer's `APSPACE = EXPTIME`: an alternating machine that
may use as much space as its input has positions decides exactly the problems
of deterministic exponential time. -/
theorem atmAcceptSpace_EXPTIME_complete : EXPTIME.Complete ATMAcceptSpace :=
  ⟨atmAcceptSpace_mem_EXPTIME, atmAcceptSpace_EXPTIME_hard⟩

end DescriptiveComplexity
