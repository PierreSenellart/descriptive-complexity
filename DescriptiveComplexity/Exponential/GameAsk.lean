/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameRun

/-!
# Asking a question of the machine

The bridge between `DescriptiveComplexity.GameProg` – the machine's two hooks
into the source structure – and the phases that use them. Everything before
this file is parametric in `concOk` and `isTarget`; here they are the ones a
program supplies, and the round becomes a statement about a *sentence*:

> `DescriptiveComplexity.GameProg.altWin_ask`: if the question holds of the two
> assignments the tape carries, the machine wins from the entry of its prefix.

## The three things the bridge has to say

* **A claim vector is a claim vector.** The phase carries `Fin M → Bool` and the
  question `Fin (natoms q) → Bool`; `DescriptiveComplexity.GameProg.claimsOf`
  extends one to the other and `claimsOf_apply` reads it back. Nothing is
  padded – the extension is junk above `natoms q`, which no rule looks at.
* **A correct claim is a hit.** The cell a challenge addresses is
  `cellPt a₀ rr i ā` with `i` the atom's relation variable, `ā` its arguments
  read at the valuation, and `rr` the region the atom's *copy* names – the
  current position sitting in region `r` and the candidate in the other, which
  is `DescriptiveComplexity.GameProg.cond_copy`. Its symbol carries the bit the
  tape gives it, and the claim being right says that bit *is* the claim.
* **The residue is the guard.** `concOk` at the concluding phase is literally
  `(data q).sub b` realized at the valuation the tuple carries, which is what
  `DescriptiveComplexity.QuestionData.MatrixHolds` supplies.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

namespace GameProg

variable {K : Language.{0, 0}} {B : SOBlock} {V M : ℕ} (prog : GameProg K B V M)
  {A : Type} [K.Structure A] [LinearOrder A] [Finite A]
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V} {ρ σ : B.Assignment A}

local notation "𝕄" => gameMachine prog.vars prog.pol a₀ hdim
  (gameRule prog.vars prog.natoms prog.concOk prog.isTarget)

/-! ### The claim vector -/

/-- **The claim vector a phase carries**, from the question's own: junk above
the question's atoms, which no rule ever looks at. -/
def claimsOf (q : GameQuestion) (b : Fin (prog.data q).natoms → Bool) : Fin M → Bool :=
  fun k => if h : (k : ℕ) < (prog.data q).natoms then b ⟨k, h⟩ else false

theorem claimsOf_apply (q : GameQuestion) (b : Fin (prog.data q).natoms → Bool)
    (j : Fin (prog.data q).natoms) :
    prog.claimsOf q b (Fin.castLE (prog.natoms_le q) j) = b j := by
  rw [claimsOf, dif_pos (show ((Fin.castLE (prog.natoms_le q) j : Fin M) : ℕ) <
    (prog.data q).natoms from j.isLt)]
  exact congrArg b (Fin.ext rfl)

/-! ### The region a copy names -/

variable {prog}

omit [LinearOrder A] [Finite A] in
/-- **The current position sits in region `r` and the candidate in the other
one**, so the copy an atom reads picks the region
`if copy then !r else r` – which is exactly the region
`DescriptiveComplexity.GameProg.isTarget` looks in. -/
theorem cond_copy (r copy : Bool) (ρ σ : B.Assignment A) :
    cond copy (cond (!r) σ ρ) (cond r σ ρ) = cond (if copy then !r else r) σ ρ := by
  cases copy <;> cases r <;> rfl

/-! ### A correct claim is a hit -/

omit [K.Structure A] [Finite A] in
/-- **The cell a challenge addresses carries the bit that was claimed**, when
the claim is right – so the seek finds it and the challenge is answered. -/
theorem seekHit_of_claim (h₀ : IsBot a₀) (q : GameQuestion) (r par : Bool)
    {b : Fin (prog.data q).natoms → Bool} {vv : Fin (gameDim B V) → A}
    (hb : ∀ j, b j = true ↔ ((prog.data q).atoms j).Holds (cond r σ ρ) (cond (!r) σ ρ)
      (prog.valOf q vv))
    (k : Fin (M + 1)) (hk : (k : ℕ) < prog.natoms q) :
    ∃ pos : GamePt B V M A, machPosn pos ∧ machDom (ctrlArity prog.vars) pos ∧
      SeekHit a₀ prog.isTarget (MachPh.seekPh q r (prog.claimsOf q b) k par) vv
        (tapeOfAssign a₀ hdim ρ σ) pos := by
  classical
  set atom := (prog.data q).atoms ⟨(k : ℕ), hk⟩ with hatom
  set rr : Bool := if atom.copy then !r else r with hrr
  set ā : Fin (B.arity atom.var) → A := fun l => prog.valOf q vv (atom.args l) with hā
  refine ⟨cellPt a₀ rr atom.var ā, machPosn_cellPt a₀ rr atom.var ā,
    machDom_cellPt a₀ h₀ rr atom.var ā, decide (cond rr σ ρ atom.var ā), rr, atom.var, ā, rfl,
    tapeOfAssign_cellPt a₀ hdim ρ σ rr atom.var ā, hk, ?_, ?_⟩
  · -- the symbol is the claimed one
    have hbit : decide (cond rr σ ρ atom.var ā) = b ⟨(k : ℕ), hk⟩ := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      refine Iff.trans ?_ (hb ⟨(k : ℕ), hk⟩).symm
      rw [BlockAtom.Holds, ← hatom, cond_copy]
    rw [hbit, ← prog.claimsOf_apply q b ⟨(k : ℕ), hk⟩]
    rfl
  · -- the address is the atom's arguments, read at the valuation
    have key : ∀ m : Fin (prog.data q).vars,
        walkTuple vv (pad a₀ ā) (Fin.castLE (prog.vars_le_gameDim q) m) = prog.valOf q vv m := by
      intro m
      rw [walkTuple, joinTuple_of_lt _ _ (lt_of_lt_of_le m.isLt (prog.vars_le q)), pref]
      exact congrArg vv (Fin.ext rfl)
    have hgoal : argsOf atom.var (addrOf (walkTuple (V := V) vv (pad a₀ ā))) =
        fun l => walkTuple vv (pad a₀ ā)
          (Fin.castLE (prog.vars_le_gameDim q) (atom.args l)) := by
      rw [addrOf_walkTuple, argsOf_pad]
      funext l
      exact (key (atom.args l)).symm
    exact hgoal

/-! ### The residue is the guard -/

omit [LinearOrder A] [Finite A] in
/-- **The concluding transition's guard is the residual formula**, read at the
valuation the tuple carries. -/
theorem concOk_of_sub (q : GameQuestion) (r par : Bool)
    {b : Fin (prog.data q).natoms → Bool} {vv : Fin (gameDim B V) → A}
    (hsub : ((prog.data q).sub b).Realize default (prog.valOf q vv)) :
    prog.concOk (MachPh.concPh q r (prog.claimsOf q b) par) vv := by
  have hfun : (fun j => prog.claimsOf q b (Fin.castLE (prog.natoms_le q) j)) = b :=
    funext (prog.claimsOf_apply q b)
  have hgoal : ((prog.data q).sub
      (fun j => prog.claimsOf q b (Fin.castLE (prog.natoms_le q) j))).Realize default
      (prog.valOf q vv) := by
    rw [hfun]
    exact hsub
  exact hgoal

/-! ### The round, and the question -/

/-- **The claim phase wins when the matrix holds.** The existential player
claims the vector the matrix supplies; each challenge is answered because the
claim is right, and the concluding transition is guarded by the residue. -/
theorem altWin_matrix (h₀ : IsBot a₀) (q : GameQuestion) {r par : Bool}
    {vv : Fin (gameDim B V) → A} {c : Config (GamePt B V M A)}
    (hmat : (prog.data q).MatrixHolds (cond r σ ρ) (cond (!r) σ ρ) (prog.valOf q vv))
    (h : CtrlCfg a₀ hdim prog.vars ρ σ (MachPh.claimPh q r par) vv c) :
    (𝕄).AltWin true c := by
  obtain ⟨b, hb, hsub⟩ := hmat
  exact altWin_claim h₀ rfl prog.vars_le (prog.claimsOf q b)
    (fun k hk => seekHit_of_claim h₀ q r (!par) hb k hk)
    (concOk_of_sub q r (!par) hsub) h

/-- **The machine wins from the entry of a question's prefix when the question
holds.** This is the whole of the second normal form on the machine side: the
prefix is played as moves, the matrix is claimed and challenged, and no
evaluator appears anywhere. -/
theorem altWin_ask (h₀ : IsBot a₀) (q : GameQuestion)
    {φ : ((K.sum B.lang).sum B.lang).Sentence} (hplays : (prog.data q).Plays φ)
    {r par : Bool} {jj : Fin (V + 1)} (hjj : (jj : ℕ) = 0)
    {vv : Fin (gameDim B V) → A} {c : Config (GamePt B V M A)}
    (hφ : @Sentence.Realize _ A (B.structure₂ (cond r σ ρ) (cond (!r) σ ρ)) φ)
    (h : CtrlCfg a₀ hdim prog.vars ρ σ (MachPh.prePh q r jj par) vv c) :
    (𝕄).AltWin true c := by
  let : Nonempty A := ⟨a₀⟩
  refine altWin_pre h₀ prog.vars_le
    (fun par' vv' c' hP h' => altWin_matrix h₀ q hP h') (prog.vars q) 0
    (le_of_eq (Nat.sub_zero _)) (Nat.zero_le _) par jj hjj vv c ?_ h
  exact (hplays A (cond r σ ρ) (cond (!r) σ ρ) (qval prog.vars_le q vv)).mp hφ

end GameProg

end DescriptiveComplexity
