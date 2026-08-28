/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.HeadBit
import DescriptiveComplexity.HeadEvalArith
import DescriptiveComplexity.LogTime.Simulate

/-!
# The bit-level logic is inside LOGSPACE

`DescriptiveComplexity.BitDefinable.mem_LOGSPACE`: every problem defined by a
prenex sentence over `≤`, `+` and the bit at an index – hence, by
`DescriptiveComplexity.ltDecidable_iff_bitDefinable`, every problem decided by an
alternating machine with a logarithmic clock – is decided by a deterministic
multi-head automaton, so it is in LOGSPACE.

This is the fence the index naming cost, restored **without** either half of
Immerman's mutual definability: nothing here goes through `FO(≤, +, ×)`, so this
route is independent of `DescriptiveComplexity.powArithDef`.

## Why it is short

The bit logic is *prenex*, so there is no formula induction to redo: the
evaluator is a recursion over `DescriptiveComplexity.BitKernel`, whose five
constructors become branches (`DescriptiveComplexity.HeadProgram.iteP`), and a
quantifier prefix, whose variables become sweeps
(`DescriptiveComplexity.HeadProgram.scanP` for a universal register, its negation
for an existential). The prefix peels its *innermost* variable first, which is
exactly how a sweep wraps a body, so the induction matches the semantics step for
step and the property a prefix decides depends on no head at all.

Only the atoms have content, and all of it is elsewhere: `≤` and an input
relation are quantifier-free guards, `+` is
`DescriptiveComplexity.HeadProgram.plusP`, and the bit is
`DescriptiveComplexity.HeadProgram.bitP` – the halving loop of
`DescriptiveComplexity.HeadBit`.

## The head budget

`2 * vars + 8`: two heads per quantified variable, the register itself and the
sweep's marker, then the eight the bit fragment needs (its five working heads
and the addition's three). Where an arithmetic evaluation pays seven scratch
heads (`DescriptiveComplexity.HeadProgram.ArithScratch`), a bit-level one pays
eight, and it never needs a multiplication.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace HeadProgram

variable {L : Language.{0, 0}} {K : ℕ}

/-! ### Negating a fragment -/

/-- **The negation of a fragment**: run it and swap the exits. -/
def notP (F : HeadProgram L K) : HeadProgram L K := iteP F (exitP false) (exitP true)

section Not

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]

omit [Finite A] in
theorem decides_notP {m : ℕ} {F : HeadProgram L K} {P : (Fin K → A) → Prop}
    (hF : F.Decides A m P) (hP : HeadLocal m P) :
    (notP F).Decides A m (fun x => ¬ P x) :=
  (decides_iteP hF (decides_exitP_false m) (decides_exitP_true m) hP
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)).congr fun x => by
      constructor
      · rintro (⟨-, hf⟩ | ⟨hn, -⟩)
        · exact hf.elim
        · exact hn
      · intro hn
        exact Or.inr ⟨hn, trivial⟩

omit [Finite A] in
theorem deterministic_notP {F : HeadProgram L K} (hF : F.Deterministic A) :
    (notP F).Deterministic A :=
  deterministic_iteP hF (deterministic_exitP _) (deterministic_exitP _)

end Not

/-! ### The scratch layout of a bit-level evaluation -/

/-- The eight heads a bit-level atom needs, pinned to the eight positions from
`S` on: the bit fragment's five working heads, then the addition's three. `S` is
the top of the quantifier region, so every level the evaluator reaches is at
most `S`. -/
structure BitScratch (y cnt cand w tmk a b mk : Fin K) (S : ℕ) : Prop where
  /-- The working value sits at `S`. -/
  hy : (y : ℕ) = S
  /-- The round counter sits at `S + 1`. -/
  hcnt : (cnt : ℕ) = S + 1
  /-- The scan's candidate sits at `S + 2`. -/
  hcand : (cand : ℕ) = S + 2
  /-- The candidate's successor sits at `S + 3`. -/
  hw : (w : ℕ) = S + 3
  /-- The scan's marker sits at `S + 4`. -/
  htmk : (tmk : ℕ) = S + 4
  /-- The addition's running head sits at `S + 5`. -/
  ha : (a : ℕ) = S + 5
  /-- The addition's counter sits at `S + 6`. -/
  hb : (b : ℕ) = S + 6
  /-- The addition's marker sits at `S + 7`. -/
  hmk : (mk : ℕ) = S + 7

namespace BitScratch

variable {y cnt cand w tmk a b mk : Fin K} {S d : ℕ}

/-- The layout gives the bit fragment the head discipline it asks for, at any
level the evaluator can reach. -/
theorem bitHeads (hs : BitScratch y cnt cand w tmk a b mk S) {ih xh : Fin K}
    (hih : (ih : ℕ) < d) (hxh : (xh : ℕ) < d) (hd : d ≤ S) :
    BitHeads ih xh y cnt cand w tmk a b mk d S (S + 5) where
  hih := hih
  hxh := hxh
  hpS := hd
  hy := hs.hy
  hcnt := hs.hcnt
  hcand := hs.hcand
  hw := hs.hw
  htmk := hs.htmk
  hm := rfl
  ha := hs.ha
  hb := hs.hb
  hmk := hs.hmk

/-- The layout gives an addition the head discipline it asks for. -/
theorem plusHeads (hs : BitScratch y cnt cand w tmk a b mk S) {i j k : Fin K}
    (hi : (i : ℕ) < d) (hj : (j : ℕ) < d) (hk : (k : ℕ) < d) (hd : d ≤ S) :
    PlusHeads i j k a b mk d where
  hi := hi
  hj := hj
  hk := hk
  ha := by have := hs.ha; omega
  hb := by have := hs.hb; omega
  hmk := by have := hs.hmk; omega
  hab := fun he => by have h1 := hs.ha; have h2 := hs.hb; rw [he] at h1; omega
  hamk := fun he => by have h1 := hs.ha; have h2 := hs.hmk; rw [he] at h1; omega
  hbmk := fun he => by have h1 := hs.hb; have h2 := hs.hmk; rw [he] at h1; omega

end BitScratch

/-! ### The atoms -/

/-- An input relation symbol, in the ordered expansion of its vocabulary. Named,
as every symbol of a sum vocabulary in this library is, so that `rw` matches
it. -/
abbrev inOrdSym {a : ℕ} (R : L.Relations a) : (L.sum Language.order).Relations a := Sum.inl R

/-- **A bit-level atom, as a program**: the order and an input relation are read
as guards, the addition and the bit are *computed*, by `plusP` and by the halving
loop `bitP`. -/
noncomputable def bitAtomP (y cnt cand w tmk a b mk : Fin K) {γ : Type} (hv : γ → Fin K) :
    BitAtom L γ → HeadProgram L K
  | .le u v => leafP (leF (hv u) (hv v)) ((BoundedFormula.IsAtomic.rel _ _).isQF)
  | .plus u v z => plusP (hv u) (hv v) (hv z) a b mk
  | .bit u v => bitP (hv u) (hv v) y cnt cand w tmk a b mk
  | .rel R args => leafP (Relations.formula (inOrdSym R) fun t => Term.var (hv (args t)))
      ((BoundedFormula.IsAtomic.rel _ _).isQF)

/-- The quantifier-free kernel, as a program: the Boolean structure becomes
branches. -/
noncomputable def bitKernelP (y cnt cand w tmk a b mk : Fin K) {γ : Type} (hv : γ → Fin K) :
    BitKernel L γ → HeadProgram L K
  | .atom at' => bitAtomP y cnt cand w tmk a b mk hv at'
  | .tt => exitP true
  | .not k => notP (bitKernelP y cnt cand w tmk a b mk hv k)
  | .and k k' => iteP (bitKernelP y cnt cand w tmk a b mk hv k)
      (bitKernelP y cnt cand w tmk a b mk hv k') (exitP false)
  | .or k k' => iteP (bitKernelP y cnt cand w tmk a b mk hv k) (exitP true)
      (bitKernelP y cnt cand w tmk a b mk hv k')

/-- **A quantified register, as a sweep**: universally the sweep itself, and
existentially its double negation. -/
noncomputable def quantP (pol : Bool) (h hm : Fin K) (F : HeadProgram L K) :
    HeadProgram L K :=
  if pol then notP (scanP h hm (notP F)) else scanP h hm F

/-- **The quantifier prefix, as nested sweeps**: the innermost variable wraps the
body first, which is how `DescriptiveComplexity.prefixHolds` peels it. Variable
`j` lives in head `sh (2 * j)`, its sweep's marker in `sh (2 * j + 1)`. -/
noncomputable def prefixP (sh : ℕ → Fin K) :
    ∀ (n : ℕ), (Fin n → Bool) → HeadProgram L K → HeadProgram L K
  | 0, _, F => F
  | n + 1, pol, F =>
      prefixP sh n (fun j => pol j.castSucc)
        (quantP (pol (Fin.last n)) (sh (2 * n)) (sh (2 * n + 1)) F)

/-! ### Correctness -/

section Eval

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {y cnt cand w tmk a b mk : Fin K} {S : ℕ}

omit [LinearOrder A] [Finite A] in
/-- A property read off a fixed tuple of heads only sees those heads. -/
theorem headLocal_of_heads {γ : Type} {d : ℕ} (hv : γ → Fin K) (hlow : ∀ v, (hv v : ℕ) < d)
    (R : (γ → A) → Prop) : HeadLocal d (fun x => R fun v => x (hv v)) := by
  intro x x' hxx
  change R (fun v => x (hv v)) ↔ R (fun v => x' (hv v))
  rw [funext fun v => hxx (hv v) (hlow v)]

/-- **An atom is decided**: as a guard where it is the order or an input
relation, by a fragment where it is the addition or the bit. -/
theorem decides_bitAtomP (hs : BitScratch y cnt cand w tmk a b mk S) (hSK : S + 8 ≤ K)
    {γ : Type} {d : ℕ} (hv : γ → Fin K) (hlow : ∀ v, (hv v : ℕ) < d) (hd : d ≤ S)
    (at' : BitAtom L γ) :
    (bitAtomP y cnt cand w tmk a b mk hv at').Decides A d
      (fun x => at'.Holds fun v => x (hv v)) := by
  cases at' with
  | le u v =>
    exact (decides_leafP (L := L) (K := K) (leF (hv u) (hv v))
      ((BoundedFormula.IsAtomic.rel _ _).isQF)).congr fun x => by
        simp only [realize_leF]
        exact Iff.rfl
  | plus u v z =>
    exact (decides_plusP (hs.plusHeads (hlow u) (hlow v) (hlow z) hd) (by omega)).congr
      fun x => Iff.rfl
  | bit u v =>
    exact (decides_bitP (hs.bitHeads (hlow u) (hlow v) hd) (by omega)).congr
      fun x => Iff.rfl
  | rel R args =>
    exact (decides_leafP (L := L) (K := K)
      (Relations.formula (inOrdSym R) fun t => Term.var (hv (args t)))
      ((BoundedFormula.IsAtomic.rel _ _).isQF)).congr fun x => Iff.rfl

/-- **A kernel is decided**, by recursion on its Boolean structure. -/
theorem decides_bitKernelP (hs : BitScratch y cnt cand w tmk a b mk S) (hSK : S + 8 ≤ K)
    {γ : Type} {d : ℕ} (hv : γ → Fin K) (hlow : ∀ v, (hv v : ℕ) < d) (hd : d ≤ S) :
    ∀ k : BitKernel L γ, (bitKernelP y cnt cand w tmk a b mk hv k).Decides A d
      (fun x => k.Holds fun v => x (hv v)) := by
  intro k
  induction k with
  | atom at' => exact decides_bitAtomP hs hSK hv hlow hd at'
  | tt => exact (decides_exitP_true d).congr fun x => Iff.rfl
  | not k ih =>
    exact (decides_notP ih (headLocal_of_heads hv hlow _)).congr fun x => Iff.rfl
  | and k k' ih ih' =>
    refine (decides_iteP ih ih' (decides_exitP_false d) (headLocal_of_heads hv hlow _)
      (headLocal_of_heads hv hlow _) (fun _ _ _ => Iff.rfl)).congr fun x => ?_
    constructor
    · rintro (⟨h1, h2⟩ | ⟨-, hf⟩)
      · exact ⟨h1, h2⟩
      · exact hf.elim
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
  | or k k' ih ih' =>
    refine (decides_iteP ih (decides_exitP_true d) ih' (headLocal_of_heads hv hlow _)
      (fun _ _ _ => Iff.rfl) (headLocal_of_heads hv hlow _)).congr fun x => ?_
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact Or.inl h1
      · exact Or.inr h2
    · rintro (h1 | h2)
      · exact Or.inl ⟨h1, trivial⟩
      · by_cases hk : k.Holds fun v => x (hv v)
        · exact Or.inl ⟨hk, trivial⟩
        · exact Or.inr ⟨hk, h2⟩

/-- **A quantified register is decided**: universally by the sweep, existentially
by its double negation. -/
theorem decides_quantP {pol : Bool} {h hm : Fin K} {lvl : ℕ} (hh : (h : ℕ) = lvl)
    (hhm : (hm : ℕ) = lvl + 1) {F : HeadProgram L K} {P : (Fin K → A) → Prop}
    (hF : F.Decides A (lvl + 2) P) (hP : HeadLocal (lvl + 1) P) :
    (quantP pol h hm F).Decides A lvl
      (fun x => if pol then ∃ v : A, P (Function.update x h v)
        else ∀ v : A, P (Function.update x h v)) := by
  classical
  have hPloc2 : HeadLocal (lvl + 2) P := hP.mono (by omega)
  cases pol with
  | false =>
    exact (decides_scanP hh hhm hF hP).congr fun x => by rw [if_neg (by simp)]
  | true =>
    have hnot : (notP F).Decides A (lvl + 2) (fun x => ¬ P x) := decides_notP hF hPloc2
    have hscan := decides_scanP hh hhm hnot (fun x x' hxx => not_congr (hP x x' hxx))
    have hloc : HeadLocal lvl (fun x => ∀ v : A, ¬ P (Function.update x h v)) := by
      intro x x' hxx
      refine forall_congr' fun v => not_congr (hP _ _ fun j hj => ?_)
      rcases eq_or_ne j h with rfl | hne
      · rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hxx j (by have : (j : ℕ) ≠ lvl := fun hc => hne (Fin.ext (by omega)); omega)
    refine (decides_notP hscan hloc).congr fun x => ?_
    rw [if_pos rfl]
    simp only [not_forall, not_not]

omit [LinearOrder A] [Finite A] in
/-- Reading a valuation off the registers, one variable per even head. -/
theorem snoc_update {n : ℕ} {sh : ℕ → Fin K} (hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i)
    (hK : 2 * n + 1 < K) (x : Fin K → A) (v : A) :
    (fun j : Fin (n + 1) => (Function.update x (sh (2 * n)) v) (sh (2 * (j : ℕ)))) =
      Fin.snoc (fun j : Fin n => x (sh (2 * (j : ℕ)))) v := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    simp only [Fin.val_last]
    rw [Function.update_self]
  | cast j =>
    rw [Fin.snoc_castSucc]
    have hne : sh (2 * (j.castSucc : ℕ)) ≠ sh (2 * n) := by
      intro he
      have h1 := hsh (2 * (j.castSucc : ℕ)) (by have := j.isLt; simp only [Fin.val_castSucc]; omega)
      have h2 := hsh (2 * n) (by omega)
      rw [he, h2] at h1
      have := j.isLt
      simp only [Fin.val_castSucc] at h1
      omega
    rw [Function.update_of_ne hne]
    simp only [Fin.val_castSucc]

/-- **The prefix is decided**: nested sweeps, one per variable, innermost first –
and what they decide depends on no head at all, the prefix binding every
variable. -/
theorem decides_prefixP {sh : ℕ → Fin K} (hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i) :
    ∀ (n : ℕ) (pol : Fin n → Bool) (F : HeadProgram L K) (R : (Fin n → A) → Prop),
      2 * n ≤ K → F.Decides A (2 * n) (fun x => R fun j : Fin n => x (sh (2 * (j : ℕ)))) →
        (prefixP sh n pol F).Decides A 0 (fun _ => prefixHolds n pol R) := by
  intro n
  induction n with
  | zero =>
    intro pol F R _ hF
    refine hF.congr fun x => ?_
    have : (fun j : Fin 0 => x (sh (2 * (j : ℕ)))) = Fin.elim0 := funext fun j => j.elim0
    rw [this]
    exact Iff.rfl
  | succ n ih =>
    intro pol F R hK hF
    have hK' : 2 * n + 1 < K := by omega
    have hlvl : ((sh (2 * n) : Fin K) : ℕ) = 2 * n := hsh _ (by omega)
    have hlvlm : ((sh (2 * n + 1) : Fin K) : ℕ) = 2 * n + 1 := hsh _ (by omega)
    have hloc : HeadLocal (2 * n + 1)
        (fun x => R fun j : Fin (n + 1) => x (sh (2 * (j : ℕ)))) := by
      refine headLocal_of_heads _ (fun j => ?_) R
      have := j.isLt
      have := hsh (2 * (j : ℕ)) (by omega)
      omega
    have hq := decides_quantP (pol := pol (Fin.last n)) hlvl hlvlm
      (by simpa [Nat.mul_succ] using hF) hloc
    refine ih (fun j => pol j.castSucc)
      (quantP (pol (Fin.last n)) (sh (2 * n)) (sh (2 * n + 1)) F)
      (fun v : Fin n → A => if pol (Fin.last n) then ∃ u : A, R (Fin.snoc v u)
        else ∀ u : A, R (Fin.snoc v u)) (by omega) (hq.congr fun x => ?_)
    simp only [snoc_update hsh hK']

end Eval

/-! ### Determinism -/

section Det

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A]
variable {y cnt cand w tmk a b mk : Fin K}

omit [Finite A] in
theorem deterministic_bitAtomP {γ : Type} (hv : γ → Fin K) (at' : BitAtom L γ) :
    (bitAtomP (L := L) y cnt cand w tmk a b mk hv at').Deterministic A := by
  cases at' with
  | le u v =>
    exact deterministic_leafP (leF (hv u) (hv v)) ((BoundedFormula.IsAtomic.rel _ _).isQF)
  | plus u v z => exact deterministic_plusP _ _ _ _ _ _
  | bit u v => exact deterministic_bitP _ _ _ _ _ _ _ _ _ _
  | rel R args =>
    exact deterministic_leafP (Relations.formula (inOrdSym R) fun t => Term.var (hv (args t)))
      ((BoundedFormula.IsAtomic.rel _ _).isQF)

omit [Finite A] in
theorem deterministic_bitKernelP {γ : Type} (hv : γ → Fin K) :
    ∀ k : BitKernel L γ,
      (bitKernelP (L := L) y cnt cand w tmk a b mk hv k).Deterministic A := by
  intro k
  induction k with
  | atom at' => exact deterministic_bitAtomP hv at'
  | tt => exact deterministic_exitP _
  | not k ih => exact deterministic_notP ih
  | and k k' ih ih' => exact deterministic_iteP ih ih' (deterministic_exitP _)
  | or k k' ih ih' => exact deterministic_iteP ih (deterministic_exitP _) ih'

omit [Finite A] in
theorem deterministic_quantP {pol : Bool} {h hm : Fin K} {F : HeadProgram L K}
    (hF : F.Deterministic A) : (quantP pol h hm F).Deterministic A := by
  cases pol with
  | false => exact deterministic_scanP hF
  | true => exact deterministic_notP (deterministic_scanP (deterministic_notP hF))

omit [Finite A] in
theorem deterministic_prefixP (sh : ℕ → Fin K) :
    ∀ (n : ℕ) (pol : Fin n → Bool) (F : HeadProgram L K), F.Deterministic A →
      (prefixP (L := L) sh n pol F).Deterministic A := by
  intro n
  induction n with
  | zero => intro pol F hF; exact hF
  | succ n ih => intro pol F hF; exact ih _ _ (deterministic_quantP hF)

end Det

end HeadProgram

/-! ### The inclusion -/

section Inclusion

open HeadProgram

variable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}

/-- **The bit-level logic is inside FO(DTC)**: a prenex sentence over `≤`, `+`
and the bit at an index is evaluated by a deterministic multi-head automaton –
the registers swept, the order and the input atoms read as guards, the addition
and the bit *computed* by `DescriptiveComplexity.HeadProgram.plusP` and
`DescriptiveComplexity.HeadProgram.bitP`.

The machine has `2 * vars + 8` heads: two per quantified register, then the
eight the bit fragment needs. -/
theorem BitDefinable.dtcDefinable (h : BitDefinable P) : DTCDefinable P := by
  classical
  obtain ⟨φ, hφ⟩ := h
  set n := φ.vars with hn
  set S := 2 * n with hSdef
  set K := S + 8 with hK
  set sh : ℕ → Fin K := fun i => if hi : i < K then ⟨i, hi⟩ else ⟨0, by omega⟩ with hsh0
  have hsh : ∀ i : ℕ, i < K → (sh i : ℕ) = i := by
    intro i hi
    rw [hsh0]
    simp only [dif_pos hi]
  set y : Fin K := ⟨S, by omega⟩ with hy
  set cnt : Fin K := ⟨S + 1, by omega⟩ with hcnt
  set cand : Fin K := ⟨S + 2, by omega⟩ with hcand
  set w : Fin K := ⟨S + 3, by omega⟩ with hw
  set tmk : Fin K := ⟨S + 4, by omega⟩ with htmk
  set a : Fin K := ⟨S + 5, by omega⟩ with ha
  set b : Fin K := ⟨S + 6, by omega⟩ with hb
  set mk : Fin K := ⟨S + 7, by omega⟩ with hmk
  have hs : BitScratch y cnt cand w tmk a b mk S :=
    { hy := rfl, hcnt := rfl, hcand := rfl, hw := rfl, htmk := rfl, ha := rfl, hb := rfl,
      hmk := rfl }
  set hv : Fin n → Fin K := fun j => sh (2 * (j : ℕ)) with hvdef
  have hlow : ∀ j : Fin n, ((hv j : Fin K) : ℕ) < S := by
    intro j
    have hj := j.isLt
    have hjv : (hv j : Fin K) = sh (2 * (j : ℕ)) := rfl
    rw [hjv, hsh (2 * (j : ℕ)) (by omega)]
    omega
  set body := bitKernelP y cnt cand w tmk a b mk hv φ.kernel with hbody
  set prog := prefixP sh n φ.pol body with hprog
  refine dtcDefinable_iff_automaton.mpr
    ⟨K, prog.compile true, isDeterministic_compile_true _, ?_⟩
  intro A _ _ _ _
  have hbodydec : body.Decides A S
      (fun x => φ.kernel.Holds fun v => x (hv v)) :=
    decides_bitKernelP hs (by omega) hv hlow le_rfl φ.kernel
  have hdec : prog.Decides A 0 (fun _ => prefixHolds n φ.pol
      fun v : Fin n → A => φ.kernel.Holds v) := by
    refine decides_prefixP hsh n φ.pol body _ (by omega) ?_
    exact hbodydec.congr fun x => Iff.rfl
  have hdet : prog.Deterministic A :=
    deterministic_prefixP sh n φ.pol body (deterministic_bitKernelP hv φ.kernel)
  rw [hφ A, accepts_compile_true _ hdet]
  have hholds : φ.Holds A = prefixHolds n φ.pol fun v : Fin n → A => φ.kernel.Holds v := rfl
  constructor
  · intro hsat
    obtain ⟨m0, hm0⟩ := exists_orank_eq (A := A) (m := 0) Nat.card_pos
    obtain ⟨z, -, hreach⟩ := hdec.complete (x := fun _ => m0) (b := true) (y := fun _ => m0)
      ⟨⟨fun _ => by rw [← hholds]; exact hsat, fun _ => rfl⟩, fun j hj => by omega⟩
    exact ⟨fun _ => m0, z, fun j e => isMin_of_orank_eq_zero hm0 e, hreach⟩
  · rintro ⟨x, z, -, hreach⟩
    rw [hholds]
    exact (hdec.sound hreach).1.mp rfl

/-- **The bit-level logic is inside LOGSPACE**, and with it the machine model of
`DescriptiveComplexity.LogTime`. No part of Immerman's mutual definability is
used: the route through AC⁰ (`DescriptiveComplexity.powArithDef`, then
`DescriptiveComplexity.ac0Definable_mem_LOGSPACE`) is a different one, and
longer. -/
theorem BitDefinable.mem_LOGSPACE (h : BitDefinable P) : P ∈ LOGSPACE :=
  (mem_LOGSPACE_iff P).mpr h.dtcDefinable

/-- **Constant-alternation logarithmic time is inside LOGSPACE**, through the
logic it is equal to. -/
theorem LTDecidable.mem_LOGSPACE (h : LTDecidable P) : P ∈ LOGSPACE :=
  (LTDecidable.bitDefinable h).mem_LOGSPACE

end Inclusion

end DescriptiveComplexity
