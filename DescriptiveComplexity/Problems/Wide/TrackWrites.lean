/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.NexOuter
import DescriptiveComplexity.Problems.Wide.NexSpec

/-!
# What a rule may not write

A forward run *constructs* the tape it walks: every lemma says the machine
reaches a configuration whose tape is a named function of a named tape state, so
nothing has to be said about what the rules leave alone. A **backward** reading
is handed an arbitrary run and has to recognise the tape, and there the missing
fact bites: a configuration's tape is of the form
`DescriptiveComplexity.Draw.DrawData.ixBack` of some tape state only because no
rule ever writes the slots the *channel* wrote – the register flag, the two ends,
the block one-hots, the name coordinates and the padding flag.

This file states that (`Rule.KeepsFile`) and proves it of the shapes a rule's
write can take: no write at all, an update of a slot that is not one of those,
and the guess's own write. With them the outer layer's rules keep the file, which
is what an opening's reading needs.
-/

namespace DescriptiveComplexity

/-! ### A run as a sequence -/

namespace TMData

section Seq

variable {V : Type} {M : TMData V}

open Classical in
/-- **A run of `n` steps is a sequence of `n + 1` configurations.** The
`StepsIn` form is an iterated existential, which is what a *forward* proof wants;
a backward reading has to speak of the configuration at each time, and that is
this. -/
theorem exists_seq_of_stepsIn : ∀ {n : ℕ} {c d : Config V}, M.StepsIn n c d →
    ∃ g : ℕ → Config V, g 0 = c ∧ (∀ i, n ≤ i → g i = d) ∧
      ∀ i, i < n → M.Step (g i) (g (i + 1)) := by
  intro n
  induction n with
  | zero =>
    intro c d h
    exact ⟨fun _ => c, rfl, (fun _ _ => (show c = d from h)),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    rintro c d ⟨e, he, hrest⟩
    obtain ⟨g, hg0, hgn, hgs⟩ := ih hrest
    refine ⟨fun i => if i = 0 then c else g (i - 1), rfl, ?_, ?_⟩
    · intro i hi
      change (if i = 0 then c else g (i - 1)) = d
      rw [if_neg (by omega)]
      exact hgn (i - 1) (by omega)
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · change M.Step (if (0 : ℕ) = 0 then c else g (0 - 1))
          (if (0 : ℕ) + 1 = 0 then c else g (0 + 1 - 1))
        rw [if_pos rfl, if_neg (by omega)]
        simpa [hg0] using he
      · change M.Step (if i = 0 then c else g (i - 1))
          (if i + 1 = 0 then c else g (i + 1 - 1))
        rw [if_neg (by omega), if_neg (by omega)]
        have h1 : i + 1 - 1 = (i - 1) + 1 := by omega
        rw [h1]
        exact hgs (i - 1) (by omega)

/-- **A stretch of a run, as reachability**: from any time to any later one, the
steps compose. This is how a backward reading passes the *rest* of the run – from
the entry it found to the accepting configuration – to
`DescriptiveComplexity.TMData.not_acc_of_reaches_dead_of_uniqueFrom`. -/
theorem reflTransGen_of_seq (g : ℕ → Config V) {n : ℕ}
    (hstep : ∀ i, i < n → M.Step (g i) (g (i + 1))) :
    ∀ {m : ℕ}, m ≤ n → Relation.ReflTransGen M.Step (g m) (g n) := by
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    rw [hm0]
  | succ k ih =>
    intro m hm
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact (ih (fun i hi => hstep i (by omega)) (by omega)).tail
        (hstep k (by omega))
    · have hmk : m = k + 1 := by omega
      rw [hmk]

end Seq

end TMData

namespace Draw

open FirstOrder

open Language Structure

/-! ### The slots the channel writes -/

section FileSlot

variable {ι : Type} {ko ki dd0 : ℕ}

/-- **A slot of the register file**: what the channel writes at time zero and no
rule may touch – the register flag, the file's two ends, the block one-hots, the
name coordinates and the padding flag. Everything else is a *track*: scratch the
program owns. -/
def Slot.IsFile : Slot ι ko ki dd0 → Prop
  | .reg => True
  | .regFirst => True
  | .regLast => True
  | .blk _ => True
  | .name _ => True
  | .pdd => True
  | _ => False

@[simp] theorem Slot.not_isFile_mir : ¬(Slot.mir : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_tgt : ¬(Slot.tgt : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_sav : ¬(Slot.sav : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_val : ¬(Slot.val : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_wk : ¬(Slot.wk : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_bot : ¬(Slot.bot : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_ltp : ¬(Slot.ltp : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_old (i : ι) :
    ¬(Slot.old i : Slot ι ko ki dd0).IsFile := id
@[simp] theorem Slot.not_isFile_new (i : ι) :
    ¬(Slot.new i : Slot ι ko ki dd0).IsFile := id

end FileSlot

/-! ### Rules that keep the file -/

section Keeps

variable {L : Language.{0, 0}} {dt : DrawData L} {A Q P : Type}

variable (dt) in
/-- **A rule keeps the file**: whatever it writes, the slots the channel wrote
come out unchanged. -/
def Rule.KeepsFile (ρ : Rule A Q dt.SlotIx P) : Prop :=
  ∀ (f : Q → A) (g : dt.SlotIx → A) (s : dt.SlotIx), s.IsFile → ρ.wr f g s = g s

theorem Rule.keepsFile_of_wr_eq {ρ : Rule A Q dt.SlotIx P}
    (h : ∀ f g, ρ.wr f g = g) : Rule.KeepsFile dt ρ :=
  fun f g s _ => congrFun (h f g) s

/-- An update of a slot that is not the file's keeps the file. -/
theorem keepsFile_update {ρ : Rule A Q dt.SlotIx P} {t : dt.SlotIx}
    (ht : ¬t.IsFile) (h : ∀ f g, ρ.wr f g = Function.update g t (ρ.wr f g t)) :
    Rule.KeepsFile dt ρ := by
  classical
  intro f g s hs
  have hne : s ≠ t := by
    rintro rfl
    exact ht hs
  rw [h f g, Function.update_of_ne hne]

variable (dt) in
/-- **A rule writes bits**: every slot it leaves is either untouched or one of
the two designated elements. This is what keeps a tape readable as an
`DescriptiveComplexity.Draw.DrawData.ixBack`, whose tracks are `bitVal`s. -/
def Rule.WritesBits (zero one : A) (ρ : Rule A Q dt.SlotIx P) : Prop :=
  ∀ (f : Q → A) (g : dt.SlotIx → A) (s : dt.SlotIx),
    ρ.wr f g s = g s ∨ ρ.wr f g s = zero ∨ ρ.wr f g s = one

variable (dt) in
/-- **A rule leaves the addressed tracks alone**: the mirror, the target, the
saved mirror and the valuation are read off the *file's* registers, so a tape
that carries them at an address which is nobody's register is not an
`ixBack` of anything. The opening never writes them. -/
def Rule.KeepsCellTracks (ρ : Rule A Q dt.SlotIx P) : Prop :=
  ∀ (f : Q → A) (g : dt.SlotIx → A) (s : dt.SlotIx),
    (s = Slot.mir ∨ s = Slot.tgt ∨ s = Slot.sav ∨ s = Slot.val) → ρ.wr f g s = g s

variable (dt) in
/-- **A rule leaves one slot alone.** The semantic half of a backward reading is
built from these: which slot each rule may touch, and hence what a track still
holds after a stretch of the run. -/
def Rule.KeepsSlot (t : dt.SlotIx) (ρ : Rule A Q dt.SlotIx P) : Prop :=
  ∀ (f : Q → A) (g : dt.SlotIx → A), ρ.wr f g t = g t

theorem Rule.keepsSlot_of_wr_eq {ρ : Rule A Q dt.SlotIx P} (t : dt.SlotIx)
    (h : ∀ f g, ρ.wr f g = g) : Rule.KeepsSlot dt t ρ :=
  fun f g => congrFun (h f g) t

variable (dt) in
/-- **A rule sets a slot**: whatever it reads, it leaves that slot holding the
designated one. The start step does this to the marker and the bottom mark. -/
def Rule.SetsSlot (one : A) (t : dt.SlotIx) (ρ : Rule A Q dt.SlotIx P) : Prop :=
  ∀ (f : Q → A) (g : dt.SlotIx → A), ρ.wr f g t = one

open Classical in
/-- **After a rule that sets a slot, that track marks the cell it was written
at** – provided it was clear before, which at the channel's tape it is
(`initBackReg_track_zero`). -/
theorem track_after_set {zero one : A} {t : dt.SlotIx}
    {ρ : Rule A Q dt.SlotIx P} (hset : Rule.SetsSlot dt one t ρ)
    {U : Type} {rest : U → dt.SlotIx → A} (hzero : ∀ r, rest r t = zero)
    (f : Q → A) (v : U) (s : U) :
    (if s = v then ρ.wr f (rest v) else rest s) t = bitVal zero one (s = v) := by
  classical
  by_cases hs : s = v
  · rw [if_pos hs, hset f (rest v), bitVal_pos hs]
  · rw [if_neg hs, hzero s, bitVal_neg hs]

end Keeps

/-! ### The shapes the outer layer writes with -/

section Outer

variable {L : Language.{0, 0}} {dt : DrawData L} {A Q B G : Type}
variable [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

omit [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] in
/-- **The guess keeps the file**: it writes the stage tracks and copies every
other slot, the file's included. -/
theorem guessWr_keepsFile (zero one : A) (x : dt.d.B.ι → Bool)
    (g : dt.SlotIx → A) (s : dt.SlotIx) (hs : s.IsFile) :
    dt.guessWr zero one x g s = g s := by
  match s with
  | .reg => rfl
  | .regFirst => rfl
  | .regLast => rfl
  | .blk c => rfl
  | .name j => rfl
  | .pdd => rfl
  | .mir => exact hs.elim
  | .tgt => exact hs.elim
  | .sav => exact hs.elim
  | .val => exact hs.elim
  | .wk => exact hs.elim
  | .bot => exact hs.elim
  | .ltp => exact hs.elim
  | .old i => exact hs.elim
  | .new i => exact hs.elim

omit [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] in
/-- **The sweep that lays nothing keeps the file**, having nothing to write. -/
theorem nullSpec_wr_keepsFile (b : B) (f : dt.CtlIx → A) (g : dt.SlotIx → A) :
    (dt.nullSpec (A := A) B).wr b f g = g := rfl

-- The two instances are used by the rule set's own `Function.update`s, which
-- the linter does not see through.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The outer layer keeps the file**: at every site but the evaluation's, the
handed program's rules either write nothing, or write the marker and the bottom
mark (the start step), or write the guess's stage tracks – and none of those is a
slot the channel wrote. The evaluation's own sites are the parameter `ruleE`, and
a backward *opening* reading never reaches them. -/
theorem nexRule_keepsFile_of_ne_eval {SE PE : Type} {ShE : SE → Type}
    (one : A) (zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i)
    (hi : ∀ e : SE, i ≠ NexSite.eval e) :
    Rule.KeepsFile dt (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ ruleE
      evalEntry bot i ρ) := by
  classical
  match i, ρ with
  | .start, _ =>
    intro f g s hs
    have h1 : s ≠ (Slot.bot : dt.SlotIx) := by rintro rfl; exact hs
    have h2 : s ≠ (Slot.wk : dt.SlotIx) := by rintro rfl; exact hs
    change Function.update (Function.update g Slot.wk one) Slot.bot one s = g s
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  | .approach, Sum.inl _ => exact fun _ _ _ _ => rfl
  | .approach, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .build, Sum.inl b => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inl b) => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inl b)) => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun _ _ _ _ => rfl
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun _ _ _ _ => rfl
  | .homeBuild, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .guess, Sum.inl ⟨b, x⟩ =>
    intro f g s hs
    change γ.wr b x f g s = g s
    rw [hγ b x]
    exact guessWr_keepsFile zero one x g s hs
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) =>
    intro f g s hs
    change γ.wr b x f g s = g s
    rw [hγ b x]
    exact guessWr_keepsFile zero one x g s hs
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
    intro f g s hs
    change γ.wr b x f g s = g s
    rw [hγ b x]
    exact guessWr_keepsFile zero one x g s hs
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact fun _ _ _ _ => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) => exact fun _ _ _ _ => rfl
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun _ _ _ _ => rfl
  | .homeGuess, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .accept, e => exact e.elim
  | .eval e, ρ' => exact absurd rfl (hi e)

omit [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] in
/-- The guess's write is a bit at the stage tracks and a copy everywhere else. -/
theorem guessWr_bits (one zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (b : Option dt.KIx) (x : dt.d.B.ι → Bool) (f : dt.CtlIx → A)
    (g : dt.SlotIx → A) (s : dt.SlotIx) :
    γ.wr b x f g s = g s ∨ γ.wr b x f g s = zero ∨ γ.wr b x f g s = one := by
  classical
  rw [hγ b x]
  match s with
  | .old i =>
    change bitVal zero one (x i = true) = _ ∨ _
    by_cases hx : x i = true
    · exact Or.inr (Or.inr (bitVal_pos hx))
    · exact Or.inr (Or.inl (bitVal_neg hx))
  | .reg => exact Or.inl rfl
  | .regFirst => exact Or.inl rfl
  | .regLast => exact Or.inl rfl
  | .blk c => exact Or.inl rfl
  | .name j => exact Or.inl rfl
  | .pdd => exact Or.inl rfl
  | .mir => exact Or.inl rfl
  | .tgt => exact Or.inl rfl
  | .sav => exact Or.inl rfl
  | .val => exact Or.inl rfl
  | .wk => exact Or.inl rfl
  | .bot => exact Or.inl rfl
  | .ltp => exact Or.inl rfl
  | .new i => exact Or.inl rfl

omit [Fintype Q] [Fintype dt.SlotIx] [DecidableEq dt.SlotIx] in
/-- The guess leaves the addressed tracks alone. -/
theorem guessWr_cellTracks (one zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (b : Option dt.KIx) (x : dt.d.B.ι → Bool) (f : dt.CtlIx → A)
    (g : dt.SlotIx → A) (s : dt.SlotIx)
    (hs : s = Slot.mir ∨ s = Slot.tgt ∨ s = Slot.sav ∨ s = Slot.val) :
    γ.wr b x f g s = g s := by
  rw [hγ b x]
  rcases hs with rfl | rfl | rfl | rfl <;> rfl

-- As above: the rule set's own updates are what the linter cannot see through.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The outer layer writes bits**: the start step writes `one`, the guess
writes a stage bit, and every other site of the opening writes nothing. -/
theorem nexRule_writesBits_of_ne_eval {SE PE : Type} {ShE : SE → Type}
    (one : A) (zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i)
    (hi : ∀ e : SE, i ≠ NexSite.eval e) :
    Rule.WritesBits dt zero one (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      ruleE evalEntry bot i ρ) := by
  classical
  match i, ρ with
  | .start, _ =>
    intro f g s
    change Function.update (Function.update g Slot.wk one) Slot.bot one s = g s ∨
      Function.update (Function.update g Slot.wk one) Slot.bot one s = zero ∨
      Function.update (Function.update g Slot.wk one) Slot.bot one s = one
    by_cases h1 : s = (Slot.bot : dt.SlotIx)
    · subst h1
      exact Or.inr (Or.inr (Function.update_self _ _ _))
    · rw [Function.update_of_ne h1]
      by_cases h2 : s = (Slot.wk : dt.SlotIx)
      · subst h2
        exact Or.inr (Or.inr (Function.update_self _ _ _))
      · rw [Function.update_of_ne h2]
        exact Or.inl rfl
  | .approach, Sum.inl _ => exact fun _ _ _ => Or.inl rfl
  | .approach, Sum.inr _ => exact fun _ _ _ => Or.inl rfl
  | .build, Sum.inl b => exact fun _ _ _ => Or.inl rfl
  | .build, Sum.inr (Sum.inl b) => exact fun _ _ _ => Or.inl rfl
  | .build, Sum.inr (Sum.inr (Sum.inl b)) => exact fun _ _ _ => Or.inl rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun _ _ _ => Or.inl rfl
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun _ _ _ => Or.inl rfl
  | .homeBuild, Sum.inr _ => exact fun _ _ _ => Or.inl rfl
  | .guess, Sum.inl ⟨b, x⟩ => exact guessWr_bits one zero γ hγ b x
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) => exact guessWr_bits one zero γ hγ b x
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) => exact guessWr_bits one zero γ hγ b x
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact fun _ _ _ => Or.inl rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) => exact fun _ _ _ => Or.inl rfl
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun _ _ _ => Or.inl rfl
  | .homeGuess, Sum.inr _ => exact fun _ _ _ => Or.inl rfl
  | .accept, e => exact e.elim
  | .eval e, ρ' => exact absurd rfl (hi e)

-- As above.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The outer layer leaves the addressed tracks alone**: the opening writes the
marker, the bottom mark and the stage tracks, never the mirror, the target, the
saved mirror or the valuation. -/
theorem nexRule_keepsCellTracks_of_ne_eval {SE PE : Type} {ShE : SE → Type}
    (one : A) (zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i)
    (hi : ∀ e : SE, i ≠ NexSite.eval e) :
    Rule.KeepsCellTracks dt (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      ruleE evalEntry bot i ρ) := by
  classical
  match i, ρ with
  | .start, _ =>
    intro f g s hs
    have h1 : s ≠ (Slot.bot : dt.SlotIx) := by
      rcases hs with rfl | rfl | rfl | rfl <;> exact fun hc => nomatch hc
    have h2 : s ≠ (Slot.wk : dt.SlotIx) := by
      rcases hs with rfl | rfl | rfl | rfl <;> exact fun hc => nomatch hc
    change Function.update (Function.update g Slot.wk one) Slot.bot one s = g s
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  | .approach, Sum.inl _ => exact fun _ _ _ _ => rfl
  | .approach, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .build, Sum.inl b => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inl b) => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inl b)) => exact fun _ _ _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun _ _ _ _ => rfl
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun _ _ _ _ => rfl
  | .homeBuild, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .guess, Sum.inl ⟨b, x⟩ => exact guessWr_cellTracks one zero γ hγ b x
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) => exact guessWr_cellTracks one zero γ hγ b x
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
    exact guessWr_cellTracks one zero γ hγ b x
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact fun _ _ _ _ => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) => exact fun _ _ _ _ => rfl
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun _ _ _ _ => rfl
  | .homeGuess, Sum.inr _ => exact fun _ _ _ _ => rfl
  | .accept, e => exact e.elim
  | .eval e, ρ' => exact absurd rfl (hi e)

-- As above.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Only the start step writes the marker and the bottom mark**: every other
site of the opening leaves both alone, so after the first step the working track
marks the address the head started on and nothing else. -/
theorem nexRule_keepsSlot_wk_bot {SE PE : Type} {ShE : SE → Type}
    (one : A) (zero : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (hγ : ∀ (b : Option dt.KIx) (x : dt.d.B.ι → Bool),
      γ.wr b x = fun (_ : dt.CtlIx → A) g => dt.guessWr zero one x g)
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i)
    (hi : ∀ e : SE, i ≠ NexSite.eval e) (hstart : i ≠ NexSite.start)
    (t : dt.SlotIx) (ht : t = Slot.wk ∨ t = Slot.bot) :
    Rule.KeepsSlot dt t (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      ruleE evalEntry bot i ρ) := by
  classical
  match i, ρ with
  | .start, _ => exact absurd rfl hstart
  | .approach, Sum.inl _ => exact fun _ _ => rfl
  | .approach, Sum.inr _ => exact fun _ _ => rfl
  | .build, Sum.inl b => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inl b) => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inl b)) => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun _ _ => rfl
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun _ _ => rfl
  | .homeBuild, Sum.inr _ => exact fun _ _ => rfl
  | .guess, Sum.inl ⟨b, x⟩ =>
    intro f g
    change γ.wr b x f g t = g t
    rw [hγ b x]
    rcases ht with rfl | rfl <;> rfl
  | .guess, Sum.inr (Sum.inl ⟨b, x⟩) =>
    intro f g
    change γ.wr b x f g t = g t
    rw [hγ b x]
    rcases ht with rfl | rfl <;> rfl
  | .guess, Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
    intro f g
    change γ.wr b x f g t = g t
    rw [hγ b x]
    rcases ht with rfl | rfl <;> rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact fun _ _ => rfl
  | .guess, Sum.inr (Sum.inr (Sum.inr (Sum.inr b))) => exact fun _ _ => rfl
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun _ _ => rfl
  | .homeGuess, Sum.inr _ => exact fun _ _ => rfl
  | .accept, e => exact e.elim
  | .eval e, ρ' => exact absurd rfl (hi e)

-- As above.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Only the guess writes the stage tracks**: every other site of the opening
leaves them alone, so what the evaluation reads there is what the guess wrote. -/
theorem nexRule_keepsSlot_old {SE PE : Type} {ShE : SE → Type}
    (one : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (i : NexSite SE) (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE i)
    (hi : ∀ e : SE, i ≠ NexSite.eval e) (hguess : i ≠ NexSite.guess)
    (iv : dt.d.B.ι) :
    Rule.KeepsSlot dt (Slot.old iv) (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      ruleE evalEntry bot i ρ) := by
  classical
  match i, ρ with
  | .start, _ =>
    intro f g
    change Function.update (Function.update g Slot.wk one) Slot.bot one (Slot.old iv) =
      g (Slot.old iv)
    rw [Function.update_of_ne (by rintro hc; exact nomatch hc),
      Function.update_of_ne (by rintro hc; exact nomatch hc)]
  | .approach, Sum.inl _ => exact fun _ _ => rfl
  | .approach, Sum.inr _ => exact fun _ _ => rfl
  | .build, Sum.inl b => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inl b) => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inl b)) => exact fun _ _ => rfl
  | .build, Sum.inr (Sum.inr (Sum.inr _)) => exact fun _ _ => rfl
  | .homeBuild, Sum.inl ρ' => cases ρ'; exact fun _ _ => rfl
  | .homeBuild, Sum.inr _ => exact fun _ _ => rfl
  | .guess, _ => exact absurd rfl hguess
  | .homeGuess, Sum.inl ρ' => cases ρ'; exact fun _ _ => rfl
  | .homeGuess, Sum.inr _ => exact fun _ _ => rfl
  | .accept, e => exact e.elim
  | .eval e, ρ' => exact absurd rfl (hi e)

-- As above.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **The start step sets the marker and the bottom mark.** -/
theorem nexRule_setsSlot_start {SE PE : Type} {ShE : SE → Type}
    (one : A)
    (γ : GuessSpec A dt.CtlIx dt.SlotIx (Option dt.KIx) (dt.d.B.ι → Bool))
    (ruleE : ∀ e : SE, ShE e → Rule A dt.CtlIx dt.SlotIx (NexPh (Option dt.KIx) PE))
    (evalEntry : PE) (bot : Option dt.KIx)
    (ρ : NexSh SE (Option dt.KIx) (dt.d.B.ι → Bool) ShE NexSite.start)
    (t : dt.SlotIx) (ht : t = Slot.wk ∨ t = Slot.bot) :
    Rule.SetsSlot dt one t (dt.nexRule one (dt.nullSpec (Option dt.KIx)) γ
      ruleE evalEntry bot NexSite.start ρ) := by
  classical
  intro f g
  change Function.update (Function.update g Slot.wk one) Slot.bot one t = one
  rcases ht with rfl | rfl
  · rw [Function.update_of_ne (by rintro hc; exact nomatch hc), Function.update_self]
  · rw [Function.update_self]

end Outer

/-! ### Reading a tape back as a tape state -/

namespace DrawData

section Recognise

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' P' I : Type}
variable [Fintype dt.SlotIx]

omit [Fintype dt.SlotIx] in
open Classical in
/-- **A tape of the right shape is an `ixBack`**: the file's slots as the layout
has them, the four addressed tracks clear, every other track a bit – and the tape
state is read off the tape, bit by bit. This is what turns a *recognised* tape
into the object every run lemma is stated against. -/
theorem exists_ixBack_of_shape (lay : Layout dt A R' P' I) {zero one : A}
    (hzo : zero ≠ one)
    (rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A)
    (st₀ : TapeSt dt A R' P' I)
    (hfile : ∀ r s, Slot.IsFile s →
      rest r s = dt.ixBack lay zero one dt.dd0Le st₀ r s)
    (hcell : ∀ r s, (s = Slot.mir ∨ s = Slot.tgt ∨ s = Slot.sav ∨ s = Slot.val) →
      rest r s = zero)
    (hbits : ∀ r s, ¬Slot.IsFile s → rest r s = zero ∨ rest r s = one) :
    ∃ st : TapeSt dt A R' P' I, rest = dt.ixBack lay zero one dt.dd0Le st ∧
      st.mir = (fun _ => False) ∧ st.tgt = (fun _ => False) ∧
      st.sav = (fun _ => False) ∧ st.val = (fun _ => False) := by
  classical
  refine ⟨{ mir := fun _ => False
            tgt := fun _ => False
            sav := fun _ => False
            val := fun _ => False
            old := fun i r => rest r (Slot.old i) = one
            new := fun i r => rest r (Slot.new i) = one
            wk := fun r => rest r Slot.wk = one
            bot := fun r => rest r Slot.bot = one
            ltp := fun r => rest r Slot.ltp = one }, ?_, rfl, rfl, rfl, rfl⟩
  funext r s
  have hbit : ∀ t : dt.SlotIx, ¬Slot.IsFile t →
      bitVal zero one (rest r t = one) = rest r t := by
    intro t ht
    rcases hbits r t ht with h | h
    · rw [h]
      exact bitVal_neg (fun hc => hzo hc)
    · rw [h]
      exact bitVal_pos rfl
  have hnone : ∀ t : dt.SlotIx,
      (t = Slot.mir ∨ t = Slot.tgt ∨ t = Slot.sav ∨ t = Slot.val) →
      bitVal zero one (bitAtOf lay.cell (fun _ : I => False) r) = rest r t := by
    intro t ht
    rw [bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc), hcell r t ht]
  match s with
  | .reg => exact (hfile r Slot.reg trivial).symm ▸ rfl
  | .regFirst => exact (hfile r Slot.regFirst trivial).symm ▸ rfl
  | .regLast => exact (hfile r Slot.regLast trivial).symm ▸ rfl
  | .blk b => exact (hfile r (Slot.blk b) trivial).symm ▸ rfl
  | .name j => exact (hfile r (Slot.name j) trivial).symm ▸ rfl
  | .pdd => exact (hfile r Slot.pdd trivial).symm ▸ rfl
  | .mir => exact (hnone Slot.mir (Or.inl rfl)).symm
  | .tgt => exact (hnone Slot.tgt (Or.inr (Or.inl rfl))).symm
  | .sav => exact (hnone Slot.sav (Or.inr (Or.inr (Or.inl rfl)))).symm
  | .val => exact (hnone Slot.val (Or.inr (Or.inr (Or.inr rfl)))).symm
  | .wk => exact (hbit Slot.wk (fun hc => hc)).symm
  | .bot => exact (hbit Slot.bot (fun hc => hc)).symm
  | .ltp => exact (hbit Slot.ltp (fun hc => hc)).symm
  | .old i => exact (hbit (Slot.old i) (fun hc => hc)).symm
  | .new i => exact (hbit (Slot.new i) (fun hc => hc)).symm

/-- **A tape the reading recognises**: every cell carries a slot vector, the
file's slots are the layout's, the four addressed tracks are clear, and every
other track is a bit. -/
structure TapeShape (lay : Layout dt A R' P' I) (zero one : A)
    (st₀ : TapeSt dt A R' P' I)
    (rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A) : Prop where
  /-- The file's slots are the layout's. -/
  file : ∀ r s, Slot.IsFile s → rest r s = dt.ixBack lay zero one dt.dd0Le st₀ r s
  /-- The four tracks read at a register are clear. -/
  cells : ∀ r s, (s = Slot.mir ∨ s = Slot.tgt ∨ s = Slot.sav ∨ s = Slot.val) →
    rest r s = zero
  /-- Every other track is a bit. -/
  bits : ∀ r s, ¬Slot.IsFile s → rest r s = zero ∨ rest r s = one

omit [Fintype dt.SlotIx] in
open Classical in
/-- **A rule that keeps the file, keeps the addressed tracks and writes bits
keeps the shape.** This is the step of the opening's reading: the cell under the
head is the only one that changes, and the three facts say the change stays
inside the shape. -/
theorem tapeShape_update {lay : Layout dt A R' P' I} {zero one : A}
    {st₀ : TapeSt dt A R' P' I}
    {rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (hshape : TapeShape (dt := dt) lay zero one st₀ rest)
    {Ph : Type} {ρ : Rule A dt.CtlIx dt.SlotIx Ph} (hfile : Rule.KeepsFile dt ρ)
    (hcell : Rule.KeepsCellTracks dt ρ) (hbits : Rule.WritesBits dt zero one ρ)
    (f : dt.CtlIx → A) (v : Univ A R' P' dt.KIx dt.dd → Prop) :
    TapeShape (dt := dt) lay zero one st₀
      (fun s => if s = v then ρ.wr f (rest v) else rest s) where
  file r s hs := by
    by_cases hr : r = v
    · subst hr
      rw [if_pos rfl, hfile f (rest r) s hs]
      exact hshape.file r s hs
    · rw [if_neg hr]
      exact hshape.file r s hs
  cells r s hs := by
    by_cases hr : r = v
    · subst hr
      rw [if_pos rfl, hcell f (rest r) s hs]
      exact hshape.cells r s hs
    · rw [if_neg hr]
      exact hshape.cells r s hs
  bits r s hs := by
    by_cases hr : r = v
    · subst hr
      rw [if_pos rfl]
      rcases hbits f (rest r) s with h | h | h
      · rw [h]
        exact hshape.bits r s hs
      · exact Or.inl h
      · exact Or.inr h
    · rw [if_neg hr]
      exact hshape.bits r s hs

omit [Fintype dt.SlotIx] in
/-- **The marker track, read back.** -/
theorem ixBack_wk_inv (lay : Layout dt A R' P' I) {zero one : A} (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) {P : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop}
    (hread : ∀ r, dt.ixBack lay zero one dt.dd0Le st r Slot.wk = bitVal zero one (P r)) :
    st.wk = P := by
  funext r
  refine propext ?_
  have h : bitVal zero one (st.wk r) = bitVal zero one (P r) := hread r
  constructor
  · intro hq
    by_contra hp
    rw [bitVal_pos hq, bitVal_neg hp] at h
    exact hzo h.symm
  · intro hp
    by_contra hq
    rw [bitVal_neg hq, bitVal_pos hp] at h
    exact hzo h

omit [Fintype dt.SlotIx] in
/-- **The bottom mark, read back.** -/
theorem ixBack_bot_inv (lay : Layout dt A R' P' I) {zero one : A} (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) {P : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop}
    (hread : ∀ r, dt.ixBack lay zero one dt.dd0Le st r Slot.bot = bitVal zero one (P r)) :
    st.bot = P := by
  funext r
  refine propext ?_
  have h : bitVal zero one (st.bot r) = bitVal zero one (P r) := hread r
  constructor
  · intro hq
    by_contra hp
    rw [bitVal_pos hq, bitVal_neg hp] at h
    exact hzo h.symm
  · intro hp
    by_contra hq
    rw [bitVal_neg hq, bitVal_pos hp] at h
    exact hzo h

omit [Fintype dt.SlotIx] in
/-- **The stage tracks, read back.** -/
theorem ixBack_old_inv (lay : Layout dt A R' P' I) {zero one : A} (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) (i : dt.d.B.ι)
    {P : (Univ A R' P' dt.KIx dt.dd → Prop) → Prop}
    (hread : ∀ r, dt.ixBack lay zero one dt.dd0Le st r (Slot.old i) =
      bitVal zero one (P r)) :
    st.old i = P := by
  funext r
  refine propext ?_
  have h : bitVal zero one (st.old i r) = bitVal zero one (P r) := hread r
  constructor
  · intro hq
    by_contra hp
    rw [bitVal_pos hq, bitVal_neg hp] at h
    exact hzo h.symm
  · intro hp
    by_contra hq
    rw [bitVal_neg hq, bitVal_pos hp] at h
    exact hzo h

omit [Fintype dt.SlotIx] in
/-- **A track read at a register, read back**: clear everywhere means clear at
every register, which is what an entry state's mirror, target, saved mirror and
valuation say. -/
theorem ixBack_cell_inv (lay : Layout dt A R' P' I) {zero one : A} (hzo : zero ≠ one)
    (st : TapeSt dt A R' P' I) {m : I → Prop}
    (hslot : ∀ r, dt.ixBack lay zero one dt.dd0Le st r Slot.mir =
      bitVal zero one (bitAtOf lay.cell m r))
    (hread : ∀ r, dt.ixBack lay zero one dt.dd0Le st r Slot.mir = zero) :
    m = fun _ => False := by
  funext u
  refine propext (iff_of_false (fun hu => ?_) (fun hc => hc))
  have h := (hslot (lay.cell u)).symm.trans (hread (lay.cell u))
  rw [bitVal_pos ⟨u, rfl, hu⟩] at h
  exact hzo h.symm

/-- **A tape whose mirror track is clear is its own pass tape**: the run layer
writes its tapes as `passTracksAt`, which overwrites the walked track with the
mark the head carries; where the head carries no mark and the track is clear,
the two agree. This is the bridge from the shape a *reading* recovers to the
tape the run lemmas are stated over. -/
theorem passTracksAt_of_mir_zero {J : Type}
    (cell : J → (Univ A R' P' dt.KIx dt.dd → Prop))
    {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd} [DecidableEq dt.SlotIx]
    (rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A)
    (hz : ∀ r, rest r Slot.mir = PR.zero) :
    PR.passTracksAt cell Slot.mir rest (fun _ => False) = rest := by
  funext r s
  change (if s = Slot.mir then bitVal PR.zero PR.one
    (bitAtOf cell (fun _ => False) r) else _) = _
  by_cases hs : s = Slot.mir
  · subst hs
    rw [if_pos rfl, bitVal_neg (by rintro ⟨u, -, hc⟩; exact hc), hz]
  · rw [if_neg hs]

end Recognise

/-! ### One step of the machine, seen from the tape -/

section StepTape

variable {L : Language.{0, 0}} {dt : DrawData L} {A R P K : Type} {c dd : ℕ}
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]
variable {Q W : Type} [Fintype Q] [Fintype W]
variable {PR : Prog A R P Q W K dd}

omit [Finite A] [Finite R] [Finite P] [Finite K] in
open Classical in
/-- **What a step does to the tape**: it leaves every cell but the one under the
head, and there it writes what the fired rule's `wr` makes of the control's
payload and the cell's own tracks. Read backwards – from an arbitrary step to the
tape it produces – this is what a recognising argument walks along, and it is the
converse of the run layer's `Prog.step_*` lemmas, which write the cell they
already know. -/
theorem step_tape_of_shape_tr (hR : PR.table.Reads)
    {x y : Config (WPoint (Univ A R P K dd))}
    {rest : (Univ A R P K dd → Prop) → W → A}
    {v : Univ A R P K dd → Prop}
    (hhead : x.head = Sum.inl v)
    (htape : x.tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank))
    {r : R} {w : Fin dd → A}
    (hread : (wideData (Univ A R P K dd)).Read
      (Sum.inr ((DrawTag.ctrl r : DrawTag R P K), w)) (x.tape x.head))
    (hwrite : (wideData (Univ A R P K dd)).Write
      (Sum.inr ((DrawTag.ctrl r : DrawTag R P K), w)) (y.tape x.head))
    (hframe : ∀ p, p ≠ x.head → y.tape p = x.tape p) :
    y.tape = wideTape (fun s => PR.syElt
      (if s = v then
        (PR.rules r).wr (fun q => unslot (unpad PR.table.payload_le w) (Sum.inl q))
          (rest v)
        else rest s))
      (PR.syElt PR.blank) := by
  classical
  -- the cell the head is on carries its own tracks, so the rule reads them
  have hxv : x.tape x.head = Sum.inr (PR.syElt (rest v)) := by
    rw [hhead, htape]
    rfl
  rw [hxv] at hread
  have hread' : PR.table.Read (DrawTag.ctrl r, w) (PR.syElt (rest v)) :=
    (hR.read _ _).mp hread
  have hg : (fun s => unslot (unpad PR.table.payload_le w) (Sum.inr s)) = rest v := by
    have h2 : PR.syElt (rest v) =
        symElt PR.zero (PR.table.readPl r (unpad PR.table.payload_le w)) := hread'
    have h3 := symElt_inj PR.table.payload_le h2
    change syPl (Q := Q) PR.zero (rest v) = syPl (Q := Q) PR.zero
      (fun s => unslot (unpad PR.table.payload_le w) (Sum.inr s)) at h3
    funext s
    have h4 := congrFun h3 ((Fintype.equivFin (Q ⊕ W)).symm.symm (Sum.inr s))
    simpa [syPl, syVec, unslot, slotPl] using h4.symm
  -- and what it writes there is the rule's own write
  rcases hy : y.tape x.head with s' | a'
  · rw [hy] at hwrite
    exact hwrite.elim
  · rw [hy] at hwrite
    have hwrite' : PR.table.Write (DrawTag.ctrl r, w) a' := (hR.write _ _).mp hwrite
    have ha' : a' = symElt PR.zero (PR.table.writePl r (unpad PR.table.payload_le w)) :=
      hwrite'
    funext p
    rcases p with s | e
    · by_cases hs : s = v
      · subst hs
        rw [hhead] at hy
        rw [hy, ha']
        change (Sum.inr (symElt PR.zero (PR.table.writePl r
          (unpad PR.table.payload_le w))) : WPoint (Univ A R P K dd)) = _
        change _ = Sum.inr (PR.syElt (if s = s then _ else _))
        rw [if_pos rfl]
        refine congrArg Sum.inr (congrArg (symElt PR.zero) ?_)
        change syPl (Q := Q) PR.zero ((PR.rules r).wr _
          (fun s' => unslot (unpad PR.table.payload_le w) (Sum.inr s'))) = _
        rw [hg]
      · have hne : (Sum.inl s : WPoint (Univ A R P K dd)) ≠ x.head := by
          rw [hhead]
          exact fun hc => hs (Sum.inl_injective hc)
        rw [hframe _ hne, htape]
        change Sum.inr (PR.syElt (rest s)) = Sum.inr (PR.syElt (if s = v then _ else _))
        rw [if_neg hs]
    · have hne : (Sum.inr e : WPoint (Univ A R P K dd)) ≠ x.head := by
        rw [hhead]
        exact fun hc => nomatch hc
      rw [hframe _ hne, htape]
      rfl

end StepTape



/-! ### The reading, along a run -/

section Recognising

variable {L : Language.{0, 0}} {dt : DrawData L} {A R' P' I : Type}
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [LinearOrder dt.KIx]
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]
variable [Fintype dt.SlotIx]
variable {PR : Prog A R' P' dt.CtlIx dt.SlotIx dt.KIx dt.dd}

variable (PR) in
/-- **A configuration the reading recognises**: its tape carries a slot vector
at every cell, of the shape `TapeShape` describes. -/
def ShapedAt (lay : Layout dt A R' P' I) (st₀ : TapeSt dt A R' P' I)
    (c : Config (WPoint (Univ A R' P' dt.KIx dt.dd))) : Prop :=
  ∃ rest, c.tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank) ∧
    TapeShape (dt := dt) lay PR.zero PR.one st₀ rest

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
open Classical in
/-- **One step of the opening keeps the configuration recognisable**: the tape
changes at the cell under the head alone (`step_tape_of_shape`), and the rule
that changed it keeps the file, keeps the addressed tracks and writes bits
(`tapeShape_update`). -/
theorem shapedAt_step (hR : PR.table.Reads) {lay : Layout dt A R' P' I}
    {st₀ : TapeSt dt A R' P' I}
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    {v : Univ A R' P' dt.KIx dt.dd → Prop} (hhead : x.head = Sum.inl v)
    (hfacts : ∀ r : R', Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r))
    (hx : ShapedAt PR lay st₀ x)
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ShapedAt PR lay st₀ y := by
  classical
  obtain ⟨rest, htape, hshape⟩ := hx
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  obtain ⟨t, w⟩ := τ
  match t with
  | .ctrl r =>
    obtain ⟨hfile, hcell, hbits⟩ := hfacts r
    exact ⟨_, step_tape_of_shape_tr hR hhead htape hread hwrite hframe,
      tapeShape_update hshape hfile hcell hbits _ v⟩
  | .sym => exact ((hR.tr _).mp hτ).elim
  | .phase p => exact ((hR.tr _).mp hτ).elim
  | .arg i => exact ((hR.tr _).mp hτ).elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A run of the opening stays recognisable**: the shape holds at the start and
every step along the way is one the reading can follow – the head on an address,
and a rule with the three properties. What the caller owes is exactly that, for
the configurations *before* the one it is asking about, which is how an opening's
reading is used: the evaluation's own rules are not among them. -/
theorem shapedAt_of_reaches (hR : PR.table.Reads) {lay : Layout dt A R' P' I}
    {st₀ : TapeSt dt A R' P' I}
    {c₀ : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hfacts : ∀ r : R', Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r))
    (h0 : ShapedAt PR lay st₀ c₀) :
    ∀ {c : Config (WPoint (Univ A R' P' dt.KIx dt.dd))},
      Relation.ReflTransGen (wideData (Univ A R' P' dt.KIx dt.dd)).Step c₀ c →
      ShapedAt PR lay st₀ c := by
  intro c hreach
  induction hreach with
  | refl => exact h0
  | @tail d e hcd hstep ih =>
    rcases hd : d.head with v | q
    · exact shapedAt_step hR hd hfacts ih hstep
    · -- the head is on the control's side, which is no position at all
      exfalso
      obtain ⟨τ, -, -, -, -, -, -, hmove⟩ := hstep
      have hposn : (wideData (Univ A R' P' dt.KIx dt.dd)).Posn d.head := by
        rcases hmove with ⟨-, hs⟩ | ⟨-, hs⟩
        · exact hs.1
        · exact hs.2.1
      obtain ⟨s, hs⟩ := wpPosn_iff (A := Univ A R' P' dt.KIx dt.dd) d.head |>.mp hposn
      rw [hd] at hs
      exact nomatch hs

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
open Classical in
/-- **One step keeps the shape, when the rule that fires is one of the phases the
caller vouches for.** A step's transition carries its rule, and the state it
fires from carries that rule's source phase, so vouching for the phases a run
passes through is vouching for the rules it fires. -/
theorem shapedAt_step_of_phase (hR : PR.table.Reads) {lay : Layout dt A R' P' I}
    {st₀ : TapeSt dt A R' P' I} {Ph : P' → Prop}
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    {v : Univ A R' P' dt.KIx dt.dd → Prop} (hhead : x.head = Sum.inl v)
    (hfacts : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r))
    (hph : ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      x.state = Sum.inr (stateElt PR.zero p f) → Ph p)
    (hx : ShapedAt PR lay st₀ x)
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ShapedAt PR lay st₀ y := by
  classical
  obtain ⟨rest, htape, hshape⟩ := hx
  -- the rule that fired, and the phase it fired from
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  rcases hxs : x.state with sx | qx
  · rw [hxs] at hsrc; exact hsrc.elim
  rw [hxs] at hsrc
  have hsrc' : PR.table.Src τ qx := (hR.src τ qx).mp hsrc
  obtain ⟨t, w⟩ := τ
  match t with
  | .ctrl r =>
    have hphr : Ph (PR.table.srcPh r) :=
      hph (PR.table.srcPh r) (PR.table.srcPl r (unpad PR.table.payload_le w))
        (by rw [hxs]; exact congrArg Sum.inr hsrc')
    obtain ⟨hfile, hcell, hbits⟩ := hfacts r hphr
    exact ⟨_, step_tape_of_shape_tr hR hhead htape hread hwrite hframe,
      tapeShape_update hshape hfile hcell hbits _ v⟩
  | .sym => exact ((hR.tr _).mp hτ).elim
  | .phase p => exact ((hR.tr _).mp hτ).elim
  | .arg i => exact ((hR.tr _).mp hτ).elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A run keeps the shape, as long as the caller vouches for the phases it
passes through** – all of them but the last, since it is the *fired* rules that
matter. This is the form an opening's reading uses: the phases before the
evaluation's entry are the outer layer's, and those are the rules
`nexRule_keepsFile_of_ne_eval` and its two siblings are about. -/
theorem shapedAt_of_reaches_of_phase (hR : PR.table.Reads)
    {lay : Layout dt A R' P' I} {st₀ : TapeSt dt A R' P' I} {Ph : P' → Prop}
    {c₀ : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hfacts : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r))
    (hhead : ∀ x : Config (WPoint (Univ A R' P' dt.KIx dt.dd)),
      ∃ v, x.head = Sum.inl v)
    (h0 : ShapedAt PR lay st₀ c₀)
    {c : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hreach : Relation.ReflTransGen (wideData (Univ A R' P' dt.KIx dt.dd)).Step c₀ c)
    (hpre : ∀ x y, Relation.ReflTransGen (wideData (Univ A R' P' dt.KIx dt.dd)).Step c₀ x →
      (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y →
      Relation.ReflTransGen (wideData (Univ A R' P' dt.KIx dt.dd)).Step y c →
      ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
        x.state = Sum.inr (stateElt PR.zero p f) → Ph p) :
    ShapedAt PR lay st₀ c := by
  induction hreach with
  | refl => exact h0
  | @tail d e hcd hstep ih =>
    obtain ⟨v, hv⟩ := hhead d
    refine shapedAt_step_of_phase hR hv hfacts
      (fun p f hst => hpre d e hcd hstep Relation.ReflTransGen.refl p f hst)
      (ih (fun x y hx hxy hy => hpre x y hx hxy (hy.tail hstep))) hstep

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The reading along a sequence**: the configuration at each time is
recognised, as long as the phases up to that time are ones the caller vouches
for. This is `shapedAt_of_reaches_of_phase` in the form a backward reading
actually has its run in – time by time, so that «the phases *before* the entry»
is a statement about indices. -/
theorem shapedAt_of_seq (hR : PR.table.Reads)
    {lay : Layout dt A R' P' I} {st₀ : TapeSt dt A R' P' I} {Ph : P' → Prop}
    (hfacts : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsFile dt (PR.rules r) ∧
      Rule.KeepsCellTracks dt (PR.rules r) ∧
      Rule.WritesBits dt PR.zero PR.one (PR.rules r))
    (g : ℕ → Config (WPoint (Univ A R' P' dt.KIx dt.dd)))
    (hhead : ∀ i, ∃ v, (g i).head = Sum.inl v)
    (h0 : ShapedAt PR lay st₀ (g 0))
    (n : ℕ)
    (hstep : ∀ i, i < n → (wideData (Univ A R' P' dt.KIx dt.dd)).Step (g i) (g (i + 1)))
    (hph : ∀ i, i < n → ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g i).state = Sum.inr (stateElt PR.zero p f) → Ph p) :
    ShapedAt PR lay st₀ (g n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨v, hv⟩ := hhead n
    exact shapedAt_step_of_phase hR hv hfacts (hph n (by omega))
      (ih (fun i hi => hstep i (by omega)) (fun i hi => hph i (by omega)))
      (hstep n (by omega))

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
open Classical in
/-- **A step that fires a rule keeping a slot leaves that track alone**, at every
address: at the head because the rule keeps it, elsewhere because a step writes
nowhere else. -/
theorem step_track_const (hR : PR.table.Reads) {Ph : P' → Prop} {t : dt.SlotIx}
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    {rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {v : Univ A R' P' dt.KIx dt.dd → Prop} (hhead : x.head = Sum.inl v)
    (htape : x.tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank))
    (hkeep : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsSlot dt t (PR.rules r))
    (hph : ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      x.state = Sum.inr (stateElt PR.zero p f) → Ph p)
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ∃ rest' : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A,
      y.tape = wideTape (fun r => PR.syElt (rest' r)) (PR.syElt PR.blank) ∧
      ∀ r, rest' r t = rest r t := by
  classical
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  rcases hxs : x.state with sx | qx
  · rw [hxs] at hsrc; exact hsrc.elim
  rw [hxs] at hsrc
  have hsrc' : PR.table.Src τ qx := (hR.src τ qx).mp hsrc
  obtain ⟨tg, w⟩ := τ
  match tg with
  | .ctrl r =>
    have hphr : Ph (PR.table.srcPh r) :=
      hph (PR.table.srcPh r) (PR.table.srcPl r (unpad PR.table.payload_le w))
        (by rw [hxs]; exact congrArg Sum.inr hsrc')
    refine ⟨_, step_tape_of_shape_tr hR hhead htape hread hwrite hframe, fun s => ?_⟩
    by_cases hs : s = v
    · subst hs
      rw [if_pos rfl]
      exact hkeep r hphr _ (rest s)
    · rw [if_neg hs]
  | .sym => exact ((hR.tr _).mp hτ).elim
  | .phase p => exact ((hR.tr _).mp hτ).elim
  | .arg i => exact ((hR.tr _).mp hτ).elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [LinearOrder A]
  [LinearOrder R'] [LinearOrder P'] [LinearOrder dt.KIx] [Fintype dt.SlotIx] in
/-- **After a step the head is on an address**: a move lands on a position, and
the positions of a wide machine are its addresses. The head of the *initial*
configuration is one by construction, so along a run every head is – which is
what a reading needs before it can speak of the cell under the head. -/
theorem head_isAddr_of_step
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ∃ v, y.head = Sum.inl v := by
  obtain ⟨τ, -, -, -, -, -, -, hmove⟩ := hstep
  have hposn : (wideData (Univ A R' P' dt.KIx dt.dd)).Posn y.head := by
    rcases hmove with ⟨-, hs⟩ | ⟨-, hs⟩
    · exact hs.2.1
    · exact hs.1
  exact wpPosn_iff (A := Univ A R' P' dt.KIx dt.dd) y.head |>.mp hposn

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A step, inverted**: the rule that fired, the data it fired on, that its
guard held, and the two phases it went between. `step_state_dst` is its
destination half; a reading that has to know *which* rule fired – because the
guard of every other one is false – needs the guard too. -/
theorem step_rule (hR : PR.table.Reads)
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ∃ (r : R') (f : dt.CtlIx → A) (g : dt.SlotIx → A),
      (PR.rules r).guard f g ∧
      x.state = Sum.inr (stateElt PR.zero (PR.rules r).srcPh
        (stPl (W := dt.SlotIx) PR.zero f)) ∧
      y.state = Sum.inr (stateElt PR.zero (PR.rules r).dstPh
        (stPl (W := dt.SlotIx) PR.zero ((PR.rules r).dstSt f g))) := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  have htr : PR.table.IsTr τ := (hR.tr τ).mp hτ
  rcases hxs : x.state with sx | qx
  · rw [hxs] at hsrc; exact hsrc.elim
  rcases hys : y.state with sy | qy
  · rw [hys] at hdst; exact hdst.elim
  rw [hxs] at hsrc
  rw [hys] at hdst
  have hsrc' : PR.table.Src τ qx := (hR.src τ qx).mp hsrc
  have hdst' : PR.table.Dst τ qy := (hR.dst τ qy).mp hdst
  obtain ⟨tg, w⟩ := τ
  match tg with
  | .ctrl r =>
    refine ⟨r, fun q => unslot (unpad PR.table.payload_le w) (Sum.inl q),
      fun s => unslot (unpad PR.table.payload_le w) (Sum.inr s), htr.2, ?_, ?_⟩
    · exact congrArg Sum.inr hsrc'
    · exact congrArg Sum.inr hdst'
  | .sym => exact htr.elim
  | .phase p => exact htr.elim
  | .arg i => exact htr.elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] [LinearOrder A]
  [LinearOrder R'] [LinearOrder P'] [LinearOrder dt.KIx]
  [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)] in
/-- **A symbol determines its tracks**: the payload is the packed track vector
and the packing is injective, so two recognised tapes that are equal carry equal
tracks. That is what lets a reading combine facts proved of *different*
recognitions of the same run – the shape's, and the marker's. -/
theorem rest_eq_of_tape
    {rest rest' : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (h : wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank) =
      wideTape (fun r => PR.syElt (rest' r)) (PR.syElt PR.blank)) :
    rest = rest' := by
  funext r
  have hr := congrFun h (Sum.inl r)
  rw [wideTape_addr, wideTape_addr] at hr
  have hsy : PR.syElt (rest r) = PR.syElt (rest' r) := Sum.inr.inj hr
  have hpl : syPl (Q := dt.CtlIx) PR.zero (rest r) =
      syPl (Q := dt.CtlIx) PR.zero (rest' r) :=
    pad_injective PR.table.payload_le (congrArg Prod.snd hsy)
  exact syPl_injective hpl

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The state a step lands in is a rule's destination**: which is how a
reading learns that a phase *no rule enters* – the start phase – occurs at time
zero and never again. -/
theorem step_state_dst (hR : PR.table.Reads)
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ∃ (r : R') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      y.state = Sum.inr (stateElt PR.zero (PR.rules r).dstPh f) := by
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  rcases hys : y.state with sy | qy
  · rw [hys] at hdst; exact hdst.elim
  rw [hys] at hdst
  have hdst' : PR.table.Dst τ qy := (hR.dst τ qy).mp hdst
  obtain ⟨tg, w⟩ := τ
  match tg with
  | .ctrl r =>
    exact ⟨r, PR.table.dstPl r (unpad PR.table.payload_le w),
      congrArg Sum.inr hdst'⟩
  | .sym => exact ((hR.tr _).mp hτ).elim
  | .phase p => exact ((hR.tr _).mp hτ).elim
  | .arg i => exact ((hR.tr _).mp hτ).elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
open Classical in
/-- **A step that fires a rule setting a slot leaves that track marking the cell
it was written at** – provided the track was clear before, which at the
channel's tape it is (`initBackReg_track_zero`). This is the one write of the
opening a backward reading has to *read*, rather than merely skip: the start
step's marker, which every later rule keeps (`nexRule_keepsSlot_wk_bot`). -/
theorem step_track_set (hR : PR.table.Reads) {Ph : P' → Prop} {t : dt.SlotIx}
    {x y : Config (WPoint (Univ A R' P' dt.KIx dt.dd))}
    {rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    {v : Univ A R' P' dt.KIx dt.dd → Prop} (hhead : x.head = Sum.inl v)
    (htape : x.tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank))
    (hset : ∀ r : R', Ph (PR.table.srcPh r) → Rule.SetsSlot dt PR.one t (PR.rules r))
    (hzero : ∀ r, rest r t = PR.zero)
    (hph : ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      x.state = Sum.inr (stateElt PR.zero p f) → Ph p)
    (hstep : (wideData (Univ A R' P' dt.KIx dt.dd)).Step x y) :
    ∃ rest' : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A,
      y.tape = wideTape (fun r => PR.syElt (rest' r)) (PR.syElt PR.blank) ∧
      ∀ s, rest' s t = bitVal PR.zero PR.one (s = v) := by
  classical
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := hstep
  obtain (sτ | τ) := τ
  · exact hτ.elim
  rcases hxs : x.state with sx | qx
  · rw [hxs] at hsrc; exact hsrc.elim
  rw [hxs] at hsrc
  have hsrc' : PR.table.Src τ qx := (hR.src τ qx).mp hsrc
  obtain ⟨tg, w⟩ := τ
  match tg with
  | .ctrl r =>
    have hphr : Ph (PR.table.srcPh r) :=
      hph (PR.table.srcPh r) (PR.table.srcPl r (unpad PR.table.payload_le w))
        (by rw [hxs]; exact congrArg Sum.inr hsrc')
    exact ⟨_, step_tape_of_shape_tr hR hhead htape hread hwrite hframe,
      fun s => track_after_set (hset r hphr) hzero _ v s⟩
  | .sym => exact ((hR.tr _).mp hτ).elim
  | .phase p => exact ((hR.tr _).mp hτ).elim
  | .arg i => exact ((hR.tr _).mp hτ).elim

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **A track the opening never writes still holds what it held**: the same
induction as the shape's, carried on one slot. Together with
`nexRule_keepsSlot_wk_bot` and `nexRule_keepsSlot_old` this is how a backward
reading learns *what* the tracks hold, not merely that they hold bits. -/
theorem track_const_of_seq (hR : PR.table.Reads) {Ph : P' → Prop} {t : dt.SlotIx}
    (hkeep : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsSlot dt t (PR.rules r))
    (g : ℕ → Config (WPoint (Univ A R' P' dt.KIx dt.dd)))
    (hhead : ∀ i, ∃ v, (g i).head = Sum.inl v)
    {rest₀ : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (h0 : (g 0).tape = wideTape (fun r => PR.syElt (rest₀ r)) (PR.syElt PR.blank))
    (n : ℕ)
    (hstep : ∀ i, i < n → (wideData (Univ A R' P' dt.KIx dt.dd)).Step (g i) (g (i + 1)))
    (hph : ∀ i, i < n → ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g i).state = Sum.inr (stateElt PR.zero p f) → Ph p) :
    ∃ rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A,
      (g n).tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank) ∧
      ∀ r, rest r t = rest₀ r t := by
  induction n with
  | zero => exact ⟨rest₀, h0, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨rest, hrest, hconst⟩ :=
      ih (fun i hi => hstep i (by omega)) (fun i hi => hph i (by omega))
    obtain ⟨v, hv⟩ := hhead n
    obtain ⟨rest', hrest', hconst'⟩ :=
      step_track_const hR hv hrest hkeep (hph n (by omega)) (hstep n (by omega))
    exact ⟨rest', hrest', fun r => (hconst' r).trans (hconst r)⟩

omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
/-- **The marker, along a run**: the first step writes it at the cell the head
began on and every later step keeps it, so at any time after the first the track
marks that cell and nothing else. With `ixBack_wk_inv` this is «the working
track marks the address the machine started at», the first of the hypotheses the
evaluation's entry state is asked for. -/
theorem track_set_of_seq (hR : PR.table.Reads) {Ph Ph₀ : P' → Prop}
    {t : dt.SlotIx}
    (hset : ∀ r : R', Ph₀ (PR.table.srcPh r) →
      Rule.SetsSlot dt PR.one t (PR.rules r))
    (hkeep : ∀ r : R', Ph (PR.table.srcPh r) → Rule.KeepsSlot dt t (PR.rules r))
    (g : ℕ → Config (WPoint (Univ A R' P' dt.KIx dt.dd)))
    (hhead : ∀ i, ∃ v, (g i).head = Sum.inl v)
    {rest₀ : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A}
    (h0 : (g 0).tape = wideTape (fun r => PR.syElt (rest₀ r)) (PR.syElt PR.blank))
    (hzero : ∀ r, rest₀ r t = PR.zero)
    {v₀ : Univ A R' P' dt.KIx dt.dd → Prop} (hhead0 : (g 0).head = Sum.inl v₀)
    (n : ℕ) (hn : 0 < n)
    (hstep : ∀ i, i < n → (wideData (Univ A R' P' dt.KIx dt.dd)).Step (g i) (g (i + 1)))
    (hph₀ : ∀ (p : P') (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g 0).state = Sum.inr (stateElt PR.zero p f) → Ph₀ p)
    (hph : ∀ i, 0 < i → i < n → ∀ (p : P')
        (f : Fin (Fintype.card (dt.CtlIx ⊕ dt.SlotIx)) → A),
      (g i).state = Sum.inr (stateElt PR.zero p f) → Ph p) :
    ∃ rest : (Univ A R' P' dt.KIx dt.dd → Prop) → dt.SlotIx → A,
      (g n).tape = wideTape (fun r => PR.syElt (rest r)) (PR.syElt PR.blank) ∧
      ∀ s, rest s t = bitVal PR.zero PR.one (s = v₀) := by
  obtain ⟨rest₁, hrest₁, hmark⟩ :=
    step_track_set hR hhead0 h0 hset hzero hph₀ (hstep 0 hn)
  obtain ⟨rest, hrest, hconst⟩ :=
    track_const_of_seq (PR := PR) hR hkeep (fun i => g (i + 1))
      (fun i => hhead (i + 1)) hrest₁ (n - 1)
      (fun i hi => by
        have h : i + 1 < n := by omega
        exact hstep (i + 1) h)
      (fun i hi p f hs => hph (i + 1) (by omega) (by omega) p f hs)
  refine ⟨rest, ?_, fun s => (hconst s).trans (hmark s)⟩
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1] at hrest
  exact hrest

end Recognising

end DrawData

end Draw

end DescriptiveComplexity
