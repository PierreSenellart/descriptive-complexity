/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Tape

/-!
# Walking the register file

The phase a space-bounded wide machine spends its life in. Its register file is
the `n` cells the input channel marked (`DescriptiveComplexity.Problems.Wide.Marks`),
one per element of the instance, and every register operation – read a bit, flip
one, increment a mirror, compare two – is the same walk:

> stand on the cell of `u`, write there, and scan right to the cell of the next
> element; repeat until the file is exhausted.

`DescriptiveComplexity.reaches_regStep` is one such move and
`DescriptiveComplexity.reaches_regWalk` is the whole traversal, the latter being
the only induction a program has to be given: the machine's state and its tape
are handed over *as functions of the element the pointer has reached*, and what
is discharged is a single move between an element and its successor.

Both come in the other direction too (`DescriptiveComplexity.reaches_regStepBack`,
`DescriptiveComplexity.reaches_regWalkBack`), and that reading is not a
convenience: the least significant digit of an address is the `WMLe`-**greatest**
element, so a program **incrementing its mirror** – clear the trailing digits, set
the first that is clear – walks the file from its last register towards its
first.

Getting *to* a register in the first place – the last one, to begin a downward
pass, and the first one, to come back from it – is
`DescriptiveComplexity.reaches_toReg` and `DescriptiveComplexity.reaches_toRegBack`:
one scan each, stopped by a symbol the target register carries and the others do
not. Only the two ends of the file need such a symbol; the marks in between are
all the same one, and must be, since a symbol is an element and there are as many
registers as elements.

Two facts make a move between consecutive registers a single scan rather than a
search: the cells of consecutive elements have **nothing marked between them**
(`DescriptiveComplexity.not_wmSeg_between`), so the scan cannot overshoot or stop
early; and the pointer lives in the machine's **control**, where a state may hold
an element of the instance, so no address arithmetic is involved in knowing which
register one is on.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Walk

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-! ### The successor of an element -/

variable (A) in
/-- **The successor of an element in the instance's order**: the least element
strictly above it. The pointer of a register walk steps by this, in the control,
while the head scans from one marked cell to the next. -/
def WMSucc (u u' : A) : Prop := WMLt WMLe u u' ∧ ∀ v : A, WMLt WMLe u v → WMLe u' v

/-- **Every element but the greatest has a successor.** -/
theorem exists_wmSucc (h : IsLinOrd (WMLe (A := A))) {u : A} (hne : ∃ v : A, WMLt WMLe u v) :
    ∃ u', WMSucc A u u' := by
  obtain ⟨u', hu', hmin⟩ := exists_least h hne
  exact ⟨u', hu', hmin⟩

/-! ### One move of the walk -/

/-- **One move of a register walk.** In the state `q`, on the cell of `u`, the
machine writes there and moves right; then, in the state `q'`, it scans over the
unmarked cells; it arrives on the cell of the successor of `u`.

The write is described the way every write in this development is – by naming the
new symbol assignment `f'` and saying it agrees with `f` off the cell of `u` – and
the scan is asked for only at the cells that are nobody's register, which is
exactly where `DescriptiveComplexity.not_wmSeg_between` says the machine will
pass. -/
theorem reaches_regStep (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u')
    {q q' b : A} {f f' : (A → Prop) → A}
    (hwrite : ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f (wmSeg u)) ∧ WMDst τ q' ∧
      WMWrite τ (f' (wmSeg u)) ∧ WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ wmSeg u → f' r = f r)
    (hscan : ∀ r : A → Prop, (∃ x : A, WMSetLe WMLe r (wmSeg x)) → (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q' ∧ WMRead τ (f' r) ∧ WMDst τ q' ∧ WMWrite τ (f' r) ∧
        WMRight τ) :
    Relation.ReflTransGen (wideData A).Step ⟨Sum.inr q, Sum.inl (wmSeg u), wideTape f b⟩
      ⟨Sum.inr q', Sum.inl (wmSeg u'), wideTape f' b⟩ := by
  have hlin := isLinOrd_wmSetLe h
  have hlt : WMSetLt WMLe (wmSeg u) (wmSeg u') := wmSetLt_wmSeg h hs.1
  -- The cell of `u` is not the last one, so the head can leave it.
  obtain ⟨t, hi⟩ := exists_wmIncr h (s := wmSeg u) ⟨u', fun hc => hs.1.2 hc⟩
  -- The increment is at or below the cell the walk is going to.
  have hub : WMSetLe WMLe t (wmSeg u') := by
    rcases hlin.2.2.2 t (wmSeg u') with hc | hc
    · exact hc
    · rcases eq_or_ne (wmSeg u') t with he | hne
      · exact he ▸ hlin.1 _
      · exact absurd ((wmSetLt_iff_of_wmIncr h hi _).mp ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩))
          (fun hcon => ((wmSetLt_iff _ _).mp hlt).2
            (hlin.2.2.1 _ _ ((wmSetLt_iff _ _).mp hlt).1 hcon))
  obtain ⟨τ, htr, hsrc, hread, hdst, hwr, hright⟩ := hwrite
  refine Relation.ReflTransGen.head
    (b := ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩)
    (step_wideTape_right h hi htr hsrc hread hdst hwr hright hagree) ?_
  -- From there, a scan whose stopping cells are the marked ones.
  obtain ⟨t₀, ⟨x, rfl⟩, hge, hfirst, hrun⟩ :=
    reaches_scan_tape (b := b) (Stop := fun r => ∃ x : A, r = wmSeg x) h
      ⟨wmSeg u', ⟨u', rfl⟩, hub⟩ fun r hlb hahead hstop =>
        hscan r (by obtain ⟨t, ⟨x, rfl⟩, hle⟩ := hahead; exact ⟨x, hle⟩)
          fun y hc => hstop ⟨y, hc⟩
  -- It stops at the cell of the successor: nothing marked lies before that one.
  have hxu : wmSeg x = wmSeg u' := by
    have hle : WMSetLe WMLe (wmSeg x) (wmSeg u') := by
      rcases hlin.2.2.2 (wmSeg x) (wmSeg u') with hc | hc
      · exact hc
      · rcases eq_or_ne (wmSeg u') (wmSeg x) with he | hne
        · exact he ▸ hlin.1 _
        · exact absurd ⟨u', rfl⟩ (hfirst (wmSeg u') hub ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩))
    rcases eq_or_ne (wmSeg x) (wmSeg u') with he | hne
    · exact he
    · exact absurd rfl (not_wmSeg_between h hs.2
        ((wmSetLt_iff _ _).mpr ⟨hlin.2.1 _ _ _ (wmSetLe_of_wmIncr hi) hge, fun hc =>
          ne_of_wmIncr hi (hlin.2.2.1 _ _ (wmSetLe_of_wmIncr hi) (hc ▸ hge))⟩)
        ((wmSetLt_iff _ _).mpr ⟨hle, hne⟩) x)
  exact hxu ▸ hrun

/-! ### The whole traversal -/

/-- The number of elements a register walk still has to visit, which is what its
induction is on. -/
private noncomputable def wmRank (u : A) : ℕ := bitRank (WMLe (A := A)) (fun _ => True) u

private theorem wmRank_lt (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hlt : WMLt WMLe u u') :
    wmRank u < wmRank u' :=
  bitRank_lt h trivial hlt.1 fun hc => hlt.2 (hc ▸ h.1 u)

/-- **A register walk.** Give the machine's state and its tape as functions of
the element its pointer has reached, discharge one move between each element of a
stretch and its successor, and the machine walks the whole stretch.

This is the only induction a program is given about its register file: with it, a
phase is described by what it does at *one* register, and the traversal – which
is a scan of exponentially many cells per register, and unbounded in a way only a
space-bounded machine can afford – never appears again. -/
theorem reaches_regWalk (h : IsLinOrd (WMLe (A := A))) {b : A} {st : A → A}
    {tp : A → (A → Prop) → A} {u₀ : A}
    (hmove : ∀ u u' : A, WMSucc A u u' → WMLe u₀ u →
      Relation.ReflTransGen (wideData A).Step ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩
        ⟨Sum.inr (st u'), Sum.inl (wmSeg u'), wideTape (tp u') b⟩) :
    ∀ u : A, WMLe u₀ u →
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr (st u₀), Sum.inl (wmSeg u₀), wideTape (tp u₀) b⟩
        ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩ := by
  have key : ∀ k : ℕ, ∀ u : A, wmRank u = k → WMLe u₀ u →
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr (st u₀), Sum.inl (wmSeg u₀), wideTape (tp u₀) b⟩
        ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hrank hge
      rcases eq_or_ne u₀ u with rfl | hne
      · exact Relation.ReflTransGen.refl
      -- The element just below `u` is still at or above `u₀`, and has `u` as successor.
      · obtain ⟨v, hv, hmax⟩ :=
          exists_greatest h (P := fun v => WMLe u₀ v ∧ WMLt WMLe v u)
            ⟨u₀, h.1 u₀, hge, fun hc => hne (h.2.2.1 u₀ u hge hc)⟩
        have hsucc : WMSucc A v u := by
          refine ⟨hv.2, fun w hw => ?_⟩
          by_contra hc
          exact hw.2 (hmax w ⟨h.2.1 u₀ v w hv.1 hw.1, (h.2.2.2 u w).resolve_left hc, hc⟩)
        exact (ih (wmRank v) (hrank ▸ wmRank_lt h hv.2) v rfl hv.1).trans
          (hmove v u hsucc hv.1)
  exact fun u hge => key _ u rfl hge

/-! ### Reaching a named register

Before a pass can start, and between one pass and the next, the head has to get
to a *particular* register – the last one to begin a downward pass, the first one
to come back from it, or the one a pointer in the control names. Each is a scan
whose stopping symbol is the name the register carries, and the two facts that
make it one scan are that the marked cells are ordered like their elements and
that a register's symbol names it. -/

/-- **Walking up to a distinguished register.** From any cell at or below the
register of `u`, in a fixed state, the machine scans right to it. The caller
offers the scanning transition at the cells that are nobody's register and at the
registers of the *other* elements – which in practice all hold the one generic
mark, so that is a single transition – and withholds it at the symbol the register
of `u` carries, which is what stops the scan. -/
theorem reaches_toReg (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A} {u : A}
    {s : A → Prop} (hle : WMSetLe WMLe s (wmSeg u))
    (hother : ∀ x : A, x ≠ u → ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f (wmSeg x)) ∧
      WMDst τ q ∧ WMWrite τ (f (wmSeg x)) ∧ WMRight τ)
    (hskip : ∀ r : A → Prop, (∃ x : A, WMSetLe WMLe r (wmSeg x)) → (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧
      WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ WMRight τ) :
    Relation.ReflTransGen (wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q, Sum.inl (wmSeg u), wideTape f b⟩ := by
  refine reaches_scanRight h hle fun r _ hlt => ?_
  by_cases hmark : ∃ x : A, r = wmSeg x
  · obtain ⟨x, rfl⟩ := hmark
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      hother x fun hc => ((wmSetLt_iff _ _).mp hlt).2 (congrArg wmSeg hc)
    exact ⟨τ, f (wmSeg x), htr, hsrc, hread, hdst, hwrite, hright, rfl⟩
  · obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      hskip r ⟨u, ((wmSetLt_iff r (wmSeg u)).mp hlt).1⟩ fun x hc => hmark ⟨x, hc⟩
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-- **Walking back down to a named register**, the same reading downwards: from
any cell at or above the register of `u`, the machine scans left to it. -/
theorem reaches_toRegBack (h : IsLinOrd (WMLe (A := A))) {q b : A} {f : (A → Prop) → A} {u : A}
    {s : A → Prop} (hle : WMSetLe WMLe (wmSeg u) s)
    (hother : ∀ x : A, x ≠ u → ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f (wmSeg x)) ∧
      WMDst τ q ∧ WMWrite τ (f (wmSeg x)) ∧ ¬WMRight τ)
    (hskip : ∀ r : A → Prop, (∃ x : A, WMSetLe WMLe (wmSeg x) r) → (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧
      WMRead τ (f r) ∧ WMDst τ q ∧ WMWrite τ (f r) ∧ ¬WMRight τ) :
    Relation.ReflTransGen (wideData A).Step ⟨Sum.inr q, Sum.inl s, wideTape f b⟩
      ⟨Sum.inr q, Sum.inl (wmSeg u), wideTape f b⟩ := by
  refine reaches_scanLeft h hle fun r hlt _ => ?_
  by_cases hmark : ∃ x : A, r = wmSeg x
  · obtain ⟨x, rfl⟩ := hmark
    obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      hother x fun hc => ((wmSetLt_iff _ _).mp hlt).2 (congrArg wmSeg hc.symm)
    exact ⟨τ, f (wmSeg x), htr, hsrc, hread, hdst, hwrite, hright, rfl⟩
  · obtain ⟨τ, htr, hsrc, hread, hdst, hwrite, hright⟩ :=
      hskip r ⟨u, ((wmSetLt_iff (wmSeg u) r).mp hlt).1⟩ fun x hc => hmark ⟨x, hc⟩
    exact ⟨τ, f r, htr, hsrc, hread, hdst, hwrite, hright, rfl⟩

/-! ### A track over the register file

The three passes of `DescriptiveComplexity.Problems.Wide.Mirror` and
`DescriptiveComplexity.Problems.Wide.Test` take the tape as a function of *one
track*, `tapeOf m`, and each asks for the same coherence condition: changing the
track at one element changes the tape at that element's cell and nowhere else. A
program does not verify that by hand. It builds its tape by reading the track
through `DescriptiveComplexity.regBit` – the track's digit at a register cell,
nothing anywhere else – and `DescriptiveComplexity.regBit_congr` is the condition,
discharged once for every program and every alphabet. -/

/-- **What a track shows at a cell**: its digit, if the cell is some element's
register; nothing at any other cell. A program's tape is a function of this and of
the address, and of nothing else about the track. -/
def regBit (m : A → Prop) (r : A → Prop) : Prop := ∃ u : A, r = wmSeg u ∧ m u

@[simp]
theorem regBit_wmSeg (h : IsLinOrd (WMLe (A := A))) (m : A → Prop) (u : A) :
    regBit m (wmSeg u) ↔ m u := by
  constructor
  · rintro ⟨v, hv, hm⟩
    rwa [wmSeg_injective h hv]
  · exact fun hm => ⟨u, rfl, hm⟩

omit [Finite A] in
/-- At a cell that is nobody's register a track shows nothing. -/
theorem regBit_of_not_reg {m r : A → Prop} (hno : ∀ u : A, r ≠ wmSeg u) : ¬regBit m r :=
  fun hc => hc.elim fun u hu => hno u hu.1

omit [Finite A] in
/-- **The coherence condition of the three passes, discharged.** Two tracks
agreeing off one element show the same thing at every cell but that element's
register – whatever else the program keeps in its symbols, since they enter the
tape only through this.

A caller finishes with `congrArg`: its tape is some `g r (regBit m r)`, and this
says the second argument does not move. -/
theorem regBit_congr {m m' : A → Prop} {u : A} (hag : ∀ v : A, v ≠ u → (m v ↔ m' v))
    {r : A → Prop} (hr : r ≠ wmSeg u) : regBit m r = regBit m' r := by
  refine propext ⟨fun ⟨v, hv, hm⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, hm⟩ => ⟨v, hv, ?_⟩⟩
  · exact (hag v fun hc => hr (hc ▸ hv)).mp hm
  · exact (hag v fun hc => hr (hc ▸ hv)).mpr hm

/-! ### The accumulator of a downward pass

A pass down the register file carries one bit of information in its control:
whether everything it has seen so far behaved. Since it walks downwards, "so far"
is "at every register above the one it is on", and the two states of the pass are
therefore a *function of the suffix*. Both subroutines built on the walk – the
mirror increment (`DescriptiveComplexity.Problems.Wide.Mirror`) and the file
tests (`DescriptiveComplexity.Problems.Wide.Test`) – are that shape, so it is
settled here. -/

open Classical in
/-- **The state a downward pass is in on arriving at the register of `w`**: the
first state exactly when the property holds at every register strictly above. -/
noncomputable def accState (P : A → Prop) (qy qn w : A) : A :=
  if ∀ v : A, WMLt WMLe w v → P v then qy else qn

open Classical in
/-- **The state a downward pass is in on leaving the register of `w`**: the same
with `w` itself taken into account. -/
noncomputable def accStateAfter (P : A → Prop) (qy qn w : A) : A :=
  if ∀ v : A, WMLe w v → P v then qy else qn

variable {P : A → Prop} {qy qn : A}

omit [Finite A] in
/-- **Leaving one register is arriving at the next one down.** -/
theorem accStateAfter_succ (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u') :
    accStateAfter P qy qn u' = accState P qy qn u := by
  have hiff : (∀ v : A, WMLe u' v → P v) ↔ ∀ v : A, WMLt WMLe u v → P v :=
    ⟨fun hall v hlt => hall v (hs.2 v hlt),
      fun hall v hle => hall v ⟨h.2.1 u u' v hs.1.1 hle, fun hc => hs.1.2 (h.2.1 u' v u hle hc)⟩⟩
  unfold accStateAfter accState
  by_cases hc : ∀ v : A, WMLt WMLe u v → P v
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun hcon => hc (hiff.mp hcon), if_neg hc]

omit [Finite A] in
/-- **At the last register nothing has been seen yet**, so the pass starts in the
first state. -/
theorem accState_top {top : A} (htop : ∀ v : A, WMLe v top) : accState P qy qn top = qy :=
  if_pos fun v hlt => absurd (htop v) hlt.2

omit [Finite A] in
/-- A pass is in one of its two states, whatever it has seen. -/
theorem accState_cases (w : A) : accState P qy qn w = qy ∨ accState P qy qn w = qn := by
  unfold accState
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Finite A] in
/-- **A pass that saw a failure ends in the second state.** -/
theorem accStateAfter_bot_neg {bot : A} (hbot : ∀ v : A, WMLe bot v) {u : A} (hu : ¬P u) :
    accStateAfter P qy qn bot = qn :=
  if_neg fun hall => hu (hall u (hbot u))

omit [Finite A] in
/-- **A pass that saw no failure ends in the first state.** -/
theorem accStateAfter_bot_pos {bot : A} (hall : ∀ u : A, P u) :
    accStateAfter P qy qn bot = qy :=
  if_pos fun v _ => hall v

/-! ### Walking the file the other way

The least significant digit of an address is the `WMLe`-**greatest** element
(`DescriptiveComplexity.Problems.Wide.Increment`), so a program incrementing its
mirror propagates the carry from the last register towards the first: the walk it
does is this one. -/

/-- **One move of a register walk, downwards.** In the state `q`, on the cell of
`u'`, the machine writes there and moves left; then it scans left over the
unmarked cells and arrives on the cell of the element `u'` succeeds. -/
theorem reaches_regStepBack (h : IsLinOrd (WMLe (A := A))) {u u' : A} (hs : WMSucc A u u')
    {q q' b : A} {f f' : (A → Prop) → A}
    (hwrite : ∃ τ : A, WMTr τ ∧ WMSrc τ q ∧ WMRead τ (f (wmSeg u')) ∧ WMDst τ q' ∧
      WMWrite τ (f' (wmSeg u')) ∧ ¬WMRight τ)
    (hagree : ∀ r : A → Prop, r ≠ wmSeg u' → f' r = f r)
    (hscan : ∀ r : A → Prop, (∃ x : A, WMSetLe WMLe (wmSeg x) r) → (∀ x : A, r ≠ wmSeg x) →
      ∃ τ : A, WMTr τ ∧ WMSrc τ q' ∧ WMRead τ (f' r) ∧ WMDst τ q' ∧ WMWrite τ (f' r) ∧
        ¬WMRight τ) :
    Relation.ReflTransGen (wideData A).Step ⟨Sum.inr q, Sum.inl (wmSeg u'), wideTape f b⟩
      ⟨Sum.inr q', Sum.inl (wmSeg u), wideTape f' b⟩ := by
  have hlin := isLinOrd_wmSetLe h
  have hlt : WMSetLt WMLe (wmSeg u) (wmSeg u') := wmSetLt_wmSeg h hs.1
  -- The cell of `u'` is not the first one, so the head can leave it downwards.
  obtain ⟨t, hi⟩ := exists_wmPred h (s := wmSeg u') ⟨u', h.1 u'⟩
  -- The predecessor is at or above the cell the walk is going to.
  have hlb : WMSetLe WMLe (wmSeg u) t :=
    (wmSetLt_iff_of_wmIncr h hi (wmSeg u)).mp hlt
  obtain ⟨τ, htr, hsrc, hread, hdst, hwr, hright⟩ := hwrite
  refine Relation.ReflTransGen.head
    (b := ⟨Sum.inr q', Sum.inl t, wideTape f' b⟩)
    (step_wideTape_left h hi htr hsrc hread hdst hwr hright hagree) ?_
  obtain ⟨t₀, ⟨x, rfl⟩, hle, hfirst, hrun⟩ :=
    reaches_scanBack_tape (b := b) (Stop := fun r => ∃ x : A, r = wmSeg x) h
      ⟨wmSeg u, ⟨u, rfl⟩, hlb⟩ fun r hub hahead hstop =>
        hscan r (by obtain ⟨t, ⟨x, rfl⟩, hle⟩ := hahead; exact ⟨x, hle⟩)
          fun y hc => hstop ⟨y, hc⟩
  -- It stops at the cell of `u`: nothing marked lies between the two.
  have hxu : wmSeg x = wmSeg u := by
    have hge : WMSetLe WMLe (wmSeg u) (wmSeg x) := by
      rcases hlin.2.2.2 (wmSeg x) (wmSeg u) with hc | hc
      · rcases eq_or_ne (wmSeg x) (wmSeg u) with he | hne
        · exact he ▸ hlin.1 _
        · exact absurd ⟨u, rfl⟩ (hfirst (wmSeg u) ((wmSetLt_iff _ _).mpr ⟨hc, hne⟩) hlb)
      · exact hc
    rcases eq_or_ne (wmSeg x) (wmSeg u) with he | hne
    · exact he
    · refine absurd rfl (not_wmSeg_between h hs.2
        ((wmSetLt_iff _ _).mpr ⟨hge, fun hc => hne hc.symm⟩)
        ((wmSetLt_iff _ _).mpr ⟨hlin.2.1 _ _ _ hle (wmSetLe_of_wmIncr hi), fun hc => ?_⟩) x)
      exact ne_of_wmIncr hi (hlin.2.2.1 _ _ (wmSetLe_of_wmIncr hi) (hc ▸ hle))
  exact hxu ▸ hrun

/-- **A register walk, downwards**: the mirror of
`DescriptiveComplexity.reaches_regWalk`, from the top of a stretch of the file to
any element of it. This is the shape of a mirror increment – clear the trailing
digits, set the first that is clear – so it is the walk a program does most. -/
theorem reaches_regWalkBack (h : IsLinOrd (WMLe (A := A))) {b : A} {st : A → A}
    {tp : A → (A → Prop) → A} {u₁ : A}
    (hmove : ∀ u u' : A, WMSucc A u u' → WMLe u' u₁ →
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr (st u'), Sum.inl (wmSeg u'), wideTape (tp u') b⟩
        ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩) :
    ∀ u : A, WMLe u u₁ →
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr (st u₁), Sum.inl (wmSeg u₁), wideTape (tp u₁) b⟩
        ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩ := by
  have key : ∀ k : ℕ, ∀ u : A, wmRank u₁ - wmRank u = k → WMLe u u₁ →
      Relation.ReflTransGen (wideData A).Step
        ⟨Sum.inr (st u₁), Sum.inl (wmSeg u₁), wideTape (tp u₁) b⟩
        ⟨Sum.inr (st u), Sum.inl (wmSeg u), wideTape (tp u) b⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hrank hle
      rcases eq_or_ne u u₁ with rfl | hne
      · exact Relation.ReflTransGen.refl
      · have hlt : WMLt WMLe u u₁ := ⟨hle, fun hc => hne (h.2.2.1 u u₁ hle hc)⟩
        obtain ⟨u', hsucc⟩ := exists_wmSucc h ⟨u₁, hlt⟩
        have hu' : WMLe u' u₁ := hsucc.2 u₁ hlt
        have h1 : wmRank u < wmRank u' := wmRank_lt h hsucc.1
        have h2 : wmRank u' ≤ wmRank u₁ := by
          rcases eq_or_ne u' u₁ with rfl | hne'
          · exact Nat.le_refl _
          · exact Nat.le_of_lt (wmRank_lt h ⟨hu', fun hc => hne' (h.2.2.1 u' u₁ hu' hc)⟩)
        exact (ih (wmRank u₁ - wmRank u') (by omega) u' rfl hu').trans (hmove u u' hsucc hu')
  exact fun u hle => key _ u rfl hle

end Walk

end DescriptiveComplexity
