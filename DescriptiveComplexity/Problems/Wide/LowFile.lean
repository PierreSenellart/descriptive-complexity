/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegFile

/-!
# A register file on a stretch of consecutive addresses

The register file the input channel marks (`DescriptiveComplexity.wmSegFile`) is
free, but it is a geometric ruler: the cell of the `j`-th element sits at address
`2 ^ m − 2 ^ (m − j − 1)`, so the file lies entirely in the **top half** of the
tape and reaching its upper registers costs almost the whole tape. A machine with
no clock does not care. A machine whose clock counts the addresses can walk that
file once and never again.

This file builds the other one:

> **the registers are `n` consecutive addresses**, the register of the `j`-th
> element being the address of rank `base + j`.

Everything a walk asks for follows at once, since
`DescriptiveComplexity.RegFile` asks only for strict monotonicity: ranks are
monotone, so the cells are (`DescriptiveComplexity.segFile`). What indexes the
registers plays no part in that, so the construction is made at an arbitrary
ordered index (`DescriptiveComplexity.ixSegFile`) and the elementwise file is
its diagonal – which is what a program too tightly clocked to afford one
register per element will build its own file with. What the geometry
buys is the *cost*: consecutive registers are consecutive addresses
(`DescriptiveComplexity.segFile_gap`), so a move of the walk is one step and a
pass over the whole file costs `n`, against the whole tape for the ruler.

**Where the stretch sits is the caller's choice, and it is not a free one.** The
subroutines written for the input channel's file assume it lies *above* the
addresses the program computes with, since that is where the ruler is
(`DescriptiveComplexity.Problems.Wide.Marks`): a scan looking for a register
scans upwards, and the bound it is given is a register. A program that builds its
own file and wants those subroutines unchanged puts it above its data as well; one
that wants it out of the way takes `base = 1`, `DescriptiveComplexity.lowFile`,
whose registers are the first `n` nonempty addresses and which therefore lies
below everything (`DescriptiveComplexity.wideRank_lowCell_le`).

There is nothing to arrange for the addresses to exist: the cell of an element
uses no marked symbol, so a program with this file **writes** its own names into
those cells – one per cell, as it walks the bottom of the tape in its first `n`
steps – and the two ends are recognized like any other register. The one fact
that has to be proved is that there is room, and there is, with room to spare:
there are `2 ^ n` addresses for `n` elements
(`DescriptiveComplexity.card_wideAddr`, the clock of the model read as a count).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section LowFile

variable {A : Type} [Language.wide.Structure A] [Finite A]

/-! ### Comparing addresses by rank -/

/-- **An address is below another exactly when its rank is smaller.** The rank
determines the address, so a family of addresses is strictly monotone as soon as
its ranks are. -/
theorem wideRank_lt_iff (h : IsLinOrd (WMLe (A := A))) (s t : A → Prop) :
    wideRank s < wideRank t ↔ WMSetLt WMLe s t := by
  have hlin := isLinOrd_wmSetLe h
  constructor
  · intro hlt
    rcases hlin.2.2.2 s t with hst | hts
    · exact (wmSetLt_iff s t).mpr ⟨hst, fun hc => absurd (hc ▸ hlt) (Nat.lt_irrefl _)⟩
    · exact absurd (wideRank_mono h hts) (by omega)
  · intro hlt
    exact bitRank_lt (isLinOrd_wpLe h) (p := (Sum.inl s : WPoint A)) trivial
      ((wmSetLt_iff s t).mp hlt).1
      fun hc => ((wmSetLt_iff s t).mp hlt).2 (Sum.inl_injective hc)

/-! ### There is room at the bottom -/

/-- **There are strictly more addresses than elements**, which is the room the
construction below needs: one address per element, and one more for the empty
address it starts above. -/
theorem card_lt_card_wideAddr :
    Nat.card A < Nat.card {p : WPoint A // (wideData A).Posn p} := by
  rw [card_wideAddr]
  exact Nat.lt_two_pow_self

/-! ### The addresses from the bottom, one by one -/

open Classical in
/-- **The `j`-th address from the bottom**: the empty address, then increments.
Beyond the last address the sequence stands still, which never happens below the
number of addresses. -/
noncomputable def addrSeq (h : IsLinOrd (WMLe (A := A))) : ℕ → (A → Prop)
  | 0 => fun _ => False
  | j + 1 =>
    if hex : ∃ x : A, ¬addrSeq h j x then Classical.choose (exists_wmIncr h hex)
    else addrSeq h j

/-- Where the sequence advances, it advances by an increment. -/
theorem wmIncr_addrSeq (h : IsLinOrd (WMLe (A := A))) {j : ℕ}
    (hex : ∃ x : A, ¬addrSeq h j x) : WMIncr WMLe (addrSeq h j) (addrSeq h (j + 1)) := by
  have : addrSeq h (j + 1) = Classical.choose (exists_wmIncr h hex) := by
    simp only [addrSeq, dif_pos hex]
  rw [this]
  exact Classical.choose_spec (exists_wmIncr h hex)

/-- **The `j`-th address has rank `j`**, as long as there is a `j`-th address at
all. This is the whole content of the construction: the ranks are the numbers
`0, 1, 2, …`, so the addresses are the tape read from its bottom end. -/
theorem wideRank_addrSeq (h : IsLinOrd (WMLe (A := A))) :
    ∀ j : ℕ, j < Nat.card {p : WPoint A // (wideData A).Posn p} → wideRank (addrSeq h j) = j := by
  intro j
  induction j with
  | zero => intro _; exact wideRank_bot h
  | succ j ih =>
    intro hlt
    have hj : wideRank (addrSeq h j) = j := ih (by omega)
    -- Below the last address the sequence is not yet the full one, so it advances.
    have hex : ∃ x : A, ¬addrSeq h j x := by
      by_contra hc
      have hfull : addrSeq h j = fun _ => True :=
        funext fun x => propext (iff_of_true (not_not.mp fun hcon => hc ⟨x, hcon⟩) trivial)
      have hmax : wideRank (addrSeq h j) + 1 =
          Nat.card {p : WPoint A // (wideData A).Posn p} := by
        rw [hfull]
        exact bitRank_maxPos (p := (Sum.inl fun _ : A => True : WPoint A)) (maxPos_wpLe h)
      omega
    rw [wideRank_incr h (wmIncr_addrSeq h hex), hj]

/-! ### The file, and where it sits

Which stretch of the tape the registers occupy is the **caller's** choice, and it
is not a free one. The file the input channel marks lies *above* every address a
program computes with (`DescriptiveComplexity.Problems.Wide.Marks`), and the
subroutines written for it are stated that way – a scan looking for a register
scans upwards, and the bound it is given is a register. A program that builds its
own file and wants those subroutines unchanged must therefore put it **above its
data** as well, which here means high in its working region; one that wants the
file out of the way puts it at the bottom. Both are the same construction at a
different base. -/

/-! ### The file, at an arbitrary index -/

section IxSeg

variable {I : Type} [Finite I] (ile : I → I → Prop)

/-- **The register of an index in the file based at `base`**: the address whose
rank is `base` above the index's, so the file is the stretch of consecutive
addresses whose ranks start at `base`. -/
noncomputable def ixSegCell (h : IsLinOrd (WMLe (A := A))) (base : ℕ) (u : I) : A → Prop :=
  addrSeq h (base + ixRank ile u)

/-- The rank of a register is its index's, shifted by the base. -/
theorem wideRank_ixSegCell (h : IsLinOrd (WMLe (A := A))) {base : ℕ}
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) (u : I) :
    wideRank (ixSegCell ile h base u) = base + ixRank ile u :=
  wideRank_addrSeq h _ (by have := ixRank_lt_card ile u; omega)

/-- **A register file on a stretch of consecutive addresses**, one register per
index. The base says where the stretch starts; it must be positive, so that no
register is the empty address the head starts on, and the stretch must fit below
the top of the tape. -/
noncomputable def ixSegFile (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hpos : 0 < base)
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) :
    IxFile A I ile where
  cell := ixSegCell ile h base
  strictMono := fun u v hlt => by
    refine (wideRank_lt_iff h _ _).mp ?_
    rw [wideRank_ixSegCell ile h hbase, wideRank_ixSegCell ile h hbase]
    exact Nat.add_lt_add_left (ixRank_lt ile hi hlt) base
  cell_nonempty := fun u => by
    by_contra hc
    have hempty : ixSegCell ile h base u = fun _ => False :=
      funext fun x => propext (iff_of_false (fun hx => hc ⟨x, hx⟩) id)
    have hr := wideRank_ixSegCell ile h hbase u
    rw [hempty, wideRank_bot h] at hr
    omega

@[simp]
theorem cell_ixSegFile (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hpos : 0 < base)
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) :
    (ixSegFile ile h hi hpos hbase).cell = ixSegCell ile h base :=
  rfl

/-- **The successor of a register's address is the next register's**, so a sweep
of the file's stretch and a walk of the file step together: the address the sweep
moves to is the cell of the index the pointer moves to. This is what lets the
file-laying phase name every cell it writes. -/
theorem wmIncr_ixSegCell (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile)
    {base : ℕ}
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p})
    {u u' : I} (hs : IxSucc ile u u') :
    WMIncr WMLe (ixSegCell ile h base u) (ixSegCell ile h base u') := by
  have hr : ixRank ile u' = ixRank ile u + 1 := ixRank_succ ile hi hs
  have hlt : base + ixRank ile u <
      Nat.card {p : WPoint A // (wideData A).Posn p} := by
    have := ixRank_lt_card ile u'
    omega
  have hex : ∃ x : A, ¬addrSeq h (base + ixRank ile u) x := by
    by_contra hc
    have hfull : addrSeq h (base + ixRank ile u) = fun _ => True :=
      funext fun x => propext (iff_of_true
        (not_not.mp fun hx => hc ⟨x, hx⟩) trivial)
    have h1 : wideRank (addrSeq h (base + ixRank ile u)) = base + ixRank ile u :=
      wideRank_addrSeq h _ hlt
    have h2 : wideRank (addrSeq h (base + ixRank ile u')) = base + ixRank ile u' := by
      refine wideRank_addrSeq h _ ?_
      have := ixRank_lt_card ile u'
      omega
    have h3 : WMSetLt WMLe (ixSegCell ile h base u) (ixSegCell ile h base u') := by
      refine (wideRank_lt_iff h _ _).mp ?_
      rw [wideRank_ixSegCell ile h hbase, wideRank_ixSegCell ile h hbase]
      omega
    rw [ixSegCell, hfull] at h3
    obtain ⟨x, -, hs, -⟩ := h3
    exact hs trivial
  have := wmIncr_addrSeq h hex
  rw [ixSegCell, ixSegCell, hr]
  exact this

/-- **Consecutive registers are consecutive addresses**, wherever the file sits,
so a move of a walk over it is a single step and a pass over the whole file costs
one step per index. -/
theorem ixSegFile_gap (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hpos : 0 < base)
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p})
    {u u' : I} (hs : IxSucc ile u u') :
    wideRank ((ixSegFile ile h hi hpos hbase).cell u') -
        wideRank ((ixSegFile ile h hi hpos hbase).cell u) ≤ 1 := by
  rw [cell_ixSegFile, wideRank_ixSegCell ile h hbase, wideRank_ixSegCell ile h hbase,
    ixRank_succ ile hi hs]
  omega

end IxSeg

/-- **The register of an element in the file based at `base`**: the address whose
rank is `base` above the element's, so the file is the stretch of `n` consecutive
addresses whose ranks start at `base`. -/
noncomputable def segCell (h : IsLinOrd (WMLe (A := A))) (base : ℕ) (u : A) : A → Prop :=
  ixSegCell (WMLe (A := A)) h base u

/-- The rank of a register is its element's, shifted by the base. -/
theorem wideRank_segCell (h : IsLinOrd (WMLe (A := A))) {base : ℕ}
    (hbase : base + Nat.card A ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) (u : A) :
    wideRank (segCell h base u) = base + wmRank u :=
  wideRank_ixSegCell _ h hbase u

/-- **A register file on a stretch of consecutive addresses.** The base says where
the stretch starts; it must be positive, so that no register is the empty address
the head starts on, and the stretch must fit below the top of the tape. -/
noncomputable def segFile (h : IsLinOrd (WMLe (A := A))) {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card A ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) : RegFile A where
  cell := segCell h base
  strictMono := (ixSegFile (WMLe (A := A)) h h hpos hbase).strictMono
  cell_nonempty := (ixSegFile (WMLe (A := A)) h h hpos hbase).cell_nonempty

@[simp]
theorem cell_segFile (h : IsLinOrd (WMLe (A := A))) {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card A ≤ Nat.card {p : WPoint A // (wideData A).Posn p}) :
    (segFile h hpos hbase).cell = segCell h base :=
  rfl

/-- **Consecutive registers are consecutive addresses**, wherever the file sits,
so a move of a walk over it is a single step and a pass over the whole file costs
one step per element. This is the hypothesis the budgeted walks ask for, with
`w = 1`. -/
theorem segFile_gap (h : IsLinOrd (WMLe (A := A))) {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card A ≤ Nat.card {p : WPoint A // (wideData A).Posn p})
    {u u' : A} (hs : WMSucc A u u') :
    wideRank ((segFile h hpos hbase).cell u') - wideRank ((segFile h hpos hbase).cell u) ≤ 1 :=
  ixSegFile_gap (WMLe (A := A)) h h hpos hbase hs

/-! ### The file at the bottom

The base-`1` case: the registers are the first `n` nonempty addresses, so the
machine builds the file in its first `n` steps and everything above it is free. -/

/-- **The register of an element in the file at the bottom of the tape.** -/
noncomputable def lowCell (h : IsLinOrd (WMLe (A := A))) (u : A) : A → Prop :=
  segCell h 1 u

/-- There is room for the file at the bottom: there are strictly more addresses
than elements. -/
theorem one_add_card_le :
    1 + Nat.card A ≤ Nat.card {p : WPoint A // (wideData A).Posn p} := by
  have := card_lt_card_wideAddr (A := A)
  omega

/-- The rank of a register is one above the rank of the element naming it. -/
theorem wideRank_lowCell (h : IsLinOrd (WMLe (A := A))) (u : A) :
    wideRank (lowCell h u) = wmRank u + 1 := by
  rw [lowCell, wideRank_segCell h (one_add_card_le)]
  omega

/-- **The register file at the bottom of the tape.** -/
noncomputable def lowFile (h : IsLinOrd (WMLe (A := A))) : RegFile A :=
  segFile h Nat.one_pos (one_add_card_le)

@[simp]
theorem cell_lowFile (h : IsLinOrd (WMLe (A := A))) : (lowFile h).cell = lowCell h :=
  rfl

/-! ### Which addresses the registers are

A program does not merely need its file to exist: the phase that **builds** it
walks the bottom of the tape writing one name per cell, so it needs to know that
the cells it passes are exactly the registers, and which element each belongs
to. Both are read off the ranks. -/

/-- **An address is determined by its rank**, ranks being a strictly monotone map
of a linear order. -/
theorem wideRank_injective (h : IsLinOrd (WMLe (A := A))) :
    Function.Injective (wideRank (A := A)) := by
  intro s t he
  rcases eq_or_ne s t with rfl | hne
  · rfl
  · rcases (isLinOrd_wmSetLe h).2.2.2 s t with hle | hle
    · exact absurd ((wideRank_lt_iff h s t).mpr ((wmSetLt_iff s t).mpr ⟨hle, hne⟩))
        (by omega)
    · refine absurd ((wideRank_lt_iff h t s).mpr ((wmSetLt_iff t s).mpr
        ⟨hle, fun hc => hne hc.symm⟩)) (by omega)

/-- **Every rank below the number of elements is taken.** The rank map is
injective into as many numbers as there are elements, so it is onto them; this is
what says the file has a register for each of the first `n` nonempty
addresses. -/
theorem exists_wmRank_eq (h : IsLinOrd (WMLe (A := A))) {k : ℕ} (hk : k < Nat.card A) :
    ∃ u : A, wmRank u = k := by
  classical
  have := Fintype.ofFinite A
  have hcard : Fintype.card A = Nat.card A := (Nat.card_eq_fintype_card (α := A)).symm
  have hinj : Function.Injective fun u : A => (⟨wmRank u, wmRank_lt_card u⟩ : Fin (Nat.card A)) :=
    fun u v he => by
      by_contra hne
      rcases h.2.2.2 u v with hle | hle
      · exact absurd (congrArg Fin.val he)
          (Nat.ne_of_lt (wmRank_lt h ⟨hle, fun hc => hne (h.2.2.1 u v hle hc)⟩))
      · exact absurd (congrArg Fin.val he).symm
          (Nat.ne_of_lt (wmRank_lt h ⟨hle, fun hc => hne (h.2.2.1 u v hc hle)⟩))
  have hsurj := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, hcard]⟩ |>.2
  obtain ⟨u, hu⟩ := hsurj ⟨k, hk⟩
  exact ⟨u, congrArg Fin.val hu⟩

/-- **Every rank below the number of indices is taken.** The index rank map is
injective into as many numbers as there are indices, so it is onto them – the
index-level sibling of `DescriptiveComplexity.exists_wmRank_eq`, and what says a
file on a stretch has a register for every address of that stretch. -/
theorem exists_ixRank_eq {I : Type} [Finite I] {ile : I → I → Prop} (hi : IsLinOrd ile)
    {k : ℕ} (hk : k < Nat.card I) : ∃ u : I, ixRank ile u = k := by
  classical
  have := Fintype.ofFinite I
  have hcard : Fintype.card I = Nat.card I := (Nat.card_eq_fintype_card (α := I)).symm
  have hinj : Function.Injective
      (fun u : I => (⟨ixRank ile u, ixRank_lt_card ile u⟩ : Fin (Nat.card I))) :=
    fun u v he => by
      by_contra hne
      rcases hi.2.2.2 u v with hle | hle
      · exact absurd (congrArg Fin.val he)
          (Nat.ne_of_lt (ixRank_lt ile hi ⟨hle, fun hc => hne (hi.2.2.1 u v hle hc)⟩))
      · exact absurd (congrArg Fin.val he).symm
          (Nat.ne_of_lt (ixRank_lt ile hi ⟨hle, fun hc => hne (hi.2.2.1 u v hc hle)⟩))
  have hsurj := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, hcard]⟩ |>.2
  obtain ⟨u, hu⟩ := hsurj ⟨k, hk⟩
  exact ⟨u, congrArg Fin.val hu⟩

/-- **The address just above a file's stretch**: where a sweep of the file
stops, one past its last register. -/
noncomputable def ixSegTop (I : Type) [Finite I] (h : IsLinOrd (WMLe (A := A)))
    (base : ℕ) : A → Prop :=
  addrSeq h (base + Nat.card I)

/-- The rank of that address is the stretch's length above the base. -/
theorem wideRank_ixSegTop {I : Type} [Finite I] (h : IsLinOrd (WMLe (A := A)))
    {base : ℕ}
    (hbase : base + Nat.card I < Nat.card {p : WPoint A // (wideData A).Posn p}) :
    wideRank (ixSegTop I h base) = base + Nat.card I :=
  wideRank_addrSeq h _ hbase

/-- **Every register is below the stretch's end**, which is the upper bound a
file-laying sweep is run against. -/
theorem wmSetLt_ixSegTop {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) {base : ℕ}
    (hbase : base + Nat.card I < Nat.card {p : WPoint A // (wideData A).Posn p})
    (u : I) : WMSetLt WMLe (ixSegCell ile h base u) (ixSegTop I h base) := by
  refine (wideRank_lt_iff h _ _).mp ?_
  rw [wideRank_ixSegCell ile h (le_of_lt hbase), wideRank_ixSegTop (I := I) h hbase]
  have := ixRank_lt_card ile u
  omega

/-- **The greatest index has the greatest rank**: every index below it, and the
ranks running over `0 … card − 1`, leave it the last. So a walk that stops at
the top register has crossed every one of them. -/
theorem ixRank_of_top {I : Type} [Finite I] {ile : I → I → Prop} (hi : IsLinOrd ile)
    {utop : I} (htop : ∀ y : I, ile y utop) : ixRank ile utop + 1 = Nat.card I := by
  have hlt := ixRank_lt_card ile utop
  refine le_antisymm hlt ?_
  by_contra hc
  obtain ⟨w, hw⟩ := exists_ixRank_eq (ile := ile) hi (k := Nat.card I - 1)
    (by omega)
  have := ixRank_le_of_le ile hi (htop w)
  omega

/-- **The last address the sequence of a stretch reaches is taken**: below the
tape's top, some cell is outside the address, which is what lets the sequence
advance. -/
theorem exists_not_addrSeq (h : IsLinOrd (WMLe (A := A))) {j : ℕ}
    (hj : j + 1 < Nat.card {p : WPoint A // (wideData A).Posn p}) :
    ∃ x : A, ¬addrSeq h j x := by
  classical
  by_contra hc
  have hstay : addrSeq h (j + 1) = addrSeq h j := by
    simp only [addrSeq, dif_neg hc]
  have h1 := wideRank_addrSeq h j (by omega)
  have h2 := wideRank_addrSeq h (j + 1) hj
  rw [hstay, h1] at h2
  omega

/-- **The least index has rank zero**: nothing lies below it, so a walk that
starts at the first register has crossed none. -/
theorem ixRank_of_bot {I : Type} [Finite I] {ile : I → I → Prop} (hi : IsLinOrd ile)
    {ubot : I} (hbot : ∀ y : I, ile ubot y) : ixRank ile ubot = 0 := by
  have : Nonempty I := ⟨ubot⟩
  have hcard : 0 < Nat.card I := Nat.card_pos
  obtain ⟨w, hw⟩ := exists_ixRank_eq (ile := ile) hi (k := 0) hcard
  have := ixRank_le_of_le ile hi (hbot w)
  omega

/-- **The address past a stretch is no register's**, which is what tells the
sweep's last landing from every cell it wrote. -/
theorem ixSegTop_ne_ixSegCell {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) {base : ℕ}
    (hbase : base + Nat.card I < Nat.card {p : WPoint A // (wideData A).Posn p})
    (w : I) : ixSegTop I h base ≠ ixSegCell ile h base w := by
  intro hc
  have h1 := wideRank_ixSegTop (I := I) h hbase
  have h2 := wideRank_ixSegCell ile h (le_of_lt hbase) w
  have h3 := ixRank_lt_card ile w
  rw [hc, h2] at h1
  omega

/-- **The step off the last register**: the address the sweep moves to when it
writes the file's last register is the one just past the stretch. -/
theorem wmIncr_ixSegCell_top {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hbase : base + Nat.card I < Nat.card {p : WPoint A // (wideData A).Posn p})
    {utop : I} (htop : ∀ y : I, ile y utop) :
    WMIncr WMLe (ixSegCell ile h base utop) (ixSegTop I h base) := by
  have hr : ixRank ile utop + 1 = Nat.card I := ixRank_of_top hi htop
  have hex : ∃ x : A, ¬addrSeq h (base + ixRank ile utop) x :=
    exists_not_addrSeq h (by omega)
  have := wmIncr_addrSeq h hex
  rw [ixSegCell, ixSegTop, show base + Nat.card I = base + ixRank ile utop + 1 by omega]
  exact this

/-! ### What a file's stretch costs

A sweep of the stretch costs the difference of the two ranks, and these are what
that difference is: the stretch is exactly as long as the file has registers,
and the last register sits one short of its end. Every budget of the opening
phases is one of these two numbers. -/

/-- **A sweep of the stretch costs one step per register.** -/
theorem wideRank_ixSegTop_sub_bot {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hbase : base + Nat.card I < Nat.card {p : WPoint A // (wideData A).Posn p})
    {ubot : I} (hbot : ∀ y : I, ile ubot y) :
    wideRank (ixSegTop I h base) - wideRank (ixSegCell ile h base ubot) = Nat.card I := by
  rw [wideRank_ixSegTop (I := I) h hbase,
    wideRank_ixSegCell ile h (le_of_lt hbase) ubot, ixRank_of_bot hi hbot]
  omega

/-- **The last register sits one short of the stretch's end**, so a walk home
from it costs the stretch and the file's base together, less one. -/
theorem wideRank_ixSegCell_top {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p})
    {utop : I} (htop : ∀ y : I, ile y utop) :
    wideRank (ixSegCell ile h base utop) + 1 = base + Nat.card I := by
  rw [wideRank_ixSegCell ile h hbase utop]
  have := ixRank_of_top hi htop
  omega

/-- **The registers of a file on a stretch are exactly the addresses of that
stretch.** So a sweep of the stretch is a walk of the file: every cell it stops
at is some register's, which is what lets the sweep's pointer name the cell it is
writing. -/
theorem exists_ixSegCell_eq {I : Type} [Finite I] (ile : I → I → Prop)
    (h : IsLinOrd (WMLe (A := A))) (hi : IsLinOrd ile) {base : ℕ}
    (hbase : base + Nat.card I ≤ Nat.card {p : WPoint A // (wideData A).Posn p})
    {s : A → Prop} (h1 : base ≤ wideRank s) (h2 : wideRank s < base + Nat.card I) :
    ∃ u : I, ixSegCell ile h base u = s := by
  obtain ⟨u, hu⟩ := exists_ixRank_eq hi (k := wideRank s - base) (by omega)
  refine ⟨u, wideRank_injective h ?_⟩
  rw [wideRank_ixSegCell ile h hbase, hu]
  omega

/-- **The registers of the bottom file are exactly the addresses of rank between
`1` and `n`.** So the phase that builds the file walks the first `n` cells above
the empty address, writing at each the name of the element whose rank is one
below the cell's. -/
theorem exists_lowCell_eq (h : IsLinOrd (WMLe (A := A))) {s : A → Prop}
    (h1 : 1 ≤ wideRank s) (h2 : wideRank s ≤ Nat.card A) : ∃ u : A, lowCell h u = s := by
  obtain ⟨u, hu⟩ := exists_wmRank_eq h (k := wideRank s - 1) (by omega)
  refine ⟨u, wideRank_injective h ?_⟩
  rw [wideRank_lowCell, hu]
  omega

/-- **The file at the bottom lies in the initial stretch of `n + 1` addresses**:
everything the machine keeps above that stretch is out of its way. -/
theorem wideRank_lowCell_le (h : IsLinOrd (WMLe (A := A))) (u : A) :
    wideRank ((lowFile h).cell u) ≤ Nat.card A := by
  have h1 : wmRank u < Nat.card A := wmRank_lt_card u
  rw [cell_lowFile, wideRank_lowCell]
  omega

end LowFile

end DescriptiveComplexity
