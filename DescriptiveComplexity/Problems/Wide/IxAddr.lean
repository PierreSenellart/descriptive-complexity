/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.Increment

/-!
# The address a file's marks stand for

A program that seeks to a computed address holds that address on its **file**,
one bit per register, and holds the address under its head there too – the
*mirror*. At the elementwise file that is nothing to say: a register is an
element, a mark on the registers *is* an address. At a coarser file it is
something to say, and this file says it.

`DescriptiveComplexity.ixAddr` is the address a mark on the index stands for –
each register carries the bit of one element (`elt`) – and
`DescriptiveComplexity.ixMark` is the mark a file keeps of an address, its bits
at the registers. The two are inverse on the addresses a file **can** hold
(`DescriptiveComplexity.IxHolds`), and what makes the correspondence useful is
that it carries the order, under three conditions:

* `elt` is injective and an order embedding (`hinj`, `hmono`), so comparing
  marks and comparing addresses is the same comparison;
* the elements it names are **upward closed** (`hup`): above one of them there
  is nothing the file has no register for. The addresses over them are then
  downward closed – an initial interval of the tape
  (`DescriptiveComplexity.ixHolds_of_wmSetLe`) – which is what makes an
  increment of the addresses an increment of the marks, with no address in
  between that the file could not have represented.

For a clocked program's file all three hold of the argument registers, because
the argument tags are the *last* ones (`DescriptiveComplexity.Pfp.lt_arg`) and
therefore the least significant: the addresses over them are the logical ones.
-/

namespace DescriptiveComplexity

section IxAddr

variable {A I : Type} {ile : I → I → Prop} {Le : A → A → Prop}

/-- **The address a mark on a file's index stands for**: the elements whose
register is marked. -/
def ixAddr (elt : I → A) (m : I → Prop) : A → Prop := fun x => ∃ u, elt u = x ∧ m u

/-- **The mark a file keeps of an address**: its bits at the registers. -/
def ixMark (elt : I → A) (s : A → Prop) : I → Prop := fun u => s (elt u)

variable {elt : I → A} {Use : I → Prop}

/-- **An address a file can hold**: every element of it is one of the file's. -/
def IxHolds (elt : I → A) (Use : I → Prop) (s : A → Prop) : Prop :=
  ∀ x, s x → ∃ u, Use u ∧ elt u = x

theorem ixAddr_elt (hinj : Function.Injective elt) (m : I → Prop) (u : I) :
    ixAddr elt m (elt u) ↔ m u :=
  ⟨fun ⟨_u', he, hm⟩ => hinj he ▸ hm, fun h => ⟨u, rfl, h⟩⟩

theorem not_ixAddr_of_not_elt {m : I → Prop} {x : A} (h : ∀ u, m u → elt u ≠ x) :
    ¬ixAddr elt m x := by
  rintro ⟨u, he, hm⟩
  exact h u hm he

/-- **A file's mark of an address stands for that address**, when the file has a
register for each of its elements. -/
theorem ixAddr_ixMark {s : A → Prop} (hs : IxHolds elt Use s) :
    ixAddr elt (ixMark elt s) = s := by
  funext x
  refine propext ⟨fun ⟨_u, he, hm⟩ => he ▸ hm, fun hx => ?_⟩
  obtain ⟨u, -, he⟩ := hs x hx
  exact ⟨u, he, by change s (elt u); rw [he]; exact hx⟩

/-- **A mark is the mark of the address it stands for.** -/
theorem ixMark_ixAddr (hinj : Function.Injective elt) (m : I → Prop) :
    ixMark elt (ixAddr elt m) = m :=
  funext fun u => propext (ixAddr_elt hinj m u)

/-- **The address of a mark is one the file can hold.** -/
theorem ixHolds_ixAddr {m : I → Prop} (hm : ∀ u, m u → Use u) :
    IxHolds elt Use (ixAddr elt m) := fun _x ⟨u, he, hmu⟩ => ⟨u, hm u hmu, he⟩

/-- **The empty address is one every file can hold.** -/
theorem ixHolds_empty : IxHolds elt Use (fun _ => False) := fun _ h => h.elim

theorem ixMark_empty : ixMark elt (fun _ : A => False) = fun _ => False := rfl

theorem ixAddr_empty : ixAddr elt (fun _ : I => False) = fun _ : A => False :=
  funext fun _ => propext ⟨fun ⟨_, _, h⟩ => h, fun h => h.elim⟩

variable (hinj : Function.Injective elt)
variable (hmono : ∀ u u', WMLt ile u u' ↔ WMLt Le (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : A), Use u → WMLt Le (elt u) x → ∃ u', Use u' ∧ elt u' = x)

include hup in
/-- **The addresses a file can hold are downward closed**: below one of them,
every element is either one the file already has a register for, or one above
such an element – and above is where the file's elements are. -/
theorem ixHolds_of_wmSetLe (hLe : IsLinOrd Le) {s t : A → Prop}
    (hs : IxHolds elt Use t) (h : WMSetLe Le s t) : IxHolds elt Use s := by
  intro x hx
  rcases h with heq | ⟨y, hagree, hny, hty⟩
  · exact hs x ((heq x).mp hx)
  · obtain ⟨uy, huy, rfl⟩ := hs y hty
    rcases em (WMLt Le x (elt uy)) with hlt | hnlt
    · exact hs x ((hagree x hlt).mp hx)
    · rcases em (WMLt Le (elt uy) x) with hgt | hngt
      · exact hup uy x huy hgt
      · exact absurd (eq_of_not_wmLt hLe hnlt hngt ▸ hx) hny

include hinj hmono in
/-- **Comparing marks is comparing the addresses they stand for**, strictly. -/
theorem wmSetLt_ixAddr (m m' : I → Prop) :
    WMSetLt ile m m' ↔ WMSetLt Le (ixAddr elt m) (ixAddr elt m') := by
  constructor
  · rintro ⟨u, hagree, hnm, hm'u⟩
    refine ⟨elt u, fun y hy => ?_, ?_, ⟨u, rfl, hm'u⟩⟩
    · by_cases hy' : ∃ u', elt u' = y
      · obtain ⟨u', rfl⟩ := hy'
        rw [ixAddr_elt hinj, ixAddr_elt hinj]
        exact hagree u' ((hmono u' u).mpr hy)
      · constructor
        · rintro ⟨u', rfl, -⟩; exact absurd ⟨u', rfl⟩ hy'
        · rintro ⟨u', rfl, -⟩; exact absurd ⟨u', rfl⟩ hy'
    · rw [ixAddr_elt hinj]; exact hnm
  · rintro ⟨x, hagree, hnx, hx⟩
    obtain ⟨u, rfl, hmu⟩ := hx
    refine ⟨u, fun v hv => ?_, ?_, hmu⟩
    · have h := hagree (elt v) ((hmono v u).mp hv)
      rwa [ixAddr_elt hinj, ixAddr_elt hinj] at h
    · rw [← ixAddr_elt hinj m u]; exact hnx

include hinj hmono in
/-- **Comparing marks is comparing the addresses they stand for.** -/
theorem wmSetLe_ixAddr (m m' : I → Prop) :
    WMSetLe ile m m' ↔ WMSetLe Le (ixAddr elt m) (ixAddr elt m') := by
  rw [wmSetLe_iff_wmSetLt, wmSetLe_iff_wmSetLt, wmSetLt_ixAddr hinj hmono]
  refine or_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
  · rw [show m = m' from funext fun u => propext (h u)]
    exact fun _ => Iff.rfl
  · intro u
    have hx := h (elt u)
    rwa [ixAddr_elt hinj, ixAddr_elt hinj] at hx

include hinj hmono in
/-- **An increment of the addresses is an increment of the marks**: the carry is
an element the file has a register for, and so is everything above it. -/
theorem wmIncr_ixMark {s s' : A → Prop} (hs' : IxHolds elt Use s')
    (hi : WMIncr Le s s') : WMIncr ile (ixMark elt s) (ixMark elt s') := by
  obtain ⟨x, hnx, habove, hnext⟩ := hi
  obtain ⟨u, _hu, rfl⟩ := hs' x ((hnext x).mpr (Or.inl rfl))
  refine ⟨u, hnx, fun v hv => habove (elt v) ((hmono u v).mp hv), fun v => ?_⟩
  constructor
  · intro hv
    rcases (hnext (elt v)).mp hv with he | ⟨hsv, hnlt⟩
    · exact Or.inl (hinj he)
    · exact Or.inr ⟨hsv, fun hc => hnlt ((hmono u v).mp hc)⟩
  · rintro (rfl | ⟨hsv, hnlt⟩)
    · exact (hnext (elt v)).mpr (Or.inl rfl)
    · exact (hnext (elt v)).mpr (Or.inr ⟨hsv, fun hc => hnlt ((hmono u v).mpr hc)⟩)

include hinj hmono hup in
/-- **An increment of the marks is an increment of the addresses**, the same
correspondence read the other way. -/
theorem wmIncr_ixAddr {m m' : I → Prop} (hm' : ∀ u, m' u → Use u)
    (hi : WMIncr ile m m') : WMIncr Le (ixAddr elt m) (ixAddr elt m') := by
  obtain ⟨u, hnu, habove, hnext⟩ := hi
  refine ⟨elt u, ?_, ?_, ?_⟩
  · rw [ixAddr_elt hinj]; exact hnu
  · intro y hy
    obtain ⟨v, _hv, rfl⟩ := hup u y (hm' u ((hnext u).mpr (Or.inl rfl))) hy
    rw [ixAddr_elt hinj]
    exact habove v ((hmono u v).mpr hy)
  · intro y
    constructor
    · rintro ⟨v, rfl, hmv⟩
      rcases (hnext v).mp hmv with rfl | ⟨hmv', hnlt⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨v, rfl, hmv'⟩, fun hc => hnlt ((hmono u v).mpr hc)⟩
    · rintro (rfl | ⟨⟨v, rfl, hmv⟩, hnlt⟩)
      · exact ⟨u, rfl, (hnext u).mpr (Or.inl rfl)⟩
      · exact ⟨v, rfl, (hnext v).mpr (Or.inr ⟨hmv, fun hc => hnlt ((hmono u v).mp hc)⟩)⟩

/-- **At the elementwise file the address is the mark**: a register is an
element, so the correspondence is the identity and every statement here is the
one the space-bounded program already had. -/
theorem ixAddr_id (m : A → Prop) : ixAddr (id : A → A) m = m :=
  funext fun x => propext ⟨fun ⟨_, he, hm⟩ => he ▸ hm, fun h => ⟨x, rfl, h⟩⟩

theorem ixMark_id (s : A → Prop) : ixMark (id : A → A) s = s := rfl

end IxAddr

end DescriptiveComplexity
