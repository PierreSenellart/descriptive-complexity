/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawTable
import DescriptiveComplexity.Problems.Machine.DetRun

/-!
# A guessing program, deterministic after its guess

A reduction into `DescriptiveComplexity.WideAccept` has to read its certificate
off an **arbitrary** accepting run, so the program cannot be deterministic: its
guessing phase is exactly the place where two runs part. What makes the reading
survivable is that it parts there and nowhere else, and the notion that says so
is `DescriptiveComplexity.TMData.UniqueFrom` – every configuration reachable from
a given one has at most one successor – which all the read-off lemmas of
`DescriptiveComplexity.Problems.Machine.DetRun` are stated at.

This file joins the two halves. `DescriptiveComplexity.Draw.Table.SepOn` is the
program's obligation, discharged rule by rule as
`DescriptiveComplexity.Draw.Table.Sep` is; `hclosed` says the phases it separates
at are never left; and the conclusion is uniqueness from any configuration whose
state has one of those phases. Global determinism is the case `Ph = fun _ => True`,
where `hclosed` is free.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Table

variable {A R P K : Type} {c dd : ℕ} {T : Table A R P K c dd}
variable [LinearOrder R] [LinearOrder P] [LinearOrder K] [LinearOrder A]
variable [Language.wide.Structure (Univ A R P K dd)]
variable [Finite A] [Finite R] [Finite P] [Finite K]

/-- **A program that separates at the phases it can reach is unique from
there.** The invariant is "the state's phase satisfies `Ph`": a rule fired from
such a phase lands in one again by `hclosed`, and at such a state the transition
is pinned by `DescriptiveComplexity.Draw.Table.tr_unique_of_sepOn`. This is what a
*guessing* program has in place of determinism. -/
theorem uniqueFrom_of_sepOn (hR : T.Reads)
    (hlin : IsLinOrd (WMLe (A := Univ A R P K dd))) {Ph : P → Prop}
    (hsep : T.SepOn Ph) (hclosed : ∀ r : R, Ph (T.srcPh r) → Ph (T.dstPh r))
    {cfg : Config (WPoint (Univ A R P K dd))}
    (hcfg : ∀ (p : P) (f : Fin c → A), cfg.state = Sum.inr (stateElt T.zero p f) → Ph p) :
    (wideData (Univ A R P K dd)).UniqueFrom cfg := by
  refine TMData.uniqueFrom_of_invariant (Inv := fun x =>
    ∀ (p : P) (f : Fin c → A), x.state = Sum.inr (stateElt T.zero p f) → Ph p) ?_ ?_ hcfg
  · rintro x y hx ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ p f hy
    obtain (sτ | τ) := τ
    · exact hτ.elim
    rcases hxs : x.state with sx | qx
    · rw [hxs] at hsrc; exact hsrc.elim
    rcases hys : y.state with sy | qy
    · rw [hys] at hy; simp at hy
    rw [hxs] at hsrc
    rw [hys] at hdst hy
    have hτ' : T.IsTr τ := (hR.tr τ).mp hτ
    have hsrc' : T.Src τ qx := (hR.src τ qx).mp hsrc
    have hdst' : T.Dst τ qy := (hR.dst τ qy).mp hdst
    obtain ⟨t, v⟩ := τ
    match t with
    | .ctrl r =>
      have hsrcPh : Ph (T.srcPh r) := hx _ _ (by rw [hxs, hsrc'])
      exact (stateElt_inj T.payload_le (hdst'.symm.trans (Sum.inr_injective hy))).1 ▸
        hclosed r hsrcPh
  · intro x y z hx h₁ h₂
    refine TMData.step_functional_at (isLinOrd_wpLe hlin) ?_ ?_ ?_ h₁ h₂
    · rintro (sτ | τ) (sq | q) (sq' | q') hq hq' <;>
        first
          | exact hq.elim
          | exact hq'.elim
          | exact congrArg Sum.inr (T.dst_functional hR τ q q' hq hq')
    · rintro (sτ | τ) (sa | a) (sa' | a') ha ha' <;>
        first
          | exact ha.elim
          | exact ha'.elim
          | exact congrArg Sum.inr (T.write_functional hR τ a a' ha ha')
    · rintro (sτ | τ) (sσ | σ) hτ hσ hsrc hsrc' hread hread' <;>
        first
          | exact hτ.elim
          | exact hσ.elim
          | skip
      rcases hxs : x.state with sx | qx
      · rw [hxs] at hsrc; exact hsrc.elim
      rcases hxa : x.tape x.head with sa | qa
      · rw [hxa] at hread; exact hread.elim
      rw [hxs] at hsrc hsrc'
      rw [hxa] at hread hread'
      exact congrArg Sum.inr (T.tr_unique_of_sepOn hR hsep
        (fun p f hp => hx p f (by rw [hxs, hp])) τ σ hτ hσ hsrc hsrc' hread hread')

omit [Finite A] [Finite R] [Finite P] [Finite K] in
/-- **A configuration is stuck at a phase no rule fires from**: a step is a
transition whose source is the state, and a control transition's source is its
rule's phase, so a phase outside every rule's source has no successor. This is
what makes a *verdict* final: the accepting phase of a clocked program has no
rules, so an accepting configuration is a dead end and the run that reached it
is the whole run. -/
theorem stuck_of_srcPh (hR : T.Reads) {Ph : P → Prop}
    (hno : ∀ r : R, ¬Ph (T.srcPh r))
    {x : Config (WPoint (Univ A R P K dd))} {p : P} {f : Fin c → A}
    (hx : x.state = Sum.inr (stateElt T.zero p f)) (hp : Ph p) :
    ∀ y, ¬(wideData (Univ A R P K dd)).Step x y := by
  rintro y ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩
  obtain (sτ | τ) := τ
  · exact hτ.elim
  rw [hx] at hsrc
  have hτ' : T.IsTr τ := (hR.tr τ).mp hτ
  have hsrc' := (hR.src τ _).mp hsrc
  obtain ⟨t, v⟩ := τ
  match t with
  | .ctrl r =>
    exact hno r ((stateElt_inj T.payload_le hsrc').1 ▸ hp)


end Table

end Draw

end DescriptiveComplexity
