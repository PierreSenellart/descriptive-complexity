/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HaltHard.Tags

/-!
# The transition table of the simulating machine

The control of the machine `M(c)` that the RE-hardness of
`DescriptiveComplexity.HALT` draws, as one **deterministic step function**
`DescriptiveComplexity.HaltHard.simStep : SimQ c → SimSym c → Option (SimSym c × SimQ c × Bool)`
(the Boolean is “move right”). Determinism is what makes the backward
direction of the simulation a case analysis rather than an invariant hunt,
and the drawn machine's transition relations are read off the graph of this
function.

The tape layout is the one of `Tags.lean`: frames left of the fixed
separator `mid`, bounded by the movable `endL`; the value **mirrored** right
of `mid`, its head block ending at the movable `endR`, so that every
operation on the head of the value works at `endR` and grows into the blank
half-tape – no marker ever crosses a letter. The states fall into walk
families between the unique letters `endL`/`mid`/`endR`/headers:

* `retL`/`retR` – seek the top frame (or accept on `mid`); `retL` doubles as
  the start state, the head starting on `endL`;
* `nSeekL p`/`nSeekR p` – walk to `mid` and dispatch on the shape of
  `codeAt p`;
* `zGo`/`zEnd` – `zero'`: append a separator at `endR`;
* `suScan`/`suE₁`/`suE₂`/`suGo`/`suEnd`/`suBack`/`suKill` – `succ`: append a
  digit (a separator and a digit, if the value was empty), then erase every
  block but the head one;
* `tlGo`/`tlLook`/`tlOnes`/`tlRest` – `tail`: erase the head block at `endR`;
* `caGo p`/`caLook p`/`caRest p` – `case`: inspect and consume the head at
  `endR`, then dispatch a child;
* `cpFetch p`/`cpCar₁ p`/`cpCarC p`/`cpEndS p`/`cpBack p`/`cpHdr p`/
  `cpHdrS p`/`cpUnp p`/`cpUnp₂ p` – the one non-destructive copy (the `cons`
  push), priming letters and writing at `endL` by the endL-shift;
* `coHdr p`/`coHdrS p`, `fiHdr p`/`fiHdrS p` – the bare header pushes;
* `fxGo p`/`fxLook p`/`fxOnes p`/`fxRest p`/`fxDropL`/`fxDropR` – the `fix`
  pop: inspect the flag at `endR`, then keep or drop the frame;
* `swGo`/`swPeek`/`swCar₁`/`swCarC`/`swEndS`/`swRest`/`swHdr`/`swHdrS`/
  `swOut`/`swScan`/`swLast`/`swApp₁`/`swAppC`/`swAppS`/`swBack` – the
  `cons₁` pop: move the value into a fresh `cons₂` frame (consuming it at
  `endR`, so the frame stores it mirrored), then move the stored value out
  (consuming the frame at its right end, so the value region gets it
  mirrored);
* `ppGo`/`ppShift`/`ppBack`/`ppFind`/`ppScan`/`ppLast`/`ppCar`/`ppCarS`/
  `ppKill` – the `cons₂` pop: append a separator, transfer the digits of the
  frame's head block (sitting at the frame's right end, since the frame is
  mirrored), and discard the rest.
-/

namespace DescriptiveComplexity

namespace HaltHard

open Turing.ToPartrec

variable {c : Code}

/-- The states of the simulating machine; see the module docstring for the
role of each family. -/
inductive SimQ (c : Code) : Type
  /-- Walk left to `endL`, then look for the top frame. -/
  | retL
  /-- Walk right over the gap to the top frame; accept on `mid`. -/
  | retR
  /-- The accepting state. -/
  | acc
  /-- Walk left to `mid` and dispatch `stepNormal (codeAt p)`. -/
  | nSeekL : CPos c → SimQ c
  /-- Walk right to `mid` and dispatch `stepNormal (codeAt p)`. -/
  | nSeekR : CPos c → SimQ c
  /-- `zero'`: walk right to `endR`. -/
  | zGo
  /-- `zero'`: re-write `endR` one cell right of the appended separator. -/
  | zEnd
  /-- `succ`: from `mid`, look whether the value is empty. -/
  | suScan
  /-- `succ` on an empty value: a separator is appended; write the digit. -/
  | suE₁
  /-- `succ` on an empty value: re-write `endR`. -/
  | suE₂
  /-- `succ`: walk right to `endR`. -/
  | suGo
  /-- `succ`: re-write `endR` one cell right of the appended digit. -/
  | suEnd
  /-- `succ`: walk left over the head block's digits. -/
  | suBack
  /-- `succ`: erase everything between the head block and `mid`. -/
  | suKill
  /-- `tail`: walk right to `endR`. -/
  | tlGo
  /-- `tail`: look at the last letter of the value. -/
  | tlLook
  /-- `tail`: erase the head block's digits, then land `endR` on its
  separator. -/
  | tlOnes
  /-- `tail` on an empty value: re-write the erased `endR`. -/
  | tlRest
  /-- `case`: walk right to `endR`. -/
  | caGo : CPos c → SimQ c
  /-- `case`: look at the last letter of the value. -/
  | caLook : CPos c → SimQ c
  /-- `case` on an empty value: re-write the erased `endR`. -/
  | caRest : CPos c → SimQ c
  /-- `cons` push: find the next unprimed letter of the value. -/
  | cpFetch : CPos c → SimQ c
  /-- `cons` push: carry a digit to `endL`. -/
  | cpCar₁ : CPos c → SimQ c
  /-- `cons` push: carry a separator to `endL`. -/
  | cpCarC : CPos c → SimQ c
  /-- `cons` push: re-write `endL` one cell left. -/
  | cpEndS : CPos c → SimQ c
  /-- `cons` push: walk right back to `mid` before resuming the scan. -/
  | cpBack : CPos c → SimQ c
  /-- `cons` push: walk left to `endL` to write the frame header. -/
  | cpHdr : CPos c → SimQ c
  /-- `cons` push: re-write `endL` left of the header. -/
  | cpHdrS : CPos c → SimQ c
  /-- `cons` push: walk right to `mid` before unpriming. -/
  | cpUnp : CPos c → SimQ c
  /-- `cons` push: unprime the copied value. -/
  | cpUnp₂ : CPos c → SimQ c
  /-- `comp` push: walk left to `endL`. -/
  | coHdr : CPos c → SimQ c
  /-- `comp` push: re-write `endL` left of the header. -/
  | coHdrS : CPos c → SimQ c
  /-- `fix` push: walk left to `endL`. -/
  | fiHdr : CPos c → SimQ c
  /-- `fix` push: re-write `endL` left of the header. -/
  | fiHdrS : CPos c → SimQ c
  /-- `fix` pop: walk right to `endR`. -/
  | fxGo : CPos c → SimQ c
  /-- `fix` pop: look at the last letter of the value. -/
  | fxLook : CPos c → SimQ c
  /-- `fix` pop, nonzero flag: erase the head block's digits. -/
  | fxOnes : CPos c → SimQ c
  /-- `fix` pop on an empty value: re-write the erased `endR`. -/
  | fxRest : CPos c → SimQ c
  /-- `fix` pop, zero flag: walk left to `endL` to drop the frame. -/
  | fxDropL
  /-- `fix` pop, zero flag: walk right to the frame header and erase it. -/
  | fxDropR
  /-- `cons₁` pop: walk right to `endR`. -/
  | swGo
  /-- `cons₁` pop: look at the last letter of the value. -/
  | swPeek
  /-- `cons₁` pop: carry a digit to `endL`. -/
  | swCar₁
  /-- `cons₁` pop: carry a separator to `endL`. -/
  | swCarC
  /-- `cons₁` pop: re-write `endL` one cell left. -/
  | swEndS
  /-- `cons₁` pop: the value is spent; re-write the erased `endR`. -/
  | swRest
  /-- `cons₁` pop: walk left to `endL` to write the `cons₂` header. -/
  | swHdr
  /-- `cons₁` pop: re-write `endL` left of the header. -/
  | swHdrS
  /-- `cons₁` pop: walk right to the old frame's header. -/
  | swOut
  /-- `cons₁` pop: walk right over the old frame's content. -/
  | swScan
  /-- `cons₁` pop: consume the old frame's last letter. -/
  | swLast
  /-- `cons₁` pop: carry a digit to `endR`. -/
  | swApp₁
  /-- `cons₁` pop: carry a separator to `endR`. -/
  | swAppC
  /-- `cons₁` pop: re-write `endR` one cell right. -/
  | swAppS
  /-- `cons₁` pop: walk left to `endL` before re-entering the frame. -/
  | swBack
  /-- `cons₂` pop: walk right to `endR` to append the separator. -/
  | ppGo
  /-- `cons₂` pop: re-write `endR` one cell right. -/
  | ppShift
  /-- `cons₂` pop: walk left to `endL`. -/
  | ppBack
  /-- `cons₂` pop: walk right over the gap to the frame. -/
  | ppFind
  /-- `cons₂` pop: walk right over the frame's content. -/
  | ppScan
  /-- `cons₂` pop: consume the frame's last letter. -/
  | ppLast
  /-- `cons₂` pop: carry a digit to `endR`. -/
  | ppCar
  /-- `cons₂` pop: re-write `endR` one cell right. -/
  | ppCarS
  /-- `cons₂` pop: erase the spent frame. -/
  | ppKill

instance : Nonempty (SimQ c) := ⟨.retL⟩

/-- The states are finitely many: `CPos c` is finite and every family is
indexed by at most one position. -/
instance : Finite (SimQ c) := by
  refine Finite.of_injective (fun q : SimQ c =>
    (match q with
      | .retL => Sum.inl 0
      | .retR => Sum.inl 1
      | .acc => Sum.inl 2
      | .zGo => Sum.inl 3
      | .zEnd => Sum.inl 4
      | .suScan => Sum.inl 5
      | .suE₁ => Sum.inl 6
      | .suE₂ => Sum.inl 7
      | .suGo => Sum.inl 8
      | .suEnd => Sum.inl 9
      | .suBack => Sum.inl 10
      | .suKill => Sum.inl 11
      | .tlGo => Sum.inl 12
      | .tlLook => Sum.inl 13
      | .tlOnes => Sum.inl 14
      | .tlRest => Sum.inl 15
      | .fxDropL => Sum.inl 16
      | .fxDropR => Sum.inl 17
      | .swGo => Sum.inl 18
      | .swPeek => Sum.inl 19
      | .swCar₁ => Sum.inl 20
      | .swCarC => Sum.inl 21
      | .swEndS => Sum.inl 22
      | .swRest => Sum.inl 23
      | .swHdr => Sum.inl 24
      | .swHdrS => Sum.inl 25
      | .swOut => Sum.inl 26
      | .swScan => Sum.inl 27
      | .swLast => Sum.inl 28
      | .swApp₁ => Sum.inl 29
      | .swAppC => Sum.inl 30
      | .swAppS => Sum.inl 31
      | .swBack => Sum.inl 32
      | .ppGo => Sum.inl 33
      | .ppShift => Sum.inl 34
      | .ppBack => Sum.inl 35
      | .ppFind => Sum.inl 36
      | .ppScan => Sum.inl 37
      | .ppLast => Sum.inl 38
      | .ppCar => Sum.inl 39
      | .ppCarS => Sum.inl 40
      | .ppKill => Sum.inl 41
      | .nSeekL p => Sum.inr (0, p)
      | .nSeekR p => Sum.inr (1, p)
      | .caGo p => Sum.inr (2, p)
      | .caLook p => Sum.inr (3, p)
      | .caRest p => Sum.inr (4, p)
      | .cpFetch p => Sum.inr (5, p)
      | .cpCar₁ p => Sum.inr (6, p)
      | .cpCarC p => Sum.inr (7, p)
      | .cpEndS p => Sum.inr (8, p)
      | .cpBack p => Sum.inr (9, p)
      | .cpHdr p => Sum.inr (10, p)
      | .cpHdrS p => Sum.inr (11, p)
      | .cpUnp p => Sum.inr (12, p)
      | .cpUnp₂ p => Sum.inr (13, p)
      | .coHdr p => Sum.inr (14, p)
      | .coHdrS p => Sum.inr (15, p)
      | .fiHdr p => Sum.inr (16, p)
      | .fiHdrS p => Sum.inr (17, p)
      | .fxGo p => Sum.inr (18, p)
      | .fxLook p => Sum.inr (19, p)
      | .fxOnes p => Sum.inr (20, p)
      | .fxRest p => Sum.inr (21, p) :
      Fin 42 ⊕ (Fin 22 × CPos c))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- The dispatch of `stepNormal (codeAt p)`, with the head reading `mid`:
the first action of each shape's handler. -/
def dispatch (p : CPos c) : SimSym c × SimQ c × Bool :=
  match codeAt p with
  | .zero' => (.mid, .zGo, true)
  | .succ => (.mid, .suScan, true)
  | .tail => (.mid, .tlGo, true)
  | .cons _ _ => (.mid, .cpFetch p, true)
  | .comp _ _ => (.mid, .coHdr p, false)
  | .case _ _ => (.mid, .caGo p, true)
  | .fix _ => (.mid, .fiHdr p, false)

/-- **The deterministic step table** (`none` = no move; the Boolean is “move
right”). The docstring of the file names each family; within a family the
letter-specific actions come first and the walk catch-alls after. -/
def simStep : SimQ c → SimSym c → Option (SimSym c × SimQ c × Bool)
  -- seek the top frame
  | .retL, .endL => some (.endL, .retR, true)
  | .retL, σ => some (σ, .retL, false)
  | .retR, .bk => some (.bk, .retR, true)
  | .retR, .mid => some (.mid, .acc, true)
  | .retR, .hComp p => some (.bk, .nSeekR p, true)
  | .retR, .hFix p => some (.hFix p, .fxGo p, true)
  | .retR, .hCons₁ p => some (.hCons₁ p, .swGo, true)
  | .retR, .hCons₂ => some (.hCons₂, .ppGo, true)
  | .retR, _ => none
  | .acc, _ => none
  -- seek mid and dispatch
  | .nSeekL p, .mid => some (dispatch p)
  | .nSeekL p, σ => some (σ, .nSeekL p, false)
  | .nSeekR p, .mid => some (dispatch p)
  | .nSeekR p, σ => some (σ, .nSeekR p, true)
  -- zero': append a separator
  | .zGo, .endR => some (.com, .zEnd, true)
  | .zGo, σ => some (σ, .zGo, true)
  | .zEnd, .bk => some (.endR, .retL, false)
  | .zEnd, _ => none
  -- succ
  | .suScan, .bk => some (.bk, .suScan, true)
  | .suScan, .endR => some (.com, .suE₁, true)
  | .suScan, .one => some (.one, .suGo, true)
  | .suScan, .com => some (.com, .suGo, true)
  | .suScan, _ => none
  | .suE₁, .bk => some (.one, .suE₂, true)
  | .suE₁, _ => none
  | .suE₂, .bk => some (.endR, .retL, false)
  | .suE₂, _ => none
  | .suGo, .endR => some (.one, .suEnd, true)
  | .suGo, σ => some (σ, .suGo, true)
  | .suEnd, .bk => some (.endR, .suBack, false)
  | .suEnd, _ => none
  | .suBack, .one => some (.one, .suBack, false)
  | .suBack, .com => some (.com, .suKill, false)
  | .suBack, _ => none
  | .suKill, .one => some (.bk, .suKill, false)
  | .suKill, .com => some (.bk, .suKill, false)
  | .suKill, .bk => some (.bk, .suKill, false)
  | .suKill, .mid => some (.mid, .retL, false)
  | .suKill, _ => none
  -- tail
  | .tlGo, .endR => some (.bk, .tlLook, false)
  | .tlGo, σ => some (σ, .tlGo, true)
  | .tlLook, .one => some (.bk, .tlOnes, false)
  | .tlLook, .com => some (.endR, .retL, false)
  | .tlLook, .bk => some (.bk, .tlRest, true)
  | .tlLook, _ => none
  | .tlOnes, .one => some (.bk, .tlOnes, false)
  | .tlOnes, .com => some (.endR, .retL, false)
  | .tlOnes, _ => none
  | .tlRest, .bk => some (.endR, .retL, false)
  | .tlRest, _ => none
  -- case
  | .caGo p, .endR => some (.bk, .caLook p, false)
  | .caGo p, σ => some (σ, .caGo p, true)
  | .caLook p, .one => some (.endR, .nSeekL (c₂ p), false)
  | .caLook p, .com => some (.endR, .nSeekL (c₁ p), false)
  | .caLook p, .bk => some (.bk, .caRest p, true)
  | .caLook _, _ => none
  | .caRest p, .bk => some (.endR, .nSeekL (c₁ p), false)
  | .caRest _, _ => none
  -- cons push: prime-copy the value into a new frame at endL
  | .cpFetch p, .one => some (.one', .cpCar₁ p, false)
  | .cpFetch p, .com => some (.com', .cpCarC p, false)
  | .cpFetch p, .endR => some (.endR, .cpHdr p, false)
  | .cpFetch p, .one' => some (.one', .cpFetch p, true)
  | .cpFetch p, .com' => some (.com', .cpFetch p, true)
  | .cpFetch p, .bk => some (.bk, .cpFetch p, true)
  | .cpFetch _, _ => none
  | .cpCar₁ p, .endL => some (.one, .cpEndS p, false)
  | .cpCar₁ p, σ => some (σ, .cpCar₁ p, false)
  | .cpCarC p, .endL => some (.com, .cpEndS p, false)
  | .cpCarC p, σ => some (σ, .cpCarC p, false)
  | .cpEndS p, .bk => some (.endL, .cpBack p, true)
  | .cpEndS _, _ => none
  | .cpBack p, .mid => some (.mid, .cpFetch p, true)
  | .cpBack p, σ => some (σ, .cpBack p, true)
  | .cpHdr p, .endL => some (.hCons₁ (c₂ p), .cpHdrS p, false)
  | .cpHdr p, σ => some (σ, .cpHdr p, false)
  | .cpHdrS p, .bk => some (.endL, .cpUnp p, true)
  | .cpHdrS _, _ => none
  | .cpUnp p, .mid => some (.mid, .cpUnp₂ p, true)
  | .cpUnp p, σ => some (σ, .cpUnp p, true)
  | .cpUnp₂ p, .one' => some (.one, .cpUnp₂ p, true)
  | .cpUnp₂ p, .com' => some (.com, .cpUnp₂ p, true)
  | .cpUnp₂ p, .bk => some (.bk, .cpUnp₂ p, true)
  | .cpUnp₂ p, .endR => some (.endR, .nSeekL (c₁ p), false)
  | .cpUnp₂ _, _ => none
  -- comp push
  | .coHdr p, .endL => some (.hComp (c₁ p), .coHdrS p, false)
  | .coHdr p, σ => some (σ, .coHdr p, false)
  | .coHdrS p, .bk => some (.endL, .nSeekR (c₂ p), true)
  | .coHdrS _, _ => none
  -- fix push
  | .fiHdr p, .endL => some (.hFix (c₁ p), .fiHdrS p, false)
  | .fiHdr p, σ => some (σ, .fiHdr p, false)
  | .fiHdrS p, .bk => some (.endL, .nSeekR (c₁ p), true)
  | .fiHdrS _, _ => none
  -- fix pop
  | .fxGo p, .endR => some (.bk, .fxLook p, false)
  | .fxGo p, σ => some (σ, .fxGo p, true)
  | .fxLook p, .one => some (.bk, .fxOnes p, false)
  | .fxLook _, .com => some (.endR, .fxDropL, false)
  | .fxLook p, .bk => some (.bk, .fxRest p, true)
  | .fxLook _, _ => none
  | .fxOnes p, .one => some (.bk, .fxOnes p, false)
  | .fxOnes p, .com => some (.endR, .nSeekL p, false)
  | .fxOnes _, _ => none
  | .fxRest _, .bk => some (.endR, .fxDropL, false)
  | .fxRest _, _ => none
  | .fxDropL, .endL => some (.endL, .fxDropR, true)
  | .fxDropL, σ => some (σ, .fxDropL, false)
  | .fxDropR, .bk => some (.bk, .fxDropR, true)
  | .fxDropR, .hFix _ => some (.bk, .retL, false)
  | .fxDropR, _ => none
  -- cons₁ pop, phase one: move the value into a fresh mirrored cons₂ frame
  | .swGo, .endR => some (.bk, .swPeek, false)
  | .swGo, σ => some (σ, .swGo, true)
  | .swPeek, .one => some (.endR, .swCar₁, false)
  | .swPeek, .com => some (.endR, .swCarC, false)
  | .swPeek, .bk => some (.bk, .swRest, true)
  | .swPeek, _ => none
  | .swRest, .bk => some (.endR, .swHdr, false)
  | .swRest, _ => none
  | .swCar₁, .endL => some (.one, .swEndS, false)
  | .swCar₁, σ => some (σ, .swCar₁, false)
  | .swCarC, .endL => some (.com, .swEndS, false)
  | .swCarC, σ => some (σ, .swCarC, false)
  | .swEndS, .bk => some (.endL, .swGo, true)
  | .swEndS, _ => none
  | .swHdr, .endL => some (.hCons₂, .swHdrS, false)
  | .swHdr, σ => some (σ, .swHdr, false)
  | .swHdrS, .bk => some (.endL, .swOut, true)
  | .swHdrS, _ => none
  -- cons₁ pop, phase two: move the stored value out to endR
  | .swOut, .hCons₁ p => some (.hCons₁ p, .swScan, true)
  | .swOut, σ => some (σ, .swOut, true)
  | .swScan, .one => some (.one, .swScan, true)
  | .swScan, .com => some (.com, .swScan, true)
  | .swScan, σ => some (σ, .swLast, false)
  | .swLast, .one => some (.bk, .swApp₁, true)
  | .swLast, .com => some (.bk, .swAppC, true)
  | .swLast, .hCons₁ p => some (.bk, .nSeekR p, true)
  | .swLast, _ => none
  | .swApp₁, .endR => some (.one, .swAppS, true)
  | .swApp₁, σ => some (σ, .swApp₁, true)
  | .swAppC, .endR => some (.com, .swAppS, true)
  | .swAppC, σ => some (σ, .swAppC, true)
  | .swAppS, .bk => some (.endR, .swBack, false)
  | .swAppS, _ => none
  | .swBack, .endL => some (.endL, .swOut, true)
  | .swBack, σ => some (σ, .swBack, false)
  -- cons₂ pop
  | .ppGo, .endR => some (.com, .ppShift, true)
  | .ppGo, σ => some (σ, .ppGo, true)
  | .ppShift, .bk => some (.endR, .ppBack, false)
  | .ppShift, _ => none
  | .ppBack, .endL => some (.endL, .ppFind, true)
  | .ppBack, σ => some (σ, .ppBack, false)
  | .ppFind, .bk => some (.bk, .ppFind, true)
  | .ppFind, .hCons₂ => some (.hCons₂, .ppScan, true)
  | .ppFind, _ => none
  | .ppScan, .one => some (.one, .ppScan, true)
  | .ppScan, .com => some (.com, .ppScan, true)
  | .ppScan, σ => some (σ, .ppLast, false)
  | .ppLast, .one => some (.bk, .ppCar, true)
  | .ppLast, .com => some (.bk, .ppKill, false)
  | .ppLast, .hCons₂ => some (.bk, .retL, false)
  | .ppLast, _ => none
  | .ppCar, .endR => some (.one, .ppCarS, true)
  | .ppCar, σ => some (σ, .ppCar, true)
  | .ppCarS, .bk => some (.endR, .ppBack, false)
  | .ppCarS, _ => none
  | .ppKill, .one => some (.bk, .ppKill, false)
  | .ppKill, .com => some (.bk, .ppKill, false)
  | .ppKill, .hCons₂ => some (.bk, .retL, false)
  | .ppKill, _ => none

end HaltHard

end DescriptiveComplexity
