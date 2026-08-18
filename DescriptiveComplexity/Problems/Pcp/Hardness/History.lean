/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

/-!
# Computation histories as dominoes

The combinatorial core of the RE-hardness of `DescriptiveComplexity.PCP`: a
string-rewriting system has a derivation from its start word to the halting
word exactly when a certain list of domino pairs has a match. Nothing here
mentions a structure or a formula – the first-order side reads this file's
`DescriptiveComplexity.Pcp.History.HasMatch` off an instance.

## The system

A rewriting system is a relation `Rule` between words over an alphabet `Γ`;
one step (`DescriptiveComplexity.Pcp.History.Step`) replaces a left-hand side
by a right-hand side somewhere in the word, and
`DescriptiveComplexity.Pcp.History.Derives` is its reflexive-transitive
closure. The question the dominoes answer is whether the start word `C₀`
derives the one-letter word `[halt]`.

## The dominoes, and the two things the construction has to arrange

A match is read left to right as a *queue*: the unmatched overhang is a word,
each domino consumes its top from the front of the overhang and appends its
bottom at the back, and the whole history `⊳C₀#C₁#…#Cₙ#` is spelt out by the
bottom words one configuration ahead of the top words. Two things have to be
arranged for that reading to be forced.

* **The match must start with the start domino.** Every word is *decorated*
  (`DescriptiveComplexity.Pcp.History.starL` puts a `star` before each letter,
  `DescriptiveComplexity.Pcp.History.starR` after each), so every top begins
  with `star` and every bottom begins with a letter that is not `star` –
  except the start domino's, which begins with `star` as well. Since the first
  domino of a match has its two words beginning alike, it can only be that
  one. This is why every right-hand side of a rule is required to be nonempty
  (`DescriptiveComplexity.Pcp.History.Ok`): a domino with an empty bottom
  would escape the argument, and it is exactly the domino the undecorated
  construction needs to close the match. Here the closing domino swallows
  `halt`, the separator and the `dia` in one piece instead, and its bottom is
  the single letter `dia`.
* **The start domino must not reappear.** Its top is the marker `tri`, which
  no other domino writes, so it can never be consumed again.

The alignment is then algebra: `starL` and `starR` are homomorphisms, and
`starL w ++ [star] = star :: starR w` is the half-letter offset that makes the
top and the bottom of a match spell the same word.
-/

namespace DescriptiveComplexity

namespace Pcp

namespace History

/-! ### The decorated alphabet -/

/-- The alphabet of the domino words: the letters of the rewriting system, the
separator between two configurations of a history, the decoration `star`, the
marker `tri` opening a history and the marker `dia` closing a match. -/
inductive Letter (Γ : Type) where
  /-- A letter of the rewriting system. -/
  | sym : Γ → Letter Γ
  /-- The separator between two configurations. -/
  | sep : Letter Γ
  /-- The decoration, which forces the alignment of a match. -/
  | star : Letter Γ
  /-- The opening marker, which forces the first domino of a match. -/
  | tri : Letter Γ
  /-- The closing marker. -/
  | dia : Letter Γ

variable {Γ : Type}

/-- Two different constructors of the alphabet are never equal; the shape in
which the case analyses below need it. -/
theorem absurd_of_ne {P : Prop} {a b : Letter Γ} (h : a = b)
    (hne : a ≠ b := by simp) : P := absurd h hne

/-- A word of the rewriting system, as a word of the alphabet above. -/
def symW (w : List Γ) : List (Letter Γ) := w.map Letter.sym

@[simp] theorem symW_nil : symW ([] : List Γ) = [] := rfl

@[simp] theorem symW_cons (a : Γ) (w : List Γ) : symW (a :: w) = Letter.sym a :: symW w := rfl

@[simp] theorem symW_append (w w' : List Γ) : symW (w ++ w') = symW w ++ symW w' := by
  simp [symW]

theorem sep_not_mem_symW (w : List Γ) : Letter.sep ∉ symW w := by
  induction w with
  | nil => simp
  | cons a w ih => simpa using fun h => ih h

/-- The word `w` decorated on the left: a `star` before each of its letters. -/
def starL : List (Letter Γ) → List (Letter Γ)
  | [] => []
  | a :: w => Letter.star :: a :: starL w

/-- The word `w` decorated on the right: a `star` after each of its letters. -/
def starR : List (Letter Γ) → List (Letter Γ)
  | [] => []
  | a :: w => a :: Letter.star :: starR w

@[simp] theorem starL_nil : starL ([] : List (Letter Γ)) = [] := rfl

@[simp] theorem starL_cons (a : Letter Γ) (w : List (Letter Γ)) :
    starL (a :: w) = Letter.star :: a :: starL w := rfl

@[simp] theorem starR_nil : starR ([] : List (Letter Γ)) = [] := rfl

@[simp] theorem starR_cons (a : Letter Γ) (w : List (Letter Γ)) :
    starR (a :: w) = a :: Letter.star :: starR w := rfl

@[simp] theorem starL_append (w w' : List (Letter Γ)) :
    starL (w ++ w') = starL w ++ starL w' := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

@[simp] theorem starR_append (w w' : List (Letter Γ)) :
    starR (w ++ w') = starR w ++ starR w' := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

/-- **The half-letter offset**: decorating on the left and closing with a
`star` is decorating on the right and opening with one. This one identity is
what makes the top and the bottom words of a match spell the same word. -/
theorem starL_star (w : List (Letter Γ)) :
    starL w ++ [Letter.star] = Letter.star :: starR w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- **One decorated word is a prefix of the other.** Two decorated words
opening a common word are comparable, and the longer one continues with the
decoration of the difference. -/
theorem starL_prefix_cases : ∀ (y z S S' : List (Letter Γ)),
    starL y ++ S = starL z ++ S' →
    (∃ t, z = y ++ t ∧ S = starL t ++ S') ∨ (∃ t, y = z ++ t ∧ starL t ++ S = S')
  | [], z, S, S', h => Or.inl ⟨z, by simp, by simpa using h⟩
  | a :: y, [], S, S', h => Or.inr ⟨a :: y, by simp, by simpa using h⟩
  | a :: y, b :: z, S, S', h => by
    have h' : a = b ∧ starL y ++ S = starL z ++ S' := by simpa using h
    obtain ⟨hab, h''⟩ := h'
    subst hab
    rcases starL_prefix_cases y z S S' h'' with ⟨t, rfl, ht⟩ | ⟨t, rfl, ht⟩
    · exact Or.inl ⟨t, by simp, ht⟩
    · exact Or.inr ⟨t, by simp, ht⟩

/-! ### The rewriting system -/

variable (Rule : List Γ → List Γ → Prop)

/-- **One rewriting step**: a left-hand side of a rule, somewhere in the word,
replaced by its right-hand side. -/
def Step (u v : List Γ) : Prop :=
  ∃ x l r y, Rule l r ∧ u = x ++ l ++ y ∧ v = x ++ r ++ y

/-- **Derivability**: any number of rewriting steps. -/
abbrev Derives : List Γ → List Γ → Prop := Relation.ReflTransGen (Step Rule)

variable {Rule}

theorem Step.congr {u v : List Γ} (h : Step Rule u v) (x y : List Γ) :
    Step Rule (x ++ u ++ y) (x ++ v ++ y) := by
  obtain ⟨x', l, r, y', hr, rfl, rfl⟩ := h
  exact ⟨x ++ x', l, r, y' ++ y, hr, by simp, by simp⟩

theorem Derives.congr {u v : List Γ} (h : Derives Rule u v) (x y : List Γ) :
    Derives Rule (x ++ u ++ y) (x ++ v ++ y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.congr x y)

/-- **Simultaneous rewriting**: any number of rules applied at once, at
disjoint places. It is what the dominoes between two separators perform, and it
derives no more than one rule at a time does
(`DescriptiveComplexity.Pcp.History.ParStep.derives`). -/
inductive ParStep (Rule : List Γ → List Γ → Prop) : List Γ → List Γ → Prop
  /-- The empty word rewrites to itself. -/
  | nil : ParStep Rule [] []
  /-- A letter may be kept. -/
  | keep (a : Γ) {u v : List Γ} : ParStep Rule u v → ParStep Rule (a :: u) (a :: v)
  /-- A rule may be applied. -/
  | rule {l r u v : List Γ} : Rule l r → ParStep Rule u v → ParStep Rule (l ++ u) (r ++ v)

theorem ParStep.derives {u v : List Γ} (h : ParStep Rule u v) : Derives Rule u v := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | keep a _ ih => simpa using ih.congr [a] []
  | @rule l r u v hr _ ih =>
    refine Relation.ReflTransGen.head (b := r ++ u) ⟨[], l, r, u, hr, by simp, by simp⟩ ?_
    simpa using ih.congr r []

theorem ParStep.snoc_keep {u v : List Γ} (h : ParStep Rule u v) (a : Γ) :
    ParStep Rule (u ++ [a]) (v ++ [a]) := by
  induction h with
  | nil => simpa using (ParStep.nil (Rule := Rule)).keep a
  | keep b _ ih => simpa using ih.keep b
  | rule hr _ ih => simpa using ih.rule hr

theorem ParStep.snoc_rule {u v l r : List Γ} (h : ParStep Rule u v) (hr : Rule l r) :
    ParStep Rule (u ++ l) (v ++ r) := by
  induction h with
  | nil => simpa using (ParStep.nil (Rule := Rule)).rule hr
  | keep b _ ih => simpa using ih.keep b
  | rule hr' _ ih => simpa using ih.rule hr'

/-! ### The dominoes -/

/-- A domino of the construction: the one that opens a history, one that
copies a letter, one that copies a separator, one per rule, and the one that
closes a match. -/
inductive Dom (Γ : Type) where
  /-- Opens the history, writing the start word. -/
  | start : Dom Γ
  /-- Copies a letter into the next configuration. -/
  | copy : Γ → Dom Γ
  /-- Copies the separator between two configurations. -/
  | copySep : Dom Γ
  /-- Applies a rule. -/
  | rule : List Γ → List Γ → Dom Γ
  /-- Closes the match on the halting configuration. -/
  | close : Dom Γ

variable (Rule) in
/-- **A domino belongs to the system**: only its rule dominoes are
constrained, and only by the rule they apply – whose two sides must be
nonempty, so that no top and no bottom word is empty. -/
def Ok : Dom Γ → Prop
  | .rule l r => Rule l r ∧ l ≠ [] ∧ r ≠ []
  | _ => True

/-- The top word of a domino. -/
def topW (halt : Γ) : Dom Γ → List (Letter Γ)
  | .start => starL [Letter.tri]
  | .copy a => starL [Letter.sym a]
  | .copySep => starL [Letter.sep]
  | .rule l _ => starL (symW l)
  | .close => starL [Letter.sym halt, Letter.sep] ++ [Letter.star, Letter.dia]

/-- The bottom word of a domino. -/
def botW (C₀ : List Γ) : Dom Γ → List (Letter Γ)
  | .start => Letter.star :: starR (Letter.tri :: (symW C₀ ++ [Letter.sep]))
  | .copy a => starR [Letter.sym a]
  | .copySep => starR [Letter.sep]
  | .rule _ r => starR (symW r)
  | .close => [Letter.dia]

/-- The word spelt by the top of a list of dominoes. -/
def tops (halt : Γ) (l : List (Dom Γ)) : List (Letter Γ) := (l.map (topW halt)).flatten

/-- The word spelt by the bottom of a list of dominoes. -/
def bots (C₀ : List Γ) (l : List (Dom Γ)) : List (Letter Γ) := (l.map (botW C₀)).flatten

@[simp] theorem tops_nil (halt : Γ) : tops halt ([] : List (Dom Γ)) = [] := rfl

@[simp] theorem tops_cons (halt : Γ) (d : Dom Γ) (l : List (Dom Γ)) :
    tops halt (d :: l) = topW halt d ++ tops halt l := rfl

@[simp] theorem bots_nil (C₀ : List Γ) : bots C₀ ([] : List (Dom Γ)) = [] := rfl

@[simp] theorem bots_cons (C₀ : List Γ) (d : Dom Γ) (l : List (Dom Γ)) :
    bots C₀ (d :: l) = botW C₀ d ++ bots C₀ l := rfl

@[simp] theorem tops_append (halt : Γ) (l l' : List (Dom Γ)) :
    tops halt (l ++ l') = tops halt l ++ tops halt l' := by
  simp [tops]

@[simp] theorem bots_append (C₀ : List Γ) (l l' : List (Dom Γ)) :
    bots C₀ (l ++ l') = bots C₀ l ++ bots C₀ l' := by
  simp [bots]

variable (Rule) in
/-- **The system has a match**: a nonempty list of its dominoes whose top
words and whose bottom words spell the same word. -/
def HasMatch (C₀ : List Γ) (halt : Γ) : Prop :=
  ∃ l : List (Dom Γ), l ≠ [] ∧ (∀ d ∈ l, Ok Rule d) ∧ tops halt l = bots C₀ l

/-! ### From a derivation to a match

The dominoes of one rewriting step copy the word on both sides of the rule and
apply the rule in the middle, so they consume one configuration and its
separator and write the next one and its separator. Chaining them writes the
whole history; the start domino opens it and the closing domino swallows the
last configuration. -/

section Forward

variable {C₀ : List Γ} {halt : Γ}

/-- The dominoes copying a word letter by letter. -/
def copies (w : List Γ) : List (Dom Γ) := w.map Dom.copy

theorem ok_copies (w : List Γ) : ∀ d ∈ copies w, Ok Rule d := by
  intro d hd
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hd
  trivial

@[simp] theorem tops_copies (w : List Γ) : tops halt (copies w) = starL (symW w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hc : copies (a :: w) = Dom.copy a :: copies w := rfl
    rw [hc, tops_cons, ih]
    simp [topW]

@[simp] theorem bots_copies (w : List Γ) : bots C₀ (copies w) = starR (symW w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hc : copies (a :: w) = Dom.copy a :: copies w := rfl
    rw [hc, bots_cons, ih]
    simp [botW]

/-- **The dominoes of one step**: they consume a configuration and its
separator, and write the next configuration and its separator. -/
theorem exists_block (hne : ∀ l r, Rule l r → l ≠ [] ∧ r ≠ []) {u v : List Γ} (h : Step Rule u v) :
    ∃ ds : List (Dom Γ), (∀ d ∈ ds, Ok Rule d) ∧
      tops halt ds = starL (symW u ++ [Letter.sep]) ∧
      bots C₀ ds = starR (symW v ++ [Letter.sep]) := by
  obtain ⟨x, l, r, y, hr, rfl, rfl⟩ := h
  refine ⟨copies x ++ Dom.rule l r :: (copies y ++ [Dom.copySep]), ?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ok_copies _ d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨hr, (hne _ _ hr).1, (hne _ _ hr).2⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact ok_copies _ d hd
    · have : d = Dom.copySep := by simpa using hd
      subst this
      trivial
  · simp [topW]
  · simp [botW]

/-- **The dominoes of a derivation**: they consume every configuration but the
last, and write every configuration but the first, so the word they consume and
the word they write are the same history read one configuration apart. -/
theorem exists_run (hne : ∀ l r, Rule l r → l ≠ [] ∧ r ≠ []) {u v : List Γ} (h : Derives Rule u v) :
    ∃ (ds : List (Dom Γ)) (T B : List (Letter Γ)), (∀ d ∈ ds, Ok Rule d) ∧
      tops halt ds = starL T ∧ bots C₀ ds = starR B ∧
      symW u ++ [Letter.sep] ++ B = T ++ (symW v ++ [Letter.sep]) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], [], [], by simp, by simp, by simp, by simp⟩
  | @head b c hstep _ ih =>
    obtain ⟨ds, T, B, hok, htop, hbot, heq⟩ := ih
    obtain ⟨es, hok', htop', hbot'⟩ := exists_block (C₀ := C₀) (halt := halt) hne hstep
    refine ⟨es ++ ds, (symW b ++ [Letter.sep]) ++ T, (symW c ++ [Letter.sep]) ++ B, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hok' d hd
      · exact hok d hd
    · simp [htop, htop']
    · simp [hbot, hbot']
    · simp only [List.append_assoc] at heq ⊢
      rw [heq]

/-- **A derivation gives a match.** -/
theorem hasMatch_of_derives (hne : ∀ l r, Rule l r → l ≠ [] ∧ r ≠ [])
    (h : Derives Rule C₀ [halt]) : HasMatch Rule C₀ halt := by
  obtain ⟨ds, T, B, hok, htop, hbot, heq⟩ :=
    exists_run (C₀ := C₀) (halt := halt) hne h
  refine ⟨Dom.start :: (ds ++ [Dom.close]), by simp, ?_, ?_⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · trivial
    rcases List.mem_append.mp hd with hd | hd
    · exact hok d hd
    · have : d = Dom.close := by simpa using hd
      subst this
      trivial
  · have heq' : symW C₀ ++ [Letter.sep] ++ B = T ++ [Letter.sym halt, Letter.sep] := by
      simpa [symW] using heq
    have hL : tops halt (Dom.start :: (ds ++ [Dom.close])) =
        starL (Letter.tri :: (symW C₀ ++ [Letter.sep] ++ B)) ++ [Letter.star] ++ [Letter.dia] := by
      rw [tops_cons, tops_append, htop, heq']
      simp [topW]
    have hR : bots C₀ (Dom.start :: (ds ++ [Dom.close])) =
        (Letter.star :: starR (Letter.tri :: (symW C₀ ++ [Letter.sep] ++ B))) ++ [Letter.dia] := by
      rw [bots_cons, bots_append, hbot]
      simp [botW]
    rw [hL, hR, starL_star]

end Forward

/-! ### From a match to a derivation

A match is read as a queue: the overhang is a word `β # γ`, where `β` is what
is left of the configuration being consumed and `γ` what has been written of
the next one, and every domino takes its top off the front of the overhang and
puts its bottom at the back. The invariant below says exactly that the queue
belongs to a history, and each domino preserves it. -/
section Backward

variable {C₀ : List Γ} {halt : Γ}

/-! The top word of a domino is the decoration of the word it takes off the
queue, followed by what it carries past the queue – nothing, except for the
closing domino, which carries the two letters that end a match. -/

/-- The undecorated word a domino takes off the queue. -/
def topUW (halt : Γ) : Dom Γ → List (Letter Γ)
  | .start => [Letter.tri]
  | .copy a => [Letter.sym a]
  | .copySep => [Letter.sep]
  | .rule l _ => symW l
  | .close => [Letter.sym halt, Letter.sep]

/-- What a domino carries past the queue. -/
def topRest : Dom Γ → List (Letter Γ)
  | .close => [Letter.star, Letter.dia]
  | _ => []

theorem topW_eq (halt : Γ) (d : Dom Γ) :
    topW halt d = starL (topUW halt d) ++ topRest d := by
  cases d <;> simp [topW, topUW, topRest]

variable (Rule C₀) in
/-- **The queue of a match belongs to a history**: it is a configuration
reached from the start word, cut in two by the separator, with the part before
the cut still to be consumed and the part after it already rewritten. -/
def Inv (z : List (Letter Γ)) : Prop :=
  ∃ α β γ : List Γ, z = symW β ++ [Letter.sep] ++ symW γ ∧
    Derives Rule C₀ (α ++ β) ∧ ParStep Rule α γ

/-- A queue carries a separator. -/
theorem sep_mem_queue (β γ : List Γ) :
    Letter.sep ∈ symW β ++ [Letter.sep] ++ symW γ := by simp

/-- A queue carries nothing but letters of the system and the separator. -/
theorem mem_queue {c : Letter Γ} {β γ : List Γ}
    (h : c ∈ symW β ++ [Letter.sep] ++ symW γ) : c = Letter.sep ∨ ∃ a, c = Letter.sym a := by
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with (h | h) | h
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨a, rfl⟩
  · exact Or.inl h
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨a, rfl⟩

/-- **The word a domino consumes is a prefix of the queue.** A top word cannot
run past the separator: the only word of the system reaching it is the one the
closing domino consumes, and the queue is then exactly that word. -/
theorem prefix_of_align {z Y S S' : List (Letter Γ)} (h : starL z ++ S = starL Y ++ S')
    (hY : ∀ t, Y = z ++ t → t = []) :
    ∃ t, z = Y ++ t ∧ starL t ++ S = S' := by
  rcases starL_prefix_cases z Y S S' h with ⟨t, hYt, hS⟩ | ⟨t, hzt, hS⟩
  · obtain rfl := hY t hYt
    exact ⟨[], by simpa using hYt.symm, by simpa using hS⟩
  · exact ⟨t, hzt, hS⟩

/-- A word without a separator is no extension of a queue. -/
theorem no_ext_of_sep_notMem {Y z : List (Letter Γ)} (hsep : Letter.sep ∈ z)
    (hY : Letter.sep ∉ Y) : ∀ t, Y = z ++ t → t = [] := by
  intro t ht
  exact absurd (ht ▸ List.mem_append_left t hsep) hY

/-- No domino consumes more than the queue holds. -/
theorem topUW_no_ext {d : Dom Γ} {z : List (Letter Γ)} (hsep : Letter.sep ∈ z) :
    ∀ t, topUW halt d = z ++ t → t = [] := by
  cases d with
  | start => exact no_ext_of_sep_notMem hsep (by simp [topUW])
  | copy a => exact no_ext_of_sep_notMem hsep (by simp [topUW])
  | rule l r => exact no_ext_of_sep_notMem hsep (by simpa [topUW] using sep_not_mem_symW l)
  | copySep =>
    intro t ht
    rcases z with _ | ⟨c, z⟩
    · simp at hsep
    · simp only [topUW, List.cons_append, List.cons.injEq] at ht
      have h2 : z = [] ∧ t = [] := by simpa using ht.2
      exact h2.2
  | close =>
    intro t ht
    rcases z with _ | ⟨c, z⟩
    · simp at hsep
    simp only [topUW, List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    rcases z with _ | ⟨c', z⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hsep
      exact absurd_of_ne hsep
    · simp only [List.cons_append, List.cons.injEq] at ht
      have h2 : z = [] ∧ t = [] := by simpa using ht.2
      exact h2.2

theorem symW_prefix {l : List Γ} {t : List (Letter Γ)} {β γ : List Γ}
    (h : symW l ++ t = symW β ++ [Letter.sep] ++ symW γ) :
    ∃ β', β = l ++ β' ∧ t = symW β' ++ [Letter.sep] ++ symW γ := by
  induction l generalizing β with
  | nil => exact ⟨β, by simp, by simpa using h⟩
  | cons a l ih =>
    cases β with
    | nil =>
      exfalso
      simp only [symW_cons, symW_nil, List.nil_append, List.cons_append] at h
      injection h with h1 _
      exact absurd_of_ne h1
    | cons b β =>
      simp only [symW_cons, List.cons_append] at h
      injection h with hab h
      obtain rfl : a = b := by injection hab
      obtain ⟨β', rfl, ht⟩ := ih h
      exact ⟨β', by simp, ht⟩

/-- **The queue lemma**: a list of dominoes whose bottom words, appended to the
current overhang, spell what its top words spell, walks the queue from a
history to the halting configuration. -/
theorem derives_of_align : ∀ (l : List (Dom Γ)) (z : List (Letter Γ)),
    (∀ d ∈ l, Ok Rule d) →
    (starL z ++ [Letter.star]) ++ bots C₀ l = tops halt l →
    Inv Rule C₀ z → Derives Rule C₀ [halt]
  | [], z, _, halign, _ => by
    exfalso
    simp only [bots_nil, tops_nil, List.append_nil] at halign
    simp at halign
  | d :: l, z, hok, halign, hinv => by
    obtain ⟨α, β, γ, rfl, hder, hpar⟩ := hinv
    have hokd : Ok Rule d := hok d (by simp)
    have hokl : ∀ e ∈ l, Ok Rule e := fun e he => hok e (by simp [he])
    have hsep : Letter.sep ∈ symW β ++ [Letter.sep] ++ symW γ := sep_mem_queue β γ
    have halign' : starL (symW β ++ [Letter.sep] ++ symW γ) ++
        ([Letter.star] ++ (botW C₀ d ++ bots C₀ l)) =
          starL (topUW halt d) ++ (topRest d ++ tops halt l) := by
      rw [tops_cons, bots_cons, topW_eq] at halign
      simpa [List.append_assoc] using halign
    obtain ⟨t, hzt, ht⟩ := prefix_of_align halign' (topUW_no_ext hsep)
    cases d with
    | start =>
      exfalso
      have htri : Letter.tri ∈ symW β ++ [Letter.sep] ++ symW γ := by
        rw [hzt]; simp [topUW]
      rcases mem_queue htri with h | ⟨a, h⟩ <;> exact absurd_of_ne h
    | copy a =>
      have hz : symW [a] ++ t = symW β ++ [Letter.sep] ++ symW γ := by
        rw [hzt]; simp [topUW, symW]
      obtain ⟨β', rfl, rfl⟩ := symW_prefix hz
      refine derives_of_align l (symW β' ++ [Letter.sep] ++ symW (γ ++ [a])) hokl ?_
        ⟨α ++ [a], β', γ ++ [a], rfl, by simpa using hder, hpar.snoc_keep a⟩
      have hnew : symW β' ++ [Letter.sep] ++ symW (γ ++ [a]) =
          (symW β' ++ [Letter.sep] ++ symW γ) ++ symW [a] := by simp
      rw [hnew]
      simp only [topRest, botW, symW, List.map_cons, List.map_nil, starL_append,
        starL_cons, starL_nil, starR_cons, starR_nil, List.append_assoc, List.nil_append,
        List.cons_append] at ht ⊢
      exact ht
    | copySep =>
      have hβ : β = [] := by
        cases β with
        | nil => rfl
        | cons b β =>
          exfalso
          simp only [symW_cons, List.cons_append, topUW, List.cons.injEq] at hzt
          exact absurd_of_ne hzt.1
      subst hβ
      have htq : symW γ = t := by simpa [topUW] using hzt
      subst htq
      refine derives_of_align l (symW γ ++ [Letter.sep] ++ symW ([] : List Γ)) hokl ?_
        ⟨[], γ, [], rfl, ?_, ParStep.nil⟩
      · have hnew : symW γ ++ [Letter.sep] ++ symW ([] : List Γ) =
            symW γ ++ [Letter.sep] := by simp
        rw [hnew]
        simp only [topRest, botW, symW, starL_append,
          starL_cons, starL_nil, starR_cons, starR_nil, List.append_assoc, List.nil_append,
          List.cons_append] at ht ⊢
        exact ht
      · simp only [List.nil_append]
        simp only [List.append_nil] at hder
        exact hder.trans hpar.derives
    | rule l' r =>
      obtain ⟨hr, _, _⟩ := hokd
      have hz : symW l' ++ t = symW β ++ [Letter.sep] ++ symW γ := by
        rw [hzt]; simp [topUW]
      obtain ⟨β', rfl, rfl⟩ := symW_prefix hz
      refine derives_of_align l (symW β' ++ [Letter.sep] ++ symW (γ ++ r)) hokl ?_
        ⟨α ++ l', β', γ ++ r, rfl, by simpa using hder, hpar.snoc_rule hr⟩
      have hnew : symW β' ++ [Letter.sep] ++ symW (γ ++ r) =
          (symW β' ++ [Letter.sep] ++ symW γ) ++ symW r := by simp
      have hkey : starL ((symW β' ++ [Letter.sep] ++ symW γ) ++ symW r) ++ [Letter.star] =
          starL (symW β' ++ [Letter.sep] ++ symW γ) ++ ([Letter.star] ++ starR (symW r)) := by
        rw [starL_append, List.append_assoc, starL_star]
        simp
      rw [hnew, hkey]
      simp only [topRest, botW, List.append_assoc, List.nil_append] at ht ⊢
      exact ht
    | close =>
      have htnil : t = [] := by
        rcases t with _ | ⟨c, t⟩
        · rfl
        exfalso
        have hc : c = Letter.dia := by
          simp only [starL_cons, topRest, List.cons_append, List.cons.injEq] at ht
          exact ht.2.1
        subst hc
        have hdia : Letter.dia ∈ symW β ++ [Letter.sep] ++ symW γ := by
          rw [hzt]; simp
        rcases mem_queue hdia with h | ⟨a, h⟩ <;> exact absurd_of_ne h
      subst htnil
      have hz : symW β ++ [Letter.sep] ++ symW γ = [Letter.sym halt, Letter.sep] := by
        simpa [topUW] using hzt
      have hβγ : β = [halt] ∧ γ = [] := by
        cases β with
        | nil =>
          exfalso
          simp only [symW_nil, List.nil_append, List.singleton_append,
            List.cons.injEq] at hz
          exact absurd_of_ne hz.1
        | cons b β =>
          simp only [symW_cons, List.cons_append, List.cons.injEq] at hz
          obtain ⟨hb, hrest⟩ := hz
          obtain rfl : b = halt := by injection hb
          cases β with
          | nil =>
            simp only [symW_nil, List.nil_append, List.singleton_append,
              List.cons.injEq] at hrest
            refine ⟨rfl, ?_⟩
            cases γ with
            | nil => rfl
            | cons g γ => exact absurd hrest.2 (by simp)
          | cons b' β =>
            exfalso
            simp only [symW_cons, List.cons_append, List.cons.injEq] at hrest
            exact absurd_of_ne hrest.1
      obtain ⟨rfl, rfl⟩ := hβγ
      refine hder.trans ?_
      simpa using hpar.derives.congr [] [halt]

/-- **A match gives a derivation.** The first domino of a match can only be
the one that opens a history, since every top word begins with the decoration
and no other bottom word does; from there the queue lemma reads the match as a
computation. -/
theorem topW_head {d : Dom Γ} (halt : Γ) (hd : Ok Rule d) :
    (topW halt d).head? = some Letter.star := by
  cases d with
  | rule l' r =>
    obtain ⟨_, hl, _⟩ := hd
    rcases l' with _ | ⟨a, l'⟩
    · exact absurd rfl hl
    · simp [topW, symW]
  | _ => simp [topW]

theorem topW_ne_nil {d : Dom Γ} (halt : Γ) (hd : Ok Rule d) : topW halt d ≠ [] := by
  intro h
  have := topW_head (Rule := Rule) halt hd
  rw [h] at this
  simp at this

theorem botW_ne_nil {d : Dom Γ} (C₀ : List Γ) (hd : Ok Rule d) : botW C₀ d ≠ [] := by
  cases d with
  | rule l' r =>
    obtain ⟨_, _, hr⟩ := hd
    rcases r with _ | ⟨b, r⟩
    · exact absurd rfl hr
    · simp [botW, symW]
  | _ => simp [botW]

/-- Only the domino opening a history has a bottom word beginning with the
decoration; every other one begins with a letter. -/
theorem botW_head_ne {d : Dom Γ} (C₀ : List Γ) (hd : Ok Rule d) (hne : d ≠ Dom.start) :
    (botW C₀ d).head? ≠ some Letter.star := by
  cases d with
  | start => exact absurd rfl hne
  | rule l' r =>
    obtain ⟨_, _, hr⟩ := hd
    rcases r with _ | ⟨b, r⟩
    · exact absurd rfl hr
    · simp [botW, symW]
  | _ => simp [botW]

/-- **A match gives a derivation.** The first domino of a match can only be
the one that opens a history, since every top word begins with the decoration
and no other bottom word does; from there the queue lemma reads the match as a
computation. -/
theorem derives_of_hasMatch (h : HasMatch Rule C₀ halt) : Derives Rule C₀ [halt] := by
  obtain ⟨l, hlne, hok, heq⟩ := h
  rcases l with _ | ⟨d, l⟩
  · exact absurd rfl hlne
  have hokd : Ok Rule d := hok d (by simp)
  have hokl : ∀ e ∈ l, Ok Rule e := fun e he => hok e (by simp [he])
  -- the first domino is the one that opens the history
  have hstart : d = Dom.start := by
    by_contra hne'
    have h1 : (tops halt (d :: l)).head? = some Letter.star := by
      rw [tops_cons, List.head?_append_of_ne_nil _ (topW_ne_nil halt hokd),
        topW_head halt hokd]
    rw [heq, bots_cons, List.head?_append_of_ne_nil _ (botW_ne_nil C₀ hokd)] at h1
    exact botW_head_ne C₀ hokd hne' h1
  subst hstart
  refine derives_of_align l (symW C₀ ++ [Letter.sep]) hokl ?_
    ⟨[], C₀, [], by simp, by simpa using Relation.ReflTransGen.refl, ParStep.nil⟩
  have h2 : tops halt l = Letter.star :: (starR (symW C₀ ++ [Letter.sep]) ++ bots C₀ l) := by
    simpa [topW, botW] using heq
  rw [starL_star, h2]
  simp

end Backward

/-- **The dominoes decide derivability**: the system has a match exactly when
its start word derives the halting configuration. -/
theorem hasMatch_iff (hne : ∀ l r, Rule l r → l ≠ [] ∧ r ≠ []) (C₀ : List Γ) (halt : Γ) :
    HasMatch Rule C₀ halt ↔ Derives Rule C₀ [halt] :=
  ⟨derives_of_hasMatch, hasMatch_of_derives hne⟩

end History

end Pcp

end DescriptiveComplexity
