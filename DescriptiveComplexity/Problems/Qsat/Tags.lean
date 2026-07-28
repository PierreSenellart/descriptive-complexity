/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Qsat.Reach
import DescriptiveComplexity.Ordered

/-!
# The shape of the QSAT instance built by the Savitch reduction

The bookkeeping of the reduction of SUCCINCT-REACH to QSAT: what its elements
are, which propositional variable each of them stands for, which clause, and in
which order the prefix quantifies them. Everything here is *semantic* – a
predicate on the coordinates of a tagged pair – so that the defining formulas of
`DescriptiveComplexity.Problems.Qsat.Interp` have something to be compared with.

## The variables (`DescriptiveComplexity.QVarTag`)

Write `SV` for the state variables of the input instance and `⊥` for the minimum
of the input order. Levels of the Savitch recursion are indexed by the state
variables themselves, in the ambient order.

| tag | coordinates | meaning |
| --- | --- | --- |
| `sS`, `sT` | `(x, ⊥)`, `x ∈ SV` | the two endpoints `S`, `T` of the walk |
| `sZ` | `(ℓ, x)` | the midpoint `Z_ℓ` chosen at level `ℓ` |
| `sU`, `sV` | `(ℓ, x)` | the pair `(U_ℓ, V_ℓ)` passed below level `ℓ` |
| `sB` | `(ℓ, ⊥)` | the universal bit `b_ℓ` choosing which half is checked |
| `aS`, `aT`, `aP` | `(a, ⊥)`, `a` arbitrary | the valuations satisfying the three clause groups |
| `sE` | `(⊥, ⊥)` | the bit saying that the base case is an equality, not a step |

## The clauses (`DescriptiveComplexity.QClTag`)

`cSrc`, `cTgt`, `cStep` copy the three clause groups of the input, read on `aS`,
`aT` and `aP`; `lS`, `lT`, `lU`, `lV` tie those valuations to the states they must
read and write; `bE` is the equality branch of the base case; `lev` is the eight
clauses of one level. Each of them is a *fixed* list of literals
(`DescriptiveComplexity.qLits`), a literal being the tag of its variable, its
sign, and a `DescriptiveComplexity.QLink` saying which coordinates that variable
has – which is what keeps the whole matrix clausal and the case analysis finite.

## The prefix

Every variable tag gets a key `(grp, lev, slot, sec, ord)`, of which `grp`,
`slot` and `ord` are static numerals (`DescriptiveComplexity.keyGrp`,
`DescriptiveComplexity.keySlot`, `DescriptiveComplexity.keyOrd`) and `lev`, `sec`
are the two coordinates in one order or the other; the
prefix is the lexicographic comparison `DescriptiveComplexity.KeyLt` of the keys.
It orders the prefix as `S, T` – then, for each level `ℓ` in increasing order,
`Z_ℓ`, `b_ℓ`, `U_ℓ, V_ℓ` – then all the auxiliary variables, with `b_ℓ` the only
universal one. Blocks of like polarity are exactly the sets of variables sharing
the first three components (`DescriptiveComplexity.keyTriple`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Tags -/

/-- The tags of the propositional variables of the QSAT instance built by the
Savitch reduction. -/
inductive QVarTag where
  /-- The source endpoint `S` of the walk. -/
  | sS
  /-- The target endpoint `T` of the walk. -/
  | sT
  /-- The midpoint `Z_ℓ` guessed at level `ℓ`. -/
  | sZ
  /-- The first component `U_ℓ` of the pair passed below level `ℓ`. -/
  | sU
  /-- The second component `V_ℓ` of the pair passed below level `ℓ`. -/
  | sV
  /-- The universal bit `b_ℓ` choosing which half of level `ℓ` is checked. -/
  | sB
  /-- The valuation satisfying the source clauses. -/
  | aS
  /-- The valuation satisfying the target clauses. -/
  | aT
  /-- The valuation satisfying the transition clauses. -/
  | aP
  /-- The bit saying that the base case is an equality rather than a step. -/
  | sE
  deriving DecidableEq

/-- The tags of the clauses of the QSAT instance built by the Savitch
reduction. -/
inductive QClTag where
  /-- A copy of a source clause, read on `aS`. -/
  | cSrc
  /-- A copy of a target clause, read on `aT`. -/
  | cTgt
  /-- A copy of a transition clause, read on `aP` and guarded by `sE`. -/
  | cStep
  /-- `aS` reads the source endpoint `S`, in one of the two directions. -/
  | lS : Bool → QClTag
  /-- `aT` reads the target endpoint `T`, in one of the two directions. -/
  | lT : Bool → QClTag
  /-- `aP` reads `U` at the bottom level, guarded by `sE`. -/
  | lU : Bool → QClTag
  /-- `aP` writes `V` at the bottom level, guarded by `sE`. -/
  | lV : Bool → QClTag
  /-- The equality branch of the base case, guarded by `sE`. -/
  | bE : Bool → QClTag
  /-- One of the eight clauses of a level: the branch of `b_ℓ`, the component of
  the pair, and the sign. -/
  | lev : Bool → Bool → Bool → QClTag
  deriving DecidableEq

/-- The tags of the interpretation: a variable tag or a clause tag. -/
abbrev QTag : Type := QVarTag ⊕ QClTag

private def varIdx : QVarTag → Fin 10
  | .sS => 0
  | .sT => 1
  | .sZ => 2
  | .sU => 3
  | .sV => 4
  | .sB => 5
  | .aS => 6
  | .aT => 7
  | .aP => 8
  | .sE => 9

instance : Finite QVarTag :=
  Finite.of_injective varIdx (by intro x y h; cases x <;> cases y <;> simp_all [varIdx])

private def clIdx : QClTag → Fin 8 × Bool × Bool × Bool
  | .cSrc => (0, false, false, false)
  | .cTgt => (1, false, false, false)
  | .cStep => (2, false, false, false)
  | .lS a => (3, a, false, false)
  | .lT a => (3, a, true, false)
  | .lU a => (4, a, false, false)
  | .lV a => (5, a, false, false)
  | .bE a => (6, a, false, false)
  | .lev a b c => (7, a, b, c)

instance : Finite QClTag :=
  Finite.of_injective clIdx (by intro x y h; cases x <;> cases y <;> simp_all [clIdx])

instance : Nonempty QTag := ⟨Sum.inl .sS⟩

/-- Where a literal's variable sits, relative to the coordinates `(p, q)` of its
clause. Each link determines the variable's coordinates, except the last two,
which range over the literals of a clause of the input instance. -/
inductive QLink where
  /-- The variable `(p, ⊥)`. -/
  | atP
  /-- The variable `(q, ⊥)`. -/
  | atQ
  /-- The variable `(⊥, ⊥)`. -/
  | botBoth
  /-- The variable `(ℓ_max, p)`, at the bottom level. -/
  | maxAtP
  /-- The variable `(p, q)`. -/
  | same
  /-- The variable `(q, ⊥)`, only when `p` is the top level. -/
  | minAtQ
  /-- The variable `(ℓ', q)` for `ℓ'` the level above `p`. -/
  | predAtQ
  /-- A variable `(r, ⊥)` occurring positively in the clause `p` of the input. -/
  | occPos
  /-- A variable `(r, ⊥)` occurring negatively in the clause `p` of the input. -/
  | occNeg
  deriving DecidableEq

/-- A literal of a clause of the constructed instance: the tag of its variable,
its sign, and where the variable sits. -/
structure QLit where
  /-- The tag of the variable the literal is on. -/
  vt : QVarTag
  /-- The sign of the literal. -/
  sign : Bool
  /-- Where the variable sits, relative to the clause's coordinates. -/
  link : QLink
  deriving DecidableEq

/-! ### The literals of each clause -/

/-- The literal of a level clause carrying the *input* of the level: the
midpoint `Z_ℓ` on the two matching branches, and one of the two endpoints of the
level – `S`/`U` at the top, `T`/`V` at the bottom – on the two others. -/
def levInLits (b w s : Bool) : List QLit :=
  if b = w then [⟨.sZ, s, .same⟩]
  else if b then [⟨.sS, s, .minAtQ⟩, ⟨.sU, s, .predAtQ⟩]
  else [⟨.sT, s, .minAtQ⟩, ⟨.sV, s, .predAtQ⟩]

/-- **The literals of each clause of the constructed instance.** A clause of the
input contributes its own literals through `DescriptiveComplexity.QLink.occPos`
and `DescriptiveComplexity.QLink.occNeg`; every other clause is a fixed list of
two or three literals. -/
def qLits : QClTag → List QLit
  | .cSrc => [⟨.aS, true, .occPos⟩, ⟨.aS, false, .occNeg⟩]
  | .cTgt => [⟨.aT, true, .occPos⟩, ⟨.aT, false, .occNeg⟩]
  | .cStep => [⟨.sE, true, .botBoth⟩, ⟨.aP, true, .occPos⟩, ⟨.aP, false, .occNeg⟩]
  | .lS s => [⟨.aS, s, .atP⟩, ⟨.sS, !s, .atP⟩]
  | .lT s => [⟨.aT, s, .atP⟩, ⟨.sT, !s, .atP⟩]
  | .lU s => [⟨.sE, true, .botBoth⟩, ⟨.aP, s, .atP⟩, ⟨.sU, !s, .maxAtP⟩]
  | .lV s => [⟨.sE, true, .botBoth⟩, ⟨.aP, s, .atQ⟩, ⟨.sV, !s, .maxAtP⟩]
  | .bE s => [⟨.sE, false, .botBoth⟩, ⟨.sU, s, .maxAtP⟩, ⟨.sV, !s, .maxAtP⟩]
  | .lev b w s => ⟨.sB, !b, .atP⟩ :: ⟨if w then .sV else .sU, !s, .same⟩ :: levInLits b w s

/-! ### The semantics of the tags -/

section Semantics

variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]

/-- The element `x` is a state variable of the input instance. -/
def IsSV (x : A) : Prop := RelMap tsStateVar ![x]

/-- The element `x` is the first state variable: the top level. -/
def IsMinSV (x : A) : Prop := IsSV x ∧ ∀ z : A, IsSV z → ¬z < x

/-- The element `x` is the last state variable: the bottom level. -/
def IsMaxSV (x : A) : Prop := IsSV x ∧ ∀ z : A, IsSV z → ¬x < z

/-- The state variable `x` is the one just above the state variable `y`. -/
def IsPredSV (x y : A) : Prop :=
  IsSV x ∧ IsSV y ∧ x < y ∧ ∀ z : A, IsSV z → ¬(x < z ∧ z < y)

/-- **Which tagged pairs are variables**: the mark each variable tag puts on its
coordinates. -/
def QVarOn : QVarTag → A → A → Prop
  | .sS | .sT | .sB => fun p q => IsSV p ∧ IsBot q
  | .sZ | .sU | .sV => fun p q => IsSV p ∧ IsSV q
  | .aS | .aT | .aP => fun _ q => IsBot q
  | .sE => fun p q => IsBot p ∧ IsBot q

/-- **Which tagged pairs are clauses**: the guard of each clause tag. -/
def QClOn : QClTag → A → A → Prop
  | .cSrc => fun p q => RelMap tsSrcCl ![p] ∧ IsBot q
  | .cTgt => fun p q => RelMap tsTgtCl ![p] ∧ IsBot q
  | .cStep => fun p q => RelMap tsStepCl ![p] ∧ IsBot q
  | .lS _ | .lT _ => fun p q => IsSV p ∧ IsBot q
  | .lU _ => fun p q => IsSV p ∧ IsBot q
  | .lV _ => fun p q => IsSV p ∧ RelMap tsNext ![p, q]
  | .bE _ => fun p q => IsSV p ∧ IsBot q
  | .lev _ _ _ => fun p q => IsSV p ∧ IsSV q

/-- **Where a literal's variable sits**: the coordinates `(r, s)` of the
variable of a literal of the clause `(p, q)`. -/
def LinkOn : QLink → A → A → A → A → Prop
  | .atP => fun p _ r s => r = p ∧ IsBot s
  | .atQ => fun _ q r s => r = q ∧ IsBot s
  | .botBoth => fun _ _ r s => IsBot r ∧ IsBot s
  | .maxAtP => fun p _ r s => IsMaxSV r ∧ s = p
  | .same => fun p q r s => r = p ∧ s = q
  | .minAtQ => fun p q r s => IsMinSV p ∧ r = q ∧ IsBot s
  | .predAtQ => fun p q r s => IsPredSV r p ∧ s = q
  | .occPos => fun p _ r s => RelMap tsPosIn ![p, r] ∧ IsBot s
  | .occNeg => fun p _ r s => RelMap tsNegIn ![p, r] ∧ IsBot s

end Semantics

/-! ### The quantifier prefix -/

/-- The outermost component of the key: the endpoints, then the levels, then the
auxiliary variables. -/
def keyGrp : QVarTag → ℕ
  | .sS | .sT => 0
  | .sZ | .sB | .sU | .sV => 1
  | .aS | .aT | .aP | .sE => 2

/-- The middle component of the key: within a level, the midpoint, then the
universal bit, then the pair. -/
def keySlot : QVarTag → ℕ
  | .sZ => 0
  | .sB => 1
  | .sU | .sV => 2
  | _ => 0

/-- The innermost component of the key, breaking ties between tags that share
everything else. -/
def keyOrd : QVarTag → ℕ
  | .sS | .sZ | .sB | .sU | .aS => 0
  | .sT | .sV | .aT => 1
  | .aP => 2
  | .sE => 3

/-- Whether the level of a variable is its first coordinate (its second one
otherwise). -/
def levFst : QVarTag → Bool
  | .sZ | .sB | .sU | .sV => true
  | _ => false

/-- **The key of a variable tag is injective**: the triples
`(keyGrp, keySlot, keyOrd)` are pairwise distinct, which is what makes the
prefix a linear order. -/
theorem qKey_inj {v v' : QVarTag} (hg : keyGrp v = keyGrp v') (hs : keySlot v = keySlot v')
    (ho : keyOrd v = keyOrd v') : v = v' := by
  revert hg hs ho
  cases v <;> cases v' <;> simp_all [keyGrp, keySlot, keyOrd]

section Order

variable {A : Type} [LinearOrder A]

/-- The coordinate of a variable that carries its level. -/
def keyLev (v : QVarTag) (p q : A) : A := if levFst v then p else q

/-- The coordinate of a variable that does not carry its level. -/
def keySec (v : QVarTag) (p q : A) : A := if levFst v then q else p

/-- **The block coordinates of a variable**: the components of its key that a
whole quantifier block shares. -/
def keyTriple (v : QVarTag) (p q : A) : ℕ × A × ℕ :=
  (keyGrp v, keyLev v p q, keySlot v)

/-- The lexicographic comparison of block coordinates. -/
def TripleLt (t t' : ℕ × A × ℕ) : Prop :=
  t.1 < t'.1 ∨ (t.1 = t'.1 ∧ (t.2.1 < t'.2.1 ∨ (t.2.1 = t'.2.1 ∧ t.2.2 < t'.2.2)))

/-- **The quantifier prefix**: the lexicographic comparison of the keys, first
on the block coordinates and then on the two remaining components. -/
def KeyLt (v : QVarTag) (p q : A) (v' : QVarTag) (p' q' : A) : Prop :=
  TripleLt (keyTriple v p q) (keyTriple v' p' q') ∨
    (keyTriple v p q = keyTriple v' p' q' ∧
      (keySec v p q < keySec v' p' q' ∨
        (keySec v p q = keySec v' p' q' ∧ keyOrd v < keyOrd v')))

/-! #### The prefix is a strict linear order -/

theorem tripleLt_irrefl (t : ℕ × A × ℕ) : ¬TripleLt t t := by
  rintro (h | ⟨-, h | ⟨-, h⟩⟩) <;> exact absurd h (lt_irrefl _)

theorem tripleLt_trans {t t' t'' : ℕ × A × ℕ} (h : TripleLt t t') (h' : TripleLt t' t'') :
    TripleLt t t'' := by
  rcases h with h1 | ⟨he1, h2⟩ <;> rcases h' with h1' | ⟨he1', h2'⟩
  · exact Or.inl (h1.trans h1')
  · exact Or.inl (he1' ▸ h1)
  · exact Or.inl (he1 ▸ h1')
  · refine Or.inr ⟨he1.trans he1', ?_⟩
    rcases h2 with h3 | ⟨he3, h4⟩ <;> rcases h2' with h3' | ⟨he3', h4'⟩
    · exact Or.inl (h3.trans h3')
    · exact Or.inl (he3' ▸ h3)
    · exact Or.inl (he3 ▸ h3')
    · exact Or.inr ⟨he3.trans he3', h4.trans h4'⟩

theorem tripleLt_total {t t' : ℕ × A × ℕ} (hne : t ≠ t') : TripleLt t t' ∨ TripleLt t' t := by
  rcases lt_trichotomy t.1 t'.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy t.2.1 t'.2.1 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
    · rcases lt_trichotomy t.2.2 t'.2.2 with h3 | h3 | h3
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, h3⟩⟩)
      · exact absurd (Prod.ext h (Prod.ext h2 h3)) hne
      · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, h3⟩⟩)
    · exact Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩)
  · exact Or.inr (Or.inl h)

theorem keyLt_irrefl (v : QVarTag) (p q : A) : ¬KeyLt v p q v p q := by
  rintro (h | ⟨-, h | ⟨-, h⟩⟩)
  · exact tripleLt_irrefl _ h
  · exact absurd h (lt_irrefl _)
  · exact absurd h (lt_irrefl _)

theorem keyLt_trans {v v' v'' : QVarTag} {p q p' q' p'' q'' : A}
    (h : KeyLt v p q v' p' q') (h' : KeyLt v' p' q' v'' p'' q'') : KeyLt v p q v'' p'' q'' := by
  rcases h with h1 | ⟨he1, h2⟩ <;> rcases h' with h1' | ⟨he1', h2'⟩
  · exact Or.inl (tripleLt_trans h1 h1')
  · exact Or.inl (he1' ▸ h1)
  · exact Or.inl (he1 ▸ h1')
  · refine Or.inr ⟨he1.trans he1', ?_⟩
    rcases h2 with h3 | ⟨he3, h4⟩ <;> rcases h2' with h3' | ⟨he3', h4'⟩
    · exact Or.inl (h3.trans h3')
    · exact Or.inl (he3' ▸ h3)
    · exact Or.inl (he3 ▸ h3')
    · exact Or.inr ⟨he3.trans he3', h4.trans h4'⟩

omit [LinearOrder A] in
/-- **A variable is determined by its key together with its coordinates**: this
is what makes distinct variables comparable. -/
theorem eq_of_key_eq {v v' : QVarTag} {p q p' q' : A}
    (htr : keyTriple v p q = keyTriple v' p' q') (hs : keySec v p q = keySec v' p' q')
    (ho : keyOrd v = keyOrd v') : v = v' ∧ p = p' ∧ q = q' := by
  have hg : keyGrp v = keyGrp v' := congrArg Prod.fst htr
  have hsl : keySlot v = keySlot v' := congrArg (fun t => t.2.2) htr
  have hlv : keyLev v p q = keyLev v' p' q' := congrArg (fun t => t.2.1) htr
  have hvv : v = v' := qKey_inj hg hsl ho
  subst hvv
  simp only [keyLev, keySec] at hlv hs
  refine ⟨rfl, ?_⟩
  cases hf : levFst v <;> rw [hf] at hlv hs <;> simp_all

/-- **The prefix is total on the variables**: two distinct variables are
comparable. -/
theorem keyLt_total {v v' : QVarTag} {p q p' q' : A} (hne : ¬(v = v' ∧ p = p' ∧ q = q')) :
    KeyLt v p q v' p' q' ∨ KeyLt v' p' q' v p q := by
  by_cases htr : keyTriple v p q = keyTriple v' p' q'
  · rcases lt_trichotomy (keySec v p q) (keySec v' p' q') with h | h | h
    · exact Or.inl (Or.inr ⟨htr, Or.inl h⟩)
    · rcases lt_trichotomy (keyOrd v) (keyOrd v') with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨htr, Or.inr ⟨h, h2⟩⟩)
      · exact absurd (eq_of_key_eq htr h h2) hne
      · exact Or.inr (Or.inr ⟨htr.symm, Or.inr ⟨h.symm, h2⟩⟩)
    · exact Or.inr (Or.inr ⟨htr.symm, Or.inl h⟩)
  · exact (tripleLt_total htr).imp Or.inl Or.inl

/-- A variable of a block precedes every variable of a later block. -/
theorem keyLt_of_tripleLt {v v' : QVarTag} {p q p' q' : A}
    (h : TripleLt (keyTriple v p q) (keyTriple v' p' q')) : KeyLt v p q v' p' q' :=
  Or.inl h

/-- Comparable variables have comparable block coordinates. -/
theorem tripleLt_or_eq_of_keyLt {v v' : QVarTag} {p q p' q' : A}
    (h : KeyLt v p q v' p' q') :
    TripleLt (keyTriple v p q) (keyTriple v' p' q') ∨ keyTriple v p q = keyTriple v' p' q' :=
  h.imp id And.left

end Order

end DescriptiveComplexity
