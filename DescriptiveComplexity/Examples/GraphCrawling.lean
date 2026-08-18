/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import DescriptiveComplexity.Encoding
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.SecondOrder
import DescriptiveComplexity.Ordered
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.Problems.Steiner.Defs
import DescriptiveComplexity.Problems.SetFamily

/-!
# Worked example: web crawling – data acquisition as graph crawling

This file is the library's second *tutorial*, a companion to
`DescriptiveComplexity.Examples.ConjunctiveQueries`: it walks, step by step,
through the addition of a new problem domain, ending in an NP-completeness
theorem and a machine-checked concrete encoding. The domain is Web data
acquisition: **graph crawling**, the optimization problem underlying focused
crawling of structured documents, formalized by
[Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2]. A website is a
rooted directed graph of pages and hyperlinks; a *crawl* is an `r`-rooted
subtree; the decision problem asks for a crawl containing every *target* page
within a cost budget. The paper proves this NP-complete (its Prop. 4) already
for unit page costs, by reduction from Set Cover; that unit-cost variant is
what this file formalizes, following the paper's proof.

The file follows the user-first arc of the conjunctive-query tutorial: start
from the *concrete problem in the user's own formalism* (step 1), construct
the encoding with the machinery of `DescriptiveComplexity.Encoding` – size
bounds discharged at construction (step 3) – prove the encoded problem
equivalent to the concrete one (step 6), and only then establish the
NP-completeness of the encoded variant (steps 7–9), which faithfulness reads
back to the concrete instances. Every step exercises machinery the CQ file
does not, which is why this example is worth reading second:

* the budget is a *cardinality threshold* – a number in the unary
  representation of `DescriptiveComplexity.Numbers.Unary`, honest here because
  crawl costs are bounded by the page count – checked by a guessed injection
  (`DescriptiveComplexity.nonempty_embedding_iff_ncard_le`);
* the semantics contains a *reachability* condition, which is not
  first-order; the membership proof replaces it by a certificate (an order in
  which every crawled page has a crawled in-neighbor strictly below it),
  the directed, single-root sibling of the Steiner-tree certificate;
* the hardness reduction is an *ordered* FO reduction (`≤ᶠᵒ[≤]`): the
  paper's budget `|U| + B + 1` needs a marked set with exactly one extra
  element, and a canonical singleton is definable only from an order – the
  same triage point as for Chromatic Number;
* the concrete instance type is *single-sorted* with a clamped budget, a
  second worked instance of `DescriptiveComplexity.Encoding` after the
  two-sorted CQ one.

Main results:

* `DescriptiveComplexity.GraphCrawling`: the bundled decision problem;
* `DescriptiveComplexity.graphCrawling_sigmaSODefinable`: membership in NP;
* `DescriptiveComplexity.setCover_ordered_fo_reduction_graphCrawling :
  SetCover ≤ᶠᵒ[≤] GraphCrawling`: the paper's reduction;
* **`DescriptiveComplexity.graphCrawling_NP_complete`**;
* `DescriptiveComplexity.crawlEncoding` with
  `DescriptiveComplexity.crawlEncoding_faithful`: the size-honest concrete
  encoding and its semantic faithfulness;
* `DescriptiveComplexity.crawlDecoding` and
  **`DescriptiveComplexity.crawlWF_NP_complete`**: the computable decoding of
  well-formed (single-root) websites, and completeness restricted to them.
-/

/-!
### Step 1: the concrete problem, in the user's own formalism

A user does not start from finite structures: they start from the data of
their own development. Here that is a packaged crawling instance – a page
count, a set of links, a root, a set of targets, a budget – with the
textbook semantics as a plain Lean predicate. Nothing in this step mentions
model theory; it is the problem as the paper states it, and it is what the
final completeness theorem will be *about*, through the faithfulness theorem
of step 5.
-/

namespace DescriptiveComplexity

/-- A packaged concrete crawling instance: `n + 1` pages, the hyperlinks, the
root page, the target pages, and the budget (clamped to `n + 1` by its type:
a crawl never has more pages than the site). -/
structure CrawlInstance where
  /-- The page count, minus one: pages are `Fin (n + 1)`, so a website is
  never empty. -/
  n : ℕ
  /-- The hyperlinks. -/
  edges : Finset (Fin (n + 1) × Fin (n + 1))
  /-- The root page, where crawls start. -/
  root : Fin (n + 1)
  /-- The target pages. -/
  targets : Finset (Fin (n + 1))
  /-- The budget, clamped by its type: a crawl never has more pages than the
  site. -/
  budget : Fin (n + 2)
  deriving DecidableEq

/-- The textbook size of a packaged instance: pages, links, targets, and the
budget in unary. The one audited line of the encoding. -/
def crawlSize : CrawlInstance → ℕ
  | ⟨n, E, _, T, B⟩ => (n + 1) + E.card + T.card + B.1

/-- The textbook semantics of a packaged instance: some set of pages
containing the root and every target, each of its pages reachable from the
root by links inside it, within budget. -/
def ConcreteCrawlHolds : CrawlInstance → Prop
  | ⟨n, E, r, T, B⟩ => ∃ S : Finset (Fin (n + 1)), r ∈ S ∧ T ⊆ S ∧
      (∀ v ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (a, b) ∈ E) r v) ∧
      S.card ≤ B.1

end DescriptiveComplexity

/-!
### Step 2: the vocabulary of website graphs

An instance is a single finite structure: the pages, the directed links, a
mark for the root, a mark for the targets, and a marked set whose
cardinality is the budget – the unary representation of numbers, as used
by Set Cover, Steiner Tree and the other threshold problems of the catalog.
-/

/- The language of website graphs lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` – a project-local `Language` namespace
would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of website graphs. -/
inductive siteGraphRel : ℕ → Type
  /-- `edge a b`: a hyperlink from page `a` to page `b`. -/
  | edge : siteGraphRel 2
  /-- `root a`: the page `a` is the crawl's starting point. -/
  | root : siteGraphRel 1
  /-- `target a`: the page `a` must be crawled. -/
  | target : siteGraphRel 1
  /-- `marked a`: the page `a` belongs to the marked set carrying the
  budget. -/
  | marked : siteGraphRel 1
  deriving DecidableEq

/-- The relational language of website graphs: directed links, a root, a set
of target pages, and a marked set whose cardinality is the crawling budget. -/
protected def siteGraph : Language :=
  ⟨fun _ => Empty, siteGraphRel⟩
  deriving IsRelational

/-- The edge symbol of website graphs. -/
abbrev wsEdge : Language.siteGraph.Relations 2 := .edge

/-- The root symbol of website graphs. -/
abbrev wsRoot : Language.siteGraph.Relations 1 := .root

/-- The target symbol of website graphs. -/
abbrev wsTarget : Language.siteGraph.Relations 1 := .target

/-- The mark symbol of website graphs. -/
abbrev wsMarked : Language.siteGraph.Relations 1 := .marked

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-!
### Step 3: the encoding, size bounds discharged at construction

With the vocabulary fixed, the concrete instances are encoded as finite
structures using `DescriptiveComplexity.Encoding`: a computable encoder
(`crawlRelBool`, standalone so it can be audited in isolation) and the bundle
whose `card_le`/`le_card` fields *force* the encoding to be size-honest – no
padding, no compression – before anything is proved about its meaning.

Two packaging choices are dictated by the machinery:

* **the budget is clamped by the type** (`Fin (n + 2)`): a crawl never has
  more than `n + 1` pages, so any larger budget is equivalent to `n + 1` –
  and an unclamped `ℕ` budget, counted in unary in the size, would break
  `le_card` exactly as `List`-repetition would for CQ atoms. The WLOG is
  baked into the packaging;
* **the budget is counted in unary** in `crawlSize`. This is the unary
  representation of `DescriptiveComplexity.Numbers.Unary`, and it is *honest*
  here because the clamp keeps the budget below the page count – contrast the
  weighted problems of
  `DescriptiveComplexity/Encoding/UnaryBlowup.lean`, where unary weights are
  exactly what the size bounds reject.
-/

/-- The encoder, standalone and auditable (cf. `cqRelBool`): a plain `def`,
so the compiler vouches that it computes, and the `#guard`s below run it. -/
def crawlRelBool (i : CrawlInstance) {n : ℕ} (R : Language.siteGraph.Relations n) :
    (Fin n → Fin (i.n + 1)) → Bool :=
  match n, R with
  | _, .edge => fun x => decide ((x 0, x 1) ∈ i.edges)
  | _, .root => fun x => decide (x 0 = i.root)
  | _, .target => fun x => decide (x 0 ∈ i.targets)
  | _, .marked => fun x => decide ((x 0).1 < i.budget.1)

/-- The encoding of packaged crawling instances by
`Language.siteGraph`-structures: the pages themselves as universe, the budget
decoded as the marked initial segment `DescriptiveComplexity.initSeg`. Both size
bounds are discharged at construction. -/
def crawlEncoding : Encoding Language.siteGraph CrawlInstance where
  size := crawlSize
  Univ := fun i => Fin (i.n + 1)
  deceq := fun _ => inferInstance
  fintype := fun _ => inferInstance
  relBool := fun i {n} R => crawlRelBool i R
  card_le := Encoding.linear_bound (c := 1) fun i => by
    obtain ⟨n, E, r, T, B⟩ := i
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, crawlSize]
    omega
  le_card := ⟨4, 2, fun i => by
    obtain ⟨n, E, r, T, B⟩ := i
    have hE : E.card ≤ (n + 1) * (n + 1) := by
      simpa [Fintype.card_prod, Fintype.card_fin] using E.card_le_univ
    have hT : T.card ≤ n + 1 := by
      simpa [Fintype.card_fin] using T.card_le_univ
    have hB : B.1 < n + 2 := B.isLt
    obtain ⟨p, hp⟩ : ∃ p, (n + 1) * (n + 1) = p := ⟨_, rfl⟩
    rw [hp] at hE
    have key : n + 1 + p + (n + 1) + (n + 2) ≤ 4 * (n + 1 + 1) ^ 2 := by
      have h : 4 * (n + 1 + 1) ^ 2 = 4 * ((n + 1) * (n + 1)) + 8 * (n + 1) + 4 := by
        ring
      rw [h, hp]
      omega
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, crawlSize]
    exact le_trans (by omega) key⟩

/-!
### Step 4: abstract semantics – rooted reachability, crawls, and their certificates

The paper defines a crawl as an `r`-rooted subtree of the website; the
semantics below phrases “some `r`-rooted subtree with node set `S`” as
“every node of `S` is reachable from `r` by edges inside `S`” – equivalent,
since the parent pointers of a breadth-first traversal assemble any such
reachable set into a tree, and it is precisely those parent pointers that
the first-order certificate recovers (each non-root node has an in-neighbor
strictly closer to the root). Reachability itself is a transitive-closure
condition, not first-order; as for connectivity in the Steiner-tree problem,
the certificate is what makes the membership proof possible, and it reuses
the `DescriptiveComplexity.reachIn` staging for the distance that
`Relation.ReflTransGen` does not carry.
-/

section Reachability

variable {A : Type}

/-- The directed step available inside a chosen set: an edge whose two
endpoints are both chosen. -/
def DiLink (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ Adjp a b

/-- Every member of `S` is reachable from `r` by directed steps inside `S` –
the shape of an `r`-rooted subtree with node set `S`, reachability being all a
breadth-first traversal needs to assemble the tree. -/
def ReachesAllOn (Adjp : A → A → Prop) (r : A) (S : A → Prop) : Prop :=
  ∀ x, S x → Relation.ReflTransGen (DiLink Adjp S) r x

open Classical in
/-- The distance from `r`: the least number of steps in which `x` is
reachable (and `0` when it is not reachable at all, a value the certificate
never looks at). Same device as in `DescriptiveComplexity.Problems.Steiner.Defs`,
over the directed step relation. -/
private noncomputable def rdist (R : A → A → Prop) (r x : A) : ℕ :=
  if h : ∃ n, reachIn R n r x then Nat.find h else 0

private theorem rdist_step {R : A → A → Prop} {r x : A}
    (hx : Relation.ReflTransGen R r x) (hne : x ≠ r) :
    ∃ z, R z x ∧ rdist R r z < rdist R r x := by
  classical
  have hex : ∃ n, reachIn R n r x := (reflTransGen_iff_exists_reachIn R r x).mp hx
  have hd : rdist R r x = Nat.find hex := dif_pos hex
  have hfind : reachIn R (Nat.find hex) r x := Nat.find_spec hex
  rcases hn : Nat.find hex with _ | m
  · rw [hn] at hfind
    exact absurd hfind.symm hne
  · rw [hn] at hfind
    rcases hfind with h | ⟨z, hz, hzx⟩
    · have hle := Nat.find_le (h := hex) h
      rw [hn] at hle
      omega
    · refine ⟨z, hzx, ?_⟩
      have hzex : ∃ n, reachIn R n r z := ⟨m, hz⟩
      have hle : rdist R r z ≤ m := by
        rw [rdist, dif_pos hzex]
        exact Nat.find_le hz
      rw [hd, hn]
      omega

/-- **Rooted reachability is first-order certifiable**: every member of `S` is
reachable from `r` inside `S` exactly when some strict partial order makes
every non-root member of `S` have a chosen in-neighbor strictly below it.
Walking down the order reaches the root; the order “distance to the root”
witnesses the converse. The in-neighbors below are the parent pointers of an
`r`-rooted spanning subtree of `S`. -/
theorem reachesAllOn_iff_exists_order [Finite A] (Adjp : A → A → Prop) (r : A)
    (S : A → Prop) :
    ReachesAllOn Adjp r S ↔ ∃ Lt : A → A → Prop,
      (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
      ∀ x, S x → x ≠ r → ∃ y, S y ∧ Adjp y x ∧ Lt y x := by
  constructor
  · intro hreach
    refine ⟨fun y x => rdist (DiLink Adjp S) r y < rdist (DiLink Adjp S) r x,
      fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, fun _ => lt_irrefl _, fun x hx hne => ?_⟩
    obtain ⟨z, hzx, hlt⟩ := rdist_step (hreach x hx) hne
    exact ⟨z, hzx.1, hzx.2.2, hlt⟩
  · rintro ⟨Lt, htrans, hirr, hstep⟩
    have : IsTrans A Lt := ⟨htrans⟩
    have : Std.Irrefl Lt := ⟨hirr⟩
    have hwf : WellFounded Lt := Finite.wellFounded_of_trans_of_irrefl Lt
    intro x
    induction x using hwf.induction with
    | _ x ih =>
      intro hx
      rcases Classical.em (x = r) with rfl | hne
      · exact Relation.ReflTransGen.refl
      · obtain ⟨y, hy, hadj, hlt⟩ := hstep x hx hne
        exact (ih y hlt hy).tail ⟨hy, hx, hadj⟩

end Reachability

/-! ### The crawling property -/

section Generic

variable {A : Type}

/-- Some marked root admits a crawl: a set of pages containing the root and
every target, entirely reachable from the root inside itself, of size (the
paper's total cost, at unit page costs) at most the number encoded by the
marked set. -/
def CrawlOn (Adjp : A → A → Prop) (Rp Tp Kp : A → Prop) : Prop :=
  ∃ r, Rp r ∧ ∃ S : A → Prop, S r ∧ (∀ x, Tp x → S x) ∧ ReachesAllOn Adjp r S ∧
    {x | S x}.ncard ≤ {x | Kp x}.ncard

/-- The certified form, with reachability witnessed by an order on the chosen
set and the budget by an injection into the marked set: the shape the
second-order definition guesses. The root is guessed as a relation constrained
to hold of exactly one element, which the object language can express. -/
theorem crawlOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Rp Tp Kp : A → Prop) :
    CrawlOn Adjp Rp Tp Kp ↔ ∃ S : A → Prop, (∀ x, Tp x → S x) ∧
      (∃ Rt : A → Prop, (∃ x, Rt x) ∧ (∀ x, Rt x → Rp x ∧ S x) ∧
        (∀ x y, Rt x → Rt y → x = y) ∧
        ∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
          ∀ x, S x → ¬Rt x → ∃ y, S y ∧ Adjp y x ∧ Lt y x) ∧
      Nonempty ({x // S x} ↪ {x // Kp x}) := by
  constructor
  · rintro ⟨r, hRp, S, hSr, hT, hreach, hcard⟩
    obtain ⟨Lt, htrans, hirr, hstep⟩ := (reachesAllOn_iff_exists_order Adjp r S).mp hreach
    exact ⟨S, hT, ⟨(· = r), ⟨r, rfl⟩, fun x hx => hx ▸ ⟨hRp, hSr⟩,
      fun x y hx hy => hx.trans hy.symm, Lt, htrans, hirr,
      fun x hx hne => hstep x hx hne⟩,
      (nonempty_embedding_iff_ncard_le _ _).mpr hcard⟩
  · rintro ⟨S, hT, ⟨Rt, ⟨r, hr⟩, hRtP, huniq, Lt, htrans, hirr, hstep⟩, he⟩
    obtain ⟨hRp, hSr⟩ := hRtP r hr
    refine ⟨r, hRp, S, hSr, hT,
      (reachesAllOn_iff_exists_order Adjp r S).mpr ⟨Lt, htrans, hirr, ?_⟩,
      (nonempty_embedding_iff_ncard_le _ _).mp he⟩
    intro x hx hne
    exact hstep x hx fun hRtx => hne (huniq x r hRtx hr)

variable {B : Type}

private theorem reflTransGen_diLink_map (u : B ≃ A) {AdjB : B → B → Prop} {SB : B → Prop}
    {AdjA : A → A → Prop} {SA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hS : ∀ b, SB b ↔ SA (u b))
    {x y : B} (h : Relation.ReflTransGen (DiLink AdjB SB) x y) :
    Relation.ReflTransGen (DiLink AdjA SA) (u x) (u y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ⟨(hS _).mp hbc.1, (hS _).mp hbc.2.1, (hadj _ _).mp hbc.2.2⟩

/-- `CrawlOn` transports along an equivalence commuting with the four
predicates. -/
theorem CrawlOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {RB TB KB : B → Prop}
    {AdjA : A → A → Prop} {RA TA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hR : ∀ b, RB b ↔ RA (u b))
    (hT : ∀ b, TB b ↔ TA (u b)) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CrawlOn AdjB RB TB KB) : CrawlOn AdjA RA TA KA := by
  obtain ⟨r, hRr, S, hSr, hTs, hreach, hcard⟩ := h
  refine ⟨u r, (hR r).mp hRr, fun a => S (u.symm a), by simpa using hSr,
    fun x hx => hTs _ ((hT _).mpr (by simpa using hx)), fun a ha => ?_, ?_⟩
  · have hpath := reflTransGen_diLink_map (SA := fun a => S (u.symm a)) u hadj
      (fun b => by simp) (hreach (u.symm a) ha)
    simpa using hpath
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u S]
    exact hcard

/-- `CrawlOn` transports along an equivalence, iff version. -/
theorem CrawlOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {RB TB KB : B → Prop}
    {AdjA : A → A → Prop} {RA TA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hR : ∀ b, RB b ↔ RA (u b))
    (hT : ∀ b, TB b ↔ TA (u b)) (hK : ∀ b, KB b ↔ KA (u b)) :
    CrawlOn AdjB RB TB KB ↔ CrawlOn AdjA RA TA KA :=
  ⟨CrawlOn.of_equiv u hadj hR hT hK,
    CrawlOn.of_equiv u.symm (fun a a' => by rw [hadj]; simp) (fun a => by rw [hR]; simp)
      (fun a => by rw [hT]; simp) fun a => by rw [hK]; simp⟩

end Generic

/-!
### Step 5: isomorphism-invariance and the bundled problem

As always, the invariance proof is a transport of the `RelMap` shorthands
along the isomorphism via the shared `relMap_equiv₁`/`₂` lemmas; the junk
conventions were stated with the semantics (a structure marking no root is a
no-instance, one marking several is read disjunctively).
-/

section Problem

section Shorthands

variable {A : Type} [Language.siteGraph.Structure A]

/-- A hyperlink in a website graph. -/
def WSEdge (a b : A) : Prop := RelMap wsEdge ![a, b]

/-- Being the root of a website graph. -/
def WSRoot (a : A) : Prop := RelMap wsRoot ![a]

/-- Being a target page. -/
def WSTarget (a : A) : Prop := RelMap wsTarget ![a]

/-- Belonging to the marked set carrying the budget. -/
def WSMarked (a : A) : Prop := RelMap wsMarked ![a]

end Shorthands

variable (A : Type) [Language.siteGraph.Structure A]

/-- A website graph admits a crawl within budget: a set of pages containing
the marked root and every target, reachable from the root inside itself, with
at most as many pages as the marked set has elements. (Finiteness of the
universe is part of the property: cardinality thresholds are only meaningful
on finite structures.) -/
def HasCheapCrawl : Prop :=
  Finite A ∧ CrawlOn (WSEdge (A := A)) WSRoot WSTarget WSMarked

end Problem

section Iso

variable {A B : Type} [Language.siteGraph.Structure A] [Language.siteGraph.Structure B]

/-- The crawling property is isomorphism-invariant. -/
theorem hasCheapCrawl_iso (e : A ≃[Language.siteGraph] B) :
    HasCheapCrawl A ↔ HasCheapCrawl B :=
  and_congr e.toEquiv.finite_iff
    (CrawlOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e wsEdge a b)
      (fun a => relMap_equiv₁ e wsRoot a) (fun a => relMap_equiv₁ e wsTarget a)
      fun a => relMap_equiv₁ e wsMarked a)

end Iso

/-- GRAPH CRAWLING ([Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2],
decision variant, unit page costs), as a problem on website graphs: is there a
crawl – a set of pages containing the marked root and every target, reachable
from the root inside itself – of at most as many pages as the marked set has
elements? -/
def GraphCrawling : DecisionProblem Language.siteGraph where
  Holds := fun A inst => @HasCheapCrawl A inst
  iso_invariant := fun e => hasCheapCrawl_iso e

/-!
### Step 6: faithfulness – the encoded problem is the concrete one

The bridge between steps 1 and 5: the abstract problem computes the textbook
semantics on every encoded instance (`Encoding.Faithful`). With the size
bounds already discharged by the bundle of step 3, this equivalence is the
*whole* of the encoding obligation – from here on, every theorem about
`GraphCrawling` reads back to the concrete instances. The worked instance
and the `#guard`s then *run* the encoder against a hand computation.

The decoding direction is what well-formedness is for. An abstract
structure may mark several roots (read disjunctively by the semantics), and
no packaged instance – carrying a single root – transcribes such a structure
without *deciding* which root works, a computation a decoder should not
contain. The well-formedness sentence `crawlWFSentence` (“exactly one root”)
removes these, and on well-formed structures a computable decoder
`crawlDecode` exists: find the root, read the links, targets and clamped
budget off the tables. It assembles into
`DescriptiveComplexity.crawlDecoding`, runs (`#guard`s below), and step 9
restricts the completeness theorem to well-formed instances accordingly
(`crawlWF_NP_complete`). See `DescriptiveComplexity/Decoding.lean` for why
the bundled computation – and not an `∃`-only covering statement – is the
meaningful notion.
-/

/-- **The packaged encoding is faithful**: the abstract problem
`GraphCrawling` computes the textbook semantics on every encoded instance –
obligation (1), with obligation (2) already discharged by the bundle. -/
theorem crawlEncoding_faithful :
    crawlEncoding.Faithful ConcreteCrawlHolds GraphCrawling := by
  rintro ⟨n, E, r, T, B⟩
  -- restate the abstract side at `Fin (n + 1)` with the encoder's relations
  -- spelled out (all definitional): the whole proof then lives in one type,
  -- where every decidability instance is found
  change ConcreteCrawlHolds ⟨n, E, r, T, B⟩ ↔ Finite (Fin (n + 1)) ∧
    CrawlOn (A := Fin (n + 1)) (fun a b => decide ((a, b) ∈ E) = true)
      (fun a => decide (a = r) = true) (fun a => decide (a ∈ T) = true)
      (fun a => decide ((a : ℕ) < B.1) = true)
  -- the marked set of the encoded structure decodes the budget
  have hRH : {x : Fin (n + 1) | (fun a => decide ((a : ℕ) < B.1) = true) x} =
      initSeg (n + 1) B.1 := by
    ext x
    simp [initSeg]
  constructor
  · rintro ⟨S, hrS, hTS, hreach, hcard⟩
    refine ⟨Finite.of_fintype _, r, decide_eq_true rfl, fun v => v ∈ S, hrS, ?_, ?_, ?_⟩
    · exact fun x hx => hTS (of_decide_eq_true hx)
    · intro x hx
      exact Relation.ReflTransGen.mono
        (fun a b hab => ⟨hab.1, hab.2.1, decide_eq_true hab.2.2⟩) _ _ (hreach x hx)
    · rw [hRH, ncard_initSeg _ _ (Nat.lt_succ_iff.mp B.isLt)]
      exact le_trans (le_of_eq (Set.ncard_coe_finset S)) hcard
  · rintro ⟨-, r', hroot, S', hS'r, hTgt, hreach, hcard⟩
    have hr' : r' = r := of_decide_eq_true hroot
    subst hr'
    classical
    rw [hRH, ncard_initSeg _ _ (Nat.lt_succ_iff.mp B.isLt)] at hcard
    refine ⟨Finset.univ.filter S', by simpa using hS'r, ?_, ?_, ?_⟩
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTgt v (decide_eq_true hv)⟩
    · intro v hv
      exact Relation.ReflTransGen.mono
        (fun a b hab => ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.2.1⟩,
          of_decide_eq_true hab.2.2⟩) _ _ (hreach v (Finset.mem_filter.mp hv).2)
    · have h2 : ((Finset.univ.filter S' : Finset (Fin (n + 1))) : Set (Fin (n + 1))) =
          {x | S' x} := by
        ext x
        simp
      have h3 : (Finset.univ.filter S').card = {x | S' x}.ncard := by
        rw [← Set.ncard_coe_finset, h2]
      rw [h3]
      exact hcard

/-- A small worked instance: four pages, root `0`, links `0 → 1`, `1 → 2`
and `0 → 3`, targets `{2, 3}`, budget `4` – a *tight* yes-instance (both
targets need the whole chain through `1`). -/
def crawlExample : CrawlInstance :=
  ⟨3, {(0, 1), (1, 2), (0, 3)}, 0, {2, 3}, 4⟩

/-- The packaged instance is a concrete yes-instance: crawl everything. -/
theorem crawlExample_holds : ConcreteCrawlHolds crawlExample := by
  refine ⟨{0, 1, 2, 3}, by decide, by decide, ?_, by decide⟩
  intro v hv
  fin_cases hv
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by decide)
  · exact Relation.ReflTransGen.tail (b := 1)
      (Relation.ReflTransGen.single (by decide)) (by decide)
  · exact Relation.ReflTransGen.single (by decide)

/-- … and, through the faithfulness theorem, its encoded structure is a
yes-instance of the abstract problem. -/
example : GraphCrawling (crawlEncoding.Univ crawlExample) :=
  (crawlEncoding_faithful crawlExample).mp crawlExample_holds

/-!
As in the CQ tutorial, the encoder can be *run*: the `#guard`s evaluate the
encoded relations of the worked instance against the hand computation.
-/

section
set_option linter.hashCommand false

#guard crawlEncoding.relBool crawlExample wsEdge (![0, 1] : Fin 2 → Fin 4)
#guard !crawlEncoding.relBool crawlExample wsEdge (![1, 0] : Fin 2 → Fin 4)
#guard crawlEncoding.relBool crawlExample wsRoot (![0] : Fin 1 → Fin 4)
#guard !crawlEncoding.relBool crawlExample wsRoot (![1] : Fin 1 → Fin 4)
#guard crawlEncoding.relBool crawlExample wsTarget (![2] : Fin 1 → Fin 4)
#guard !crawlEncoding.relBool crawlExample wsTarget (![0] : Fin 1 → Fin 4)
#guard crawlEncoding.relBool crawlExample wsMarked (![3] : Fin 1 → Fin 4)

end

/-!
The well-formedness sentence, its meaning, and the decoder.
-/

/-- Well-formedness of a website graph: exactly one root page. What makes an
honest decoder possible. -/
noncomputable def crawlWFSentence : Language.siteGraph.Sentence :=
  Formula.iExs (Fin 1) (Relations.formula₁ wsRoot (Term.var (Sum.inr 0)) ⊓
    Formula.iAlls (Fin 1)
      ((Relations.formula₁ wsRoot (Term.var (Sum.inr 0))).imp
        (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl (Sum.inr 0))))))

theorem realize_crawlWFSentence {A : Type} [Language.siteGraph.Structure A] :
    A ⊨ crawlWFSentence ↔ ∃ x : A, WSRoot x ∧ ∀ y : A, WSRoot y → y = x := by
  simp only [crawlWFSentence, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, WSRoot]
  constructor
  · rintro ⟨i, hr, hu⟩
    exact ⟨i 0, hr, fun y hy => hu (fun _ => y) hy⟩
  · rintro ⟨x, hr, hu⟩
    exact ⟨fun _ => x, hr, fun j hj => hu (j 0) hj⟩

section Decoder

variable (S : FinPresentation Language.siteGraph)

/-- The root pages of a presented website. -/
def crawlRoots : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool wsRoot ![x]

theorem mem_crawlRoots (x : Fin S.card) : x ∈ crawlRoots S ↔ WSRoot x := by
  simp [crawlRoots, WSRoot]

private theorem gc_cast_cast {n m : ℕ} (h : n = m) (v : Fin n) :
    Fin.cast h.symm (Fin.cast h v) = v := by
  ext
  simp

private theorem gc_cast_cast' {n m : ℕ} (h : n = m) (v : Fin m) :
    Fin.cast h (Fin.cast h.symm v) = v := by
  ext
  simp

/-- Decode a presented website whose unique root has been found: read the
links, targets and budget off the tables, the budget clamped to the page
count as the packaging requires. (The root's existence is what makes the
page count positive.) -/
def crawlDecodeAt (r : Fin S.card) : CrawlInstance :=
  ⟨S.card - 1,
    Finset.univ.filter fun p : Fin (S.card - 1 + 1) × Fin (S.card - 1 + 1) =>
      S.relBool wsEdge ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.1,
        Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.2],
    Fin.cast (Nat.succ_pred_eq_of_pos r.pos).symm r,
    Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
      S.relBool wsTarget ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x],
    ⟨min ((Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
        S.relBool wsMarked ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x]).card)
      (S.card - 1 + 1), by omega⟩⟩

/-- The decoder: `none` unless the site has exactly one root. -/
def crawlDecode : Option CrawlInstance :=
  match (crawlRoots S).sort (· ≤ ·) with
  | [] => none
  | [r] => some (crawlDecodeAt S r)
  | _ :: _ :: _ => none

theorem crawlDecode_sound (i : CrawlInstance) (hi : i ∈ crawlDecode S) :
    ConcreteCrawlHolds i ↔ GraphCrawling (Fin S.card) := by
  unfold crawlDecode at hi
  split at hi
  · exact absurd hi (by simp)
  case _ r hr =>
    rw [Option.mem_def, Option.some.injEq] at hi
    subst hi
    have hn : S.card - 1 + 1 = S.card := Nat.succ_pred_eq_of_pos r.pos
    have hroot : ∀ x : Fin S.card, WSRoot x ↔ x = r := by
      intro x
      rw [← mem_crawlRoots]
      constructor
      · intro hxx
        have hxs : x ∈ (crawlRoots S).sort (· ≤ ·) := (Finset.mem_sort _).mpr hxx
        rw [hr] at hxs
        simpa using hxs
      · rintro rfl
        refine (Finset.mem_sort (α := Fin S.card) (· ≤ ·)).mp ?_
        rw [hr]
        simp
    unfold crawlDecodeAt
    -- the marked set of the presented structure, counted once for both
    -- directions
    have hiffm : ∀ b : Fin S.card, WSMarked b ↔
        (finCongr hn.symm) b ∈ Finset.univ.filter
          (fun x : Fin (S.card - 1 + 1) =>
            S.relBool wsMarked ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x]) := by
      intro b
      rw [finCongr_apply, Finset.mem_filter]
      constructor
      · intro hb
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [gc_cast_cast']
        exact hb
      · rintro ⟨-, hb⟩
        rw [gc_cast_cast'] at hb
        exact hb
    have h2 : {x : Fin S.card | WSMarked x}.ncard =
        (Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
          S.relBool wsMarked ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x]).card := by
      rw [ncard_setOf_equiv (finCongr hn.symm)
        (KB := fun x : Fin S.card => WSMarked x) hiffm]
      generalize (Finset.univ.filter fun x : Fin (S.card - 1 + 1) =>
        S.relBool wsMarked ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) x]) = K
      simp
    constructor
    · rintro ⟨Sc, hrS, hTS, hreach, hcard⟩
      refine ⟨Finite.of_fintype _, r, (hroot r).mpr rfl,
        fun v => Fin.cast hn.symm v ∈ Sc, hrS, ?_, ?_, ?_⟩
      · intro x hx
        refine hTS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        rw [gc_cast_cast']
        exact hx
      · intro x hx
        have hmap : ∀ {u v : Fin (S.card - 1 + 1)}, Relation.ReflTransGen
            (fun a b => a ∈ Sc ∧ b ∈ Sc ∧ (a, b) ∈ Finset.univ.filter
              (fun p : Fin (S.card - 1 + 1) × Fin (S.card - 1 + 1) =>
                S.relBool wsEdge ![Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.1,
                  Fin.cast (Nat.succ_pred_eq_of_pos r.pos) p.2])) u v →
            Relation.ReflTransGen (DiLink (WSEdge (A := Fin S.card))
              fun w => Fin.cast hn.symm w ∈ Sc) (Fin.cast hn u) (Fin.cast hn v) := by
          intro u v hp
          induction hp with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hcd ih =>
            refine ih.tail ⟨?_, ?_, ?_⟩
            · dsimp only
              rw [gc_cast_cast]
              exact hcd.1
            · dsimp only
              rw [gc_cast_cast]
              exact hcd.2.1
            · exact (Finset.mem_filter.mp hcd.2.2).2
        have hpath := hmap (hreach (Fin.cast hn.symm x) hx)
        rw [gc_cast_cast'] at hpath
        exact hpath
      · change {x : Fin S.card | Fin.cast hn.symm x ∈ Sc}.ncard ≤
          {x : Fin S.card | WSMarked x}.ncard
        have hiffs : ∀ b : Fin S.card, Fin.cast hn.symm b ∈ Sc ↔
            (finCongr hn.symm) b ∈ Sc := fun b => by rw [finCongr_apply]
        have h1 : {x : Fin S.card | Fin.cast hn.symm x ∈ Sc}.ncard = Sc.card := by
          rw [ncard_setOf_equiv (finCongr hn.symm)
            (KB := fun x : Fin S.card => Fin.cast hn.symm x ∈ Sc)
            (KA := fun a : Fin (S.card - 1 + 1) => a ∈ Sc) hiffs]
          simp
        rw [h1, h2]
        exact le_trans hcard (min_le_left _ _)
    · rintro ⟨-, r'', hR'', S', hS'r, hTgt, hreach, hcard⟩
      obtain rfl : r'' = r := (hroot r'').mp hR''
      classical
      refine ⟨Finset.univ.filter fun v : Fin (S.card - 1 + 1) => S' (Fin.cast hn v),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_, ?_, ?_⟩
      · rw [gc_cast_cast']
        exact hS'r
      · intro v hv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hTgt _ (Finset.mem_filter.mp hv).2
      · intro v hv
        have hmap : ∀ {u w : Fin S.card}, Relation.ReflTransGen
            (DiLink (WSEdge (A := Fin S.card)) S') u w →
            Relation.ReflTransGen (fun a b =>
              (a ∈ Finset.univ.filter fun v : Fin (S.card - 1 + 1) =>
                S' (Fin.cast hn v)) ∧
              (b ∈ Finset.univ.filter fun v : Fin (S.card - 1 + 1) =>
                S' (Fin.cast hn v)) ∧
              (a, b) ∈ Finset.univ.filter (fun p : Fin (S.card - 1 + 1) ×
                  Fin (S.card - 1 + 1) =>
                S.relBool wsEdge ![Fin.cast hn p.1, Fin.cast hn p.2]))
              (Fin.cast hn.symm u) (Fin.cast hn.symm w) := by
          intro u w hp
          induction hp with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hcd ih =>
            refine ih.tail ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
            · rw [gc_cast_cast']
              exact hcd.1
            · rw [gc_cast_cast']
              exact hcd.2.1
            · change (S.relBool wsEdge ![Fin.cast hn (Fin.cast hn.symm _),
                Fin.cast hn (Fin.cast hn.symm _)]) = true
              rw [gc_cast_cast', gc_cast_cast']
              exact hcd.2.2
        have hpath := hmap (hreach (Fin.cast hn v) (Finset.mem_filter.mp hv).2)
        rw [gc_cast_cast] at hpath
        exact hpath
      · refine le_min ?_ ?_
        · have hiffs : ∀ b : Fin S.card, S' b ↔
              (finCongr hn.symm) b ∈ Finset.univ.filter
                (fun v : Fin (S.card - 1 + 1) => S' (Fin.cast hn v)) := by
            intro b
            rw [finCongr_apply, Finset.mem_filter]
            constructor
            · intro hb
              refine ⟨Finset.mem_univ _, ?_⟩
              rw [gc_cast_cast']
              exact hb
            · rintro ⟨-, hb⟩
              rw [gc_cast_cast'] at hb
              exact hb
          have h1 : (Finset.univ.filter fun v : Fin (S.card - 1 + 1) =>
              S' (Fin.cast hn v)).card = {x : Fin S.card | S' x}.ncard := by
            rw [ncard_setOf_equiv (finCongr hn.symm)
              (KB := fun x : Fin S.card => S' x) hiffs]
            generalize (Finset.univ.filter fun v : Fin (S.card - 1 + 1) =>
              S' (Fin.cast hn v)) = K
            simp
          rw [h1, ← h2]
          exact hcard
        · simpa using Finset.card_le_univ (Finset.univ.filter
            fun v : Fin (S.card - 1 + 1) => S' (Fin.cast hn v))
  · exact absurd hi (by simp)

theorem crawlDecode_total (_hpos : 0 < S.card)
    (hW : DecisionProblem.ofSentence crawlWFSentence (Fin S.card)) :
    (crawlDecode S).isSome := by
  obtain ⟨x, hx, hu⟩ := realize_crawlWFSentence.mp hW
  have hset : crawlRoots S = {x} := by
    ext y
    rw [mem_crawlRoots, Finset.mem_singleton]
    exact ⟨fun hy => hu y hy, fun hy => hy ▸ hx⟩
  unfold crawlDecode
  split
  · next hr =>
    rw [hset, Finset.sort_singleton] at hr
    exact absurd hr (by simp)
  · rfl
  · next _ _ _ hr =>
    rw [hset, Finset.sort_singleton] at hr
    exact absurd hr (by simp)

end Decoder

/-- **The computable decoding of well-formed website graphs**. Together with
`crawlEncoding_faithful` it closes the loop between the concrete and the
abstract problem – a decoder that exists only because well-formedness
removed the multi-root structures. -/
def crawlDecoding : Decoding Language.siteGraph
    (DecisionProblem.ofSentence crawlWFSentence) ConcreteCrawlHolds GraphCrawling where
  dec := crawlDecode
  sound := crawlDecode_sound
  total := crawlDecode_total

/-- The worked instance of step 1, presented as raw tables. -/
def crawlPres : FinPresentation Language.siteGraph where
  card := 4
  relBool := fun {n} R =>
    match n, R with
    | _, .edge => fun x =>
        x 0 == 0 && x 1 == 1 || x 0 == 1 && x 1 == 2 || x 0 == 0 && x 1 == 3
    | _, .root => fun x => x 0 == 0
    | _, .target => fun x => x 0 == 2 || x 0 == 3
    | _, .marked => fun _ => true

section
set_option linter.hashCommand false

/- Decoding the presented tables recovers exactly the packaged worked
instance – the decoder and the encoder meet in the middle. -/
#guard crawlDecode crawlPres = some crawlExample

end

/-!
### Step 7: membership in NP

NP is *defined* as `Σ₁` second-order definability, so membership means
exhibiting a second-order sentence: guess an object-level certificate, check
it with a first-order kernel. The certificate is the one of
`DescriptiveComplexity.crawlOn_iff_certificate`: the crawled set, its root, the
order witnessing reachability, and the injection witnessing the budget – four
relation variables, nine first-order clauses. The construction mirrors the
Steiner-tree kernel (`DescriptiveComplexity.Problems.Steiner.Membership`), with
three differences worth spotting: the step clause walks *into* each crawled
page along a directed edge, the guessed root must exist and carry the
vocabulary's root mark, and the budget injection is total on the whole
crawled set, since the paper's cost counts every crawled page.
-/

open SOBlock

section SigmaOne

/-- The four relation variables guessed by the `Σ₁` definition of Graph
Crawling. -/
inductive CrawlGuess
  /-- The crawled set of pages. -/
  | set
  /-- The root the crawl starts from. -/
  | root
  /-- The order certifying reachability from the root. -/
  | order
  /-- The injection witnessing the budget. -/
  | inj
  deriving DecidableEq

instance : Fintype CrawlGuess := ⟨{.set, .root, .order, .inj}, fun t => by cases t <;> decide⟩

/-- The single existential block of the `Σ₁` definition of Graph Crawling. -/
def crawlGuessBlock : SOBlock where
  ι := CrawlGuess
  arity := fun i => match i with
    | .set => 1
    | .root => 1
    | .order => 2
    | .inj => 2

/-- The symbol of the crawled-set relation variable. -/
def cgSetRel : crawlGuessBlock.lang.Relations 1 := ⟨.set, rfl⟩

/-- The symbol of the root relation variable. -/
def cgRootRel : crawlGuessBlock.lang.Relations 1 := ⟨.root, rfl⟩

/-- The symbol of the order relation variable. -/
def cgOrderRel : crawlGuessBlock.lang.Relations 2 := ⟨.order, rfl⟩

/-- The symbol of the injection relation variable. -/
def cgInjRel : crawlGuessBlock.lang.Relations 2 := ⟨.inj, rfl⟩

/-- The vocabulary of the kernel. -/
abbrev crawlSOLang : Language := Language.siteGraph.sum crawlGuessBlock.lang

/-- The edge symbol in the kernel's vocabulary. -/
abbrev kCrEdgeSym : crawlSOLang.Relations 2 := Sum.inl wsEdge

/-- The root-mark symbol in the kernel's vocabulary. -/
abbrev kCrRootMarkSym : crawlSOLang.Relations 1 := Sum.inl wsRoot

/-- The target symbol in the kernel's vocabulary. -/
abbrev kCrTargetSym : crawlSOLang.Relations 1 := Sum.inl wsTarget

/-- The budget-mark symbol in the kernel's vocabulary. -/
abbrev kCrMarkedSym : crawlSOLang.Relations 1 := Sum.inl wsMarked

/-- The crawled-set symbol in the kernel's vocabulary. -/
abbrev kCrSetSym : crawlSOLang.Relations 1 := Sum.inr cgSetRel

/-- The root symbol in the kernel's vocabulary. -/
abbrev kCrRootSym : crawlSOLang.Relations 1 := Sum.inr cgRootRel

/-- The order symbol in the kernel's vocabulary. -/
abbrev kCrLtSym : crawlSOLang.Relations 2 := Sum.inr cgOrderRel

/-- The injection symbol in the kernel's vocabulary. -/
abbrev kCrInjSym : crawlSOLang.Relations 2 := Sum.inr cgInjRel

/-! ### The clauses -/

/-- Kernel clause: every target is crawled. -/
private noncomputable def crTargetClause : crawlSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kCrTargetSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kCrSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: some root is guessed. -/
private noncomputable def crRootExistsClause : crawlSOLang.Sentence :=
  (Relations.formula₁ kCrRootSym (Term.var (Sum.inr 0))).iExs (Fin 1)

/-- Kernel clause: the guessed root carries the vocabulary's root mark and is
crawled. -/
private noncomputable def crRootClause : crawlSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kCrRootSym (Term.var (Sum.inr 0))).imp
      (Relations.formula₁ kCrRootMarkSym (Term.var (Sum.inr 0)) ⊓
        Relations.formula₁ kCrSetSym (Term.var (Sum.inr 0))))

/-- Kernel clause: there is at most one guessed root. -/
private noncomputable def crRootUniqueClause : crawlSOLang.Sentence :=
  ((Relations.formula₁ kCrRootSym (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ kCrRootSym (Term.var (Sum.inr 1))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 2)

/-- Kernel clause: the guessed order is transitive. -/
private noncomputable def crTransClause : crawlSOLang.Sentence :=
  ((Relations.formula₂ kCrLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)) ⊓
      Relations.formula₂ kCrLtSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Relations.formula₂ kCrLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)))).iAlls (Fin 3)

/-- Kernel clause: the guessed order is irreflexive. -/
private noncomputable def crIrreflClause : crawlSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    (∼(Relations.formula₂ kCrLtSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))))

/-- Kernel clause: every crawled non-root page is linked from a crawled page
strictly below it. -/
private noncomputable def crStepClause : crawlSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kCrSetSym (Term.var (Sum.inr 0)) ⊓
        ∼(Relations.formula₁ kCrRootSym (Term.var (Sum.inr 0)))).imp
      ((Relations.formula₁ kCrSetSym (Term.var (Sum.inr ())) ⊓
        Relations.formula₂ kCrEdgeSym (Term.var (Sum.inr ()))
          (Term.var (Sum.inl (Sum.inr 0))) ⊓
        Relations.formula₂ kCrLtSym (Term.var (Sum.inr ()))
          (Term.var (Sum.inl (Sum.inr 0)))).iExs Unit))

/-- Kernel clause: the guessed injection maps every crawled page to a marked
element. -/
private noncomputable def crTotalClause : crawlSOLang.Sentence :=
  Formula.iAlls (Fin 1)
    ((Relations.formula₁ kCrSetSym (Term.var (Sum.inr 0))).imp
      ((Relations.formula₂ kCrInjSym (Term.var (Sum.inl (Sum.inr 0)))
          (Term.var (Sum.inr ())) ⊓
        Relations.formula₁ kCrMarkedSym (Term.var (Sum.inr ()))).iExs Unit))

/-- Kernel clause: the guessed injection is injective. -/
private noncomputable def crInjClause : crawlSOLang.Sentence :=
  ((Relations.formula₂ kCrInjSym (Term.var (Sum.inr 0)) (Term.var (Sum.inr 2)) ⊓
      Relations.formula₂ kCrInjSym (Term.var (Sum.inr 1)) (Term.var (Sum.inr 2))).imp
    (Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))).iAlls (Fin 3)

/-- The first-order kernel of the `Σ₁` definition of Graph Crawling. -/
noncomputable def crawlKernel : crawlSOLang.Sentence :=
  crTargetClause ⊓ (crRootExistsClause ⊓ (crRootClause ⊓ (crRootUniqueClause ⊓
    (crTransClause ⊓ (crIrreflClause ⊓ (crStepClause ⊓ (crTotalClause ⊓ crInjClause)))))))

/-! ### Realization -/

section Realize

variable {A : Type} [Language.siteGraph.Structure A]
  (ρ : crawlGuessBlock.Assignment A)

/-- Realization at a structure expanded by an assignment of the block. -/
private abbrev CRealize (φ : crawlSOLang.Sentence) : Prop :=
  @Sentence.Realize crawlSOLang A
    (@sumStructure _ _ A _ (crawlGuessBlock.structure ρ)) φ

private theorem realize_crTargetClause :
    CRealize ρ crTargetClause ↔ ∀ x : A, WSTarget x → ρ .set ![x] := by
  let := crawlGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  rw [crTargetClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl, hS]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩

private theorem realize_crRootExistsClause :
    CRealize ρ crRootExistsClause ↔ ∃ x : A, ρ .root ![x] := by
  let := crawlGuessBlock.structure ρ
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  rw [crRootExistsClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iExs, Formula.realize_rel₁,
    Term.realize_var, Sum.elim_inr, hR]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩

private theorem realize_crRootClause :
    CRealize ρ crRootClause ↔ ∀ x : A, ρ .root ![x] → WSRoot x ∧ ρ .set ![x] := by
  let := crawlGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  rw [crRootClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hS, hR]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h i hi => h (i 0) hi⟩

private theorem realize_crRootUniqueClause :
    CRealize ρ crRootUniqueClause ↔ ∀ x y : A, ρ .root ![x] → ρ .root ![y] → x = y := by
  let := crawlGuessBlock.structure ρ
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  rw [crRootUniqueClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₁, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, hR]
  exact ⟨fun h x y hx hy => h ![x, y] ⟨hx, hy⟩, fun h i hi => h (i 0) (i 1) hi.1 hi.2⟩

private theorem realize_crTransClause :
    CRealize ρ crTransClause ↔
      ∀ x y z : A, ρ .order ![x, y] → ρ .order ![y, z] → ρ .order ![x, z] := by
  let := crawlGuessBlock.structure ρ
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := crawlSOLang) (M := A) kCrLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [crTransClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hL]
  exact ⟨fun h x y z h₁ h₂ => h ![x, y, z] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

private theorem realize_crIrreflClause :
    CRealize ρ crIrreflClause ↔ ∀ x : A, ¬ρ .order ![x, x] := by
  let := crawlGuessBlock.structure ρ
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := crawlSOLang) (M := A) kCrLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [crIrreflClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, hL]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

private theorem realize_crStepClause :
    CRealize ρ crStepClause ↔ ∀ x : A, ρ .set ![x] → ¬ρ .root ![x] →
      ∃ y : A, (ρ .set ![y] ∧ WSEdge y x) ∧ ρ .order ![y, x] := by
  let := crawlGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hR : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrRootSym w ↔ ρ .root w := fun _ => Iff.rfl
  have hL : ∀ (w : Fin 2 → A),
      RelMap (L := crawlSOLang) (M := A) kCrLtSym w ↔ ρ .order w := fun _ => Iff.rfl
  rw [crStepClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hS, hR, hL]
  constructor
  · intro h x hx hnr
    obtain ⟨y, hy⟩ := h (fun _ => x) ⟨hx, hnr⟩
    exact ⟨y (), ⟨hy.1.1, hy.1.2⟩, hy.2⟩
  · intro h i hi
    obtain ⟨y, hy⟩ := h (i 0) hi.1 hi.2
    exact ⟨fun _ => y, ⟨hy.1.1, hy.1.2⟩, hy.2⟩

private theorem realize_crTotalClause :
    CRealize ρ crTotalClause ↔ ∀ x : A, ρ .set ![x] →
      ∃ y : A, ρ .inj ![x, y] ∧ WSMarked y := by
  let := crawlGuessBlock.structure ρ
  have hS : ∀ (w : Fin 1 → A),
      RelMap (L := crawlSOLang) (M := A) kCrSetSym w ↔ ρ .set w := fun _ => Iff.rfl
  have hI : ∀ (w : Fin 2 → A),
      RelMap (L := crawlSOLang) (M := A) kCrInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [crTotalClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hS, hI]
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := h (fun _ => x) hx
    exact ⟨y (), hy⟩
  · intro h i hi
    obtain ⟨y, hy⟩ := h (i 0) hi
    exact ⟨fun _ => y, hy⟩

private theorem realize_crInjClause :
    CRealize ρ crInjClause ↔ ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  let := crawlGuessBlock.structure ρ
  have hI : ∀ (w : Fin 2 → A),
      RelMap (L := crawlSOLang) (M := A) kCrInjSym w ↔ ρ .inj w := fun _ => Iff.rfl
  rw [crInjClause]
  simp only [CRealize, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, hI]
  exact ⟨fun h x x' y h₁ h₂ => h ![x, x', y] ⟨h₁, h₂⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1 hi.2⟩

private theorem realize_crawlKernel :
    CRealize ρ crawlKernel ↔
      (∀ x : A, WSTarget x → ρ .set ![x]) ∧
      (∃ x : A, ρ .root ![x]) ∧
      (∀ x : A, ρ .root ![x] → WSRoot x ∧ ρ .set ![x]) ∧
      (∀ x y : A, ρ .root ![x] → ρ .root ![y] → x = y) ∧
      (∀ x y z : A, ρ .order ![x, y] → ρ .order ![y, z] → ρ .order ![x, z]) ∧
      (∀ x : A, ¬ρ .order ![x, x]) ∧
      (∀ x : A, ρ .set ![x] → ¬ρ .root ![x] →
        ∃ y : A, (ρ .set ![y] ∧ WSEdge y x) ∧ ρ .order ![y, x]) ∧
      (∀ x : A, ρ .set ![x] → ∃ y : A, ρ .inj ![x, y] ∧ WSMarked y) ∧
      ∀ x x' y : A, ρ .inj ![x, y] → ρ .inj ![x', y] → x = x' := by
  rw [crawlKernel]
  simp only [CRealize, Sentence.Realize, Formula.realize_inf]
  exact and_congr (realize_crTargetClause ρ)
    (and_congr (realize_crRootExistsClause ρ)
      (and_congr (realize_crRootClause ρ)
        (and_congr (realize_crRootUniqueClause ρ)
          (and_congr (realize_crTransClause ρ)
            (and_congr (realize_crIrreflClause ρ)
              (and_congr (realize_crStepClause ρ)
                (and_congr (realize_crTotalClause ρ) (realize_crInjClause ρ))))))))

end Realize

/-- **Graph Crawling is `Σ₁`-definable**: guess the crawled set, its root, an
order certifying that everything crawled is reachable from the root, and an
injection of the crawled set into the marked set, then check the nine
conditions first-order. -/
theorem graphCrawling_sigmaSODefinable : SigmaSODefinable 1 GraphCrawling := by
  refine ⟨[crawlGuessBlock], rfl, crawlKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨-, hcr⟩
    obtain ⟨S, htargets, ⟨Rt, ⟨r, hr⟩, hRtP, huniq, Lt, htrans, hirr, hstep⟩, ⟨e⟩⟩ :=
      (crawlOn_iff_certificate _ _ _ _).mp hcr
    refine ⟨fun i => match i with
      | .set => fun w : Fin 1 → A => S (w 0)
      | .root => fun w : Fin 1 → A => Rt (w 0)
      | .order => fun w : Fin 2 → A => Lt (w 0) (w 1)
      | .inj => fun w : Fin 2 → A =>
          ∃ h : S (w 0), (e ⟨w 0, h⟩ : {x // WSMarked x}).1 = w 1, ?_⟩
    refine (realize_crawlKernel _).mpr ⟨htargets, ⟨r, hr⟩,
      fun x hx => ⟨(hRtP x hx).1, (hRtP x hx).2⟩, huniq, htrans, hirr, ?_,
      fun x hx => ⟨(e ⟨x, hx⟩).1, ⟨hx, rfl⟩, (e ⟨x, hx⟩).2⟩, ?_⟩
    · intro x hx hnr
      obtain ⟨y, hy, hadj, hlt⟩ := hstep x hx hnr
      exact ⟨y, ⟨hy, hadj⟩, hlt⟩
    · rintro x x' y ⟨h, hy⟩ ⟨h', hy'⟩
      exact congrArg Subtype.val (e.injective (Subtype.ext (hy.trans hy'.symm)))
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htargets, hex, hRtP, huniq, htrans, hirr, hstep, htot, hinj⟩ :=
      (realize_crawlKernel ρ).mp hρ
    have hch : ∀ x : {x : A // ρ .set ![x]}, ∃ y : A, ρ .inj ![x.1, y] ∧ WSMarked y :=
      fun x => htot x.1 x.2
    choose f hf1 hf2 using hch
    refine ⟨‹Finite A›, (crawlOn_iff_certificate _ _ _ _).mpr
      ⟨fun x => ρ .set ![x], htargets,
        ⟨fun x => ρ .root ![x], hex, fun x hx => hRtP x hx, huniq,
          fun x y => ρ .order ![x, y], htrans, hirr, ?_⟩,
        ⟨⟨fun x => ⟨f x, hf2 x⟩, fun x x' hxx' => ?_⟩⟩⟩⟩
    · intro x hx hnr
      obtain ⟨y, ⟨hy, hadj⟩, hlt⟩ := hstep x hx hnr
      exact ⟨y, hy, hadj, hlt⟩
    · have hval : f x = f x' := congrArg Subtype.val hxx'
      refine Subtype.ext (hinj x.1 x'.1 (f x) (hf1 x) ?_)
      rw [hval]
      exact hf1 x'

end SigmaOne

/-!
### Step 8: NP-hardness, by reduction from Set Cover

The hardness half follows the paper's proof: a set-cover instance becomes a
depth-2 website – a root linking to one page per set of the family, each set
page linking to the elements it contains – whose targets are the elements,
and a cover of at most `B` sets is exactly a crawl of at most `|U| + B + 1`
pages (the root, the chosen sets, and all the elements).

The budget `|U| + B + 1` is assembled per tag: the marked set of the produced
instance is the elements (on the element tag, `|U|`), the marked elements of
the source (on the set tag, `B`), and one copy of the *minimum* of the
input's order (on the root tag, `1`). The `+ 1` is why this is an *ordered*
reduction: a marked set with exactly one more element needs a canonical
singleton, which only an order provides. The root mark and the root's
out-edges are guarded by minimality too, so the junk copies of the root tag
are unmarked and edgeless.

Cardinality bookkeeping is by tag slices: a set of interpreted elements that
is a per-tag family of subsets of the input has as cardinality the sum of
the slices (`DescriptiveComplexity.ncard_tagged_eq_sum`), and both the crawl
produced from a cover and the marked set decompose this way, so both
directions of the correctness proof reduce to arithmetic on three slice
sizes.
-/

/-- Tags for the interpretation of website graphs in set systems. -/
inductive CrawlTag : Type
  /-- `(root, a)`: a copy of the crawl root (only the copy of the minimum is
  marked as root, linked, and counted). -/
  | root : CrawlTag
  /-- `(fam, a)`: the page of the set `a` of the family. -/
  | fam : CrawlTag
  /-- `(elem, a)`: the page of the ground element `a` – a target. -/
  | elem : CrawlTag
  deriving DecidableEq, Nonempty

instance : Fintype CrawlTag :=
  ⟨{.root, .fam, .elem}, fun t => by cases t <;> decide⟩

/-- The ground-element symbol over the ordered expansion of set systems. -/
abbrev oSSElem : (Language.setSystem.sum Language.order).Relations 1 := Sum.inl ssElem

/-- The family symbol over the ordered expansion of set systems. -/
abbrev oSSFam : (Language.setSystem.sum Language.order).Relations 1 := Sum.inl ssFam

/-- The incidence symbol over the ordered expansion of set systems. -/
abbrev oSSMem : (Language.setSystem.sum Language.order).Relations 2 := Sum.inl ssMem

/-- The mark symbol over the ordered expansion of set systems. -/
abbrev oSSMarked : (Language.setSystem.sum Language.order).Relations 1 := Sum.inl ssMarked

/-- The interpretation producing, from a set system, the depth-2 website of
the paper's reduction: the minimum's root copy links to every set of the
family, each set links to its elements, the elements are the targets, and the
marked set carries `|U| + B + 1`. -/
noncomputable def crawlInterp :
    FOInterpretation (Language.setSystem.sum Language.order) Language.siteGraph
      CrawlTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .edge => fun t =>
      match t 0, t 1 with
      | .root, .fam => minF (0, 0) ⊓ Relations.formula₁ oSSFam (Term.var (1, 0))
      | .fam, .elem =>
          (Relations.formula₂ oSSMem (Term.var (1, 0)) (Term.var (0, 0)) ⊓
            Relations.formula₁ oSSFam (Term.var (0, 0))) ⊓
            Relations.formula₁ oSSElem (Term.var (1, 0))
      | _, _ => ⊥
    | _, .root => fun t =>
      match t 0 with
      | .root => minF (0, 0)
      | _ => ⊥
    | _, .target => fun t =>
      match t 0 with
      | .elem => Relations.formula₁ oSSElem (Term.var (0, 0))
      | _ => ⊥
    | _, .marked => fun t =>
      match t 0 with
      | .root => minF (0, 0)
      | .fam => Relations.formula₁ oSSMarked (Term.var (0, 0))
      | .elem => Relations.formula₁ oSSElem (Term.var (0, 0))

section Characterizations

variable {A : Type} [Language.setSystem.Structure A] [LinearOrder A]

@[simp]
theorem crawl_edge_iff (t t' : CrawlTag) (w w' : Fin 1 → A) :
    WSEdge (A := crawlInterp.Map A) (t, w) (t', w') ↔
      (t = .root ∧ t' = .fam ∧ (∀ a : A, w 0 ≤ a) ∧ SSFam (w' 0)) ∨
      (t = .fam ∧ t' = .elem ∧
        (SSMem (w' 0) (w 0) ∧ SSFam (w 0)) ∧ SSElem (w' 0)) := by
  change RelMap (M := crawlInterp.Map A) wsEdge ![(t, w), (t', w')] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> cases t' <;>
    simp [crawlInterp, SSFam, SSElem, SSMem, Formula.realize_rel₁, Formula.realize_rel₂]

@[simp]
theorem crawl_root_iff (t : CrawlTag) (w : Fin 1 → A) :
    WSRoot (A := crawlInterp.Map A) (t, w) ↔ t = .root ∧ ∀ a : A, w 0 ≤ a := by
  change RelMap (M := crawlInterp.Map A) wsRoot ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [crawlInterp]

@[simp]
theorem crawl_target_iff (t : CrawlTag) (w : Fin 1 → A) :
    WSTarget (A := crawlInterp.Map A) (t, w) ↔ t = .elem ∧ SSElem (w 0) := by
  change RelMap (M := crawlInterp.Map A) wsTarget ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [crawlInterp, SSElem, Formula.realize_rel₁]

@[simp]
theorem crawl_marked_iff (t : CrawlTag) (w : Fin 1 → A) :
    WSMarked (A := crawlInterp.Map A) (t, w) ↔
      match t with
      | .root => ∀ a : A, w 0 ≤ a
      | .fam => SSMarked (w 0)
      | .elem => SSElem (w 0) := by
  change RelMap (M := crawlInterp.Map A) wsMarked ![(t, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [crawlInterp, SSMarked, SSElem, Formula.realize_rel₁]

end Characterizations

/-! ### Counting by tag slices -/

section Counting

variable {A : Type}

/-- Membership in a per-tag family of subsets of the input, stated at the raw
product type so that it applies to interpreted elements. -/
def InSlices (s : CrawlTag → Set A) (p : CrawlTag × (Fin 1 → A)) : Prop :=
  p.2 0 ∈ s p.1

private theorem sum_crawlTag (f : CrawlTag → ℕ) :
    ∑ t, f t = f .root + f .fam + f .elem := by
  change ∑ t ∈ ({.root, .fam, .elem} : Finset CrawlTag), f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  omega

variable [Language.setSystem.Structure A] [LinearOrder A]

omit [Language.setSystem.Structure A] [LinearOrder A] in
/-- The cardinality of a per-tag family of slices is the sum of the slice
sizes. -/
theorem ncard_inSlices [Finite A] (s : CrawlTag → Set A) :
    {p : crawlInterp.Map A | InSlices s p}.ncard =
      (s .root).ncard + (s .fam).ncard + (s .elem).ncard := by
  have h1 : {q : CrawlTag × A | q.2 ∈ s q.1}.ncard =
      {p : crawlInterp.Map A | InSlices s p}.ncard :=
    ncard_setOf_equiv ((Equiv.refl CrawlTag).prodCongr (Equiv.funUnique (Fin 1) A).symm)
      fun q => Iff.rfl
  rw [← h1, ncard_tagged_eq_sum s, sum_crawlTag]

/-- The tag slices of the crawl produced from a subfamily `G`: the minimum on
the root tag, `G` on the set tag, the ground elements on the element tag.
Instantiated at `G := SSMarked` this is also the decomposition of the marked
set. -/
def coverSlices (G : A → Prop) : CrawlTag → Set A
  | .root => {a : A | ∀ b : A, a ≤ b}
  | .fam => {a : A | G a}
  | .elem => {a : A | SSElem a}

omit [Language.setSystem.Structure A] in
/-- On a finite linearly ordered nonempty type, the set of minima is a
singleton. -/
theorem ncard_min_slice [Finite A] [Nonempty A] :
    {a : A | ∀ b : A, a ≤ b}.ncard = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  have hset : {a : A | ∀ b : A, a ≤ b} = {m} := by
    ext a
    constructor
    · intro ha
      exact le_antisymm (ha m) (hm a)
    · rintro rfl
      exact hm
  rw [hset, Set.ncard_singleton]

private theorem marked_iff_inSlices (p : crawlInterp.Map A) :
    WSMarked p ↔ InSlices (coverSlices SSMarked) p := by
  obtain ⟨t, w⟩ := p
  cases t
  · exact (crawl_marked_iff _ w).trans Iff.rfl
  · exact (crawl_marked_iff _ w).trans Iff.rfl
  · exact (crawl_marked_iff _ w).trans Iff.rfl

/-- The marked set of the interpreted website decomposes into tag slices. -/
theorem marked_eq_slices :
    {p : crawlInterp.Map A | WSMarked p} =
      {p : crawlInterp.Map A | InSlices (coverSlices SSMarked) p} :=
  Set.ext fun p => marked_iff_inSlices p

end Counting

/-! ### Correctness -/

section Correctness

variable {A : Type}

private theorem tuple_eta (w : Fin 1 → A) : w = fun _ => w 0 :=
  funext fun j => congrArg w (Subsingleton.elim j 0)

/-- Correctness of the interpretation: the set system has a small cover iff
the interpreted website has a cheap crawl. -/
theorem hasSmallSetCover_iff_crawl_map (A : Type) [Language.setSystem.Structure A]
    [LinearOrder A] [Finite A] [Nonempty A] :
    HasSmallSetCover A ↔ HasCheapCrawl (crawlInterp.Map A) := by
  have hfin : Finite (crawlInterp.Map A) := crawlInterp.map_finite A
  obtain ⟨m, hm⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  constructor
  · -- a cover of at most `B` sets becomes a crawl: root, chosen sets, all
    -- elements
    rintro ⟨-, G, hGF, hcov, hcard⟩
    refine ⟨hfin, (.root, fun _ => m), (crawl_root_iff _ _).mpr ⟨rfl, hm⟩,
      InSlices (coverSlices G), hm, ?_, ?_, ?_⟩
    · -- every target is crawled
      rintro ⟨t, w⟩ hT
      obtain ⟨rfl, hE⟩ := (crawl_target_iff t w).mp hT
      exact hE
    · -- everything crawled is reachable from the root
      rintro ⟨t, w⟩ hp
      cases t with
      | root =>
        have hw0 : w 0 = m := le_antisymm (hp m) (hm (w 0))
        have heq : ((CrawlTag.root, w) : crawlInterp.Map A) = (.root, fun _ => m) := by
          rw [tuple_eta w, hw0]
        rw [heq]
        exact Relation.ReflTransGen.refl
      | fam =>
        have hSr : InSlices (coverSlices G) (CrawlTag.root, fun _ => m) := hm
        have hG : G (w 0) := hp
        exact Relation.ReflTransGen.single ⟨hSr, hp,
          (crawl_edge_iff _ _ _ _).mpr (Or.inl ⟨rfl, rfl, hm, hGF _ hG⟩)⟩
      | elem =>
        have hE : SSElem (w 0) := hp
        obtain ⟨s, hGs, hmem⟩ := hcov (w 0) hE
        have hSr : InSlices (coverSlices G) (CrawlTag.root, fun _ => m) := hm
        have hSs : InSlices (coverSlices G) (CrawlTag.fam, fun _ => s) := hGs
        refine Relation.ReflTransGen.tail (b := (CrawlTag.fam, fun _ => s)) ?_ ?_
        · exact Relation.ReflTransGen.single ⟨hSr, hSs,
            (crawl_edge_iff _ _ _ _).mpr (Or.inl ⟨rfl, rfl, hm, hGF s hGs⟩)⟩
        · exact ⟨hSs, hp, (crawl_edge_iff _ _ _ _).mpr
            (Or.inr ⟨rfl, rfl, ⟨hmem, hGF s hGs⟩, hE⟩)⟩
    · -- the crawl stays within budget: compare the slices
      rw [marked_eq_slices, ncard_inSlices, ncard_inSlices]
      simp only [coverSlices]
      have h1 : {a : A | ∀ b : A, a ≤ b}.ncard = 1 := ncard_min_slice
      omega
  · -- a cheap crawl yields a cover: the sets whose page is crawled
    rintro ⟨-, r, hRr, S, hSr, hT, hreach, hcard⟩
    obtain ⟨tr, wr⟩ := r
    obtain ⟨htr, hwr⟩ := (crawl_root_iff tr wr).mp hRr
    subst htr
    -- crawled set pages are genuine sets of the family (reachability polices
    -- the junk: the only edges into the set tag come from the root, guarded)
    have hfam : ∀ w : Fin 1 → A, S (.fam, w) → SSFam (w 0) := by
      intro w hw
      rcases (hreach (.fam, w) hw).cases_tail with heq | ⟨c, -, hlink⟩
      · exact CrawlTag.noConfusion
          (congrArg (fun p : CrawlTag × (Fin 1 → A) => p.1) heq)
      · obtain ⟨tc, wc⟩ := c
        rcases (crawl_edge_iff tc .fam wc w).mp hlink.2.2 with ⟨-, -, -, hF⟩ | ⟨-, h, -⟩
        · exact hF
        · exact CrawlTag.noConfusion h
    -- every crawled element page is entered from a crawled set page
    have helem : ∀ w : Fin 1 → A, S (.elem, w) →
        ∃ s, S (.fam, fun _ => s) ∧ SSMem (w 0) s := by
      intro w hw
      rcases (hreach (.elem, w) hw).cases_tail with heq | ⟨c, -, hlink⟩
      · exact CrawlTag.noConfusion
          (congrArg (fun p : CrawlTag × (Fin 1 → A) => p.1) heq)
      · obtain ⟨tc, wc⟩ := c
        rcases (crawl_edge_iff tc .elem wc w).mp hlink.2.2 with
          ⟨-, h, -⟩ | ⟨htc, -, ⟨hmem, -⟩, -⟩
        · exact CrawlTag.noConfusion h
        · subst htc
          refine ⟨wc 0, ?_, hmem⟩
          rw [← tuple_eta wc]
          exact hlink.1
    refine ⟨‹Finite A›, fun s => S (.fam, fun _ => s), fun s hs => ?_, fun x hx => ?_, ?_⟩
    · exact hfam _ hs
    · obtain ⟨s, hs, hmem⟩ :=
        helem (fun _ => x) (hT (.elem, fun _ => x) ((crawl_target_iff _ _).mpr ⟨rfl, hx⟩))
      exact ⟨s, hs, hmem⟩
    · -- the budget bounds the number of crawled set pages
      have hsub : ∀ p : crawlInterp.Map A,
          InSlices (coverSlices fun s => S (.fam, fun _ => s)) p → S p := by
        intro p hp
        obtain ⟨t, w⟩ := p
        cases t with
        | root =>
          have hw : w = wr := funext fun j =>
            (congrArg w (Subsingleton.elim j 0)).trans
              ((le_antisymm (hp (wr 0)) (hwr (w 0))).trans
                (congrArg wr (Subsingleton.elim (0 : Fin 1) j)))
          exact (congrArg (Prod.mk CrawlTag.root) hw).symm ▸ hSr
        | fam =>
          have hG : S (.fam, fun _ => w 0) := hp
          exact (congrArg (Prod.mk CrawlTag.fam) (tuple_eta w)).symm ▸ hG
        | elem =>
          have hE : SSElem (w 0) := hp
          exact hT (.elem, w) ((crawl_target_iff _ _).mpr ⟨rfl, hE⟩)
      have hle : {p : crawlInterp.Map A |
            InSlices (coverSlices fun s => S (.fam, fun _ => s)) p}.ncard ≤
          {x | S x}.ncard :=
        Set.ncard_le_ncard (fun p hp => hsub p hp) (Set.toFinite _)
      rw [ncard_inSlices] at hle
      rw [marked_eq_slices, ncard_inSlices] at hcard
      simp only [coverSlices] at hle hcard
      have h1 : {a : A | ∀ b : A, a ≤ b}.ncard = 1 := ncard_min_slice
      change {s : A | S (.fam, fun _ => s)}.ncard ≤ {x : A | SSMarked x}.ncard
      omega

end Correctness

/-- **Set Cover ordered-FO-reduces to Graph Crawling** – the reduction of
[Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2], Prop. 4: a cover
of at most `B` sets is a crawl of at most `|U| + B + 1` pages of the depth-2
website. -/
noncomputable def setCover_ordered_fo_reduction_graphCrawling :
    SetCover ≤ᶠᵒ[≤] GraphCrawling where
  Tag := CrawlTag
  dim := 1
  toInterpretation := crawlInterp
  correct A _ _ _ _ := hasSmallSetCover_iff_crawl_map A

/-!
### Step 9: completeness

Membership and hardness combine into the completeness theorem – the
formalized counterpart of Prop. 4 of
[Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2]. Through the
faithfulness theorem of step 6, it is a statement about the packaged
concrete instances of step 1: `ConcreteCrawlHolds` is decided by a problem
that is NP-complete, over an encoding that provably neither pads nor
compresses.
-/

/-- Graph Crawling is in NP. -/
theorem graphCrawling_mem_NP : GraphCrawling ∈ NP := graphCrawling_sigmaSODefinable

/-- Graph Crawling is NP-hard: Set Cover, which is NP-hard, reduces to it by
an ordered FO reduction. -/
theorem graphCrawling_NP_hard : NP.Hard GraphCrawling :=
  NP.hard_of_orderedReduction setCover_ordered_fo_reduction_graphCrawling setCover_NP_hard

/-- **The graph crawling problem is NP-complete**
([Gauquier–Manolescu–Senellart 2026][gauquier2026efficient2], Prop. 4). -/
theorem graphCrawling_NP_complete : NP.Complete GraphCrawling :=
  ⟨graphCrawling_mem_NP, graphCrawling_NP_hard⟩

/-- The image of the hardness reduction is well-formed: the only root-marked
page of an interpreted website is the minimum\'s root copy. -/
theorem crawlInterp_wf (A : Type) [Language.setSystem.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] :
    DecisionProblem.ofSentence crawlWFSentence (crawlInterp.Map A) := by
  obtain ⟨mn, hmn⟩ : ∃ m : A, ∀ a : A, m ≤ a := Finite.exists_min id
  refine realize_crawlWFSentence.mpr ⟨(.root, fun _ => mn),
    (crawl_root_iff _ _).mpr ⟨rfl, hmn⟩, ?_⟩
  rintro ⟨t, w⟩ hy
  obtain ⟨rfl, hw⟩ := (crawl_root_iff t w).mp hy
  have hw0 : w 0 = mn := le_antisymm (hw mn) (hmn (w 0))
  exact congrArg (Prod.mk CrawlTag.root) (by rw [tuple_eta w, hw0])

/-- **Well-formed graph crawling is NP-complete**: crawling restricted to
websites with exactly one root – the instances the decoder of step 6
handles. Both halves are one-line upgrades of the plain completeness proof
(`OrderedFOReduction.withInvariant`, `SigmaSODefinable.inf_ofSentence`). -/
theorem crawlWF_NP_complete :
    NP.Complete (DecisionProblem.ofSentence crawlWFSentence ⊓ GraphCrawling) :=
  ⟨graphCrawling_sigmaSODefinable.inf_ofSentence crawlWFSentence,
    NP.hard_of_orderedReduction (setCover_ordered_fo_reduction_graphCrawling.withInvariant _
      fun A _ _ _ _ => crawlInterp_wf A) setCover_NP_hard⟩

end DescriptiveComplexity
