import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Lax904597.Classes
import Lax799700.Problems
import Lax117614.WebsiteGraphs

/-!
---
title: The graph crawling problem
type: definition
---
A crawl of a website graph is a set of pages containing a root page and
every target page, each of its pages reachable from the root by hyperlinks
inside the set; this is the node set of a rooted subtree, the crawl of
Gauquier, Manolescu and Senellart (EDBT 2026). A website graph has a cheap
crawl when it is finite and some crawl has at most as many pages as the
marked set has elements, the budget. The graph crawling problem is the
decision problem on website graphs whose yes-instances are the website
graphs isomorphic to one with a cheap crawl.
-/

namespace Lax117614.GraphCrawlingProblem

open FirstOrder

open FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes Lax799700.Problems Lax117614.WebsiteGraphs

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

end Reachability

section Generic

variable {A : Type}

/-- Some marked root admits a crawl: a set of pages containing the root and
every target, entirely reachable from the root inside itself, of size (the
paper's total cost, at unit page costs) at most the number encoded by the
marked set. -/
def CrawlOn (Adjp : A → A → Prop) (Rp Tp Kp : A → Prop) : Prop :=
  ∃ r, Rp r ∧ ∃ S : A → Prop, S r ∧ (∀ x, Tp x → S x) ∧ ReachesAllOn Adjp r S ∧
    {x | S x}.ncard ≤ {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [siteGraph.Structure A]

/-- A website graph admits a crawl within budget: a set of pages containing
the marked root and every target, reachable from the root inside itself, with
at most as many pages as the marked set has elements. (Finiteness of the
universe is part of the property: cardinality thresholds are only meaningful
on finite structures.) -/
def HasCheapCrawl : Prop :=
  Finite A ∧ CrawlOn (WSEdge (A := A)) WSRoot WSTarget WSMarked

end Problem

/-- GRAPH CRAWLING, decision variant at unit page costs: does the website
graph satisfy `HasCheapCrawl`? -/
def GraphCrawling : DecisionProblem siteGraph :=
  DecisionProblem.ofPred HasCheapCrawl

end Lax117614.GraphCrawlingProblem
