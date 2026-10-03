import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Lattice

/-!
---
title: Website graphs
type: definition
---
A website graph is a finite structure with a binary relation, the
hyperlinks between pages, and three unary relations: the root pages, the
target pages, and a marked set of pages whose cardinality is the crawling
budget, in unary representation. This is the website of Gauquier, Manolescu
and Senellart (EDBT 2026) at unit page costs, the budget being then a
number of pages.
-/

namespace Lax117614.WebsiteGraphs

open FirstOrder

open FirstOrder.Language Structure

/-- The relation symbols of the language. -/
inductive siteGraphRel : ℕ → Type where
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
def siteGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, siteGraphRel⟩

instance instIsRelationalSiteGraph : FirstOrder.Language.IsRelational siteGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `edge a b`: a hyperlink from page `a` to page `b`. -/
abbrev wsEdge : siteGraph.Relations 2 :=
  .edge

/-- `root a`: the page `a` is the crawl's starting point. -/
abbrev wsRoot : siteGraph.Relations 1 :=
  .root

/-- `target a`: the page `a` must be crawled. -/
abbrev wsTarget : siteGraph.Relations 1 :=
  .target

/-- `marked a`: the page `a` belongs to the marked set carrying the
  budget. -/
abbrev wsMarked : siteGraph.Relations 1 :=
  .marked

section Shorthands

variable {A : Type} [siteGraph.Structure A]

/-- A hyperlink in a website graph. -/
def WSEdge (a b : A) : Prop := RelMap wsEdge ![a, b]

/-- Being the root of a website graph. -/
def WSRoot (a : A) : Prop := RelMap wsRoot ![a]

/-- Being a target page. -/
def WSTarget (a : A) : Prop := RelMap wsTarget ![a]

/-- Belonging to the marked set carrying the budget. -/
def WSMarked (a : A) : Prop := RelMap wsMarked ![a]

end Shorthands

end Lax117614.WebsiteGraphs
