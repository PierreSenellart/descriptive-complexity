import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Lax117614.WebsiteGraphs
import Lax117614.GraphCrawlingProblem

/-!
---
title: Packaged crawling instances
type: definition
---
A packaged crawling instance is the website as a user handles it: a page
count, a finite set of hyperlinks, a root page, a finite set of target pages
and a budget, clamped to the page count since a crawl never has more pages
than the site. Its size is the textbook one, pages, links, targets and the
budget in unary, and its semantics the textbook one, some set of pages
containing the root and the targets, reachable from the root inside itself,
within budget. The encoder computes the website graph of an instance, on its
pages as universe. A presentation is a raw relation table on a finite
universe; a presented website is well-formed when it has exactly one root
page, which a first-order sentence states, and the decoder reads a packaged
instance off a well-formed presented website. Well-formed graph crawling is
the graph crawling problem restricted to well-formed website graphs.
-/

namespace Lax117614.CrawlInstances

open FirstOrder

open FirstOrder.Language Structure

open Lax904597.Problems Lax904597.Classes Lax799700.Problems
open Lax117614.WebsiteGraphs Lax117614.GraphCrawlingProblem

/-- A concretely presented finite `L`-structure: a size and a computable
relation table. This is the input type of decoders – the “raw bytes” a
decoding computation reads. -/
structure FinPresentation (L : Language.{0, 0}) where
  /-- The number of elements. -/
  card : ℕ
  /-- The relations, as computations on `Fin card`. -/
  relBool : ∀ {n}, L.Relations n → (Fin n → Fin card) → Bool

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str {L : Language.{0, 0}} [L.IsRelational] (S : FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

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

/-- The encoder, standalone and auditable: a plain `def`, so the compiler
vouches that it computes. -/
def crawlRelBool (i : CrawlInstance) {n : ℕ} (R : siteGraph.Relations n) :
    (Fin n → Fin (i.n + 1)) → Bool :=
  match n, R with
  | _, .edge => fun x => decide ((x 0, x 1) ∈ i.edges)
  | _, .root => fun x => decide (x 0 = i.root)
  | _, .target => fun x => decide (x 0 ∈ i.targets)
  | _, .marked => fun x => decide ((x 0).1 < i.budget.1)

/-- The website graph a packaged instance encodes: the pages themselves as
universe, the relations the encoder's computations read as propositions. -/
instance crawlStructure (i : CrawlInstance) : siteGraph.Structure (Fin (i.n + 1)) where
  funMap f := isEmptyElim f
  RelMap R x := crawlRelBool i R x = true

/-- Well-formedness of a website graph: exactly one root page. What makes an
honest decoder possible. -/
noncomputable def crawlWFSentence : siteGraph.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1)
  (FirstOrder.Language.Relations.formula₁ wsRoot (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((FirstOrder.Language.Relations.formula₁ wsRoot
          (FirstOrder.Language.Term.var (Sum.inr 0))).imp
        (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))))))

section Decoder

variable (S : FinPresentation siteGraph)

/-- The root pages of a presented website. -/
def crawlRoots : Finset (Fin S.card) :=
  Finset.univ.filter fun x => S.relBool wsRoot ![x]

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

end Decoder

/-- Graph crawling on well-formed websites: those with exactly one root, the
ones the decoder handles. -/
def WFGraphCrawling : DecisionProblem siteGraph :=
  DecisionProblem.ofPred fun (A : Type) [siteGraph.Structure A] =>
    A ⊨ crawlWFSentence ∧ HasCheapCrawl A

end Lax117614.CrawlInstances
