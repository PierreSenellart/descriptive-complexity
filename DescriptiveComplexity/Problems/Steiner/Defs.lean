/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Numbers.Unary
import DescriptiveComplexity.Problems.CliqueFamily.Defs

/-!
# Steiner Tree: definitions

STEINER TREE ([Karp 1972][karp1972reducibility]) in its *node-weighted* form
with unit weights: given a graph, a set of *terminals* and a threshold `k`, is
there a connected set of vertices containing every terminal and using at most
`k` non-terminals? The vocabulary `FirstOrder.Language.steinerGraph` is that of
graphs with two unary marks – the terminals, and the marked set carrying `k`
in the unary representation (A) of `DescriptiveComplexity.Numbers.Unary`.

Karp's original problem weights *edges* and bounds the total weight; on a tree
the two readings differ by one (`#edges = #vertices - 1`), so the reduction
below would carry over, but the bridge between them needs the fact that a
connected graph has at least `n - 1` edges. Mathlib has it only for trees on a
whole vertex type (`SimpleGraph.IsTree.card_edgeFinset`), so the edge-weighted
version waits for that glue; the node-weighted version is the standard variant
and is what this file formalizes.

## Connectivity, and its first-order certificate

Connectivity (`DescriptiveComplexity.ConnectedOn`) is stated with
`Relation.ReflTransGen` over the *symmetric* restriction of adjacency to the
chosen set, so it is the usual undirected notion and is not first-order. As
for acyclicity in `DescriptiveComplexity.Problems.Feedback`, what saves the
membership proof is a certificate: a root of the chosen set together with a
strict partial order in which every other chosen vertex has a chosen neighbour
strictly below it (`DescriptiveComplexity.connectedOn_iff_exists_root_order`). Walking
down that order reaches the root, and the root joins any two vertices.

Producing the certificate from connectivity is the direction with content: it
needs a *distance*, which `Relation.ReflTransGen` does not carry. The
`DescriptiveComplexity.reachIn` staging below supplies it – reachability in at most
`n` steps, with `Nat.find` picking the least such `n` – and that is the whole
of the extra machinery. It is stated for an arbitrary relation, so the
Hamilton problems and the edge-weighted Steiner tree can reuse it.
-/

/- The language of terminal-marked graphs lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the language of graphs with terminals. -/
inductive steinerRel : ℕ → Type
  /-- `adj a b`: there is an edge between `a` and `b`. -/
  | adj : steinerRel 2
  /-- `terminal a`: the vertex `a` must be spanned. -/
  | terminal : steinerRel 1
  /-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
  | marked : steinerRel 1
  deriving DecidableEq

/-- The relational language of graphs with terminals: adjacency, a set of
terminals to be spanned, and a marked set whose cardinality is the budget of
non-terminals. -/
protected def steinerGraph : Language :=
  ⟨fun _ => Empty, steinerRel⟩
  deriving IsRelational

/-- The adjacency symbol of terminal-marked graphs. -/
abbrev stAdj : Language.steinerGraph.Relations 2 := .adj

/-- The terminal symbol of terminal-marked graphs. -/
abbrev stTerminal : Language.steinerGraph.Relations 1 := .terminal

/-- The mark symbol of terminal-marked graphs. -/
abbrev stMarked : Language.steinerGraph.Relations 1 := .marked

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Connectivity and its certificate -/

section Connectivity

variable {A : Type}

/-- The edges available inside a chosen set: adjacency in either direction,
restricted to the set. -/
def Link (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ (Adjp a b ∨ Adjp b a)

theorem link_symm {Adjp : A → A → Prop} {S : A → Prop} {a b : A} (h : Link Adjp S a b) :
    Link Adjp S b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- A set of vertices is connected if any two of its members are joined by a
path inside it. -/
def ConnectedOn (Adjp : A → A → Prop) (S : A → Prop) : Prop :=
  ∀ x y, S x → S y → Relation.ReflTransGen (Link Adjp S) x y

/-! #### Reachability in a bounded number of steps

`Relation.ReflTransGen` carries no length, and the certificate needs one: the
order it guesses is “distance to the root”. -/

/-- Reachability in at most `n` steps. -/
def reachIn (R : A → A → Prop) : ℕ → A → A → Prop
  | 0, x, y => x = y
  | n + 1, x, y => reachIn R n x y ∨ ∃ z, reachIn R n x z ∧ R z y

theorem reachIn_succ_of_reachIn {R : A → A → Prop} {n : ℕ} {x y : A}
    (h : reachIn R n x y) : reachIn R (n + 1) x y := Or.inl h

/-- Reachability is reachability in some bounded number of steps. -/
theorem reflTransGen_iff_exists_reachIn (R : A → A → Prop) (x y : A) :
    Relation.ReflTransGen R x y ↔ ∃ n, reachIn R n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, hn, hbc⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing y with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ k ih =>
      rcases hn with h | ⟨z, hz, hzy⟩
      · exact ih _ h
      · exact (ih _ hz).tail hzy

/-- The reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem reflTransGen_symm {R : A → A → Prop} (hsymm : ∀ a b, R a b → R b a) {x y : A}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

/-! #### The certificate -/

open Classical in
/-- The distance from `r`: the least number of steps in which `x` is
reachable (and `0` when it is not reachable at all, a value the certificate
never looks at). -/
private noncomputable def rdist (R : A → A → Prop) (r x : A) : ℕ :=
  if h : ∃ n, reachIn R n r x then Nat.find h else 0

private theorem rdist_step {R : A → A → Prop} {r x : A} (hx : Relation.ReflTransGen R r x)
    (hne : x ≠ r) : ∃ z, R z x ∧ rdist R r z < rdist R r x := by
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

/-- **Connectivity is first-order certifiable**: a set is connected exactly
when, from any of its members chosen as root, some strict partial order makes
every other member have a neighbour strictly below it. Walking down the order
reaches the root, and the root joins any two members. -/
theorem connectedOn_iff_exists_root_order [Finite A] (Adjp : A → A → Prop) (S : A → Prop) :
    ConnectedOn Adjp S ↔ ∀ r, S r → ∃ Lt : A → A → Prop,
      (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
      ∀ x, S x → x ≠ r → ∃ y, Link Adjp S x y ∧ Lt y x := by
  constructor
  · intro hconn r hr
    refine ⟨fun y x => rdist (Link Adjp S) r y < rdist (Link Adjp S) r x,
      fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, fun _ => lt_irrefl _, fun x hx hne => ?_⟩
    obtain ⟨z, hzx, hlt⟩ := rdist_step (hconn r x hr hx) hne
    exact ⟨z, link_symm hzx, hlt⟩
  · intro h x y hx hy
    obtain ⟨Lt, htrans, hirr, hstep⟩ := h x hx
    haveI : IsTrans A Lt := ⟨htrans⟩
    haveI : Std.Irrefl Lt := ⟨hirr⟩
    have hwf : WellFounded Lt := Finite.wellFounded_of_trans_of_irrefl Lt
    have hreach : ∀ z, S z → Relation.ReflTransGen (Link Adjp S) z x := by
      intro z
      induction z using hwf.induction with
      | _ z ih =>
        intro hz
        rcases Classical.em (z = x) with rfl | hne
        · exact Relation.ReflTransGen.refl
        · obtain ⟨w, hlink, hlt⟩ := hstep z hz hne
          exact Relation.ReflTransGen.head hlink (ih w hlt hlink.2.1)
    exact reflTransGen_symm (fun _ _ hab => link_symm hab) (hreach y hy)

/-- The existential form of the certificate, the one a `Σ₁` definition
guesses: a *root relation* (constrained to hold of at most one element of the
set) together with the order. The empty set is connected and has no root,
which is why the root is guessed as a relation rather than an element. -/
theorem connectedOn_iff_exists_root [Finite A] (Adjp : A → A → Prop) (S : A → Prop) :
    ConnectedOn Adjp S ↔ ∃ Rt : A → Prop, (∀ x, Rt x → S x) ∧
      (∀ x y, Rt x → Rt y → x = y) ∧ ∃ Lt : A → A → Prop,
        (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
        ∀ x, S x → ¬Rt x → ∃ y, Link Adjp S x y ∧ Lt y x := by
  constructor
  · intro hconn
    rcases Classical.em (∃ r, S r) with ⟨r, hr⟩ | hempty
    · obtain ⟨Lt, htrans, hirr, hstep⟩ :=
        (connectedOn_iff_exists_root_order Adjp S).mp hconn r hr
      exact ⟨fun x => x = r, fun x hx => hx ▸ hr, fun x y hx hy => hx.trans hy.symm,
        Lt, htrans, hirr, fun x hx hne => hstep x hx hne⟩
    · exact ⟨fun _ => False, fun _ h => h.elim, fun _ _ h => h.elim,
        fun _ _ => False, fun _ _ _ h => h.elim, fun _ h => h,
        fun x hx _ => absurd ⟨x, hx⟩ hempty⟩
  · rintro ⟨Rt, hRtS, huniq, Lt, htrans, hirr, hstep⟩
    haveI : IsTrans A Lt := ⟨htrans⟩
    haveI : Std.Irrefl Lt := ⟨hirr⟩
    have hwf : WellFounded Lt := Finite.wellFounded_of_trans_of_irrefl Lt
    have hroot : ∀ z, S z → ∃ r, Rt r ∧ Relation.ReflTransGen (Link Adjp S) z r := by
      intro z
      induction z using hwf.induction with
      | _ z ih =>
        intro hz
        rcases Classical.em (Rt z) with hr | hr
        · exact ⟨z, hr, Relation.ReflTransGen.refl⟩
        · obtain ⟨w, hlink, hlt⟩ := hstep z hz hr
          obtain ⟨r, hrRt, hpath⟩ := ih w hlt hlink.2.1
          exact ⟨r, hrRt, Relation.ReflTransGen.head hlink hpath⟩
    intro x y hx hy
    obtain ⟨r, hr, hxr⟩ := hroot x hx
    obtain ⟨r', hr', hyr'⟩ := hroot y hy
    rw [huniq r' r hr' hr] at hyr'
    exact hxr.trans (reflTransGen_symm (fun _ _ hab => link_symm hab) hyr')

/-- `ConnectedOn` transports along an equivalence commuting with the
adjacency relations and the chosen sets. -/
theorem ConnectedOn.of_equiv {B : Type} (u : B ≃ A) {AdjB : B → B → Prop} {SB : B → Prop}
    {AdjA : A → A → Prop} {SA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hS : ∀ b, SB b ↔ SA (u b))
    (h : ConnectedOn AdjB SB) : ConnectedOn AdjA SA := by
  have hlink : ∀ a a', Link AdjA SA a a' → Link AdjB SB (u.symm a) (u.symm a') := by
    rintro a a' ⟨h₁, h₂, h₃⟩
    exact ⟨(hS _).mpr (by simpa using h₁), (hS _).mpr (by simpa using h₂),
      by rcases h₃ with h | h
         · exact Or.inl ((hadj _ _).mpr (by simpa using h))
         · exact Or.inr ((hadj _ _).mpr (by simpa using h))⟩
  intro x y hx hy
  have hxy := h (u.symm x) (u.symm y) ((hS _).mpr (by simpa using hx))
    ((hS _).mpr (by simpa using hy))
  have hmap : ∀ {b b' : B}, Relation.ReflTransGen (Link AdjB SB) b b' →
      Relation.ReflTransGen (Link AdjA SA) (u b) (u b') := by
    intro b b' hb
    induction hb with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hcd ih =>
      refine ih.tail ⟨(hS _).mp hcd.1, (hS _).mp hcd.2.1, ?_⟩
      rcases hcd.2.2 with h | h
      · exact Or.inl ((hadj _ _).mp h)
      · exact Or.inr ((hadj _ _).mp h)
  simpa using hmap hxy

end Connectivity

/-! #### Connectivity costs edges

The certificate gives each non-root member of a connected set a *parent edge*,
and that assignment is injective: two members sharing an edge would have to be
each other's parent, hence strictly below each other. This is the
`n - 1` edge bound for connected graphs, in the form the edge-weighted Steiner
tree needs, and it is proved from the certificate rather than from a spanning
tree. -/

/-- **A connected set costs edges**: a set connected through `T` has at most
one more element than `T` has pairs. -/
theorem ncard_le_ncard_of_connected [Finite A] {T : A → A → Prop} {S : A → Prop} {r : A}
    (hr : S r) (hconn : ConnectedOn T S) :
    {x | S x ∧ x ≠ r}.ncard ≤ {p : A × A | T p.1 p.2}.ncard := by
  classical
  obtain ⟨Lt, htrans, hirr, hstep⟩ := (connectedOn_iff_exists_root_order T S).mp hconn r hr
  -- the parent edge of a non-root member, oriented as it occurs in `T`
  have hpar : ∀ x : {x : A // S x ∧ x ≠ r}, ∃ q : A × A, T q.1 q.2 ∧
      ((q.1 = x.1 ∧ Lt q.2 x.1) ∨ (q.2 = x.1 ∧ Lt q.1 x.1)) := by
    rintro ⟨x, hx, hxr⟩
    obtain ⟨y, hlink, hlt⟩ := hstep x hx hxr
    rcases hlink.2.2 with h | h
    · exact ⟨(x, y), h, Or.inl ⟨rfl, hlt⟩⟩
    · exact ⟨(y, x), h, Or.inr ⟨rfl, hlt⟩⟩
  choose f hf1 hf2 using hpar
  have hinj : Function.Injective fun x : {x : A // S x ∧ x ≠ r} =>
      (⟨f x, hf1 x⟩ : {p : A × A // T p.1 p.2}) := by
    intro x x' hxx'
    have hval : f x = f x' := congrArg Subtype.val hxx'
    rcases hf2 x with ⟨h1, hlt⟩ | ⟨h1, hlt⟩ <;> rcases hf2 x' with ⟨h1', hlt'⟩ | ⟨h1', hlt'⟩
    · exact Subtype.ext (by rw [← h1, hval, h1'])
    · -- `x` is the source of the shared edge and `x'` its target: each is below the other
      exfalso
      have e2 : (f x).2 = x'.1 := by rw [hval]; exact h1'
      have e1 : (f x').1 = x.1 := by rw [← hval]; exact h1
      exact hirr x.1 (htrans _ _ _ (e1 ▸ hlt') (e2 ▸ hlt))
    · exfalso
      have e2 : (f x').2 = x.1 := by rw [← hval]; exact h1
      have e1 : (f x).1 = x'.1 := by rw [hval]; exact h1'
      exact hirr x.1 (htrans _ _ _ (e2 ▸ hlt') (e1 ▸ hlt))
    · exact Subtype.ext (by rw [← h1, hval, h1'])
  have hcard : Nat.card {x : A // S x ∧ x ≠ r} ≤ Nat.card {p : A × A // T p.1 p.2} :=
    Nat.card_le_card_of_injective _ hinj
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard

/-! ### The problem -/

section Generic

variable {A : Type}

/-- Some connected set contains every terminal and uses at most as many
non-terminals as the number encoded by the marked set. -/
def SteinerOn (Adjp : A → A → Prop) (Term Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard ≤ {x | Kp x}.ncard

/-- The certified form, with connectivity witnessed by a root and an order and
the threshold by an injection: the shape the second-order definition
guesses. -/
theorem steinerOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Term Kp : A → Prop) :
    SteinerOn Adjp Term Kp ↔ ∃ S : A → Prop, (∀ x, Term x → S x) ∧
      (∃ Rt : A → Prop, (∀ x, Rt x → S x) ∧ (∀ x y, Rt x → Rt y → x = y) ∧
        ∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
          ∀ x, S x → ¬Rt x → ∃ y, Link Adjp S x y ∧ Lt y x) ∧
      Nonempty ({x // S x ∧ ¬Term x} ↪ {x // Kp x}) :=
  exists_congr fun S =>
    and_congr_right fun _ =>
      and_congr (connectedOn_iff_exists_root Adjp S)
        (nonempty_embedding_iff_ncard_le (fun x => S x ∧ ¬Term x) Kp).symm

variable {B : Type}

/-- Some set of edges of the graph, connecting a set that contains every
terminal, is at most as large as the number encoded by the marked set: the
*edge-weighted* Steiner tree with unit weights, Karp's original reading.

The chosen edges are given as a set of ordered pairs, one per edge, and
connectivity reads them symmetrically
(`DescriptiveComplexity.ConnectedOn`); a witness listing both orientations of an edge
merely pays for it twice, so the yes-instances are unaffected. The threshold
compares a count of *pairs* with a count of *elements*, which is meaningful
because a threshold is just a number – and necessary here, since an edge set
can be quadratically larger than the universe. -/
def SteinerEdgeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) : Prop :=
  ∃ T : A → A → Prop, ∃ S : A → Prop,
    (∀ a b, T a b → Adjp a b) ∧ (∀ x, Term x → S x) ∧ ConnectedOn T S ∧
    {p : A × A | T p.1 p.2}.ncard ≤ {x | Kp x}.ncard

/-- The certified form of the edge-weighted problem. -/
theorem steinerEdgeOn_iff_certificate [Finite A] (Adjp : A → A → Prop) (Term Kp : A → Prop) :
    SteinerEdgeOn Adjp Term Kp ↔ ∃ T : A → A → Prop, ∃ S : A → Prop,
      (∀ a b, T a b → Adjp a b) ∧ (∀ x, Term x → S x) ∧
      (∃ Rt : A → Prop, (∀ x, Rt x → S x) ∧ (∀ x y, Rt x → Rt y → x = y) ∧
        ∃ Lt : A → A → Prop, (∀ x y z, Lt x y → Lt y z → Lt x z) ∧ (∀ x, ¬Lt x x) ∧
          ∀ x, S x → ¬Rt x → ∃ y, Link T S x y ∧ Lt y x) ∧
      Nonempty ({p : A × A // T p.1 p.2} ↪ {x // Kp x}) :=
  exists_congr fun T => exists_congr fun S =>
    and_congr_right fun _ =>
      and_congr_right fun _ =>
        and_congr (connectedOn_iff_exists_root T S)
          (nonempty_embedding_iff_ncard_le' (fun p : A × A => T p.1 p.2) Kp).symm

/-- `SteinerOn` transports along an equivalence commuting with the three
predicates. -/
theorem SteinerOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) (h : SteinerOn AdjB TermB KB) :
    SteinerOn AdjA TermA KA := by
  obtain ⟨S, hterms, hconn, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), fun x hx => hterms _ ((hterm _).mpr (by simpa using hx)),
    ConnectedOn.of_equiv u hadj (fun b => by simp) hconn, ?_⟩
  rw [← ncard_setOf_equiv u hK,
    ← ncard_setOf_equiv (KB := fun b => S b ∧ ¬TermB b) u (fun b => by
      simp only [hterm b]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using h₁, h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using h₁, h₂⟩)]
  exact hcard

/-- `SteinerOn` transports along an equivalence, iff version. -/
theorem SteinerOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) : SteinerOn AdjB TermB KB ↔ SteinerOn AdjA TermA KA :=
  ⟨SteinerOn.of_equiv u hadj hterm hK,
    SteinerOn.of_equiv u.symm (fun a a' => by rw [hadj]; simp) (fun a => by rw [hterm]; simp)
      fun a => by rw [hK]; simp⟩

end Generic

/-- `SteinerEdgeOn` transports along an equivalence commuting with the three
predicates. -/
theorem SteinerEdgeOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) (h : SteinerEdgeOn AdjB TermB KB) :
    SteinerEdgeOn AdjA TermA KA := by
  obtain ⟨T, S, hsub, hterms, hconn, hcard⟩ := h
  refine ⟨fun a a' => T (u.symm a) (u.symm a'), fun a => S (u.symm a), fun a a' haa' => ?_,
    fun x hx => hterms _ ((hterm _).mpr (by simpa using hx)),
    ConnectedOn.of_equiv u (fun b b' => by simp) (fun b => by simp) hconn, ?_⟩
  · have h := (hadj (u.symm a) (u.symm a')).mp (hsub _ _ haa')
    simpa using h
  · rw [← ncard_setOf_equiv u hK,
      ← ncard_setOf_equiv₂ (RB := T) (RA := fun a a' => T (u.symm a) (u.symm a')) u
        (fun b b' => by simp)]
    exact hcard

/-- `SteinerEdgeOn` transports along an equivalence, iff version. -/
theorem SteinerEdgeOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {TermB KB : B → Prop}
    {AdjA : A → A → Prop} {TermA KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hterm : ∀ b, TermB b ↔ TermA (u b))
    (hK : ∀ b, KB b ↔ KA (u b)) :
    SteinerEdgeOn AdjB TermB KB ↔ SteinerEdgeOn AdjA TermA KA :=
  ⟨SteinerEdgeOn.of_equiv u hadj hterm hK,
    SteinerEdgeOn.of_equiv u.symm (fun a a' => by rw [hadj]; simp) (fun a => by rw [hterm]; simp)
      fun a => by rw [hK]; simp⟩

section Problem

section Shorthands

variable {A : Type} [Language.steinerGraph.Structure A]

/-- Adjacency in a graph with terminals. -/
def STAdj (a b : A) : Prop := RelMap stAdj ![a, b]

/-- Being a terminal. -/
def STTerminal (a : A) : Prop := RelMap stTerminal ![a]

/-- Belonging to the marked set carrying the threshold. -/
def STMarked (a : A) : Prop := RelMap stMarked ![a]

end Shorthands

variable (A : Type) [Language.steinerGraph.Structure A]

/-- A graph with terminals admits a connected set spanning the terminals and
using at most as many non-terminals as its marked set has elements.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSteinerTree : Prop :=
  Finite A ∧ SteinerOn (STAdj (A := A)) STTerminal STMarked

end Problem

section Iso

variable {A B : Type} [Language.steinerGraph.Structure A] [Language.steinerGraph.Structure B]

/-- The Steiner-tree property is isomorphism-invariant. -/
theorem hasSmallSteinerTree_iso (e : A ≃[Language.steinerGraph] B) :
    HasSmallSteinerTree A ↔ HasSmallSteinerTree B :=
  and_congr e.toEquiv.finite_iff
    (SteinerOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e stAdj a b)
      (fun a => relMap_equiv₁ e stTerminal a) fun a => relMap_equiv₁ e stMarked a)

end Iso

/-- A graph with terminals admits a set of edges connecting its terminals, of
size at most the number encoded by the marked set. -/
def HasSmallEdgeSteinerTree (A : Type) [Language.steinerGraph.Structure A] : Prop :=
  Finite A ∧ SteinerEdgeOn (STAdj (A := A)) STTerminal STMarked

/-- The edge-weighted Steiner-tree property is isomorphism-invariant. -/
theorem hasSmallEdgeSteinerTree_iso {A B : Type} [Language.steinerGraph.Structure A]
    [Language.steinerGraph.Structure B] (e : A ≃[Language.steinerGraph] B) :
    HasSmallEdgeSteinerTree A ↔ HasSmallEdgeSteinerTree B :=
  and_congr e.toEquiv.finite_iff
    (SteinerEdgeOn.equiv_iff e.toEquiv (fun a b => relMap_equiv₂ e stAdj a b)
      (fun a => relMap_equiv₁ e stTerminal a) fun a => relMap_equiv₁ e stMarked a)

/-- STEINER TREE (edge-weighted, unit weights) – Karp's original reading – as a
problem on graphs with terminals: is there a set of at most `k` edges
connecting all the terminals? -/
def EdgeSteinerTree : DecisionProblem Language.steinerGraph where
  Holds := fun A inst => @HasSmallEdgeSteinerTree A inst
  iso_invariant := fun e => hasSmallEdgeSteinerTree_iso e

/-- STEINER TREE (node-weighted, unit weights), as a problem on graphs with
terminals: is there a connected set of vertices containing every terminal and
using at most as many non-terminals as the marked set has elements? -/
def SteinerTree : DecisionProblem Language.steinerGraph where
  Holds := fun A inst => @HasSmallSteinerTree A inst
  iso_invariant := fun e => hasSmallSteinerTree_iso e

end DescriptiveComplexity
