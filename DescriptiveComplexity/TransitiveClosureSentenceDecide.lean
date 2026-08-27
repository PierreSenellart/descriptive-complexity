/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureFlatten

/-!
# A walk over an expansion, with endpoints, as one decider

The last assembly step of the normal form: an FO(TC) *sentence* over an
expansion – a walk whose step, source and target formulas read the relations
of a block that has deciders – is decided by one
`DescriptiveComplexity.Decider` over the base vocabulary
(`DescriptiveComplexity.ParamTCSpec.sentenceDecider`), hence is one
`DescriptiveComplexity.TCSpec` (`DescriptiveComplexity.Decider.toSpec`).

The sentence says “some source node reaches some target node”. Its modes
are finite, so it is a finite disjunction over the pairs of modes
(`DescriptiveComplexity.Decider.listOr`); at a pair, the two tuples are
existentially quantified (`DescriptiveComplexity.Decider.exTup`), the source
and target formulas are decided by
`DescriptiveComplexity.Decider.exists_of_formula`, and reachability is that of
the flat walk (`DescriptiveComplexity.ParamTCSpec.flat`) between the
encodings of the two nodes, decided by
`DescriptiveComplexity.ParamTCSpec.reachDecider` – or, deterministically, by
`DescriptiveComplexity.ParamTCSpec.detReachDecider` on the searching flat
walk, which is functional. The encodings are two more quantified tuples,
pinned by a formula (`DescriptiveComplexity.ParamTCSpec.encF`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Finite disjunctions of deciders -/

namespace Decider

variable {L : Language.{0, 0}} {β : Type}

/-- The disjunction of a list of deciders, by De Morgan. -/
@[reducible]
noncomputable def listOr : List (Decider L β) → Decider L β
  | [] => atom ⊥
  | D :: l => (seq D.neg (listOr l).neg).neg

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
theorem decides_listOr (l : List (Decider L β)) (v : β → A) {P : Decider L β → Prop}
    (h : ∀ D ∈ l, D.Decides v (P D)) : (listOr l).Decides v (∃ D ∈ l, P D) := by
  induction l with
  | nil =>
    refine (decides_atom ⊥ v).congr ?_
    simp
  | cons D l ih =>
    refine (decides_neg _ v (decides_seq _ _ v (decides_neg D v (h D (List.mem_cons_self ..)))
      (decides_neg _ v (ih fun D' hD' => h D' (List.mem_cons_of_mem D hD'))))).congr ?_
    simp only [not_and, not_not, List.mem_cons, exists_eq_or_imp]
    exact ⟨fun h' => (Classical.em (P D)).elim Or.inl fun hn => Or.inr (h' hn),
      fun h' hn => h'.resolve_left hn⟩

omit [Finite A] [Nonempty A] in
/-- The disjunction of a family of deciders indexed by a list. -/
theorem decides_listOr_map {ι : Type} (l : List ι) (f : ι → Decider L β) (v : β → A)
    {P : ι → Prop} (h : ∀ i ∈ l, (f i).Decides v (P i)) :
    (listOr (l.map f)).Decides v (∃ i ∈ l, P i) := by
  induction l with
  | nil =>
    refine (decides_atom ⊥ v).congr ?_
    simp
  | cons i l ih =>
    refine (decides_neg _ v (decides_seq _ _ v (decides_neg _ v (h i (List.mem_cons_self ..)))
      (decides_neg _ v (ih fun i' hi' => h i' (List.mem_cons_of_mem i hi'))))).congr ?_
    simp only [not_and, not_not, List.mem_cons, exists_eq_or_imp]
    exact ⟨fun h' => (Classical.em (P i)).elim Or.inl fun hn => Or.inr (h' hn),
      fun h' hn => h'.resolve_left hn⟩

omit [Finite A] [Nonempty A] in
theorem functional_listOr (l : List (Decider L β)) (h : ∀ D ∈ l, D.Functional A) :
    (listOr l).Functional A := by
  induction l with
  | nil => exact functional_atom _
  | cons D l ih =>
    exact functional_neg _ (functional_seq _ _ (functional_neg D (h D (List.mem_cons_self ..)))
      (functional_neg _ (ih fun D' hD' => h D' (List.mem_cons_of_mem D hD'))))

/-- A formula with free variables, decided; the sentence-level instance of
`DescriptiveComplexity.Decider.exists_of_formula`. -/
theorem exists_of_formula₀ [L.IsRelational] {B : SOBlock}
    (ρ : (A : Type) → [L.Structure A] → [LinearOrder A] → B.Assignment A)
    (Dq : ∀ q : B.ι, Decider L (Fin (B.arity q)))
    (hD : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (q : B.ι)
      (w : Fin (B.arity q) → A), (Dq q).Decides w (ρ A q w))
    {α : Type} (φ : ((L.sum Language.order).sum B.lang).Formula α) :
    ∃ D : Decider L α,
      (∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] (v : α → A),
        D.Decides v (@Formula.Realize _ A (B.structure₁ (L := L.sum Language.order) (ρ A)) _ φ v)) ∧
      (∀ (A : Type) [L.Structure A] [LinearOrder A],
        (∀ q, (Dq q).Functional A) → D.Functional A) := by
  obtain ⟨D, hdec, hf⟩ := exists_of_formula ρ Dq hD φ
  refine ⟨D.relabelPar (Sum.elim id finZeroElim), fun A _ _ _ _ v => ?_,
    fun A _ _ h => functional_relabelPar _ _ (hf A h)⟩
  refine decides_relabelPar _ _ _ ((hdec A v finZeroElim).congr_val (funext fun i => ?_))
  rcases i with i | i
  · rfl
  · exact i.elim0

end Decider

/-! ### The sentence decider -/

namespace ParamTCSpec

variable {L : Language.{0, 0}} [L.IsRelational] {B : SOBlock}
variable (S : ParamTCSpec ((L.sum Language.order).sum B.lang))
variable (D : S.Mode → S.Mode → Decider L ((Fin S.k ⊕ Fin S.k) ⊕ Fin S.par))

/-- The pairs of modes, listed. -/
noncomputable def allPairs : List (S.Mode × S.Mode) :=
  letI : Fintype (S.Mode × S.Mode) := Fintype.ofFinite _
  (Finset.univ : Finset (S.Mode × S.Mode)).toList

omit [L.IsRelational] in
theorem mem_allPairs (p : S.Mode × S.Mode) : p ∈ S.allPairs := by
  let : Fintype (S.Mode × S.Mode) := Fintype.ofFinite _
  exact Finset.mem_toList.mpr (Finset.mem_univ p)

/-- The parameters of the innermost decider: the outer parameters, the source
tuple, the target tuple, and the two encodings. -/
abbrev Par4 (det : Bool) : Type :=
  (((Fin S.par ⊕ Fin S.k) ⊕ Fin S.k) ⊕ Fin (Nat.card (S.flat D det).Coord)) ⊕
    Fin (Nat.card (S.flat D det).Coord)

variable {det : Bool}

/-- **“The tuple `w` encodes the node with tuple `x`”**: on the current
coordinates it is `x`, everywhere else the minimum. -/
noncomputable def encF {γ : Type} (x : Fin S.k → γ) (w : Fin (Nat.card (S.flat D det).Coord) → γ) :
    (L.sum Language.order).Formula γ :=
  Formula.iInf fun c : S.FlatCoord D =>
    match c with
    | Sum.inl (Sum.inl i) =>
        Term.equal (Term.var (w ((S.flat D det).coordEquiv c))) (Term.var (x i))
    | c => minF (w ((S.flat D det).coordEquiv c))

/-- The variables of the source formula's decider. -/
def srcVar : Fin S.k → S.Par4 D det := fun i => Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))

/-- The variables of the target formula's decider. -/
def tgtVar : Fin S.k → S.Par4 D det := fun i => Sum.inl (Sum.inl (Sum.inr i))

/-- The variables of the first encoding. -/
def enc₁Var : Fin (Nat.card (S.flat D det).Coord) → S.Par4 D det := fun j => Sum.inl (Sum.inr j)

/-- The variables of the second encoding. -/
def enc₂Var : Fin (Nat.card (S.flat D det).Coord) → S.Par4 D det := fun j => Sum.inr j

/-- The variables of the outer parameters. -/
def parVar : Fin S.par → S.Par4 D det := fun i => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))

/-- The variables of the reachability decider of the flat walk. -/
noncomputable def reachVar : Fin (Nat.card (S.flat D det).Coord + Nat.card (S.flat D det).Coord +
    S.par) → S.Par4 D det :=
  ParamTCSpec.pack (s := (S.flat D det).toParam) (S.enc₁Var D) (S.enc₂Var D) (S.parVar D)

variable (det) (Ssrc Stgt : S.Mode → ((L.sum Language.order).sum B.lang).Formula (Fin S.k))
variable (Dsrc Dtgt : S.Mode → Decider L (Fin S.k))
  (Dr : S.Mode → S.Mode → Decider L (Fin (Nat.card (S.flat D det).Coord +
    Nat.card (S.flat D det).Coord + S.par)))

/-- The decider of one pair of modes: some source tuple, some target tuple,
their two encodings, and reachability between the encodings. -/
@[reducible]
noncomputable def pairDecider (p : S.Mode × S.Mode) : Decider L (Fin S.par) :=
  Decider.exTup S.k (Decider.exTup S.k (Decider.exTup _ (Decider.exTup _
    (Decider.seq ((Dsrc p.1).relabelPar (S.srcVar D))
      (Decider.seq ((Dtgt p.2).relabelPar (S.tgtVar D))
        (Decider.seq (Decider.atom (S.encF D (S.srcVar D) (S.enc₁Var D)))
          (Decider.seq (Decider.atom (S.encF D (S.tgtVar D) (S.enc₂Var D)))
            ((Dr p.1 p.2).relabelPar (S.reachVar D)))))))))

/-- **The sentence decider**: the disjunction over the pairs of modes. -/
@[reducible]
noncomputable def sentenceDecider : Decider L (Fin S.par) :=
  Decider.listOr (S.allPairs.map (S.pairDecider D det Dsrc Dtgt Dr))

/-! ### Semantics -/

section Semantics

variable {A : Type} [L.Structure A] [LinearOrder A]

omit [L.IsRelational] in
theorem realize_encF {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) {γ : Type} (x : Fin S.k → γ)
    (w : Fin (Nat.card (S.flat D det).Coord) → γ) (v : γ → A) :
    (S.encF D x w).Realize v ↔
      (v ∘ w) ∘ (S.flat D det).coordEquiv =
        Sum.elim (Sum.elim (v ∘ x) fun _ => a₀) fun _ => a₀ := by
  rw [encF, Formula.realize_iInf]
  constructor
  · intro h
    funext c
    have := h c
    rcases c with (i | i) | c
    · simpa using this
    · simp only [realize_minF] at this
      exact bot_unique this hbot
    · simp only [realize_minF] at this
      exact bot_unique this hbot
  · intro h c
    have := congrFun h c
    rcases c with (i | i) | c
    · simpa using this
    · simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr] at this
      simp only [realize_minF, this]
      exact hbot
    · simp only [Function.comp_apply, Sum.elim_inr] at this
      simp only [realize_minF, this]
      exact hbot

variable [Finite A] [Nonempty A]

/-- The valuation of the innermost parameters. -/
abbrev val4 (z : Fin S.par → A) (x y : Fin S.k → A)
    (w₁ w₂ : Fin (Nat.card (S.flat D det).Coord) → A) : S.Par4 D det → A :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim z x) y) w₁) w₂

variable (A) in
/-- What the reachability deciders of the flat walk decide, in the two
readings. -/
def DecidesReach : Prop :=
  ∀ (m n : S.Mode) (w : Fin (Nat.card (S.flat D det).Coord + Nat.card (S.flat D det).Coord +
      S.par) → A),
    (Dr m n).Decides w
      ((S.flat D det).toParam.ReachAt (w ∘ (S.flat D det).toParam.parIx)
        (Sum.inl m, w ∘ (S.flat D det).toParam.leftIx)
        (Sum.inl n, w ∘ (S.flat D det).toParam.rightIx))

variable [instE : ((L.sum Language.order).sum B.lang).Structure A]

omit [L.IsRelational] in
/-- **The pair decider decides**: some source tuple and some target tuple,
the outer walk reaching the target from the source – given that the flat walk
simulates the outer one at the encodings. -/
theorem decides_pairDecider {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (z : Fin S.par → A)
    (p : S.Mode × S.Mode)
    (hsrc : ∀ (m : S.Mode) (x : Fin S.k → A),
      (Dsrc m).Decides x (@Formula.Realize _ A instE _ (Ssrc m) x))
    (htgt : ∀ (m : S.Mode) (x : Fin S.k → A),
      (Dtgt m).Decides x (@Formula.Realize _ A instE _ (Stgt m) x))
    (hr : S.DecidesReach D det Dr A)
    (hsim : ∀ a b : S.Node A,
      (S.flat D det).ReachAt z (S.flatEnc D det a₀ a) (S.flatEnc D det a₀ b) ↔ S.ReachAt z a b) :
    (S.pairDecider D det Dsrc Dtgt Dr p).Decides z
      (∃ x y : Fin S.k → A, @Formula.Realize _ A instE _ (Ssrc p.1) x ∧
        @Formula.Realize _ A instE _ (Stgt p.2) y ∧ S.ReachAt z (p.1, x) (p.2, y)) := by
  have hinner : ∀ (x y : Fin S.k → A) (w₁ w₂ : Fin (Nat.card (S.flat D det).Coord) → A),
      (Decider.seq ((Dsrc p.1).relabelPar (S.srcVar D))
        (Decider.seq ((Dtgt p.2).relabelPar (S.tgtVar D))
          (Decider.seq (Decider.atom (S.encF D (S.srcVar D) (S.enc₁Var D)))
            (Decider.seq (Decider.atom (S.encF D (S.tgtVar D) (S.enc₂Var D)))
              ((Dr p.1 p.2).relabelPar (S.reachVar D)))))).Decides (S.val4 D det z x y w₁ w₂)
        (@Formula.Realize _ A instE _ (Ssrc p.1) x ∧
          (@Formula.Realize _ A instE _ (Stgt p.2) y ∧
            ((S.encF D (S.srcVar D) (S.enc₁Var D)).Realize (S.val4 D det z x y w₁ w₂) ∧
              ((S.encF D (S.tgtVar D) (S.enc₂Var D)).Realize (S.val4 D det z x y w₁ w₂) ∧
                (S.flat D det).toParam.ReachAt
                  ((S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘ (S.flat D det).toParam.parIx)
                  (Sum.inl p.1,
                    (S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘ (S.flat D det).toParam.leftIx)
                  (Sum.inl p.2,
                    (S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘
                      (S.flat D det).toParam.rightIx))))) :=
    fun x y w₁ w₂ =>
      Decider.decides_seq _ _ _ (Decider.decides_relabelPar _ _ _ (hsrc p.1 x))
        (Decider.decides_seq _ _ _ (Decider.decides_relabelPar _ _ _ (htgt p.2 y))
          (Decider.decides_seq _ _ _ (Decider.decides_atom _ _)
            (Decider.decides_seq _ _ _ (Decider.decides_atom _ _)
              (Decider.decides_relabelPar _ _ _ (hr p.1 p.2 _)))))
  have hpack : ∀ (x y : Fin S.k → A) (w₁ w₂ : Fin (Nat.card (S.flat D det).Coord) → A),
      ((S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘ (S.flat D det).toParam.parIx) = z ∧
      ((S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘ (S.flat D det).toParam.leftIx) = w₁ ∧
      ((S.val4 D det z x y w₁ w₂ ∘ S.reachVar D) ∘ (S.flat D det).toParam.rightIx) = w₂ := by
    intro x y w₁ w₂
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
    · simp [reachVar, ParamTCSpec.pack_par, parVar]
    · simp [reachVar, ParamTCSpec.pack_left, enc₁Var]
    · simp [reachVar, ParamTCSpec.pack_right, enc₂Var]
  have hcomp : ∀ f : S.FlatCoord D → A,
      (f ∘ (S.flat D det).coordEquiv.symm) ∘ (S.flat D det).coordEquiv = f := by
    intro f
    funext c
    simp
  refine (Decider.decides_exTup _ _ _ fun x => Decider.decides_exTup _ _ _ fun y =>
    Decider.decides_exTup _ _ _ fun w₁ => Decider.decides_exTup _ _ _ fun w₂ =>
      hinner x y w₁ w₂).congr ?_
  constructor
  · rintro ⟨x, y, w₁, w₂, hx, hy, he₁, he₂, hreach⟩
    refine ⟨x, y, hx, hy, ?_⟩
    obtain ⟨hz, hw₁, hw₂⟩ := hpack x y w₁ w₂
    rw [hz, hw₁, hw₂, CoordWalk.reachAt_toParam] at hreach
    rw [S.realize_encF D det hbot] at he₁ he₂
    change (S.val4 D det z x y w₁ w₂ ∘ S.enc₁Var D) ∘ _ = _ at he₁
    change (S.val4 D det z x y w₁ w₂ ∘ S.enc₂Var D) ∘ _ = _ at he₂
    change (S.flat D det).ReachAt z (Sum.inl p.1, w₁ ∘ (S.flat D det).coordEquiv)
      (Sum.inl p.2, w₂ ∘ (S.flat D det).coordEquiv) at hreach
    have he₁' : w₁ ∘ (S.flat D det).coordEquiv = (S.flatEnc D det a₀ (p.1, x)).2 := he₁
    have he₂' : w₂ ∘ (S.flat D det).coordEquiv = (S.flatEnc D det a₀ (p.2, y)).2 := he₂
    rw [he₁', he₂'] at hreach
    exact (hsim (p.1, x) (p.2, y)).mp hreach
  · rintro ⟨x, y, hx, hy, hreach⟩
    refine ⟨x, y, (S.flatEnc D det a₀ (p.1, x)).2 ∘ (S.flat D det).coordEquiv.symm,
      (S.flatEnc D det a₀ (p.2, y)).2 ∘ (S.flat D det).coordEquiv.symm, hx, hy, ?_, ?_, ?_⟩
    · rw [S.realize_encF D det hbot]
      exact hcomp _
    · rw [S.realize_encF D det hbot]
      exact hcomp _
    · obtain ⟨hz, hw₁, hw₂⟩ := hpack x y _ _
      rw [hz, hw₁, hw₂, CoordWalk.reachAt_toParam]
      change (S.flat D det).ReachAt z (Sum.inl p.1, _) (Sum.inl p.2, _)
      rw [hcomp, hcomp]
      exact (hsim (p.1, x) (p.2, y)).mpr hreach

omit [L.IsRelational] in
/-- **The sentence decider decides the sentence**: some source node reaches
some target node in the outer walk. -/
theorem decides_sentenceDecider {a₀ : A} (hbot : ∀ a : A, a₀ ≤ a) (z : Fin S.par → A)
    (hsrc : ∀ (m : S.Mode) (x : Fin S.k → A),
      (Dsrc m).Decides x (@Formula.Realize _ A instE _ (Ssrc m) x))
    (htgt : ∀ (m : S.Mode) (x : Fin S.k → A),
      (Dtgt m).Decides x (@Formula.Realize _ A instE _ (Stgt m) x))
    (hr : S.DecidesReach D det Dr A)
    (hsim : ∀ a b : S.Node A,
      (S.flat D det).ReachAt z (S.flatEnc D det a₀ a) (S.flatEnc D det a₀ b) ↔ S.ReachAt z a b) :
    (S.sentenceDecider D det Dsrc Dtgt Dr).Decides z
      (∃ a b : S.Node A, @Formula.Realize _ A instE _ (Ssrc a.1) a.2 ∧
        @Formula.Realize _ A instE _ (Stgt b.1) b.2 ∧ S.ReachAt z a b) := by
  refine (Decider.decides_listOr_map S.allPairs _ z (P := fun p =>
      ∃ x y : Fin S.k → A, @Formula.Realize _ A instE _ (Ssrc p.1) x ∧
        @Formula.Realize _ A instE _ (Stgt p.2) y ∧ S.ReachAt z (p.1, x) (p.2, y))
    fun p _ => S.decides_pairDecider D det Ssrc Stgt Dsrc Dtgt Dr hbot z p hsrc htgt hr hsim).congr
    ?_
  constructor
  · rintro ⟨p, -, x, y, hx, hy, h⟩
    exact ⟨(p.1, x), (p.2, y), hx, hy, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨(a.1, b.1), S.mem_allPairs _, a.2, b.2, ha, hb, h⟩

omit [L.IsRelational] [Finite A] [Nonempty A] instE in
/-- **The sentence decider is functional** when its components are. -/
theorem functional_sentenceDecider (hsrc : ∀ m, (Dsrc m).Functional A)
    (htgt : ∀ m, (Dtgt m).Functional A) (hr : ∀ m n, (Dr m n).Functional A) :
    (S.sentenceDecider D det Dsrc Dtgt Dr).Functional A := by
  refine Decider.functional_listOr _ fun D' hD' => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hD'
  exact Decider.functional_exTup _ _ (Decider.functional_exTup _ _ (Decider.functional_exTup _ _
    (Decider.functional_exTup _ _ (Decider.functional_seq _ _
      (Decider.functional_relabelPar _ _ (hsrc p.1)) (Decider.functional_seq _ _
        (Decider.functional_relabelPar _ _ (htgt p.2)) (Decider.functional_seq _ _
          (Decider.functional_atom _) (Decider.functional_seq _ _ (Decider.functional_atom _)
            (Decider.functional_relabelPar _ _ (hr p.1 p.2)))))))))

end Semantics

end ParamTCSpec

end DescriptiveComplexity
