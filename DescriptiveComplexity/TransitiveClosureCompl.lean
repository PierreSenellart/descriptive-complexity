/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosure
import DescriptiveComplexity.InductiveCounting.Complete

/-!
# FO(TC) is closed under complement

**Immerman–Szelepcsényi**, as a theorem about the logic: on finite ordered
structures, the complement of an FO(TC) definable problem is FO(TC) definable
([Immerman 1988][immerman1988nondeterministic], [Szelepcsényi
1988][szelepcsenyi1988method]).

The proof runs the inductive-counting machine of `DescriptiveComplexity.InductiveCounting`
inside a single transitive closure. The machine's nodes are the nodes of the
given `DescriptiveComplexity.TCSpec`, linearly ordered mode-major by the order of the
structure; its configurations are a finite control together with eight
registers, each holding a node or a count, and each stored as one `k`-tuple of
elements beside a mode kept in the control. So a configuration *is* a mode
together with a `8k`-tuple, which is exactly what a `TCSpec` of arity `8k` can
walk on.

The one thing the translation must supply is the *formulas*: each atomic
constraint of `DescriptiveComplexity.InductiveCounting.VAtom` becomes, given the modes recorded
by the two control states, either a first-order formula over the two tuples or
the information that no tuples can satisfy it (`compileAtom`). Since the modes
are finite control data, every mode-level condition – "these two registers hold
the same mode", "this mode is the least one", "this mode is covered by that
one" – is decided *outside* the formula, and what remains for the formula is a
condition on tuples of elements: equality, the lexicographic minimum, maximum
or successor (`DescriptiveComplexity.OrderWalk`), or one of the given spec's own
formulas.
-/

namespace DescriptiveComplexity

open FirstOrder Language InductiveCounting

variable {L : Language.{0, 0}}

/-! ### Padding a specification with a spare mode -/

namespace TCSpec

/-- The specification with one spare, isolated mode added, so that the mode
type is nonempty: the new mode has no transitions and is neither a source nor
a target. -/
noncomputable def pad (spec : TCSpec L) : TCSpec L where
  Mode := Option spec.Mode
  k := spec.k
  step p q := match p, q with
    | some m, some m' => spec.step m m'
    | _, _ => ⊥
  src p := match p with
    | some m => spec.src m
    | none => ⊥
  tgt p := match p with
    | some m => spec.tgt m
    | none => ⊥

instance instNonemptyPadMode (spec : TCSpec L) : Nonempty (spec.pad).Mode :=
  ⟨(none : Option spec.Mode)⟩

variable (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

/-- The nodes of the padded specification that carry a genuine mode. -/
private def padNode (a : spec.Node A) : (spec.pad).Node A := (some a.1, a.2)

private theorem pad_step_iff {a b : spec.Node A} :
    (spec.pad).Step (spec.padNode a) (spec.padNode b) ↔ spec.Step a b := Iff.rfl

private theorem pad_step_genuine {a b : (spec.pad).Node A} (h : (spec.pad).Step a b) :
    ∃ a' b' : spec.Node A, a = spec.padNode a' ∧ b = spec.padNode b' := by
  obtain ⟨p, x⟩ := a
  obtain ⟨q, y⟩ := b
  cases p with
  | none => exact absurd h (by exact fun h => h)
  | some m =>
    cases q with
    | none => exact absurd h (by exact fun h => h)
    | some m' => exact ⟨(m, x), (m', y), rfl, rfl⟩

private theorem pad_reach_of_reach {a b : spec.Node A} (h : spec.Reach a b) :
    (spec.pad).Reach (spec.padNode a) (spec.padNode b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((spec.pad_step_iff).mpr hcd)

private theorem reach_of_pad_reach {a : spec.Node A} :
    ∀ {b : (spec.pad).Node A}, (spec.pad).Reach (spec.padNode a) b →
      ∃ b' : spec.Node A, b = spec.padNode b' ∧ spec.Reach a b' := by
  intro b h
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨c', rfl, hc'⟩ := ih
    obtain ⟨c'', d', hceq, rfl⟩ := spec.pad_step_genuine hcd
    have hcc : c'' = c' := by
      obtain ⟨m1, t1⟩ := c'
      obtain ⟨m2, t2⟩ := c''
      have h1 : some m1 = some m2 := congrArg Prod.fst hceq
      have h2 : t1 = t2 := congrArg Prod.snd hceq
      rw [Option.some.inj h1, h2]
    subst hcc
    exact ⟨d', rfl, hc'.tail ((spec.pad_step_iff).mp hcd)⟩

variable (A) in
/-- Padding does not change acceptance. -/
theorem pad_accepts_iff : (spec.pad).Accepts A ↔ spec.Accepts A := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨p, x⟩ := u
    cases p with
    | none => exact absurd hu (by exact fun h => h)
    | some m =>
      obtain ⟨v', rfl, hreach⟩ := spec.reach_of_pad_reach (a := (m, x)) huv
      exact ⟨(m, x), v', hu, hv, hreach⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨spec.padNode u, spec.padNode v, hu, hv, spec.pad_reach_of_reach huv⟩

end TCSpec

/-! ### The nodes of a specification as a finite linear order -/

namespace TCCompl

variable (spec : TCSpec L) (A : Type) [L.Structure A] [LinearOrder A] [LinearOrder spec.Mode]

/-- The nodes of the walk, ordered mode-major and then lexicographically on
tuples. -/
abbrev NodeOrd : Type := spec.Mode ×ₗ Lex (Fin spec.k → A)

variable {spec A}

/-- The node underlying an ordered node. -/
def toNode (z : NodeOrd spec A) : spec.Node A := ((ofLex z).1, ofLex (ofLex z).2)

/-- The ordered node of a node. -/
def ofNode (n : spec.Node A) : NodeOrd spec A := toLex (n.1, toLex n.2)

omit [L.Structure A] [LinearOrder A] [LinearOrder spec.Mode] in
@[simp] theorem toNode_ofNode (n : spec.Node A) : toNode (ofNode n) = n := rfl

omit [L.Structure A] [LinearOrder A] [LinearOrder spec.Mode] in
@[simp] theorem ofNode_toNode (z : NodeOrd spec A) : ofNode (toNode z) = z := rfl

/-- The edges of the walk, on ordered nodes. -/
def edge (z z' : NodeOrd spec A) : Prop := spec.Step (toNode z) (toNode z')

/-- The starting nodes of the walk, on ordered nodes. -/
def src (z : NodeOrd spec A) : Prop := spec.IsSrc (toNode z)

/-- The accepting nodes of the walk, on ordered nodes. -/
def tgt (z : NodeOrd spec A) : Prop := spec.IsTgt (toNode z)

omit [LinearOrder spec.Mode] in
theorem reach_of_edge {z z' : NodeOrd spec A} (h : Relation.ReflTransGen edge z z') :
    spec.Reach (toNode z) (toNode z') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail hbc

omit [LinearOrder spec.Mode] in
theorem edge_of_reach {u v : spec.Node A} (h : spec.Reach u v) :
    Relation.ReflTransGen (edge (spec := spec)) (ofNode u) (ofNode v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail hbc

omit [LinearOrder spec.Mode] in
variable (spec A) in
/-- Acceptance of the specification, read on the ordered nodes. -/
theorem exists_reach_iff :
    (∃ a b : NodeOrd spec A, src a ∧ tgt b ∧ Relation.ReflTransGen edge a b) ↔
      spec.Accepts A := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨toNode a, toNode b, ha, hb, reach_of_edge hab⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨ofNode u, ofNode v, hu, hv, edge_of_reach huv⟩

/-! ### Registers inside one tuple -/

section Compile

variable (spec : TCSpec L) [LinearOrder spec.Mode]

/-- The arity of the complement specification: eight registers of `k` elements
each. -/
abbrev dim : ℕ := 8 * spec.k

/-- The variables of a transition formula: two tuples of that arity. -/
abbrev Var : Type := Fin (dim spec) ⊕ Fin (dim spec)

/-- The variable holding coordinate `i` of register `r`. -/
def regIdx (r : Reg) (i : Fin spec.k) : Fin (dim spec) := finProdFinEquiv (r, i)

/-- The variables holding the tuple a slot reads. -/
def slotSel : Slot → Fin spec.k → Var spec
  | (false, r) => fun i => Sum.inl (regIdx spec r i)
  | (true, r) => fun i => Sum.inr (regIdx spec r i)

variable {spec}
variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The tuple a register holds inside a tuple of the walk. -/
def regTup (x : Fin (dim spec) → A) (r : Reg) : Fin spec.k → A :=
  fun i => x (regIdx spec r i)

variable (spec) in
/-- Assembling the eight registers into one tuple. -/
def mkTup (f : Reg → Fin spec.k → A) : Fin (dim spec) → A :=
  fun q => f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
@[simp] theorem regTup_mkTup (f : Reg → Fin spec.k → A) (r : Reg) :
    regTup (mkTup spec f) r = f r := by
  funext i
  simp [regTup, mkTup, regIdx]

/-- The tuple a slot reads, from the two tuples of a transition. -/
def slotTup (x y : Fin (dim spec) → A) : Slot → Fin spec.k → A
  | (false, r) => regTup x r
  | (true, r) => regTup y r

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem realize_slotSel (x y : Fin (dim spec) → A) (a : Slot) (i : Fin spec.k) :
    Sum.elim x y (slotSel spec a i) = slotTup x y a i := by
  obtain ⟨s, r⟩ := a
  cases s <;> rfl

/-! ### The formulas of the atomic constraints -/

variable (spec)

/-- Two slots hold the same tuple. -/
noncomputable def eqTupF (a b : Slot) : (L.sum Language.order).Formula (Var spec) :=
  listInf ((List.finRange spec.k).map fun i =>
    Term.equal (Term.var (slotSel spec a i)) (Term.var (slotSel spec b i)))

/-- The two slots hold tuples joined by a transition of the given modes. -/
noncomputable def stepF (m m' : spec.Mode) (a b : Slot) :
    (L.sum Language.order).Formula (Var spec) :=
  (spec.step m m').relabel (Sum.elim (slotSel spec a) (slotSel spec b))

/-- The slot holds a starting tuple of the given mode. -/
noncomputable def srcF (m : spec.Mode) (a : Slot) : (L.sum Language.order).Formula (Var spec) :=
  (spec.src m).relabel (slotSel spec a)

/-- The slot holds an accepting tuple of the given mode. -/
noncomputable def tgtF (m : spec.Mode) (a : Slot) : (L.sum Language.order).Formula (Var spec) :=
  (spec.tgt m).relabel (slotSel spec a)

variable {spec}

omit [LinearOrder spec.Mode] in
theorem realize_eqTupF (x y : Fin (dim spec) → A) (a b : Slot) :
    (eqTupF spec a b).Realize (Sum.elim x y) ↔ slotTup x y a = slotTup x y b := by
  rw [eqTupF, realize_listInf]
  constructor
  · intro h
    funext i
    have hi := h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var, realize_slotSel,
      realize_slotSel] at hi
    exact hi
  · rintro h φ hφ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ
    rw [Formula.realize_equal, Term.realize_var, Term.realize_var, realize_slotSel,
      realize_slotSel, h]

omit [LinearOrder spec.Mode] in
theorem realize_stepF (x y : Fin (dim spec) → A) (m m' : spec.Mode) (a b : Slot) :
    (stepF spec m m' a b).Realize (Sum.elim x y) ↔
      spec.Step ((m, slotTup x y a) : spec.Node A) (m', slotTup x y b) := by
  rw [stepF, Formula.realize_relabel]
  refine iff_of_eq (congrArg (spec.step m m').Realize (funext fun j => ?_))
  cases j with
  | inl i => exact realize_slotSel x y a i
  | inr i => exact realize_slotSel x y b i

omit [LinearOrder spec.Mode] in
theorem realize_srcF (x y : Fin (dim spec) → A) (m : spec.Mode) (a : Slot) :
    (srcF spec m a).Realize (Sum.elim x y) ↔ spec.IsSrc ((m, slotTup x y a) : spec.Node A) := by
  rw [srcF, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.src m).Realize (funext fun i => realize_slotSel x y a i))

omit [LinearOrder spec.Mode] in
theorem realize_tgtF (x y : Fin (dim spec) → A) (m : spec.Mode) (a : Slot) :
    (tgtF spec m a).Realize (Sum.elim x y) ↔ spec.IsTgt ((m, slotTup x y a) : spec.Node A) := by
  rw [tgtF, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.tgt m).Realize (funext fun i => realize_slotSel x y a i))

omit [LinearOrder spec.Mode] in
theorem realize_minTup (x y : Fin (dim spec) → A) (a : Slot) :
    (minTupF (L := L) (slotSel spec a)).Realize (Sum.elim x y) ↔
      ∀ (p : Fin spec.k) (z : A), slotTup x y a p ≤ z := by
  rw [realize_minTupF]
  exact forall_congr' fun p => by rw [realize_slotSel]

omit [LinearOrder spec.Mode] in
theorem realize_maxTup (x y : Fin (dim spec) → A) (a : Slot) :
    (maxTupF (L := L) (slotSel spec a)).Realize (Sum.elim x y) ↔
      ∀ (p : Fin spec.k) (z : A), z ≤ slotTup x y a p := by
  rw [realize_maxTupF]
  exact forall_congr' fun p => by rw [realize_slotSel]

omit [LinearOrder spec.Mode] in
theorem realize_succTup (x y : Fin (dim spec) → A) (a b : Slot) :
    (succTupF (L := L) (slotSel spec a) (slotSel spec b)).Realize (Sum.elim x y) ↔
      TupSucc (slotTup x y a) (slotTup x y b) := by
  rw [realize_succTupF]
  have h1 : Sum.elim x y ∘ slotSel spec a = slotTup x y a := funext (realize_slotSel x y a)
  have h2 : Sum.elim x y ∘ slotSel spec b = slotTup x y b := funext (realize_slotSel x y b)
  rw [h1, h2]

end Compile

/-! ### Register values -/

section Values

variable {spec : TCSpec L} [LinearOrder spec.Mode] {A : Type} [L.Structure A] [LinearOrder A]

variable (spec) in
/-- The value of a register: `⊥` when the control records no mode, the node
made of the mode and the tuple otherwise. -/
def fuse (om : Option spec.Mode) (t : Fin spec.k → A) : WithBot (NodeOrd spec A) :=
  match om with
  | none => ⊥
  | some m => ↑(ofNode ((m, t) : spec.Node A))

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem fuse_none (t : Fin spec.k → A) : fuse spec none t = ⊥ := rfl

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem fuse_some (m : spec.Mode) (t : Fin spec.k → A) :
    fuse spec (some m) t = ↑(ofNode ((m, t) : spec.Node A)) := rfl

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem fuse_eq_iff {m m' : spec.Mode} {t t' : Fin spec.k → A} :
    fuse spec (some m) t = fuse spec (some m') t' ↔ m = m' ∧ t = t' := by
  rw [fuse_some, fuse_some, WithBot.coe_inj]
  constructor
  · intro h
    have h' : ((m, t) : spec.Node A) = (m', t') := congrArg toNode h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem fuse_ne_bot {m : spec.Mode} {t : Fin spec.k → A} : fuse spec (some m) t ≠ ⊥ := by
  rw [fuse_some]
  exact WithBot.coe_ne_bot

omit [L.Structure A] in
theorem covBy_fuse [Nonempty A] {m m' : spec.Mode} {t t' : Fin spec.k → A} :
    fuse spec (some m) t ⋖ fuse spec (some m') t' ↔
      (m = m' ∧ TupSucc t t') ∨
        (m ⋖ m' ∧ (∀ (p : Fin spec.k) (z : A), z ≤ t p) ∧
          ∀ (p : Fin spec.k) (z : A), t' p ≤ z) := by
  rw [fuse_some, fuse_some, WithBot.coe_covBy_coe]
  have h : (ofNode ((m, t) : spec.Node A) ⋖ ofNode ((m', t') : spec.Node A)) ↔
      (toLex (m, toLex t) ⋖ toLex (m', toLex t')) := Iff.rfl
  rw [h, prodLex_covBy_iff]
  exact or_congr (and_congr_right fun _ => tupSucc_iff_covBy.symm)
    (and_congr_right fun _ => and_congr tup_isTop_iff tup_isBot_iff)

omit [L.Structure A] in
theorem bot_covBy_fuse {m : spec.Mode} {t : Fin spec.k → A} :
    (⊥ : WithBot (NodeOrd spec A)) ⋖ fuse spec (some m) t ↔
      (∀ m' : spec.Mode, m ≤ m') ∧ ∀ (p : Fin spec.k) (z : A), t p ≤ z := by
  rw [fuse_some, WithBot.bot_covBy_coe]
  constructor
  · intro h
    have h' : ∀ u : NodeOrd spec A, ofNode ((m, t) : spec.Node A) ≤ u := fun u =>
      (le_total u (ofNode ((m, t) : spec.Node A))).elim (fun hu => h hu) id
    have := prodLex_isBot_iff.mp h'
    exact ⟨this.1, tup_isBot_iff.mp this.2⟩
  · rintro ⟨h1, h2⟩
    have h' : ∀ u : NodeOrd spec A, ofNode ((m, t) : spec.Node A) ≤ u :=
      prodLex_isBot_iff.mpr ⟨h1, tup_isBot_iff.mpr h2⟩
    exact fun u _ => h' u

omit [LinearOrder spec.Mode] in
theorem eW_fuse {m m' : spec.Mode} {t t' : Fin spec.k → A} :
    EW (edge (spec := spec)) (fuse spec (some m) t) (fuse spec (some m') t') ↔
      spec.Step ((m, t) : spec.Node A) (m', t') := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    rw [fuse_some, WithBot.coe_inj] at hp hq
    subst hp; subst hq
    exact hpq
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

omit [LinearOrder spec.Mode] in
theorem eW_fuse_none_left {om : Option spec.Mode} {t t' : Fin spec.k → A} :
    ¬EW (edge (spec := spec)) (fuse spec none t) (fuse spec om t') := by
  rintro ⟨p, q, hp, -, -⟩
  exact absurd hp.symm (WithBot.coe_ne_bot)

omit [LinearOrder spec.Mode] in
theorem eW_fuse_none_right {om : Option spec.Mode} {t t' : Fin spec.k → A} :
    ¬EW (edge (spec := spec)) (fuse spec om t) (fuse spec none t') := by
  rintro ⟨p, q, -, hq, -⟩
  exact absurd hq.symm (WithBot.coe_ne_bot)

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem pW_fuse {P : NodeOrd spec A → Prop} {m : spec.Mode} {t : Fin spec.k → A} :
    PW P (fuse spec (some m) t) ↔ P (ofNode ((m, t) : spec.Node A)) := by
  constructor
  · rintro ⟨p, hp, h⟩
    rw [fuse_some, WithBot.coe_inj] at hp
    exact hp ▸ h
  · intro h
    exact ⟨_, rfl, h⟩

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem pW_fuse_none {P : NodeOrd spec A → Prop} {t : Fin spec.k → A} :
    ¬PW P (fuse spec none t) := by
  rintro ⟨p, hp, -⟩
  exact absurd hp.symm (WithBot.coe_ne_bot)

omit [L.Structure A] in
theorem pW_fuse_isMin {m : spec.Mode} {t : Fin spec.k → A} :
    PW (fun p : NodeOrd spec A => ∀ z : NodeOrd spec A, p ≤ z) (fuse spec (some m) t) ↔
      (∀ m' : spec.Mode, m ≤ m') ∧ ∀ (p : Fin spec.k) (z : A), t p ≤ z := by
  rw [pW_fuse]
  constructor
  · intro h
    have := prodLex_isBot_iff.mp h
    exact ⟨this.1, tup_isBot_iff.mp this.2⟩
  · rintro ⟨h1, h2⟩
    exact prodLex_isBot_iff.mpr ⟨h1, tup_isBot_iff.mpr h2⟩

omit [L.Structure A] in
theorem pW_fuse_isMax {m : spec.Mode} {t : Fin spec.k → A} :
    PW (fun p : NodeOrd spec A => ∀ z : NodeOrd spec A, z ≤ p) (fuse spec (some m) t) ↔
      (∀ m' : spec.Mode, m' ≤ m) ∧ ∀ (p : Fin spec.k) (z : A), z ≤ t p := by
  rw [pW_fuse]
  constructor
  · intro h
    have := prodLex_isTop_iff.mp h
    exact ⟨this.1, tup_isTop_iff.mp this.2⟩
  · rintro ⟨h1, h2⟩
    exact prodLex_isTop_iff.mpr ⟨h1, tup_isTop_iff.mpr h2⟩

end Values

/-! ### Compiling an atomic constraint -/

section CompileAtom

variable (spec : TCSpec L) [LinearOrder spec.Mode]

/-- The mode a slot reads, from the modes the two control states record. -/
def slotMode (pm qm : Reg → Option spec.Mode) : Slot → Option spec.Mode
  | (false, r) => pm r
  | (true, r) => qm r

open Classical in
/-- The formula of an atomic constraint, given the modes recorded by the two
control states: `none` when those modes already make the constraint
unsatisfiable. Every mode-level condition is decided here, outside the
formula. -/
noncomputable def compileAtom (pm qm : Reg → Option spec.Mode) :
    VAtom → Option ((L.sum Language.order).Formula (Var spec))
  | .eqR a b =>
      match slotMode spec pm qm a, slotMode spec pm qm b with
      | none, none => some ⊤
      | some m, some m' => if m = m' then some (eqTupF spec a b) else none
      | _, _ => none
  | .neqR a b =>
      match slotMode spec pm qm a, slotMode spec pm qm b with
      | none, none => none
      | some m, some m' => if m = m' then some (∼(eqTupF spec a b)) else some ⊤
      | _, _ => some ⊤
  | .succR a b =>
      match slotMode spec pm qm a, slotMode spec pm qm b with
      | none, some m' =>
          if (∀ m'' : spec.Mode, m' ≤ m'') then some (minTupF (slotSel spec b)) else none
      | some m, some m' =>
          if m = m' then some (succTupF (slotSel spec a) (slotSel spec b))
          else if m ⋖ m' then some (maxTupF (slotSel spec a) ⊓ minTupF (slotSel spec b))
          else none
      | _, _ => none
  | .edge a b =>
      match slotMode spec pm qm a, slotMode spec pm qm b with
      | some m, some m' => some (stepF spec m m' a b)
      | _, _ => none
  | .nedge a b =>
      match slotMode spec pm qm a, slotMode spec pm qm b with
      | some m, some m' => some (∼(stepF spec m m' a b))
      | _, _ => some ⊤
  | .srcR a =>
      match slotMode spec pm qm a with
      | some m => some (srcF spec m a)
      | none => none
  | .nsrcR a =>
      match slotMode spec pm qm a with
      | some m => some (∼(srcF spec m a))
      | none => some ⊤
  | .tgtR a =>
      match slotMode spec pm qm a with
      | some m => some (tgtF spec m a)
      | none => none
  | .ntgtR a =>
      match slotMode spec pm qm a with
      | some m => some (∼(tgtF spec m a))
      | none => some ⊤
  | .botNode a =>
      match slotMode spec pm qm a with
      | some m => if (∀ m' : spec.Mode, m ≤ m') then some (minTupF (slotSel spec a)) else none
      | none => none
  | .topNode a =>
      match slotMode spec pm qm a with
      | some m => if (∀ m' : spec.Mode, m' ≤ m) then some (maxTupF (slotSel spec a)) else none
      | none => none
  | .isZero a =>
      match slotMode spec pm qm a with
      | none => some ⊤
      | some _ => none

variable {spec}
variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The registers a control state and a tuple describe. -/
def regsOf (pm : Reg → Option spec.Mode) (x : Fin (dim spec) → A) :
    Reg → WithBot (NodeOrd spec A) := fun r => fuse spec (pm r) (regTup x r)

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem slotVal_regsOf (pm qm : Reg → Option spec.Mode) (x y : Fin (dim spec) → A) (a : Slot) :
    slotVal (regsOf pm x) (regsOf qm y) a = fuse spec (slotMode spec pm qm a) (slotTup x y a) := by
  obtain ⟨s, r⟩ := a
  cases s <;> rfl

private theorem iff_none {P : Prop} {γ : Type} {v : γ → A} (h : ¬P) :
    P ↔ ∃ f : (L.sum Language.order).Formula γ,
      (none : Option ((L.sum Language.order).Formula γ)) = some f ∧ f.Realize v :=
  ⟨fun hp => absurd hp h, by rintro ⟨f, hf, -⟩; exact absurd hf.symm (Option.some_ne_none f)⟩

private theorem iff_some {P : Prop} {γ : Type} {v : γ → A} {g : (L.sum Language.order).Formula γ}
    (h : P ↔ g.Realize v) :
    P ↔ ∃ f, (some g : Option ((L.sum Language.order).Formula γ)) = some f ∧ f.Realize v := by
  rw [h]
  exact ⟨fun hg => ⟨g, rfl, hg⟩, fun ⟨f, hf, hr⟩ => (Option.some.inj hf) ▸ hr⟩

/-- **The atomic constraints are first-order**: given the modes, an atomic
constraint holds of the registers exactly when its compiled formula holds of
the tuples. -/
theorem holds_iff_compileAtom [Nonempty A] (pm qm : Reg → Option spec.Mode)
    (x y : Fin (dim spec) → A) (a : VAtom) :
    VAtom.Holds (edge (spec := spec)) src tgt (regsOf pm x) (regsOf qm y) a ↔
      ∃ f, compileAtom spec pm qm a = some f ∧ f.Realize (Sum.elim x y) := by
  classical
  cases a with
  | eqR a b =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a <;> cases hmb : slotMode spec pm qm b
    · refine iff_some ?_
      simp [fuse_none]
    · refine iff_none ?_
      simp [fuse_none, fuse_some]
    · refine iff_none ?_
      simp [fuse_none, fuse_some]
    · rename_i m m'
      dsimp only
      split_ifs with hmm
      · refine iff_some ?_
        rw [fuse_eq_iff, realize_eqTupF]; simp [hmm]
      · simp only [false_and, exists_false, iff_false]
        rw [fuse_eq_iff]; tauto
  | neqR a b =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a <;> cases hmb : slotMode spec pm qm b
    · refine iff_none ?_
      simp [fuse_none]
    · refine iff_some ?_
      simp [fuse_none, fuse_some]
    · refine iff_some ?_
      simp [fuse_none, fuse_some]
    · rename_i m m'
      dsimp only
      split_ifs with hmm
      · refine iff_some ?_
        rw [ne_eq, Formula.realize_not, fuse_eq_iff, realize_eqTupF]; simp [hmm]
      · refine iff_some ?_
        rw [ne_eq, Formula.realize_top, fuse_eq_iff]; tauto
  | succR a b =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a <;> cases hmb : slotMode spec pm qm b
    · refine iff_none ?_
      rw [fuse_none]; exact fun h => absurd h.lt (lt_irrefl _)
    · rename_i m'
      dsimp only
      split_ifs with h
      · refine iff_some ?_
        rw [fuse_none, bot_covBy_fuse, realize_minTup]; simp [h]
      · simp only [false_and, exists_false, iff_false]
        rw [fuse_none, bot_covBy_fuse]
        tauto
    · refine iff_none ?_
      exact fun h => absurd h.lt not_lt_bot
    · rename_i m m'
      dsimp only
      split_ifs with hmm hcov
      · refine iff_some ?_
        rw [covBy_fuse, realize_succTup]
        exact ⟨fun hh => hh.elim (fun h1 => h1.2) (fun h1 => absurd (hmm ▸ h1.1).lt (lt_irrefl _)),
          fun hh => Or.inl ⟨hmm, hh⟩⟩
      · refine iff_some ?_
        rw [covBy_fuse, Formula.realize_inf, realize_maxTup, realize_minTup]
        exact ⟨fun hh => hh.elim (fun h1 => absurd h1.1 hmm) (fun h1 => ⟨h1.2.1, h1.2.2⟩),
          fun hh => Or.inr ⟨hcov, hh.1, hh.2⟩⟩
      · simp only [false_and, exists_false, iff_false]
        rw [covBy_fuse]
        rintro (h1 | h1)
        · exact hmm h1.1
        · exact hcov h1.1
  | edge a b =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a <;> cases hmb : slotMode spec pm qm b
    · exact iff_none eW_fuse_none_left
    · exact iff_none eW_fuse_none_left
    · exact iff_none eW_fuse_none_right
    · refine iff_some ?_
      rw [eW_fuse, realize_stepF]
  | nedge a b =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a <;> cases hmb : slotMode spec pm qm b
    · refine iff_some ?_
      rw [Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => eW_fuse_none_left⟩
    · refine iff_some ?_
      rw [Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => eW_fuse_none_left⟩
    · refine iff_some ?_
      rw [Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => eW_fuse_none_right⟩
    · refine iff_some ?_
      rw [Formula.realize_not, eW_fuse, realize_stepF]
  | srcR a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · exact iff_none pW_fuse_none
    · refine iff_some ?_
      rw [pW_fuse, realize_srcF]; exact Iff.rfl
  | nsrcR a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · refine iff_some ?_
      rw [Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => pW_fuse_none⟩
    · refine iff_some ?_
      rw [Formula.realize_not, pW_fuse, realize_srcF]; exact Iff.rfl
  | tgtR a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · exact iff_none pW_fuse_none
    · refine iff_some ?_
      rw [pW_fuse, realize_tgtF]; exact Iff.rfl
  | ntgtR a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · refine iff_some ?_
      rw [Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => pW_fuse_none⟩
    · refine iff_some ?_
      rw [Formula.realize_not, pW_fuse, realize_tgtF]; exact Iff.rfl
  | botNode a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · exact iff_none pW_fuse_none
    · rename_i m
      dsimp only
      split_ifs with h
      · refine iff_some ?_
        rw [pW_fuse_isMin, realize_minTup]; simp [h]
      · simp only [false_and, exists_false, iff_false]
        rw [pW_fuse_isMin]; tauto
  | topNode a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · exact iff_none pW_fuse_none
    · rename_i m
      dsimp only
      split_ifs with h
      · refine iff_some ?_
        rw [pW_fuse_isMax, realize_maxTup]; simp [h]
      · simp only [false_and, exists_false, iff_false]
        rw [pW_fuse_isMax]; tauto
  | isZero a =>
    simp only [VAtom.Holds, slotVal_regsOf, compileAtom]
    cases hma : slotMode spec pm qm a
    · refine iff_some ?_
      rw [fuse_none, Formula.realize_top]
      exact ⟨fun _ => trivial, fun _ => rfl⟩
    · refine iff_none ?_
      rw [fuse_some]; exact WithBot.coe_ne_bot

end CompileAtom

/-! ### Compiling a table entry -/

section CompileList

variable (spec : TCSpec L) [LinearOrder spec.Mode]

open Classical in
/-- The formula of one alternative: the conjunction of its atomic
constraints. -/
noncomputable def compileConj (pm qm : Reg → Option spec.Mode) :
    List VAtom → Option ((L.sum Language.order).Formula (Var spec))
  | [] => some ⊤
  | a :: l =>
      match compileAtom spec pm qm a, compileConj pm qm l with
      | some f, some g => some (f ⊓ g)
      | _, _ => none

/-- The formula of a table entry: the disjunction of its satisfiable
alternatives. -/
noncomputable def compileDisj (pm qm : Reg → Option spec.Mode) (ls : List (List VAtom)) :
    (L.sum Language.order).Formula (Var spec) :=
  listSup (ls.filterMap (compileConj spec pm qm))

variable {spec}
variable {A : Type} [L.Structure A] [LinearOrder A] [Nonempty A]

theorem sat_iff_compileConj (pm qm : Reg → Option spec.Mode) (x y : Fin (dim spec) → A)
    (l : List VAtom) :
    Sat (edge (spec := spec)) src tgt (regsOf pm x) (regsOf qm y) l ↔
      ∃ f, compileConj spec pm qm l = some f ∧ f.Realize (Sum.elim x y) := by
  induction l with
  | nil =>
    simp only [compileConj, Option.some.injEq, exists_eq_left', Formula.realize_top]
    exact ⟨fun _ => trivial, fun _ => sat_nil _ _ _ _ _⟩
  | cons a l ih =>
    rw [sat_cons, ih, holds_iff_compileAtom]
    cases hA : compileAtom spec pm qm a <;> cases hB : compileConj spec pm qm l <;>
      simp [compileConj, hA, hB, Formula.realize_inf]

theorem exists_sat_iff_compileDisj (pm qm : Reg → Option spec.Mode)
    (x y : Fin (dim spec) → A) (ls : List (List VAtom)) :
    (∃ l ∈ ls, Sat (edge (spec := spec)) src tgt (regsOf pm x) (regsOf qm y) l) ↔
      (compileDisj spec pm qm ls).Realize (Sum.elim x y) := by
  rw [compileDisj, realize_listSup]
  constructor
  · rintro ⟨l, hl, hsat⟩
    obtain ⟨f, hf, hr⟩ := (sat_iff_compileConj pm qm x y l).mp hsat
    exact ⟨f, List.mem_filterMap.mpr ⟨l, hl, hf⟩, hr⟩
  · rintro ⟨f, hf, hr⟩
    obtain ⟨l, hl, hfl⟩ := List.mem_filterMap.mp hf
    exact ⟨l, hl, (sat_iff_compileConj pm qm x y l).mpr ⟨f, hfl, hr⟩⟩

end CompileList

/-! ### The complement specification -/

section Spec

variable (spec : TCSpec L) [LinearOrder spec.Mode]

/-- The control states of the counting machine: a phase, the flag, and the
mode of each of the eight registers. -/
abbrev Ctrl : Type := Phase × Bool × (Reg → Option spec.Mode)

open Classical in
/-- The formula defining the initial configurations: the source scan is about
to start with a zero count and the outer register at the least node. -/
noncomputable def srcFormula (p : Ctrl spec) : (L.sum Language.order).Formula (Fin (dim spec)) :=
  if p.1 = Phase.initCount ∧ p.2.1 = false ∧ p.2.2 Reg.c = none ∧
      ∃ m : spec.Mode, p.2.2 Reg.v = some m ∧ ∀ m' : spec.Mode, m ≤ m' then
    minTupF (fun i => regIdx spec Reg.v i)
  else ⊥

open Classical in
/-- **The complement specification**: the inductive-counting machine, as a
single transitive closure over `8k`-tuples. -/
noncomputable def complSpec : TCSpec L where
  Mode := Ctrl spec
  k := dim spec
  step p q := compileDisj spec p.2.2 q.2.2 (table (p.1, p.2.1) (q.1, q.2.1))
  src p := srcFormula spec p
  tgt p := if p.1 = Phase.accept then ⊤ else ⊥

variable {spec}
variable {A : Type} [L.Structure A] [LinearOrder A] [Nonempty A]

/-- The configuration a node of the complement specification describes. -/
def toCfg (n : (complSpec spec).Node A) : Cfg (NodeOrd spec A) :=
  ⟨n.1.1, n.1.2.1, regsOf n.1.2.2 n.2⟩

/-- The mode a register value records. -/
noncomputable def splitMode (w : WithBot (NodeOrd spec A)) : Option spec.Mode :=
  match w with
  | ⊥ => none
  | (z : NodeOrd spec A) => some (toNode z).1

/-- The tuple a register value records. -/
noncomputable def splitTup (w : WithBot (NodeOrd spec A)) : Fin spec.k → A :=
  match w with
  | ⊥ => fun _ => Classical.arbitrary A
  | (z : NodeOrd spec A) => (toNode z).2

omit [LinearOrder spec.Mode] [L.Structure A] [LinearOrder A] in
theorem fuse_split (w : WithBot (NodeOrd spec A)) :
    fuse spec (splitMode w) (splitTup w) = w := by
  cases w with
  | bot => rfl
  | coe z => rfl

/-- Every configuration comes from a node of the complement specification. -/
noncomputable def ofCfg (s : Cfg (NodeOrd spec A)) : (complSpec spec).Node A :=
  ((s.phase, s.flag, fun r => splitMode (s.regs r)),
    mkTup spec (fun r => splitTup (s.regs r)))

omit [L.Structure A] [LinearOrder A] in
theorem toCfg_ofCfg (s : Cfg (NodeOrd spec A)) : toCfg (ofCfg s) = s := by
  obtain ⟨ph, fl, regs⟩ := s
  refine congrArg (Cfg.mk ph fl) (funext fun r => ?_)
  change fuse spec (splitMode (regs r)) (regTup (mkTup spec fun r => splitTup (regs r)) r)
    = regs r
  rw [regTup_mkTup, fuse_split]

theorem step_iff (n n' : (complSpec spec).Node A) :
    (complSpec spec).Step n n' ↔ CfgStep (edge (spec := spec)) src tgt (toCfg n) (toCfg n') :=
  (exists_sat_iff_compileDisj n.1.2.2 n'.1.2.2 n.2 n'.2 _).symm

theorem cfgReach_of_reach {n n' : (complSpec spec).Node A} (h : (complSpec spec).Reach n n') :
    CfgReach (edge (spec := spec)) src tgt (toCfg n) (toCfg n') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ((step_iff b c).mp hbc)

theorem reach_of_cfgReach {n : (complSpec spec).Node A} {s : Cfg (NodeOrd spec A)}
    (h : CfgReach (edge (spec := spec)) src tgt (toCfg n) s) :
    ∃ n' : (complSpec spec).Node A, toCfg n' = s ∧ (complSpec spec).Reach n n' := by
  induction h with
  | refl => exact ⟨n, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n1, hn1, hreach⟩ := ih
    refine ⟨ofCfg c, toCfg_ofCfg c, hreach.tail ?_⟩
    rw [step_iff, hn1, toCfg_ofCfg]
    exact hbc

omit [Nonempty A] in
theorem realize_srcFormula (p : Ctrl spec) (x : Fin (dim spec) → A) :
    (srcFormula spec p).Realize x ↔ p.1 = Phase.initCount ∧ p.2.1 = false ∧
      p.2.2 Reg.c = none ∧ ∃ m : spec.Mode, p.2.2 Reg.v = some m ∧ (∀ m' : spec.Mode, m ≤ m') ∧
        ∀ (i : Fin spec.k) (z : A), x (regIdx spec Reg.v i) ≤ z := by
  classical
  rw [srcFormula]
  split_ifs with h
  · obtain ⟨hph, hfl, hc, m, hm, hmin⟩ := h
    rw [realize_minTupF]
    exact ⟨fun hx => ⟨hph, hfl, hc, m, hm, hmin, hx⟩, fun hx => hx.2.2.2.choose_spec.2.2⟩
  · rw [Formula.realize_bot]
    refine ⟨False.elim, fun hx => absurd ?_ h⟩
    obtain ⟨hph, hfl, hc, m, hm, hmin, -⟩ := hx
    exact ⟨hph, hfl, hc, m, hm, hmin⟩

omit [Nonempty A] in
theorem isSrc_iff (n : (complSpec spec).Node A) :
    (complSpec spec).IsSrc n ↔ CfgIsSrc (toCfg n) := by
  classical
  refine Iff.trans (realize_srcFormula n.1 n.2) ?_
  have hv : (toCfg n).regs Reg.v = fuse spec (n.1.2.2 Reg.v) (regTup n.2 Reg.v) := rfl
  have hc : (toCfg n).regs Reg.c = fuse spec (n.1.2.2 Reg.c) (regTup n.2 Reg.c) := rfl
  simp only [CfgIsSrc, hv, hc]
  constructor
  · rintro ⟨hph, hfl, hcnone, m, hm, hmin, hx⟩
    refine ⟨hph, hfl, by rw [hcnone, fuse_none], ?_⟩
    rw [hm, pW_fuse_isMin]
    exact ⟨hmin, fun i z => hx i z⟩
  · rintro ⟨hph, hfl, hcbot, hvmin⟩
    refine ⟨hph, hfl, ?_, ?_⟩
    · cases hm : n.1.2.2 Reg.c with
      | none => rfl
      | some m =>
        rw [hm] at hcbot
        exact absurd hcbot fuse_ne_bot
    · cases hm : n.1.2.2 Reg.v with
      | none =>
        rw [hm] at hvmin
        exact absurd hvmin pW_fuse_none
      | some m =>
        rw [hm, pW_fuse_isMin] at hvmin
        exact ⟨m, rfl, hvmin.1, fun i z => hvmin.2 i z⟩

omit [Nonempty A] in
theorem realize_tgtFormula (p : Ctrl spec) (x : Fin (dim spec) → A) :
    ((complSpec spec).tgt p).Realize x ↔ p.1 = Phase.accept := by
  classical
  change (if p.1 = Phase.accept then (⊤ : (L.sum Language.order).Formula (Fin (dim spec)))
    else ⊥).Realize x ↔ _
  split_ifs with h
  · simp only [Formula.realize_top]
    exact ⟨fun _ => h, fun _ => trivial⟩
  · simp only [Formula.realize_bot]
    exact ⟨False.elim, fun hh => absurd hh h⟩

omit [Nonempty A] in
theorem isTgt_iff (n : (complSpec spec).Node A) :
    (complSpec spec).IsTgt n ↔ CfgIsTgt (toCfg n) :=
  realize_tgtFormula n.1 n.2

theorem accepts_iff :
    (complSpec spec).Accepts A ↔
      MachineAccepts (edge (spec := spec) (A := A)) (src (spec := spec) (A := A))
        (tgt (spec := spec) (A := A)) := by
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨toCfg u, toCfg v, (isSrc_iff u).mp hu, (isTgt_iff v).mp hv, cfgReach_of_reach huv⟩
  · rintro ⟨s, s', hs, hs', hss'⟩
    obtain ⟨n', hn', hreach⟩ :=
      reach_of_cfgReach (n := ofCfg s) (s := s') (by rw [toCfg_ofCfg]; exact hss')
    exact ⟨ofCfg s, n', (isSrc_iff _).mpr (by rw [toCfg_ofCfg]; exact hs),
      (isTgt_iff _).mpr (by rw [hn']; exact hs'), hreach⟩

/-- **The complement specification is correct**: it accepts exactly the
structures the given specification rejects. -/
theorem complSpec_accepts_iff [Nonempty spec.Mode] [Finite A] :
    (complSpec spec).Accepts A ↔ ¬spec.Accepts A := by
  rw [accepts_iff, machineAccepts_iff, exists_reach_iff]

end Spec

end TCCompl

end DescriptiveComplexity
