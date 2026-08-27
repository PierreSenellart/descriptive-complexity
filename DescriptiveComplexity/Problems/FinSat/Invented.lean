/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.FinSat.Fixpoint

/-!
# The certificate: a finite model, invented

The mathematical content of `FINSAT ∈ RE`, ahead of any second-order syntax:
an encoded sentence has a finite model exactly when a *finite set of invented
values* carries one (`DescriptiveComplexity.FinSat.finSatOn_iff_cert`). The
`∃SO[new]` sentence of `DescriptiveComplexity.Problems.FinSat.Membership` is then this
statement written out, the invented values being the extension `A ⊕ Fin m` of
the universe and the five relations below the guessed relation variables.

## What has to be invented, and why

* **the elements of the model** (`Elt`) – unbounded in the instance, which is
  exactly what `∃SO[new]` adds to `Σ₁` and what takes the problem out of NP;
* **the environments** (`Env`, with `Val e x d` reading the value of the
  variable `x` in the environment `e`). An environment is a *function* from the
  variables of the sentence to the model, so it cannot be a tuple: its arity
  would be the number of variables of the input. Reifying it as an invented
  value, with its graph as a guessed ternary relation, is the only way a
  first-order kernel can quantify over environments. `val_update` – every
  environment can be updated at one variable to any value – is what makes the
  reified environments cover *all* assignments, and it is used exactly where
  the truth definition updates the environment, at a quantifier node;
* **the truth values of the nodes** (`G g e`), constrained by the truth
  definition read as an equivalence (`step`). Well-formedness makes that
  fixed point unique (`DescriptiveComplexity.FinSat.IsEval.iff_Gval`), so the
  guess is forced to be satisfaction – this is where the acyclicity of the
  parse DAG is spent;
* **the truth values of the atoms** (`H g e`), *not* the interpretation of the
  relation symbols. An atom's arguments form a tuple of unbounded arity too, so
  the interpretation cannot be guessed directly; it is instead **recovered**
  from `H` by the coherence condition `atom_coh` – two atoms of the same symbol
  whose arguments have the same values get the same truth value – which is
  first-order and needs no tuples at all. The atom shape conditions of
  `DescriptiveComplexity.FinSat.IsWF` are what make that recovery sound.

Note that `G` must be given separately from `H`: a node that is a *negated*
atom has the negation of the atom's truth value, so the two cannot be the same
relation – the equation `G g e ↔ ¬G g e` has no solutions.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace FinSat

variable {A : Type} [Language.finsat.Structure A] {D : Type}

/-! ### The certificate -/

/-- `e'` is the environment `e` with the variable `x` set to the value `d`. -/
def UpdAt (Val : D → A → D → Prop) (e e' : D) (x : A) (d : D) : Prop :=
  Val e' x d ∧ ∀ y : A, y ≠ x → ∀ c, (Val e' y c ↔ Val e y c)

/-- The truth definition of `DescriptiveComplexity.FinSat.gstep`, read on a
certificate: environments are invented values, an updated environment is any
invented value that updates the given one, and the two atom clauses read the
guessed truth value of the atom rather than an interpretation. -/
def CertStep (Elt Env : D → Prop) (Val : D → A → D → Prop) (G H : A → D → Prop)
    (g : A) (e : D) : Prop :=
  (AndG g ∧ ∀ c, ChildG g c → G c e) ∨
  (OrG g ∧ ∃ c, ChildG g c ∧ G c e) ∨
  (AllG g ∧ ∀ x, BindG g x → ∀ d, Elt d → ∀ e', Env e' → UpdAt Val e e' x d →
    ∀ c, ChildG g c → G c e') ∨
  (ExG g ∧ ∃ x, BindG g x ∧ ∃ d, Elt d ∧ ∃ e', Env e' ∧ UpdAt Val e e' x d ∧
    ∃ c, ChildG g c ∧ G c e') ∨
  (∃ x y, EqG g x y ∧ ∀ d, (Val e x d ↔ Val e y d)) ∨
  (∃ x y, NeqG g x y ∧ ∃ d, Val e x d ∧ ¬Val e y d) ∨
  (∃ s, PosG g s ∧ H g e) ∨
  (∃ s, NegG g s ∧ ¬H g e)

/-- **A certificate of finite satisfiability**, over a set `D` of invented
values: a nonempty model `Elt`, environments `Env` with their graph `Val`,
truth values `G` of the nodes and `H` of the atoms, subject to the conditions
of the module docstring. Every condition is first-order in the vocabulary of
the instance together with the five relations, which is what makes the
`∃SO[new]` sentence of `DescriptiveComplexity.Problems.FinSat.Membership` possible. -/
structure CertOK (Elt Env : D → Prop) (Val : D → A → D → Prop) (G H : A → D → Prop) :
    Prop where
  /-- The model is nonempty. -/
  elt_nonempty : ∃ d, Elt d
  /-- There is at least one environment. -/
  env_nonempty : ∃ e, Env e
  /-- An environment gives every variable a value in the model. -/
  val_total : ∀ e, Env e → ∀ x : A, ∃ d, Elt d ∧ Val e x d
  /-- An environment gives every variable at most one value. -/
  val_fun : ∀ e, Env e → ∀ (x : A) (d d' : D), Val e x d → Val e x d' → d = d'
  /-- Environments are closed under updating one variable: this is what makes
  the invented environments cover every assignment. -/
  val_update : ∀ e, Env e → ∀ (x : A) (d : D), Elt d → ∃ e', Env e' ∧ UpdAt Val e e' x d
  /-- The truth value of a node depends on the environment only through the
  values it gives: two environments with the same graph agree. -/
  g_ext : ∀ (g : A) (e e' : D), Env e → Env e' → (∀ x d, Val e x d ↔ Val e' x d) →
    (G g e ↔ G g e')
  /-- The truth values obey the truth definition. -/
  step : ∀ (g : A) (e : D), Env e → (G g e ↔ CertStep Elt Env Val G H g e)
  /-- **Atoms cohere**: two atoms of the same relation symbol whose arguments
  have the same values have the same truth value. This is what an
  interpretation of the symbol *is*, written without tuples. -/
  atom_coh : ∀ (g g' s : A) (e e' : D), Env e → Env e' →
    (PosG g s ∨ NegG g s) → (PosG g' s ∨ NegG g' s) →
    (∀ p x x', ArgG g p x → ArgG g' p x' → ∀ d, (Val e x d ↔ Val e' x' d)) →
    (H g e ↔ H g' e')
  /-- The root holds under every environment. -/
  root_holds : ∀ g : A, RootG g → ∀ e, Env e → G g e

/-! ### Matching the arguments of an atom

An assignment of the argument positions *matches* an atom under an environment
when it gives each argument position the value of the variable the atom has
there. The shape conditions of `DescriptiveComplexity.FinSat.IsWF` make such an
assignment exist, and make any two of them agree wherever the symbol's
signature can see – so “some matching assignment satisfies the symbol” and
“every matching assignment does” coincide, which is what the *negated* atom
clause of the truth definition needs. -/

/-- Some assignment of the argument positions matches the arguments of an
atom: they are functional. -/
theorem matching_exists (hwf : IsWF A) (g : A) {M : Type} (v : A → M) :
    ∃ w : A → M, ∀ p x, ArgG g p x → w p = v x := by
  classical
  refine ⟨fun p => if h : ∃ x, ArgG g p x then v h.choose else v p, fun p x hp => ?_⟩
  have hex : ∃ x, ArgG g p x := ⟨x, hp⟩
  change (if h : ∃ x, ArgG g p x then v h.choose else v p) = v x
  rw [dif_pos hex]
  exact congrArg v (hwf.arg_fun g p _ _ hex.choose_spec hp)

/-- Two assignments matching the arguments of an atom agree on every position
of its symbol's signature: the atom has an argument at each of them. -/
theorem matching_agree (hwf : IsWF A) {g s : A} (hs : PosG g s ∨ NegG g s) {M : Type}
    {v w w' : A → M} (hw : ∀ p x, ArgG g p x → w p = v x)
    (hw' : ∀ p x, ArgG g p x → w' p = v x) : ∀ p, SigG s p → w p = w' p := by
  intro p hp
  obtain ⟨x, hx⟩ := hwf.arg_tot g s p hs hp
  rw [hw p x hx, hw' p x hx]

/-! ### From a certificate to a model -/

section OfCert

variable {Elt Env : D → Prop} {Val : D → A → D → Prop} {G H : A → D → Prop}

/-- The environment object `e` represents the assignment `v`. -/
def Represents (Val : D → A → D → Prop) {Elt : D → Prop} (e : D)
    (v : A → {d : D // Elt d}) : Prop :=
  ∀ x : A, Val e x (v x : D)

/-- **The interpretation a certificate carries**: a symbol holds of an
assignment of its argument positions when some atom of that symbol, whose
arguments have those values under some environment, is guessed true. -/
def CertI (Env : D → Prop) (Val : D → A → D → Prop) (H : A → D → Prop) {Elt : D → Prop}
    (s : A) (w : A → {d : D // Elt d}) : Prop :=
  ∃ (g : A) (e : D), Env e ∧ (PosG g s ∨ NegG g s) ∧
    (∀ p x, ArgG g p x → Val e x (w p : D)) ∧ H g e

/-- The valuation of the nodes a certificate carries. -/
def CertV (Env : D → Prop) (Val : D → A → D → Prop) (G : A → D → Prop) {Elt : D → Prop}
    (v : A → {d : D // Elt d}) (g : A) : Prop :=
  ∃ e, Env e ∧ Represents Val e v ∧ G g e

variable (hc : CertOK Elt Env Val G H)
include hc

theorem val_iff_of_represents {e : D} (he : Env e) {v : A → {d : D // Elt d}}
    (hv : Represents Val e v) (x : A) (d : D) : Val e x d ↔ d = (v x : D) :=
  ⟨fun h => hc.val_fun e he x d _ h (hv x), fun h => h ▸ hv x⟩

/-- **Every assignment is represented**: the environments are closed under
updating one variable, and the instance has finitely many of them. -/
theorem represents_exists [Finite A] (v : A → {d : D // Elt d}) :
    ∃ e, Env e ∧ Represents Val e v := by
  classical
  let := Fintype.ofFinite A
  suffices h : ∀ S : Finset A, ∃ e, Env e ∧ ∀ x ∈ S, Val e x (v x : D) by
    obtain ⟨e, he, hS⟩ := h Finset.univ
    exact ⟨e, he, fun x => hS x (Finset.mem_univ x)⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨e, he⟩ := hc.env_nonempty
    exact ⟨e, he, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨e, he, hS⟩ := ih
    obtain ⟨e', he', hu⟩ := hc.val_update e he a (v a : D) (v a).2
    refine ⟨e', he', fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      exact hu.1
    · exact (hu.2 x hxa _).mpr (hS x ((Finset.mem_insert.mp hx).resolve_left hxa))

theorem certV_iff {e : D} (he : Env e) {v : A → {d : D // Elt d}}
    (hv : Represents Val e v) (g : A) : CertV Env Val G v g ↔ G g e := by
  constructor
  · rintro ⟨e', he', hv', hg⟩
    refine (hc.g_ext g e' e he' he fun x d => ?_).mp hg
    rw [val_iff_of_represents hc he' hv' x d, val_iff_of_represents hc he hv x d]
  · exact fun hg => ⟨e, he, hv, hg⟩

omit hc in
/-- The interpretation a certificate carries is local: an atom only has
arguments at the positions its symbol declares. -/
theorem certI_local (hwf : IsWF A) : Local (CertI Env Val H (Elt := Elt)) := by
  intro s w w' hww
  constructor <;> rintro ⟨g, e, he, hs, hargs, hH⟩ <;> refine ⟨g, e, he, hs, ?_, hH⟩ <;>
    intro p x hp
  · rw [← hww p (hwf.arg_sig g s p x hs hp)]
    exact hargs p x hp
  · rw [hww p (hwf.arg_sig g s p x hs hp)]
    exact hargs p x hp

/-- **The guessed truth value of an atom is the truth of that atom** in the
interpretation the certificate carries: coherence one way, the arguments of the
atom the other. -/
theorem certH_iff (hwf : IsWF A) {g s : A} (hs : PosG g s ∨ NegG g s) {e : D} (he : Env e)
    {v : A → {d : D // Elt d}} (hv : Represents Val e v) :
    H g e ↔ ∃ w, (∀ p x, ArgG g p x → w p = v x) ∧ CertI Env Val H s w := by
  classical
  constructor
  · intro hH
    obtain ⟨w, hw⟩ := matching_exists hwf g v
    refine ⟨w, hw, g, e, he, hs, fun p x hp => ?_, hH⟩
    rw [hw p x hp]
    exact hv x
  · rintro ⟨w, hw, g', e', he', hs', hargs', hH'⟩
    refine (hc.atom_coh g g' s e e' he he' hs hs' fun p x x' hx hx' d => ?_).mpr hH'
    have h1 : (w p : D) = (v x : D) := congrArg _ (hw p x hx)
    have h2 : Val e' x' (w p : D) := hargs' p x' hx'
    rw [val_iff_of_represents hc he hv x d]
    constructor
    · intro hd
      rw [hd, ← h1]
      exact h2
    · intro hd
      exact (hc.val_fun e' he' x' d (w p : D) hd h2).trans h1

/-- The same, read universally: all the assignments matching the arguments of
an atom give it the same value, so “some matching assignment” and “every
matching assignment” agree. -/
theorem certH_iff_forall (hwf : IsWF A) {g s : A} (hs : PosG g s ∨ NegG g s) {e : D}
    (he : Env e) {v : A → {d : D // Elt d}} (hv : Represents Val e v) :
    H g e ↔ ∀ w, (∀ p x, ArgG g p x → w p = v x) → CertI Env Val H s w := by
  rw [certH_iff hc hwf hs he hv]
  constructor
  · rintro ⟨w, hw, hI⟩ w' hw'
    exact (certI_local hwf s w w' (matching_agree hwf hs hw hw')).mp hI
  · intro h
    obtain ⟨w, hw⟩ := matching_exists hwf g v
    exact ⟨w, hw, h w hw⟩

omit hc [Language.finsat.Structure A] in
theorem represents_upd {e e' : D} {v : A → {d : D // Elt d}}
    (hv : Represents Val e v) {x : A} {d : {d : D // Elt d}}
    (hu : UpdAt Val e e' x (d : D)) : Represents Val e' (upd v x d) := by
  intro y
  by_cases hy : y = x
  · subst hy
    rw [upd_self]
    exact hu.1
  · rw [upd_of_ne v d hy]
    exact (hu.2 y hy _).mpr (hv y)

/-- **The certificate's truth values obey the truth definition** of the model
it carries: one clause at a time, the invented environments standing for the
assignments they represent. -/
theorem certStep_iff [Finite A] (hwf : IsWF A) {e : D} (he : Env e)
    {v : A → {d : D // Elt d}} (hv : Represents Val e v) (g : A) :
    CertStep Elt Env Val G H g e ↔
      gstep (CertI Env Val H) (CertV Env Val G) v g := by
  simp only [CertStep, gstep]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_
    (or_congr ?_ (or_congr ?_ ?_))))))
  · exact and_congr_right fun _ => forall_congr' fun c => imp_congr_right fun _ =>
      (certV_iff hc he hv c).symm
  · exact and_congr_right fun _ => exists_congr fun c => and_congr_right fun _ =>
      (certV_iff hc he hv c).symm
  · refine and_congr_right fun _ => forall_congr' fun x => imp_congr_right fun _ => ?_
    constructor
    · intro hL d c hcc
      obtain ⟨e', he', hu⟩ := hc.val_update e he x (d : D) d.2
      exact (certV_iff hc he' (represents_upd hv hu) c).mpr
        (hL (d : D) d.2 e' he' hu c hcc)
    · intro hR d hd e' he' hu c hcc
      exact (certV_iff hc he' (represents_upd hv (d := ⟨d, hd⟩) hu) c).mp
        (hR ⟨d, hd⟩ c hcc)
  · refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨x, hx, d, hd, e', he', hu, c, hcc, hG⟩
      exact ⟨x, hx, ⟨d, hd⟩, c, hcc,
        (certV_iff hc he' (represents_upd hv (d := ⟨d, hd⟩) hu) c).mpr hG⟩
    · rintro ⟨x, hx, d, c, hcc, hV⟩
      obtain ⟨e', he', hu⟩ := hc.val_update e he x (d : D) d.2
      exact ⟨x, hx, (d : D), d.2, e', he', hu, c, hcc,
        (certV_iff hc he' (represents_upd hv hu) c).mp hV⟩
  · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
    constructor
    · intro hL
      exact Subtype.ext (hc.val_fun e he y (v x : D) (v y : D) ((hL (v x : D)).mp (hv x)) (hv y))
    · intro hL d
      rw [val_iff_of_represents hc he hv x d, val_iff_of_represents hc he hv y d, hL]
  · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨d, hdx, hdy⟩ heq
      rw [val_iff_of_represents hc he hv x d] at hdx
      exact hdy (by rw [val_iff_of_represents hc he hv y d, hdx, heq])
    · intro hne
      exact ⟨(v x : D), hv x, fun hcon =>
        hne (Subtype.ext (hc.val_fun e he y (v x : D) (v y : D) hcon (hv y)))⟩
  · exact exists_congr fun s => and_congr_right fun hs => certH_iff hc hwf (Or.inl hs) he hv
  · refine exists_congr fun s => and_congr_right fun hs => ?_
    rw [certH_iff_forall hc hwf (Or.inr hs) he hv]
    constructor
    · intro hn
      obtain ⟨w, hw⟩ := matching_exists hwf g v
      refine ⟨w, hw, fun hI => hn fun w' hw' => ?_⟩
      exact (certI_local hwf s w w' (matching_agree hwf (Or.inr hs) hw hw')).mp hI
    · rintro ⟨w, hw, hnI⟩ hall
      exact hnI (hall w hw)

theorem certV_isEval [Finite A] (hwf : IsWF A) :
    IsEval (CertI Env Val H) (CertV Env Val G (Elt := Elt)) := by
  intro v g
  obtain ⟨e, he, hv⟩ := represents_exists hc v
  rw [certV_iff hc he hv g, hc.step g e he]
  exact certStep_iff hc hwf he hv g

/-- **A certificate gives a finite model**: its marked values are the universe,
its coherent atom values the interpretation, and its node values satisfaction –
by uniqueness of the fixed point of the truth definition. -/
theorem finSatOn_of_cert [Finite A] [Finite D] (hwf : IsWF A) : FinSatOn A := by
  obtain ⟨d₀, hd₀⟩ := hc.elt_nonempty
  have : Nonempty {d : D // Elt d} := ⟨⟨d₀, hd₀⟩⟩
  refine ⟨hwf, {d : D // Elt d}, inferInstance, inferInstance, CertI Env Val H,
    certI_local hwf, fun v g hg => ?_⟩
  obtain ⟨e, he, hv⟩ := represents_exists hc v
  exact (IsEval.iff_Gval hwf (certV_isEval hc hwf) v g).mp ⟨e, he, hv, hc.root_holds g hg e he⟩

end OfCert

/-! ### From a model to a certificate

The invented values are the assignments themselves: an environment *is* an
assignment, and an element of the model is the constant assignment at it. -/

section ToCert

variable {M : Type}

/-- The invented values standing for elements of the model: the constant
assignments. -/
def EnvElt (d : A → M) : Prop := ∃ z : M, d = fun _ => z

/-- The graph of an environment, when environments are assignments. -/
def EnvVal (e : A → M) (x : A) (d : A → M) : Prop := d = fun _ => e x

/-- The truth values of the nodes read off satisfaction. -/
def EnvG (I : A → (A → M) → Prop) (g : A) (e : A → M) : Prop := Gval I e g

/-- The truth values of the atoms read off the interpretation. -/
def EnvH (I : A → (A → M) → Prop) (g : A) (e : A → M) : Prop :=
  ∀ s : A, (PosG g s ∨ NegG g s) → ∃ w : A → M, (∀ p x, ArgG g p x → w p = e x) ∧ I s w

variable [Nonempty A] {I : A → (A → M) → Prop}

omit [Language.finsat.Structure A] in
theorem envVal_eq {e e' : A → M} {x x' : A} (h : ∀ d, EnvVal e x d ↔ EnvVal e' x' d) :
    e x = e' x' := by
  have h1 : EnvVal e' x' (fun _ => e x) := (h _).mp rfl
  exact congrFun h1 (Classical.arbitrary A)

omit [Language.finsat.Structure A] [Nonempty A] in
theorem updAt_upd (e : A → M) (x : A) (z : M) :
    UpdAt EnvVal e (upd e x z) x (fun _ => z) := by
  refine ⟨?_, fun y hy c => ?_⟩
  · change (fun _ => z) = fun _ => upd e x z x
    rw [upd_self]
  · change c = (fun _ => upd e x z y) ↔ c = fun _ => e y
    rw [upd_of_ne e z hy]

omit [Language.finsat.Structure A] in
theorem eq_upd_of_updAt {e e' : A → M} {x : A} {z : M}
    (hu : UpdAt EnvVal e e' x (fun _ => z)) : e' = upd e x z := by
  funext y
  by_cases hy : y = x
  · subst hy
    rw [upd_self]
    exact (congrFun hu.1 (Classical.arbitrary A)).symm
  · rw [upd_of_ne e z hy]
    exact envVal_eq (hu.2 y hy)

omit [Nonempty A] in
theorem envH_iff (hwf : IsWF A) {g s : A} (hs : PosG g s ∨ NegG g s) (e : A → M) :
    EnvH I g e ↔ ∃ w : A → M, (∀ p x, ArgG g p x → w p = e x) ∧ I s w := by
  refine ⟨fun h => h s hs, fun h s' hs' => ?_⟩
  rwa [hwf.atom_sym g s' s hs' hs]

omit [Nonempty A] in
/-- The same, read universally: every assignment matching the arguments of an
atom gives it the same value. -/
theorem envH_iff_forall (hwf : IsWF A) (hloc : Local I) {g s : A}
    (hs : PosG g s ∨ NegG g s) (e : A → M) :
    EnvH I g e ↔ ∀ w, (∀ p x, ArgG g p x → w p = e x) → I s w := by
  rw [envH_iff hwf hs e]
  constructor
  · rintro ⟨w, hw, hI⟩ w' hw'
    exact (hloc s w w' (matching_agree hwf hs hw hw')).mp hI
  · intro h
    obtain ⟨w, hw⟩ := matching_exists hwf g e
    exact ⟨w, hw, h w hw⟩

/-- The atom values read off a local interpretation cohere: an atom's arguments
cover exactly the argument positions of its symbol, so two atoms of that symbol
whose arguments have the same values are read at the same tuple. -/
theorem envH_coh (hwf : IsWF A) (hloc : Local I) {g g' s : A} {e e' : A → M}
    (hs : PosG g s ∨ NegG g s) (hs' : PosG g' s ∨ NegG g' s)
    (hval : ∀ p x x', ArgG g p x → ArgG g' p x' → ∀ d, (EnvVal e x d ↔ EnvVal e' x' d)) :
    EnvH I g e → EnvH I g' e' := by
  classical
  intro hH
  obtain ⟨w, hw, hI⟩ := (envH_iff hwf hs e).mp hH
  refine (envH_iff hwf hs' e').mpr
    ⟨fun p => if h : ∃ x', ArgG g' p x' then e' h.choose else w p, fun p x' hp => ?_, ?_⟩
  · have hex : ∃ x', ArgG g' p x' := ⟨x', hp⟩
    change (if h : ∃ x', ArgG g' p x' then e' h.choose else w p) = e' x'
    rw [dif_pos hex]
    exact congrArg e' (hwf.arg_fun g' p _ _ hex.choose_spec hp)
  · refine (hloc s _ w fun p hp => ?_).mpr hI
    obtain ⟨x, hx⟩ := hwf.arg_tot g s p hs hp
    obtain ⟨x', hx'⟩ := hwf.arg_tot g' s p hs' hp
    have hex : ∃ x', ArgG g' p x' := ⟨x', hx'⟩
    change (if h : ∃ x', ArgG g' p x' then e' h.choose else w p) = w p
    rw [dif_pos hex]
    have hch : hex.choose = x' := hwf.arg_fun g' p _ _ hex.choose_spec hx'
    rw [hch, hw p x hx]
    exact (envVal_eq (hval p x x' hx hx')).symm

/-- **A finite model gives a certificate**: invent the assignments. -/
theorem cert_of_model [Finite A] [Finite M] [Nonempty M] (hwf : IsWF A) (hloc : Local I)
    (hroot : ∀ (v : A → M) (g : A), RootG g → Gval I v g) :
    CertOK (A := A) EnvElt (fun _ => True) EnvVal (EnvG I) (EnvH I) where
  elt_nonempty := ⟨fun _ => Classical.arbitrary M, ⟨Classical.arbitrary M, rfl⟩⟩
  env_nonempty := ⟨fun _ => Classical.arbitrary M, trivial⟩
  val_total e _ x := ⟨fun _ => e x, ⟨e x, rfl⟩, rfl⟩
  val_fun _ _ _ _ _ hd hd' := hd.trans hd'.symm
  val_update e _ x d hd := by
    obtain ⟨z, rfl⟩ := hd
    exact ⟨upd e x z, trivial, updAt_upd e x z⟩
  g_ext g e e' _ _ hval := by
    have : e = e' := funext fun x => envVal_eq (hval x)
    rw [this]
  step g e _ := by
    change Gval I e g ↔ _
    rw [Gval_isEval hwf I e g]
    simp only [gstep, CertStep]
    refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ (or_congr ?_ (or_congr ?_
      (or_congr ?_ (or_congr ?_ ?_))))))
    · refine and_congr_right fun _ => forall_congr' fun x => imp_congr_right fun _ => ?_
      constructor
      · intro hL d hd e' _ hu c hcc
        obtain ⟨z, rfl⟩ := hd
        rw [eq_upd_of_updAt hu]
        exact hL z c hcc
      · intro hR z c hcc
        exact hR (fun _ => z) ⟨z, rfl⟩ (upd e x z) trivial (updAt_upd e x z) c hcc
    · refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => ?_
      constructor
      · rintro ⟨z, c, hcc, hG⟩
        exact ⟨fun _ => z, ⟨z, rfl⟩, upd e x z, trivial, updAt_upd e x z, c, hcc, hG⟩
      · rintro ⟨d, ⟨z, rfl⟩, e', _, hu, c, hcc, hG⟩
        rw [eq_upd_of_updAt hu] at hG
        exact ⟨z, c, hcc, hG⟩
    · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
      exact ⟨fun h d => by change d = (fun _ => e x) ↔ d = (fun _ => e y); rw [h],
        fun h => envVal_eq h⟩
    · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
      constructor
      · intro hne
        exact ⟨fun _ => e x, rfl, fun hcon => hne (congrFun hcon (Classical.arbitrary A))⟩
      · rintro ⟨d, hdx, hdy⟩ heq
        exact hdy (hdx.trans (by rw [heq]))
    · exact exists_congr fun s => and_congr_right fun hs => (envH_iff hwf (Or.inl hs) e).symm
    · refine exists_congr fun s => and_congr_right fun hs => ?_
      rw [envH_iff_forall hwf hloc (Or.inr hs) e]
      constructor
      · rintro ⟨w, hw, hnI⟩ hall
        exact hnI (hall w hw)
      · intro hn
        obtain ⟨w, hw⟩ := matching_exists hwf g e
        exact ⟨w, hw, fun hI => hn fun w' hw' =>
          (hloc s w w' (matching_agree hwf (Or.inr hs) hw hw')).mp hI⟩
  atom_coh g g' s e e' _ _ hs hs' hval :=
    ⟨envH_coh hwf hloc hs hs' hval,
      envH_coh hwf hloc hs' hs fun p x' x hx' hx d => (hval p x x' hx hx' d).symm⟩
  root_holds g hg e _ := hroot e g hg

end ToCert

/-! ### Relabeling the invented values

The `∃SO[new]` sentence of `DescriptiveComplexity.Problems.FinSat.Membership` guesses its
relations over `A ⊕ Fin m`, so it needs the invented values *indexed*. Nothing
in `DescriptiveComplexity.FinSat.CertOK` looks at the set of invented values
beyond its elements, so a bijection carries a certificate over one such set to a
certificate over another, one field at a time. -/

section Transport

variable {D' : Type}

omit [Language.finsat.Structure A] in
private theorem forall_symm (σ : D ≃ D') (p : D → Prop) :
    (∀ d : D', p (σ.symm d)) ↔ ∀ d : D, p d :=
  ⟨fun h d => by simpa using h (σ d), fun h d => h _⟩

omit [Language.finsat.Structure A] in
private theorem exists_symm (σ : D ≃ D') (p : D → Prop) :
    (∃ d : D', p (σ.symm d)) ↔ ∃ d : D, p d :=
  ⟨fun ⟨_, hd⟩ => ⟨_, hd⟩, fun ⟨d, hd⟩ => ⟨σ d, by simpa using hd⟩⟩

/-- The graph of an environment, relabeled along a bijection of the invented
values. -/
def mapVal (σ : D ≃ D') (Val : D → A → D → Prop) : D' → A → D' → Prop :=
  fun e x d => Val (σ.symm e) x (σ.symm d)

omit [Language.finsat.Structure A] in
theorem updAt_map (σ : D ≃ D') (Val : D → A → D → Prop) (e e' : D') (x : A) (d : D') :
    UpdAt (mapVal σ Val) e e' x d ↔ UpdAt Val (σ.symm e) (σ.symm e') x (σ.symm d) := by
  simp only [UpdAt, mapVal]
  refine and_congr Iff.rfl (forall_congr' fun y => imp_congr_right fun _ => ?_)
  exact forall_symm σ fun c => Val (σ.symm e') y c ↔ Val (σ.symm e) y c

/-- The truth definition, read on a relabeled certificate. -/
theorem certStep_map (σ : D ≃ D') {Elt Env : D → Prop} {Val : D → A → D → Prop}
    {G H : A → D → Prop} (g : A) (e : D') :
    CertStep (fun d => Elt (σ.symm d)) (fun e => Env (σ.symm e)) (mapVal σ Val)
        (fun g e => G g (σ.symm e)) (fun g e => H g (σ.symm e)) g e ↔
      CertStep Elt Env Val G H g (σ.symm e) := by
  simp only [CertStep, updAt_map]
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ (or_congr ?_ (or_congr ?_
    (or_congr ?_ (or_congr Iff.rfl Iff.rfl))))))
  · refine and_congr_right fun _ => forall_congr' fun x => imp_congr_right fun _ => ?_
    constructor
    · intro h d hd e' he' hu c hc
      simpa using
        h (σ d) (by simpa using hd) (σ e') (by simpa using he') (by simpa using hu) c hc
    · intro h d hd e' he' hu c hc
      exact h (σ.symm d) hd (σ.symm e') he' hu c hc
  · refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨d, hd, e', he', hu, c, hc, hG⟩
      exact ⟨σ.symm d, hd, σ.symm e', he', hu, c, hc, hG⟩
    · rintro ⟨d, hd, e', he', hu, c, hc, hG⟩
      exact ⟨σ d, by simpa using hd, σ e', by simpa using he', by simpa using hu, c, hc,
        by simpa using hG⟩
  · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
    exact forall_symm σ fun d => Val (σ.symm e) x d ↔ Val (σ.symm e) y d
  · refine exists_congr fun x => exists_congr fun y => and_congr_right fun _ => ?_
    exact exists_symm σ fun d => Val (σ.symm e) x d ∧ ¬Val (σ.symm e) y d

/-- **A certificate can be carried to any equinumerous set of invented
values**, which is what lets the `∃SO[new]` sentence guess its relations over
the extension `A ⊕ Fin m` of the universe. -/
theorem CertOK.map (σ : D ≃ D') {Elt Env : D → Prop} {Val : D → A → D → Prop}
    {G H : A → D → Prop} (hc : CertOK Elt Env Val G H) :
    CertOK (fun d => Elt (σ.symm d)) (fun e => Env (σ.symm e)) (mapVal σ Val)
      (fun g e => G g (σ.symm e)) (fun g e => H g (σ.symm e)) where
  elt_nonempty := by
    obtain ⟨d, hd⟩ := hc.elt_nonempty
    exact ⟨σ d, by simpa using hd⟩
  env_nonempty := by
    obtain ⟨e, he⟩ := hc.env_nonempty
    exact ⟨σ e, by simpa using he⟩
  val_total e he x := by
    obtain ⟨d, hd, hv⟩ := hc.val_total _ he x
    exact ⟨σ d, by simpa using hd, by simpa [mapVal] using hv⟩
  val_fun _ he x _ _ hd hd' := σ.symm.injective (hc.val_fun _ he x _ _ hd hd')
  val_update e he x d hd := by
    obtain ⟨e', he', hu⟩ := hc.val_update _ he x _ hd
    exact ⟨σ e', by simpa using he', by rw [updAt_map]; simpa using hu⟩
  g_ext g e e' he he' hval :=
    hc.g_ext g _ _ he he' fun x d => by simpa [mapVal] using hval x (σ d)
  step g e he := by
    rw [certStep_map]
    exact hc.step g _ he
  atom_coh g g' s e e' he he' hs hs' hval :=
    hc.atom_coh g g' s _ _ he he' hs hs'
      fun p x x' hx hx' d => by simpa [mapVal] using hval p x x' hx hx' (σ d)
  root_holds g hg e he := hc.root_holds g hg _ he

end Transport

/-! ### The characterization -/

/-- **An encoded sentence has a finite model exactly when a finite set of
invented values carries one.** The right-hand side is first-order in the
instance together with five guessed relations, which is what
`DescriptiveComplexity.Problems.FinSat.Membership` turns into an `∃SO[new]`
sentence. -/
theorem finSatOn_iff_cert (A : Type) [Language.finsat.Structure A] [Finite A] [Nonempty A] :
    FinSatOn A ↔ IsWF A ∧ ∃ (D : Type) (_ : Finite D) (Elt Env : D → Prop)
      (Val : D → A → D → Prop) (G H : A → D → Prop), CertOK Elt Env Val G H := by
  constructor
  · rintro ⟨hwf, M, hMfin, hMne, I, hloc, hroot⟩
    exact ⟨hwf, A → M, inferInstance, EnvElt, fun _ => True, EnvVal, EnvG I, EnvH I,
      cert_of_model hwf hloc hroot⟩
  · rintro ⟨hwf, D, hDfin, Elt, Env, Val, G, H, hc⟩
    exact finSatOn_of_cert hc hwf

/-- The same, with the invented values **indexed**: exactly the form the
`∃SO[new]` sentence of `DescriptiveComplexity.Problems.FinSat.Membership` needs, its
relation variables ranging over the extension `A ⊕ Fin m` of the universe. -/
theorem finSatOn_iff_certFin (A : Type) [Language.finsat.Structure A] [Finite A] [Nonempty A] :
    FinSatOn A ↔ IsWF A ∧ ∃ (m : ℕ) (Elt Env : Fin m → Prop)
      (Val : Fin m → A → Fin m → Prop) (G H : A → Fin m → Prop), CertOK Elt Env Val G H := by
  rw [finSatOn_iff_cert]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨D, hDfin, Elt, Env, Val, G, H, hc⟩
    obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin D
    exact ⟨n, _, _, _, _, _, hc.map σ⟩
  · rintro ⟨m, Elt, Env, Val, G, H, hc⟩
    exact ⟨Fin m, inferInstance, Elt, Env, Val, G, H, hc⟩

end FinSat

end DescriptiveComplexity
