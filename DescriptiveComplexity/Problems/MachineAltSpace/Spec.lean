/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.MachineAltSpace.Guards

/-!
# The configuration block, and the four sentences of the machine

The second layer: the block whose assignments are the configurations, and the
`DescriptiveComplexity.SOGameSpec` an alternating machine is.

* `DescriptiveComplexity.ATMSpace.cfgBlock` has one variable for the state, one
  for the head and one – **binary** – for the tape, a
  `DescriptiveComplexity.Config` carrying a function `A → A`;
* `DescriptiveComplexity.ATMSpace.isCfgS` says an assignment is a configuration:
  the two unary variables are singletons and the binary one is a function.
  `DescriptiveComplexity.ATMSpace.cfgOf` is the assignment a configuration is,
  and `DescriptiveComplexity.ATMSpace.exists_cfgOf` the equivalence;
* the four sentences follow `DescriptiveComplexity.TMData.Step`,
  `DescriptiveComplexity.ATMData.IsUniv`, `DescriptiveComplexity.TMData.Acc` and
  `DescriptiveComplexity.TMData.IsInit`. Every quantifier in them ranges over
  the **base** – a transition, a state, a head position, a symbol – which is
  what keeps them first-order there.

The two promises `DescriptiveComplexity.TMData.WellFormed` and
`DescriptiveComplexity.ATMData.BlocksSplit` are conjoined to `start`:
`DescriptiveComplexity.ExpDefinable` compares `P A` with `Q (X.Map A)` and has
nowhere else to put a condition on `A` alone.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace ATMSpace

/-! ### The block -/

/-- The relation variables a configuration is made of. -/
inductive CIx where
  /-- The current state. -/
  | st
  /-- The cell the head is on. -/
  | hd
  /-- The contents of each cell. -/
  | tp
  deriving DecidableEq

instance : Fintype CIx := ⟨{CIx.st, CIx.hd, CIx.tp}, by intro x; cases x <;> simp⟩

/-- **The configuration block**: a unary variable for the state, a unary one for
the head, and a binary one for the tape. -/
abbrev cfgBlock : SOBlock where
  ι := CIx
  arity := fun i => match i with | .st => 1 | .hd => 1 | .tp => 2

/-- The base vocabulary expanded by one copy of the block. -/
abbrev cfg1 : Language.{0, 0} := tmaOrd.sum cfgBlock.lang

/-- The base vocabulary expanded by two copies of the block. -/
abbrev cfg2 : Language.{0, 0} := cfg1.sum cfgBlock.lang

/-! ### The atoms of the block -/

/-- The state variable, at one copy. -/
abbrev stS : cfg1.Relations 1 := Sum.inr ⟨CIx.st, rfl⟩

/-- The head variable, at one copy. -/
abbrev hdS : cfg1.Relations 1 := Sum.inr ⟨CIx.hd, rfl⟩

/-- The tape variable, at one copy. -/
abbrev tpS : cfg1.Relations 2 := Sum.inr ⟨CIx.tp, rfl⟩

/-- The state variable of the current configuration. -/
abbrev stA : cfg2.Relations 1 := Sum.inl (Sum.inr ⟨CIx.st, rfl⟩)

/-- The head variable of the current configuration. -/
abbrev hdA : cfg2.Relations 1 := Sum.inl (Sum.inr ⟨CIx.hd, rfl⟩)

/-- The tape variable of the current configuration. -/
abbrev tpA : cfg2.Relations 2 := Sum.inl (Sum.inr ⟨CIx.tp, rfl⟩)

/-- The state variable of the next configuration. -/
abbrev stB : cfg2.Relations 1 := Sum.inr ⟨CIx.st, rfl⟩

/-- The head variable of the next configuration. -/
abbrev hdB : cfg2.Relations 1 := Sum.inr ⟨CIx.hd, rfl⟩

/-- The tape variable of the next configuration. -/
abbrev tpB : cfg2.Relations 2 := Sum.inr ⟨CIx.tp, rfl⟩

section Atoms

variable {γ : Type}

/-- `x` is the state, at one copy. -/
noncomputable def stF (x : γ) : cfg1.Formula γ := Relations.formula₁ stS (Term.var x)

/-- `x` is the head, at one copy. -/
noncomputable def hdF (x : γ) : cfg1.Formula γ := Relations.formula₁ hdS (Term.var x)

/-- The cell `x` holds `y`, at one copy. -/
noncomputable def tpF (x y : γ) : cfg1.Formula γ :=
  Relations.formula₂ tpS (Term.var x) (Term.var y)

/-- `x` is the state of the current configuration. -/
noncomputable def stAF (x : γ) : cfg2.Formula γ := Relations.formula₁ stA (Term.var x)

/-- `x` is the head of the current configuration. -/
noncomputable def hdAF (x : γ) : cfg2.Formula γ := Relations.formula₁ hdA (Term.var x)

/-- The cell `x` holds `y` in the current configuration. -/
noncomputable def tpAF (x y : γ) : cfg2.Formula γ :=
  Relations.formula₂ tpA (Term.var x) (Term.var y)

/-- `x` is the state of the next configuration. -/
noncomputable def stBF (x : γ) : cfg2.Formula γ := Relations.formula₁ stB (Term.var x)

/-- `x` is the head of the next configuration. -/
noncomputable def hdBF (x : γ) : cfg2.Formula γ := Relations.formula₁ hdB (Term.var x)

/-- The cell `x` holds `y` in the next configuration. -/
noncomputable def tpBF (x y : γ) : cfg2.Formula γ :=
  Relations.formula₂ tpB (Term.var x) (Term.var y)

/-- A base guard, read at one copy of the block. -/
noncomputable def lift1 (φ : tmaOrd.Formula γ) : cfg1.Formula γ := LHom.sumInl.onFormula φ

/-- A base guard, read at two copies of the block. -/
noncomputable def lift2 (φ : tmaOrd.Formula γ) : cfg2.Formula γ :=
  LHom.sumInl.onFormula (LHom.sumInl.onFormula φ)

end Atoms

/-! ### What an assignment says -/

section Reading

variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]

/-- The state an assignment names. -/
def St (ρ : cfgBlock.Assignment A) (q : A) : Prop := ρ CIx.st fun _ => q

/-- The head position an assignment names. -/
def Hd (ρ : cfgBlock.Assignment A) (h : A) : Prop := ρ CIx.hd fun _ => h

/-- The tape an assignment names. -/
def Tp (ρ : cfgBlock.Assignment A) (p a : A) : Prop := ρ CIx.tp ![p, a]

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
/-- A unary variable is read at its only argument. -/
theorem apply₁ (f : (Fin 1 → A) → Prop) (v : Fin 1 → A) : f v ↔ f fun _ => v 0 :=
  iff_of_eq (congrArg f (funext fun j => congrArg v (Subsingleton.elim j 0)))

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
/-- A binary variable is read at its two arguments. -/
theorem apply₂ (f : (Fin 2 → A) → Prop) (v : Fin 2 → A) : f v ↔ f ![v 0, v 1] := by
  refine iff_of_eq (congrArg f (funext fun j => ?_))
  fin_cases j <;> rfl

variable {γ : Type} {v : γ → A}

@[simp]
theorem realize_stF (ρ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) _ (stF x) v ↔ St ρ (v x)) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [stF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_hdF (ρ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) _ (hdF x) v ↔ Hd ρ (v x)) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [hdF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_tpF (ρ : cfgBlock.Assignment A) (x y : γ) :
    (@Formula.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) _ (tpF x y) v ↔
      Tp ρ (v x) (v y)) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [tpF, Formula.realize_rel₂]
  exact apply₂ _ _

@[simp]
theorem realize_stAF (ρ σ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (stAF x) v ↔
      St ρ (v x)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [stAF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_hdAF (ρ σ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (hdAF x) v ↔
      Hd ρ (v x)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [hdAF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_tpAF (ρ σ : cfgBlock.Assignment A) (x y : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (tpAF x y) v ↔
      Tp ρ (v x) (v y)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [tpAF, Formula.realize_rel₂]
  exact apply₂ _ _

@[simp]
theorem realize_stBF (ρ σ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (stBF x) v ↔
      St σ (v x)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [stBF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_hdBF (ρ σ : cfgBlock.Assignment A) (x : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (hdBF x) v ↔
      Hd σ (v x)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [hdBF, Formula.realize_rel₁]
  exact apply₁ _ _

@[simp]
theorem realize_tpBF (ρ σ : cfgBlock.Assignment A) (x y : γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (tpBF x y) v ↔
      Tp σ (v x) (v y)) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [tpBF, Formula.realize_rel₂]
  exact apply₂ _ _

@[simp]
theorem realize_lift1 (ρ : cfgBlock.Assignment A) (φ : tmaOrd.Formula γ) :
    (@Formula.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) _ (lift1 φ) v ↔
      φ.Realize v) := by
  letI := cfgBlock.structure ρ
  rw [lift1]
  exact LHom.realize_onFormula _ φ

@[simp]
theorem realize_lift2 (ρ σ : cfgBlock.Assignment A) (φ : tmaOrd.Formula γ) :
    (@Formula.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) _ (lift2 φ) v ↔
      φ.Realize v) := by
  letI := cfgBlock.structure ρ
  letI := cfgBlock.structure σ
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [lift2]
  exact (LHom.realize_onFormula _ (LHom.sumInl.onFormula φ)).trans
    (LHom.realize_onFormula _ φ)

end Reading

/-! ### Configurations -/

section Cfg

variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]

/-- **The assignment a configuration is.** -/
def cfgOf (c : Config A) : cfgBlock.Assignment A := fun i =>
  match i with
  | .st => fun v => v 0 = c.state
  | .hd => fun v => v 0 = c.head
  | .tp => fun v => c.tape (v 0) = v 1

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
@[simp]
theorem st_cfgOf (c : Config A) (q : A) : St (cfgOf c) q ↔ q = c.state := Iff.rfl

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
@[simp]
theorem hd_cfgOf (c : Config A) (h : A) : Hd (cfgOf c) h ↔ h = c.head := Iff.rfl

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
@[simp]
theorem tp_cfgOf (c : Config A) (p a : A) : Tp (cfgOf c) p a ↔ c.tape p = a := Iff.rfl

/-- **An assignment is a configuration**: the two unary variables are singletons
and the binary one is a function. -/
def IsCfg (ρ : cfgBlock.Assignment A) : Prop :=
  (∃ q, St ρ q) ∧ ((∀ q q', St ρ q → St ρ q' → q = q') ∧
    ((∃ h, Hd ρ h) ∧ ((∀ h h', Hd ρ h → Hd ρ h' → h = h') ∧
      ((∀ p, ∃ a, Tp ρ p a) ∧ ∀ p a a', Tp ρ p a → Tp ρ p a' → a = a'))))

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
theorem isCfg_cfgOf (c : Config A) : IsCfg (cfgOf c) :=
  ⟨⟨c.state, rfl⟩, fun _ _ h1 h2 => h1.trans h2.symm,
    ⟨c.head, rfl⟩, fun _ _ h1 h2 => h1.trans h2.symm,
    fun p => ⟨c.tape p, rfl⟩, fun _ _ _ h1 h2 => h1.symm.trans h2⟩

omit [(Language.turingAlt 2).Structure A] [LinearOrder A] in
/-- **A configuration assignment is the assignment of a configuration.** -/
theorem exists_cfgOf {ρ : cfgBlock.Assignment A} (h : IsCfg ρ) : ∃ c : Config A, ρ = cfgOf c := by
  classical
  obtain ⟨⟨q, hq⟩, huq, ⟨hh, hhh⟩, huh, hex, hut⟩ := h
  choose f hf using hex
  refine ⟨⟨q, hh, f⟩, funext fun i => ?_⟩
  match i with
  | .st =>
    funext v
    refine propext ?_
    refine (apply₁ (ρ CIx.st) v).trans ?_
    exact ⟨fun hv => huq _ _ hv hq, fun hv => hv ▸ hq⟩
  | .hd =>
    funext v
    refine propext ?_
    refine (apply₁ (ρ CIx.hd) v).trans ?_
    exact ⟨fun hv => huh _ _ hv hhh, fun hv => hv ▸ hhh⟩
  | .tp =>
    funext v
    refine propext ?_
    refine (apply₂ (ρ CIx.tp) v).trans ?_
    exact ⟨fun hv => hut _ _ _ (hf (v 0)) hv, fun hv => hv ▸ hf (v 0)⟩

end Cfg

/-! ### The four sentences -/

/-- An assignment is a configuration, as a sentence over one copy. -/
noncomputable def isCfgS : cfg1.Sentence :=
  Formula.iExs (Fin 1) (stF (Sum.inr 0)) ⊓
    (Formula.iAlls (Fin 2) ((stF (Sum.inr 0) ⊓ stF (Sum.inr 1)) ⟹
        lift1 (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
      (Formula.iExs (Fin 1) (hdF (Sum.inr 0)) ⊓
        (Formula.iAlls (Fin 2) ((hdF (Sum.inr 0) ⊓ hdF (Sum.inr 1)) ⟹
            lift1 (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
          (Formula.iAlls (Fin 1) (Formula.iExs (Fin 1)
              (tpF (Sum.inl (Sum.inr 0)) (Sum.inr 0))) ⊓
            Formula.iAlls (Fin 3) ((tpF (Sum.inr 0) (Sum.inr 1) ⊓ tpF (Sum.inr 0) (Sum.inr 2)) ⟹
              lift1 (eqG (Sum.inr 1) (Sum.inr 2)))))))

/-- The *next* configuration is a configuration, as a sentence over two
copies. -/
noncomputable def isCfgBS : cfg2.Sentence :=
  Formula.iExs (Fin 1) (stBF (Sum.inr 0)) ⊓
    (Formula.iAlls (Fin 2) ((stBF (Sum.inr 0) ⊓ stBF (Sum.inr 1)) ⟹
        lift2 (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
      (Formula.iExs (Fin 1) (hdBF (Sum.inr 0)) ⊓
        (Formula.iAlls (Fin 2) ((hdBF (Sum.inr 0) ⊓ hdBF (Sum.inr 1)) ⟹
            lift2 (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
          (Formula.iAlls (Fin 1) (Formula.iExs (Fin 1)
              (tpBF (Sum.inl (Sum.inr 0)) (Sum.inr 0))) ⊓
            Formula.iAlls (Fin 3) ((tpBF (Sum.inr 0) (Sum.inr 1) ⊓ tpBF (Sum.inr 0) (Sum.inr 2)) ⟹
              lift2 (eqG (Sum.inr 1) (Sum.inr 2)))))))

/-- The state is marked by the universal player. -/
noncomputable def univS : cfg1.Sentence :=
  Formula.iExs (Fin 1) (stF (Sum.inr 0) ⊓ lift1 (blkG (1 : Fin 2) (Sum.inr 0)))

/-- The state is accepting. -/
noncomputable def wonS : cfg1.Sentence :=
  Formula.iExs (Fin 1) (stF (Sum.inr 0) ⊓ lift1 (accG (Sum.inr 0)))

section SentenceRealize

variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]

theorem realize_isCfgS (ρ : cfgBlock.Assignment A) :
    (@Sentence.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) isCfgS ↔ IsCfg ρ) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [isCfgS, IsCfg, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_imp, realize_stF, realize_hdF, realize_tpF, realize_lift1, realize_eqG,
    Sum.elim_inl, Sum.elim_inr]
  refine and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩
    (and_congr ⟨fun h q q' h1 h2 => h ![q, q'] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
      (and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨h, hh⟩ => ⟨fun _ => h, hh⟩⟩
        (and_congr ⟨fun h q q' h1 h2 => h ![q, q'] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          (and_congr ?_ ?_))))
  · exact ⟨fun h p => ⟨(h fun _ => p).choose 0, (h fun _ => p).choose_spec⟩,
      fun h w => ⟨fun _ => (h (w 0)).choose, (h (w 0)).choose_spec⟩⟩
  · exact ⟨fun h p a a' h1 h2 => h ![p, a, a'] ⟨h1, h2⟩,
      fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩

theorem realize_isCfgBS (ρ σ : cfgBlock.Assignment A) :
    (@Sentence.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) ρ σ) isCfgBS ↔ IsCfg σ) := by
  letI := cfgBlock.structure₂ (L := tmaOrd) ρ σ
  rw [isCfgBS, IsCfg, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_imp, realize_stBF, realize_hdBF, realize_tpBF, realize_lift2, realize_eqG,
    Sum.elim_inl, Sum.elim_inr]
  refine and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩
    (and_congr ⟨fun h q q' h1 h2 => h ![q, q'] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
      (and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨h, hh⟩ => ⟨fun _ => h, hh⟩⟩
        (and_congr ⟨fun h q q' h1 h2 => h ![q, q'] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          (and_congr ?_ ?_))))
  · exact ⟨fun h p => ⟨(h fun _ => p).choose 0, (h fun _ => p).choose_spec⟩,
      fun h w => ⟨fun _ => (h (w 0)).choose, (h (w 0)).choose_spec⟩⟩
  · exact ⟨fun h p a a' h1 h2 => h ![p, a, a'] ⟨h1, h2⟩,
      fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩

theorem realize_univS (c : Config A) :
    (@Sentence.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)) univS ↔
      RelMap (atmBlk (1 : Fin 2)) ![c.state]) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)
  rw [univS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_stF, realize_lift1,
    realize_blkG, st_cfgOf, Sum.elim_inr]
  exact ⟨fun ⟨w, hw, hb⟩ => hw ▸ hb, fun hb => ⟨fun _ => c.state, rfl, hb⟩⟩

theorem realize_wonS (c : Config A) :
    (@Sentence.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)) wonS ↔
      ATMAcc (k := 2) c.state) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)
  rw [wonS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_stF, realize_lift1,
    realize_accG, st_cfgOf, Sum.elim_inr]
  exact ⟨fun ⟨w, hw, hb⟩ => hw ▸ hb, fun hb => ⟨fun _ => c.state, rfl, hb⟩⟩

end SentenceRealize

/-! ### The step relation

Seven elements of the base are quantified – the transition, the two states, the
two head positions, the symbol read and the symbol written – and one pair is
quantified universally, for the cells the head does not touch. Nothing here
quantifies over a *configuration*, which is what keeps the sentence first-order
over the base. -/

/-- **One step of the machine**, as a sentence over two copies of the block. -/
noncomputable def stepS : cfg2.Sentence :=
  Formula.iExs (Fin 7)
    (lift2 (trG (Sum.inr 0)) ⊓
      (stAF (Sum.inr 1) ⊓
        (lift2 (srcG (Sum.inr 0) (Sum.inr 1)) ⊓
          (stBF (Sum.inr 2) ⊓
            (lift2 (dstG (Sum.inr 0) (Sum.inr 2)) ⊓
              (hdAF (Sum.inr 3) ⊓
                (hdBF (Sum.inr 4) ⊓
                  (tpAF (Sum.inr 3) (Sum.inr 5) ⊓
                    (lift2 (readG (Sum.inr 0) (Sum.inr 5)) ⊓
                      (tpBF (Sum.inr 3) (Sum.inr 6) ⊓
                        (lift2 (writeG (Sum.inr 0) (Sum.inr 6)) ⊓
                          (Formula.iAlls (Fin 2)
                              (∼(lift2 (eqG (Sum.inr 0) (Sum.inl (Sum.inr 3)))) ⟹
                                (tpBF (Sum.inr 0) (Sum.inr 1) ⇔ tpAF (Sum.inr 0) (Sum.inr 1))) ⊓
                            ((lift2 (rightG (Sum.inr 0)) ⊓
                                lift2 (succPosG (Sum.inr 3) (Sum.inr 4))) ⊔
                              (∼(lift2 (rightG (Sum.inr 0))) ⊓
                                lift2 (succPosG (Sum.inr 4) (Sum.inr 3))))))))))))))))

/-! ### The starting configurations -/

/-- **An initial configuration**, as a sentence over one copy. -/
noncomputable def isInitS : cfg1.Sentence :=
  Formula.iExs (Fin 1) (stF (Sum.inr 0) ⊓ lift1 (startG (Sum.inr 0))) ⊓
    (Formula.iExs (Fin 1) (hdF (Sum.inr 0) ⊓ lift1 (minPosG (Sum.inr 0))) ⊓
      Formula.iAlls (Fin 2) (tpF (Sum.inr 0) (Sum.inr 1) ⟹
        lift1 (initTapeG (Sum.inr 0) (Sum.inr 1))))

/-- **A starting state of the game**: the two promises about the instance, and
an initial configuration. -/
noncomputable def startS : cfg1.Sentence :=
  lift1 wfS ⊓ (lift1 blocksSplitS ⊓ (isCfgS ⊓ isInitS))

section BigRealize

variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]

theorem realize_stepS (c c' : Config A) :
    (@Sentence.Realize cfg2 A (cfgBlock.structure₂ (L := tmaOrd) (cfgOf c) (cfgOf c')) stepS ↔
      (atmData 2 A).toTMData.Step c c') := by
  letI := cfgBlock.structure₂ (L := tmaOrd) (cfgOf c) (cfgOf c')
  rw [stepS, TMData.Step, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, Formula.realize_imp, Formula.realize_iAlls, Formula.realize_iff,
    realize_stAF, realize_stBF, realize_hdAF, realize_hdBF, realize_tpAF, realize_tpBF,
    realize_lift2, realize_trG, realize_srcG, realize_dstG, realize_readG, realize_writeG,
    realize_rightG, realize_succPosG, realize_eqG, st_cfgOf, hd_cfgOf, tp_cfgOf,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨w, htr, hq, hsrc, hq', hdst, hh, hh', hta, hread, htb, hwrite, hframe, hdir⟩
    rw [hq] at hsrc
    rw [hq'] at hdst
    rw [hh] at hta htb hframe
    rw [hh, hh'] at hdir
    rw [← hta] at hread
    rw [← htb] at hwrite
    refine ⟨w 0, htr, hsrc, hread, hdst, hwrite, fun p hp => ?_, hdir⟩
    exact (hframe ![p, c.tape p] hp).mpr rfl
  · rintro ⟨τ, htr, hsrc, hread, hdst, hwrite, hframe, hdir⟩
    refine ⟨![τ, c.state, c'.state, c.head, c'.head, c.tape c.head, c'.tape c.head],
      htr, rfl, hsrc, rfl, hdst, rfl, rfl, rfl, hread, rfl, hwrite, fun i hi => ?_, hdir⟩
    rw [hframe (i 0) hi]

theorem realize_isInitS (c : Config A) :
    (@Sentence.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)) isInitS ↔
      (atmData 2 A).toTMData.IsInit c) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) (cfgOf c)
  rw [isInitS, TMData.IsInit, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_imp,
    Formula.realize_iAlls, realize_stF, realize_hdF, realize_tpF, realize_lift1,
    realize_startG, realize_minPosG, realize_initTapeG, st_cfgOf, hd_cfgOf, tp_cfgOf,
    Sum.elim_inr]
  refine and_congr ⟨fun ⟨w, hw, hs⟩ => hw ▸ hs, fun hs => ⟨fun _ => c.state, rfl, hs⟩⟩
    (and_congr ⟨fun ⟨w, hw, hs⟩ => hw ▸ hs, fun hs => ⟨fun _ => c.head, rfl, hs⟩⟩ ?_)
  exact ⟨fun h p => h ![p, c.tape p] rfl, fun h w hw => hw ▸ h (w 0)⟩

theorem realize_startS (ρ : cfgBlock.Assignment A) :
    (@Sentence.Realize cfg1 A (cfgBlock.structure₁ (L := tmaOrd) ρ) startS ↔
      ((atmData 2 A).toTMData.WellFormed ∧ (atmData 2 A).BlocksSplit ∧
        ∃ c : Config A, ρ = cfgOf c ∧ (atmData 2 A).toTMData.IsInit c)) := by
  letI := cfgBlock.structure₁ (L := tmaOrd) ρ
  rw [startS, Sentence.Realize]
  simp only [Formula.realize_inf, realize_lift1]
  refine and_congr realize_wfS (and_congr realize_blocksSplitS ?_)
  constructor
  · rintro ⟨hcfg, hinit⟩
    obtain ⟨c, rfl⟩ := exists_cfgOf ((realize_isCfgS ρ).mp hcfg)
    exact ⟨c, rfl, (realize_isInitS c).mp hinit⟩
  · rintro ⟨c, rfl, hinit⟩
    exact ⟨(realize_isCfgS (cfgOf c)).mpr (isCfg_cfgOf c), (realize_isInitS c).mpr hinit⟩

end BigRealize

end ATMSpace

end DescriptiveComplexity
