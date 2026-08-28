/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

/-!
# A surface syntax for first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula` is locally nameless: a variable
bound by the `k`-th enclosing block is written `Sum.inr i` under `k - 1`
applications of `Sum.inl`. Writing a clause by hand therefore means counting
blocks, and reading one means counting them back.

`fo%` removes the counting. It is a *macro*: it elaborates to exactly the
`DescriptiveComplexity.Formula.iAlls` / `Term.var (Sum.inr _)` term one would
have written, so a definition converted to it is unchanged, its equation lemma
is unchanged, and every proof about it – `simp only [myClause,
Formula.realize_iAlls, …]` – keeps working verbatim.

```
fo% ∀ x₀ x₁ x₂ x₃,
  (((patV(x₀) ∧ patV(x₁)) ∧ patE(x₀, x₁)) ∧ map(x₀, x₂)) ∧ map(x₁, x₃) →
    hostE(x₂, x₃)
```

## The syntax

Connectives are `∧ ∨ ¬ → ↔` (for `⊓ ⊔ ∼ .imp .iff`), with `⊤ᶠ` and `⊥ᶠ` for the
constants; `∧` and `∨` associate to the right, so a left-nested conjunction
needs its parentheses. `∀ x y z, φ` and `∃ x y z, φ` each bind *one* block, so
they produce a single `iAlls (Fin 3)` and `Formula.realize_iAlls` fires once,
as it does today. `⋀ i : T, φ` and `⋁ i : T, φ` are the finite `Formula.iInf`
and `Formula.iSup` over a Lean type; their binder is a Lean variable, not an
object variable.

Atoms come in two forms, matching the two conventions of the library:

* `R(x, y)` applies a *relation symbol*, giving `Relations.formula₂ R
  (Term.var x) (Term.var y)`. Every arity is accepted: arity 1 and 2 go to
  Mathlib's `formula₁` and `formula₂`, and anything else to `Relations.formula`
  on a vector, which is what a hand-written arity-3 atom does anyway.
* `f⟨x, y⟩` applies a *formula builder*, one of the `α`-polymorphic
  abbreviations a problem file defines for its own atoms; it is plain function
  application.

`x ≐ y` is `Term.equal`, and `!e` escapes to an arbitrary Lean term – as a
whole formula, or (inside an atom's argument list) as a variable that the
macro should pass through untouched.

## Free variables

The variables a formula does *not* bind have to be declared, since the macro
must lift them under every block:

* `fo%[t, t'] φ` declares `t` and `t'` as variables of the ambient
  free-variable type. This is the shape of a builder such as
  `fun (t t' : α) => …`.
* `fo%⟨u, v⟩ φ` declares the *arguments* of an interpretation's defining
  formula, whose free-variable type is `Fin n × Fin dim`: `u` is the coordinate
  `(0, 0)`, `v` is `(1, 0)`, and `v[1]` is `(1, 1)`.

Both clauses may appear, the arguments first. An identifier that is neither
bound nor declared is an error rather than a silently captured Lean constant.

## What it does not do

The macro is source-level only: goals, `#print` and the documentation still
show the underlying `iAlls` term. Terms are out of scope, the library being
relational throughout.
-/

namespace DescriptiveComplexity

open Lean

/-- An object variable: a name bound by `fo%`, a coordinate of a declared
interpretation argument, or `!e` for a verbatim Lean term. -/
declare_syntax_cat fovar
syntax ident : fovar
syntax ident noWs "[" num "]" : fovar
syntax "!" term:max : fovar

/-- A first-order formula in surface syntax; see the module docstring. -/
declare_syntax_cat foform
syntax:max "(" foform ")" : foform
syntax:max "⊤ᶠ" : foform
syntax:max "⊥ᶠ" : foform
syntax:max ident noWs "(" fovar,* ")" : foform
syntax:max ident noWs "⟨" fovar,* "⟩" : foform
syntax:max "!" term:max : foform
syntax:max fovar " ≐ " fovar : foform
syntax:40 "¬ " foform:41 : foform
syntax:35 foform:36 " ∧ " foform:35 : foform
syntax:30 foform:31 " ∨ " foform:30 : foform
syntax:25 foform:26 " ↔ " foform:26 : foform
syntax:20 foform:21 " → " foform:20 : foform
syntax:max "⋀ " ident (" : " term)? ", " foform : foform
syntax:max "⋁ " ident (" : " term)? ", " foform : foform
syntax:max "∀ " ident+ ", " foform : foform
syntax:max "∃ " ident+ ", " foform : foform

/-- `fo%⟨u, v⟩[t, t'] φ` is the formula `φ`, written with named variables:
`u` and `v` name the arguments of an interpretation's defining formula, `t`
and `t'` the free variables of the ambient formula. See the module docstring. -/
syntax (name := foTerm) "fo%" ("⟨" ident,* "⟩")? ("[" ident,* "]")? foform : term

namespace FOSurface

/-- `Sum.inl` applied `d` times to `e`: the lift of a variable of an outer
block to the free-variable type of the `d`-th block inside it. -/
private def liftIn : Nat → Term → MacroM Term
  | 0, e => pure e
  | d + 1, e => do liftIn d (← `(Sum.inl $e))

/-- What the macro knows at a point of the formula: how many blocks are open,
which names they bound (with the depth at which each was bound and its index in
its block), which names are free variables of the ambient formula, and which
name the arguments of an interpretation. -/
private structure Env where
  /-- The number of quantifier blocks open at this point. -/
  depth : Nat
  /-- The bound names, each with its birth depth and its index in its block. -/
  vars : List (Name × Nat × Nat)
  /-- The declared free variables of the ambient formula. -/
  free : List Name
  /-- The declared arguments of an interpretation's defining formula. -/
  args : List Name

/-- Open one more block, binding `xs` in order. -/
private def Env.push (env : Env) (xs : Array Ident) : Env :=
  { env with
    depth := env.depth + 1,
    vars := env.vars ++ xs.toList.zipIdx.map fun (x, i) => (x.getId, env.depth, i) }

/-- Translate one occurrence of an object variable. -/
private def transVar (env : Env) (t : TSyntax `fovar) : MacroM Term := do
  if let `(fovar| !$e) := t then return e
  let coord : Nat := if let `(fovar| $_:ident[$j]) := t then j.getNat else 0
  unless t.raw[0].isIdent do Macro.throwErrorAt t "expected an object variable"
  let i : Name := t.raw[0].getId
  if let some k := env.args.idxOf? i then
    return ← liftIn env.depth
      (← `(($(Syntax.mkNumLit (toString k)), $(Syntax.mkNumLit (toString coord)))))
  match env.vars.reverse.find? (fun (p : Name × Nat × Nat) => p.1 == i) with
  | some (_, born, idx) =>
      liftIn (env.depth - born - 1) (← `(Sum.inr $(Syntax.mkNumLit (toString idx))))
  | none =>
      if env.free.contains i then
        liftIn env.depth (mkIdent i)
      else
        Macro.throwErrorAt t s!"'{i}' is not an object variable in scope: bind it, \
          or declare it in the ⟨…⟩ or […] clause of fo%"

/-- Translate a formula of the surface syntax to the term it abbreviates. -/
private partial def trans (env : Env) (stx : TSyntax `foform) : MacroM Term := do
  match stx with
  | `(foform| ($φ)) => trans env φ
  | `(foform| ⊤ᶠ) => `(Top.top)
  | `(foform| ⊥ᶠ) => `(Bot.bot)
  | `(foform| !$t) => pure t
  | `(foform| ¬ $φ) => do `(FirstOrder.Language.BoundedFormula.not $(← trans env φ))
  | `(foform| $φ ∧ $ψ) => do `($(← trans env φ) ⊓ $(← trans env ψ))
  | `(foform| $φ ∨ $ψ) => do `($(← trans env φ) ⊔ $(← trans env ψ))
  | `(foform| $φ → $ψ) => do `(($(← trans env φ)).imp $(← trans env ψ))
  | `(foform| $φ ↔ $ψ) => do `(($(← trans env φ)).iff $(← trans env ψ))
  | `(foform| $x:fovar ≐ $y:fovar) => do
      `(FirstOrder.Language.Term.equal
          (FirstOrder.Language.Term.var $(← transVar env x))
          (FirstOrder.Language.Term.var $(← transVar env y)))
  | `(foform| $r:ident($args,*)) => do
      let vs ← args.getElems.mapM (transVar env)
      let ts ← vs.mapM fun v => `(FirstOrder.Language.Term.var $v)
      match ts.size with
      | 1 => `(FirstOrder.Language.Relations.formula₁ $r $(ts[0]!))
      | 2 => `(FirstOrder.Language.Relations.formula₂ $r $(ts[0]!) $(ts[1]!))
      | _ => `(FirstOrder.Language.Relations.formula $r ![$ts,*])
  | `(foform| $f:ident⟨$args,*⟩) => do
      return Syntax.mkApp f (← args.getElems.mapM (transVar env))
  | `(foform| ⋀ $i $[: $t]?, $φ) => do
      `(FirstOrder.Language.Formula.iInf (fun $i $[: $t]? => $(← trans env φ)))
  | `(foform| ⋁ $i $[: $t]?, $φ) => do
      `(FirstOrder.Language.Formula.iSup (fun $i $[: $t]? => $(← trans env φ)))
  | `(foform| ∀ $xs*, $φ) => do
      let body ← trans (env.push xs) φ
      `(FirstOrder.Language.Formula.iAlls (Fin $(Syntax.mkNumLit (toString xs.size))) $body)
  | `(foform| ∃ $xs*, $φ) => do
      let body ← trans (env.push xs) φ
      `(FirstOrder.Language.Formula.iExs (Fin $(Syntax.mkNumLit (toString xs.size))) $body)
  | _ => Macro.throwErrorAt stx "unsupported first-order syntax"

/-- The names of an optional comma-separated declaration clause. -/
private def declared (o : Option (Syntax.TSepArray `ident ",")) : List Name :=
  match o with
  | some xs => xs.getElems.toList.map (·.getId)
  | none => []

end FOSurface

macro_rules
  | `(fo% $[⟨$as,*⟩]? $[[$fs,*]]? $φ) =>
      FOSurface.trans
        { depth := 0, vars := [], free := FOSurface.declared fs,
          args := FOSurface.declared as } φ

end DescriptiveComplexity
