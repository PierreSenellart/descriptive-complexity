# Contributing to DescriptiveComplexity

Thank you for your interest in contributing to DescriptiveComplexity!

## Reporting bugs and requesting features

Please use the [GitHub issue
tracker](https://github.com/PierreSenellart/descriptive-complexity/issues).
A “bug” here is usually one of: a definition that does not say what it claims
to say, a theorem statement that is vacuous or weaker than its name suggests,
a proof that leans on an unintended hypothesis, or a build failure. Since the
kernel checks every proof, there are no runtime bugs to report – but there is
plenty of room for a formalization to be *correct and yet wrong*, and those
reports are the most valuable ones.

If you would like to formalize a new problem or class, please open an issue
first: [ROADMAP.md](ROADMAP.md) records what is planned and in which order, and
the answer may be that the machinery you would need is already half-built.

## Development setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (which installs
the Lean toolchain named in `lean-toolchain`) and `git`. Nothing else: Mathlib
is fetched by Lake.

```sh
lake exe cache get   # download Mathlib's build cache – do not skip this
lake build           # build the library
```

`lake exe cache get` is what makes the build minutes rather than hours; without
it, Lake compiles all of Mathlib from source. The library tracks one Mathlib
release at a time, so use the toolchain in `lean-toolchain` rather than your
system default; elan does this automatically inside the repository.

## Building is the test suite

There is no separate test target, and that is deliberate: every theorem in the
library is checked by the Lean kernel at build time, so a green `lake build`
*is* the regression suite. Two additional properties are expected of every
contribution, and both are cheap to check:

**Warning-free.** The Mathlib standard linter set is enabled in
`lakefile.lean`, so `lake build` reports style and hygiene problems as
warnings. A contribution should add none.

**Axiom-clean.** The library declares no axioms of its own and depends on no
classical extras beyond Lean's own. Check any theorem you add or touch:

```lean
#print axioms my_new_theorem
-- expected, and nothing else:
-- 'my_new_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A fourth axiom in that list means something has gone wrong – most often a
`sorry` left in a dependency.

## Code organization

The library is in three layers, described in full in the
[`DescriptiveComplexity` module
docstring](https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html),
which is the authoritative map:

1. **Framework** – `Interpretation.lean` (decision problems as
   isomorphism-invariant properties of finite structures, first-order
   interpretations, reductions), `Ordered.lean` and `Relativized.lean` for the
   ordered and definable-domain variants, and their `Composition` files, which
   give transitivity.
2. **Complexity layer** – `Complexity.lean` (complexity classes, membership,
   hardness, completeness, closed under reductions by construction) and
   `Hierarchy.lean` (the polynomial hierarchy), over the definability notions
   built in the `SecondOrder*` and `FixedPoint*` files.
3. **Problem catalog** – `DescriptiveComplexity/Problems/`, one problem per
   file, growing into a directory when its reductions get heavy;
   `DescriptiveComplexity/Examples/` holds tutorial-style walkthroughs, read
   top to bottom.

Reduction machinery reusable across problems lives at the top level rather than
inside a problem directory. Before writing a gadget, check whether one exists:
number encodings, occurrence orders, walks along a finite linear order, padding,
and the standard certificate shapes (acyclicity, connectivity, tours) are all
already there, and reusing them is much less work than rediscovering them.

## Adding a problem

Every problem in the catalog follows the same arc, walked end to end by
`Examples/ConjunctiveQueries.lean`:

1. **Vocabulary** – a `Language` for the instances; reuse an existing one where
   possible.
2. **Semantics** – the yes-instance predicate, as a Lean predicate on the
   structure.
3. **Invariance** – the proof that it is isomorphism-invariant, via the shared
   transport lemmas.
4. **Membership** – a definability witness for the class in question.
5. **Hardness** – a first-order interpretation from a problem already known to
   be hard, plus its correctness proof.
6. **Completeness** – the theorem conjoining membership and hardness.

A first-order reduction is *stronger* than a polynomial-time one, so a textbook
Karp reduction is not automatically usable: it has to be expressible without
counting or iteration. Whether a reduction can avoid an order on the universe,
and how a numeric threshold can be encoded at all, are the two design questions
that decide whether a problem is cheap or expensive to add. If either looks
doubtful, an issue before the work will save you time.

## Conventions

**Docstrings.** Mathlib style: a module docstring (`/-! # … -/`) on every file
and a `/-- … -/` docstring on every public declaration. This library is read
through its generated API documentation, so a declaration without a docstring
is effectively undocumented.

**Names.** Completeness results and their parts are named systematically:
`foo_NP_complete`, `foo_mem_NP`, `foo_NP_hard`, interpretations are `fooInterp`,
and a reduction term reads `source_fo_reduction_target` (with
`source_ordered_fo_reduction_target` for the ordered variant). Follow the
pattern of the nearest existing problem.

**Notation.** The scoped notations are `P ≤ᶠᵒ Q` for a first-order reduction,
`P ≤ᶠᵒ[≤] Q` for an ordered one, `P ≤ʳᶠᵒ[≤] Q` for a relativized one, and
`P ∈ C` for membership. Hierarchy levels are the definitions `SigmaP k` and
`PiP k`, with `NP`, `coNP`, `PTIME` and `PH` as abbreviations; `Σₖᵖ` and `Πₖᵖ`
are prose spellings for docstrings, not notation.

**Citations.** References are cited as `[Author Year][key]` against
`docbuild/docs/references.bib`; add an entry there when you cite something new.

**Two doc surfaces stay in sync.** When a problem becomes complete for a class,
it is added both to the table in [README.md](README.md) and to the catalog in
the `DescriptiveComplexity` module docstring. A completeness result that
appears in neither is invisible.

## Submitting a pull request

1. Fork the repository and create a branch from `master`.
2. Make your change, keeping the build green, warning-free and axiom-clean.
3. Add or update the docstrings, and both doc surfaces above if you completed a
   problem.
4. Open a pull request against `master`, describing what is proved and how it
   relates to what is already there. If your reduction departs from the usual
   recipe, say why in the description – that is the part a reviewer cannot
   reconstruct from the code.
5. Do **not** bump the package version, `CITATION.cff`, or the README
   compatibility table: releases are cut by the maintainer with
   `scripts/release.sh`, which updates all of them together.

CI must pass: the `Build` job compiles the library, and the `Release metadata`
job checks that the version and Mathlib pin agree across every file that
records them.

## License

By contributing, you agree that your contributions will be licensed under the
[Apache License 2.0](LICENSE).
