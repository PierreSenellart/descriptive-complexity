import Lake
open Lake DSL

package "descriptive-complexity" where
  version := v!"1.4.0"
  description := "Descriptive complexity in Lean 4: machine-model-free NP-completeness via first-order reductions, and the polynomial hierarchy via second-order alternation"
  keywords := #["complexity", "descriptive complexity", "model theory",
    "NP-completeness", "reductions"]
  homepage := "https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    -- Implementation modules of this library have no public declaration: their siblings
    -- reach them with `import all`, which is the design, not an omission.
    ⟨`weak.linter.privateModule, false⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib «DescriptiveComplexity» where
  -- add any library configuration options here
