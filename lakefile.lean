import Lake
open Lake DSL

package "descriptive-complexity" where
  version := v!"0.1.0"
  description := "Descriptive complexity in Lean 4: machine-model-free NP-completeness via first-order reductions, and the polynomial hierarchy via second-order alternation"
  keywords := #["complexity", "descriptive complexity", "model theory",
    "NP-completeness", "reductions"]
  homepage := "https://pierresenellart.github.io/descriptive-complexity/DescriptiveComplexity.html"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.33.0-rc1"

@[default_target]
lean_lib «DescriptiveComplexity» where
  -- add any library configuration options here
