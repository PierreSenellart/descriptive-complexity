/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Numbers.Unary
import FOReduction.Numbers.Binary

/-!
# Number encodings

Umbrella file for the shared number-representation layer: unary encoding by
cardinalities of marked sets (`FOReduction.Numbers.Unary`, for problems whose
numbers are polynomially bounded) and binary encoding by bit positions
(`FOReduction.Numbers.Binary`, for problems whose numbers must be
exponential). See the design discussion in the repository notes: the two are
complements, chosen per problem.
-/
