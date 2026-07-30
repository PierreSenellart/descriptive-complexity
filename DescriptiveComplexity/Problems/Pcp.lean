/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Pcp.Defs
import DescriptiveComplexity.Problems.Pcp.Membership
import DescriptiveComplexity.Problems.Pcp.Hardness

/-!
# PCP: Post's correspondence problem

The umbrella of the `PCP` files. The instance is a marked list of domino pairs
over an alphabet, ordered by the order of the positions of its own words, and
the yes-instances are those with a **match**: a nonempty sequence of marked
dominoes whose top words and whose bottom words have the same concatenation
(`DescriptiveComplexity.PCP`, in `DescriptiveComplexity.Problems.Pcp.Defs`).

What is proved:

* `DescriptiveComplexity.pcp_mem_RE` – the match is *invented*, as a segment of
  slots carrying one domino each, together with a **matching between the two
  parses** of the word the sequence spells
  (`DescriptiveComplexity.Problems.Pcp.Cert` for the mathematics,
  `DescriptiveComplexity.Problems.Pcp.Membership` for the syntax);
* `DescriptiveComplexity.pcp_le_finsat` – whence Post's problem reduces to
  finite satisfiability, `DescriptiveComplexity.FINSAT` being RE-hard;
* `DescriptiveComplexity.halt_ordered_fo_reduction_pcp` – RE-*hardness*, the
  computation-history dominoes for the machine drawn in the instance
  (`DescriptiveComplexity.Problems.Pcp.Hardness`); whence
  `DescriptiveComplexity.pcp_RE_complete` and the undecidability of Post's
  problem, `DescriptiveComplexity.pcp_not_computable`
  (`DescriptiveComplexity.Computability.PcpComplete`).

The common word is never written down. Its letters are indexed, on the top
side, by the pairs (slot, position of the top word sitting there) in
lexicographic order, and on the bottom side by its own parse; a relation
variable matches the two, and a first-order kernel checks only that the
matching lands in the two parses, is defined everywhere on both, reflects the
two orders, and preserves letters. That is enough
(`DescriptiveComplexity.Pcp.forall₂_of_matching`), because a relation between
the members of two strictly sorted lists with those properties pairs their
entries index by index.

RE-*hardness* could not be a translation of the logic: `PCP` is not the
syntactic image of any logic – a certificate of `∃SO[new]` is a structure with
relations, a certificate of `PCP` is a string with two parses – so the
reduction is the classical computation-history construction, one decorated
domino per transition-attribute tuple of the machine the `HALT` instance
carries as elements.
-/
