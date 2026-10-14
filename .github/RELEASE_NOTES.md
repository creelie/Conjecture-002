Three answers to questions of R. Sahbi, *Upper k-star-forming sets, k-independence, and upper
domination* (arXiv:2610.03785v2; the preprint was withdrawn by its author on 12 October 2026).

- Conjecture 4.1 fails for every k ≥ 3, and the answer to Problem 7.3 is no: for every k ≥ 3 the
  connected bipartite graph G_k on 3k + 3 vertices has k-independence number 2k + 2 and a minimal
  k-star-forming set of size 3k. The case k = 2 was settled earlier by a 10-vertex example
  (the-omega-institute/trureturing, pull request 14727).
- Conjecture 6.4 (Problem 9.1) holds: β_k = SF_k on every chain graph for every k ≥ 2.
- New in v1.1.0, Problem 9.3: deciding whether a bipartite graph has a minimal 2-star-forming set
  with at least t vertices is NP-complete, also on planar bipartite graphs. For every graph H the
  bipartite graph H# (each edge replaced by a path of length four, a pendant vertex at each vertex)
  has β_2(H#) = SF_2(H#) = n + 2m + α(H), which reduces Independent Set to the problem.

Attached: the paper (PDF), its LaTeX source with the figures as PNG, and the arXiv tarball. The
repository contains the Lean 4 proofs with Mathlib (twenty-six theorems audited, standard axioms
only; the NP-completeness argument itself is on paper), the C, Python and SAT checks, the exhaustive
searches, and the dated priority check.

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).
