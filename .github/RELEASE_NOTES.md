Two answers to questions of R. Sahbi, *Upper k-star-forming sets, k-independence, and upper
domination* (arXiv:2610.03785).

- Conjecture 4.1 fails for every k ≥ 3, and the answer to Problem 7.3 is no: for every k ≥ 3 the
  connected bipartite graph G_k on 3k + 3 vertices has k-independence number 2k + 2 and a minimal
  k-star-forming set of size 3k. The case k = 2 was settled earlier by a 10-vertex example
  (the-omega-institute/trureturing, pull request 14727).
- Conjecture 6.4 (Problem 9.1) holds: β_k = SF_k on every chain graph for every k ≥ 2.

Attached: the paper (PDF), its LaTeX source with the figure as PNG, and the arXiv tarball. The
repository contains the Lean 4 proofs with Mathlib (eighteen theorems audited, standard axioms only),
the C and Python checks, the exhaustive searches, and the dated priority check.

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).
