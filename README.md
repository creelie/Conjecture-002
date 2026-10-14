# Upper k-star-forming sets and k-independence in bipartite graphs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23356026.svg)](https://doi.org/10.5281/zenodo.23356026)

Release v1.0.0: [doi:10.5281/zenodo.23356026](https://doi.org/10.5281/zenodo.23356026) (all versions: [doi:10.5281/zenodo.23356025](https://doi.org/10.5281/zenodo.23356025)).

R. Sahbi, *Upper k-star-forming sets, k-independence, and upper domination*,
[arXiv:2610.03785](https://arxiv.org/abs/2610.03785), conjectured (Conjecture 4.1) that the
k-independence number β_k and the upper k-star-forming number SF_k agree on every bipartite graph and
every k, the case k = 1 being the theorem Γ = α of Cockayne, Favaron, Payan and Thomason. He also asked
(Problem 7.3) whether β_3 = SF_3 on every triangle-free graph. The case k = 2 was refuted by a
10-vertex bipartite graph in
[the-omega-institute/trureturing pull request 14727](https://github.com/the-omega-institute/trureturing/pull/14727).

This repository answers both questions and proves his chain-graph conjecture.

**Conjecture 4.1 fails for every k ≥ 3 as well, and the answer to Problem 7.3 is no.** For every
k ≥ 2 the connected bipartite graph G_k on 3k + 3 vertices below has β_k(G_k) = 2k + 2 and a
minimal k-star-forming set of size 3k, so SF_k(G_k) − β_k(G_k) ≥ k − 2. Together with the k = 2
example, β_k = SF_k holds on all bipartite graphs only for k = 1, which answers Problem 9.4 of the
paper for the class of bipartite graphs.

**Conjecture 6.4 holds: β_k = SF_k on every chain graph for every k ≥ 2** (Sahbi proved k = 2 and
posed k ≥ 3 as Problem 9.1). A chain graph is a bipartite graph in which the neighbourhoods of the
vertices on one side are nested. In a minimal k-star-forming set S of a chain graph at most one vertex
has k or more neighbours in S, and that vertex can be exchanged for a vertex outside S to give a
k-independent set of the same size.

Definitions (Chellali and Favaron, J. Combin. Math. Combin. Comput. 68 (2009) 205–214): I is
*k-independent* if G[I] has maximum degree less than k; S is *k-star-forming* if every vertex v ∉ S
lies in a copy of K_{1,k} inside G[S ∪ {v}]; β_k is the largest k-independent set and SF_k the largest
minimal k-star-forming set.

| | |
|---|---|
| vertices | hubs h_1, …, h_{k−1}; X_1 = {u_1, …, u_{k−1}}; X_2 = {w_1, …, w_{k−1}}; x_0, p, c_1, c_2, q_1, q_2 |
| edges | every hub to every vertex of X = X_1 ∪ X_2 ∪ {x_0}; x_0p; c_1 to X_1 and q_1; c_2 to X_2 and q_2 (2k² − k + 2 edges) |
| bipartition | {h_i, p, c_1, c_2} and X ∪ {q_1, q_2} |
| S = V ∖ {p, q_1, q_2} | minimal k-star-forming, \|S\| = 3k: the pendant vertices p, q_1, q_2 hang on x_0, c_1, c_2, each of which has exactly k − 1 neighbours in S, and deleting any vertex of S strands one of them |
| I_0 = X ∪ {p, q_1, q_2} | a largest k-independent set, \|I_0\| = 2k + 2 |
| G_3 (12 vertices, graph6 `K???C@oBfW\_`) | β_3 = 8 < 9 = SF_3 |

The proof of β_k ≤ 2k + 2 splits on t = |I ∩ H|: with no hub, G_k − H is an edge and two copies of
K_{1,k}; with 1 ≤ t ≤ k − 2 hubs, I meets X in at most k − 1 vertices; with all k − 1 hubs, every
vertex of I ∩ X forces its neighbour among p, c_1, c_2 out of I.

| k | vertices | edges | β_k | SF_k | SF_k − β_k |
|---|---|---|---|---|---|
| 2 | 9 | 8 | 6 | 6 | 0 |
| 3 | 12 | 17 | 8 | 9 | 1 |
| 4 | 15 | 30 | 10 | 12 | 2 |
| 5 | 18 | 47 | 12 | 15 | 3 |
| 6 | 21 | 68 | 14 | 18 | 4 |
| 7 | 24 | 93 | 16 | 21 | 5 |

The SF_k column is computed exactly over all subsets (`data/family_values.txt`); the theorem itself
only uses SF_k ≥ 3k.

## What is proved, and how

The paper (`preprint/main.tex`, built into `dist/`) proves everything by hand. The Lean 4 proofs with
Mathlib (v4.34.1) take the definitions literally from Sahbi's paper (a star K_{1,k} through v inside
G[S ∪ {v}], minimality against every proper subset, and β_k, SF_k as the largest sizes):

```lean
theorem betaK_family (k : ℕ) (hk : 3 ≤ k) :
    (G (k - 1)).Colorable 2 ∧ betaK (G (k - 1)) k = 2 * k + 2 ∧ 3 * k ≤ sfK (G (k - 1)) k

theorem sfK_eq_betaK_of_isChain [Fintype V] (hG : IsChain G side) (hk : 2 ≤ k) :
    sfK G k = betaK G k
```

Here `IsChain G side` says that every edge joins the two sides given by `side : V → Bool` and that
the neighbourhoods of the vertices on the side `false` are nested.

| Statement | Lean theorem |
|---|---|
| β_k < SF_k on a bipartite graph, every k ≥ 3 | `StarForming.betaK_lt_sfK`, `StarForming.sf_gt_beta` |
| β_k(G_k) = 2k + 2 and SF_k(G_k) ≥ 3k | `StarForming.betaK_family` |
| all of Lemmas 3.1 and 3.2 at once | `StarForming.main` |
| G_k is bipartite | `StarForming.colorable_two` |
| S is minimal k-star-forming, \|S\| = 3k | `StarForming.isMinimalStarForming_S0`, `StarForming.card_S0` |
| every k-independent set has at most 2k + 2 vertices | `StarForming.kIndep_card_le` |
| I_0 is k-independent with 2k + 2 vertices | `StarForming.kIndep_I0`, `StarForming.card_I0` |
| G_k has 3k + 3 vertices | `StarForming.card_W` |
| minimality reduces to one-point deletions | `StarForming.isMinimalStarForming_of_erase` |
| SF_k = β_k on chain graphs, every k ≥ 2 (Theorem 1.3) | `StarForming.sfK_eq_betaK_of_isChain` |
| Lemma 4.1 (exchange, any graph) | `StarForming.exists_kIndep_of_unique_high` |
| Lemma 4.2 | `StarForming.deg_add_two_le` |
| Lemma 4.3 | `StarForming.eq_of_high` |
| nested neighbourhoods on both sides | `StarForming.IsChain.nested` |
| β_k ≤ SF_k (Chellali–Favaron) | `StarForming.betaK_le_sfK`, `StarForming.isMinimalStarForming_of_maximal` |
| Lemma 2.1 (local form of the definition) | `StarForming.starAt_iff_covered` |

`lean/Check.lean` prints the axioms of eighteen theorems and `scripts/audit_axioms.py` checks that
only `propext`, `Classical.choice` and `Quot.sound` occur (`verification/axioms.txt`).

Independent checks outside Lean (`scripts/run_all.sh`):

- `verification/c/sfcheck.c`: builds G_k for 2 ≤ k ≤ 7, computes β_k and SF_k exactly over all
  subsets and checks that S is a minimal k-star-forming set (`data/family_values.txt`).
- `verification/python/check_definition.py`: implements Definition 2.1 of the paper literally (stars
  through v in G[S ∪ {v}], minimality against all subsets), recomputes G_3 and G_4, checks that
  k-star-forming sets are closed upward, and checks the k = 2 example of pull request 14727.
- `verification/c/chainlemmas.c`: checks Lemmas 4.1–4.3 on every minimal k-star-forming set of every
  chain graph with at most 12 vertices, 2 ≤ k ≤ 7 (`data/chain_lemmas.txt`).
- `scripts/searches.sh`: exhaustive searches with nauty, below.

## Searches

`verification/c/sfsearch.c` computes β_k and SF_k of every graph it reads. Outputs are in
`data/search/`; each lists the graphs with β_k ≠ SF_k (graph6, both values, a largest minimal
k-star-forming set as a bit mask) and the number of graphs read. These computations are not part of the
proof.

| Class | Range | Graphs with β_k ≠ SF_k |
|---|---|---|
| bipartite, 2 ≤ k ≤ 7 | up to 12 vertices | smallest: 10 vertices for k = 2 (only the graph of pull request 14727), 12 for k = 3 (51 graphs, G_3 among them), 10 for k = 4 (one graph), 12 for k = 5; none for k = 6, 7 |
| triangle-free, k = 3 | up to 11 vertices | smallest: 10 vertices (two graphs) |
| chain graphs, 3 ≤ k ≤ 8 | up to 16 vertices | none, as Theorem 1.3 says |
| trees, 2 ≤ k ≤ 6 | up to 16 vertices | none |

## Layout

```
lean/                          Lean 4 + Mathlib (v4.34.1)
  StarForming/Basic.lean       k-independence, stars, k-star-forming and minimal k-star-forming sets
  StarForming/Local.lean       Lemma 2.1, β_k and SF_k, β_k ≤ SF_k, the exchange Lemma 4.1
  StarForming/Family.lean      the graphs G_k
  StarForming/Chain.lean       chain graphs: Lemmas 4.2, 4.3 and Theorem 1.3
  StarForming/Summary.lean     both answers stated with β_k and SF_k
  Check.lean                   axiom audit
verification/c/                sfcheck.c, sfsearch.c, chainlemmas.c
verification/python/           check_definition.py
verification/axioms.txt        output of Check.lean
data/                          family_values.txt, chain_lemmas.txt, search/
preprint/                      the paper (amsart) and its TikZ figure
dist/                          the paper as PDF, as LaTeX with a PNG figure, and as an arXiv tarball
scripts/                       run_all.sh, searches.sh, chain_graphs.py, build_paper.sh, audit_axioms.py
PRIORITY-CHECK.md              the dated check that the question was still open
```

To reproduce: `scripts/run_all.sh` (C compiler, Python 3, nauty), `scripts/searches.sh full` for the
12- and 16-vertex searches, `cd lean && lake exe cache get && lake build && lake env lean Check.lean`,
and `scripts/build_paper.sh` (TeX Live). The workflow `.github/workflows/verify.yml` runs the checks,
the Lean build with the audit, and the paper build on every pull request.

## Author

Deep Bhattacharjee, formerly Electro-Gravitational Space Propulsion Laboratory (EGSPL),
Bhubaneswar, Odisha 751030, India. d.bhattacharjee@erl-forschung.de, itsdeep@live.com,
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).

The k = 2 counterexample is due to the author of pull request 14727 and is only checked here. The
author used Claude (Anthropic) to find the construction by computer search, to check it in C, Python
and Lean, to find and formalise the proof for chain graphs, and to draft the text; the author verified every step and is responsible for the content.

MIT License.
