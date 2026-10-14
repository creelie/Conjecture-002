# Priority check

Done on 14 October 2026, 02:10–02:40 UTC for the counterexamples and 03:00–03:05 UTC for chain
graphs, before the results were written up.

**Question.** R. Sahbi, *Upper k-star-forming sets, k-independence, and upper domination*,
[arXiv:2610.03785](https://arxiv.org/abs/2610.03785) (v1 30 September 2026, v2 6 October 2026):
Conjecture 4.1 (β_k = SF_k for every bipartite graph and every k), Conjecture 6.4 and Problem 9.1
(β_k = SF_k for every chain graph and every k ≥ 3; Sahbi proved k = 2), Problem 7.3 (β_3 = SF_3 for
every triangle-free graph?) and Problem 9.4 (for which k does equality hold throughout natural
triangle-free classes?).

**What was already known.**

- Conjectures 4.1, 4.2 and 7.2 were refuted **for k = 2 only** by a 10-vertex bipartite graph with
  β_2 = 5 and SF_2 = 6: [the-omega-institute/trureturing pull request 14727](https://github.com/the-omega-institute/trureturing/pull/14727)
  (opened and merged 9 October 2026; preregistration issue 14706). Its graph is checked in
  `verification/python/check_definition.py` and is isomorphic to the unique 10-vertex bipartite
  example found by our own search (`data/search/bipartite-10.txt`). The pull request says nothing
  about k ≥ 3, chain graphs, Problem 7.3 or Problem 9.4; it mentions that the grid Conjecture 8.4 holds on the grids
  it tested.
- Sahbi's own Proposition 7.1 is a triangle-free graph that is not bipartite, with β_4 < SF_4.

**Where we looked for k ≥ 3, chain graphs, Problem 7.3 and Problem 9.4.**

| Source | Query | Result |
|---|---|---|
| OpenRefute (github.com/the-omega-institute/trureturing) | issues and pull requests mentioning `2610.03785` and `star-forming` | only #14706 and #14727 (k = 2) |
| arXiv | abstract page and versions of 2610.03785; full-text search "star-forming sets" | v2 is the latest; no other paper on k-star-forming sets |
| Zenodo | "star-forming" with dissociation / Sahbi / k-independence; "2610.03785" | nothing relevant |
| zbMATH | title "star-forming" | Chellali–Favaron, J. Combin. Math. Combin. Comput. 68 (2009) 205–214, Zbl 1176.05052, which introduces SF_k, proves β_k ≤ SF_k and studies trees, chordal graphs and K_{1,r}-free graphs |
| Web search | the paper's terms with "counterexample", "β_3", "triangle-free" | only the paper and the OpenRefute items |
| OpenRefute, rechecked 03:00 UTC | issues and pull requests mentioning `2610.03785` | still only #14706 and #14727, neither about chain graphs |
| arXiv abstract page, rechecked 03:00 UTC | 2610.03785 | still v2 (6 October 2026); the abstract keeps the chain-graph case open for k ≥ 3 |
| Web search, 03:00 UTC | "star-forming" with "chain graph", k-independence, Sahbi | nothing on k-star-forming sets in chain graphs |

The full text of Chellali–Favaron (2009) was not available to us; its zbMATH summary does not mention
bipartite graphs, and Sahbi, who cites it, poses the bipartite equality as open.

**Conclusion.** As of 14 October 2026 no counterexample for k ≥ 3, no answer to Problem 7.3 and no
proof of Conjecture 6.4 for k ≥ 3 was found in any of these sources.
