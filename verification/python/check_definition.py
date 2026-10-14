"""Independent check in Python, written directly from Definition 2.1 of Sahbi (arXiv:2610.03785).

A set S is k-star-forming if for every vertex v outside S the induced subgraph G[S + v] contains a
copy of K_{1,k} containing v.  Such a copy has a centre c in S + v and k leaves adjacent to c in
S + v, and v is the centre or a leaf; so it exists exactly when some c in S + v with c = v or c
adjacent to v has at least k neighbours in S + v.  This file tests that condition literally, tests
minimality against every proper subset of size |S| - 1 (enough, since supersets of star-forming
sets are star-forming, which is also checked on G_3), and computes beta_k and SF_k exhaustively for

* G_3 (12 vertices) and G_4 (15 vertices), the graphs of the paper;
* the 10-vertex bipartite graph of the-omega-institute/trureturing pull request 14727 (k = 2).
"""
from itertools import combinations


def family(k):
    """The graph G_k of the paper as an adjacency dict."""
    m = k - 1
    V = [("h", i) for i in range(m)] + [("u", j) for j in range(m)] + [("w", j) for j in range(m)]
    V += ["x0", "p", "c1", "c2", "q1", "q2"]
    adj = {v: set() for v in V}

    def edge(a, b):
        adj[a].add(b)
        adj[b].add(a)

    for i in range(m):
        edge(("h", i), "x0")
        for j in range(m):
            edge(("h", i), ("u", j))
            edge(("h", i), ("w", j))
    edge("x0", "p")
    for j in range(m):
        edge("c1", ("u", j))
        edge("c2", ("w", j))
    edge("c1", "q1")
    edge("c2", "q2")
    return adj


def openrefute_graph():
    rows = ["11001", "11010", "00011", "01111", "10111"]
    adj = {("a", i): set() for i in range(5)}
    adj.update({("b", j): set() for j in range(5)})
    for i, r in enumerate(rows):
        for j, c in enumerate(r):
            if c == "1":
                adj[("a", i)].add(("b", j))
                adj[("b", j)].add(("a", i))
    return adj


def star_containing(adj, k, T, v):
    """Is there a copy of K_{1,k} in G[T] that contains v?"""
    for c in T:
        if c != v and v not in adj[c]:
            continue
        if len(adj[c] & T) >= k:
            return True
    return False


def star_forming(adj, k, S):
    return all(star_containing(adj, k, S | {v}, v) for v in adj if v not in S)


def minimal_star_forming(adj, k, S):
    return star_forming(adj, k, S) and not any(star_forming(adj, k, S - {s}) for s in S)


def k_independent(adj, k, I):
    return all(len(adj[v] & I) < k for v in I)


def beta(adj, k):
    V = list(adj)
    for r in range(len(V), -1, -1):
        for I in combinations(V, r):
            if k_independent(adj, k, set(I)):
                return r
    return 0


def upper_sf(adj, k):
    V = list(adj)
    for r in range(len(V), -1, -1):
        for S in combinations(V, r):
            if minimal_star_forming(adj, k, set(S)):
                return r
    return 0


def check_upward_closed(adj, k):
    """Supersets of star-forming sets are star-forming (all subsets, all one-point extensions)."""
    V = list(adj)
    for r in range(len(V) + 1):
        for S in combinations(V, r):
            S = set(S)
            if star_forming(adj, k, S):
                for v in V:
                    if v not in S and not star_forming(adj, k, S | {v}):
                        return False
    return True


def main():
    ok = True
    for k in (3, 4):
        adj = family(k)
        n = len(adj)
        edges = sum(len(a) for a in adj.values()) // 2
        S = set(adj) - {"p", "q1", "q2"}
        b, sfk = beta(adj, k), upper_sf(adj, k)
        line = (f"G_{k}: n={n} (3k+3={3*k+3}) edges={edges} (2k^2-k+2={2*k*k-k+2}) "
                f"beta_{k}={b} (2k+2={2*k+2}) SF_{k}={sfk} |S|={len(S)} S minimal: "
                f"{minimal_star_forming(adj, k, S)}")
        print(line)
        ok &= (n == 3 * k + 3 and edges == 2 * k * k - k + 2 and b == 2 * k + 2 and sfk == 3 * k
               and len(S) == 3 * k and minimal_star_forming(adj, k, S))
    adj = family(3)
    up = check_upward_closed(adj, 3)
    print(f"G_3: star-forming sets are closed upwards: {up}")
    ok &= up
    adj = openrefute_graph()
    b, sfk = beta(adj, 2), upper_sf(adj, 2)
    print(f"trureturing PR 14727 graph: n=10 beta_2={b} SF_2={sfk}")
    ok &= (b, sfk) == (5, 6)
    print("all checks passed" if ok else "CHECK FAILED")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
