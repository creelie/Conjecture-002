"""Check beta_2(H#) = SF_2(H#) = n + 2m + alpha(H) (Theorem 1.4 of the paper) with a SAT solver.

Reads graphs H in graph6 format on standard input.  H# replaces every edge uv (u < v) of H by the
path u a b c v and attaches a pendant vertex v' to every vertex v.  beta_2(H#) and SF_2(H#) are
computed independently of sharpcheck.c and of the Lean proof:

* a set S is 2-star-forming if every vertex w outside S has two neighbours in S, or a neighbour u
  in S together with a neighbour of u other than w in S (Lemma 2.1 with k = 2); so w is covered
  exactly when one of its "covering pairs" lies inside S;
* S is minimal if for every s in S some vertex w (w = s, or w outside S) is not covered by S - s;
* both numbers are maximised by asking for at least t chosen vertices with t increasing until the
  formula becomes unsatisfiable.

alpha(H) is computed by brute force.  One line per graph (graph6 n m alpha beta2 SF2) and a last
line with the number of graphs and failures.  Needs python-sat (pip install python-sat).

    usage: nauty-geng -c 7 | python3 -I check_sharp_sat.py
"""
import sys
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def parse_graph6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    edges, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def sharp(n, edges):
    """Adjacency lists of H#: v, then v' = n + v, then a, b, c = 2n + 3e + 0, 1, 2."""
    nv = 2 * n + 3 * len(edges)
    N = [set() for _ in range(nv)]

    def edge(x, y):
        N[x].add(y)
        N[y].add(x)

    for v in range(n):
        edge(v, n + v)
    for e, (u, v) in enumerate(edges):
        a, b, c = 2 * n + 3 * e, 2 * n + 3 * e + 1, 2 * n + 3 * e + 2
        edge(u, a)
        edge(a, b)
        edge(b, c)
        edge(c, v)
    return [sorted(x) for x in N]


def alpha(n, edges):
    best = 0
    for mask in range(1 << n):
        size = bin(mask).count("1")
        if size > best and all(not (mask >> u & 1 and mask >> v & 1) for u, v in edges):
            best = size
    return best


def covering_pairs(N, w):
    pairs = {frozenset(p) for p in combinations(N[w], 2)}
    for u in N[w]:
        pairs.update(frozenset((u, z)) for z in N[u] if z != w)
    return pairs


def sf2_formula(N):
    nv = len(N)
    pool = IDPool(start_from=nv + 1)
    cnf = CNF()
    var = {}

    def pair(p):  # a variable equivalent to "both vertices of p lie in S"
        if p not in var:
            a, b = tuple(p)
            y = pool.id(("pair", a, b))
            cnf.extend([[-y, a + 1], [-y, b + 1], [y, -(a + 1), -(b + 1)]])
            var[p] = y
        return var[p]

    CP = [covering_pairs(N, w) for w in range(nv)]
    for w in range(nv):  # S is 2-star-forming
        cnf.append([w + 1] + [pair(p) for p in CP[w]])
    for s in range(nv):  # S - s is not 2-star-forming, for each s in S
        near = {s} | set(N[s]) | {z for u in N[s] for z in N[u]}
        witnesses = []
        for w in sorted(near):
            keep = [p for p in CP[w] if s not in p]
            if w != s and len(keep) == len(CP[w]):
                continue  # deleting s does not change whether w is covered
            c = pool.id(("uncovered", s, w))
            witnesses.append(c)
            if w != s:
                cnf.append([-c, -(w + 1)])
            cnf.extend([[-c, -pair(p)] for p in keep])
        cnf.append([-(s + 1)] + witnesses)
    return cnf, pool


def beta2_formula(N):
    cnf = CNF()
    for v in range(len(N)):
        for a, b in combinations(N[v], 2):
            cnf.append([-(v + 1), -(a + 1), -(b + 1)])
    return cnf, IDPool(start_from=len(N) + 1)


def maximum(nv, cnf, pool):
    best, t = 0, 1
    while t <= nv:
        card = CardEnc.atleast(lits=list(range(1, nv + 1)), bound=t, vpool=pool,
                               encoding=EncType.seqcounter)
        with Solver(name="cadical153", bootstrap_with=cnf.clauses + card.clauses) as solver:
            if not solver.solve():
                break
            model = solver.get_model()
            best = sum(1 for v in range(nv) if model[v] > 0)
            t = best + 1
    return best


def main():
    graphs = bad = 0
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith(">"):
            continue
        n, edges = parse_graph6(line)
        N = sharp(n, edges)
        a = alpha(n, edges)
        b2 = maximum(len(N), *beta2_formula(N))
        sf2 = maximum(len(N), *sf2_formula(N))
        want = n + 2 * len(edges) + a
        ok = b2 == want and sf2 == want
        graphs += 1
        bad += not ok
        print(line, n, len(edges), a, b2, sf2, *([] if ok else ["FAIL"]), flush=True)
    print("graphs", graphs, "failures", bad, flush=True)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
