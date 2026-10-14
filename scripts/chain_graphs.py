"""Prints, in graph6 format, every chain graph on exactly n vertices without isolated vertices.

A chain graph has parts A = {a_1, ..., a_p} and B = {b_1, ..., b_q} with N(a_i) = {b_1, ..., b_{d_i}}
for q = d_1 >= d_2 >= ... >= d_p >= 1, so it is given by a partition fitting in a p x q box whose
first part is q.  Every such graph is printed once for each pair (p, q) with p + q = n; isomorphic
copies (from p <-> q symmetry) are harmless for the search.

    usage: python3 chain_graphs.py n
"""
import sys


def graph6(n, edges):
    bits = []
    adj = {(min(a, b), max(a, b)) for a, b in edges}
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in adj else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for t in range(0, len(bits), 6):
        v = 0
        for b in bits[t:t + 6]:
            v = 2 * v + b
        out += chr(v + 63)
    return out


def partitions(p, top):
    if p == 0:
        yield []
        return
    for d in range(top, 0, -1):
        for rest in partitions(p - 1, d):
            yield [d] + rest


def main():
    n = int(sys.argv[1])
    for p in range(1, n):
        q = n - p
        for degs in partitions(p - 1, q):
            degs = [q] + degs
            edges = [(i, p + j) for i, d in enumerate(degs) for j in range(d)]
            print(graph6(n, edges))


if __name__ == "__main__":
    main()
