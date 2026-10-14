/* chainlemmas.c -- checks the lemmas of Section 4 on every chain graph without isolated vertices on at
 * most N vertices, for one k.
 *
 *   usage: chainlemmas N k
 *
 * A chain graph with parts A = {a_1..a_p}, B = {b_1..b_q} is given by degrees q = d_1 >= ... >= d_p >= 1,
 * with N(a_i) = {b_1..b_{d_i}}.  For every minimal k-star-forming set S (all subsets are tried) it
 * checks:
 *   Lemma 4.2: if a vertex of S has >= k neighbours in S, every vertex of S on the other side has
 *              at most k - 2;
 *   Lemma 4.3: at most one vertex of S has >= k neighbours in S;
 *   Lemma 4.1: if h is that vertex, then for every vertex z that S - h leaves uncovered, z != h and
 *              (S - h) + z is k-independent.
 * Prints the number of minimal k-star-forming sets checked and the number of failures (exit code 1 if
 * any). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, p, q;
static unsigned adj[32];
static int ds[32];
static long nsets, nfail;

static int pc(unsigned x) { return __builtin_popcount(x); }

/* v outside T lies in a K_{1,k} inside G[T + v] (Lemma 2.1) */
static int covered(unsigned T, int k, int v)
{
  if (pc(adj[v] & T) >= k) return 1;
  for (unsigned nb = adj[v] & T; nb; nb &= nb - 1)
    if (pc(adj[__builtin_ctz(nb)] & T) >= k - 1) return 1;
  return 0;
}

static int starforming(unsigned S, int k)
{
  for (int v = 0; v < n; v++)
    if (!(S >> v & 1) && !covered(S, k, v)) return 0;
  return 1;
}

static int kindep(unsigned I, int k)
{
  for (int v = 0; v < n; v++)
    if ((I >> v & 1) && pc(adj[v] & I) >= k) return 0;
  return 1;
}

static void fail(const char *what, int k, unsigned S)
{
  nfail++;
  if (nfail <= 10) printf("%s fails: p=%d q=%d k=%d S=%x\n", what, p, q, k, S);
}

static void check(int k)
{
  for (unsigned S = 0; S < (1u << n); S++) {
    if (!starforming(S, k)) continue;
    int minimal = 1;
    for (unsigned t = S; t && minimal; t &= t - 1)
      if (starforming(S & ~(t & -t), k)) minimal = 0;
    if (!minimal) continue;
    nsets++;
    int nhigh = 0, h = -1, highA = 0, highB = 0, maxA = 0, maxB = 0;
    for (int v = 0; v < n; v++) {
      if (!(S >> v & 1)) continue;
      int d = pc(adj[v] & S);
      if (d >= k) { nhigh++; h = v; if (v < p) highA = 1; else highB = 1; }
      if (v < p) { if (d > maxA) maxA = d; } else { if (d > maxB) maxB = d; }
    }
    if ((highA && maxB > k - 2) || (highB && maxA > k - 2)) fail("Lemma 4.2", k, S);
    if (nhigh > 1) fail("Lemma 4.3", k, S);
    if (nhigh == 1) {
      unsigned T = S & ~(1u << h);
      int witnesses = 0;
      for (int z = 0; z < n; z++) {
        if ((T >> z & 1) || covered(T, k, z)) continue;
        witnesses++;
        if (z == h || !kindep(T | (1u << z), k)) fail("Lemma 4.1", k, S);
      }
      if (!witnesses) fail("minimality", k, S);
    }
  }
}

static void gen(int i, int maxd, int k)
{
  if (i == p) {
    if (ds[0] != q) return;
    memset(adj, 0, sizeof adj);
    for (int a = 0; a < p; a++)
      for (int j = 0; j < ds[a]; j++) { adj[a] |= 1u << (p + j); adj[p + j] |= 1u << a; }
    check(k);
    return;
  }
  for (int d = maxd; d >= 1; d--) { ds[i] = d; gen(i + 1, d, k); }
}

int main(int argc, char **argv)
{
  if (argc != 3) { fprintf(stderr, "usage: chainlemmas N k\n"); return 2; }
  int N = atoi(argv[1]), k = atoi(argv[2]);
  if (N < 2 || N > 16 || k < 2) { fprintf(stderr, "need 2 <= N <= 16 and k >= 2\n"); return 2; }
  for (n = 2; n <= N; n++)
    for (p = 1; p < n; p++) { q = n - p; gen(0, q, k); }
  printf("chain graphs up to %d vertices, k = %d: %ld minimal sets, %ld failures\n", N, k, nsets, nfail);
  return nfail != 0;
}
