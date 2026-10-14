/* sharpcheck.c -- checks Theorem 1.4 and Lemma 5.2 of the paper on small graphs.
 *
 * Reads graphs H in graph6 format on standard input, builds H# (every edge uv, u < v, becomes the
 * path u a b c v, and every vertex v gets a pendant vertex v'), and computes by exhaustive search
 * over all vertex subsets of H#
 *
 *   alpha(H), beta_2(H#) and SF_2(H#),
 *
 * checking beta_2(H#) = SF_2(H#) = n + 2m + alpha(H).  For every minimal 2-star-forming set S of
 * H# it also checks parts (a)-(c) of Lemma 5.2: v or v' is in S; no edge has a, b, c all in S; an
 * edge whose two ends u, v have u, u', v, v' in S has at most one of a, b, c in S.  Graphs H with
 * 2n + 3m > MAXV are skipped.  One line per graph:
 *
 *   graph6 n m alpha beta2 SF2 minimal_sets
 *
 * and a last line with the number of graphs checked and of failures (exit status 1 on a failure).
 *
 *   usage: sharpcheck MAXV < graphs.g6        (MAXV <= 26)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nh, mh, nv;            /* H has nh vertices and mh edges; H# has nv vertices */
static uint32_t hadj[32];         /* adjacency of H */
static int eu[400], ev[400];      /* ends of the edges of H, eu < ev */
static uint32_t adj[32];          /* adjacency of H# */
static char *sf;

static int pc(uint32_t x) { return __builtin_popcount(x); }

static int parse(const char *s)
{
  nh = s[0] - 63;
  if (nh < 1 || nh > 30) return 0;
  memset(hadj, 0, sizeof hadj);
  mh = 0;
  const char *q = s + 1;
  int bit = 0, val = 0;
  for (int j = 1; j < nh; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { val = *q++ - 63; bit = 6; }
      bit--;
      if ((val >> bit) & 1) {
        hadj[i] |= 1u << j; hadj[j] |= 1u << i;
        eu[mh] = i; ev[mh] = j; mh++;
      }
    }
  return 1;
}

/* vertex numbers in H#: v for v in H, nh + v for the pendant v', 2nh + 3e + {0,1,2} for a_e, b_e, c_e */
static int P(int v) { return nh + v; }
static int A(int e) { return 2 * nh + 3 * e; }
static int Bv(int e) { return 2 * nh + 3 * e + 1; }
static int C(int e) { return 2 * nh + 3 * e + 2; }

static void edge(int x, int y) { adj[x] |= 1u << y; adj[y] |= 1u << x; }

static void build(void)
{
  nv = 2 * nh + 3 * mh;
  memset(adj, 0, sizeof adj);
  for (int v = 0; v < nh; v++) edge(v, P(v));
  for (int e = 0; e < mh; e++) {
    edge(eu[e], A(e)); edge(A(e), Bv(e)); edge(Bv(e), C(e)); edge(C(e), ev[e]);
  }
}

static int alpha(void)
{
  int best = 0;
  for (uint32_t I = 0; I < (1u << nh); I++) {
    if (pc(I) <= best) continue;
    int ok = 1;
    for (uint32_t t = I; t && ok; t &= t - 1)
      if (hadj[__builtin_ctz(t)] & I) ok = 0;
    if (ok) best = pc(I);
  }
  return best;
}

/* Lemma 2.1 with k = 2: every v outside S has two neighbours in S or a neighbour in S with a
 * neighbour in S */
static int star_forming(uint32_t S)
{
  int d[32];
  for (int v = 0; v < nv; v++) d[v] = pc(adj[v] & S);
  for (int v = 0; v < nv; v++) {
    if (S >> v & 1 || d[v] >= 2) continue;
    int ok = 0;
    for (uint32_t t = adj[v] & S; t && !ok; t &= t - 1)
      if (d[__builtin_ctz(t)] >= 1) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int two_independent(uint32_t I)
{
  for (uint32_t t = I; t; t &= t - 1)
    if (pc(adj[__builtin_ctz(t)] & I) >= 2) return 0;
  return 1;
}

static int in(uint32_t S, int x) { return (int)(S >> x & 1); }

/* parts (a)-(c) of Lemma 5.2 for a minimal 2-star-forming set S */
static int lemma(uint32_t S)
{
  for (int v = 0; v < nh; v++)
    if (!in(S, v) && !in(S, P(v))) return 0;
  for (int e = 0; e < mh; e++) {
    int inner = in(S, A(e)) + in(S, Bv(e)) + in(S, C(e));
    if (inner == 3) return 0;
    int u = eu[e], v = ev[e];
    if (in(S, u) && in(S, P(u)) && in(S, v) && in(S, P(v)) && inner > 1) return 0;
  }
  return 1;
}

int main(int argc, char **argv)
{
  if (argc != 2) { fprintf(stderr, "usage: sharpcheck MAXV < graphs.g6\n"); return 2; }
  int maxv = atoi(argv[1]);
  if (maxv < 1 || maxv > 26) { fprintf(stderr, "MAXV must be between 1 and 26\n"); return 2; }
  sf = malloc((size_t)1 << maxv);
  if (!sf) return 1;
  char line[256];
  long graphs = 0, bad = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (line[0] == '>' || line[0] == 0) continue;
    if (!parse(line)) { fprintf(stderr, "bad graph6 line: %s\n", line); return 1; }
    if (2 * nh + 3 * mh > maxv) continue;
    build();
    graphs++;
    uint32_t N = 1u << nv;
    int beta = 0, SF = 0, lem = 1;
    long minimal_sets = 0;
    for (uint32_t S = 0; S < N; S++) {
      sf[S] = (char)star_forming(S);
      if (pc(S) > beta && two_independent(S)) beta = pc(S);
    }
    for (uint32_t S = 0; S < N; S++) {
      if (!sf[S]) continue;
      int minimal = 1;
      for (uint32_t t = S; t && minimal; t &= t - 1)
        if (sf[S & ~(t & -t)]) minimal = 0;
      if (!minimal) continue;
      minimal_sets++;
      if (pc(S) > SF) SF = pc(S);
      if (!lemma(S)) lem = 0;
    }
    int a = alpha(), want = nh + 2 * mh + a;
    int ok = beta == want && SF == want && lem;
    if (!ok) bad++;
    printf("%s %d %d %d %d %d %ld%s\n", line, nh, mh, a, beta, SF, minimal_sets, ok ? "" : " FAIL");
  }
  printf("graphs %ld failures %ld\n", graphs, bad);
  return bad ? 1 : 0;
}
