/* sfsearch.c -- reads graphs in graph6 format (at most 24 vertices) on standard input and prints
 * every graph and every k in [KMIN, KMAX] with beta_k(G) != SF_k(G), with both values and a
 * largest minimal k-star-forming set as a bit mask.  The last line, on standard error, counts the
 * graphs read and the pairs (G, k) printed.
 *
 *   usage: sfsearch KMIN KMAX < graphs.g6
 *
 * beta_k and SF_k are computed as in sfcheck.c, by exhaustive search over all vertex subsets.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static uint32_t adj[32];
static char *sf;

static int pc(uint32_t x) { return __builtin_popcount(x); }

static int parse(const char *s)
{
  n = s[0] - 63;
  if (n < 1 || n > 24) return 0;
  memset(adj, 0, sizeof adj);
  const char *q = s + 1;
  int bit = 0, val = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) { val = *q++ - 63; bit = 6; }
      bit--;
      if ((val >> bit) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
  return 1;
}

static int star_forming(uint32_t S, int k)
{
  int d[32];
  for (int v = 0; v < n; v++) d[v] = pc(adj[v] & S);
  for (int v = 0; v < n; v++) {
    if (S >> v & 1) continue;
    if (d[v] >= k) continue;
    int ok = 0;
    for (uint32_t t = adj[v] & S; t && !ok; t &= t - 1)
      if (d[__builtin_ctz(t)] >= k - 1) ok = 1;
    if (!ok) return 0;
  }
  return 1;
}

static int k_independent(uint32_t I, int k)
{
  for (uint32_t t = I; t; t &= t - 1)
    if (pc(adj[__builtin_ctz(t)] & I) >= k) return 0;
  return 1;
}

int main(int argc, char **argv)
{
  if (argc != 3) { fprintf(stderr, "usage: sfsearch KMIN KMAX < graphs.g6\n"); return 2; }
  int kmin = atoi(argv[1]), kmax = atoi(argv[2]);
  sf = malloc(1u << 24);
  if (!sf) return 1;
  char line[256];
  long graphs = 0, bad = 0;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (line[0] == '>' || line[0] == 0) continue;
    if (!parse(line)) { fprintf(stderr, "bad graph6 line: %s\n", line); return 1; }
    graphs++;
    uint32_t N = 1u << n;
    for (int k = kmin; k <= kmax; k++) {
      int beta = 0, SF = 0;
      uint32_t best = 0;
      for (uint32_t S = 0; S < N; S++) {
        sf[S] = (char)star_forming(S, k);
        if (pc(S) > beta && k_independent(S, k)) beta = pc(S);
      }
      for (uint32_t S = 0; S < N; S++) {
        if (!sf[S] || pc(S) <= SF) continue;
        int minimal = 1;
        for (uint32_t t = S; t && minimal; t &= t - 1)
          if (sf[S & ~(t & -t)]) minimal = 0;
        if (minimal) { SF = pc(S); best = S; }
      }
      if (SF != beta) {
        bad++;
        printf("%s k=%d beta=%d SF=%d S=%x\n", line, k, beta, SF, best);
      }
    }
  }
  fprintf(stderr, "graphs %ld unequal %ld\n", graphs, bad);
  return 0;
}
