/* sfcheck.c -- exact values of beta_k and SF_k for the graphs G_k of the paper, 2 <= k <= KMAX.
 *
 * G_k has 3k+3 vertices: hubs h_1..h_{k-1}, blocks X_1 = {u_j} and X_2 = {w_j} (k-1 each), and
 * x0, p, c1, c2, q1, q2.  Edges: every hub to x0 and to X_1 and X_2; x0p; c1 to X_1 and q1;
 * c2 to X_2 and q2.
 *
 * beta_k = largest set inducing maximum degree < k.
 * SF_k   = largest minimal k-star-forming set.  A set S is k-star-forming when every v outside S
 *          lies in a copy of K_{1,k} inside G[S + v]: either v has >= k neighbours in S, or some
 *          neighbour u in S has >= k-1 neighbours in S (Lemma 2.2 of Sahbi).  Star-forming sets
 *          are closed upwards, so minimality is tested on one-point deletions.
 * Everything is by exhaustive search over all 2^(3k+3) subsets.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define KMAX 7

static int n;
static uint32_t adj[32];

static int pc(uint32_t x) { return __builtin_popcount(x); }

static void edge(int a, int b) { adj[a] |= 1u << b; adj[b] |= 1u << a; }

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

int main(void)
{
  printf("k n edges beta_k SF_k |S| S_minimal\n");
  for (int k = 2; k <= KMAX; k++) {
    int m = k - 1;
    n = 3 * m + 6;
    for (int v = 0; v < 32; v++) adj[v] = 0;
    int x0 = 3 * m, p = x0 + 1, c1 = x0 + 2, c2 = x0 + 3, q1 = x0 + 4, q2 = x0 + 5;
    for (int h = 0; h < m; h++) {
      edge(h, x0);
      for (int j = 0; j < m; j++) { edge(h, m + j); edge(h, 2 * m + j); }
    }
    edge(x0, p);
    for (int j = 0; j < m; j++) { edge(c1, m + j); edge(c2, 2 * m + j); }
    edge(c1, q1);
    edge(c2, q2);
    int edges = 0;
    for (int v = 0; v < n; v++) edges += pc(adj[v]);
    edges /= 2;

    uint32_t N = 1u << n;
    char *sf = malloc(N);
    if (!sf) return 1;
    int beta = 0, SF = 0;
    for (uint32_t S = 0; S < N; S++) {
      sf[S] = (char)star_forming(S, k);
      if (pc(S) > beta && k_independent(S, k)) beta = pc(S);
    }
    for (uint32_t S = 0; S < N; S++) {
      if (!sf[S] || pc(S) <= SF) continue;
      int minimal = 1;
      for (uint32_t t = S; t && minimal; t &= t - 1)
        if (sf[S & ~(t & -t)]) minimal = 0;
      if (minimal) SF = pc(S);
    }
    uint32_t S0 = (N - 1) & ~((1u << p) | (1u << q1) | (1u << q2));
    int S0min = sf[S0];
    for (uint32_t t = S0; t && S0min; t &= t - 1)
      if (sf[S0 & ~(t & -t)]) S0min = 0;
    printf("%d %d %d %d %d %d %s\n", k, n, edges, beta, SF, pc(S0), S0min ? "yes" : "no");
    fflush(stdout);
    free(sf);
  }
  return 0;
}
