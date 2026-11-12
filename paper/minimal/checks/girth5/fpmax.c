/* Forest proportions of T-joins of a small connected subcubic graph, by complete enumeration.
 *
 * Input on stdin:  n m, then m lines "u v" (vertices 0..n-1).  The graph must be connected and
 * subcubic.  The boundary vertices are the vertices of degree less than three.
 * For an even set T of boundary vertices, a T-join is a set of edges in which exactly the
 * vertices of T have odd degree.  There are 2^beta of them, beta = m - n + 1.
 * The forest proportion of T is the proportion of the T-joins that are forests.
 *
 * Usage:  fpmax [maxT]        maxT = largest size of T that is examined (default: all sizes)
 * Output: one line   n m beta k  best_count best_T_size  number_of_T_examined  number_with_fp>=3/5
 *                    number_rigid  best_T (list of vertices)
 * where best_count is the largest number of forest T-joins over the examined nonempty sets T,
 * and a set T is rigid if all its T-joins are forests.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 mask;
#define MAXN 128
static int n, m, eu[MAXN], ev[MAXN], deg[MAXN], adjv[MAXN][3], adje[MAXN][3];
static mask pathm[MAXN], basis[MAXN];
static inline int popc(mask x) { return __builtin_popcountll((unsigned long long)x) + __builtin_popcountll((unsigned long long)(x >> 64)); }

/* J is a T-join: all degrees are at most two, and the vertices of degree one are those of T.
   J is a forest if and only if the paths that start in T contain all edges of J. */
static int is_forest(mask J, const int *T, int tsize) {
  int total = popc(J), seen = 0;
  mask used = 0;
  for (int i = 0; i < tsize; i++) {
    int cur = T[i], pe = -1;
    /* the unique edge of J at T[i] */
    int first = -1;
    for (int a = 0; a < deg[cur]; a++) if ((J >> adje[cur][a]) & 1) { first = adje[cur][a]; break; }
    if (first < 0) return 0;               /* cannot happen for a T-join */
    if ((used >> first) & 1) continue;      /* this path was walked from its other end */
    pe = first;
    for (;;) {
      used |= ((mask)1) << pe; seen++;
      cur = (eu[pe] == cur) ? ev[pe] : eu[pe];
      int nxt = -1;
      for (int a = 0; a < deg[cur]; a++) { int e = adje[cur][a]; if (e != pe && ((J >> e) & 1)) { nxt = e; break; } }
      if (nxt < 0) break;                   /* the other end of the path */
      pe = nxt;
    }
  }
  return seen == total;
}

int main(int argc, char **argv) {
  int maxT = argc > 1 ? atoi(argv[1]) : MAXN;
  if (scanf("%d %d", &n, &m) != 2 || n > MAXN || m > MAXN) { fprintf(stderr, "bad input\n"); return 2; }
  for (int e = 0; e < m; e++) {
    if (scanf("%d %d", &eu[e], &ev[e]) != 2) { fprintf(stderr, "bad edge\n"); return 2; }
    int a = eu[e], b = ev[e];
    if (deg[a] >= 3 || deg[b] >= 3 || a == b) { fprintf(stderr, "not subcubic or loop\n"); return 2; }
    adjv[a][deg[a]] = b; adje[a][deg[a]++] = e; adjv[b][deg[b]] = a; adje[b][deg[b]++] = e;
  }
  /* spanning tree by breadth-first search from 0 */
  int par[MAXN], pedge[MAXN], q[MAXN], qh = 0, qt = 0; char intree[MAXN];
  memset(intree, 0, sizeof intree);
  for (int v = 0; v < n; v++) par[v] = -2;
  par[0] = -1; q[qt++] = 0; pathm[0] = 0;
  while (qh < qt) {
    int u = q[qh++];
    for (int a = 0; a < deg[u]; a++) { int w = adjv[u][a], e = adje[u][a];
      if (par[w] == -2) { par[w] = u; pedge[w] = e; intree[e] = 1; pathm[w] = pathm[u] ^ (((mask)1) << e); q[qt++] = w; } }
  }
  if (qt != n) { fprintf(stderr, "not connected\n"); return 2; }
  int beta = 0;
  for (int e = 0; e < m; e++) if (!intree[e]) basis[beta++] = (((mask)1) << e) ^ pathm[eu[e]] ^ pathm[ev[e]];
  if (beta != m - n + 1 || beta > 40) { fprintf(stderr, "rank %d is too large or wrong\n", beta); return 2; }
  int bd[MAXN], k = 0;
  for (int v = 0; v < n; v++) if (deg[v] < 3) bd[k++] = v;
  if (k > 24) { fprintf(stderr, "too many boundary vertices\n"); return 2; }
  /* the examined sets T: nonempty, even, of size at most maxT */
  long nT = 0; long *Tsets = malloc(sizeof(long) * ((size_t)1 << (k > 0 ? k - 1 : 0)));
  for (long s = 1; s < (1L << k); s++) { int c = __builtin_popcountl(s); if (c % 2 == 0 && c <= maxT) Tsets[nT++] = s; }
  mask *JT = malloc(sizeof(mask) * (nT ? nT : 1));
  int (*Tl)[24] = malloc(sizeof(int[24]) * (nT ? nT : 1)); int *Tsz = malloc(sizeof(int) * (nT ? nT : 1));
  unsigned long long *cnt = calloc(nT ? nT : 1, sizeof(unsigned long long));
  for (long i = 0; i < nT; i++) { mask j = 0; int c = 0;
    for (int b = 0; b < k; b++) if ((Tsets[i] >> b) & 1) { j ^= pathm[bd[b]]; Tl[i][c++] = bd[b]; }
    JT[i] = j; Tsz[i] = c; }
  unsigned long long total = 1ULL << beta; mask x = 0;
  for (unsigned long long g = 0; g < total; g++) {
    if (g) x ^= basis[__builtin_ctzll(g)];
    for (long i = 0; i < nT; i++) cnt[i] += is_forest(JT[i] ^ x, Tl[i], Tsz[i]);
  }
  long best = -1, good = 0, rigid = 0;
  for (long i = 0; i < nT; i++) {
    if (best < 0 || cnt[i] > cnt[best]) best = i;
    if (5 * cnt[i] >= 3 * total) good++;
    if (cnt[i] == total) rigid++;
  }
  printf("%d %d %d %d %llu %d %ld %ld %ld", n, m, beta, k, best >= 0 ? cnt[best] : 0ULL, best >= 0 ? Tsz[best] : 0, nT, good, rigid);
  if (best >= 0) for (int c = 0; c < Tsz[best]; c++) printf(" %d", Tl[best][c]);
  printf("\n");
  return 0;
}
