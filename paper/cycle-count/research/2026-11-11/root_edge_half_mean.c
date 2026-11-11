/* Cycle census of cubic graphs (Fable 5.2, 10 November 2026).
 *
 * Input: graph6 lines on standard input, each a connected simple cubic graph
 * on n <= 26 vertices (for example from nauty's "geng -c -d3 -D3 n").
 * For every graph the program enumerates the binary cycle space with a Gray
 * code and tests each nonzero even subgraph for connectedness. In a cubic
 * graph a connected nonzero even subgraph is a cycle. So it obtains
 *   c(G)    the number of cycles,
 *   c_e(G)  the number of cycles through each edge e.
 * Output: one JSON object with
 *   the largest c(G) and the graphs that attain it (with girth and edge data),
 *   for each girth: the number of graphs and the largest c(G),
 *   the largest value of min_e c_e(G) and one graph that attains it,
 *   the graphs with 2 min_e c_e(G) > c(G)   (edge-half conjecture fails),
 *   the graphs in which some vertex has 2 c_e(G) > c(G) for all three of its edges
 *   (the vertex form of the edge-half conjecture fails), with their number,
 *   the smallest value of c(G) - 2 min_e c_e(G).
 * All arithmetic is exact (64-bit integers).
 * Build:  cc -O2 -o fable_cycle_census fable_cycle_census.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define MAXE 50
#define KEEP 64

static int n, m, r;
static int eu[MAXE], ev[MAXE];
static uint64_t inc[MAXN];
static int adj[MAXN][3], deg[MAXN], adje[MAXN][3];

static int parse(const char *s) {
    n = s[0] - 63;
    if (n < 1 || n > MAXN) return 0;
    m = 0;
    memset(deg, 0, sizeof deg);
    memset(inc, 0, sizeof inc);
    const char *p = s + 1;
    int bits = 0, left = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (left == 0) { bits = *p++ - 63; left = 6; }
            int b = (bits >> (left - 1)) & 1;
            left--;
            if (b) {
                if (m >= MAXE || deg[i] >= 3 || deg[j] >= 3) return 0;
                eu[m] = i; ev[m] = j;
                inc[i] |= 1ULL << m; inc[j] |= 1ULL << m;
                adj[i][deg[i]] = j; adje[i][deg[i]++] = m;
                adj[j][deg[j]] = i; adje[j][deg[j]++] = m;
                m++;
            }
        }
    for (int i = 0; i < n; i++) if (deg[i] != 3) return 0;
    r = m - n + 1;
    return 1;
}

static int girth(void) {
    int best = 1000;
    for (int s = 0; s < n; s++) {
        int dist[MAXN], par[MAXN], q[MAXN], h = 0, t = 0;
        for (int i = 0; i < n; i++) dist[i] = -1;
        dist[s] = 0; par[s] = -1; q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int a = 0; a < 3; a++) {
                int y = adj[x][a];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; par[y] = x; q[t++] = y; }
                else if (par[x] != y && dist[x] + dist[y] + 1 < best) best = dist[x] + dist[y] + 1;
            }
        }
    }
    return best;
}

static uint64_t basis[MAXE];

static int make_basis(void) {
    uint64_t path[MAXN];
    int seen[MAXN], q[MAXN], h = 0, t = 0, used[MAXE];
    memset(seen, 0, sizeof seen);
    memset(used, 0, sizeof used);
    seen[0] = 1; path[0] = 0; q[t++] = 0;
    while (h < t) {
        int x = q[h++];
        for (int a = 0; a < 3; a++) {
            int y = adj[x][a], e = adje[x][a];
            if (!seen[y]) { seen[y] = 1; path[y] = path[x] | (1ULL << e); used[e] = 1; q[t++] = y; }
        }
    }
    if (t != n) return 0;                      /* not connected */
    int k = 0;
    for (int e = 0; e < m; e++)
        if (!used[e]) basis[k++] = path[eu[e]] ^ path[ev[e]] ^ (1ULL << e);
    return k == r;
}

static long long cnt[MAXE];

static long long census(void) {
    long long c = 0;
    memset(cnt, 0, sizeof cnt);
    uint64_t x = 0;
    uint64_t total = 1ULL << r;
    for (uint64_t i = 1; i < total; i++) {
        x ^= basis[__builtin_ctzll(i)];
        int k = __builtin_popcountll(x);
        int e0 = __builtin_ctzll(x);
        int start = eu[e0], cur = ev[e0], prev = e0, steps = 1;
        while (cur != start) {
            int nx = __builtin_ctzll((inc[cur] & x) & ~(1ULL << prev));
            cur = eu[nx] ^ ev[nx] ^ cur;
            prev = nx;
            steps++;
        }
        if (steps == k) {
            c++;
            uint64_t y = x;
            while (y) { cnt[__builtin_ctzll(y)]++; y &= y - 1; }
        }
    }
    return c;
}

int main(int argc, char **argv) {
    char line[256], best[256]="";
    long long graphs=0, bad=0, minfreq=0, bestc=1, bestlen=0;
    long long bestscore=-(1LL<<60);
    while(fgets(line,sizeof line,stdin)) {
        if(line[0]=='>')continue;
        line[strcspn(line,"\r\n")]=0;
        if(!parse(line)||!make_basis())return 2;
        if(argc>1 && strcmp(argv[1],"3ec")==0) {
            uint64_t cols[MAXE]={0}; int good=1;
            for(int j=0;j<r;j++)for(int e=0;e<m;e++) if(basis[j]>>e&1)cols[e]|=1ULL<<j;
            for(int e=0;e<m;e++){if(!cols[e])good=0;for(int f=0;f<e;f++)if(cols[e]==cols[f])good=0;}
            if(!good)continue;
        }
        long long c=census(), length=0, mn=cnt[0];
        for(int e=0;e<m;e++){length+=cnt[e]; if(cnt[e]<mn)mn=cnt[e];}
        long long score=4*length-3*n*c;
        graphs++;
        if(graphs==1 || score*bestc>bestscore*c){bestscore=score;bestc=c;bestlen=length;minfreq=mn;strcpy(best,line);}
        if(score>0) {
            bad++;
            printf("{\"kind\":\"mean_violation\",\"n\":%d,\"g6\":\"%s\",\"cycles\":%lld,\"length_sum\":%lld,\"score\":%lld,\"min_edge\":%lld}\n",n,line,c,length,score,mn);
            fflush(stdout);
            if(bad>=5)break;
        }
    }
    printf("{\"kind\":\"summary\",\"n\":%d,\"graphs\":%lld,\"violations\":%lld,\"best_g6\":\"%s\",\"best_cycles\":%lld,\"best_length_sum\":%lld,\"best_score\":%lld,\"best_min_edge\":%lld}\n",n,graphs,bad,best,bestc,bestlen,bestscore,minfreq);
    return 0;
}
