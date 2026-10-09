/* Exhaustive test of Graffiti.pc / Written on the Wall II Conjecture 352 on trees.
 *
 * Conjecture 352: for a tree T on n > 2 vertices,
 *   gamma_t(T) >= c(T) + ceil( ecc_avg(M) / 2 ),
 * where gamma_t is the total domination number, c(T) the number of components of the
 * subgraph induced by N(D2) u D2 (D2 = vertices of degree 2) and ecc_avg(M) the average
 * eccentricity of the vertices of maximum degree.
 *
 * Input: trees in graph6 format, one per line (e.g. nauty: gentreeg -q n | copyg -g -q).
 * Output: every violating tree, then a summary per order n.
 * gamma_t is computed by a tree dynamic programme; with -b it is also computed by brute force
 * over all vertex subsets (n <= 24) and the two values are compared.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 32
#define INF 1000000

static int n, deg[MAXN], nb[MAXN][MAXN];
static uint32_t adjm[MAXN];

static int parse_g6(const char *s) {
    n = s[0] - 63;
    if (n < 1 || n > MAXN) return 0;
    memset(deg, 0, sizeof deg); memset(adjm, 0, sizeof adjm);
    int bit = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int byte = 1 + bit / 6, sh = 5 - bit % 6;
            if (((s[byte] - 63) >> sh) & 1) {
                nb[i][deg[i]++] = j; nb[j][deg[j]++] = i;
                adjm[i] |= 1u << j; adjm[j] |= 1u << i;
            }
            bit++;
        }
    return 1;
}

static int min2(int a, int b) { return a < b ? a : b; }

/* total domination number of a tree by dynamic programming over a rooted orientation.
   States at v (for the subtree of v, all descendants already totally dominated):
   A: v in D and v has a child in D;  B: v in D, no child in D;
   C: v not in D, v has a child in D;  E: v not in D, no child in D. */
static int gamma_t_dp(void) {
    int order[MAXN], parent[MAXN], seen[MAXN] = {0}, top = 0, cnt = 0;
    int stack[MAXN]; stack[top++] = 0; seen[0] = 1; parent[0] = -1;
    while (top) { int u = stack[--top]; order[cnt++] = u;
        for (int k = 0; k < deg[u]; k++) { int w = nb[u][k]; if (!seen[w]) { seen[w] = 1; parent[w] = u; stack[top++] = w; } } }
    static int A[MAXN], B[MAXN], C[MAXN], E[MAXN];
    for (int idx = cnt - 1; idx >= 0; idx--) {
        int v = order[idx];
        long sall = 0, sce = 0, sac = 0, sc = 0; int bestA = INF, bestC = INF, nch = 0;
        for (int k = 0; k < deg[v]; k++) { int c = nb[v][k]; if (c == parent[v]) continue; nch++;
            int mall = min2(min2(A[c], B[c]), min2(C[c], E[c]));
            sall += mall; sce += min2(C[c], E[c]);
            int mac = min2(A[c], C[c]); sac += mac; sc += C[c];
            int gA = min2(A[c], B[c]) - mall; if (gA < bestA) bestA = gA;
            int gC = A[c] - mac; if (gC < bestC) bestC = gC; }
        A[v] = nch ? (int)(1 + sall + bestA) : INF;
        B[v] = (int)(1 + sce);
        C[v] = nch ? (int)(sac + bestC) : INF;
        E[v] = (int)sc;
        if (A[v] > INF) A[v] = INF;
        if (B[v] > INF) B[v] = INF;
        if (C[v] > INF) C[v] = INF;
        if (E[v] > INF) E[v] = INF;
    }
    return min2(A[0], C[0]);
}

static int gamma_t_brute(void) {
    uint32_t full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    int best = n;
    for (uint64_t S = 1; S <= full; S++) {
        int k = __builtin_popcount((uint32_t)S);
        if (k >= best) continue;
        uint32_t cov = 0;
        for (uint32_t t = (uint32_t)S; t; t &= t - 1) cov |= adjm[__builtin_ctz(t)];
        if (cov == full) best = k;
    }
    return best;
}

static int ecc_of(int v) {
    int dist[MAXN], q[MAXN], h = 0, t = 0, e = 0;
    for (int i = 0; i < n; i++) dist[i] = -1;
    dist[v] = 0; q[t++] = v;
    while (h < t) { int u = q[h++]; if (dist[u] > e) e = dist[u];
        for (int k = 0; k < deg[u]; k++) { int w = nb[u][k]; if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; } } }
    return e;
}

static int components_of(uint32_t S) {
    int c = 0;
    while (S) { uint32_t seen = S & -S, fr = seen;
        while (fr) { uint32_t nx = 0; for (uint32_t t = fr; t; t &= t - 1) nx |= adjm[__builtin_ctz(t)];
            nx &= S & ~seen; seen |= nx; fr = nx; }
        S &= ~seen; c++; }
    return c;
}

int main(int argc, char **argv) {
    int brute = (argc > 1 && strcmp(argv[1], "-b") == 0);
    char line[512];
    long long tested[MAXN + 1] = {0}, viol[MAXN + 1] = {0};
    while (fgets(line, sizeof line, stdin)) {
        int L = (int)strlen(line); while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (!L || !parse_g6(line) || n <= 2) continue;
        int gt = gamma_t_dp();
        if (brute && n <= 24) { int gb = gamma_t_brute(); if (gb != gt) { printf("MISMATCH %s dp=%d brute=%d\n", line, gt, gb); return 1; } }
        int Delta = 0; for (int v = 0; v < n; v++) if (deg[v] > Delta) Delta = deg[v];
        int sumecc = 0, cntM = 0; uint32_t D2 = 0, X = 0;
        for (int v = 0; v < n; v++) { if (deg[v] == Delta) { sumecc += ecc_of(v); cntM++; } if (deg[v] == 2) D2 |= 1u << v; }
        X = D2; for (int v = 0; v < n; v++) if (D2 >> v & 1) X |= adjm[v];
        int c = components_of(X);
        /* ceil(sumecc / (2 cntM)) for positive integers */
        int half = (sumecc + 2 * cntM - 1) / (2 * cntM);
        int rhs = c + half;
        tested[n]++;
        if (gt < rhs) { viol[n]++; printf("VIOLATION %s n=%d gamma_t=%d components=%d ecc_sum_M=%d |M|=%d bound=%d\n", line, n, gt, c, sumecc, cntM, rhs); }
    }
    for (int k = 0; k <= MAXN; k++) if (tested[k]) printf("n=%d trees=%lld violations=%lld\n", k, tested[k], viol[k]);
    return 0;
}
