#!/usr/bin/env python3
"""Independent check of the counterexamples to Written on the Wall II Conjecture 427.

Conjecture 427 (Graffiti.pc, 2010), as printed: for a connected graph G on n > 3 vertices,
    i(G) <= |E(C, V - C)| + floor( (2/3) |E(G[V - N(P)])| ),
where i(G) is the independent domination number, P the set of pendant vertices and C the center
(the statement defines neither C nor P; these are their meanings in the neighbouring conjectures).
We also test the reading in which C is the set M of vertices of maximum degree.

H_m (m >= 2): a path v_{-m} .. v_m with one pendant leaf at every v_j, j != 0 (4m + 1 vertices).
   Center reading: right side = 2, while i(H_m) >= 2m.
F_m (m >= 5): a path v_1 .. v_m with one pendant leaf at every v_j and a second leaf at v_2
   (2m + 1 vertices).  M reading: right side = 4, while i(F_m) >= m.
The smallest counterexample (center reading) has 8 vertices; it is checked here as well.
i(G) is computed exactly by exhaustion over independent sets.
"""
import itertools
import sys


def masks(n, edges):
    nb = [0] * n
    for u, v in edges:
        assert u != v and not (nb[u] >> v) & 1
        nb[u] |= 1 << v; nb[v] |= 1 << u
    return nb


def dist_from(n, nb, srcs):
    d = [-1] * n
    for s in srcs:
        d[s] = 0
    fr = list(srcs)
    while fr:
        nxt = []
        for u in fr:
            for w in range(n):
                if (nb[u] >> w) & 1 and d[w] < 0:
                    d[w] = d[u] + 1; nxt.append(w)
        fr = nxt
    assert min(d) >= 0
    return d


def rhs(n, nb, which):
    deg = [bin(x).count('1') for x in nb]
    if which == 'center':
        ecc = [max(dist_from(n, nb, [v])) for v in range(n)]
        X = {v for v in range(n) if ecc[v] == min(ecc)}
    else:
        X = {v for v in range(n) if deg[v] == max(deg)}
    cut = sum(1 for u in X for w in range(n) if (nb[u] >> w) & 1 and w not in X)
    P = [v for v in range(n) if deg[v] == 1]
    NP = {w for p in P for w in range(n) if (nb[p] >> w) & 1}
    W = [v for v in range(n) if v not in NP]
    eW = sum(1 for a, b in itertools.combinations(W, 2) if (nb[a] >> b) & 1)
    return cut + (2 * eW) // 3, sorted(X)


def i_number(n, nb):
    full = (1 << n) - 1
    best = n
    def rec(v, S, dom, k):
        nonlocal best
        if k >= best:
            return
        if dom == full:
            best = k; return
        if v == n:
            return
        rec(v + 1, S, dom, k)                                # v not in S
        if not (nb[v] & S):                                  # v may join S
            rec(v + 1, S | (1 << v), dom | nb[v] | (1 << v), k + 1)
    rec(0, 0, 0, 0)
    return best


def H(m):
    idx = {j: j + m for j in range(-m, m + 1)}
    edges = [(idx[j], idx[j + 1]) for j in range(-m, m)]
    n = 2 * m + 1
    for j in range(-m, m + 1):
        if j != 0:
            edges.append((idx[j], n)); n += 1
    return n, edges


def F(m):
    edges = [(j, j + 1) for j in range(m - 1)]
    n = m
    for j in range(m):
        edges.append((j, n)); n += 1
    edges.append((1, n)); n += 1                             # second leaf at v_2
    return n, edges


def main():
    ok = True
    for m in (2, 3, 4, 5):
        n, edges = H(m); nb = masks(n, edges)
        r, C = rhs(n, nb, 'center'); i = i_number(n, nb)
        good = n == 4 * m + 1 and C == [m] and r == 2 and i >= 2 * m and i > r
        print(f"H_{m}: n={n} center={C} right side={r} i={i}", 'OK' if good else 'FAIL'); ok &= good
    for m in (5, 6, 7, 8):
        n, edges = F(m); nb = masks(n, edges)
        r, M = rhs(n, nb, 'M'); i = i_number(n, nb)
        good = n == 2 * m + 1 and M == [1] and r == 4 and i >= m and i > r
        print(f"F_{m}: n={n} M={M} right side (C = M)={r} i={i}", 'OK' if good else 'FAIL'); ok &= good
    # smallest counterexample (center reading): path 4-0-6-2-7-1-5 with a leaf 3 at 7
    n, edges = 8, [(0, 4), (0, 6), (1, 5), (1, 7), (2, 6), (2, 7), (3, 7)]
    nb = masks(n, edges); r, C = rhs(n, nb, 'center'); i = i_number(n, nb)
    good = C == [2] and r == 2 and i == 3
    print(f"8-vertex tree: center={C} right side={r} i={i}", 'OK' if good else 'FAIL'); ok &= good
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
