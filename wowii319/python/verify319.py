#!/usr/bin/env python3
"""Independent check of the counterexamples to Written on the Wall II Conjecture 319.

Conjecture 319 (Graffiti.pc, 2007).  Let G be a connected graph with n > 1.  If the largest value of
dist_even(v) equals the domination number gamma(G), then G is well totally dominated, that is, every
minimal total dominating set of G has gamma_t(G) vertices.  Here dist_even(v) is the number of vertices
whose distance from v is even; v itself (distance 0) is counted.

G_k (k >= 3): a clique on c_1..c_k, a hub x, and for each i a path x - p_i - q_i - c_i.  It has 3k + 1
vertices, every vertex has dist_even = k + 1, gamma = gamma_t = k + 1, and {p_1..p_k, q_1..q_k} is a
minimal total dominating set with 2k > k + 1 vertices.

If v itself is not counted, the path P_5 already violates the conjecture; this is checked too.

Exact integer arithmetic; gamma, gamma_t and the upper total domination number Gamma_t (largest
minimal total dominating set) are computed by exhaustion over all vertex subsets for k = 3, 4, 5.
"""
import sys


def build(k):
    names = [f'c{i}' for i in range(1, k + 1)] + ['x']
    edges = [(i, j) for i in range(k) for j in range(i + 1, k)]
    x = k
    for i in range(k):
        p = len(names); names.append(f'p{i+1}')
        q = len(names); names.append(f'q{i+1}')
        edges += [(x, p), (p, q), (q, i)]
    return len(names), edges, names


def masks(n, edges):
    nb = [0] * n
    for u, v in edges:
        assert u != v and not (nb[u] >> v) & 1
        nb[u] |= 1 << v; nb[v] |= 1 << u
    return nb


def distances(n, nb, v):
    dist = [-1] * n; dist[v] = 0; frontier = [v]
    while frontier:
        nxt = []
        for u in frontier:
            for w in range(n):
                if (nb[u] >> w) & 1 and dist[w] < 0:
                    dist[w] = dist[u] + 1; nxt.append(w)
        frontier = nxt
    assert min(dist) >= 0, 'disconnected'
    return dist


def parameters(n, nb):
    full = (1 << n) - 1
    open_nb = [0] * (1 << n); closed_nb = [0] * (1 << n)
    for S in range(1, 1 << n):
        low = S & -S; v = low.bit_length() - 1
        open_nb[S] = open_nb[S ^ low] | nb[v]
        closed_nb[S] = closed_nb[S ^ low] | nb[v] | low
    gamma = min(bin(S).count('1') for S in range(1, 1 << n) if closed_nb[S] == full)
    tds = [S for S in range(1, 1 << n) if open_nb[S] == full]
    gamma_t = min(bin(S).count('1') for S in tds)

    def minimal(S):
        T = S
        while T:
            b = T & -T
            if open_nb[S ^ b] == full:
                return False
            T ^= b
        return True
    sizes = sorted({bin(S).count('1') for S in tds if minimal(S)})
    return gamma, gamma_t, sizes, open_nb, minimal


def main():
    ok = True
    for k in (3, 4, 5):
        n, edges, names = build(k)
        nb = masks(n, edges)
        ev_incl = []
        for v in range(n):
            d = distances(n, nb, v)
            ev_incl.append(sum(1 for t in d if t % 2 == 0))
        gamma, gamma_t, sizes, open_nb, minimal = parameters(n, nb)
        idx = {s: i for i, s in enumerate(names)}
        D_small = [idx['x'], idx['p1']] + [idx[f'c{i}'] for i in range(2, k + 1)]
        D_big = [idx[f'p{i}'] for i in range(1, k + 1)] + [idx[f'q{i}'] for i in range(1, k + 1)]
        full = (1 << n) - 1
        mS = sum(1 << v for v in D_small); mB = sum(1 << v for v in D_big)
        good = (n == 3 * k + 1 and set(ev_incl) == {k + 1} and gamma == k + 1 and gamma_t == k + 1
                and open_nb[mS] == full and minimal(mS) and len(D_small) == k + 1
                and open_nb[mB] == full and minimal(mB) and len(D_big) == 2 * k
                and max(ev_incl) == gamma and len(sizes) > 1)
        print(f"G_{k}: n={n} dist_even (v counted) = {sorted(set(ev_incl))} gamma={gamma} gamma_t={gamma_t} "
              f"minimal TDS sizes={sizes} explicit minimal TDS sizes {len(D_small)} and {len(D_big)}",
              'OK' if good else 'FAIL')
        ok = ok and good
    # the other reading of dist_even (v not counted) fails on the path P_5
    n, edges = 5, [(0, 1), (1, 2), (2, 3), (3, 4)]
    nb = masks(n, edges)
    ev_excl = [sum(1 for t in distances(n, nb, v) if t % 2 == 0) - 1 for v in range(n)]
    gamma, gamma_t, sizes, _, _ = parameters(n, nb)
    good = max(ev_excl) == gamma == 2 and sizes == [3, 4]
    print(f"P_5: dist_even (v not counted) max={max(ev_excl)} gamma={gamma} minimal TDS sizes={sizes}",
          'OK' if good else 'FAIL')
    ok = ok and good
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
