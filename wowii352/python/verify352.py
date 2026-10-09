#!/usr/bin/env python3
"""Independent check of the counterexamples to Written on the Wall II Conjecture 352.

Conjecture 352 (Graffiti.pc, 2009): for every tree T on n > 2 vertices,
    gamma_t(T) >= c(T) + ceil(ecc_avg(M) / 2),
where c(T) is the number of components of the subgraph induced by N(D2) u D2
(D2 = vertices of degree two) and ecc_avg(M) is the average eccentricity of the
vertices of maximum degree.

T(a, r): a hub h with three pendant leaves, a path of a degree-two vertices x_1..x_a,
three consecutive support vertices s_1, s_2, s_3 (each with one pendant leaf),
a path of r degree-two vertices y_1..y_r, and a final leaf z.
The paper proves gamma_t(T(a, r)) = (a + r + 7)/2 < (a + r + 9)/2 = bound
whenever a = 3 (mod 4) and r = 0 (mod 4), r >= 4.

This script uses exact integer arithmetic only.  For every tree it checks
  * the tree property (connected, n - 1 edges),
  * the bound c(T) + ceil(ecc_avg(M)/2) from first principles (BFS),
  * an explicit total dominating set of size (a + r + 7)/2,
  * that no total dominating set of size (a + r + 5)/2 exists (exhaustive over
    all subsets of that size; only for the smaller members).
"""
import itertools
import sys


def build(a, r):
    edges = []
    count = [0]

    def new():
        count[0] += 1
        return count[0] - 1

    h = new()
    labels = {h: 'h'}
    for i in range(3):
        leaf = new(); labels[leaf] = f'h-leaf{i+1}'; edges.append((h, leaf))
    prev = h
    xs = []
    for i in range(a):
        x = new(); labels[x] = f'x{i+1}'; edges.append((prev, x)); prev = x; xs.append(x)
    ss = []
    for i in range(3):
        s = new(); labels[s] = f's{i+1}'; edges.append((prev, s)); prev = s; ss.append(s)
        leaf = new(); labels[leaf] = f's{i+1}-leaf'; edges.append((s, leaf))
    ys = []
    for i in range(r):
        y = new(); labels[y] = f'y{i+1}'; edges.append((prev, y)); prev = y; ys.append(y)
    z = new(); labels[z] = 'z'; edges.append((prev, z))
    return count[0], edges, labels, h, xs, ss, ys, z


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adj[u]
        adj[u].add(v); adj[v].add(u)
    return adj


def bfs(adj, src):
    dist = {src: 0}
    frontier = [src]
    while frontier:
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; nxt.append(w)
        frontier = nxt
    return dist


def is_tree(n, adj):
    m = sum(len(a) for a in adj) // 2
    return m == n - 1 and len(bfs(adj, 0)) == n


def n_components(adj, S):
    S = set(S); seen = set(); c = 0
    for s in S:
        if s in seen:
            continue
        c += 1
        stack = [s]; seen.add(s)
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w in S and w not in seen:
                    seen.add(w); stack.append(w)
    return c


def bound352(n, adj):
    deg = [len(a) for a in adj]
    Delta = max(deg)
    M = [v for v in range(n) if deg[v] == Delta]
    ecc_sum = sum(max(bfs(adj, v).values()) for v in M)
    D2 = {v for v in range(n) if deg[v] == 2}
    X = set(D2)
    for v in D2:
        X |= adj[v]
    c = n_components(adj, X)
    # ceil(ecc_sum / (2|M|)) with integers
    half = -((-ecc_sum) // (2 * len(M)))
    return c, ecc_sum, len(M), c + half


def is_tds(adj, S):
    S = set(S)
    return all(adj[v] & S for v in range(len(adj)))


def explicit_tds(a, r, h, xs, ss, ys):
    """The set from the paper: h, x_1, pairs x_{4j}, x_{4j+1}; s_1, s_2, s_3; pairs y_{4i-1}, y_{4i}."""
    D = [h, xs[0]] + list(ss)
    for j in range(1, (a - 3) // 4 + 1):
        D += [xs[4*j - 1], xs[4*j]]          # x_{4j}, x_{4j+1} (0-based indices)
    for i in range(1, r // 4 + 1):
        D += [ys[4*i - 2], ys[4*i - 1]]      # y_{4i-1}, y_{4i}
    return D


def no_tds_of_size(adj, k):
    n = len(adj)
    for S in itertools.combinations(range(n), k):
        if is_tds(adj, S):
            return False, S
    return True, None


def main():
    ok = True
    exhaustive_limit = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    for a in (3, 7, 11):
        for r in (4, 8, 12, 16):
            n, edges, labels, h, xs, ss, ys, z = build(a, r)
            adj = adjacency(n, edges)
            assert is_tree(n, adj)
            c, ecc_sum, sizeM, bound = bound352(n, adj)
            D = explicit_tds(a, r, h, xs, ss, ys)
            assert len(set(D)) == len(D)
            tds_ok = is_tds(adj, D)
            line = (f"T({a},{r}): n={n} max-degree vertices={sizeM} ecc={ecc_sum} components={c} "
                    f"bound={bound} explicit TDS size={len(D)} valid={tds_ok}")
            good = tds_ok and len(D) == (a + r + 7) // 2 and bound == (a + r + 9) // 2 and len(D) < bound
            if n <= exhaustive_limit:
                none_smaller, S = no_tds_of_size(adj, len(D) - 1)
                line += f" no TDS of size {len(D)-1}: {none_smaller}"
                good = good and none_smaller
            print(line, 'OK' if good else 'FAIL')
            ok = ok and good
    # the 18-vertex counterexample in graph6 found by exhaustive search
    n, edges, labels, h, xs, ss, ys, z = build(3, 4)
    print('T(3,4) edges (labelled):', [(labels[u], labels[v]) for u, v in edges])
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
