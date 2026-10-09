#!/usr/bin/env python3
"""Independent check of the counterexamples to Written on the Wall II Conjectures 358 and 359.

For a tree T on n > 2 vertices, with C the center, S the support vertices and L the leaves:
  358:  gamma_t(T) >= ecc(C)/2 + (number of isolated vertices of <S>),
  359:  gamma_t(T) >= ecc(C)/2 + (number of components of <S u L>),
where ecc(C) is the largest distance from a vertex outside C to the set C.

Q_k (k odd, k >= 3) is the caterpillar whose spine consists of k blocks s - c - s' (two support
vertices and the vertex between them), consecutive blocks joined through two vertices of degree
two, and one pendant leaf at every support vertex.  It has 7k - 2 vertices, and the paper proves
    gamma_t(Q_k) = 3k  <  (5k - 1)/4 + 2k,
so both conjectures fail by (k - 1)/4.

This script uses exact arithmetic only.  For every Q_k it checks the tree property, the center,
ecc(C), the isolates of <S>, the components of <S u L>, an explicit total dominating set of size 3k,
and the value of gamma_t computed by a tree dynamic programme; for Q_3 it also checks by exhaustion
that no total dominating set has 8 vertices.
"""
import itertools
import sys
from fractions import Fraction


def build(k):
    edges, labels = [], {}
    count = [0]

    def new(name):
        labels[count[0]] = name
        count[0] += 1
        return count[0] - 1

    blocks = []
    prev = None
    for j in range(1, k + 1):
        if prev is not None:
            u = new(f'u{j-1}'); w = new(f'w{j-1}')
            edges += [(prev, u), (u, w)]
            prev = w
        s1 = new(f's{j}'); c = new(f'c{j}'); s2 = new(f's{j}\'')
        if prev is not None:
            edges.append((prev, s1))
        edges += [(s1, c), (c, s2)]
        for s in (s1, s2):
            leaf = new(f'leaf({labels[s]})'); edges.append((s, leaf))
        blocks.append((s1, c, s2))
        prev = s2
    return count[0], edges, labels, blocks


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adj[u]
        adj[u].add(v); adj[v].add(u)
    return adj


def bfs(adj, sources):
    dist = {s: 0 for s in sources}
    frontier = list(sources)
    while frontier:
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; nxt.append(w)
        frontier = nxt
    return dist


def n_components(adj, X):
    X = set(X); seen = set(); c = 0
    for s in X:
        if s in seen:
            continue
        c += 1; stack = [s]; seen.add(s)
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w in X and w not in seen:
                    seen.add(w); stack.append(w)
    return c


def is_tds(adj, D):
    D = set(D)
    return all(adj[v] & D for v in range(len(adj)))


def gamma_t_tree(adj):
    """Total domination number of a tree by dynamic programming (independent of the C code).
    For the subtree of v, with every vertex below v totally dominated:
      a: v in D, dominated by a child;  b: v in D, not yet dominated;
      c: v not in D, dominated by a child;  e: v not in D, not yet dominated."""
    INF = float('inf')
    n = len(adj); parent = {0: None}; order = [0]
    for u in order:
        for w in adj[u]:
            if w not in parent:
                parent[w] = u; order.append(w)
    val = {}
    for v in reversed(order):
        ch = [w for w in adj[v] if w != parent[v]]
        # v in D: each child may be in any state except that a child in state e (undominated)
        # is now dominated by v; children in D (a or b) dominate v.
        def best(states_allowed_with_flag):
            # returns (min cost with no child in D, min cost with at least one child in D)
            none_in, some_in = 0, INF
            for w in ch:
                a, b, c, e = val[w]
                opts_out = states_allowed_with_flag['out'](a, b, c, e)
                opts_in = states_allowed_with_flag['in'](a, b, c, e)
                new_none = none_in + opts_out
                new_some = min(some_in + min(opts_out, opts_in), none_in + opts_in)
                none_in, some_in = new_none, new_some
            return none_in, some_in
        inD = {'out': lambda a, b, c, e: min(c, e), 'in': lambda a, b, c, e: min(a, b)}
        outD = {'out': lambda a, b, c, e: c, 'in': lambda a, b, c, e: a}
        n1, s1 = best(inD)
        n0, s0 = best(outD)
        val[v] = (1 + s1, 1 + n1, s0, n0)
    a, b, c, e = val[0]
    return min(a, c)


def main():
    ok = True
    for k in (3, 5, 7, 9, 11):
        n, edges, labels, blocks = build(k)
        adj = adjacency(n, edges)
        assert len(edges) == n - 1 and len(bfs(adj, [0])) == n          # a tree
        ecc = [max(bfs(adj, [v]).values()) for v in range(n)]
        rad = min(ecc); C = [v for v in range(n) if ecc[v] == rad]
        d = bfs(adj, C); eccC = max(d[v] for v in range(n) if v not in C)
        L = [v for v in range(n) if len(adj[v]) == 1]
        S = sorted({w for v in L for w in adj[v]})
        iso = sum(1 for v in S if not adj[v] & set(S))
        comps = n_components(adj, set(S) | set(L))
        D = [x for blk in blocks for x in blk]
        gt = gamma_t_tree(adj)
        b358 = Fraction(eccC, 2) + iso
        b359 = Fraction(eccC, 2) + comps
        good = (n == 7 * k - 2 and len(C) == 1 and labels[C[0]] == f'c{(k + 1) // 2}' and eccC == (5 * k - 1) // 2
                and iso == 2 * k and comps == 2 * k and is_tds(adj, D) and len(D) == 3 * k and gt == 3 * k
                and gt < b358 and gt < b359 and b358 - gt == Fraction(k - 1, 4))
        line = (f"Q_{k}: n={n} center={[labels[c] for c in C]} ecc(C)={eccC} isolates(S)={iso} "
                f"components(S u L)={comps} gamma_t(DP)={gt} explicit TDS={len(D)} bounds 358/359={b358}/{b359}")
        if k == 3:
            none8 = not any(is_tds(adj, X) for X in itertools.combinations(range(n), 8))
            line += f" no TDS of size 8: {none8}"
            good = good and none8
        print(line, 'OK' if good else 'FAIL')
        ok = ok and good
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
