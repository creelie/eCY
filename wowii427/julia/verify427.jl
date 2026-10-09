# Independent Julia check of the counterexamples to Written on the Wall II Conjecture 427:
#   i(G) <= |E(C, V-C)| + floor((2/3)|E(G[V - N(P)])|),  P = pendant vertices,
# with C the center (H_m and the 8-vertex tree) and with C = M, the maximum-degree vertices (F_m).
# i(G) is computed by brute force over all vertex subsets.

function nbmasks(n, edges)
    nb = zeros(UInt32, n)
    for (u, v) in edges
        nb[u] |= UInt32(1) << (v - 1); nb[v] |= UInt32(1) << (u - 1)
    end
    return nb
end

bit(x, k) = (x >> (k - 1)) & 1 == 1

function rhs(n, nb, which)
    deg = [count_ones(nb[v]) for v in 1:n]
    if which == :center
        ecc = zeros(Int, n)
        for v in 1:n
            seen = UInt32(1) << (v - 1); fr = seen; d = 0
            while true
                nx = UInt32(0)
                for u in 1:n; bit(fr, u) && (nx |= nb[u]); end
                nx &= ~seen
                nx == 0 && break
                d += 1; seen |= nx; fr = nx
            end
            ecc[v] = d
        end
        X = [v for v in 1:n if ecc[v] == minimum(ecc)]
    else
        X = [v for v in 1:n if deg[v] == maximum(deg)]
    end
    cut = sum(count(w -> bit(nb[u], w) && !(w in X), 1:n) for u in X)
    NP = Set(w for p in 1:n if deg[p] == 1 for w in 1:n if bit(nb[p], w))
    W = [v for v in 1:n if !(v in NP)]
    eW = count(((a, b),) -> a < b && bit(nb[a], b), [(a, b) for a in W for b in W])
    return cut + (2 * eW) ÷ 3, X
end

function i_brute(n, nb)
    full = (UInt32(1) << n) - 1; best = n
    for S in UInt32(1):full
        k = count_ones(S); k >= best && continue
        dom = S; indep = true; T = S
        while T != 0
            v = trailing_zeros(T) + 1
            if nb[v] & S != 0; indep = false; break; end
            dom |= nb[v]; T &= T - 1
        end
        indep && dom == full && (best = k)
    end
    return best
end

function H(m)
    edges = [(j, j + 1) for j in 1:2m]           # spine 1..2m+1, centre m+1
    n = 2m + 1
    for j in 1:2m+1
        j == m + 1 && continue
        n += 1; push!(edges, (j, n))
    end
    return n, edges
end

function F(m)
    edges = [(j, j + 1) for j in 1:m-1]
    n = m
    for j in 1:m; n += 1; push!(edges, (j, n)); end
    n += 1; push!(edges, (2, n))
    return n, edges
end

function main()
    allok = true
    for m in 2:5
        n, edges = H(m); nb = nbmasks(n, edges)
        r, C = rhs(n, nb, :center); i = i_brute(n, nb)
        ok = C == [m + 1] && r == 2 && i == 2m
        println("H_$m: n=$n right side=$r i=$i ", ok ? "OK" : "FAIL"); allok &= ok
    end
    for m in 5:8
        n, edges = F(m); nb = nbmasks(n, edges)
        r, M = rhs(n, nb, :maxdeg); i = i_brute(n, nb)
        ok = M == [2] && r == 4 && i == m
        println("F_$m: n=$n right side (C = M)=$r i=$i ", ok ? "OK" : "FAIL"); allok &= ok
    end
    n, edges = 8, [(1,5),(1,7),(2,6),(2,8),(3,7),(3,8),(4,8)]
    nb = nbmasks(n, edges); r, C = rhs(n, nb, :center); i = i_brute(n, nb)
    ok = C == [3] && r == 2 && i == 3
    println("8-vertex tree: right side=$r i=$i ", ok ? "OK" : "FAIL"); allok &= ok
    println(allok ? "ALL OK" : "SOMETHING FAILED")
    return allok
end

main() || exit(1)
