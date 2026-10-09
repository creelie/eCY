# Independent Julia check of the counterexamples T(a, r) to Written on the Wall II Conjecture 352.
# gamma_t is computed by brute force over all vertex subsets (bitmasks), so it does not rely on
# the explicit set or on the path-counting lower bound used in the paper.

function build(a::Int, r::Int)
    edges = Tuple{Int,Int}[]
    n = 0
    new() = (n += 1; n)          # 1-based vertex labels
    h = new()
    for _ in 1:3; push!(edges, (h, new())); end
    prev = h
    for _ in 1:a; x = new(); push!(edges, (prev, x)); prev = x; end
    for _ in 1:3
        s = new(); push!(edges, (prev, s)); prev = s
        push!(edges, (s, new()))
    end
    for _ in 1:r; y = new(); push!(edges, (prev, y)); prev = y; end
    push!(edges, (prev, new()))
    return n, edges
end

function nbmasks(n, edges)
    nb = zeros(UInt64, n)
    for (u, v) in edges
        nb[u] |= UInt64(1) << (v - 1)
        nb[v] |= UInt64(1) << (u - 1)
    end
    return nb
end

function gamma_t_brute(n, nb)
    full = (UInt64(1) << n) - 1
    best = n
    for S in UInt64(1):full
        k = count_ones(S)
        k >= best && continue
        cov = UInt64(0)
        T = S
        while T != 0
            i = trailing_zeros(T)
            cov |= nb[i + 1]
            T &= T - 1
        end
        cov == full && (best = k)
    end
    return best
end

function bfs_dist(n, nb, src)
    dist = fill(-1, n); dist[src] = 0
    frontier = [src]
    while !isempty(frontier)
        nxt = Int[]
        for u in frontier, w in 1:n
            if (nb[u] >> (w - 1)) & 1 == 1 && dist[w] < 0
                dist[w] = dist[u] + 1; push!(nxt, w)
            end
        end
        frontier = nxt
    end
    return dist
end

function components(n, nb, S::Vector{Int})
    inS = falses(n); for v in S; inS[v] = true; end
    seen = falses(n); c = 0
    for s in S
        seen[s] && continue
        c += 1; stack = [s]; seen[s] = true
        while !isempty(stack)
            u = pop!(stack)
            for w in 1:n
                if (nb[u] >> (w - 1)) & 1 == 1 && inS[w] && !seen[w]
                    seen[w] = true; push!(stack, w)
                end
            end
        end
    end
    return c
end

function bound352(n, nb)
    deg = [count_ones(nb[v]) for v in 1:n]
    Δ = maximum(deg)
    M = [v for v in 1:n if deg[v] == Δ]
    eccsum = sum(maximum(bfs_dist(n, nb, v)) for v in M)
    D2 = [v for v in 1:n if deg[v] == 2]
    X = Set(D2)
    for v in D2, w in 1:n
        (nb[v] >> (w - 1)) & 1 == 1 && push!(X, w)
    end
    c = components(n, nb, collect(X))
    half = cld(eccsum, 2 * length(M))
    return c, eccsum, length(M), c + half
end

function main()
    allok = true
    for (a, r) in [(3, 4), (3, 8), (7, 4), (3, 12), (7, 8), (11, 4)]
        n, edges = build(a, r)
        @assert length(edges) == n - 1
        nb = nbmasks(n, edges)
        @assert all(bfs_dist(n, nb, 1) .>= 0)          # connected, so a tree
        c, eccsum, sizeM, bound = bound352(n, nb)
        gt = gamma_t_brute(n, nb)
        ok = gt == (a + r + 7) ÷ 2 && bound == (a + r + 9) ÷ 2 && gt < bound
        println("T($a,$r): n=$n gamma_t=$gt components=$c ecc(M)=$eccsum |M|=$sizeM bound=$bound ", ok ? "OK" : "FAIL")
        allok &= ok
    end
    println(allok ? "ALL OK" : "SOMETHING FAILED")
    return allok
end

main() || exit(1)
