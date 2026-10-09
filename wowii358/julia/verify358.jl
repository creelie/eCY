# Independent Julia check of the counterexamples Q_k to Written on the Wall II Conjectures 358 and 359.
# For Q_3 (19 vertices) gamma_t is computed by brute force over all 2^19 vertex subsets; for larger k by a
# tree dynamic programme written separately from the C and Python ones. All comparisons are exact (Rational).

function build(k::Int)
    edges = Tuple{Int,Int}[]
    n = 0
    new() = (n += 1; n)
    blocks = NTuple{3,Int}[]
    prev = 0
    for j in 1:k
        if prev != 0
            u = new(); w = new()
            push!(edges, (prev, u)); push!(edges, (u, w)); prev = w
        end
        s1 = new(); c = new(); s2 = new()
        prev != 0 && push!(edges, (prev, s1))
        push!(edges, (s1, c)); push!(edges, (c, s2))
        for s in (s1, s2)
            push!(edges, (s, new()))
        end
        push!(blocks, (s1, c, s2)); prev = s2
    end
    return n, edges, blocks
end

function neighbours(n, edges)
    nb = [Int[] for _ in 1:n]
    for (u, v) in edges
        push!(nb[u], v); push!(nb[v], u)
    end
    return nb
end

function bfs(nb, sources)
    dist = fill(-1, length(nb))
    for s in sources; dist[s] = 0; end
    frontier = collect(sources)
    while !isempty(frontier)
        nxt = Int[]
        for u in frontier, w in nb[u]
            if dist[w] < 0
                dist[w] = dist[u] + 1; push!(nxt, w)
            end
        end
        frontier = nxt
    end
    return dist
end

function gamma_t_brute(n, nb)
    mask = zeros(UInt64, n)
    for v in 1:n, w in nb[v]; mask[v] |= UInt64(1) << (w - 1); end
    full = (UInt64(1) << n) - 1
    best = n
    for S in UInt64(1):full
        k = count_ones(S)
        k >= best && continue
        cov = UInt64(0); T = S
        while T != 0
            i = trailing_zeros(T); cov |= mask[i + 1]; T &= T - 1
        end
        cov == full && (best = k)
    end
    return best
end

# minimum total dominating set of a tree: f[v][s] for s = (inD, dominated-from-below)
function gamma_t_dp(n, nb)
    INF = typemax(Int) ÷ 4
    parent = zeros(Int, n); order = [1]; parent[1] = -1
    i = 1
    while i <= length(order)
        u = order[i]; i += 1
        for w in nb[u]
            if parent[w] == 0 && w != 1
                parent[w] = u; push!(order, w)
            end
        end
    end
    f = Dict{Int,NTuple{4,Int}}()   # (in&dom, in&undom, out&dom, out&undom)
    for v in reverse(order)
        ch = [w for w in nb[v] if w != parent[v]]
        # v in D
        none_in, some_in = 0, INF
        for w in ch
            a, b, c, e = f[w]
            o = min(c, e); x = min(a, b)
            none_in, some_in = none_in + o, min(some_in + min(o, x), none_in + x)
        end
        A, B = 1 + some_in, 1 + none_in
        # v not in D
        none_in, some_in = 0, INF
        for w in ch
            a, b, c, e = f[w]
            none_in, some_in = none_in + c, min(some_in + min(c, a), none_in + a)
        end
        f[v] = (min(A, INF), min(B, INF), min(some_in, INF), min(none_in, INF))
    end
    a, b, c, e = f[1]
    return min(a, c)
end

function main()
    allok = true
    for k in (3, 5, 7, 9, 11)
        n, edges, blocks = build(k)
        nb = neighbours(n, edges)
        @assert length(edges) == n - 1 && all(bfs(nb, [1]) .>= 0)
        ecc = [maximum(bfs(nb, [v])) for v in 1:n]
        C = findall(==(minimum(ecc)), ecc)
        d = bfs(nb, C); eccC = maximum(d)
        L = [v for v in 1:n if length(nb[v]) == 1]
        S = sort(unique([nb[v][1] for v in L]))
        iso = count(s -> isempty(intersect(nb[s], S)), S)
        # components of <S u L>: every leaf hangs on its support vertex, so count the supports' groups
        X = union(S, L); seen = Set{Int}(); comps = 0
        for x in X
            x in seen && continue
            comps += 1; stack = [x]; push!(seen, x)
            while !isempty(stack)
                u = pop!(stack)
                for w in nb[u]
                    if w in X && !(w in seen); push!(seen, w); push!(stack, w); end
                end
            end
        end
        gt = k == 3 ? gamma_t_brute(n, nb) : gamma_t_dp(n, nb)
        k == 3 && @assert gt == gamma_t_dp(n, nb)
        b358 = eccC // 2 + iso; b359 = eccC // 2 + comps
        ok = n == 7k - 2 && length(C) == 1 && eccC == (5k - 1) ÷ 2 && iso == 2k && comps == 2k &&
             gt == 3k && gt < b358 && gt < b359 && b358 - gt == (k - 1) // 4
        println("Q_$k: n=$n ecc(C)=$eccC isolates=$iso components=$comps gamma_t=$gt ",
                k == 3 ? "(brute force) " : "(tree DP) ", "bound=$b358 ", ok ? "OK" : "FAIL")
        allok &= ok
    end
    println(allok ? "ALL OK" : "SOMETHING FAILED")
    return allok
end

main() || exit(1)
