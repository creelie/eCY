# Independent Julia check of the counterexamples G_k to Written on the Wall II Conjecture 319.
# gamma, gamma_t and all minimal total dominating sets are found by brute force over vertex subsets.

function build(k::Int)
    edges = Tuple{Int,Int}[]
    for i in 1:k, j in i+1:k; push!(edges, (i, j)); end      # clique c_1..c_k = 1..k
    x = k + 1; n = k + 1
    for i in 1:k
        p = n + 1; q = n + 2; n += 2
        push!(edges, (x, p)); push!(edges, (p, q)); push!(edges, (q, i))
    end
    return n, edges
end

function nbmasks(n, edges)
    nb = zeros(UInt32, n)
    for (u, v) in edges
        nb[u] |= UInt32(1) << (v - 1); nb[v] |= UInt32(1) << (u - 1)
    end
    return nb
end

function disteven_incl(n, nb, v)
    dist = fill(-1, n); dist[v] = 0; frontier = [v]
    while !isempty(frontier)
        nxt = Int[]
        for u in frontier, w in 1:n
            if (nb[u] >> (w - 1)) & 1 == 1 && dist[w] < 0
                dist[w] = dist[u] + 1; push!(nxt, w)
            end
        end
        frontier = nxt
    end
    @assert all(dist .>= 0)
    return count(iseven, dist)
end

function analyse(n, nb)
    full = (UInt32(1) << n) - 1
    onb = zeros(UInt32, 1 << n); cnb = zeros(UInt32, 1 << n)
    for S in UInt32(1):full
        low = S & (~S + UInt32(1)); v = trailing_zeros(S) + 1
        onb[S + 1] = onb[(S ⊻ low) + 1] | nb[v]
        cnb[S + 1] = cnb[(S ⊻ low) + 1] | nb[v] | low
    end
    gamma = minimum(count_ones(S) for S in UInt32(1):full if cnb[S + 1] == full)
    sizes = Set{Int}()
    for S in UInt32(1):full
        onb[S + 1] == full || continue
        minimal = true; T = S
        while T != 0
            b = T & (~T + UInt32(1))
            if onb[(S ⊻ b) + 1] == full; minimal = false; break; end
            T ⊻= b
        end
        minimal && push!(sizes, count_ones(S))
    end
    return gamma, sort(collect(sizes))
end

function main()
    allok = true
    for k in 3:6
        n, edges = build(k)
        nb = nbmasks(n, edges)
        ev = [disteven_incl(n, nb, v) for v in 1:n]
        gamma, sizes = analyse(n, nb)
        ok = n == 3k + 1 && all(ev .== k + 1) && gamma == k + 1 && sizes[1] == k + 1 && 2k in sizes && length(sizes) > 1
        println("G_$k: n=$n max dist_even=$(maximum(ev)) gamma=$gamma gamma_t=$(sizes[1]) minimal TDS sizes=$sizes ", ok ? "OK" : "FAIL")
        allok &= ok
    end
    println(allok ? "ALL OK" : "SOMETHING FAILED")
    return allok
end

main() || exit(1)
