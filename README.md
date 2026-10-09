# Counterexamples to five conjectures of Graffiti.pc on domination

Deep Bhattacharjee

*Written on the Wall II* (E. DeLaViña's list of the conjectures of the program Graffiti.pc)
marks Conjectures 319, 352, 358, 359 and 427 as open in its version of 26 July 2026. This
repository contains a paper proving that all five are false, and independent computer checks of
every finite claim in it, in C, Python, Julia and Lean 4.

| Conjecture | Statement (for trees on n > 2 vertices unless stated) | Counterexamples | Smallest |
|---|---|---|---|
| 352 | γ_t ≥ c⟨N(D₂) ∪ D₂⟩ + ⌈ecc_avg(M)/2⌉ | caterpillars T(a,r), a ≡ 3, r ≡ 0 (mod 4), r ≥ 4: γ_t = (a+r+7)/2, right side (a+r+9)/2 | T(3,4), 18 vertices, γ_t = 7 < 8 |
| 358 | γ_t ≥ ecc(C)/2 + iso⟨S⟩ | caterpillars Q_k, odd k ≥ 3: γ_t = 3k, right side 3k + (k−1)/4 | Q₃, 19 vertices, γ_t = 9 < 9.5 |
| 359 | γ_t ≥ ecc(C)/2 + c⟨S ∪ L⟩ | the same Q_k | Q₃ |
| 319 | graphs with n > 1: if max_v dist_even(v) = γ, then G is well totally dominated | G_k (K_k, a hub and k paths of length 3), k ≥ 3: minimal total dominating sets of sizes k+1 and 2k | G₃, 10 vertices |
| 427 | graphs with n > 3: i ≤ \|E(C, V−C)\| + ⌊(2/3)\|E⟨V−N(P)⟩\|⌋ | caterpillars H_m, m ≥ 2: i = 2m, right side 2 | an 8-vertex tree, i = 3 > 2 |

For 358, 359 and 427 the gap between the two sides is unbounded. The printed statement of 427
uses C and P without defining them; the paper reads C as the center and P as the pendant
vertices, as in the neighbouring entries of the list, and shows that the conjecture also fails
when C is read as the set M of maximum-degree vertices (caterpillars F_m, m ≥ 5, with i = m and
right side 4).

The proofs in the paper are by hand. The exhaustive searches show that T(3,4) and Q₃ are the
only counterexamples of their orders among all 63,242,254 trees with 3 to 24 vertices, that G₃
is the only counterexample to 319 among all 1,018,690,328 connected graphs with 2 to 11
vertices, and that the 8-vertex tree is the only counterexample to 427 with at most 8 vertices.

## Contents

```
paper/               main.tex (amsart) and the TikZ figures (figures/*.tex, with PDF and PNG)
wowii352/            Conjecture 352: c/search352.c, python/, julia/, lean/C352.lean, data/
wowii358/            Conjectures 358 and 359: c/search358.c, python/, julia/, lean/C358.lean, data/
wowii319/            Conjecture 319: c/c319.c, python/, julia/, lean/C319.lean, data/
wowii427/            Conjecture 427: c/c427.c, python/, julia/, lean/C427.lean, data/
scripts/run_all.sh   re-runs every check
scripts/build_paper.sh  builds dist/: the PDF, a tex.zip with PNG figures, an arXiv tarball
```

The `data/` folders hold the complete outputs of the exhaustive searches: trees with 3 to 24
vertices for 352, 358 and 359 (from nauty's `gentreeg`), connected graphs with 2 to 11 vertices
for 319 and with 4 to 10 vertices for 427 (from nauty's `geng`).

## Running the checks

```
scripts/run_all.sh                 # quick: about two minutes
FULL=1 scripts/run_all.sh          # repeats the full searches recorded in data/ (hours)
```

The C programs need a C compiler and nauty (`gentreeg`, `copyg`, `geng` on `PATH`, or `NAUTY`
set to their directory). The Python checks need Python 3 only. The Julia checks run if `julia`
is on `PATH` or `JULIA` is set. The Lean files are self-contained (Lean 4 core, no Mathlib); each
`lean/` folder pins its toolchain (`leanprover/lean4:v4.34.1`), so with
[elan](https://github.com/leanprover/elan) installed `lean C352.lean` fetches the right
version. The Lean refutations of 352, 358 and 359 depend on no axioms; those of 319 and 427
depend only on `propext`. The script prints this.

The searches for 319 on 11 vertices were run in three parts:

```
geng -cq 11 0/3 | c319;  geng -cq 11 1/3 | c319;  geng -cq 11 2/3 | c319
```

## Building the paper

```
scripts/build_paper.sh
```

Needs pdflatex (amsart, tikz, hyperref), pdftoppm, zip and tar.

## Citation

See `CITATION.cff`. The paper cites, as in its reference list,
D. Bhattacharjee, P. Mandal and U. Bhattacharya, *Resolving Erdős–Ulam monochromatic
union-closed family conjectures*, arXiv:2610.02833.

## Licence

MIT, see `LICENSE`.
