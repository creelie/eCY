**Counterexamples to five conjectures of Graffiti.pc on domination**, by Deep Bhattacharjee.

Written on the Wall II, the list of conjectures of the program Graffiti.pc, records Conjectures 319, 352, 358, 359 and 427 as open. The paper shows that all five are false. The counterexamples are caterpillars for Conjectures 352, 358, 359 and 427, and graphs built from complete graphs for Conjecture 319; each comes in an infinite family, and for Conjectures 358, 359 and 427 the difference between the two sides is unbounded.

| Conjecture | Smallest counterexample |
|---|---|
| 352 | the caterpillar T(3,4), 18 vertices: γ_t = 7, right side 8 |
| 358, 359 | the caterpillar Q₃, 19 vertices: γ_t = 9, right sides 19/2 |
| 319 | G₃, 10 vertices: minimal total dominating sets of sizes 4 and 6 |
| 427 | an 8-vertex tree: i = 3, right side 2 |

The proofs are by hand. Every finite claim is re-checked in C, Python, Julia and Lean 4; the Lean refutations of 352, 358 and 359 depend on no axioms, and those of 319 and 427 only on `propext`. Exhaustive searches cover all 63,242,254 trees with 3 to 24 vertices and all connected graphs with up to 11 vertices (319) or 10 vertices (427).

Files:
- `graffiti-domination-counterexamples.pdf`: the paper
- `graffiti-domination-counterexamples-tex.zip`: LaTeX source with the figures as PNG (and their TikZ sources)
- `graffiti-domination-counterexamples-arxiv.tar.gz`: LaTeX source with the figures as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
