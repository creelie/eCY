/-
  Certificate that the 19-vertex caterpillar Q₃ refutes Written on the Wall II Conjectures 358 and 359.

  For a tree T on n > 2 vertices, with C the center, S the support vertices and L the leaves:
    Conjecture 358:  γ_t(T) ≥ ecc(C)/2 + (number of isolated vertices of ⟨S⟩),
    Conjecture 359:  γ_t(T) ≥ ecc(C)/2 + (number of components of ⟨S ∪ L⟩),
  where ecc(C) is the largest distance from a vertex outside C to the set C.
  We use the equivalent integer forms  2·|D| ≥ ecc(C) + 2·(count)  for every total dominating set D.

  One total dominating set that is too small refutes each conjecture.  The file is self-contained
  (Lean 4 core, no Mathlib).  `decide` checks the refutations; the exhaustive statement that no total
  dominating set has eight vertices (so γ_t = 9) uses `native_decide` and is not needed for them.

  Vertex labels: blocks (s₁, c₁, s₁') = (0, 1, 2), (s₂, c₂, s₂') = (7, 8, 9), (s₃, c₃, s₃') = (14, 15, 16);
  leaves 3, 4, 10, 11, 17, 18; degree-two connectors u₁ = 5, w₁ = 6, u₂ = 12, w₂ = 13.
-/

def N : Nat := 19

def E : List (Nat × Nat) :=
  [(0,1),(1,2),(0,3),(2,4),(2,5),(5,6),(6,7),(7,8),(8,9),(7,10),(9,11),(9,12),
   (12,13),(13,14),(14,15),(15,16),(14,17),(16,18)]

def V : List Nat := List.range N

def adj (u v : Nat) : Bool :=
  E.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def nbrs (v : Nat) : List Nat := V.filter (adj v)

def deg (v : Nat) : Nat := (nbrs v).length

/-- every vertex has a neighbour in `S` -/
def isTDS (S : List Nat) : Bool := V.all fun v => (nbrs v).any fun u => S.contains u

/-- vertices reachable from `seen` inside `X` (breadth-first, with fuel) -/
def reach (X : List Nat) : Nat → List Nat → List Nat
  | 0, seen => seen
  | fuel + 1, seen =>
    let nxt := X.filter fun w => !seen.contains w && seen.any fun u => adj u w
    if nxt.isEmpty then seen else reach X fuel (seen ++ nxt)

/-- number of components of the subgraph induced by `X` -/
def countComp (X : List Nat) : Nat → List Nat → Nat
  | 0, _ => 0
  | fuel + 1, rem =>
    match rem with
    | [] => 0
    | v :: _ =>
      let C := reach X N [v]
      1 + countComp X fuel (rem.filter fun w => !C.contains w)

/-- number of breadth-first layers after the start set (its eccentricity as a set) -/
def eccAux : Nat → List Nat → List Nat → Nat → Nat
  | 0, _, _, d => d
  | fuel + 1, seen, frontier, d =>
    let nxt := V.filter fun w => !seen.contains w && frontier.any fun u => adj u w
    if nxt.isEmpty then d else eccAux fuel (seen ++ nxt) nxt (d + 1)

def ecc (v : Nat) : Nat := eccAux N [v] [v] 0
def rad : Nat := (V.map ecc).foldl min N
def C : List Nat := V.filter fun v => ecc v == rad
def eccC : Nat := eccAux N C C 0

def L : List Nat := V.filter fun v => deg v == 1
def S : List Nat := V.filter fun v => (nbrs v).any fun u => deg u == 1
def isolatesS : Nat := (S.filter fun v => !(nbrs v).any fun u => S.contains u).length
def compsSL : Nat := countComp (S ++ L) N (S ++ L)

def isTree : Bool := E.length == N - 1 && (reach V N [0]).length == N &&
  E.all fun e => e.1 < N && e.2 < N && e.1 != e.2

def D9 : List Nat := [0, 1, 2, 7, 8, 9, 14, 15, 16]

theorem isTree_true : isTree = true := by decide
theorem C_eq : C = [8] := by decide
theorem eccC_eq : eccC = 7 := by decide
theorem S_eq : S = [0, 2, 7, 9, 14, 16] := by decide
theorem isolates_eq : isolatesS = 6 := by decide
theorem comps_eq : compsSL = 6 := by decide
theorem D9_tds : isTDS D9 = true := by decide
theorem D9_nodup : D9.Nodup := by decide
theorem D9_len : D9.length = 9 := by decide

/-- Conjecture 358 fails for Q₃: a total dominating set with 2·9 = 18 < 7 + 2·6 = 19. -/
theorem conjecture358_false :
    ¬ (∀ D : List Nat, D.Nodup → isTDS D = true → eccC + 2 * isolatesS ≤ 2 * D.length) := by
  intro h
  have h9 := h D9 D9_nodup D9_tds
  rw [eccC_eq, isolates_eq, D9_len] at h9
  exact absurd h9 (by decide)

/-- Conjecture 359 fails for Q₃: a total dominating set with 2·9 = 18 < 7 + 2·6 = 19. -/
theorem conjecture359_false :
    ¬ (∀ D : List Nat, D.Nodup → isTDS D = true → eccC + 2 * compsSL ≤ 2 * D.length) := by
  intro h
  have h9 := h D9 D9_nodup D9_tds
  rw [eccC_eq, comps_eq, D9_len] at h9
  exact absurd h9 (by decide)

/-- Exactness (not needed for the refutations): no total dominating set has eight or fewer vertices. -/
def subsetOf (mask : Nat) : List Nat := V.filter fun v => mask.testBit v

def noTDSUpTo8 : Bool :=
  (List.range (2 ^ N)).all fun mask => (subsetOf mask).length ≥ 9 || !isTDS (subsetOf mask)

theorem gamma_t_eq_9 : noTDSUpTo8 = true := by native_decide

#print axioms conjecture358_false
#print axioms conjecture359_false
