/-
  Certificate that the 18-vertex tree T(3,4) refutes Written on the Wall II Conjecture 352.

  Conjecture 352 (Graffiti.pc, 2009).  For every tree T on n > 2 vertices,
      γ_t(T) ≥ c(T) + ⌈ ecc_avg(M) / 2 ⌉,
  where γ_t is the total domination number, c(T) is the number of components of the
  subgraph induced by N(D₂) ∪ D₂ (D₂ the vertices of degree two) and ecc_avg(M) is the
  average eccentricity of the vertices of maximum degree.

  Since γ_t(T) ≥ b holds exactly when every total dominating set has at least b vertices,
  one total dominating set with fewer than b vertices refutes the conjecture.  The file is
  self-contained (Lean 4 core, no Mathlib).  `decide` checks the small facts; the exhaustive
  statement that no total dominating set has six vertices uses `native_decide`.

  Vertex labels: 0 = hub h, 1-3 its leaves, 4-6 = x₁..x₃, 7 = s₁, 8 its leaf, 9 = s₂,
  10 its leaf, 11 = s₃, 12 its leaf, 13-16 = y₁..y₄, 17 = z.
-/

def N : Nat := 18

def E : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(4,5),(5,6),(6,7),(7,8),(7,9),(9,10),(9,11),(11,12),
   (11,13),(13,14),(14,15),(15,16),(16,17)]

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

/-- eccentricity of `v`: number of breadth-first layers after `v` -/
def eccAux : Nat → List Nat → List Nat → Nat → Nat
  | 0, _, _, d => d
  | fuel + 1, seen, frontier, d =>
    let nxt := V.filter fun w => !seen.contains w && frontier.any fun u => adj u w
    if nxt.isEmpty then d else eccAux fuel (seen ++ nxt) nxt (d + 1)

def ecc (v : Nat) : Nat := eccAux N [v] [v] 0

def D2 : List Nat := V.filter fun v => deg v == 2
def X : List Nat := V.filter fun v => D2.contains v || D2.any (adj v)
def maxDeg : Nat := (V.map deg).foldl max 0
def M : List Nat := V.filter fun v => deg v == maxDeg
def eccSumM : Nat := (M.map ecc).foldl (· + ·) 0

/-- right-hand side of Conjecture 352: c(T) + ⌈ eccSumM / (2|M|) ⌉ -/
def bound : Nat := countComp X N X + (eccSumM + 2 * M.length - 1) / (2 * M.length)

def isTree : Bool := E.length == N - 1 && (reach V N [0]).length == N &&
  E.all fun e => e.1 < N && e.2 < N && e.1 != e.2

def S7 : List Nat := [0, 4, 7, 9, 11, 15, 16]

theorem isTree_true : isTree = true := by decide
theorem maxDeg_eq : maxDeg = 4 := by decide
theorem M_eq : M = [0] := by decide
theorem ecc_hub : ecc 0 = 11 := by decide
theorem comps_eq : countComp X N X = 2 := by decide
theorem bound_eq : bound = 8 := by decide
theorem S7_tds : isTDS S7 = true := by decide
theorem S7_nodup : S7.Nodup := by decide
theorem S7_len : S7.length = 7 := by decide

/-- Conjecture 352 fails for this tree: a total dominating set with 7 < 8 vertices. -/
theorem conjecture352_false :
    ¬ (∀ S : List Nat, S.Nodup → isTDS S = true → bound ≤ S.length) := by
  intro h
  have h7 := h S7 S7_nodup S7_tds
  rw [bound_eq, S7_len] at h7
  exact absurd h7 (by decide)

/-- Exactness (not needed for the refutation): no total dominating set has six or fewer vertices. -/
def subsetOf (mask : Nat) : List Nat := V.filter fun v => mask.testBit v

def noTDSUpTo6 : Bool :=
  (List.range (2 ^ N)).all fun mask => (subsetOf mask).length ≥ 7 || !isTDS (subsetOf mask)

theorem gamma_t_eq_7 : noTDSUpTo6 = true := by native_decide

#print axioms conjecture352_false
