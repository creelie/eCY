/-
  Certificates that Written on the Wall II Conjecture 427 fails.

  Conjecture 427 (Graffiti.pc, 2010), as printed: for a connected graph G on n > 3 vertices,
      i(G) ≤ |E(C, V - C)| + ⌊(2/3)·|E(G[V - N(P)])|⌋,
  where i(G) is the independent domination number and P the set of pendant vertices.  The statement
  does not define C; we refute it when C is the center (`T8`, 8 vertices) and when C is the set of
  vertices of maximum degree (`F5`, 11 vertices).

  Vertex sets are bit masks.  Self-contained (Lean 4 core, no Mathlib); every statement is checked by
  the kernel (`decide +kernel`).
-/

structure Graph where
  N : Nat
  E : List (Nat × Nat)

namespace Graph
variable (g : Graph)

def V : List Nat := List.range g.N
def adj (u v : Nat) : Bool := g.E.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)
def nbrs (v : Nat) : List Nat := g.V.filter (g.adj v)
def deg (v : Nat) : Nat := (g.nbrs v).length
def subsetOf (mask : Nat) : List Nat := g.V.filter fun v => mask.testBit v

def isIndepDom (S : List Nat) : Bool :=
  (g.V.all fun v => S.contains v || (g.nbrs v).any fun u => S.contains u) &&
  (S.all fun u => S.all fun w => !g.adj u w)

/-- independent domination number: least size of an independent dominating set (over all subsets) -/
def iVal : Nat :=
  (List.range (2 ^ g.N)).foldl
    (fun acc m => if g.isIndepDom (g.subsetOf m) then min acc (g.subsetOf m).length else acc) g.N

def eccAux : Nat → List Nat → List Nat → Nat → Nat
  | 0, _, _, d => d
  | fuel + 1, seen, frontier, d =>
    let nxt := g.V.filter fun w => !seen.contains w && frontier.any fun u => g.adj u w
    if nxt.isEmpty then d else eccAux fuel (seen ++ nxt) nxt (d + 1)

def ecc (v : Nat) : Nat := g.eccAux g.N [v] [v] 0
def rad : Nat := (g.V.map g.ecc).foldl min g.N
def center : List Nat := g.V.filter fun v => g.ecc v == g.rad
def maxDeg : Nat := (g.V.map g.deg).foldl max 0
def M : List Nat := g.V.filter fun v => g.deg v == g.maxDeg
def P : List Nat := g.V.filter fun v => g.deg v == 1
def NP : List Nat := g.V.filter fun v => (g.nbrs v).any fun u => g.deg u == 1
def W : List Nat := g.V.filter fun v => !g.NP.contains v
def edgesIn (X : List Nat) : Nat := (g.E.filter fun e => X.contains e.1 && X.contains e.2).length
def cut (X : List Nat) : Nat := (g.E.filter fun e => X.contains e.1 != X.contains e.2).length

/-- right side of Conjecture 427 with the set X in the role of C -/
def rhs (X : List Nat) : Nat := g.cut X + (2 * g.edgesIn g.W) / 3

/-- the graph is connected: every vertex is reached from 0 by breadth-first search -/
def reach : Nat → List Nat → List Nat
  | 0, seen => seen
  | fuel + 1, seen =>
    let nxt := g.V.filter fun w => !seen.contains w && seen.any fun u => g.adj u w
    if nxt.isEmpty then seen else reach fuel (seen ++ nxt)
def isConnected : Bool := (g.reach g.N [0]).length == g.N

end Graph

/-- 8 vertices: the path 4-0-6-2-7-1-5 with a pendant vertex 3 at 7 (a tree; center {2}) -/
def T8 : Graph := ⟨8, [(0,4),(0,6),(1,5),(1,7),(2,6),(2,7),(3,7)]⟩

/-- 11 vertices: the path 0-1-2-3-4 with a pendant at each vertex and a second pendant at 1 -/
def F5 : Graph := ⟨11, [(0,1),(1,2),(2,3),(3,4),(0,5),(1,6),(2,7),(3,8),(4,9),(1,10)]⟩

theorem T8_connected : T8.isConnected = true := by decide +kernel
theorem T8_center : T8.center = [2] := by decide +kernel
theorem T8_rhs : T8.rhs T8.center = 2 := by decide +kernel
theorem T8_i : T8.iVal = 3 := by decide +kernel

theorem F5_connected : F5.isConnected = true := by decide +kernel
theorem F5_M : F5.M = [1] := by decide +kernel
theorem F5_rhs : F5.rhs F5.M = 4 := by decide +kernel
theorem F5_i : F5.iVal = 5 := by decide +kernel

/-- Conjecture 427 with C the center fails for T8: i = 3 > 2. -/
theorem conjecture427_center_false : ¬ (T8.iVal ≤ T8.rhs T8.center) := by
  rw [T8_i, T8_rhs]; decide

/-- Conjecture 427 with C the set of maximum-degree vertices fails for F5: i = 5 > 4. -/
theorem conjecture427_maxdeg_false : ¬ (F5.iVal ≤ F5.rhs F5.M) := by
  rw [F5_i, F5_rhs]; decide

#print axioms conjecture427_center_false
#print axioms conjecture427_maxdeg_false
