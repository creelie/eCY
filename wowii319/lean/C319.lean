/-
  Certificate that the 10-vertex graph G₃ refutes Written on the Wall II Conjecture 319.

  Conjecture 319 (Graffiti.pc, 2007).  Let G be a connected graph with n > 1.  If the largest value of
  dist_even(v) equals the domination number γ(G), then G is well totally dominated: every minimal
  total dominating set has the same number of vertices.  dist_even(v) counts the vertices at even
  distance from v, including v itself.

  G₃: a triangle c₁c₂c₃, a hub x, and paths x - pᵢ - qᵢ - cᵢ (i = 1, 2, 3).
  Vertex labels: c₁ = 0, c₂ = 1, c₃ = 2, x = 3, p₁ = 4, q₁ = 5, p₂ = 6, q₂ = 7, p₃ = 8, q₃ = 9.

  Vertex sets are bit masks below 2¹⁰.  The file is self-contained (Lean 4 core, no Mathlib); every
  statement is checked by the kernel (`decide +kernel`).
-/

def N : Nat := 10

def E : List (Nat × Nat) :=
  [(0,1),(0,2),(1,2),(3,4),(4,5),(5,0),(3,6),(6,7),(7,1),(3,8),(8,9),(9,2)]

def V : List Nat := List.range N

def adj (u v : Nat) : Bool :=
  E.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def nbrs (v : Nat) : List Nat := V.filter (adj v)

def subsetOf (mask : Nat) : List Nat := V.filter fun v => mask.testBit v

/-- every vertex is in `S` or has a neighbour in `S` -/
def isDom (S : List Nat) : Bool := V.all fun v => S.contains v || (nbrs v).any fun u => S.contains u

/-- every vertex has a neighbour in `S` -/
def isTDS (S : List Nat) : Bool := V.all fun v => (nbrs v).any fun u => S.contains u

/-- a total dominating set none of whose vertices can be removed (total domination is preserved by
    supersets, so this is the usual notion of a minimal total dominating set) -/
def isMinimalTDS (S : List Nat) : Bool := isTDS S && S.all fun v => !isTDS (S.erase v)

/-- domination number: least size of a dominating set, over all subsets of V -/
def gammaVal : Nat :=
  (List.range (2 ^ N)).foldl
    (fun acc m => if isDom (subsetOf m) then min acc (subsetOf m).length else acc) N

/-- breadth-first distance from v to u (layers counted with fuel) -/
def distAux : Nat → List Nat → List Nat → Nat → Nat → Nat
  | 0, _, _, d, _ => d
  | fuel + 1, seen, frontier, d, u =>
    if frontier.contains u then d else
    let nxt := V.filter fun w => !seen.contains w && frontier.any fun z => adj z w
    distAux fuel (seen ++ nxt) nxt (d + 1) u

def dist (v u : Nat) : Nat := distAux N [v] [v] 0 u

def connected : Bool := V.all fun u => dist 0 u < N

def distEven (v : Nat) : Nat := (V.filter fun u => dist v u % 2 == 0).length

def maxDistEven : Nat := (V.map distEven).foldl max 0

/-- well totally dominated: all minimal total dominating sets have the same size -/
def WTD : Prop :=
  ∀ m₁ m₂ : Nat, m₁ < 2 ^ N → m₂ < 2 ^ N →
    isMinimalTDS (subsetOf m₁) = true → isMinimalTDS (subsetOf m₂) = true →
    (subsetOf m₁).length = (subsetOf m₂).length

/-- {x, p₁, c₂, c₃} = {1, 2, 3, 4}: mask 2+4+8+16 = 30;  {p₁, q₁, p₂, q₂, p₃, q₃}: mask 1008 -/
def small : Nat := 30
def large : Nat := 1008

theorem connected_true : connected = true := by decide +kernel
theorem distEven_all : V.all (fun v => distEven v == 4) = true := by decide +kernel
theorem maxDistEven_eq : maxDistEven = 4 := by decide +kernel
theorem gamma_eq : gammaVal = 4 := by decide +kernel
theorem small_minimal : isMinimalTDS (subsetOf small) = true := by decide +kernel
theorem large_minimal : isMinimalTDS (subsetOf large) = true := by decide +kernel
theorem small_len : (subsetOf small).length = 4 := by decide +kernel
theorem large_len : (subsetOf large).length = 6 := by decide +kernel

theorem not_WTD : ¬ WTD := by
  intro h
  have := h small large (by decide) (by decide) small_minimal large_minimal
  rw [small_len, large_len] at this
  exact absurd this (by decide)

/-- Conjecture 319 fails for G₃: max dist_even = γ = 4, yet G₃ is not well totally dominated. -/
theorem conjecture319_false : ¬ (maxDistEven = gammaVal → WTD) := by
  intro h
  exact not_WTD (h (by rw [maxDistEven_eq, gamma_eq]))

#print axioms conjecture319_false
