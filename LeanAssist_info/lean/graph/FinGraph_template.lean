/-!
# FinGraph -- finite simple graphs as data, with computable checks (LeanAssist)

A graph is `⟨n, edges⟩`: vertices 0 … n−1 and undirected edges (u, v) with u < v.
Mathematica (LeanAssist `LeanGraphTheorem`) writes the graph and a certificate — a colouring, a
Hamiltonian cycle, a perfect matching, a spanning tree, a separating vertex set, an Euler circuit, an
isomorphism, a clique — as Lean data, and the theorem `check … = true` is proved by `decide`
(kernel) or `native_decide` (compiled code).

Negative statements are exhaustive checks over an explicit enumeration, so the theorem says
literally "no candidate works": `notColorable g k` runs over `allColorings g.n k` (every list of
length n with entries < k), `notHamiltonian g` over `allCycles g.n` (every cyclic order starting at
vertex 0), `notIsomorphic g h` over `perms (List.range g.n)`.
-/

namespace FinGraph

structure G where
  n : Nat
  edges : List (Nat × Nat)

def adj (g : G) (u v : Nat) : Bool :=
  g.edges.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u))

/-- vertices in range, u < v for every edge (no loops), no repeated edge -/
def simple (g : G) : Bool :=
  g.edges.all (fun e => decide (e.1 < e.2) && decide (e.2 < g.n)) && decide g.edges.Nodup

def get (l : List Nat) (i : Nat) : Nat := l.getD i 0

def degree (g : G) (v : Nat) : Nat := (g.edges.filter (fun e => e.1 == v || e.2 == v)).length

def degreeSum (g : G) : Nat := ((List.range g.n).map (degree g)).foldl (· + ·) 0

/-- the handshake lemma for this graph: Σ deg v = 2 |E| -/
def handshake (g : G) : Bool := degreeSum g == 2 * g.edges.length

/-- `col` is a proper colouring with colours 0 … k−1 -/
def properColoring (g : G) (k : Nat) (col : List Nat) : Bool :=
  col.length == g.n && col.all (fun c => decide (c < k)) && g.edges.all (fun e => get col e.1 != get col e.2)

/-- every list of length n with entries < k -/
def allColorings : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, k => (allColorings n k).flatMap (fun l => (List.range k).map (fun c => c :: l))

/-- no colouring with k colours is proper -/
def notColorable (g : G) (k : Nat) : Bool := (allColorings g.n k).all (fun c => !properColoring g k c)

/-- l is a permutation of 0 … n−1 -/
def isPerm (n : Nat) (l : List Nat) : Bool := l.length == n && decide l.Nodup && l.all (fun v => decide (v < n))

/-- consecutive vertices (and the last and the first) are adjacent -/
def closedWalk (g : G) : List Nat → Bool
  | [] => false
  | v0 :: rest => (List.zip (v0 :: rest) (rest ++ [v0])).all (fun p => adj g p.1 p.2)

def hamiltonianCycle (g : G) (l : List Nat) : Bool := decide (3 ≤ g.n) && isPerm g.n l && closedWalk g l

def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (fun l => y :: l)

/-- all permutations of a list -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

/-- every cyclic order of 0 … n−1, rotated to start at 0 -/
def allCycles (n : Nat) : List (List Nat) := (perms ((List.range n).drop 1)).map (fun p => 0 :: p)

def notHamiltonian (g : G) : Bool := decide (3 ≤ g.n) && (allCycles g.n).all (fun c => !hamiltonianCycle g c)

/-- every vertex is an endpoint of exactly one edge of m, and m ⊆ E -/
def perfectMatching (g : G) (m : List (Nat × Nat)) : Bool :=
  m.all (fun e => adj g e.1 e.2) && isPerm g.n (m.flatMap (fun e => [e.1, e.2]))

/-- connected: every v ≠ r has a neighbour `parent v` with depth one less, and only r has depth 0 -/
def spanningTree (g : G) (r : Nat) (parent depth : List Nat) : Bool :=
  decide (r < g.n) && parent.length == g.n && depth.length == g.n && get depth r == 0 &&
  (List.range g.n).all (fun v => v == r || (adj g v (get parent v) && get depth (get parent v) + 1 == get depth v))

/-- disconnected: s is a non-empty proper vertex set and no edge has exactly one end in s -/
def separated (g : G) (s : List Nat) : Bool :=
  s.all (fun v => decide (v < g.n)) && decide s.Nodup && decide (0 < s.length) && decide (s.length < g.n) &&
  g.edges.all (fun e => s.contains e.1 == s.contains e.2)

def normEdge (u v : Nat) : Nat × Nat := if u ≤ v then (u, v) else (v, u)

/-- Euler circuit: a closed vertex sequence whose steps use every edge exactly once -/
def eulerCircuit (g : G) (w : List Nat) : Bool :=
  let steps := (List.zip w w.tail).map (fun p => normEdge p.1 p.2)
  simple g && w.head? == w.getLast? && decide (0 < g.edges.length) && steps.length == g.edges.length &&
  decide steps.Nodup && steps.all (fun e => g.edges.contains e)

/-- p maps vertex v of g to vertex (p v) of h; injective, edges to edges, |E(g)| = |E(h)| -/
def isomorphism (g h : G) (p : List Nat) : Bool :=
  simple g && simple h && g.n == h.n && isPerm g.n p && g.edges.length == h.edges.length &&
  g.edges.all (fun e => adj h (get p e.1) (get p e.2))

def notIsomorphic (g h : G) : Bool := (perms (List.range g.n)).all (fun p => !isomorphism g h p)

/-- l is a set of pairwise adjacent vertices -/
def clique (g : G) (l : List Nat) : Bool :=
  decide l.Nodup && l.all (fun v => decide (v < g.n)) && l.all (fun u => l.all (fun v => u == v || adj g u v))

/-- sanity checks of the template: the triangle is 3-colourable and not 2-colourable, C4 has a Hamiltonian cycle -/
theorem triangle_checks : (properColoring ⟨3, [(0, 1), (1, 2), (0, 2)]⟩ 3 [0, 1, 2] && notColorable ⟨3, [(0, 1), (1, 2), (0, 2)]⟩ 2) = true := by decide
theorem c4_checks : (hamiltonianCycle ⟨4, [(0, 1), (1, 2), (2, 3), (0, 3)]⟩ [0, 1, 2, 3] && notHamiltonian ⟨4, [(0, 1), (1, 2), (0, 2), (2, 3)]⟩) = true := by decide

end FinGraph
