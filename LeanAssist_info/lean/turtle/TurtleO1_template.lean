/-!
# TurtleO1 -- kernel-checked base simulation (obligation O1) of a pass-substitution certificate

O1 of `proof_unbounded.md`: for every pass family π of parity B mod 2, in the standard level-B
supertile X of type τ(π), the crossing port(π.in, B) leads into a rhomb owned by X; starting
there the turtle performs exactly N(π, B) S-moves, the first N − 1 between rhombs owned by X, and
the N-th is the crossing port(π.out, B), which leads to a rhomb not owned by X.

Everything is recomputed from the definitions (same specification as `verify_cert.py`,
class `Supertile`, and `lib.wl`, `ptRhombs "Ghost" -> True` / `ptNav`):

* the fine triangles of X: `subdivide` applied B times to the standard marked triangle;
* ownership: every positively oriented fine triangle (A, B, C) owns the rhomb (A, B, B + C − A, C)
  (its mirror half is the ghost half when the negative triangle is not in X);
* navigation by directed edge keys: the rhomb on the far side of the leg a → b is the one that has
  the directed edge b → a in its counter-clockwise order;
* turtle: state (rhomb, edge e ∈ Z_4, command index); S crosses edge e and takes the opposite edge
  of the rhomb entered (or exits when no owned rhomb lies there), R: e ← e − 1, L: e ← e + 1.

The orientation of a fine triangle is decided exactly: its legs AB, AC are unit vectors with
C − A = ρ^{±θ}(B − A), θ = 1 (acute) or 3 (obtuse); a triangle of any other shape makes the
check fail.  Directed edges are looked up in the balanced binary search tree `BTree` of the O2
checker on packed integer keys; the checker verifies that the keys are injective on the
coordinates in use, and `BTree.ofList` that no two owned rhombs share a directed edge and that
the tree holds every entry, so a lookup miss really means "no owned rhomb on the far side".

This file is appended to `TurtleO2_template.lean` (namespace `TurtleO2`: Z[ζ] arithmetic,
substitution, certificate structures and index, `portAt`, `BTree`); the data section (`prog`,
`o1Data`) is written by LeanAssist (`LeanTurtleBaseSimulation`, examples/turtle_port_identities.wl).
Standalone Lean 4, no Mathlib; the final theorem `checkO1 cert prog o1Data = true` is checked by
`decide +kernel`.
-/

namespace TurtleO1
open TurtleO2

/-- turtle command -/
inductive Cmd where
  | S
  | R
  | L
deriving Repr, DecidableEq

/-- a rhomb owned by the supertile: vertices in counter-clockwise order,
v0 = apex A of its positive half (A, B, C), v1 = B, v2 = A* = B + C − A, v3 = C -/
structure Quad where
  v0 : Z5
  v1 : Z5
  v2 : Z5
  v3 : Z5
deriving Repr

/-- vertex `e` (mod 4) of the rhomb -/
def Quad.get (q : Quad) (e : Nat) : Z5 :=
  match e % 4 with
  | 0 => q.v0
  | 1 => q.v1
  | 2 => q.v2
  | _ => q.v3

/-- marked fine triangle (col, A, B, C) -/
abbrev Tri := Nat × Z5 × Z5 × Z5

def subdivideAll : List Tri → List Tri
  | [] => []
  | (col, A, B, C) :: ts => subdivide col A B C ++ subdivideAll ts

/-- the fine triangles of the standard level-`B` supertile of type (col, sign) -/
def supertile (col : Nat) (sign : Int) (B : Nat) : List Tri :=
  let (A, Bv, Cv) := stdTriangle col sign
  iter subdivideAll B [(col, A, Bv, Cv)]

/-- orientation of a marked Robinson triangle, decided exactly: the legs AB, AC are unit vectors
with C − A = ρ^θ (B − A) (positive, +1) or C − A = ρ^{−θ} (B − A) (negative, −1), θ = 1 for the
acute and 3 for the obtuse triangle; 0 when the triangle has neither shape -/
def orient (col : Nat) (A B C : Z5) : Int :=
  let θ := if col == 0 then 1 else 3
  let u := Z5.sub B A
  let v := Z5.sub C A
  if Z5.beq v (rotN θ u) then 1 else if Z5.beq v (rotN (10 - θ) u) then -1 else 0

/-- the rhombs owned by the supertile: one per positively oriented fine triangle;
`none` when a fine triangle is malformed -/
def rhombsOf : List Tri → Option (List Quad)
  | [] => some []
  | (col, A, B, C) :: ts =>
    let o := orient col A B C
    if o == 0 then none
    else
      match rhombsOf ts with
      | none => none
      | some qs => if o == 1 then some (⟨A, B, Z5.sub (Z5.add B C) A, C⟩ :: qs) else some qs

/-- packed key of a canonical point whose coordinates lie in (−1024, 1024) (checked by `inRange`) -/
def digit (x : Int) : Nat := Int.toNat (x + 1024)

def pointKey (k : Z5) : Nat :=
  let c := Z5.canon k
  ((digit c.a * 2048 + digit c.b) * 2048 + digit c.c) * 2048 + digit c.d

/-- key of the directed edge tail → head (2048⁴ = 17592186044416) -/
def edgeKey (tail head : Z5) : Nat := pointKey tail * 17592186044416 + pointKey head

def inRange (k : Z5) : Bool :=
  let c := Z5.canon k
  (-1024 < c.a && c.a < 1024) && (-1024 < c.b && c.b < 1024) &&
  (-1024 < c.c && c.c < 1024) && (-1024 < c.d && c.d < 1024)

def Quad.inRange (q : Quad) : Bool :=
  TurtleO1.inRange q.v0 && TurtleO1.inRange q.v1 && TurtleO1.inRange q.v2 && TurtleO1.inRange q.v3

/-- navigation table: key of the directed edge v_e → v_{e+1} ↦ (rhomb, e) -/
abbrev Nav := BTree (Quad × Nat)

def entriesOf : List Quad → List (Nat × (Quad × Nat))
  | [] => []
  | q :: qs =>
    (edgeKey q.v0 q.v1, (q, 0)) :: (edgeKey q.v1 q.v2, (q, 1)) ::
    (edgeKey q.v2 q.v3, (q, 2)) :: (edgeKey q.v3 q.v0, (q, 3)) :: entriesOf qs

/-- the navigation table of the standard level-B supertile of type (col, sign);
`none` when a triangle is malformed, a coordinate is out of the key range, two owned rhombs share
a directed edge, or the tree lost an entry -/
def buildTable (col : Nat) (sign : Int) (B : Nat) : Option Nav :=
  match rhombsOf (supertile col sign B) with
  | none => none
  | some qs => if !(qs.all Quad.inRange) then none else BTree.ofList (entriesOf qs)

/-- state after the entry crossing (tail, head, i): the rhomb with the directed edge head → tail,
heading its opposite edge, next command i + 1; `none` when no owned rhomb lies beyond the leg or
when the rhomb left is owned as well (not an entry) -/
def entryState (t : Nav) (x : Cross) : Option (Quad × Nat × Nat) :=
  match BTree.find t (edgeKey x.head x.tail), BTree.find t (edgeKey x.tail x.head) with
  | some (q, eb), none => some (q, (eb + 2) % 4, x.i + 1)
  | _, _ => none

def nth : List Cmd → Nat → Option Cmd
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, n + 1 => nth cs n

/-- the turtle run: (rhomb q, edge e, command index ci), N S-moves so far; returns the exit crossing
(in the counter-clockwise order of the rhomb left) and the number of S-moves including the exit -/
def run (t : Nav) (prog : List Cmd) : Nat → Quad → Nat → Nat → Nat → Option (Cross × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, q, e, ci, N =>
    match nth prog (ci % prog.length) with
    | some Cmd.S =>
      let a := q.get e
      let b := q.get (e + 1)
      match BTree.find t (edgeKey b a) with
      | none => some (⟨a, b, ci % prog.length⟩, N + 1)
      | some (q', e2) => run t prog fuel q' ((e2 + 2) % 4) (ci + 1) (N + 1)
    | some Cmd.R => run t prog fuel q ((e + 3) % 4) (ci + 1) N
    | some Cmd.L => run t prog fuel q ((e + 1) % 4) (ci + 1) N
    | none => none

/-- O1 datum: pass family id and its length N(π, B) -/
structure O1Pass where
  id : Nat
  N : Nat
deriving Repr

def tableFor (tbls : List ((Nat × Int) × Nav)) (col : Nat) (sign : Int) : Option Nav :=
  (tbls.find? (fun x => x.1.1 == col && x.1.2 == sign)).map (fun x => x.2)

/-- H(B) for one pass family: entry crossing enters an owned rhomb, exactly N S-moves, the N-th is
the exit port (which leaves the owned rhombs) -/
def checkPassO1 (ix : Idx) (tbls : List ((Nat × Int) × Nav)) (prog : List Cmd) (o : O1Pass) : Bool :=
  match findPass ix o.id with
  | none => false
  | some p =>
    match findPort ix p.id, findPort ix p.out with
    | some pin, some pout =>
      pin.parity == ix.B % 2 &&
      match tableFor tbls pin.col pin.sign with
      | none => false
      | some t =>
        match entryState t (portAt ix.B pin ix.B) with
        | none => false
        | some (q, e, ci) =>
          match run t prog ((o.N + 1) * prog.length) q e ci 0 with
          | some (ex, n) => Cross.beq ex (portAt ix.B pout ix.B) && n == o.N
          | none => false
    | _, _ => false

/-- every pass family of parity B mod 2 has an O1 datum -/
def coversBase (c : Cert) (ix : Idx) (o1 : List O1Pass) : Bool :=
  c.passes.all (fun p =>
    match findPort ix p.id with
    | some pin => pin.parity != ix.B % 2 || o1.any (fun o => o.id == p.id)
    | none => false)

def types : List (Nat × Int) := [(0, 1), (0, -1), (1, 1), (1, -1)]

def checkO1 (c : Cert) (prog : List Cmd) (o1 : List O1Pass) : Bool :=
  match c.index with
  | none => false
  | some ix =>
    prog.length > 0 && prog.any (fun x => x == Cmd.S) &&
    let tbls := types.filterMap (fun ty => (buildTable ty.1 ty.2 ix.B).map (fun t => (ty, t)))
    coversBase c ix o1 && o1.all (checkPassO1 ix tbls prog)

end TurtleO1
