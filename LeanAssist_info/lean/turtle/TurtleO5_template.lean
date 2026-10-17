/-!
# TurtleO5 -- exit property (obligation O5 / condition (V3)) of a pass-substitution certificate, exact

Appended after `TurtleO2_template.lean` (Z5 arithmetic, ports, frames, `portAt`, `Cert.index`).
Same specification as `verify_cert.py` (O5) and `verify_cert_exact.py` (exact re-check): for every pass family π
(type τ, parity q) with last child (slot j, entry a, exit b), n₀ = (lowest level of parity q above B) − 1,
c = δ_tail(b) − φ δ_tail(b) and y = tail(port(b, n₀)) − c,

* (affine form) tail(port(b, n₀ + 2)) = c + φ² y,
* there is an edge UW of the standard child triangle of type τ_j such that
  (i)  y lies on the open segment φ^{n₀}U — φ^{n₀}W (collinear in Z[ζ], 0 < s < 1),
  (ii) the placed edge G_j(U) G_j(W) lies on a side of the inflated parent triangle (closed segment),
  (iii) min(|y − φ^{n₀}U|, |y − φ^{n₀}W|) ≥ (1.903 + |c|) / sin 36° + 0.05
       (the + 0.05 is the safety margin of the Python checkers; the paper's condition is without it).

All arithmetic is exact.  Distances and dot products live in Z[√5]: for u, v ∈ Z[ζ],
4·Re(u v̄) = A + B√5 with A, B ∈ ℤ (cos 72° = (√5 − 1)/4, cos 144° = (−√5 − 1)/4), and the sign of A + B√5 is
decided with integers.  Square roots are not computed in Lean: Mathematica supplies a rational lower bound
s ≤ sin 36° (checked: s > 0, 8 s² ≤ 5 − √5) and for every pass a rational upper bound ĉ ≥ |c| (checked:
ĉ ≥ 0, 4 ĉ² ≥ 4 |c|²), and (iii) is checked as |y − φ^{n₀}U|² ≥ need² with the rational
need = (1.903 + ĉ) / s + 1/20, which is ≥ the right-hand side of (iii).
-/

namespace TurtleO5
open TurtleO2

/-- complex conjugate in Z[ζ]: K_j ↦ K_{−j} -/
def conj (k : Z5) : Z5 := ⟨k.a, k.e, k.d, k.c, k.b⟩

/-- product in Z[ζ] (coefficient m collects K_i L_j with i + j ≡ m mod 5), not canonicalised -/
def zmul (k l : Z5) : Z5 :=
  ⟨k.a * l.a + k.b * l.e + k.c * l.d + k.d * l.c + k.e * l.b,
   k.a * l.b + k.b * l.a + k.c * l.e + k.d * l.d + k.e * l.c,
   k.a * l.c + k.b * l.b + k.c * l.a + k.d * l.e + k.e * l.d,
   k.a * l.d + k.b * l.c + k.c * l.b + k.d * l.a + k.e * l.e,
   k.a * l.e + k.b * l.d + k.c * l.c + k.d * l.b + k.e * l.a⟩

/-- u and v are parallel as complex numbers: Im(ū v) = 0, i.e. ū v = u v̄ -/
def parallel (u v : Z5) : Bool := Z5.beq (zmul (conj u) v) (zmul u (conj v))

/-- 4·Re(u v̄) = A + B √5: with w = u v̄, 4 Re w = 4 w₀ + (√5 − 1)(w₁ + w₄) − (√5 + 1)(w₂ + w₃) -/
def dot4 (u v : Z5) : Int × Int :=
  let w := zmul u (conj v)
  (4 * w.a - w.b - w.c - w.d - w.e, w.b + w.e - w.c - w.d)

/-- a + b √5 > 0 -/
def pos5 (a b : Int) : Bool :=
  if 0 ≤ a then (if 0 ≤ b then (decide (0 < a) || decide (0 < b)) else decide (5 * (b * b) < a * a))
  else (if b ≤ 0 then false else decide (a * a < 5 * (b * b)))

/-- a + b √5 ≥ 0 -/
def nonneg5 (a b : Int) : Bool := (a == 0 && b == 0) || pos5 a b

def pos (x : Int × Int) : Bool := pos5 x.1 x.2
def nonneg (x : Int × Int) : Bool := nonneg5 x.1 x.2
def minus (x y : Int × Int) : Int × Int := (x.1 - y.1, x.2 - y.2)

/-- x on the closed segment [p, q] (q ≠ p is implied by the strict checks of the caller) -/
def onClosedSegment (p q x : Z5) : Bool :=
  let v := Z5.sub q p
  let w := Z5.sub x p
  parallel w v && nonneg (dot4 w v) && nonneg (minus (dot4 v v) (dot4 w v))

def tri3 (t : Z5 × Z5 × Z5) : List Z5 := [t.1, t.2.1, t.2.2]

/-- the three edges (V₀V₁, V₁V₂, V₂V₀) of a triangle -/
def edges : List Z5 → List (Z5 × Z5)
  | [p, q, r] => [(p, q), (q, r), (r, p)]
  | _ => []

def onSideOf (par : List Z5) (gU gW : Z5) : Bool :=
  (edges par).any (fun e => onClosedSegment e.1 e.2 gU && onClosedSegment e.1 e.2 gW)

/-- rational upper bound (P, Q) of (1.903 + ĉ) / s + 1/20 for ĉ = cn / cd and s = sn / sd -/
def need (cn cd sn sd : Int) : Int × Int :=
  (20 * (1903 * cd + 1000 * cn) * sd + 1000 * cd * sn, 20000 * cd * sn)

/-- |v| ≥ P / Q, given d2 = 4 |v|² = A + B √5 and P, Q > 0: Q² (A + B √5) − 4 P² ≥ 0 -/
def atLeast (d2 : Int × Int) (pq : Int × Int) : Bool :=
  nonneg5 (pq.2 * pq.2 * d2.1 - 4 * pq.1 * pq.1) (pq.2 * pq.2 * d2.2)

/-- conditions (i)–(iii) for the child edge (U, W) -/
def edgeOK (n0 : Nat) (y : Z5) (fr : Frame) (par : List Z5) (nd : Int × Int) (uw : Z5 × Z5) : Bool :=
  let un := phiN n0 uw.1
  let wn := phiN n0 uw.2
  let a := Z5.sub y un
  let v := Z5.sub wn un
  let b := Z5.sub y wn
  let place := fun (k : Z5) => Z5.add (rotN fr.k k) fr.t
  parallel a v && pos (dot4 a v) && pos (minus (dot4 v v) (dot4 a v)) &&
  onSideOf par (place uw.1) (place uw.2) &&
  atLeast (dot4 a a) nd && atLeast (dot4 b b) nd

/-- witness of one pass family: rational upper bound cn / cd of |c| -/
structure Wit where
  id : Nat
  cn : Int
  cd : Int
deriving Repr

def lastChild : List Child → Option Child
  | [] => none
  | [x] => some x
  | _ :: t => lastChild t

def checkPassO5 (ix : Idx) (sn sd : Int) (p : Pass) (w : Wit) : Bool :=
  p.id == w.id && decide (0 ≤ w.cn) && decide (0 < w.cd) &&
  match findPort ix p.id, lastChild p.children with
  | some pin, some ch =>
    match findFrames ix pin.col pin.sign, findPort ix ch.exit with
    | some frs, some f =>
      match frs[ch.slot]? with
      | some fr =>
        let B := ix.B
        let m1 := if (B + 1) % 2 == pin.parity then B + 1 else B + 2
        let n0 := m1 - 1
        let c := Z5.sub f.dtail (Z5.mulphi f.dtail)
        let y := Z5.sub (portAt B f n0).tail c
        let affine := Z5.beq (portAt B f (n0 + 2)).tail (Z5.add c (phi2 y))
        let cc := dot4 c c
        let cOK := nonneg5 (4 * w.cn * w.cn - cc.1 * w.cd * w.cd) (-(cc.2 * w.cd * w.cd))
        let nd := need w.cn w.cd sn sd
        let child := tri3 (stdTriangle fr.ccol fr.csign)
        let par := (tri3 (stdTriangle pin.col pin.sign)).map Z5.mulphi
        affine && cOK && (edges child).any (edgeOK n0 y fr par nd)
      | none => false
    | _, _ => false
  | _, _ => false

/-- s = sn / sd is a positive lower bound of sin 36°: 8 s² ≤ 5 − √5 -/
def sinOK (sn sd : Int) : Bool :=
  decide (0 < sn) && decide (0 < sd) && nonneg5 (5 * sd * sd - 8 * sn * sn) (-(sd * sd))

/-- O5 for every pass family; the witnesses are listed in the order of `c.passes` -/
def checkO5 (c : Cert) (sn sd : Int) (ws : List Wit) : Bool :=
  match c.index with
  | some ix => sinOK sn sd && c.passes.length == ws.length &&
      (List.zip c.passes ws).all (fun pw => checkPassO5 ix sn sd pw.1 pw.2)
  | none => false

/-- sanity: |1 + ζ|² = φ² ... 4·|1 + ζ|² = 4 + 2(√5 − 1) = 2 + 2√5, and 4 Re(1 · ζ̄) = √5 − 1 -/
theorem dot4_sample : dot4 ⟨1, 1, 0, 0, 0⟩ ⟨1, 1, 0, 0, 0⟩ = (6, 2) ∧ dot4 ⟨1, 0, 0, 0, 0⟩ ⟨0, 1, 0, 0, 0⟩ = (-1, 1) := by decide
theorem sign_sample : pos5 3 (-1) = true ∧ pos5 2 (-1) = false ∧ nonneg5 (-5) 2 = false ∧ pos5 (-4) 2 = true := by decide

end TurtleO5
