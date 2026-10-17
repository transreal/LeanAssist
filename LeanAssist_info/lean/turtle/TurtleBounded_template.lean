/-!
# TurtleBounded -- kernel-checked atlas closure and bounded runs V(P, n)

The finite part of the boundedness proof of turtle programs on Penrose rhomb tilings
(`proof_sketch.md`, `prove2.py`, `subst_fast.py`, `notebook_src/check_atlas.wl`):

* **Step 1, atlas closure** (`checkAtlas`).  An atlas entry is a marked triangle corona: a centre
  triangle `t_C` and all triangles sharing a vertex with it, given in the frame of the centre.
  The checker verifies that every entry is the corona of its centre (complete: the angles around
  each vertex of the centre sum to 360°, in integer units of 36°; every triangle touches the
  centre), that the entries are pairwise inequivalent, and, for every child `t′ ⊂ σ(t_C)`, that
  the corona of `t′` inside `σ(C)` is complete and its canonical form is one of the entries.
  Canonical form (as `ptCoronaCanon` in `lib.wl`): translate the apex of the centre to 0, rotate
  by the multiple of 36° that turns its leg AB to direction 0, pack every triangle (colour,
  centre flag, vertices) into one `Nat` and sort.  Equal forms ⇔ the marked coronas agree up to
  translation and rotation by a multiple of 36°.
* **Step 2, V(P, n)** (`checkCorona`, `checkBounded`).  For every entry `C`, every fine triangle
  `t` of `σⁿ(t_C)` (enumerated by the checker) and every heading `e ∈ Z₄`, the state
  (rhomb of `t`, `e`) lies on a closed orbit of the program `P` (states compared after whole
  cycles) whose rhombs are rhombs of the patch `σⁿ(C)`, and the set of minimal periods is the
  stated one.  The certificate written by Mathematica gives
  - the rhombs used by the orbits, each as the addresses of its two triangles in `σⁿ(C)`
    (`root · 3ⁿ + Σ slotᵢ 3ⁿ⁻ⁱ`: triangle `root` of the corona, then child `slotᵢ` at level `i`);
    the checker recomputes both triangles by `n` substitutions and requires a positively oriented
    triangle and its mirror image across the common base (`rhombOf`, the merge of `merge_v`);
  - one representative state per orbit with its period; the checker runs whole cycles of `P`
    from it, requires that the state after cycle `p` (and no earlier cycle) is the start, and that
    every S-move enters a rhomb of the certificate (otherwise: an escape, the check fails);
  - the period set.
  The states met after whole cycles are collected in a search tree (`BTree.ofList`: orbits are
  disjoint), and every start state must be found there; its period must belong to the stated set,
  and every stated period must occur.

Rhombs are `TurtleO1.Quad` (counter-clockwise, `v0` = apex of the positive half), navigation is
by directed edge keys as in the O1 checker, here with 16-bit coordinate digits (`wEdgeKey`,
range checked by `wInRange`) so that levels up to n = 10 fit.  A state is identified by the key
of its directed edge `v_e → v_{e+1}`, which is injective because no two rhombs of the table share
a directed edge (checked by `BTree.ofList`).

Appended to `TurtleO2_template.lean` and `TurtleO1_template.lean` (`Z5`, `subdivide`, `rotN`,
`unit`, `BTree`, `Tri`, `subdivideAll`, `orient`, `Quad`, `Cmd`, `Nav`); the data section
(`atlas`, `certs`, ...) is written by LeanAssist (examples/turtle_bounded.wl).  Standalone Lean 4,
no Mathlib.  `checkAtlas atlas = true` by `decide +kernel`; `checkBounded prog n atlas certs
periods = true` by `native_decide`, or by `decide +kernel` one corona per theorem.

Not checked here (facts of the argument): the entries are legal coronas (they come from
`σ⁸(sun)`), the geometric lemma corona(t′) ⊂ σ(corona(u)) for t′ ⊂ σ(u), repetitivity (F2), and
that every triangle of a tiling is paired with its mirror image (F3).
-/

namespace TurtleBounded
open TurtleO2 TurtleO1

/-! ## keys with 16-bit coordinate digits -/

/-- digit of a coordinate in (−32768, 32768) (checked by `wInRange`) -/
def wDigit (x : Int) : Nat := Int.toNat (x + 32768)

def wPointKey (k : Z5) : Nat :=
  let c := Z5.canon k
  ((wDigit c.a * 65536 + wDigit c.b) * 65536 + wDigit c.c) * 65536 + wDigit c.d

def wInRange (k : Z5) : Bool :=
  let c := Z5.canon k
  (-32768 < c.a && c.a < 32768) && (-32768 < c.b && c.b < 32768) &&
  (-32768 < c.c && c.c < 32768) && (-32768 < c.d && c.d < 32768)

/-- key of the directed edge tail → head (65536⁴ = 18446744073709551616) -/
def wEdgeKey (tail head : Z5) : Nat := wPointKey tail * 18446744073709551616 + wPointKey head

/-! ## coronas and the atlas closure (Step 1) -/

/-- angle of a marked triangle of colour `col` at its vertex A (`role` 0), B (1), C (2), in units
of 36°: acute (36°, 72°, 72°), obtuse (108°, 36°, 36°) -/
def angleUnits (col role : Nat) : Nat :=
  if col == 0 then (if role == 0 then 1 else 2) else (if role == 0 then 3 else 1)

/-- the total angle at the point `v` of the triangles of `ts` that have `v` as a vertex -/
def angleAt (ts : List Tri) (v : Z5) : Nat :=
  ts.foldl (fun s u =>
    let (col, A, B, C) := u
    s + (if Z5.beq A v then angleUnits col 0 else 0) + (if Z5.beq B v then angleUnits col 1 else 0) +
      (if Z5.beq C v then angleUnits col 2 else 0)) 0

/-- the angles of the triangles of `ts` around each vertex of `t` sum to 360° -/
def completeAt (ts : List Tri) (t : Tri) : Bool :=
  let (_, A, B, C) := t
  angleAt ts A == 10 && angleAt ts B == 10 && angleAt ts C == 10

def hasVertex (u : Tri) (v : Z5) : Bool :=
  let (_, A, B, C) := u
  Z5.beq A v || Z5.beq B v || Z5.beq C v

/-- `u` shares a vertex with `t` -/
def touches (t u : Tri) : Bool :=
  let (_, A, B, C) := t
  hasVertex u A || hasVertex u B || hasVertex u C

def triEq (t u : Tri) : Bool :=
  t.1 == u.1 && Z5.beq t.2.1 u.2.1 && Z5.beq t.2.2.1 u.2.2.1 && Z5.beq t.2.2.2 u.2.2.2

/-- the `k ∈ {0, …, 9}` with `ρᵏ · 1 = d` -/
def unitIndex (d : Z5) : Option Nat := (List.range 10).find? (fun k => Z5.beq (unit k) d)

/-- the triangle `u` translated by `−A0` and rotated by `ρʳ` -/
def toFrame (A0 : Z5) (r : Nat) (u : Tri) : Tri :=
  let (col, A, B, C) := u
  (col, rotN r (Z5.sub A A0), rotN r (Z5.sub B A0), rotN r (Z5.sub C A0))

def triOK (u : Tri) : Bool :=
  let (col, A, B, C) := u
  Nat.ble col 1 && wInRange A && wInRange B && wInRange C

/-- key of a triangle: centre flag, colour, then its three vertices (2⁶⁴ = 18446744073709551616) -/
def triKey (flag : Bool) (u : Tri) : Nat :=
  let (col, A, B, C) := u
  ((((if flag then 2 else 0) + col) * 18446744073709551616 + wPointKey A) * 18446744073709551616 +
    wPointKey B) * 18446744073709551616 + wPointKey C

/-- canonical form of the marked patch `ts` around the triangle `t` (up to translation and rotation
by multiples of 36°): the sorted keys of its triangles in the frame of `t`, `t` flagged.  `none`
when the leg AB of `t` is not a unit vector, a triangle is malformed or a triangle is repeated. -/
def canonOf (ts : List Tri) (t : Tri) : Option (List Nat) :=
  let (_, A0, B0, _) := t
  match unitIndex (Z5.sub B0 A0) with
  | none => none
  | some k =>
    let fr := ts.map (fun u => (triEq u t, toFrame A0 ((10 - k) % 10) u))
    if !(fr.all (fun x => triOK x.2)) then none
    else
      let es := BTree.msort 64 (fr.map (fun x => (triKey x.1 x.2, ())))
      if BTree.sortedStrict es && es.length == ts.length then some (es.map (·.1)) else none

/-- an atlas entry: the triangles of a corona, in the frame of the centre `tris[centre]` -/
structure Corona where
  tris : List Tri
  centre : Nat
deriving Repr

def Corona.centreTri (C : Corona) : Option Tri := C.tris[C.centre]?

/-- the entry is the corona of its centre: complete around the centre, every triangle touches it -/
def Corona.wellFormed (C : Corona) : Bool :=
  match C.centreTri with
  | none => false
  | some t => completeAt C.tris t && C.tris.all (touches t)

def Corona.form (C : Corona) : Option (List Nat) :=
  match C.centreTri with
  | none => none
  | some t => canonOf C.tris t

/-- the canonical form of the corona of `t'` inside the patch `ts`; `none` when it is incomplete -/
def coronaForm (ts : List Tri) (t' : Tri) : Option (List Nat) :=
  if completeAt ts t' then canonOf (ts.filter (touches t')) t' else none

/-- the coronas of the children of the centre inside σ(C) -/
def Corona.childForms (C : Corona) : List (Option (List Nat)) :=
  match C.centreTri with
  | none => [none]
  | some (col, A, B, Cv) => (subdivide col A B Cv).map (coronaForm (subdivideAll C.tris))

def memForm (fs : List (List Nat)) (f : List Nat) : Bool := fs.any (fun g => g == f)

def distinctForms : List (List Nat) → Bool
  | [] => true
  | f :: fs => !(memForm fs f) && distinctForms fs

/-- Step 1: every entry is the corona of its centre, the entries are pairwise inequivalent, and
the coronas of the children of every centre are complete inside σ(C) and equivalent to entries -/
def checkAtlas (atlas : List Corona) : Bool :=
  let fs := atlas.filterMap Corona.form
  atlas.length > 0 && fs.length == atlas.length && atlas.all Corona.wellFormed && distinctForms fs &&
  atlas.all (fun C => C.childForms.all (fun o =>
    match o with
    | some f => memForm fs f
    | none => false))

/-! ## search trees from certified orders

Sorting is expensive in the kernel (a fuel-bounded merge sort of 3276 entries takes about 17 s).
The certificate therefore lists the entries of every search tree in increasing key order; the
checker verifies that the keys (which it computes itself) are strictly increasing and builds the
balanced tree in one pass (`buildBal`), so the tree is a search tree.  An entry left out only
makes a lookup fail. -/

/-- lookup in a search tree, written with the recursor and `Nat.ble` / `Nat.beq` (cheap kernel
reduction; same result as `BTree.find`); `tfindImpl` is the structural twin for the compiler -/
noncomputable def tfind {α : Type} (t : BTree α) (k : Nat) : Option α :=
  BTree.rec (motive := fun _ => Option α) none
    (fun _ key v _ ihl ihr => Bool.rec ihl (Bool.rec ihr (some v) (Nat.beq key k)) (Nat.ble key k)) t

def tfindImpl {α : Type} (t : BTree α) (k : Nat) : Option α :=
  match t with
  | .leaf => none
  | .node l key v r => cond (Nat.ble key k) (cond (Nat.beq key k) (some v) (tfindImpl r k)) (tfindImpl l k)

@[csimp] theorem tfind_eq_tfindImpl : @tfind = @tfindImpl := by
  funext α t k
  induction t with
  | leaf => rfl
  | node l key v r ihl ihr =>
    show Bool.rec (motive := fun _ => Option α) (tfind l k)
      (Bool.rec (motive := fun _ => Option α) (tfind r k) (some v) (Nat.beq key k)) (Nat.ble key k) = _
    rw [ihl, ihr]
    simp only [tfindImpl]
    cases h1 : Nat.ble key k <;> cases h2 : Nat.beq key k <;> rfl

/-- the balanced tree of the first `k` entries of `xs` (in their order) and the remaining entries;
the fuel `f` bounds the depth -/
def buildBal {α : Type} : Nat → Nat → List (Nat × α) → BTree α × List (Nat × α)
  | 0, _, xs => (.leaf, xs)
  | _ + 1, 0, xs => (.leaf, xs)
  | f + 1, k + 1, xs =>
    match buildBal f (k / 2) xs with
    | (l, []) => (l, [])
    | (l, (key, v) :: rest) =>
      match buildBal f (k - k / 2) rest with
      | (r, rest') => (.node l key v r, rest')

/-- the search tree of a list of entries in strictly increasing key order; `none` otherwise -/
def treeOfSorted {α : Type} (xs : List (Nat × α)) : Option (BTree α) :=
  if BTree.sortedStrict xs then some (buildBal 64 xs.length xs).1 else none

def indexed {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: indexed (i + 1) xs

/-- the search tree of a list indexed by position -/
def indexTree {α : Type} (xs : List α) : BTree α := (buildBal 64 xs.length (indexed 0 xs)).1

/-! ## fine triangles and rhombs of σⁿ(C) -/

/-- `(root, [slot₁, …, slotₙ])` of the address `code = root · 3ⁿ + Σ slotᵢ 3ⁿ⁻ⁱ`: the triangle
`root` of the patch, then the child `slotᵢ` at level `i` (coarsest first) -/
def splitAddr : Nat → Nat → List Nat → Nat × List Nat
  | 0, c, acc => (c, acc)
  | k + 1, c, acc => splitAddr k (c / 3) (c % 3 :: acc)

/-- the descendants of `t` along the slots, one per level -/
def fresh : Tri → List Nat → Option (List Tri)
  | _, [] => some []
  | (col, A, B, C), s :: ss =>
    match (subdivide col A B C)[s]? with
    | none => none
    | some t => (fresh t ss).map (t :: ·)

/-- the descendants of `t` along the slots `ss`, reusing the descendants `as` of `t` along `os`
for the common prefix of `ss` and `os` -/
def share : Tri → List Nat → List Nat → List Tri → Option (List Tri)
  | t, s :: ss, o :: os, a :: as => if s == o then (share a ss os as).map (a :: ·) else fresh t (s :: ss)
  | t, ss, _, _ => fresh t ss

def lastOr : Tri → List Tri → Tri
  | t, [] => t
  | _, a :: as => lastOr a as

/-- the fine triangles of σⁿ(patch) with the given addresses, from the previous address (root,
slots, descendants) on: consecutive addresses share the descendants of their common prefix (the
certificate lists the addresses in increasing order; any order gives the same triangles) -/
def fineTris (ts : List Tri) (n : Nat) : List Nat → Option Nat → List Nat → List Tri → Option (List Tri)
  | [], _, _, _ => some []
  | code :: cs, prevRoot, prevSlots, prevDesc =>
    let (root, slots) := splitAddr n code []
    match ts[root]? with
    | none => none
    | some t =>
      match (if prevRoot == some root then share t slots prevSlots prevDesc else fresh t slots) with
      | none => none
      | some ds =>
        match fineTris ts n cs (some root) slots ds with
        | none => none
        | some tl => some (lastOr t ds :: tl)

/-- the rhomb (A, B, A*, C), A* = B + C − A, of a positively oriented triangle `p` = (col, A, B, C)
and its mirror image `q` = (col, A*, B, C) across the base BC; `none` otherwise -/
def rhombOf (p q : Tri) : Option Quad :=
  let (col, A, B, C) := p
  let (col', A', B', C') := q
  let As := Z5.sub (Z5.add B C) A
  if orient col A B C == 1 && col == col' && Z5.beq A' As && Z5.beq B' B && Z5.beq C' C then
    some ⟨A, B, As, C⟩
  else none

/-- the rhomb that contains the fine triangle `u` (with its mirror image across the base) -/
def rhombOfTri (u : Tri) : Option Quad :=
  let (col, A, B, C) := u
  let As := Z5.sub (Z5.add B C) A
  let o := orient col A B C
  if o == 1 then some ⟨A, B, As, C⟩ else if o == -1 then some ⟨As, B, A, C⟩ else none

def pairsOf : List Nat → List (Nat × Nat)
  | a :: b :: tl => (a, b) :: pairsOf tl
  | _ => []

def triplesOf : List Nat → List (Nat × Nat × Nat)
  | a :: b :: c :: tl => (a, b, c) :: triplesOf tl
  | _ => []

/-- the rhombs of the certificate: pairs of fine triangles (indices into the tree `ft`) -/
def rhombsOfPairs (ft : BTree Tri) : List (Nat × Nat) → Option (List Quad)
  | [] => some []
  | (a, b) :: tl =>
    match tfind ft a, tfind ft b, rhombsOfPairs ft tl with
    | some p, some q, some qs => (rhombOf p q).map (· :: qs)
    | _, _, _ => none

def Quad.wInRange (q : Quad) : Bool :=
  TurtleBounded.wInRange q.v0 && TurtleBounded.wInRange q.v1 &&
  TurtleBounded.wInRange q.v2 && TurtleBounded.wInRange q.v3

/-- a rhomb by the keys of its vertices (counter-clockwise, as in `Quad`); the keys are injective
on points in range, so the turtle runs on keys only -/
structure KQuad where
  k0 : Nat
  k1 : Nat
  k2 : Nat
  k3 : Nat
deriving Repr

def KQuad.get (q : KQuad) (e : Nat) : Nat :=
  match e % 4 with
  | 0 => q.k0
  | 1 => q.k1
  | 2 => q.k2
  | _ => q.k3

def Quad.keys (q : Quad) : KQuad := ⟨wPointKey q.v0, wPointKey q.v1, wPointKey q.v2, wPointKey q.v3⟩

/-- key of the state (rhomb, heading e): the key `wEdgeKey` of its directed edge v_e → v_{e+1} -/
def stateKey (q : KQuad) (e : Nat) : Nat := q.get e * 18446744073709551616 + q.get (e + 1)

/-- navigation table: key of the directed edge v_e → v_{e+1} ↦ (rhomb, e) -/
abbrev KNav := BTree (KQuad × Nat)

/-! ## orbits (Step 2) -/

/-- one cycle of the program from (q, e); `none` when an S-move would leave the rhombs of the table -/
def cycleRun (t : KNav) : List Cmd → KQuad → Nat → Option (KQuad × Nat)
  | [], q, e => some (q, e)
  | Cmd.S :: cs, q, e =>
    match tfind t (q.get (e + 1) * 18446744073709551616 + q.get e) with
    | none => none
    | some (q', e2) => cycleRun t cs q' ((e2 + 2) % 4)
  | Cmd.R :: cs, q, e => cycleRun t cs q ((e + 3) % 4)
  | Cmd.L :: cs, q, e => cycleRun t cs q ((e + 1) % 4)

/-- the state with key `key` is the claimed state `(o, j)` (the state after `j` cycles of orbit `o`) -/
def claimIs (st : BTree (Nat × Nat)) (key o j : Nat) : Bool :=
  match tfind st key with
  | some (o', j') => Nat.beq o' o && Nat.beq j' j
  | none => false

/-- `k` more cycles of orbit `o` from its `j`-th state (q, e): every state met before the last cycle
differs from the start (key `key0`) and is the claimed state `(o, j)`; the last cycle returns to
the start -/
def orbitOK (nav : KNav) (st : BTree (Nat × Nat)) (prog : List Cmd) (o key0 : Nat) :
    Nat → Nat → KQuad → Nat → Bool
  | 0, _, _, _ => false
  | k + 1, j, q, e =>
    match cycleRun nav prog q e with
    | none => false
    | some (q', e') =>
      let key := stateKey q' e'
      match k with
      | 0 => key == key0
      | i + 1 => !(key == key0) && claimIs st key o j && orbitOK nav st prog o key0 (i + 1) (j + 1) q' e'

/-- the orbits of the certificate, `(4 · rhomb index + e, period)`, from orbit number `o` on:
each is closed with the stated minimal period, and its states are the claimed ones -/
def orbitsOK (nav : KNav) (st : BTree (Nat × Nat)) (tr : BTree KQuad) (prog : List Cmd) :
    Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | o, (s, p) :: tl =>
    match tfind tr (s / 4) with
    | none => false
    | some q =>
      let key0 := stateKey q (s % 4)
      claimIs st key0 o 0 && orbitOK nav st prog o key0 p 1 q (s % 4) && orbitsOK nav st tr prog (o + 1) tl

/-- navigation entries (key, (rhomb, e)) of the state codes `4 · rhomb index + e` -/
def navList (tr : BTree KQuad) : List Nat → Option (List (Nat × (KQuad × Nat)))
  | [] => some []
  | s :: ss =>
    match tfind tr (s / 4), navList tr ss with
    | some q, some tl => some ((stateKey q (s % 4), (q, s % 4)) :: tl)
    | _, _ => none

/-- claimed states (key, (orbit, cycle)) of the triples `(4 · rhomb index + e, o, j)` -/
def claimList (tr : BTree KQuad) : List (Nat × Nat × Nat) → Option (List (Nat × (Nat × Nat)))
  | [] => some []
  | (s, o, j) :: ts =>
    match tfind tr (s / 4), claimList tr ts with
    | some q, some tl => some ((stateKey q (s % 4), (o, j)) :: tl)
    | _, _ => none

/-- the keys of the four states of the rhombs of the fine triangles `us` -/
def startKeys : List Tri → Option (List Nat)
  | [] => some []
  | u :: us =>
    match rhombOfTri u, startKeys us with
    | some q, some ks =>
      if Quad.wInRange q then
        let k := Quad.keys q
        some (stateKey k 0 :: stateKey k 1 :: stateKey k 2 :: stateKey k 3 :: ks)
      else none
    | _, _ => none

def sumPeriods : List (Nat × Nat) → Nat
  | [] => 0
  | (_, p) :: tl => p + sumPeriods tl

/-! ## the certificate of a corona

The lists of a certificate hold thousands of numbers; written as list literals they make
elaboration and compilation slow (the compiler spent 10 minutes on the literals of V(SSR, 7)).
They are therefore packed into a few large numbers (written in hexadecimal): a chunk is
`h + 2³² · Σ dᵢ 2^(w (i − 1))` with the header `h = 64 · count + w` (digits `d₁, …, d_count` of
`w` bits), a packed list is a list of chunks.  Division, remainder and powers of `Nat` literals
are evaluated by GMP in the kernel and in compiled code. -/

/-- the `k` lowest digits of `x` in base `b`, least significant first -/
def digitsIn (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => x % b :: digitsIn b k (x / b)

/-- the numbers of a packed list -/
def unpack : List Nat → List Nat
  | [] => []
  | c :: cs =>
    let h := c % 4294967296
    digitsIn (2 ^ (h % 64)) (h / 64) (c / 4294967296) ++ unpack cs

/-- the certificate of one corona (packed lists, see `unpack`):
* `fine`: the addresses of the fine triangles used, in increasing order;
* `rhombs`: pairs (positive triangle, mirror image) of indices into `fine`; rhomb `r` is the `r`-th pair;
* `orbits`: pairs (`4 r + e` of the representative state, period); orbit `o` is the `o`-th pair;
* `nav`: the states `4 r + e` of the navigation table, by increasing key;
* `states`: triples (`4 r + e`, `o`, `j`): the state after `j` cycles of orbit `o`, by increasing key;
* `periods` (not packed): the set of periods of the start states. -/
structure CoronaCert where
  fine : List Nat
  rhombs : List Nat
  orbits : List Nat
  nav : List Nat
  states : List Nat
  periods : List Nat
deriving Repr

/-- the rhombs of the certificate, as rhombs of σⁿ(C) with their vertex keys -/
def certRhombs (C : Corona) (n : Nat) (cert : CoronaCert) : Option (List KQuad) :=
  match fineTris C.tris n (unpack cert.fine) none [] [] with
  | none => none
  | some fs =>
    match rhombsOfPairs (indexTree fs) (pairsOf (unpack cert.rhombs)) with
    | none => none
    | some qs => if qs.all Quad.wInRange then some (qs.map Quad.keys) else none

/-- V(P, n) for one corona: every state of every rhomb of σⁿ(t_C) is a claimed state; the claimed
states are exactly the states of the orbits of the certificate (matched one to one by orbit and
cycle number); each orbit is closed with the stated minimal period inside the rhombs of σⁿ(C) of
the certificate (no escape); the periods of the start states form the stated set -/
def checkCorona (prog : List Cmd) (n : Nat) (C : Corona) (cert : CoronaCert) : Bool :=
  match C.centreTri, certRhombs C n cert with
  | some (col, A, B, Cv), some ks =>
    let tr := indexTree ks
    let cl := triplesOf (unpack cert.states)
    match navList tr (unpack cert.nav), claimList tr cl with
    | some nl, some sl =>
      match treeOfSorted nl, treeOfSorted sl with
      | some nav, some st =>
        let os := pairsOf (unpack cert.orbits)
        if !(orbitsOK nav st tr prog 0 os && cl.length == sumPeriods os) then false
        else
          match startKeys (iter subdivideAll n [(col, A, B, Cv)]) with
          | none => false
          | some sk =>
            let to := indexTree (os.map (·.2))
            let ps := sk.map (fun k => (tfind st k).bind (fun x => tfind to x.1))
            ps.all (fun o =>
              match o with
              | some p => cert.periods.contains p
              | none => false) &&
            cert.periods.all (fun p => ps.contains (some p))
      | _, _ => false
    | _, _ => false
  | _, _ => false

def allCoronas (prog : List Cmd) (n : Nat) : List Corona → List CoronaCert → Bool
  | [], [] => true
  | C :: cs, d :: ds => checkCorona prog n C d && allCoronas prog n cs ds
  | _, _ => false

def unionPeriods (certs : List CoronaCert) : List Nat :=
  certs.foldl (fun acc d => d.periods.foldl (fun a p => if a.contains p then a else p :: a) acc) []

def samePeriods (xs ys : List Nat) : Bool := xs.all ys.contains && ys.all xs.contains

/-- the computational part of the boundedness proof of `(prog)*` at level `n`: the atlas is closed
(Step 1) and V(P, n) holds for every corona of the atlas (Step 2), with the stated period set -/
def checkBounded (prog : List Cmd) (n : Nat) (atlas : List Corona) (certs : List CoronaCert)
    (periods : List Nat) : Bool :=
  checkAtlas atlas && allCoronas prog n atlas certs && samePeriods (unionPeriods certs) periods

end TurtleBounded
