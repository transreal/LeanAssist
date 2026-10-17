/-!
# TurtleO46 -- kernel-checked growth (O4) and exact recurrence (O6) of a pass-substitution certificate

O4 and the computational part of O6 of `proof_unbounded.md`: the lengths
`N(π, m)` of the pass families are defined by `N(π, B)` from the base simulation (O1, the data
`o1Data`) and `N(π, m+1) = Σ_children N(child, m)`.  Along one parity class
`N(m+2) = M N(m)` with the two-level expansion matrix `M` (entry `(π, π')` = multiplicity of
`π'` among the grandchildren of `π`).  For every root family `r` listed in `o6Data` the checker
verifies, with `K = dim M + 3` steps from the first level `m₀` of its parity class:

* O4 (growth): `r` occurs `μ ≥ 1` times in its own two-level expansion, which has more than `μ`
  members (hence `N(r, m+2) ≥ μ N(r, m) + 1` and `N(r, m) → ∞`);
* the two-level identity `N(π, m₀+2s+2) = M N(π, m₀+2s)` for every family `π` of the parity class
  (the vector two levels up, computed level by level, equals the grandchildren sums), `s < K`;
* O6 (closed recurrence): `N(r, m₀) = N₀` and `N(r, m+2) = a N(r, m) + b` for `s < K`.

By `CayleyHamiltonRecurrence.affine_of_initial` (Mathlib) the closed recurrence then holds at
every level of the parity class (`dim M + 1` consecutive steps suffice).

All lengths are recomputed level by level from the pass table (no `N` of the certificate JSON
is trusted).  The families of each parity class are put once into a table (`BTree` on the family
ids, value = the entry ids of the children); the lengths of a level are a tree of the same shape,
computed from the previous level by mapping over the table, and the iteration is a fold that
passes on only the current level.  The O1 data must give `N(π, B)` for every family of parity
`B mod 2` (`baseVec`).  Appended to `TurtleO2_template.lean` and `TurtleO1_template.lean` (`Cert`,
`Idx`, `findPort`, `findPass`, `BTree`, `O1Pass`); the data section (`cert`, `o1Data`, `o6Data`) is
written by LeanAssist (`LeanTurtleRecurrence`, examples/turtle_port_identities.wl).  Standalone
Lean 4, no Mathlib; the theorem `checkO46 cert o1Data o6Data = true` is checked by `decide +kernel`.

Kernel cost: `decide +kernel` keeps every intermediate term of the evaluation in its caches until
the end of the declaration, so its memory grows with the total number of reduction steps, not
with the live data.  The functions evaluated at every level (`get`, `sumOf`, `step`, `twoLevelOK`)
are therefore written with the recursors `BTree.rec` / `List.rec` and the primitive
`Nat.ble` / `Nat.beq` / `Nat.add`: a tree node then costs a few iota steps, about a quarter of
the memory of structural recursion (`brecOn`) with `if`.  The code generator does not support
recursors, so each of them has a structural twin (`…Impl`) that branches in the same way, and a
`@[csimp]` theorem proves the two equal: `native_decide` and `#eval` run the twins.
cert_SRSRSRSRSSR (dim M = 390, 393 steps): 160 s and 15 GB with `decide +kernel` (the previous
version, which rebuilt a sorted tree at every level, exceeded 40 GB).
-/

namespace TurtleO46
open TurtleO2 TurtleO1

/-- O6 datum: a root family, the closed recurrence `N(m+2) = a N(m) + b` of its lengths along its
parity class, and its length `N₀` at the first level `m₀ = R(q)` of the class -/
structure O6Root where
  id : Nat
  a : Int
  b : Int
  N0 : Nat
deriving Repr

/-- the lengths of the families of one parity class at one level, indexed by family id -/
abbrev Lengths := BTree Nat

/-- the families of one parity class: family id ↦ entry ids of its children (with multiplicity) -/
abbrev Table := BTree (List Nat)

/-- the parity of a pass family (that of its entry port) -/
def famParity (ix : Idx) (p : Pass) : Option Nat :=
  (findPort ix p.id).map (·.parity)

/-- the families of parity `q`, in the order of the table -/
def familiesOf (c : Cert) (ix : Idx) (q : Nat) : List Pass :=
  c.passes.filter (fun p => famParity ix p == some q)

/-- the table of the families of parity `q`; `none` when two families share an id -/
def tableOf (c : Cert) (ix : Idx) (q : Nat) : Option Table :=
  BTree.ofList ((familiesOf c ix q).map (fun p => (p.id, p.children.map (·.entry))))

/-- every id of the list is a family of the table `u` -/
def keysIn (u : Table) : List Nat → Bool
  | [] => true
  | id :: ids => (BTree.find u id).isSome && keysIn u ids

/-- the children of every family of the table are families of the table `u` -/
def closedIn (u : Table) : Table → Bool
  | .leaf => true
  | .node l _ chs r => keysIn u chs && closedIn u l && closedIn u r

/-! ## evaluated at every level: recursors for the kernel, structural twins for the compiler -/

/-- the length of family `id` (0 when absent: only used for ids checked by `closedIn`) -/
noncomputable def get (v : Lengths) (id : Nat) : Nat :=
  BTree.rec (motive := fun _ => Nat) 0
    (fun _ key val _ ihl ihr => Bool.rec ihl (Bool.rec ihr val (Nat.beq key id)) (Nat.ble key id)) v

def getImpl (v : Lengths) (id : Nat) : Nat :=
  match v with
  | .leaf => 0
  | .node l key val r => cond (Nat.ble key id) (cond (Nat.beq key id) val (getImpl r id)) (getImpl l id)

@[csimp] theorem get_eq_getImpl : @get = @getImpl := by
  funext v id
  induction v with
  | leaf => rfl
  | node l key val r ihl ihr =>
    show Bool.rec (motive := fun _ => Nat) (get l id)
      (Bool.rec (motive := fun _ => Nat) (get r id) val (Nat.beq key id)) (Nat.ble key id) = _
    rw [ihl, ihr]
    simp only [getImpl]
    cases h1 : Nat.ble key id <;> cases h2 : Nat.beq key id <;> rfl

/-- Σ of the lengths of a list of family ids (with multiplicity) -/
noncomputable def sumOf (v : Lengths) (ids : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun id _ ih => Nat.add (get v id) ih) ids

def sumOfImpl (v : Lengths) : List Nat → Nat
  | [] => 0
  | id :: ids => Nat.add (get v id) (sumOfImpl v ids)

@[csimp] theorem sumOf_eq_sumOfImpl : @sumOf = @sumOfImpl := by
  funext v ids
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    show Nat.add (get v id) (sumOf v ids) = _
    rw [ih]
    rfl

/-- the lengths one level up, on the table `t` of the other parity class:
`N(π, m+1) = Σ_children N(child, m)`; the result has the shape of `t` -/
noncomputable def step (v : Lengths) (t : Table) : Lengths :=
  BTree.rec (motive := fun _ => Lengths) .leaf
    (fun _ k chs _ ihl ihr => .node ihl k (sumOf v chs) ihr) t

def stepImpl (v : Lengths) : Table → Lengths
  | .leaf => .leaf
  | .node l k chs r => .node (stepImpl v l) k (sumOf v chs) (stepImpl v r)

@[csimp] theorem step_eq_stepImpl : @step = @stepImpl := by
  funext v t
  induction t with
  | leaf => rfl
  | node l k chs r ihl ihr =>
    show BTree.node (step v l) k (sumOf v chs) (step v r) = _
    rw [ihl, ihr]
    rfl

/-- `N(π, m+2) = M N(π, m)` for every family `π`: the vector `v2` two levels up equals the
grandchildren sums of the vector `v` (`g` = rows of `M`, same shape as `v2`) -/
noncomputable def twoLevelOK (v : Lengths) (g : Table) : Lengths → Bool :=
  BTree.rec (motive := fun _ => Lengths → Bool)
    (fun v2 => BTree.casesOn (motive := fun _ => Bool) v2 true (fun _ _ _ _ => false))
    (fun _ k gs _ ihl ihr v2 => BTree.casesOn (motive := fun _ => Bool) v2 false
      (fun l2 k2 n2 r2 =>
        Bool.rec false (Bool.rec false (Bool.rec false (ihr r2) (ihl l2)) (Nat.beq (sumOf v gs) n2))
          (Nat.beq k k2))) g

def twoLevelOKImpl (v : Lengths) : Table → Lengths → Bool
  | .leaf, .leaf => true
  | .leaf, .node .. => false
  | .node .., .leaf => false
  | .node l k gs r, .node l2 k2 n2 r2 =>
    cond (Nat.beq k k2)
      (cond (Nat.beq (sumOf v gs) n2) (cond (twoLevelOKImpl v l l2) (twoLevelOKImpl v r r2) false) false)
      false

@[csimp] theorem twoLevelOK_eq_twoLevelOKImpl : @twoLevelOK = @twoLevelOKImpl := by
  funext v g v2
  induction g generalizing v2 with
  | leaf => cases v2 <;> rfl
  | node l k gs r ihl ihr =>
    cases v2 with
    | leaf => rfl
    | node l2 k2 n2 r2 =>
      show Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (twoLevelOK v r r2) (twoLevelOK v l l2))
            (Nat.beq (sumOf v gs) n2)) (Nat.beq k k2) = _
      rw [ihl, ihr]
      simp only [twoLevelOKImpl]
      cases h1 : Nat.beq k k2 <;> cases h2 : Nat.beq (sumOf v gs) n2 <;> cases h3 : twoLevelOKImpl v l l2 <;> rfl

/-! ## the tables, the base level and the iteration -/

def childrenIn (u : Table) (id : Nat) : List Nat :=
  match BTree.find u id with
  | some l => l
  | none => []

def grandList (u : Table) : List Nat → List Nat
  | [] => []
  | ch :: chs => childrenIn u ch ++ grandList u chs

/-- the grandchildren (with multiplicity) of every family of `t`, i.e. the rows of the two-level
expansion matrix `M`; same shape as `t` -/
def grand (u : Table) : Table → Table
  | .leaf => .leaf
  | .node l k chs r => .node (grand u l) k (grandList u chs) (grand u r)

/-- the lengths at level B on the table of the families of parity B mod 2, from the O1 data;
`none` when a family has no O1 datum -/
def baseVec (o1t : BTree Nat) : Table → Option Lengths
  | .leaf => some .leaf
  | .node l k _ r =>
    match baseVec o1t l, BTree.find o1t k, baseVec o1t r with
    | some l', some n, some r' => some (.node l' k n r')
    | _, _, _ => none

/-- the grandchildren (entry ids, with multiplicity) of a list of children; `none` when a child
is not a pass family of the table -/
def grandchildren (ix : Idx) : List Child → Option (List Nat)
  | [] => some []
  | ch :: rest =>
    match findPass ix ch.entry, grandchildren ix rest with
    | some p, some tl => some (p.children.map (·.entry) ++ tl)
    | _, _ => none

def count (id : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x == id then 1 else 0) + count id xs

/-- O4 for one family: it occurs `μ ≥ 1` times in its own two-level expansion, which has more
than `μ` members -/
def growthOK (ix : Idx) (p : Pass) : Bool :=
  match grandchildren ix p.children with
  | some g => count p.id g ≥ 1 && g.length > count p.id g
  | none => false

/-- `k` steps of two levels from the vector `v` of the parity class of the table `tq` (other
class `tq'`, rows of `M` in `gq`): the two-level identity for the whole class and the closed
recurrence of the root at each step.  A fold: only the current level is passed on. -/
def iterate (tq tq' gq : Table) (r : O6Root) : Nat → Lengths → Bool
  | 0, _ => true
  | k + 1, v =>
    let v2 := step (step v tq') tq
    twoLevelOK v gq v2 &&
    ((get v2 r.id : Int) == r.a * (get v r.id : Int) + r.b) &&
    iterate tq tq' gq r k v2

/-- the O1 data indexed by family id; `none` when an id is duplicated -/
def baseLengths (o1 : List O1Pass) : Option (BTree Nat) :=
  BTree.ofList (o1.map (fun o => (o.id, o.N)))

/-- the lengths of the parity class `q` at its first level `m₀ = R(q)`: the O1 data at level B,
one step up when `q ≠ B mod 2` -/
def firstLevel (ix : Idx) (o1t : BTree Nat) (q : Nat) (tq tq' : Table) : Option Lengths :=
  if q == ix.B % 2 then baseVec o1t tq else (baseVec o1t tq').map (fun vB => step vB tq)

/-- O4 and O6 for one root: growth, the tables of both parity classes are closed under children,
`N(r, m₀) = N₀`, and `dim M + 3` steps of the two-level identity and of the closed recurrence -/
def rootOK (c : Cert) (ix : Idx) (o1t : BTree Nat) (r : O6Root) : Bool :=
  match findPass ix r.id with
  | none => false
  | some p =>
    growthOK ix p &&
    match famParity ix p with
    | none => false
    | some q =>
      q < 2 &&
      match tableOf c ix q, tableOf c ix (1 - q) with
      | some tq, some tq' =>
        closedIn tq' tq && closedIn tq tq' && (BTree.find tq r.id).isSome &&
        match firstLevel ix o1t q tq tq' with
        | none => false
        | some v => get v r.id == r.N0 && iterate tq tq' (grand tq' tq) r (tq.size + 3) v
      | _, _ => false

/-- O4 / O6 of the certificate: every root listed in `o6` passes `rootOK` (at least one root);
the O1 data cover the base level (checked by `baseVec`) -/
def checkO46 (c : Cert) (o1 : List O1Pass) (o6 : List O6Root) : Bool :=
  match c.index, baseLengths o1 with
  | some ix, some o1t => o6.length > 0 && o6.all (rootOK c ix o1t)
  | _, _ => false

/-- the lengths `N(r, m₀ + 2 s)` of a root for `s < k` (for `#eval`; not used by the check) -/
def rootLengths (c : Cert) (o1 : List O1Pass) (rid : Nat) (k : Nat) : Option (List Nat) :=
  match c.index, baseLengths o1 with
  | some ix, some o1t =>
    match findPass ix rid with
    | none => none
    | some p =>
      match famParity ix p with
      | none => none
      | some q =>
        match tableOf c ix q, tableOf c ix (1 - q) with
        | some tq, some tq' =>
          let rec go : Nat → Lengths → List Nat
            | 0, _ => []
            | j + 1, v => get v rid :: go j (step (step v tq') tq)
          (firstLevel ix o1t q tq tq').map (go k)
        | _, _ => none
  | _, _ => none

end TurtleO46
