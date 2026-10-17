import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Ring

/-!
# CheckerSoundness -- from the Bool checkers to Theorem U(1) of `proof_unbounded.md`

The finite obligations of a pass-substitution certificate are decided by Bool functions in plain Lean
(`TurtleO2_template.lean`: frames, port deltas, O3, O2; `TurtleO1_template.lean`: O1;
`TurtleO46_template.lean`: O4, O6), and the logic is formalized on an abstract structure
(`PassInduction.lean`: `PassSystem`, the induction `PassInduction.H_all`, determinism
`PassInduction.distinct`; `CayleyHamiltonRecurrence.lean`: O6 at every level).  This file joins the two:

1. **A concrete pass system** `TurtleSound.turtleSystem c prog o1 : PassSystem Crs` built from the
   certificate: points of Z[ζ] in canonical coordinates (`Pt = ℤ⁴`, basis 1, ζ, ζ², ζ³; `toPt` from the
   checker's `Z5`), the substitution σ (`subdividePt`), the standard supertiles (`supertilePt`), ownership
   (`ownedQuads`: the rhomb (A, B, B + C − A, C) of every positively oriented fine triangle), placed
   supertiles (type, level, isometry x ↦ ρ^k x + t), crossings (tail, head, command index), the rhomb a
   crossing leads into (the directed edge head → tail), the turtle step (`nextIn`), the child frames of
   the four standard triangles (`stdFrames`, the `frameData` of every certificate), lengths from the O1
   data and N(π, m+1) = Σ N(child, m).
2. **Soundness of the checkers**: `BTree.ofList_sound` (`ofList` succeeds ⇒ `find` looks up exactly the
   entries), `findPort_iff` / `findPass_iff` (the index of a certificate), `checkO3_sound` (O3 as a
   proposition), `model_O2At` / `model_O2` (O2 ⇒ the identities (a), (b), (c) of the model at the two lowest
   levels of each parity class), `model_H_base` (O1 ⇒ H(B): the checker's supertile, owned rhombs and
   navigation table are the model's, its run is the model's trace), `checkO46_sound` / `root_recurrence`
   (O4 and O6 as propositions: the checker's length vectors are the model's lengths), and
   `model_H_all`: the checkers and Lemma 2 give H(m) for every m ≥ B.
3. **Theorem U(1)**: `period_gt` (determinism: an injective crossing map that agrees with the turtle step
   of X inside the owned rhombs has no repetition within the N crossings of a segment that ends with an
   exit), `period_ge` (the same for states, by pigeonhole), `model_growth` (O4: N(r, m+2) ≥ N(r, m) + 1),
   `root_recurrence_all` (O6 at every level by Cayley–Hamilton), and `TurtleSound.unbounded`: for a
   certificate accepted by the checkers, the pass of a root is arbitrarily long and the orbit of its entry
   crossing has no repetition within any given bound, in every isometric copy of the supertile.

## Which fields of `PassSystem` are proved

| field | content | status |
|---|---|---|
| `enters_act` | the rhomb entered is equivariant | proved (`rfl`) |
| `owned_act` | ownership is equivariant | proved (isometries are injective) |
| `next_act` | the turtle step is equivariant | proved (`nextIn_act`) |
| `next_sub` | locality: in a sub-tile that owns the rhomb entered, the step is the sub-tile's | proved from the axiom `TurtleGeom.edgeUnique` |
| `owned_sub` | ownership of a sub-tile refines ownership (sub-tile = owned rhombs included) | proved (definition of `sub`) |
| `child_sub` | the placed children are sub-tiles of the parent | proved (`child_sub`: child frames by `decide`, σ commutes with isometries) |
| `portIn_rec`, `portOut_rec` | port(m+2) = φ² port(m) + δ from the lowest level of the class | proved (`portCQ_rec`) |
| `G_rec` | G_{j,m+2}(φ² x + d) = φ² G_{j,m}(x) + ρ^{k_j} d | proved (`G_rec`; G_{j,m} = ρ^k x + φ^m φ⁻¹ t) |

The hypotheses of `PassInduction.H_all`: O1 (`model_H_base`), O2 (`model_O2`), O3 (`model_O3`), the length
recursion (`model_N`) are proved from the checkers; Lemma 2 (`ExitProperty`, the exit property) is a
hypothesis, stated per certificate as an axiom in the generated file.

## Axioms

* `TurtleGeom.edgeUnique τ m` — in the standard supertile of every type and level, no two owned rhombs share
  a directed edge (non-overlap of the rhombs of a Penrose tiling, classical facts (F1)–(F3)).  At the base
  level it is what the O1 checker verifies (`BTree.ofList` of the directed-edge keys).
* `TurtleGeom.exitProperty_<certificate>` (in the generated file) — Lemma 2 for that certificate,
  proved in the paper from O5 (checked by `TurtleO5_template.lean`) and plane geometry.

Everything else depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Use

Not a standalone file: LeanAssist appends it, after `TurtleO2_template.lean`, `TurtleO1_template.lean`,
`TurtleO46_template.lean`, `PassInduction.lean` and `CayleyHamiltonRecurrence.lean` (the `import` lines of
all parts first), and then the data of a certificate and the final theorem
(`LeanTurtleUnbounded[certFile]`, examples/turtle_port_identities.wl; the result is saved as
`unbounded_<program>_verified.lean`, a complete file for `LeanCheckFile`).  Theorems carry qualified names
so that the `#print axioms` lines that LeanAssist appends resolve.  The side conditions that the template
checkers leave implicit (standard frames, parities 0/1, entry ports in the key range of the O1 table) are
checked by `checkSide`.
-/

section
open TurtleO2

/-! ## Z[ζ] in canonical coordinates -/

/-- `TurtleO2.iter` is `Nat.iterate` -/
theorem TurtleSound.iter_eq {α : Type} (f : α → α) (n : ℕ) (x : α) : iter f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- points of Z[ζ]: coordinates in the basis 1, ζ, ζ², ζ³ (ζ⁴ = −1 − ζ − ζ² − ζ³) -/
abbrev TurtleSound.Pt := ℤ × ℤ × ℤ × ℤ

/-- the point of a `Z5` (coordinates modulo (1,1,1,1,1)) -/
def TurtleSound.toPt (k : Z5) : TurtleSound.Pt := (k.a - k.e, k.b - k.e, k.c - k.e, k.d - k.e)

/-- multiplication by φ = 1 + ζ + ζ⁴ -/
def TurtleSound.phiPt (p : TurtleSound.Pt) : TurtleSound.Pt :=
  (p.2.1 - p.2.2.2, p.2.1 + p.2.2.1 - p.2.2.2, p.2.1 + p.2.2.1 - p.1, p.2.2.1 - p.1)

/-- multiplication by ρ = −ζ³ (rotation by 36°) -/
def TurtleSound.rotPt (p : TurtleSound.Pt) : TurtleSound.Pt :=
  (p.2.1 - p.2.2.1, p.2.1 - p.2.2.2, p.2.1, p.2.1 - p.1)

def TurtleSound.rotK (k : ℕ) (p : TurtleSound.Pt) : TurtleSound.Pt := TurtleSound.rotPt^[k] p
def TurtleSound.phiK (n : ℕ) (p : TurtleSound.Pt) : TurtleSound.Pt := TurtleSound.phiPt^[n] p

end

section
open TurtleO2 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.toPt_canon (k : Z5) : toPt (Z5.canon k) = toPt k := by
  simp [toPt, Z5.canon]

theorem TurtleSound.toPt_add (k l : Z5) : toPt (Z5.add k l) = toPt k + toPt l := by
  simp only [toPt, Z5.add, Z5.canon, Prod.mk_add_mk, Prod.mk.injEq]; omega

theorem TurtleSound.toPt_sub (k l : Z5) : toPt (Z5.sub k l) = toPt k - toPt l := by
  simp only [toPt, Z5.sub, Z5.canon, Prod.mk_sub_mk, Prod.mk.injEq]; omega

theorem TurtleSound.toPt_mulphi (k : Z5) : toPt (Z5.mulphi k) = phiPt (toPt k) := by
  simp only [toPt, Z5.mulphi, Z5.canon, phiPt, Prod.mk.injEq]; omega

theorem TurtleSound.toPt_rot36 (k : Z5) : toPt (Z5.rot36 k) = rotPt (toPt k) := by
  simp only [toPt, Z5.rot36, Z5.canon, rotPt, Prod.mk.injEq]; omega

theorem TurtleSound.toPt_zero : toPt Z5.zero = 0 := by
  simp [toPt, Z5.zero]

theorem TurtleSound.beq_iff (k l : Z5) : Z5.beq k l = true ↔ toPt k = toPt l := by
  unfold Z5.beq
  rw [beq_iff_eq]
  simp only [Z5.canon, Z5.mk.injEq, toPt, Prod.mk.injEq, and_true]

theorem TurtleSound.toPt_rotN (k : ℕ) (v : Z5) : toPt (rotN k v) = rotK k (toPt v) := by
  unfold rotN rotK
  rw [TurtleSound.iter_eq]
  exact (Function.Semiconj.iterate_right (f := toPt) (fun x => TurtleSound.toPt_rot36 x) k) v

theorem TurtleSound.toPt_phiN (n : ℕ) (v : Z5) : toPt (phiN n v) = phiK n (toPt v) := by
  unfold phiN phiK
  rw [TurtleSound.iter_eq]
  exact (Function.Semiconj.iterate_right (f := toPt) (fun x => TurtleSound.toPt_mulphi x) n) v

theorem TurtleSound.toPt_phi2 (v : Z5) : toPt (phi2 v) = phiPt (phiPt (toPt v)) := by
  simp [phi2, TurtleSound.toPt_mulphi]

/-! linear maps -/

theorem TurtleSound.phiPt_add (p q : Pt) : phiPt (p + q) = phiPt p + phiPt q := by
  simp [phiPt, Prod.ext_iff] <;> omega

theorem TurtleSound.rotPt_add (p q : Pt) : rotPt (p + q) = rotPt p + rotPt q := by
  simp [rotPt, Prod.ext_iff] <;> omega

theorem TurtleSound.phiPt_sub (p q : Pt) : phiPt (p - q) = phiPt p - phiPt q := by
  simp [phiPt, Prod.ext_iff] <;> omega

theorem TurtleSound.rotPt_sub (p q : Pt) : rotPt (p - q) = rotPt p - rotPt q := by
  simp [rotPt, Prod.ext_iff] <;> omega

theorem TurtleSound.rotPt_zero : rotPt 0 = 0 := by decide
theorem TurtleSound.phiPt_zero : phiPt 0 = 0 := by decide

theorem TurtleSound.rot_phi_comm (p : Pt) : rotPt (phiPt p) = phiPt (rotPt p) := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [rotPt, phiPt, Prod.mk.injEq]; omega

/-- φ² = φ + 1 -/
theorem TurtleSound.phi_sq (p : Pt) : phiPt (phiPt p) = phiPt p + p := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [phiPt, Prod.mk_add_mk, Prod.mk.injEq]; omega

theorem TurtleSound.rotPt_injective : Function.Injective rotPt := by
  intro p q h
  obtain ⟨a, b, c, d⟩ := p; obtain ⟨a', b', c', d'⟩ := q
  simp only [rotPt, Prod.mk.injEq] at h ⊢; omega

theorem TurtleSound.rotK_add (k : ℕ) (p q : Pt) : rotK k (p + q) = rotK k p + rotK k q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
    simp only [rotK, Function.iterate_succ_apply] at ih ⊢
    rw [rotPt_add, ih]

theorem TurtleSound.rotK_sub (k : ℕ) (p q : Pt) : rotK k (p - q) = rotK k p - rotK k q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
    simp only [rotK, Function.iterate_succ_apply] at ih ⊢
    rw [rotPt_sub, ih]

theorem TurtleSound.rotK_zero (k : ℕ) : rotK k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotK, Function.iterate_succ_apply] at ih ⊢; rw [rotPt_zero, ih]

theorem TurtleSound.phiK_add (n : ℕ) (p q : Pt) : phiK n (p + q) = phiK n p + phiK n q := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [phiK, Function.iterate_succ_apply] at ih ⊢
    rw [phiPt_add, ih]

theorem TurtleSound.phiK_sub (n : ℕ) (p q : Pt) : phiK n (p - q) = phiK n p - phiK n q := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [phiK, Function.iterate_succ_apply] at ih ⊢
    rw [phiPt_sub, ih]

theorem TurtleSound.rotK_injective (k : ℕ) : Function.Injective (rotK k) :=
  TurtleSound.rotPt_injective.iterate k

theorem TurtleSound.rotK_phiPt (k : ℕ) (p : Pt) : rotK k (phiPt p) = phiPt (rotK k p) :=
  ((Function.Commute.iterate_left (f := rotPt) (g := phiPt) (fun x => rot_phi_comm x) k) p)

theorem TurtleSound.rotK_phiK (k n : ℕ) (p : Pt) : rotK k (phiK n p) = phiK n (rotK k p) :=
  ((Function.Commute.iterate_iterate (f := rotPt) (g := phiPt) (fun x => rot_phi_comm x) k n) p)

theorem TurtleSound.rotK_add_k (k k' : ℕ) (p : Pt) : rotK (k + k') p = rotK k (rotK k' p) := by
  simp only [rotK]; rw [Function.iterate_add_apply]

theorem TurtleSound.phiK_succ (n : ℕ) (p : Pt) : phiK (n + 1) p = phiPt (phiK n p) := by
  simp only [phiK]; rw [Function.iterate_succ_apply']

end

/-! ## the balanced search tree: `ofList` succeeds ⇒ `find` looks up exactly the entries -/

section
open TurtleO2
set_option linter.unnecessarySeqFocus false

/-- in-order list of the entries -/
def TurtleO2.BTree.toList {α : Type} : BTree α → List (ℕ × α)
  | .leaf => []
  | .node l k v r => l.toList ++ (k, v) :: r.toList

theorem TurtleO2.BTree.size_eq {α : Type} (t : BTree α) : t.size = t.toList.length := by
  induction t with
  | leaf => rfl
  | node l k v r ihl ihr =>
    simp only [BTree.size, BTree.toList, List.length_append, List.length_cons, ihl, ihr]
    omega

theorem TurtleO2.BTree.split_perm {α : Type} : ∀ xs : List (ℕ × α), List.Perm ((split xs).1 ++ (split xs).2) xs
  | [] => by simp [split]
  | [x] => by simp [split]
  | x :: y :: tl => by
    have ih := split_perm tl
    rcases h : split tl with ⟨a, b⟩
    rw [h] at ih
    simp only [split, h, List.cons_append]
    exact List.Perm.cons x (List.perm_middle.trans (List.Perm.cons y ih))

theorem TurtleO2.BTree.mergeBy_perm {α : Type} :
    ∀ (n : ℕ) (xs ys : List (ℕ × α)), List.Perm (mergeBy n xs ys) (xs ++ ys)
  | 0, xs, ys => by simp [mergeBy]
  | _ + 1, [], ys => by simp [mergeBy]
  | _ + 1, x :: xs, [] => by simp [mergeBy]
  | n + 1, x :: xs, y :: ys => by
    simp only [mergeBy]
    split_ifs
    · exact List.Perm.cons x (mergeBy_perm n xs (y :: ys))
    · exact (List.Perm.cons y (mergeBy_perm n (x :: xs) ys)).trans List.perm_middle.symm

theorem TurtleO2.BTree.msort_perm {α : Type} : ∀ (n : ℕ) (xs : List (ℕ × α)), List.Perm (msort n xs) xs
  | 0, xs => by simp [msort]
  | n + 1, [] => by simp [msort]
  | n + 1, [x] => by simp [msort]
  | n + 1, x :: y :: tl => by
    have hs := split_perm (x :: y :: tl)
    rcases h : split (x :: y :: tl) with ⟨a, b⟩
    rw [h] at hs
    simp only [msort, h]
    exact (mergeBy_perm _ _ _).trans ((List.Perm.append (msort_perm n a) (msort_perm n b)).trans hs)

theorem TurtleO2.BTree.pairwise_of_sortedStrict {α : Type} :
    ∀ xs : List (ℕ × α), sortedStrict xs = true → xs.Pairwise (fun a b => a.1 < b.1)
  | [] => fun _ => List.Pairwise.nil
  | [_] => fun _ => List.pairwise_singleton _ _
  | x :: y :: tl => fun h => by
    simp only [sortedStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_sortedStrict (y :: tl) h.2
    refine List.Pairwise.cons ?_ ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hz)

theorem TurtleO2.BTree.build_sublist {α : Type} :
    ∀ (n : ℕ) (xs : List (ℕ × α)), List.Sublist (build n xs).toList xs
  | 0, xs => by simp [build, BTree.toList]
  | n + 1, [] => by simp [build, BTree.toList]
  | n + 1, x :: xs' => by
    simp only [build]
    split
    · simp [BTree.toList]
    · rename_i k v rest heq
      simp only [BTree.toList]
      have h1 := build_sublist n ((x :: xs').take ((x :: xs').length / 2))
      have h2 := build_sublist n rest
      have hx : (x :: xs') = (x :: xs').take ((x :: xs').length / 2) ++ (k, v) :: rest := by
        rw [← heq, List.take_append_drop]
      have := List.Sublist.append h1 (List.Sublist.cons_cons (k, v) h2)
      rw [← hx] at this
      exact this

theorem TurtleO2.BTree.find_mem {α : Type} (t : BTree α) (k : ℕ) (v : α)
    (h : t.find k = some v) : (k, v) ∈ t.toList := by
  induction t with
  | leaf => simp [BTree.find] at h
  | node l key val r ihl ihr =>
    simp only [BTree.find] at h
    simp only [BTree.toList, List.mem_append, List.mem_cons]
    split_ifs at h with h1 h2
    · exact Or.inl (ihl h)
    · exact Or.inr (Or.inr (ihr h))
    · cases h
      have : k = key := by omega
      subst this
      exact Or.inr (Or.inl rfl)

theorem TurtleO2.BTree.find_of_mem {α : Type} (t : BTree α) (hs : t.toList.Pairwise (fun a b => a.1 < b.1))
    (k : ℕ) (v : α) (h : (k, v) ∈ t.toList) : t.find k = some v := by
  induction t with
  | leaf => simp [BTree.toList] at h
  | node l key val r ihl ihr =>
    simp only [BTree.toList, List.pairwise_append, List.pairwise_cons, List.mem_cons] at hs
    obtain ⟨hl, ⟨hk, hr⟩, hlr⟩ := hs
    simp only [BTree.toList, List.mem_append, List.mem_cons] at h
    simp only [BTree.find]
    rcases h with h | h | h
    · have hlt : k < key := hlr (k, v) h (key, val) (Or.inl rfl)
      rw [if_pos hlt]
      exact ihl hl h
    · cases h
      simp
    · have hlt : key < k := hk (k, v) h
      rw [if_neg (by omega), if_pos hlt]
      exact ihr hr h

/-- `ofList` succeeds ⇒ the lookups of the tree are exactly the entries of the list (in particular
the keys of the list are distinct) -/
theorem TurtleO2.BTree.ofList_sound {α : Type} (xs : List (ℕ × α)) (t : BTree α) (h : ofList xs = some t) :
    ∀ k v, t.find k = some v ↔ (k, v) ∈ xs := by
  unfold ofList at h
  simp only at h
  split_ifs at h with h1 h2
  cases h
  have hsorted := pairwise_of_sortedStrict _ (by simpa using h1)
  have hsub := build_sublist 64 (msort 64 xs)
  have hlen : (build 64 (msort 64 xs)).toList.length = (msort 64 xs).length := by
    rw [← size_eq]; simpa using h2
  have heq := hsub.eq_of_length hlen
  intro k v
  have hmem : (k, v) ∈ xs ↔ (k, v) ∈ (build 64 (msort 64 xs)).toList := by
    rw [heq]; exact (msort_perm 64 xs).mem_iff.symm
  rw [hmem]
  constructor
  · exact find_mem _ k v
  · exact find_of_mem _ (by rw [heq]; exact hsorted) k v

/-- the keys of a list accepted by `ofList` determine the entries -/
theorem TurtleO2.BTree.ofList_unique {α : Type} (xs : List (ℕ × α)) (t : BTree α) (h : ofList xs = some t)
    (k : ℕ) (v v' : α) (h1 : (k, v) ∈ xs) (h2 : (k, v') ∈ xs) : v = v' := by
  have e1 := (ofList_sound xs t h k v).mpr h1
  have e2 := (ofList_sound xs t h k v').mpr h2
  rw [e1] at e2
  exact Option.some.inj e2

end

/-! ## the index of a certificate -/

section
open TurtleO2

theorem TurtleSound.index_fields (c : Cert) (ix : Idx) (h : c.index = some ix) :
    ix.B = c.B ∧ ix.frames = c.frames := by
  unfold Cert.index at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem TurtleSound.findPort_iff (c : Cert) (ix : Idx) (h : c.index = some ix) (pid : ℕ) (p : Port) :
    findPort ix pid = some p ↔ p ∈ c.ports ∧ p.id = pid := by
  unfold Cert.index at h
  split at h
  · rename_i tp tq h1 _
    cases h
    unfold findPort
    rw [BTree.ofList_sound _ _ h1]
    simp only [List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨ha, rfl⟩; exact ⟨p, ha, rfl, rfl⟩
  · cases h

theorem TurtleSound.findPass_iff (c : Cert) (ix : Idx) (h : c.index = some ix) (pid : ℕ) (p : Pass) :
    findPass ix pid = some p ↔ p ∈ c.passes ∧ p.id = pid := by
  unfold Cert.index at h
  split at h
  · rename_i tp tq _ h2
    cases h
    unfold findPass
    rw [BTree.ofList_sound _ _ h2]
    simp only [List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨ha, rfl⟩; exact ⟨p, ha, rfl, rfl⟩
  · cases h

end

/-! ## the geometric model: triangles, substitution, owned rhombs, isometries, the turtle step -/

section
open TurtleO2 TurtleO1 TurtleSound

/-- supertile types: (acute, positively oriented) -/
abbrev TurtleSound.Typ := Bool × Bool

/-- the type of the certificate's (col, sign) (`stdTriangle` and `subdivide` only test `col == 0`
and `sign > 0`) -/
def TurtleSound.normTyp (col : ℕ) (sign : ℤ) : TurtleSound.Typ := (col == 0, decide (0 < sign))

/-- marked triangle (acute, A, B, C) -/
abbrev TurtleSound.TriPt := Bool × TurtleSound.Pt × TurtleSound.Pt × TurtleSound.Pt

def TurtleSound.toTri (t : Tri) : TurtleSound.TriPt := (t.1 == 0, toPt t.2.1, toPt t.2.2.1, toPt t.2.2.2)

/-- the standard triangle of a type: A = 0, (B, C) = (1, ρ^θ) if positive, (ρ^θ, 1) if negative
(ρ = −ζ³ = (0,0,0,−1), ρ³ = 1 + ζ + ζ² + ζ³) -/
def TurtleSound.stdTriPt (τ : TurtleSound.Typ) : TurtleSound.TriPt :=
  let c : TurtleSound.Pt := if τ.1 then (0, 0, 0, -1) else (1, 1, 1, 1)
  if τ.2 then (τ.1, 0, (1, 0, 0, 0), c) else (τ.1, 0, c, (1, 0, 0, 0))

/-- the substitution σ (children in the coordinates of the inflated parent), as `TurtleO2.subdivide` -/
def TurtleSound.subdividePt : TurtleSound.TriPt → List TurtleSound.TriPt
  | (acute, A, B, C) =>
    if acute then
      [(true, phiPt C, phiPt A + (B - A), phiPt B), (false, phiPt A + (B - A), phiPt C, phiPt A)]
    else
      [(false, phiPt B + (C - B), phiPt C, phiPt A), (false, phiPt B + (A - B), phiPt B + (C - B), phiPt B),
       (true, phiPt B + (C - B), phiPt B + (A - B), phiPt A)]

def TurtleSound.subAllPt : List TurtleSound.TriPt → List TurtleSound.TriPt
  | [] => []
  | t :: ts => subdividePt t ++ subAllPt ts

/-- the fine triangles of the standard level-m supertile -/
def TurtleSound.supertilePt (τ : TurtleSound.Typ) (m : ℕ) : List TurtleSound.TriPt :=
  subAllPt^[m] [stdTriPt τ]

/-- orientation, exactly as `TurtleO1.orient`: C − A = ρ^{±θ}(B − A) -/
def TurtleSound.orientPt (acute : Bool) (A B C : TurtleSound.Pt) : ℤ :=
  if C - A = rotK (if acute then 1 else 3) (B - A) then 1
  else if C - A = rotK (if acute then 9 else 7) (B - A) then -1 else 0

/-- rhomb, vertices in counter-clockwise order -/
abbrev TurtleSound.QuadPt := TurtleSound.Pt × TurtleSound.Pt × TurtleSound.Pt × TurtleSound.Pt

def TurtleSound.getQ (q : TurtleSound.QuadPt) (e : ℕ) : TurtleSound.Pt :=
  match e % 4 with
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2.1
  | _ => q.2.2.2

/-- ownership: every positively oriented fine triangle (A, B, C) owns the rhomb (A, B, B + C − A, C) -/
def TurtleSound.ownedQuads : List TurtleSound.TriPt → List TurtleSound.QuadPt
  | [] => []
  | (acute, A, B, C) :: ts =>
    if orientPt acute A B C = 1 then (A, B, B + C - A, C) :: ownedQuads ts else ownedQuads ts

/-- the directed edges of the rhombs of a list are pairwise distinct (as (rhomb, edge) pairs) -/
def TurtleSound.EdgeUnique (qs : List TurtleSound.QuadPt) : Prop :=
  ∀ q ∈ qs, ∀ q' ∈ qs, ∀ e, e < 4 → ∀ e', e' < 4 → getQ q e = getQ q' e' → getQ q (e + 1) = getQ q' (e' + 1) →
    q = q' ∧ e = e'

/-- orientation-preserving isometry x ↦ ρ^k x + t -/
abbrev TurtleSound.Iso := ℕ × TurtleSound.Pt

def TurtleSound.isoPt (g : TurtleSound.Iso) (x : TurtleSound.Pt) : TurtleSound.Pt := rotK g.1 x + g.2
def TurtleSound.mulIso (g h : TurtleSound.Iso) : TurtleSound.Iso := (g.1 + h.1, rotK g.1 h.2 + g.2)
def TurtleSound.scaleIso (g : TurtleSound.Iso) : TurtleSound.Iso := (g.1, phiPt g.2)
def TurtleSound.actTri (g : TurtleSound.Iso) (t : TurtleSound.TriPt) : TurtleSound.TriPt :=
  (t.1, isoPt g t.2.1, isoPt g t.2.2.1, isoPt g t.2.2.2)
def TurtleSound.actQ (g : TurtleSound.Iso) (q : TurtleSound.QuadPt) : TurtleSound.QuadPt :=
  (isoPt g q.1, isoPt g q.2.1, isoPt g q.2.2.1, isoPt g q.2.2.2)

/-- placed supertile (type, level, placement) -/
abbrev TurtleSound.Tile := TurtleSound.Typ × ℕ × TurtleSound.Iso

def TurtleSound.quadsOf (X : TurtleSound.Tile) : List TurtleSound.QuadPt :=
  (ownedQuads (supertilePt X.1 X.2.1)).map (actQ X.2.2)

/-- crossing (tail, head, command index) -/
abbrev TurtleSound.Crs := TurtleSound.Pt × TurtleSound.Pt × ℤ

def TurtleSound.toC (x : Cross) : TurtleSound.Crs := (toPt x.tail, toPt x.head, (x.i : ℤ))

/-- position of the directed edge u → v in the rhomb -/
def TurtleSound.edgePos (q : TurtleSound.QuadPt) (u v : TurtleSound.Pt) : Option ℕ :=
  (List.range 4).find? (fun e => decide (getQ q e = u ∧ getQ q (e + 1) = v))

/-- the first rhomb of the list with the directed edge u → v, and its position -/
def TurtleSound.findEdge (qs : List TurtleSound.QuadPt) (u v : TurtleSound.Pt) :
    Option (TurtleSound.QuadPt × ℕ) :=
  qs.findSome? (fun q => (edgePos q u v).map (fun e => (q, e)))

/-- the turtle in rhomb q heading edge e, next command ci: R / L until an S, which crosses edge e -/
def TurtleSound.advance (prog : List Cmd) (q : TurtleSound.QuadPt) : ℕ → ℕ → ℕ → Option TurtleSound.Crs
  | 0, _, _ => none
  | f + 1, e, ci =>
    match nth prog (ci % prog.length) with
    | some Cmd.S => some (getQ q e, getQ q (e + 1), ((ci % prog.length : ℕ) : ℤ))
    | some Cmd.R => advance prog q f ((e + 3) % 4) (ci + 1)
    | some Cmd.L => advance prog q f ((e + 1) % 4) (ci + 1)
    | none => none

/-- the next crossing after the crossing x, computed in the rhombs qs: x leads into the rhomb of qs with
the directed edge head → tail; the turtle heads the opposite edge with the next command -/
def TurtleSound.nextIn (prog : List Cmd) (qs : List TurtleSound.QuadPt) (x : TurtleSound.Crs) : TurtleSound.Crs :=
  match findEdge qs x.2.1 x.1 with
  | some (q, eb) => (advance prog q prog.length ((eb + 2) % 4) (x.2.2.toNat + 1)).getD x
  | none => x

/-- the child frames of the four standard triangles (the `frameData` written by LeanAssist for every
certificate: they depend only on the substitution) -/
def TurtleSound.stdFrames : List (ℕ × ℤ × List Frame) :=
  [(0, 1, [⟨0, 1, 7, ⟨1, 1, 0, 0, 0⟩⟩, ⟨1, 1, 2, ⟨1, 0, 0, 0, 0⟩⟩]),
   (0, -1, [⟨0, -1, 3, ⟨0, 0, -1, -1, 0⟩⟩, ⟨1, -1, 6, ⟨0, 0, 0, -1, 0⟩⟩]),
   (1, 1, [⟨1, 1, 4, ⟨0, 1, 0, 0, 0⟩⟩, ⟨1, -1, 0, ⟨-1, 0, -1, -1, 0⟩⟩, ⟨0, -1, 7, ⟨0, 1, 0, 0, 0⟩⟩]),
   (1, -1, [⟨1, -1, 6, ⟨0, 0, 0, -1, 0⟩⟩, ⟨1, 1, 0, ⟨-1, 0, 0, -1, 0⟩⟩, ⟨0, 1, 5, ⟨0, 0, 0, -1, 0⟩⟩])]

def TurtleSound.typCol (τ : TurtleSound.Typ) : ℕ := if τ.1 then 0 else 1
def TurtleSound.typSign (τ : TurtleSound.Typ) : ℤ := if τ.2 then 1 else -1

def TurtleSound.findFramesIn (L : List (ℕ × ℤ × List Frame)) (col : ℕ) (sign : ℤ) : Option (List Frame) :=
  (L.find? (fun f => f.1 == col && f.2.1 == sign)).map (fun f => f.2.2)

def TurtleSound.framesFor (τ : TurtleSound.Typ) : List Frame :=
  (findFramesIn stdFrames (typCol τ) (typSign τ)).getD []

def TurtleSound.defaultFrame : Frame := ⟨0, 1, 0, ⟨0, 0, 0, 0, 0⟩⟩

/-- the frame of slot j (slot 0 for a slot beyond the children) -/
def TurtleSound.frameAt (τ : TurtleSound.Typ) (j : ℕ) : Frame :=
  ((framesFor τ)[j]?).getD ((framesFor τ).headD defaultFrame)

def TurtleSound.slotTyp (τ : TurtleSound.Typ) (j : ℕ) : TurtleSound.Typ :=
  normTyp (frameAt τ j).ccol (frameAt τ j).csign

/-- G_{j,m}: x ↦ ρ^k x + φ^m φ⁻¹ t (= φ^{m−1} t for m ≥ 1; φ⁻¹ = φ − 1) -/
def TurtleSound.Gm (τ : TurtleSound.Typ) (j m : ℕ) : TurtleSound.Iso :=
  ((frameAt τ j).k, phiK m (phiPt (toPt (frameAt τ j).t) - toPt (frameAt τ j).t))

end

/-! ### lemmas on the model -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.isoPt_injective (g : Iso) : Function.Injective (isoPt g) := by
  intro x y h
  simp only [isoPt, add_left_inj] at h
  exact rotK_injective g.1 h

theorem TurtleSound.isoPt_sub (g : Iso) (x y : Pt) : isoPt g x - isoPt g y = rotK g.1 (x - y) := by
  simp only [isoPt, rotK_sub]; abel

theorem TurtleSound.isoPt_mul (g h : Iso) (x : Pt) : isoPt (mulIso g h) x = isoPt g (isoPt h x) := by
  simp only [isoPt, mulIso, rotK_add_k, rotK_add]; abel

theorem TurtleSound.isoPt_one (x : Pt) : isoPt (0, 0) x = x := by
  simp [isoPt, rotK]

theorem TurtleSound.mulIso_one (g : Iso) : mulIso g (0, 0) = g := by
  simp [mulIso, rotK_zero]

theorem TurtleSound.isoPt_quad (g : Iso) (A B C : Pt) :
    isoPt g B + isoPt g C - isoPt g A = isoPt g (B + C - A) := by
  simp only [isoPt, rotK_add, rotK_sub]; abel

theorem TurtleSound.rotK_comm (k k' : ℕ) (p : Pt) : rotK k (rotK k' p) = rotK k' (rotK k p) := by
  rw [← rotK_add_k, ← rotK_add_k, Nat.add_comm]

theorem TurtleSound.getQ_act (g : Iso) (q : QuadPt) (e : ℕ) : getQ (actQ g q) e = isoPt g (getQ q e) := by
  unfold getQ actQ
  split <;> rfl

theorem TurtleSound.actQ_mul (g h : Iso) (q : QuadPt) : actQ (mulIso g h) q = actQ g (actQ h q) := by
  simp [actQ, isoPt_mul]

theorem TurtleSound.actQ_one (q : QuadPt) : actQ (0, 0) q = q := by
  simp [actQ, isoPt_one]

theorem TurtleSound.actQ_one' : actQ (0, 0) = id := funext actQ_one

theorem TurtleSound.actQ_injective (g : Iso) : Function.Injective (actQ g) := by
  intro q q' h
  simp only [actQ, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have i := isoPt_injective g
  exact Prod.ext (i h1) (Prod.ext (i h2) (Prod.ext (i h3) (i h4)))

theorem TurtleSound.orientPt_act (g : Iso) (a : Bool) (A B C : Pt) :
    orientPt a (isoPt g A) (isoPt g B) (isoPt g C) = orientPt a A B C := by
  unfold orientPt
  rw [isoPt_sub, isoPt_sub, rotK_comm _ g.1, rotK_comm _ g.1]
  simp only [(rotK_injective g.1).eq_iff]

theorem TurtleSound.iso_scale_phi (g : Iso) (x : Pt) : isoPt (scaleIso g) (phiPt x) = phiPt (isoPt g x) := by
  simp only [isoPt, scaleIso, phiPt_add, rotK_phiPt]

theorem TurtleSound.iso_scale_phi' (g : Iso) (x y : Pt) :
    isoPt (scaleIso g) (phiPt x + (y - x)) = phiPt (isoPt g x) + (isoPt g y - isoPt g x) := by
  rw [isoPt_sub]
  simp only [isoPt, scaleIso, phiPt_add, rotK_phiPt, rotK_add]; abel

theorem TurtleSound.subdividePt_act (g : Iso) (t : TriPt) :
    subdividePt (actTri g t) = (subdividePt t).map (actTri (scaleIso g)) := by
  obtain ⟨a, A, B, C⟩ := t
  cases a <;> simp only [subdividePt, actTri, List.map_cons, List.map_nil, iso_scale_phi, iso_scale_phi',
    Bool.false_eq_true, if_false, if_true]

theorem TurtleSound.subAllPt_append (l1 l2 : List TriPt) : subAllPt (l1 ++ l2) = subAllPt l1 ++ subAllPt l2 := by
  induction l1 with
  | nil => rfl
  | cons t ts ih => simp [subAllPt, ih]

theorem TurtleSound.subAllPt_map (g : Iso) (l : List TriPt) :
    subAllPt (l.map (actTri g)) = (subAllPt l).map (actTri (scaleIso g)) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [subAllPt, ih, subdividePt_act]

theorem TurtleSound.subAllPt_iter_map (m : ℕ) : ∀ (g : Iso) (l : List TriPt),
    subAllPt^[m] (l.map (actTri g)) = (subAllPt^[m] l).map (actTri (scaleIso^[m] g)) := by
  induction m with
  | zero => intro g l; rfl
  | succ m ih =>
    intro g l
    simp only [Function.iterate_succ_apply]
    rw [subAllPt_map, ih]

theorem TurtleSound.scaleIso_iter (m : ℕ) (k : ℕ) (t : Pt) : scaleIso^[m] (k, t) = (k, phiK m t) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply, scaleIso]
    rw [ih]; rfl

theorem TurtleSound.mem_subAllPt (l : List TriPt) (y : TriPt) : y ∈ subAllPt l ↔ ∃ x ∈ l, y ∈ subdividePt x := by
  induction l with
  | nil => simp [subAllPt]
  | cons t ts ih => simp [subAllPt, ih]

theorem TurtleSound.subAllPt_mono (l1 l2 : List TriPt) (h : ∀ x ∈ l1, x ∈ l2) :
    ∀ y ∈ subAllPt l1, y ∈ subAllPt l2 := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := (mem_subAllPt l1 y).mp hy
  exact (mem_subAllPt l2 y).mpr ⟨x, h x hx, hy⟩

theorem TurtleSound.subAllPt_iter_mono (m : ℕ) : ∀ (l1 l2 : List TriPt), (∀ x ∈ l1, x ∈ l2) →
    ∀ y ∈ subAllPt^[m] l1, y ∈ subAllPt^[m] l2 := by
  induction m with
  | zero => intro l1 l2 h; exact h
  | succ m ih =>
    intro l1 l2 h
    simp only [Function.iterate_succ_apply]
    exact ih _ _ (subAllPt_mono l1 l2 h)

theorem TurtleSound.mem_ownedQuads (l : List TriPt) (q : QuadPt) :
    q ∈ ownedQuads l ↔ ∃ t ∈ l, orientPt t.1 t.2.1 t.2.2.1 t.2.2.2 = 1 ∧
      q = (t.2.1, t.2.2.1, t.2.2.1 + t.2.2.2 - t.2.1, t.2.2.2) := by
  induction l with
  | nil => simp [ownedQuads]
  | cons t ts ih =>
    obtain ⟨a, A, B, C⟩ := t
    simp only [ownedQuads]
    split_ifs with h
    · simp [ih, h]
    · simp [ih, h]

theorem TurtleSound.ownedQuads_mono (l1 l2 : List TriPt) (h : ∀ x ∈ l1, x ∈ l2) :
    ∀ q ∈ ownedQuads l1, q ∈ ownedQuads l2 := by
  intro q hq
  obtain ⟨t, ht, h1, h2⟩ := (mem_ownedQuads l1 q).mp hq
  exact (mem_ownedQuads l2 q).mpr ⟨t, h t ht, h1, h2⟩

theorem TurtleSound.ownedQuads_act (g : Iso) (l : List TriPt) :
    ownedQuads (l.map (actTri g)) = (ownedQuads l).map (actQ g) := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, A, B, C⟩ := t
    simp only [List.map_cons, actTri, ownedQuads, orientPt_act]
    split_ifs
    · simp only [List.map_cons, ih, actQ, isoPt_quad]
    · exact ih

/-- the child frames: the child in a slot is the frame's image of the standard triangle of its type -/
theorem TurtleSound.frames_sub (τ : Typ) : ∀ fr ∈ framesFor τ,
    actTri (fr.k, toPt fr.t) (stdTriPt (normTyp fr.ccol fr.csign)) ∈ subdividePt (stdTriPt τ) := by
  rcases τ with ⟨_ | _, _ | _⟩ <;> decide

theorem TurtleSound.framesFor_ne (τ : Typ) : framesFor τ ≠ [] := by
  rcases τ with ⟨_ | _, _ | _⟩ <;> decide

theorem TurtleSound.frameAt_mem (τ : Typ) (j : ℕ) : frameAt τ j ∈ framesFor τ := by
  unfold frameAt
  cases h : (framesFor τ)[j]? with
  | some fr => exact List.mem_of_getElem? h
  | none =>
    simp only [Option.getD_none]
    cases h' : framesFor τ with
    | nil => exact absurd h' (framesFor_ne τ)
    | cons a l => simp

theorem TurtleSound.phiK_Gm (m : ℕ) (t : Pt) : phiK (m + 1) (phiPt t - t) = phiK m t := by
  simp only [phiK, Function.iterate_succ_apply, phiPt_sub, phi_sq]
  congr 1; abel

/-- the placed child of slot j is a sub-tile of the parent: its owned rhombs are owned by the parent -/
theorem TurtleSound.child_sub (τ : Typ) (j m : ℕ) :
    ∀ q ∈ quadsOf (slotTyp τ j, m, mulIso (Gm τ j (m + 1)) (0, 0)), q ∈ quadsOf (τ, m + 1, (0, 0)) := by
  intro q hq
  simp only [quadsOf, mulIso_one, actQ_one', List.map_id] at hq ⊢
  have hG : Gm τ j (m + 1) = scaleIso^[m] ((frameAt τ j).k, toPt (frameAt τ j).t) := by
    rw [scaleIso_iter]; simp only [Gm, phiK_Gm]
  rw [hG, ← ownedQuads_act, supertilePt, ← List.map_singleton, ← subAllPt_iter_map] at hq
  refine ownedQuads_mono _ _ ?_ q hq
  simp only [supertilePt, Function.iterate_succ_apply, subAllPt, List.append_nil]
  refine subAllPt_iter_mono m _ _ ?_
  intro x hx
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  exact frames_sub τ (frameAt τ j) (frameAt_mem τ j)

end

/-! ### the turtle step: equivariance and locality -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.edgePos_spec (q : QuadPt) (u v : Pt) (e : ℕ) (h : edgePos q u v = some e) :
    e < 4 ∧ getQ q e = u ∧ getQ q (e + 1) = v := by
  unfold edgePos at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  exact ⟨List.mem_range.mp h2, h1⟩

theorem TurtleSound.edgePos_isSome (q : QuadPt) (u v : Pt) (e : ℕ) (he : e < 4)
    (h1 : getQ q e = u) (h2 : getQ q (e + 1) = v) : ∃ e', edgePos q u v = some e' := by
  unfold edgePos
  cases hf : (List.range 4).find? (fun e => decide (getQ q e = u ∧ getQ q (e + 1) = v)) with
  | some e' => exact ⟨e', rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf e (List.mem_range.mpr he)
    simp [h1, h2] at this

theorem TurtleSound.findEdge_spec (qs : List QuadPt) (u v : Pt) (q : QuadPt) (e : ℕ)
    (h : findEdge qs u v = some (q, e)) : q ∈ qs ∧ e < 4 ∧ getQ q e = u ∧ getQ q (e + 1) = v := by
  induction qs with
  | nil => simp [findEdge] at h
  | cons q0 qs ih =>
    simp only [findEdge, List.findSome?_cons] at h ih
    cases hp : edgePos q0 u v with
    | some e0 =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, edgePos_spec q0 u v e0 hp⟩
    | none =>
      rw [hp] at h
      simp only [Option.map_none] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem TurtleSound.findEdge_isSome (qs : List QuadPt) (u v : Pt) (q : QuadPt) (hq : q ∈ qs) (e : ℕ) (he : e < 4)
    (h1 : getQ q e = u) (h2 : getQ q (e + 1) = v) : ∃ q' e', findEdge qs u v = some (q', e') := by
  induction qs with
  | nil => simp at hq
  | cons q0 qs ih =>
    simp only [findEdge, List.findSome?_cons] at ih ⊢
    cases hp : edgePos q0 u v with
    | some e0 => exact ⟨q0, e0, by simp⟩
    | none =>
      simp only [Option.map_none]
      rcases List.mem_cons.mp hq with rfl | hq
      · obtain ⟨e', he'⟩ := edgePos_isSome q u v e he h1 h2
        rw [hp] at he'; cases he'
      · exact ih hq

/-- with unique directed edges, the rhomb found is the rhomb that has the edge -/
theorem TurtleSound.findEdge_unique (qs : List QuadPt) (hu : EdgeUnique qs) (u v : Pt) (q : QuadPt) (hq : q ∈ qs)
    (e : ℕ) (he : e < 4) (h1 : getQ q e = u) (h2 : getQ q (e + 1) = v) : findEdge qs u v = some (q, e) := by
  obtain ⟨q', e', h⟩ := findEdge_isSome qs u v q hq e he h1 h2
  obtain ⟨hq', he', h1', h2'⟩ := findEdge_spec qs u v q' e' h
  obtain ⟨rfl, rfl⟩ := hu q' hq' q hq e' he' e he (h1'.trans h1.symm) (h2'.trans h2.symm)
  exact h

theorem TurtleSound.edgePos_act (g : Iso) (q : QuadPt) (u v : Pt) :
    edgePos (actQ g q) (isoPt g u) (isoPt g v) = edgePos q u v := by
  unfold edgePos
  simp only [getQ_act, (isoPt_injective g).eq_iff]

theorem TurtleSound.findEdge_act (g : Iso) (qs : List QuadPt) (u v : Pt) :
    findEdge (qs.map (actQ g)) (isoPt g u) (isoPt g v) = (findEdge qs u v).map (fun x => (actQ g x.1, x.2)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [findEdge, List.map_cons, List.findSome?_cons, edgePos_act] at ih ⊢
    cases edgePos q u v with
    | some e => simp
    | none => simpa using ih

theorem TurtleSound.edgeUnique_map (g : Iso) (qs : List QuadPt) (h : EdgeUnique qs) : EdgeUnique (qs.map (actQ g)) := by
  intro q hq q' hq' e he e' he' h1 h2
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hq'
  simp only [getQ_act, (isoPt_injective g).eq_iff] at h1 h2
  obtain ⟨rfl, rfl⟩ := h p hp p' hp' e he e' he' h1 h2
  exact ⟨rfl, rfl⟩

/-- the crossing map of an isometry -/
def TurtleSound.actCrs (g : Iso) (x : Crs) : Crs := (isoPt g x.1, isoPt g x.2.1, x.2.2)

theorem TurtleSound.advance_act (prog : List Cmd) (g : Iso) (q : QuadPt) :
    ∀ f e ci, advance prog (actQ g q) f e ci = (advance prog q f e ci).map (actCrs g)
  | 0, e, ci => rfl
  | f + 1, e, ci => by
    simp only [advance]
    split
    · simp [getQ_act, actCrs]
    · exact advance_act prog g q f _ _
    · exact advance_act prog g q f _ _
    · rfl

theorem TurtleSound.nextIn_act (prog : List Cmd) (g : Iso) (qs : List QuadPt) (x : Crs) :
    nextIn prog (qs.map (actQ g)) (actCrs g x) = actCrs g (nextIn prog qs x) := by
  unfold nextIn
  simp only [actCrs, findEdge_act]
  cases findEdge qs x.2.1 x.1 with
  | none => rfl
  | some p =>
    obtain ⟨q, eb⟩ := p
    simp only [Option.map_some]
    rw [advance_act]
    cases advance prog q prog.length ((eb + 2) % 4) (x.2.2.toNat + 1) <;> rfl

end

/-! ### the geometric axiom -/

/-- **Axiom (non-overlap).**  In the standard supertile of every type and level, no two owned rhombs
share a directed edge and the four directed edges of an owned rhomb are distinct.

The owned rhombs of a supertile are rhombs of a Penrose rhomb tiling (classical facts (F1)–(F3) of
`proof_unbounded.md`: the triangle tilings come from rhomb tilings, every rhomb is the union of a
positively and a negatively oriented triangle, mirror images across their base), so they do not
overlap; a rhomb lies on the left of each of its counter-clockwise directed edges.  For the base
level `B` the statement is checked by the O1 checker (`BTree.ofList` of the directed-edge keys,
`TurtleO1.buildTable`); this axiom is its extension to every level. -/
axiom TurtleGeom.edgeUnique (τ : TurtleSound.Typ) (m : ℕ) :
    TurtleSound.EdgeUnique (TurtleSound.ownedQuads (TurtleSound.supertilePt τ m))

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.edgeUnique_tile (X : Tile) : EdgeUnique (quadsOf X) :=
  edgeUnique_map X.2.2 _ (TurtleGeom.edgeUnique X.1 X.2.1)

/-- locality: if the crossing leads into a rhomb owned by the sub-tile Y, the step computed in the tile
X (whose directed edges are unique) is the step computed in Y -/
theorem TurtleSound.nextIn_sub (prog : List Cmd) (X Y : Tile) (hsub : ∀ q ∈ quadsOf Y, q ∈ quadsOf X)
    (x : Crs) (q : QuadPt) (hq : q ∈ quadsOf Y) (e : ℕ) (he : e < 4) (h1 : getQ q e = x.2.1)
    (h2 : getQ q (e + 1) = x.1) : nextIn prog (quadsOf X) x = nextIn prog (quadsOf Y) x := by
  obtain ⟨q', e', hY⟩ := findEdge_isSome (quadsOf Y) x.2.1 x.1 q hq e he h1 h2
  obtain ⟨hq', he', h1', h2'⟩ := findEdge_spec _ _ _ _ _ hY
  have hX := findEdge_unique (quadsOf X) (edgeUnique_tile X) x.2.1 x.1 q' (hsub q' hq') e' he' h1' h2'
  unfold nextIn
  rw [hX, hY]

end

/-! ## the certificate as a pass system -/

section
open TurtleO2 TurtleO1 TurtleSound

def TurtleSound.findPortC (c : Cert) (pid : ℕ) : Option Port :=
  match c.index with
  | some ix => findPort ix pid
  | none => none

def TurtleSound.findPassC (c : Cert) (pid : ℕ) : Option Pass :=
  match c.index with
  | some ix => findPass ix pid
  | none => none

/-- pass families: the ids of the pass table -/
abbrev TurtleSound.Fam (c : Cert) : Type := {pid : ℕ // (findPassC c pid).isSome}

def TurtleSound.passOf (c : Cert) (π : TurtleSound.Fam c) : Pass := (findPassC c π.1).get π.2

def TurtleSound.famOf (c : Cert) (pid : ℕ) : Option (TurtleSound.Fam c) :=
  if h : (findPassC c pid).isSome then some ⟨pid, h⟩ else none

def TurtleSound.famChildren (c : Cert) (π : TurtleSound.Fam c) : List (ℕ × TurtleSound.Fam c) :=
  (passOf c π).children.filterMap (fun ch => (famOf c ch.entry).map (fun f => (ch.slot, f)))

def TurtleSound.portParity (c : Cert) (pid : ℕ) : ℕ := ((findPortC c pid).map (·.parity)).getD 0

def TurtleSound.portTyp (c : Cert) (pid : ℕ) : TurtleSound.Typ :=
  ((findPortC c pid).map (fun p => normTyp p.col p.sign)).getD (true, true)

/-- `portAt` with the lowest level of the parity class `q` given explicitly -/
def TurtleSound.portAtQ (B q : ℕ) (p : Port) (m : ℕ) : Cross :=
  let s := (m - Rq B q) / 2
  { tail := iter (fun x => Z5.add (phi2 x) p.dtail) s p.ref.tail,
    head := iter (fun x => Z5.add (phi2 x) p.dhead) s p.ref.head,
    i := p.ref.i }

/-- the port `pid` at level m, in the parity class q -/
def TurtleSound.portCQ (c : Cert) (q pid m : ℕ) : TurtleSound.Crs :=
  ((findPortC c pid).map (fun p => toC (portAtQ c.B q p m))).getD 0

def TurtleSound.portD (c : Cert) (pid : ℕ) : TurtleSound.Crs :=
  ((findPortC c pid).map (fun p => (toPt p.dtail, toPt p.dhead, (0 : ℤ)))).getD 0

/-- N(π, B) from the O1 data -/
def TurtleSound.baseN (o1 : List O1Pass) (pid : ℕ) : ℕ := ((o1.find? (fun o => o.id == pid)).map (·.N)).getD 0

/-- N(π, B + k): N(π, B) from the O1 data, N(π, m+1) = Σ_children N(child, m) -/
def TurtleSound.lenAt (c : Cert) (o1 : List O1Pass) : ℕ → TurtleSound.Fam c → ℕ
  | 0, π => baseN o1 π.1
  | k + 1, π => ((famChildren c π).map (fun ch => lenAt c o1 k ch.2)).sum

end

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.portAtQ_rec (B q : ℕ) (p : Port) (m : ℕ) (hm : Rq B q ≤ m) :
    toC (portAtQ B q p (m + 2)) = (phiPt (phiPt (toC (portAtQ B q p m)).1) + toPt p.dtail,
      phiPt (phiPt (toC (portAtQ B q p m)).2.1) + toPt p.dhead, (toC (portAtQ B q p m)).2.2) := by
  have hs : (m + 2 - Rq B q) / 2 = (m - Rq B q) / 2 + 1 := by omega
  simp only [toC, portAtQ, hs, TurtleSound.iter_eq, Function.iterate_succ_apply', toPt_add, toPt_phi2]

theorem TurtleSound.Rq_eq (B q : ℕ) : Rq B q = if B % 2 = q then B else B + 1 := by
  unfold Rq; simp [beq_iff_eq]

theorem TurtleSound.portCQ_rec (c : Cert) (q pid m : ℕ) (hm : (if c.B % 2 = q then c.B else c.B + 1) ≤ m) :
    portCQ c q pid (m + 2) = (phiPt (phiPt (portCQ c q pid m).1), phiPt (phiPt (portCQ c q pid m).2.1),
      (portCQ c q pid m).2.2) + portD c pid := by
  unfold portCQ portD
  cases findPortC c pid with
  | none => simp [phiPt_zero]; rfl
  | some p =>
    simp only [Option.map_some, Option.getD_some]
    rw [portAtQ_rec c.B q p m (by rw [Rq_eq]; exact hm)]
    simp only [Prod.mk_add_mk, add_zero]

theorem TurtleSound.G_rec (τ : Typ) (j m : ℕ) (x d : Crs) :
    actCrs (Gm τ j (m + 2)) ((phiPt (phiPt x.1), phiPt (phiPt x.2.1), x.2.2) + d) =
      (phiPt (phiPt (actCrs (Gm τ j m) x).1), phiPt (phiPt (actCrs (Gm τ j m) x).2.1), (actCrs (Gm τ j m) x).2.2) +
        (rotK (frameAt τ j).k d.1, rotK (frameAt τ j).k d.2.1, d.2.2) := by
  obtain ⟨t, h, i⟩ := x
  obtain ⟨dt, dh, di⟩ := d
  have hG : ∀ s, phiK (m + 2) s = phiPt (phiPt (phiK m s)) := by
    intro s; simp only [phiK, Function.iterate_succ_apply']
  simp only [actCrs, Gm, isoPt, Prod.mk_add_mk, rotK_add, rotK_phiPt, phiPt_add, hG]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp only <;> abel

end

section
open TurtleO2 TurtleO1 TurtleSound

/-- **The certificate as a `PassSystem`.**  Crossings are (tail, head, command index) with points in
Z[ζ]; tiles are placed supertiles (type, level, isometry); the rhomb a crossing leads into is the
directed edge head → tail (the rhomb on its left); ownership and the turtle step are computed from
the owned rhombs of the tile (`ownedQuads`, `nextIn`).  Every field is proved; `next_sub` (locality)
uses the axiom `TurtleGeom.edgeUnique`. -/
def TurtleSound.turtleSystem (c : Cert) (prog : List Cmd) (o1 : List O1Pass) : PassSystem TurtleSound.Crs where
  Fam := TurtleSound.Fam c
  Typ := TurtleSound.Typ
  Slot := ℕ
  Tile := TurtleSound.Tile
  Rh := TurtleSound.Pt × TurtleSound.Pt
  Iso := TurtleSound.Iso
  B := c.B
  parity π := portParity c π.1
  typ π := portTyp c π.1
  children := famChildren c
  portIn π m := portCQ c (portParity c π.1) π.1 m
  portOut π m := portCQ c (portParity c π.1) (passOf c π).out m
  N π m := lenAt c o1 (m - c.B) π
  std τ m := (τ, m, (0, 0))
  slotTyp := slotTyp
  G := Gm
  enters x := (x.2.1, x.1)
  owned X r := ∃ q ∈ quadsOf X, ∃ e, e < 4 ∧ getQ q e = r.1 ∧ getQ q (e + 1) = r.2
  next X x := nextIn prog (quadsOf X) x
  sub Y X := ∀ q ∈ quadsOf Y, q ∈ quadsOf X
  actC := actCrs
  actT g X := (X.1, X.2.1, mulIso g X.2.2)
  actR g r := (isoPt g r.1, isoPt g r.2)
  Φ x := (phiPt (phiPt x.1), phiPt (phiPt x.2.1), x.2.2)
  dIn π := portD c π.1
  dOut π := portD c (passOf c π).out
  rot τ j d := (rotK (frameAt τ j).k d.1, rotK (frameAt τ j).k d.2.1, d.2.2)
  enters_act _ _ := rfl
  owned_act g X r := by
    simp only [quadsOf, List.mem_map]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, e, he, h1, h2⟩
      simp only [actQ_mul, getQ_act, (isoPt_injective g).eq_iff] at h1 h2
      exact ⟨actQ X.2.2 p, ⟨p, hp, rfl⟩, e, he, by rw [getQ_act]; exact h1, by rw [getQ_act]; exact h2⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, e, he, h1, h2⟩
      refine ⟨actQ (mulIso g X.2.2) p, ⟨p, hp, rfl⟩, e, he, ?_, ?_⟩
      · rw [actQ_mul, getQ_act, h1]
      · rw [actQ_mul, getQ_act, h2]
  next_act g X x _ := by
    show nextIn prog (quadsOf (X.1, X.2.1, mulIso g X.2.2)) (actCrs g x) = actCrs g (nextIn prog (quadsOf X) x)
    have : quadsOf (X.1, X.2.1, mulIso g X.2.2) = (quadsOf X).map (actQ g) := by
      simp only [quadsOf, List.map_map]
      congr 1
      funext q
      simp [actQ_mul]
    rw [this, nextIn_act]
  next_sub X Y x hsub hown := by
    obtain ⟨q, hq, e, he, h1, h2⟩ := hown
    exact nextIn_sub prog X Y hsub x q hq e he h1 h2
  owned_sub X Y r hsub hown := by
    obtain ⟨q, hq, e, he, h1, h2⟩ := hown
    exact ⟨q, hsub q hq, e, he, h1, h2⟩
  child_sub τ j m := child_sub τ j m
  portIn_rec π m hm := portCQ_rec c _ _ m hm
  portOut_rec π m hm := portCQ_rec c _ _ m hm
  G_rec τ j m x d := G_rec τ j m x d

end

/-! ## soundness of the checkers: O3, O2, the lengths -/

deriving instance DecidableEq for TurtleO2.Frame

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

/-- side conditions that the template checkers leave implicit: the frames are the standard ones,
every port has parity 0 or 1, and the entry port at level B of every O1 datum is inside the key range of
the O1 navigation table (its directed-edge key then cannot alias the key of an owned rhomb) -/
def TurtleSound.checkSide (c : Cert) (o1 : List O1Pass) : Bool :=
  c.frames == stdFrames && c.ports.all (fun p => decide (p.parity < 2)) &&
  o1.all (fun o => match findPortC c o.id with
    | some p => TurtleO1.inRange (portAt c.B p c.B).tail && TurtleO1.inRange (portAt c.B p c.B).head
    | none => false)

theorem TurtleSound.checkSide_sound (c : Cert) (o1 : List O1Pass) (h : checkSide c o1 = true) :
    c.frames = stdFrames ∧ (∀ p ∈ c.ports, p.parity < 2) ∧
    ∀ o ∈ o1, ∃ p, findPortC c o.id = some p ∧ TurtleO1.inRange (portAt c.B p c.B).tail = true ∧
      TurtleO1.inRange (portAt c.B p c.B).head = true := by
  simp only [checkSide, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun o ho => ?_⟩
  have h3 := h3 o ho
  split at h3
  · rename_i p hp
    simp only [Bool.and_eq_true] at h3
    exact ⟨p, hp, h3.1, h3.2⟩
  · cases h3

theorem TurtleSound.findPortC_eq {c : Cert} {ix : Idx} (h : c.index = some ix) (pid : ℕ) :
    findPortC c pid = findPort ix pid := by simp [findPortC, h]

theorem TurtleSound.findPassC_eq {c : Cert} {ix : Idx} (h : c.index = some ix) (pid : ℕ) :
    findPassC c pid = findPass ix pid := by simp [findPassC, h]

theorem TurtleSound.passOf_eq {c : Cert} {ix : Idx} (h : c.index = some ix) (π : Fam c) :
    findPass ix π.1 = some (passOf c π) := by
  unfold passOf
  rw [← findPassC_eq h]
  exact (Option.some_get _).symm

theorem TurtleSound.passOf_of {c : Cert} {ix : Idx} (h : c.index = some ix) (π : Fam c) (p : Pass)
    (hp : findPass ix π.1 = some p) : passOf c π = p := by
  have := passOf_eq h π
  rw [hp] at this
  exact (Option.some.inj this).symm

theorem TurtleSound.portParity_of {c : Cert} {ix : Idx} (h : c.index = some ix) (pid : ℕ) (p : Port)
    (hp : findPort ix pid = some p) : portParity c pid = p.parity := by
  simp [portParity, findPortC_eq h, hp]

theorem TurtleSound.portTyp_of {c : Cert} {ix : Idx} (h : c.index = some ix) (pid : ℕ) (p : Port)
    (hp : findPort ix pid = some p) : portTyp c pid = normTyp p.col p.sign := by
  simp [portTyp, findPortC_eq h, hp]

theorem TurtleSound.portCQ_of {c : Cert} {ix : Idx} (h : c.index = some ix) (q pid m : ℕ) (p : Port)
    (hp : findPort ix pid = some p) : portCQ c q pid m = toC (portAtQ c.B q p m) := by
  simp [portCQ, findPortC_eq h, hp]

theorem TurtleSound.portAt_eq (B : ℕ) (p : Port) (m : ℕ) : portAt B p m = portAtQ B p.parity p m := rfl

theorem TurtleSound.cross_beq (x y : Cross) (h : Cross.beq x y = true) : toC x = toC y := by
  simp only [Cross.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [toC, (TurtleSound.beq_iff _ _).mp h1, (TurtleSound.beq_iff _ _).mp h2, h3]

theorem TurtleSound.crossEq_sound (x y : Option Cross) (h : crossEq x y = true) :
    ∃ a b, x = some a ∧ y = some b ∧ toC a = toC b := by
  unfold crossEq at h
  split at h
  · rename_i a b
    exact ⟨a, b, rfl, rfl, cross_beq a b h⟩
  · cases h

theorem TurtleSound.toC_GCross (fr : Frame) (n : ℕ) (x : Cross) :
    toC (GCross fr (n + 1) x) = actCrs (fr.k, phiK n (toPt fr.t)) (toC x) := by
  simp [toC, GCross, G, actCrs, isoPt, toPt_add, toPt_rotN, toPt_phiN]

theorem TurtleSound.Gm_succ (τ : Typ) (j n : ℕ) :
    Gm τ j (n + 1) = ((frameAt τ j).k, phiK n (toPt (frameAt τ j).t)) := by
  simp [Gm, phiK_Gm]

/-- the frames found by the checker are the frames of the normalized type -/
theorem TurtleSound.frames_norm (col : ℕ) (sign : ℤ) (frs : List Frame)
    (h : findFramesIn stdFrames col sign = some frs) : framesFor (normTyp col sign) = frs := by
  have key : typCol (normTyp col sign) = col ∧ typSign (normTyp col sign) = sign := by
    unfold findFramesIn at h
    obtain ⟨f, hf, -⟩ := Option.map_eq_some_iff.mp h
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [stdFrames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at hp <;> obtain ⟨rfl, rfl⟩ := hp <;> decide
  unfold framesFor
  rw [key.1, key.2, h]
  rfl

theorem TurtleSound.frameAt_of (col : ℕ) (sign : ℤ) (frs : List Frame)
    (h : findFramesIn stdFrames col sign = some frs) (j : ℕ) (fr : Frame) (hj : frs[j]? = some fr) :
    frameAt (normTyp col sign) j = fr := by
  unfold frameAt
  rw [frames_norm col sign frs h, hj]
  rfl

/-! ### O3 -/

/-- **O3, as a proposition.**  For every pass family `p` of the table: its entry and exit ports and the
frames of its type exist; the exit port has the type and parity of the entry port; there is a child;
and for every child: its entry is a pass family of the table whose exit is the child's exit, its entry
and exit ports have the type of the slot (`fr.ccol`, `fr.csign`) and the opposite parity. -/
theorem TurtleSound.checkO3_sound {c : Cert} {ix : Idx} (h : checkO3 c ix = true) (p : Pass) (hp : p ∈ c.passes) :
    ∃ pin pout frs, findPort ix p.id = some pin ∧ findPort ix p.out = some pout ∧
      findFrames ix pin.col pin.sign = some frs ∧
      pout.col = pin.col ∧ pout.sign = pin.sign ∧ pout.parity = pin.parity ∧ p.children ≠ [] ∧
      ∀ ch ∈ p.children, ∃ a b fr pa, findPort ix ch.entry = some a ∧ findPort ix ch.exit = some b ∧
        frs[ch.slot]? = some fr ∧ findPass ix ch.entry = some pa ∧ pa.out = ch.exit ∧
        a.col = fr.ccol ∧ a.sign = fr.csign ∧ b.col = fr.ccol ∧ b.sign = fr.csign ∧
        a.parity = 1 - pin.parity ∧ b.parity = 1 - pin.parity := by
  have hp' := List.all_eq_true.mp h p hp
  unfold checkPassO3 at hp'
  split at hp'
  · rename_i pin pout h1 h2
    split at hp'
    · rename_i frs h3
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hp'
      obtain ⟨⟨⟨⟨⟨hc, hs⟩, hq⟩, hlen⟩, hall⟩, -⟩ := hp'
      refine ⟨pin, pout, frs, h1, h2, h3, hc.symm, hs.symm, hq.symm, List.ne_nil_of_length_pos hlen, ?_⟩
      intro ch hch
      have hc := hall ch hch
      unfold childOK at hc
      split at hc
      · rename_i a b fr pa e1 e2 e3 e4
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hc
        exact ⟨a, b, fr, pa, e1, e2, e3, e4, h11, h5, h6, h7, h8, h9, h10⟩
      · cases hc
    · cases hp'
  · cases hp'

theorem TurtleSound.forall₂_mem_right {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {y : β} (hy : y ∈ l2) : ∃ x ∈ l1, R x y := by
  induction h with
  | nil => simp at hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hxy⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-- the children of the model mirror the children of the pass table when every child entry is a pass -/
theorem TurtleSound.famChildren_forall₂ (c : Cert) (π : Fam c)
    (hall : ∀ ch ∈ (passOf c π).children, (findPassC c ch.entry).isSome) :
    List.Forall₂ (fun ch x => x.1 = ch.slot ∧ x.2.1 = ch.entry) (passOf c π).children (famChildren c π) := by
  unfold famChildren
  generalize (passOf c π).children = L at hall ⊢
  induction L with
  | nil => exact List.Forall₂.nil
  | cons ch L ih =>
    have h1 := hall ch List.mem_cons_self
    simp only [List.filterMap_cons, famOf, h1, dite_true, Option.map_some]
    exact List.Forall₂.cons ⟨rfl, rfl⟩ (ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)))

/-- the facts of O3 about one family, in the model -/
structure TurtleSound.FamFacts (c : Cert) (ix : Idx) (π : Fam c) where
  pin : Port
  pout : Port
  frs : List Frame
  hin : findPort ix π.1 = some pin
  hout : findPort ix (passOf c π).out = some pout
  hfrs : findFrames ix pin.col pin.sign = some frs
  hpar : pout.parity = pin.parity
  hne : (passOf c π).children ≠ []
  hch : ∀ ch ∈ (passOf c π).children, ∃ a b fr pa, findPort ix ch.entry = some a ∧ findPort ix ch.exit = some b ∧
        frs[ch.slot]? = some fr ∧ findPass ix ch.entry = some pa ∧ pa.out = ch.exit ∧
        a.col = fr.ccol ∧ a.sign = fr.csign ∧ b.col = fr.ccol ∧ b.sign = fr.csign ∧
        a.parity = 1 - pin.parity ∧ b.parity = 1 - pin.parity

theorem TurtleSound.famFacts {c : Cert} {ix : Idx} (hix : c.index = some ix) (h3 : checkO3 c ix = true)
    (π : Fam c) : Nonempty (FamFacts c ix π) := by
  have hp := passOf_eq hix π
  obtain ⟨hmem, hid⟩ := (findPass_iff c ix hix π.1 (passOf c π)).mp hp
  obtain ⟨pin, pout, frs, h1, h2, h3', -, -, hq, hne, hall⟩ := checkO3_sound h3 (passOf c π) hmem
  rw [hid] at h1
  exact ⟨⟨pin, pout, frs, h1, h2, h3', hq, hne, hall⟩⟩

/-- **O3 in the model** (hypothesis `hO3` of `PassInduction.H_all`) -/
theorem TurtleSound.model_O3 {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (hfr : c.frames = stdFrames) (h3 : checkO3 c ix = true) (π : (turtleSystem c prog o1).Fam) :
    (turtleSystem c prog o1).children π ≠ [] ∧
      ∀ ch ∈ (turtleSystem c prog o1).children π,
        (turtleSystem c prog o1).parity ch.2 = 1 - (turtleSystem c prog o1).parity π ∧
        (turtleSystem c prog o1).typ ch.2 = (turtleSystem c prog o1).slotTyp ((turtleSystem c prog o1).typ π) ch.1 := by
  obtain ⟨F⟩ := famFacts hix h3 π
  have hall : ∀ ch ∈ (passOf c π).children, (findPassC c ch.entry).isSome := by
    intro ch hch
    obtain ⟨a, b, fr, pa, -, -, -, e4, -⟩ := F.hch ch hch
    rw [findPassC_eq hix, e4]; rfl
  have h2 := famChildren_forall₂ c π hall
  have hfrs : findFramesIn stdFrames F.pin.col F.pin.sign = some F.frs := by
    have := F.hfrs; unfold findFrames at this
    rw [(index_fields c ix hix).2, hfr] at this; exact this
  show famChildren c π ≠ [] ∧ ∀ ch ∈ famChildren c π,
    portParity c ch.2.1 = 1 - portParity c π.1 ∧ portTyp c ch.2.1 = slotTyp (portTyp c π.1) ch.1
  constructor
  · intro hnil
    rw [hnil] at h2
    exact F.hne (List.forall₂_nil_right_iff.mp h2)
  · intro x hx
    obtain ⟨ch, hch, ⟨hs, he⟩⟩ := forall₂_mem_right h2 hx
    obtain ⟨a, b, fr, pa, e1, -, e3, -, -, hac, has, -, -, hap, -⟩ := F.hch ch hch
    rw [he, portParity_of hix _ a e1, portParity_of hix _ F.pin F.hin, portTyp_of hix _ a e1,
      portTyp_of hix _ F.pin F.hin, hs, slotTyp, frameAt_of _ _ _ hfrs ch.slot fr e3, hac, has]
    exact ⟨hap, rfl⟩

end

/-! ### O2 -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.placed_eq (ix : Idx) (frs : List Frame) (slot pid n : ℕ) (p : Port) (fr : Frame)
    (hp : findPort ix pid = some p) (hf : frs[slot]? = some fr) :
    placed ix frs slot pid (n + 1) = some (GCross fr (n + 1) (portAt ix.B p n)) := by
  simp [placed, hp, hf]

theorem TurtleSound.S_portIn {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (π : Fam c) (pin : Port) (h : findPort ix π.1 = some pin) (m : ℕ) :
    (turtleSystem c prog o1).portIn π m = toC (portAt c.B pin m) := by
  show portCQ c (portParity c π.1) π.1 m = _
  rw [portParity_of hix _ pin h, portCQ_of hix _ _ m pin h]
  rfl

theorem TurtleSound.S_portOut {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (π : Fam c) (pin pout : Port) (h : findPort ix π.1 = some pin) (h' : findPort ix (passOf c π).out = some pout)
    (hq : pout.parity = pin.parity) (m : ℕ) :
    (turtleSystem c prog o1).portOut π m = toC (portAt c.B pout m) := by
  show portCQ c (portParity c π.1) (passOf c π).out m = _
  rw [portParity_of hix _ pin h, portCQ_of hix _ _ m pout h', ← hq]
  rfl

/-- the placed entry and exit of a child, in the model and in the checker -/
theorem TurtleSound.S_placed {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (pin : Port) (frs : List Frame) (hfrs : findFramesIn stdFrames pin.col pin.sign = some frs) (n : ℕ)
    (ch : Child) (x : ℕ × Fam c) (hx : x.1 = ch.slot ∧ x.2.1 = ch.entry)
    (a b : Port) (fr : Frame) (pa : Pass) (e1 : findPort ix ch.entry = some a) (e2 : findPort ix ch.exit = some b)
    (e3 : frs[ch.slot]? = some fr) (e4 : findPass ix ch.entry = some pa) (e5 : pa.out = ch.exit)
    (hab : b.parity = a.parity) :
    (turtleSystem c prog o1).placedIn (normTyp pin.col pin.sign) n x = toC (GCross fr (n + 1) (portAt c.B a n)) ∧
    (turtleSystem c prog o1).placedOut (normTyp pin.col pin.sign) n x = toC (GCross fr (n + 1) (portAt c.B b n)) := by
  obtain ⟨s, f⟩ := x
  obtain ⟨hs, hf⟩ := hx
  simp only at hs hf
  subst hs
  have hG : Gm (normTyp pin.col pin.sign) ch.slot (n + 1) = (fr.k, phiK n (toPt fr.t)) := by
    rw [Gm_succ, frameAt_of _ _ _ hfrs ch.slot fr e3]
  have hpa : passOf c f = pa := passOf_of hix f pa (by rw [hf]; exact e4)
  constructor
  · show actCrs (Gm (normTyp pin.col pin.sign) ch.slot (n + 1)) ((turtleSystem c prog o1).portIn f n) = _
    rw [S_portIn prog o1 hix f a (by rw [hf]; exact e1), hG, toC_GCross]
  · show actCrs (Gm (normTyp pin.col pin.sign) ch.slot (n + 1)) ((turtleSystem c prog o1).portOut f n) = _
    rw [S_portOut prog o1 hix f a b (by rw [hf]; exact e1) (by rw [hpa, e5]; exact e2) hab, hG, toC_GCross]

/-- identities (b) along the children and (c) at the end -/
theorem TurtleSound.chain_sound {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (pin : Port) (frs : List Frame) (hfrs : findFramesIn stdFrames pin.col pin.sign = some frs) (n : ℕ)
    (outC : Cross) (P : Child → Prop)
    (hP : ∀ ch, P ch → ∃ a b fr pa, findPort ix ch.entry = some a ∧ findPort ix ch.exit = some b ∧
        frs[ch.slot]? = some fr ∧ findPass ix ch.entry = some pa ∧ pa.out = ch.exit ∧ b.parity = a.parity) :
    ∀ (tl : List Child) (xs : List (ℕ × Fam c)) (prev : Child) (x : ℕ × Fam c),
      P prev → (∀ ch ∈ tl, P ch) → (x.1 = prev.slot ∧ x.2.1 = prev.entry) →
      List.Forall₂ (fun ch x => x.1 = ch.slot ∧ x.2.1 = ch.entry) tl xs →
      chainOK ix frs (n + 1) outC prev tl = true →
      (turtleSystem c prog o1).linked (normTyp pin.col pin.sign) n (x :: xs) ∧
        toC outC = (turtleSystem c prog o1).lastOut (normTyp pin.col pin.sign) n x xs := by
  have hB := (index_fields c ix hix).1
  intro tl
  induction tl with
  | nil =>
    intro xs prev x hprev _ hx h2 hc
    cases h2
    obtain ⟨a, b, fr, pa, e1, e2, e3, e4, e5, hab⟩ := hP prev hprev
    refine ⟨trivial, ?_⟩
    simp only [chainOK] at hc
    obtain ⟨u, v, hu, hv, huv⟩ := crossEq_sound _ _ hc
    cases hu
    rw [placed_eq ix frs prev.slot prev.exit n b fr e2 e3, hB] at hv
    cases hv
    rw [huv]
    exact ((S_placed prog o1 hix pin frs hfrs n prev x hx a b fr pa e1 e2 e3 e4 e5 hab).2).symm
  | cons nxt tl ih =>
    intro xs prev x hprev htl hx h2 hc
    cases h2 with
    | cons hy h2 =>
      rename_i y ys
      simp only [chainOK, Bool.and_eq_true] at hc
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨a, b, fr, pa, e1, e2, e3, e4, e5, hab⟩ := hP prev hprev
      obtain ⟨a', b', fr', pa', e1', e2', e3', e4', e5', hab'⟩ := hP nxt (htl nxt List.mem_cons_self)
      obtain ⟨u, v, hu, hv, huv⟩ := crossEq_sound _ _ hc1
      rw [placed_eq ix frs prev.slot prev.exit n b fr e2 e3, hB] at hu
      rw [placed_eq ix frs nxt.slot nxt.entry n a' fr' e1' e3', hB] at hv
      cases hu; cases hv
      obtain ⟨hl, ho⟩ := ih ys nxt y (htl nxt List.mem_cons_self) (fun ch hch => htl ch (List.mem_cons_of_mem _ hch))
        hy h2 hc2
      refine ⟨⟨?_, hl⟩, ho⟩
      rw [(S_placed prog o1 hix pin frs hfrs n prev x hx a b fr pa e1 e2 e3 e4 e5 hab).2,
        (S_placed prog o1 hix pin frs hfrs n nxt y hy a' b' fr' pa' e1' e2' e3' e4' e5' hab').1, huv]

/-- **O2 at one level, in the model**: if the checker accepts the identities (a), (b), (c) of the family
at parent level `n + 1`, then `O2At π n` holds -/
theorem TurtleSound.model_O2At {c : Cert} {ix : Idx} (prog : List Cmd) (o1 : List O1Pass) (hix : c.index = some ix)
    (hfr : c.frames = stdFrames) (h3 : checkO3 c ix = true) (π : Fam c) (n : ℕ)
    (hlev : checkPassLevel ix (passOf c π) (n + 1) = true) : (turtleSystem c prog o1).O2At π n := by
  obtain ⟨F⟩ := famFacts hix h3 π
  have hB := (index_fields c ix hix).1
  have hid : (passOf c π).id = π.1 := ((findPass_iff c ix hix π.1 (passOf c π)).mp (passOf_eq hix π)).2
  have hfrs : findFramesIn stdFrames F.pin.col F.pin.sign = some F.frs := by
    have := F.hfrs; unfold findFrames at this
    rw [(index_fields c ix hix).2, hfr] at this; exact this
  have hall : ∀ ch ∈ (passOf c π).children, (findPassC c ch.entry).isSome := by
    intro ch hch
    obtain ⟨a, b, fr, pa, -, -, -, e4, -⟩ := F.hch ch hch
    rw [findPassC_eq hix, e4]; rfl
  have h2 := famChildren_forall₂ c π hall
  have hP : ∀ ch, ch ∈ (passOf c π).children → ∃ a b fr pa, findPort ix ch.entry = some a ∧
      findPort ix ch.exit = some b ∧ F.frs[ch.slot]? = some fr ∧ findPass ix ch.entry = some pa ∧
      pa.out = ch.exit ∧ b.parity = a.parity := by
    intro ch hch
    obtain ⟨a, b, fr, pa, e1, e2, e3, e4, e5, -, -, -, -, h9, h10⟩ := F.hch ch hch
    exact ⟨a, b, fr, pa, e1, e2, e3, e4, e5, by rw [h9, h10]⟩
  have htyp : (turtleSystem c prog o1).typ π = normTyp F.pin.col F.pin.sign := portTyp_of hix _ F.pin F.hin
  unfold checkPassLevel at hlev
  rw [hid, F.hin, F.hout] at hlev
  simp only at hlev
  rw [F.hfrs] at hlev
  generalize hL : (passOf c π).children = L at hlev h2 hP
  generalize hFC : famChildren c π = FC at h2
  cases L with
  | nil => exact absurd hL F.hne
  | cons ch0 rest =>
    simp only [Bool.and_eq_true] at hlev
    obtain ⟨ha, hc⟩ := hlev
    cases h2 with
    | cons hx0 hxs =>
      rename_i x0 xs
      have hfc : (turtleSystem c prog o1).children π = x0 :: xs := hFC
      unfold PassSystem.O2At
      rw [hfc]
      simp only
      rw [htyp]
      obtain ⟨u, v, hu, hv, huv⟩ := crossEq_sound _ _ ha
      cases hu
      obtain ⟨a, b, fr, pa, e1, e2, e3, e4, e5, hab⟩ := hP ch0 List.mem_cons_self
      rw [placed_eq ix F.frs ch0.slot ch0.entry n a fr e1 e3] at hv
      cases hv
      obtain ⟨hl, ho⟩ := chain_sound prog o1 hix F.pin F.frs hfrs n (portAt ix.B F.pout (n + 1))
        (fun ch => ch ∈ ch0 :: rest) hP rest xs ch0 x0 List.mem_cons_self
        (fun ch hch => List.mem_cons_of_mem _ hch) hx0 hxs hc
      refine ⟨?_, hl, ?_⟩
      · rw [S_portIn prog o1 hix π F.pin F.hin, (S_placed prog o1 hix F.pin F.frs hfrs n ch0 x0 hx0 a b fr pa
          e1 e2 e3 e4 e5 hab).1, ← hB, huv]
      · rw [S_portOut prog o1 hix π F.pin F.pout F.hin F.hout F.hpar, ← ho, hB]

end

/-! ### O1: the checker's supertile, rhombs and navigation table are the model's -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.subdivide_toTri (col : ℕ) (A B C : Z5) :
    (subdivide col A B C).map toTri = subdividePt (toTri (col, A, B, C)) := by
  unfold subdivide
  by_cases h : col = 0
  · subst h
    simp [toTri, subdividePt, toPt_add, toPt_sub, toPt_mulphi]
  · have h' : (col == 0) = false := by simpa using h
    simp [toTri, subdividePt, toPt_add, toPt_sub, toPt_mulphi, h']

theorem TurtleSound.subdivideAll_toTri (ts : List Tri) : (subdivideAll ts).map toTri = subAllPt (ts.map toTri) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨col, A, B, C⟩ := t
    simp only [subdivideAll, List.map_append, List.map_cons, subAllPt, ih, subdivide_toTri]

theorem TurtleSound.stdTriangle_toTri (col : ℕ) (sign : ℤ) :
    toTri (col, (stdTriangle col sign).1, (stdTriangle col sign).2.1, (stdTriangle col sign).2.2) =
      stdTriPt (normTyp col sign) := by
  by_cases h1 : col = 0 <;> by_cases h2 : 0 < sign
  · subst h1; simp [stdTriangle, toTri, stdTriPt, normTyp, h2] <;> decide
  · subst h1; simp [stdTriangle, toTri, stdTriPt, normTyp, h2] <;> decide
  · have h' : (col == 0) = false := by simpa using h1
    simp [stdTriangle, toTri, stdTriPt, normTyp, h2, h'] <;> decide
  · have h' : (col == 0) = false := by simpa using h1
    simp [stdTriangle, toTri, stdTriPt, normTyp, h2, h'] <;> decide

/-- the checker's supertile is the model's -/
theorem TurtleSound.supertile_toTri (col : ℕ) (sign : ℤ) (B : ℕ) :
    (supertile col sign B).map toTri = supertilePt (normTyp col sign) B := by
  unfold supertile supertilePt
  simp only [TurtleSound.iter_eq]
  rw [(Function.Semiconj.iterate_right (f := List.map toTri) (fun ts => subdivideAll_toTri ts) B)]
  simp only [List.map_cons, List.map_nil]
  rw [← stdTriangle_toTri]

theorem TurtleSound.orient_toPt (col : ℕ) (A B C : Z5) :
    orient col A B C = orientPt (col == 0) (toPt A) (toPt B) (toPt C) := by
  unfold orient orientPt
  by_cases h : col = 0
  · subst h
    simp only [beq_self_eq_true, if_true, TurtleSound.beq_iff, toPt_rotN, toPt_sub]
  · have h' : (col == 0) = false := by simpa using h
    simp only [h', Bool.false_eq_true, if_false, TurtleSound.beq_iff, toPt_rotN, toPt_sub]

def TurtleSound.toQuad (q : Quad) : QuadPt := (toPt q.v0, toPt q.v1, toPt q.v2, toPt q.v3)

theorem TurtleSound.getQ_toQuad (q : Quad) (e : ℕ) : getQ (toQuad q) e = toPt (q.get e) := by
  unfold getQ Quad.get toQuad
  split <;> rfl

/-- the checker's owned rhombs are the model's -/
theorem TurtleSound.rhombsOf_toQuad (ts : List Tri) (qs : List Quad) (h : rhombsOf ts = some qs) :
    ownedQuads (ts.map toTri) = qs.map toQuad := by
  induction ts generalizing qs with
  | nil => simp [rhombsOf] at h; subst h; rfl
  | cons t ts ih =>
    obtain ⟨col, A, B, C⟩ := t
    simp only [rhombsOf] at h
    simp only [List.map_cons, toTri, ownedQuads, ← orient_toPt]
    by_cases h0 : orient col A B C = 0
    · simp [h0] at h
    · rw [if_neg (by simpa using h0)] at h
      cases hr : rhombsOf ts with
      | none => rw [hr] at h; cases h
      | some qs' =>
        rw [hr] at h
        simp only at h
        have ih' := ih qs' hr
        by_cases h1 : orient col A B C = 1
        · rw [if_pos (by simpa using h1)] at h
          cases h
          rw [if_pos h1]
          simp only [List.map_cons, ih']
          simp [toQuad, toPt_add, toPt_sub]
        · rw [if_neg (by simpa using h1)] at h
          cases h
          rw [if_neg h1]
          exact ih'

/-! the navigation table -/

theorem TurtleSound.pointKey_toPt (k l : Z5) (h : toPt k = toPt l) : pointKey k = pointKey l := by
  simp only [toPt, Prod.mk.injEq] at h
  simp only [pointKey, Z5.canon, h]

theorem TurtleSound.edgeKey_toPt (u v u' v' : Z5) (h1 : toPt u = toPt u') (h2 : toPt v = toPt v') :
    edgeKey u v = edgeKey u' v' := by
  simp only [edgeKey, pointKey_toPt u u' h1, pointKey_toPt v v' h2]

theorem TurtleSound.pointKey_lt (k : Z5) (h : inRange k = true) : pointKey k < 17592186044416 := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [pointKey, digit]
  omega

theorem TurtleSound.pointKey_inj (k l : Z5) (hk : inRange k = true) (hl : inRange l = true)
    (h : pointKey k = pointKey l) : toPt k = toPt l := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hk hl
  simp only [pointKey, digit] at h
  simp only [toPt, Prod.mk.injEq]
  simp only [Z5.canon] at hk hl h
  omega

theorem TurtleSound.edgeKey_inj (u v u' v' : Z5) (hu : inRange u = true) (hv : inRange v = true)
    (hu' : inRange u' = true) (hv' : inRange v' = true) (h : edgeKey u v = edgeKey u' v') :
    toPt u = toPt u' ∧ toPt v = toPt v' := by
  have a := pointKey_lt v hv
  have b := pointKey_lt v' hv'
  simp only [edgeKey] at h
  have h1 : pointKey u = pointKey u' := by omega
  have h2 : pointKey v = pointKey v' := by omega
  exact ⟨pointKey_inj u u' hu hu' h1, pointKey_inj v v' hv hv' h2⟩

theorem TurtleSound.mem_entriesOf (qs : List Quad) (k : ℕ) (q : Quad) (e : ℕ) :
    (k, (q, e)) ∈ entriesOf qs ↔ q ∈ qs ∧ e < 4 ∧ k = edgeKey (q.get e) (q.get (e + 1)) := by
  induction qs with
  | nil => simp [entriesOf]
  | cons q0 qs ih =>
    simp only [entriesOf, List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨Or.inl rfl, by omega, rfl⟩
      · exact ⟨Or.inl rfl, by omega, rfl⟩
      · exact ⟨Or.inl rfl, by omega, rfl⟩
      · exact ⟨Or.inl rfl, by omega, rfl⟩
      · exact ⟨Or.inr h1, h2, h3⟩
    · rintro ⟨rfl | h1, h2, h3⟩
      · obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
        · exact Or.inl ⟨h3, rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨h3, rfl, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h3, rfl, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩)))

theorem TurtleSound.quad_get_inRange (q : Quad) (h : q.inRange = true) (e : ℕ) : inRange (q.get e) = true := by
  simp only [Quad.inRange, Bool.and_eq_true] at h
  unfold Quad.get
  split
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

/-- O1's table: unique directed edges, and lookups by key are lookups of the model's `findEdge` -/
theorem TurtleSound.table_sound (qs : List Quad) (t : Nav) (hin : qs.all Quad.inRange = true)
    (ht : BTree.ofList (entriesOf qs) = some t) :
    EdgeUnique (qs.map toQuad) ∧
    (∀ u v q e, inRange u = true → inRange v = true → BTree.find t (edgeKey u v) = some (q, e) →
      q ∈ qs ∧ findEdge (qs.map toQuad) (toPt u) (toPt v) = some (toQuad q, e)) ∧
    (∀ u v, BTree.find t (edgeKey u v) = none →
      ∀ Q ∈ qs.map toQuad, ∀ e, e < 4 → ¬ (getQ Q e = toPt u ∧ getQ Q (e + 1) = toPt v)) := by
  have hsound := BTree.ofList_sound _ _ ht
  have huniq : EdgeUnique (qs.map toQuad) := by
    intro Q hQ Q' hQ' e he e' he' h1 h2
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hQ
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hQ'
    rw [getQ_toQuad, getQ_toQuad] at h1 h2
    have hk := edgeKey_toPt _ _ _ _ h1 h2
    have m1 := (mem_entriesOf qs _ p e).mpr ⟨hp, he, rfl⟩
    have m2 := (mem_entriesOf qs _ p' e').mpr ⟨hp', he', hk⟩
    have := BTree.ofList_unique _ _ ht _ _ _ m1 m2
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨rfl, rfl⟩
  refine ⟨huniq, ?_, ?_⟩
  · intro u v q e hu hv hf
    have hm := (hsound _ _).mp hf
    obtain ⟨hq, he, hk⟩ := (mem_entriesOf qs _ q e).mp hm
    have hqin : q.inRange = true := List.all_eq_true.mp hin q hq
    obtain ⟨h1, h2⟩ := edgeKey_inj _ _ _ _ hu hv (quad_get_inRange q hqin e) (quad_get_inRange q hqin (e + 1)) hk
    refine ⟨hq, findEdge_unique _ huniq _ _ (toQuad q) (List.mem_map_of_mem hq) e he ?_ ?_⟩
    · rw [getQ_toQuad, h1]
    · rw [getQ_toQuad, h2]
  · intro u v hf Q hQ e he ⟨h1, h2⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hQ
    rw [getQ_toQuad] at h1 h2
    have hk := edgeKey_toPt _ _ _ _ h1 h2
    have hm := (mem_entriesOf qs _ p e).mpr ⟨hp, he, hk.symm⟩
    rw [(hsound _ _).mpr hm] at hf
    cases hf

end

/-! ### O1: the run of the checker is the trace of the model -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.nth_eq (l : List Cmd) (n : ℕ) : nth l n = l[n]? := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons c cs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem TurtleSound.advance_succ (prog : List Cmd) (Q : QuadPt) (f e ci : ℕ) : advance prog Q (f + 1) e ci =
    match nth prog (ci % prog.length) with
    | some Cmd.S => some (getQ Q e, getQ Q (e + 1), ((ci % prog.length : ℕ) : ℤ))
    | some Cmd.R => advance prog Q f ((e + 3) % 4) (ci + 1)
    | some Cmd.L => advance prog Q f ((e + 1) % 4) (ci + 1)
    | none => none := rfl

theorem TurtleSound.advance_mono (prog : List Cmd) (Q : QuadPt) :
    ∀ f e ci x, advance prog Q f e ci = some x → advance prog Q (f + 1) e ci = some x
  | 0, e, ci, x, h => by simp [advance] at h
  | f + 1, e, ci, x, h => by
    rw [advance_succ] at h ⊢
    split at h
    · exact h
    · exact advance_mono prog Q f _ _ x h
    · exact advance_mono prog Q f _ _ x h
    · cases h

theorem TurtleSound.advance_mono' (prog : List Cmd) (Q : QuadPt) (f e ci : ℕ) (x : Crs)
    (h : advance prog Q f e ci = some x) : ∀ k, advance prog Q (f + k) e ci = some x
  | 0 => h
  | k + 1 => advance_mono prog Q _ e ci x (advance_mono' prog Q f e ci x h k)

theorem TurtleSound.advance_det (prog : List Cmd) (Q : QuadPt) (f1 f2 e ci : ℕ) (x y : Crs)
    (h1 : advance prog Q f1 e ci = some x) (h2 : advance prog Q f2 e ci = some y) : x = y := by
  have a := advance_mono' prog Q f1 e ci x h1 f2
  have b := advance_mono' prog Q f2 e ci y h2 f1
  rw [Nat.add_comm] at b
  rw [a] at b
  exact Option.some.inj b

/-- the command index matters only modulo the length of the program -/
theorem TurtleSound.advance_mod (prog : List Cmd) (Q : QuadPt) :
    ∀ f e ci ci', ci % prog.length = ci' % prog.length → advance prog Q f e ci = advance prog Q f e ci'
  | 0, _, _, _, _ => rfl
  | f + 1, e, ci, ci', h => by
    rw [advance_succ, advance_succ, h]
    have h1 : (ci + 1) % prog.length = (ci' + 1) % prog.length := by rw [Nat.add_mod, h, ← Nat.add_mod]
    cases nth prog (ci' % prog.length) with
    | none => rfl
    | some cmd =>
      cases cmd with
      | S => rfl
      | R => exact advance_mod prog Q f _ _ _ h1
      | L => exact advance_mod prog Q f _ _ _ h1

theorem TurtleSound.advance_some_aux (prog : List Cmd) (Q : QuadPt) (hpos : 0 < prog.length) :
    ∀ d e ci, nth prog ((ci + d) % prog.length) = some Cmd.S → ∃ x, advance prog Q (d + 1) e ci = some x
  | 0, e, ci, h => by
    rw [Nat.add_zero] at h
    exact ⟨_, by rw [advance_succ, h]⟩
  | d + 1, e, ci, h => by
    cases hn : nth prog (ci % prog.length) with
    | none =>
      rw [nth_eq, List.getElem?_eq_none_iff] at hn
      have := Nat.mod_lt ci hpos
      omega
    | some cmd =>
      have h' : nth prog ((ci + 1 + d) % prog.length) = some Cmd.S := by
        rw [show ci + 1 + d = ci + (d + 1) by omega]; exact h
      cases cmd with
      | S => exact ⟨_, by rw [advance_succ, hn]⟩
      | R =>
        obtain ⟨x, hx⟩ := advance_some_aux prog Q hpos d ((e + 3) % 4) (ci + 1) h'
        exact ⟨x, by rw [advance_succ, hn]; exact hx⟩
      | L =>
        obtain ⟨x, hx⟩ := advance_some_aux prog Q hpos d ((e + 1) % 4) (ci + 1) h'
        exact ⟨x, by rw [advance_succ, hn]; exact hx⟩

/-- a program with an S reaches it within one cycle -/
theorem TurtleSound.advance_some (prog : List Cmd) (Q : QuadPt) (hS : prog.any (fun x => x == Cmd.S) = true)
    (e ci : ℕ) : ∃ x, advance prog Q prog.length e ci = some x := by
  obtain ⟨c0, hc0, hcS⟩ := List.any_eq_true.mp hS
  have hc : c0 = Cmd.S := by simpa using hcS
  subst hc
  obtain ⟨p, hp, hpS⟩ := List.getElem_of_mem hc0
  have hpos : 0 < prog.length := by omega
  have hr : ci % prog.length < prog.length := Nat.mod_lt _ hpos
  have hkey : (ci + (p + prog.length - ci % prog.length) % prog.length) % prog.length = p := by
    rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod_mod,
      show ci % prog.length + (p + prog.length - ci % prog.length) = p + prog.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  have hn : nth prog ((ci + (p + prog.length - ci % prog.length) % prog.length) % prog.length) = some Cmd.S := by
    rw [hkey, nth_eq, List.getElem?_eq_getElem hp, hpS]
  obtain ⟨x, hx⟩ := advance_some_aux prog Q hpos _ e ci hn
  have hd : (p + prog.length - ci % prog.length) % prog.length < prog.length := Nat.mod_lt _ hpos
  refine ⟨x, ?_⟩
  have := advance_mono' prog Q _ e ci x hx (prog.length - ((p + prog.length - ci % prog.length) % prog.length + 1))
  rwa [show (p + prog.length - ci % prog.length) % prog.length + 1 +
    (prog.length - ((p + prog.length - ci % prog.length) % prog.length + 1)) = prog.length by omega] at this

theorem TurtleSound.run_succ (t : Nav) (prog : List Cmd) (fuel : ℕ) (q : Quad) (e ci N : ℕ) :
    run t prog (fuel + 1) q e ci N =
    match nth prog (ci % prog.length) with
    | some Cmd.S =>
      match BTree.find t (edgeKey (q.get (e + 1)) (q.get e)) with
      | none => some (⟨q.get e, q.get (e + 1), ci % prog.length⟩, N + 1)
      | some (q', e2) => run t prog fuel q' ((e2 + 2) % 4) (ci + 1) (N + 1)
    | some Cmd.R => run t prog fuel q ((e + 3) % 4) (ci + 1) N
    | some Cmd.L => run t prog fuel q ((e + 1) % 4) (ci + 1) N
    | none => none := rfl

/-- the run of the checker from the state (q, e, ci) is a segment of the model's trace from the first
S-crossing, ending with an exit -/
theorem TurtleSound.run_sound (c : Cert) (prog : List Cmd) (o1 : List O1Pass)
    (hS : prog.any (fun x => x == Cmd.S) = true)
    (qs : List Quad) (t : Nav) (hin : qs.all Quad.inRange = true) (ht : BTree.ofList (entriesOf qs) = some t)
    (X : Tile) (hX : quadsOf X = qs.map toQuad) :
    ∀ F q e ci N ex n, q ∈ qs → run t prog F q e ci N = some (ex, n) →
      ∃ x, advance prog (toQuad q) prog.length e ci = some x ∧ N + 1 ≤ n ∧
        (turtleSystem c prog o1).Seg X x (n - N - 1) (toC ex) ∧
        ¬ (turtleSystem c prog o1).owned X ((turtleSystem c prog o1).enters (toC ex)) := by
  obtain ⟨-, hsome, hnone⟩ := table_sound qs t hin ht
  intro F
  induction F with
  | zero => intro q e ci N ex n _ h; simp [run] at h
  | succ F ih =>
    intro q e ci N ex n hq h
    have hqin : q.inRange = true := List.all_eq_true.mp hin q hq
    obtain ⟨z, hz⟩ := advance_some prog (toQuad q) hS e ci
    have hpos : 0 < prog.length := by
      obtain ⟨c0, hc0, -⟩ := List.any_eq_true.mp hS
      exact List.length_pos_of_mem hc0
    obtain ⟨l, hl⟩ : ∃ l, prog.length = l + 1 := ⟨prog.length - 1, by omega⟩
    rw [run_succ] at h
    cases hn : nth prog (ci % prog.length) with
    | none => rw [hn] at h; cases h
    | some cmd =>
      rw [hn] at h
      cases cmd with
      | S =>
        have hadv : advance prog (toQuad q) prog.length e ci =
            some (toPt (q.get e), toPt (q.get (e + 1)), ((ci % prog.length : ℕ) : ℤ)) := by
          rw [hl, advance_succ, ← hl, hn, getQ_toQuad, getQ_toQuad]
        refine ⟨_, hadv, ?_⟩
        cases hf : BTree.find t (edgeKey (q.get (e + 1)) (q.get e)) with
        | none =>
          rw [hf] at h
          cases h
          refine ⟨Nat.le_refl _, ?_, ?_⟩
          · rw [show N + 1 - N - 1 = 0 by omega]
            exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), rfl⟩
          rintro ⟨Q, hQ, e', he', h1, h2⟩
          rw [hX] at hQ
          exact hnone _ _ hf Q hQ e' he' ⟨h1, h2⟩
        | some r =>
          obtain ⟨q', e2⟩ := r
          rw [hf] at h
          simp only at h
          obtain ⟨hq', hfe⟩ := hsome _ _ q' e2 (quad_get_inRange q hqin _) (quad_get_inRange q hqin _) hf
          obtain ⟨y, hy, hn', hseg, hout⟩ := ih q' _ _ _ ex n hq' h
          refine ⟨by omega, ?_, hout⟩
          have hnext : (turtleSystem c prog o1).next X (toPt (q.get e), toPt (q.get (e + 1)),
              ((ci % prog.length : ℕ) : ℤ)) = y := by
            show nextIn prog (quadsOf X) _ = y
            unfold nextIn
            rw [hX]
            simp only
            rw [hfe]
            simp only [Int.toNat_natCast]
            rw [advance_mod prog _ _ _ _ (ci + 1) (by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]), hy]
            rfl
          have hown : (turtleSystem c prog o1).owned X ((turtleSystem c prog o1).enters
              (toPt (q.get e), toPt (q.get (e + 1)), ((ci % prog.length : ℕ) : ℤ))) := by
            obtain ⟨hm, he2, h1, h2⟩ := findEdge_spec _ _ _ _ _ hfe
            exact ⟨toQuad q', by rw [hX]; exact hm, e2, he2, h1, h2⟩
          have h1seg : (turtleSystem c prog o1).Seg X (toPt (q.get e), toPt (q.get (e + 1)),
              ((ci % prog.length : ℕ) : ℤ)) 1 y :=
            ⟨fun k hk => by obtain rfl : k = 0 := by omega
                            exact hown, hnext⟩
          have := PassSystem.Seg.concat (turtleSystem c prog o1) h1seg hseg
          rwa [show 1 + (n - (N + 1) - 1) = n - N - 1 by omega] at this
      | R =>
        obtain ⟨y, hy, hn', hseg, hout⟩ := ih q _ _ _ ex n hq h
        refine ⟨y, ?_, hn', hseg, hout⟩
        have hz' : advance prog (toQuad q) l ((e + 3) % 4) (ci + 1) = some z := by
          rw [hl, advance_succ, hn] at hz; exact hz
        rw [hz, advance_det prog _ _ _ _ _ z y hz' hy]
      | L =>
        obtain ⟨y, hy, hn', hseg, hout⟩ := ih q _ _ _ ex n hq h
        refine ⟨y, ?_, hn', hseg, hout⟩
        have hz' : advance prog (toQuad q) l ((e + 1) % 4) (ci + 1) = some z := by
          rw [hl, advance_succ, hn] at hz; exact hz
        rw [hz, advance_det prog _ _ _ _ _ z y hz' hy]

end

/-! ### O1 ⇒ H(B); all the hypotheses of `PassInduction.H_all` -/

section
open TurtleO2 TurtleO1 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.checkCertificate_sound (c : Cert) (h : checkCertificate c = true) :
    ∃ ix, c.index = some ix ∧ framesOK c = true ∧ checkPorts c = true ∧ checkO3 c ix = true ∧
      checkO2 c ix = true := by
  unfold checkCertificate at h
  split at h
  · cases h
  · rename_i ix hix
    simp only [Bool.and_eq_true] at h
    exact ⟨ix, hix, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem TurtleSound.tableFor_sound (B : ℕ) (col : ℕ) (sign : ℤ) (t : Nav)
    (h : tableFor (types.filterMap (fun ty => (buildTable ty.1 ty.2 B).map (fun t => (ty, t)))) col sign = some t) :
    buildTable col sign B = some t := by
  unfold tableFor at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hx
  have hm := List.mem_of_find?_eq_some hx
  obtain ⟨ty, -, hty⟩ := List.mem_filterMap.mp hm
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hty
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [← h1, ← h2]
  exact ht'

theorem TurtleSound.buildTable_sound (col : ℕ) (sign : ℤ) (B : ℕ) (t : Nav) (h : buildTable col sign B = some t) :
    ∃ qs, rhombsOf (supertile col sign B) = some qs ∧ qs.all Quad.inRange = true ∧
      BTree.ofList (entriesOf qs) = some t := by
  unfold buildTable at h
  split at h
  · cases h
  · rename_i qs hqs
    split_ifs at h with h1
    exact ⟨qs, hqs, by simpa using h1, h⟩

theorem TurtleSound.entryState_sound (t : Nav) (x : Cross) (q : Quad) (e ci : ℕ)
    (h : entryState t x = some (q, e, ci)) :
    ∃ eb, BTree.find t (edgeKey x.head x.tail) = some (q, eb) ∧ e = (eb + 2) % 4 ∧ ci = x.i + 1 := by
  unfold entryState at h
  split at h
  · rename_i q' eb h1 _
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨eb, h1, rfl, rfl⟩
  · cases h

theorem TurtleSound.quadsOf_std (τ : Typ) (m : ℕ) : quadsOf (τ, m, (0, 0)) = ownedQuads (supertilePt τ m) := by
  simp [quadsOf, actQ_one', List.map_id]

theorem TurtleSound.quadsOf_base (col : ℕ) (sign : ℤ) (B : ℕ) (qs : List Quad)
    (h : rhombsOf (supertile col sign B) = some qs) : quadsOf (normTyp col sign, B, (0, 0)) = qs.map toQuad := by
  rw [quadsOf_std, ← supertile_toTri, rhombsOf_toQuad _ _ h]

/-- **O1 ⇒ H(B) in the model** -/
theorem TurtleSound.model_H_base (c : Cert) (prog : List Cmd) (o1 : List O1Pass)
    (hc : checkCertificate c = true) (h1 : checkO1 c prog o1 = true) (hside : checkSide c o1 = true) :
    (turtleSystem c prog o1).H c.B := by
  obtain ⟨ix, hix, -, -, h3, -⟩ := checkCertificate_sound c hc
  have hB := (index_fields c ix hix).1
  obtain ⟨-, -, hrange⟩ := checkSide_sound c o1 hside
  unfold checkO1 at h1
  rw [hix] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨-, hS⟩, hcov, hall⟩ := h1
  unfold coversBase at hcov
  rw [hB] at hcov
  intro π hπ
  obtain ⟨F⟩ := famFacts hix h3 π
  have hid : (passOf c π).id = π.1 := ((findPass_iff c ix hix π.1 (passOf c π)).mp (passOf_eq hix π)).2
  have hmem : passOf c π ∈ c.passes := ((findPass_iff c ix hix π.1 (passOf c π)).mp (passOf_eq hix π)).1
  have hpar : F.pin.parity = c.B % 2 := by
    have : (turtleSystem c prog o1).parity π = portParity c π.1 := rfl
    rw [this, portParity_of hix _ F.pin F.hin] at hπ
    exact hπ
  -- an O1 datum of the family
  have hcov' := List.all_eq_true.mp hcov _ hmem
  rw [hid, F.hin] at hcov'
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq] at hcov'
  have hex : ∃ o ∈ o1, o.id = π.1 := by
    rcases hcov' with h | h
    · exact absurd hpar h
    · exact h
  obtain ⟨o', ho'⟩ : ∃ o', o1.find? (fun o => o.id == π.1) = some o' := by
    cases h : o1.find? (fun o => o.id == π.1) with
    | some o' => exact ⟨o', rfl⟩
    | none =>
      obtain ⟨o, ho, hoid⟩ := hex
      have := List.find?_eq_none.mp h o ho
      simp [hoid] at this
  have ho'mem := List.mem_of_find?_eq_some ho'
  have ho'id : o'.id = π.1 := by simpa using List.find?_some ho'
  have hN : (turtleSystem c prog o1).N π c.B = o'.N := by
    show lenAt c o1 (c.B - c.B) π = o'.N
    rw [Nat.sub_self]
    show baseN o1 π.1 = o'.N
    simp [baseN, ho']
  -- the check of that datum
  have hc1 := List.all_eq_true.mp hall o' ho'mem
  unfold checkPassO1 at hc1
  rw [hB, ho'id, passOf_eq hix π] at hc1
  simp only at hc1
  rw [hid, F.hin, F.hout] at hc1
  simp only [Bool.and_eq_true, beq_iff_eq] at hc1
  obtain ⟨-, hc1⟩ := hc1
  split at hc1
  · cases hc1
  · rename_i tbl htbl
    split at hc1
    · cases hc1
    · rename_i q0 e0 ci0 hent
      split at hc1
      · rename_i ex n hrun
        simp only [Bool.and_eq_true, beq_iff_eq] at hc1
        obtain ⟨hexit, hnN⟩ := hc1
        obtain ⟨qs, hqs, hin, ht⟩ := buildTable_sound _ _ _ _ (tableFor_sound _ _ _ _ htbl)
        obtain ⟨eb, hfind, he0, hci0⟩ := entryState_sound _ _ _ _ _ hent
        have hX : quadsOf (normTyp F.pin.col F.pin.sign, c.B, (0, 0)) = qs.map toQuad := quadsOf_base _ _ _ _ hqs
        obtain ⟨p', hp', hr1, hr2⟩ := hrange o' ho'mem
        rw [ho'id, findPortC_eq hix, F.hin] at hp'
        cases hp'
        obtain ⟨hq0, hfe⟩ := (table_sound qs tbl hin ht).2.1 _ _ q0 eb hr2 hr1 hfind
        obtain ⟨x1, hx1, hn1, hseg, hout⟩ := run_sound c prog o1 hS qs tbl hin ht _ hX _ q0 e0 ci0 0 ex n hq0 hrun
        have htyp : (turtleSystem c prog o1).typ π = normTyp F.pin.col F.pin.sign := portTyp_of hix _ F.pin F.hin
        have hstd : (turtleSystem c prog o1).std ((turtleSystem c prog o1).typ π) c.B =
            (normTyp F.pin.col F.pin.sign, c.B, (0, 0)) := by rw [htyp]; rfl
        have hexit' : toC ex = (turtleSystem c prog o1).portOut π c.B := by
          rw [S_portOut prog o1 hix π F.pin F.pout F.hin F.hout F.hpar]
          exact cross_beq _ _ hexit
        rw [hstd, S_portIn prog o1 hix π F.pin F.hin, hN, ← hexit', ← hnN]
        refine ⟨by omega, ?_, hout⟩
        -- the entry crossing leads into the rhomb q0, and the next crossing is x1
        have hown : (turtleSystem c prog o1).owned (normTyp F.pin.col F.pin.sign, c.B, (0, 0))
            ((turtleSystem c prog o1).enters (toC (portAt c.B F.pin c.B))) := by
          obtain ⟨hm, he2, h1, h2⟩ := findEdge_spec _ _ _ _ _ hfe
          exact ⟨toQuad q0, by rw [hX]; exact hm, eb, he2, h1, h2⟩
        have hnext : (turtleSystem c prog o1).next (normTyp F.pin.col F.pin.sign, c.B, (0, 0))
            (toC (portAt c.B F.pin c.B)) = x1 := by
          show nextIn prog (quadsOf _) _ = x1
          unfold nextIn
          rw [hX]
          simp only [toC]
          rw [hfe]
          simp only [Int.toNat_natCast]
          rw [← he0, ← hci0, hx1]
          rfl
        have h1seg : (turtleSystem c prog o1).Seg (normTyp F.pin.col F.pin.sign, c.B, (0, 0))
            (toC (portAt c.B F.pin c.B)) 1 x1 :=
          ⟨fun k hk => by obtain rfl : k = 0 := by omega
                          exact hown, hnext⟩
        have := PassSystem.Seg.concat (turtleSystem c prog o1) h1seg hseg
        rwa [show 1 + (n - 0 - 1) = n by omega] at this
      · cases hc1

theorem TurtleSound.childSum_eq (c : Cert) (prog : List Cmd) (o1 : List O1Pass) (m : ℕ) :
    ∀ L : List (ℕ × Fam c), (turtleSystem c prog o1).childSum m L =
      (L.map (fun ch => (turtleSystem c prog o1).N ch.2 m)).sum
  | [] => rfl
  | ch :: L => by
    show (turtleSystem c prog o1).N ch.2 m + (turtleSystem c prog o1).childSum m L = _
    rw [childSum_eq c prog o1 m L, List.map_cons, List.sum_cons]

/-- the lengths obey N(π, m+1) = Σ_children N(child, m) (hypothesis `hN` of `H_all`) -/
theorem TurtleSound.model_N (c : Cert) (prog : List Cmd) (o1 : List O1Pass) (π : Fam c) (m : ℕ) (hm : c.B ≤ m) :
    (turtleSystem c prog o1).N π (m + 1) =
      (turtleSystem c prog o1).childSum m ((turtleSystem c prog o1).children π) := by
  rw [childSum_eq]
  show lenAt c o1 (m + 1 - c.B) π = ((famChildren c π).map (fun ch => lenAt c o1 (m - c.B) ch.2)).sum
  rw [show m + 1 - c.B = (m - c.B) + 1 by omega]
  rfl

/-- **O2 in the model at the two lowest levels of each parity class** (hypothesis `hO2` of `H_all`) -/
theorem TurtleSound.model_O2 (c : Cert) (prog : List Cmd) (o1 : List O1Pass)
    (hc : checkCertificate c = true) (hside : checkSide c o1 = true) (π : Fam c) :
    (turtleSystem c prog o1).O2At π ((turtleSystem c prog o1).n0 ((turtleSystem c prog o1).parity π)) ∧
    (turtleSystem c prog o1).O2At π ((turtleSystem c prog o1).n0 ((turtleSystem c prog o1).parity π) + 2) := by
  obtain ⟨ix, hix, -, -, h3, h2⟩ := checkCertificate_sound c hc
  have hB := (index_fields c ix hix).1
  obtain ⟨hfr, hpar2, -⟩ := checkSide_sound c o1 hside
  obtain ⟨F⟩ := famFacts hix h3 π
  have hid : (passOf c π).id = π.1 := ((findPass_iff c ix hix π.1 (passOf c π)).mp (passOf_eq hix π)).2
  have hmem : passOf c π ∈ c.passes := ((findPass_iff c ix hix π.1 (passOf c π)).mp (passOf_eq hix π)).1
  have hq : F.pin.parity < 2 := hpar2 F.pin ((findPort_iff c ix hix π.1 F.pin).mp F.hin).1
  have hp := List.all_eq_true.mp h2 _ hmem
  unfold checkPassO2 at hp
  rw [hid, F.hin] at hp
  simp only [levelsFor, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
  have hpar : (turtleSystem c prog o1).parity π = F.pin.parity := portParity_of hix _ F.pin F.hin
  have hn0 : (turtleSystem c prog o1).n0 ((turtleSystem c prog o1).parity π) + 1 =
      (if (ix.B + 1) % 2 = F.pin.parity then ix.B + 1 else ix.B + 2) := by
    rw [hpar]
    show (if c.B % 2 = F.pin.parity then c.B + 1 else c.B) + 1 = _
    rw [hB]
    split_ifs <;> omega
  obtain ⟨hl1, hl2⟩ := hp
  simp only [beq_iff_eq] at hl1 hl2
  constructor
  · apply model_O2At prog o1 hix hfr h3 π
    rw [hn0]; exact hl1
  · apply model_O2At prog o1 hix hfr h3 π
    rw [show (turtleSystem c prog o1).n0 ((turtleSystem c prog o1).parity π) + 2 + 1 =
      (turtleSystem c prog o1).n0 ((turtleSystem c prog o1).parity π) + 1 + 2 by omega, hn0]
    exact hl2

/-- Lemma 2 (exit property) for the model of a certificate: given H(m), the placed exit of the last child
of every family of parity m + 1 leads to a rhomb not owned by the parent (hypothesis `hL2` of `H_all`) -/
def TurtleSound.ExitProperty (c : Cert) (prog : List Cmd) (o1 : List O1Pass) : Prop :=
  ∀ m, c.B ≤ m → (turtleSystem c prog o1).H m → ∀ π, (turtleSystem c prog o1).parity π = (m + 1) % 2 →
    ∀ ch0 L, (turtleSystem c prog o1).children π = ch0 :: L →
    ¬ (turtleSystem c prog o1).owned
      ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ π) (m + 1))
      ((turtleSystem c prog o1).enters ((turtleSystem c prog o1).lastOut ((turtleSystem c prog o1).typ π) m ch0 L))

/-- **The checkers imply H(m) for every m ≥ B** (with Lemma 2 as the hypothesis `ExitProperty`):
`checkCertificate` (frames, port deltas, O3, O2), `checkO1` (base simulation) and the side conditions
`checkSide` give the hypotheses O1, O2, O3 and the length recursion of `PassInduction.H_all`. -/
theorem TurtleSound.model_H_all (c : Cert) (prog : List Cmd) (o1 : List O1Pass)
    (hc : checkCertificate c = true) (h1 : checkO1 c prog o1 = true) (hside : checkSide c o1 = true)
    (hL2 : ExitProperty c prog o1) : ∀ m, c.B ≤ m → (turtleSystem c prog o1).H m := by
  obtain ⟨ix, hix, -, -, h3, -⟩ := checkCertificate_sound c hc
  obtain ⟨hfr, -, -⟩ := checkSide_sound c o1 hside
  exact PassInduction.H_all (turtleSystem c prog o1) (model_H_base c prog o1 hc h1 hside)
    (model_O2 c prog o1 hc hside) (model_O3 prog o1 hix hfr h3) (fun π m hm => model_N c prog o1 π m hm) hL2

end

/-! ## soundness of O4 / O6 (`checkO46`) -/

section
open TurtleO2 TurtleO1 TurtleO46 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleO2.BTree.ofList_size {α : Type} (xs : List (ℕ × α)) (t : BTree α) (h : BTree.ofList xs = some t) :
    t.size = xs.length := by
  unfold BTree.ofList at h
  simp only at h
  split_ifs at h with h1 h2
  cases h
  have : (BTree.build 64 (BTree.msort 64 xs)).size = (BTree.msort 64 xs).length := by simpa using h2
  rw [this, (BTree.msort_perm 64 xs).length_eq]

/-- the length of the pass family `id` at level m in the model (0 if `id` is not a pass family) -/
def TurtleSound.NId (c : Cert) (o1 : List O1Pass) (id m : ℕ) : ℕ :=
  match famOf c id with
  | some π => lenAt c o1 (m - c.B) π
  | none => 0

/-- the number of pass families of parity q (the dimension of the two-level expansion matrix M) -/
def TurtleSound.famCount (c : Cert) (q : ℕ) : ℕ :=
  (c.passes.filter (fun p => (findPortC c p.id).map (·.parity) == some q)).length

theorem TurtleSound.famOf_some (c : Cert) (id : ℕ) (h : (findPassC c id).isSome) : famOf c id = some ⟨id, h⟩ := by
  simp [famOf, h]

theorem TurtleSound.NId_fam (c : Cert) (prog : List Cmd) (o1 : List O1Pass) (π : Fam c) (m : ℕ) :
    NId c o1 π.1 m = (turtleSystem c prog o1).N π m := by
  simp only [NId, famOf_some c π.1 π.2]
  rfl

theorem TurtleSound.sum_famChildren (c : Cert) (o1 : List O1Pass) (k : ℕ) (L : List Child) :
    ((L.filterMap (fun ch => (famOf c ch.entry).map (fun f => (ch.slot, f)))).map
      (fun ch => lenAt c o1 k ch.2)).sum = (L.map (fun ch => NId c o1 ch.entry (k + c.B))).sum := by
  induction L with
  | nil => rfl
  | cons ch L ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases h : famOf c ch.entry with
    | none => simp [NId, h, ih]
    | some f => simp [NId, h, ih]

theorem TurtleSound.NId_succ (c : Cert) (o1 : List O1Pass) (id m : ℕ) (p : Pass) (hp : findPassC c id = some p)
    (hm : c.B ≤ m) : NId c o1 id (m + 1) = (p.children.map (fun ch => NId c o1 ch.entry m)).sum := by
  have hs : (findPassC c id).isSome := by rw [hp]; rfl
  have hNId : NId c o1 id (m + 1) = lenAt c o1 (m + 1 - c.B) ⟨id, hs⟩ := by simp only [NId, famOf_some c id hs]
  rw [hNId, show m + 1 - c.B = (m - c.B) + 1 by omega]
  simp only [lenAt, famChildren]
  have hpo : passOf c ⟨id, hs⟩ = p := by simp [passOf, hp]
  rw [hpo, sum_famChildren, show m - c.B + c.B = m by omega]

theorem TurtleSound.get_eq_find (v : Lengths) (id : ℕ) : get v id = (BTree.find v id).getD 0 := by
  rw [get_eq_getImpl]
  induction v with
  | leaf => rfl
  | node l key val r ihl ihr =>
    simp only [getImpl, BTree.find]
    by_cases h1 : key ≤ id
    · have e1 : Nat.ble key id = true := Nat.ble_eq.mpr h1
      by_cases h2 : key = id
      · subst h2
        have e2 : Nat.beq key key = true := Nat.beq_eq.mpr rfl
        simp [e1]
      · have e2 : Nat.beq key id = false := by
          cases h : Nat.beq key id
          · rfl
          · exact absurd (Nat.beq_eq.mp h) h2
        rw [e1, e2, if_neg (by omega), if_pos (by omega)]
        exact ihr
    · have e1 : Nat.ble key id = false := by
        cases h : Nat.ble key id
        · rfl
        · exact absurd (Nat.ble_eq.mp h) h1
      rw [e1, if_pos (by omega)]
      exact ihl

theorem TurtleSound.sumOf_eq (v : Lengths) (ids : List ℕ) : sumOf v ids = (ids.map (get v)).sum := by
  rw [sumOf_eq_sumOfImpl]
  induction ids with
  | nil => rfl
  | cons id ids ih => simp only [sumOfImpl, List.map_cons, List.sum_cons, ← ih]; rfl

theorem TurtleSound.find_step (v : Lengths) (t : Table) (id : ℕ) :
    BTree.find (step v t) id = (BTree.find t id).map (sumOf v) := by
  rw [step_eq_stepImpl]
  induction t with
  | leaf => rfl
  | node l k chs r ihl ihr =>
    simp only [stepImpl, BTree.find]
    split_ifs
    · exact ihl
    · exact ihr
    · rfl

theorem TurtleSound.find_baseVec (o1t : BTree ℕ) : ∀ (t : Table) (v : Lengths), baseVec o1t t = some v →
    ∀ id chs, BTree.find t id = some chs → ∃ n, BTree.find o1t id = some n ∧ BTree.find v id = some n
  | .leaf, v, _, id, chs, hf => by simp [BTree.find] at hf
  | .node l k chs0 r, v, h, id, chs, hf => by
    simp only [baseVec] at h
    split at h
    · rename_i l' n r' hl hn hr
      cases h
      simp only [BTree.find] at hf ⊢
      split_ifs at hf ⊢ with h1 h2
      · exact find_baseVec o1t l l' hl id chs hf
      · exact find_baseVec o1t r r' hr id chs hf
      · have : id = k := by omega
        subst this
        exact ⟨n, hn, rfl⟩
    · cases h

theorem TurtleSound.keysIn_sound (u : Table) (ids : List ℕ) (h : keysIn u ids = true) :
    ∀ x ∈ ids, (BTree.find u x).isSome := by
  induction ids with
  | nil => simp
  | cons x xs ih =>
    simp only [keysIn, Bool.and_eq_true] at h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact ih h.2 y hy

theorem TurtleSound.closedIn_sound (u : Table) : ∀ (t : Table), closedIn u t = true →
    ∀ id chs, BTree.find t id = some chs → ∀ x ∈ chs, (BTree.find u x).isSome
  | .leaf, _, id, chs, hf => by simp [BTree.find] at hf
  | .node l k chs0 r, h, id, chs, hf => by
    simp only [closedIn, Bool.and_eq_true] at h
    simp only [BTree.find] at hf
    split_ifs at hf with h1 h2
    · exact closedIn_sound u l h.1.2 id chs hf
    · exact closedIn_sound u r h.2 id chs hf
    · obtain rfl : chs0 = chs := Option.some.inj hf
      exact keysIn_sound u chs0 h.1.1

theorem TurtleSound.tableOf_find {c : Cert} {ix : Idx} (hix : c.index = some ix) (q : ℕ) (tq : Table)
    (h : tableOf c ix q = some tq) (id : ℕ) (chs : List ℕ) :
    BTree.find tq id = some chs ↔
      ∃ p, findPass ix id = some p ∧ famParity ix p = some q ∧ chs = p.children.map (·.entry) := by
  unfold tableOf at h
  rw [BTree.ofList_sound _ _ h]
  simp only [List.mem_map, familiesOf, List.mem_filter, Prod.mk.injEq, beq_iff_eq]
  constructor
  · rintro ⟨p, ⟨hp, hq⟩, rfl, rfl⟩
    exact ⟨p, (findPass_iff c ix hix p.id p).mpr ⟨hp, rfl⟩, hq, rfl⟩
  · rintro ⟨p, hp, hq, rfl⟩
    obtain ⟨hm, rfl⟩ := (findPass_iff c ix hix id p).mp hp
    exact ⟨p, ⟨hm, hq⟩, rfl, rfl⟩

theorem TurtleSound.tableOf_size {c : Cert} {ix : Idx} (hix : c.index = some ix) (q : ℕ) (tq : Table)
    (h : tableOf c ix q = some tq) : tq.size = famCount c q := by
  unfold tableOf at h
  rw [BTree.ofList_size _ _ h, List.length_map]
  unfold familiesOf famCount famParity
  congr 1
  apply List.filter_congr
  intro p _
  rw [findPortC_eq hix]

/-- the length vector `v` of the checker represents the lengths of the families of the table `t` at level m -/
def TurtleSound.Rep (c : Cert) (o1 : List O1Pass) (t : Table) (v : Lengths) (m : ℕ) : Prop :=
  ∀ id chs, BTree.find t id = some chs → get v id = NId c o1 id m

theorem TurtleSound.rep_step {c : Cert} {ix : Idx} (hix : c.index = some ix) (o1 : List O1Pass) (qB : ℕ)
    (tA tB : Table) (htB : tableOf c ix qB = some tB) (hcl : closedIn tA tB = true)
    (v : Lengths) (m : ℕ) (hm : c.B ≤ m) (hrep : Rep c o1 tA v m) : Rep c o1 tB (step v tB) (m + 1) := by
  intro id chs hf
  obtain ⟨p, hp, -, rfl⟩ := (tableOf_find hix qB tB htB id chs).mp hf
  rw [get_eq_find, find_step, hf, Option.map_some, Option.getD_some, sumOf_eq,
    NId_succ c o1 id m p (by rw [findPassC_eq hix]; exact hp) hm, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ch hch
  have hin := closedIn_sound tA tB hcl id _ hf ch.entry (List.mem_map_of_mem hch)
  obtain ⟨chs', hchs'⟩ := Option.isSome_iff_exists.mp hin
  exact hrep ch.entry chs' hchs'

theorem TurtleSound.iterate_sound {c : Cert} {ix : Idx} (hix : c.index = some ix) (o1 : List O1Pass) (q : ℕ)
    (tq tq' : Table) (htq : tableOf c ix q = some tq) (htq' : tableOf c ix (1 - q) = some tq')
    (hcl1 : closedIn tq' tq = true) (hcl2 : closedIn tq tq' = true) (r : O6Root) (hr : (BTree.find tq r.id).isSome) :
    ∀ k (v : Lengths) (m : ℕ), c.B ≤ m → Rep c o1 tq v m → iterate tq tq' (grand tq' tq) r k v = true →
      ∀ s, s < k → (NId c o1 r.id (m + 2 * s + 2) : ℤ) = r.a * NId c o1 r.id (m + 2 * s) + r.b := by
  obtain ⟨chr, hchr⟩ := Option.isSome_iff_exists.mp hr
  intro k
  induction k with
  | zero => intro v m _ _ _ s hs; omega
  | succ k ih =>
    intro v m hm hrep hit s hs
    simp only [iterate, Bool.and_eq_true, beq_iff_eq] at hit
    obtain ⟨⟨-, hrec⟩, hit⟩ := hit
    have hrep1 := rep_step hix o1 (1 - q) tq tq' htq' hcl2 v m hm hrep
    have hrep2 := rep_step hix o1 q tq' tq htq hcl1 _ (m + 1) (by omega) hrep1
    cases s with
    | zero =>
      rw [hrep2 r.id chr hchr, hrep r.id chr hchr] at hrec
      simpa using hrec
    | succ s =>
      have := ih _ (m + 2) (by omega) hrep2 hit s (by omega)
      rw [show m + 2 * (s + 1) + 2 = m + 2 + 2 * s + 2 by omega, show m + 2 * (s + 1) = m + 2 + 2 * s by omega]
      exact this

theorem TurtleSound.rep_base {c : Cert} {ix : Idx} (hix : c.index = some ix) (o1 : List O1Pass) (o1t : BTree ℕ)
    (ho1 : baseLengths o1 = some o1t) (q : ℕ) (tq : Table) (htq : tableOf c ix q = some tq) (v : Lengths)
    (hv : baseVec o1t tq = some v) : Rep c o1 tq v c.B := by
  intro id chs hf
  obtain ⟨n, hn, hvn⟩ := find_baseVec o1t tq v hv id chs hf
  obtain ⟨p, hp, -, -⟩ := (tableOf_find hix q tq htq id chs).mp hf
  have hs : (findPassC c id).isSome := by rw [findPassC_eq hix, hp]; rfl
  rw [get_eq_find, hvn, Option.getD_some]
  simp only [NId, famOf_some c id hs, Nat.sub_self, lenAt, baseN]
  have hmem := (BTree.ofList_sound _ _ ho1 id n).mp hn
  obtain ⟨o, ho, hoe⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at hoe
  obtain ⟨hoid, hoN⟩ := hoe
  cases h : o1.find? (fun o => o.id == id) with
  | none =>
    have := List.find?_eq_none.mp h o ho
    simp [hoid] at this
  | some o' =>
    have h1 := List.mem_of_find?_eq_some h
    have h2 : o'.id = id := by simpa using List.find?_some h
    have := BTree.ofList_unique _ _ ho1 id n o'.N hmem (List.mem_map.mpr ⟨o', h1, by rw [h2]⟩)
    simp [this]

/-- the facts that `rootOK` establishes for one root -/
structure TurtleSound.RootFacts (c : Cert) (ix : Idx) (o1 : List O1Pass) (r : O6Root) where
  p : Pass
  q : ℕ
  g : List ℕ
  hp : findPass ix r.id = some p
  hq : famParity ix p = some q
  hq2 : q < 2
  hg : grandchildren ix p.children = some g
  hmu : 1 ≤ count p.id g
  hgl : count p.id g < g.length
  hN0 : NId c o1 r.id (Rq c.B q) = r.N0
  hrec : ∀ s, s < famCount c q + 3 →
    (NId c o1 r.id (Rq c.B q + 2 * s + 2) : ℤ) = r.a * NId c o1 r.id (Rq c.B q + 2 * s) + r.b

theorem TurtleSound.rootFacts {c : Cert} {ix : Idx} (hix : c.index = some ix) (o1 : List O1Pass) (o1t : BTree ℕ)
    (ho1 : baseLengths o1 = some o1t) (r : O6Root) (h : rootOK c ix o1t r = true) :
    Nonempty (RootFacts c ix o1 r) := by
  have hB := (index_fields c ix hix).1
  unfold rootOK at h
  split at h
  · cases h
  · rename_i p hp
    simp only [Bool.and_eq_true] at h
    obtain ⟨hgrow, h⟩ := h
    unfold growthOK at hgrow
    split at hgrow
    · rename_i g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, gt_iff_lt] at hgrow
      split at h
      · cases h
      · rename_i q hq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hq2, h⟩ := h
        split at h
        · rename_i tq tq' htq htq'
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hcl1, hcl2⟩, hr⟩, h⟩ := h
          split at h
          · cases h
          · rename_i v hv
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨hN0, hit⟩ := h
            obtain ⟨chr, hchr⟩ := Option.isSome_iff_exists.mp hr
            -- the first level of the parity class
            have hfirst : Rep c o1 tq v (Rq c.B q) := by
              unfold firstLevel at hv
              rw [hB] at hv
              by_cases hqB : q = c.B % 2
              · rw [if_pos (by simpa using hqB)] at hv
                have : Rq c.B q = c.B := by simp [Rq, hqB]
                rw [this]
                exact rep_base hix o1 o1t ho1 q tq htq v hv
              · rw [if_neg (by simpa using hqB)] at hv
                obtain ⟨vB, hvB, rfl⟩ := Option.map_eq_some_iff.mp hv
                have h1q : 1 - q = c.B % 2 := by omega
                have : Rq c.B q = c.B + 1 := by
                  simp only [Rq]; rw [if_neg (by simpa using fun h => hqB h.symm)]
                rw [this]
                exact rep_step hix o1 q tq' tq htq hcl1 vB c.B (Nat.le_refl _)
                  (rep_base hix o1 o1t ho1 (1 - q) tq' htq' vB hvB)
            have hRq : c.B ≤ Rq c.B q := by unfold Rq; split_ifs <;> omega
            refine ⟨⟨p, q, g, hp, hq, hq2, hg, hgrow.1, hgrow.2, ?_, ?_⟩⟩
            · rw [← hfirst r.id chr hchr]; exact hN0
            · intro s hs
              rw [← tableOf_size hix q tq htq] at hs
              exact iterate_sound hix o1 q tq tq' htq htq' hcl1 hcl2 r hr _ v _ hRq hfirst hit s hs
        · cases h
    · cases hgrow

/-- **O4 / O6, as propositions.** For every root r of `o6` accepted by `checkO46`: r is a pass family of
parity q ∈ {0, 1}; it occurs μ ≥ 1 times in its own two-level expansion, which has more than μ members;
its length at the first level m₀ = R(q) of its class is N₀; and `N(r, m₀+2s+2) = a N(r, m₀+2s) + b` for
the `dim M + 3` steps `s < famCount c q + 3` (dim M = the number of families of parity q). -/
theorem TurtleSound.checkO46_sound (c : Cert) (o1 : List O1Pass) (o6 : List O6Root) (h : checkO46 c o1 o6 = true) :
    ∃ ix, c.index = some ix ∧ ∀ r ∈ o6, Nonempty (RootFacts c ix o1 r) := by
  unfold checkO46 at h
  split at h
  · rename_i ix o1t hix ho1
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨ix, hix, fun r hr => rootFacts hix o1 o1t ho1 r (h.2 r hr)⟩
  · cases h

end

/-! ## O4 in the model: the root's pass is arbitrarily long -/

section
open TurtleO2 TurtleO1 TurtleO46 TurtleSound
set_option linter.unnecessarySeqFocus false

theorem TurtleSound.mem_grandchildren (ix : Idx) : ∀ (chs : List Child) (g : List ℕ), grandchildren ix chs = some g →
    ∀ x ∈ g, ∃ ch ∈ chs, ∃ pa, findPass ix ch.entry = some pa ∧ ∃ gc ∈ pa.children, gc.entry = x
  | [], g, h, x, hx => by simp [grandchildren] at h; subst h; simp at hx
  | ch :: rest, g, h, x, hx => by
    simp only [grandchildren] at h
    split at h
    · rename_i pa tl hpa htl
      cases h
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨gc, hgc, rfl⟩ := List.mem_map.mp hx
        exact ⟨ch, List.mem_cons_self, pa, hpa, gc, hgc, rfl⟩
      · obtain ⟨ch', hch', pa', h1, h2⟩ := mem_grandchildren ix rest tl htl x hx
        exact ⟨ch', List.mem_cons_of_mem _ hch', pa', h1, h2⟩
    · cases h

theorem TurtleSound.sum_grandchildren {c : Cert} {ix : Idx} (hix : c.index = some ix) (o1 : List O1Pass) (m : ℕ)
    (hm : c.B ≤ m) : ∀ (chs : List Child) (g : List ℕ), grandchildren ix chs = some g →
    (chs.map (fun ch => NId c o1 ch.entry (m + 1))).sum = (g.map (fun x => NId c o1 x m)).sum
  | [], g, h => by simp [grandchildren] at h; subst h; rfl
  | ch :: rest, g, h => by
    simp only [grandchildren] at h
    split at h
    · rename_i pa tl hpa htl
      cases h
      rw [List.map_cons, List.sum_cons, List.map_append, List.sum_append,
        sum_grandchildren hix o1 m hm rest tl htl,
        NId_succ c o1 ch.entry m pa (by rw [findPassC_eq hix]; exact hpa) hm, List.map_map]
      rfl
    · cases h

theorem TurtleSound.count_le_length (a : ℕ) : ∀ g : List ℕ, count a g ≤ g.length
  | [] => Nat.le_refl _
  | x :: xs => by
    have := count_le_length a xs
    simp only [count, List.length_cons]
    split_ifs <;> omega

/-- Σ f over g ≥ μ f(a) + (|g| − μ) when f ≥ 1 on g (μ = multiplicity of a in g) -/
theorem TurtleSound.sum_ge_count (f : ℕ → ℕ) (a : ℕ) : ∀ g : List ℕ, (∀ x ∈ g, 1 ≤ f x) →
    count a g * f a + (g.length - count a g) ≤ (g.map f).sum
  | [], _ => by simp [count]
  | x :: xs, hpos => by
    have ih := sum_ge_count f a xs (fun y hy => hpos y (List.mem_cons_of_mem _ hy))
    have hx := hpos x List.mem_cons_self
    have hle := count_le_length a xs
    simp only [count, List.length_cons, List.map_cons, List.sum_cons]
    by_cases h : x = a
    · subst h
      simp only [beq_self_eq_true, if_true]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · have : (x == a) = false := by simpa using h
      simp only [this, Bool.false_eq_true, if_false, Nat.zero_add]
      omega

/-- **O4 in the model**: N(r, m+2) ≥ N(r, m) + 1 at the levels of the root's parity class, given that every
family of that parity has a positive length at level m (H(m)) -/
theorem TurtleSound.model_growth (c : Cert) (prog : List Cmd) (o1 : List O1Pass) {ix : Idx} (hix : c.index = some ix)
    (h3 : checkO3 c ix = true) (r : O6Root) (R : RootFacts c ix o1 r) (m : ℕ) (hm : c.B ≤ m) (hq : R.q = m % 2)
    (hpos : ∀ π : Fam c, portParity c π.1 = m % 2 → 0 < (turtleSystem c prog o1).N π m) :
    NId c o1 r.id m + 1 ≤ NId c o1 r.id (m + 2) := by
  have hp := R.hp
  obtain ⟨hmem, hid⟩ := (findPass_iff c ix hix r.id R.p).mp hp
  rw [show m + 2 = (m + 1) + 1 by omega, NId_succ c o1 r.id (m + 1) R.p (by rw [findPassC_eq hix]; exact hp) (by omega),
    sum_grandchildren hix o1 m hm R.p.children R.g R.hg]
  -- every grandchild is a family of the root's parity, hence of positive length
  obtain ⟨pin, _, _, h1, _, _, _, _, _, _, hch⟩ := checkO3_sound h3 R.p hmem
  have hpin : pin.parity = R.q := by
    have := R.hq; unfold famParity at this; rw [h1] at this; simpa using this
  have hposg : ∀ x ∈ R.g, 1 ≤ NId c o1 x m := by
    intro x hx
    obtain ⟨ch, hchm, pa, hpa, gc, hgc, rfl⟩ := mem_grandchildren ix R.p.children R.g R.hg x hx
    obtain ⟨a, _, _, _, e1, _, _, e4, _, _, _, _, _, ha, _⟩ := hch ch hchm
    obtain ⟨hpam, hpaid⟩ := (findPass_iff c ix hix ch.entry pa).mp hpa
    obtain ⟨pin', _, _, h1', _, _, _, _, _, _, hch'⟩ := checkO3_sound h3 pa hpam
    rw [hpaid, e1] at h1'
    cases h1'
    obtain ⟨a'', _, _, pa'', e1'', _, _, e4'', _, _, _, _, _, ha'', _⟩ := hch' gc hgc
    have hs : (findPassC c gc.entry).isSome := by rw [findPassC_eq hix, e4'']; rfl
    have hpar : portParity c gc.entry = m % 2 := by
      rw [portParity_of hix _ a'' e1'', ha'', ha, hpin, hq]
      have := Nat.mod_lt m (by omega : 0 < 2)
      omega
    have := hpos ⟨gc.entry, hs⟩ hpar
    rw [← NId_fam c prog o1 ⟨gc.entry, hs⟩ m] at this
    exact this
  have hsum := sum_ge_count (fun x => NId c o1 x m) r.id R.g hposg
  have hmu : 1 ≤ count r.id R.g := by rw [← hid]; exact R.hmu
  have hgl : count r.id R.g < R.g.length := by rw [← hid]; exact R.hgl
  have : NId c o1 r.id m ≤ count r.id R.g * NId c o1 r.id m := Nat.le_mul_of_pos_left _ hmu
  simp only at hsum
  omega

theorem TurtleSound.Rq_mod (B q : ℕ) (hq : q < 2) : Rq B q % 2 = q := by
  unfold Rq
  split_ifs with h
  · simpa using h
  · have : B % 2 ≠ q := by simpa using h
    omega

theorem TurtleSound.Rq_ge (B q : ℕ) : B ≤ Rq B q := by
  unfold Rq; split_ifs <;> omega

end

/-! ## Theorem U(1): determinism and the period -/

section
open TurtleSound

/-- the orbit of a crossing map F that agrees with the turtle step of X on crossings into rhombs owned
by X follows the trace of the segment -/
theorem TurtleSound.orbit_eq_trace {Cross : Type} [AddGroup Cross] (S : PassSystem Cross) {X : S.Tile}
    {c e : Cross} {N : ℕ} (h : S.Seg X c N e) (F : Cross → Cross)
    (hF : ∀ x, S.owned X (S.enters x) → F x = S.next X x) : ∀ k, k ≤ N → F^[k] c = S.trace X c k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply', ih (by omega), hF _ (h.inside k (by omega))]
    rfl

/-- **Theorem U(1), determinism ⇒ period.**  Let a segment of N crossings in X end with an exit.  For every
injective crossing map F (the turtle of a tiling: the step map on states is a bijection) that agrees with
the turtle step of X on crossings into rhombs owned by X, any repetition F^[i] c = F^[j] c, i < j, of the
orbit of c is more than N crossings (S-moves) apart: the orbit is infinite or its period exceeds N S-moves,
i.e. N / (S-moves per cycle) ≥ N / |P| cycles. -/
theorem TurtleSound.period_gt {Cross : Type} [AddGroup Cross] (S : PassSystem Cross) {X : S.Tile}
    {c e : Cross} {N : ℕ} (h : S.Seg X c N e) (hout : ¬ S.owned X (S.enters e)) (F : Cross → Cross)
    (hinj : Function.Injective F) (hF : ∀ x, S.owned X (S.enters x) → F x = S.next X x) :
    ∀ i j, i < j → F^[i] c = F^[j] c → N < j - i := by
  intro i j hij heq
  have h1 : F^[j] c = F^[i] (F^[j - i] c) := by
    rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
  rw [h1] at heq
  have h2 : c = F^[j - i] c := (hinj.iterate i) heq
  by_contra hN
  have hd := PassInduction.distinct S h hout 0 (j - i) (by omega) (by omega)
  apply hd
  rw [← orbit_eq_trace S h F hF 0 (by omega), ← orbit_eq_trace S h F hF (j - i) (by omega)]
  exact h2

/-- the same for states: if the states at N + 1 times are pairwise distinct, every period of a periodic
point is at least N + 1 (pigeonhole) -/
theorem TurtleSound.period_ge {σ : Type} (f : σ → σ) (s : σ) (N : ℕ) (t : ℕ → ℕ)
    (hd : ∀ k k', k < k' → k' ≤ N → f^[t k] s ≠ f^[t k'] s) (T : ℕ) (hT : 0 < T) (hper : f^[T] s = s) :
    N + 1 ≤ T := by
  have hpow : ∀ k, f^[T * k] s = s := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
  have hmod : ∀ n, f^[n] s = f^[n % T] s := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n T, Function.iterate_add_apply, hpow]
  by_contra hlt'
  have hlt : T < N + 1 := by omega
  obtain ⟨k, hk, k', hk', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := Finset.range T) (f := fun k => t k % T)
    (by simp; omega) (fun k _ => by simp [Nat.mod_lt _ hT])
  simp only [Finset.mem_range] at hk hk'
  have hs : f^[t k] s = f^[t k'] s := by rw [hmod (t k), hmod (t k'), heq]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hd k k' h (by omega) hs
  · exact hd k' k h (by omega) hs.symm

end

/-! ## the unboundedness theorem for a certificate -/

section
open TurtleO2 TurtleO1 TurtleO46 TurtleSound

/-- **Theorem U(1) for a certificate accepted by the checkers.**  Under Lemma 2 (`ExitProperty`), for
every root r of `o6` and every M there is a level m such that the root's pass in the standard level-m
supertile X (and in every isometric copy g X) is a segment of more than M crossings, ending with an exit;
every injective crossing map F that agrees with the turtle step of g X on crossings into rhombs owned by
g X has no repetition within M crossings on the orbit of the entry crossing. -/
theorem TurtleSound.unbounded (c : Cert) (prog : List Cmd) (o1 : List O1Pass) (o6 : List O6Root)
    (hc : checkCertificate c = true) (h1 : checkO1 c prog o1 = true) (h46 : checkO46 c o1 o6 = true)
    (hside : checkSide c o1 = true) (hL2 : ExitProperty c prog o1) (r : O6Root) (hr : r ∈ o6) :
    ∃ ρ : (turtleSystem c prog o1).Fam, ρ.1 = r.id ∧ ∀ M : ℕ, ∃ m, c.B ≤ m ∧
      M < (turtleSystem c prog o1).N ρ m ∧
      (turtleSystem c prog o1).Seg ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ ρ) m)
        ((turtleSystem c prog o1).portIn ρ m) ((turtleSystem c prog o1).N ρ m) ((turtleSystem c prog o1).portOut ρ m) ∧
      ¬ (turtleSystem c prog o1).owned ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ ρ) m)
        ((turtleSystem c prog o1).enters ((turtleSystem c prog o1).portOut ρ m)) ∧
      ∀ (g : (turtleSystem c prog o1).Iso) (F : Crs → Crs), Function.Injective F →
        (∀ x, (turtleSystem c prog o1).owned
            ((turtleSystem c prog o1).actT g ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ ρ) m))
            ((turtleSystem c prog o1).enters x) →
          F x = (turtleSystem c prog o1).next
            ((turtleSystem c prog o1).actT g ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ ρ) m)) x) →
        ∀ i j, i < j → F^[i] ((turtleSystem c prog o1).actC g ((turtleSystem c prog o1).portIn ρ m)) =
          F^[j] ((turtleSystem c prog o1).actC g ((turtleSystem c prog o1).portIn ρ m)) → M < j - i := by
  have hH := model_H_all c prog o1 hc h1 hside hL2
  obtain ⟨ix, hix, -, -, h3, -⟩ := checkCertificate_sound c hc
  obtain ⟨ix', hix', hroots⟩ := checkO46_sound c o1 o6 h46
  rw [hix] at hix'
  cases hix'
  obtain ⟨R⟩ := hroots r hr
  have hs : (findPassC c r.id).isSome := by rw [findPassC_eq hix, R.hp]; rfl
  let ρ : Fam c := ⟨r.id, hs⟩
  have hparρ : portParity c r.id = R.q := by
    obtain ⟨pin, _, _, h1', _⟩ := checkO3_sound h3 R.p ((findPass_iff c ix hix r.id R.p).mp R.hp).1
    have hid := ((findPass_iff c ix hix r.id R.p).mp R.hp).2
    have := R.hq
    unfold famParity at this
    rw [h1'] at this
    rw [hid] at h1'
    rw [portParity_of hix _ pin h1']
    simpa using this
  -- the lengths along the parity class grow by at least one per two levels
  have hgrow : ∀ s, NId c o1 r.id (Rq c.B R.q) + s ≤ NId c o1 r.id (Rq c.B R.q + 2 * s) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hm : c.B ≤ Rq c.B R.q + 2 * s := by have := Rq_ge c.B R.q; omega
      have hpar : R.q = (Rq c.B R.q + 2 * s) % 2 := by
        have := Rq_mod c.B R.q R.hq2; omega
      have := model_growth c prog o1 hix h3 r R _ hm hpar (fun π hπ => (hH _ hm π hπ).1)
      rw [show Rq c.B R.q + 2 * (s + 1) = Rq c.B R.q + 2 * s + 2 by omega]
      omega
  have hpos0 : 1 ≤ NId c o1 r.id (Rq c.B R.q) := by
    have := (hH _ (Rq_ge c.B R.q) ρ (by
      show portParity c r.id = _
      rw [hparρ, Rq_mod c.B R.q R.hq2])).1
    rw [← NId_fam c prog o1 ρ] at this
    exact this
  refine ⟨ρ, rfl, fun M => ⟨Rq c.B R.q + 2 * M, by have := Rq_ge c.B R.q; omega, ?_⟩⟩
  have hmB : c.B ≤ Rq c.B R.q + 2 * M := by have := Rq_ge c.B R.q; omega
  have hparm : (turtleSystem c prog o1).parity ρ = (Rq c.B R.q + 2 * M) % 2 := by
    show portParity c r.id = _
    rw [hparρ]; have := Rq_mod c.B R.q R.hq2; omega
  obtain ⟨-, hseg, hout⟩ := hH _ hmB ρ hparm
  refine ⟨?_, hseg, hout, ?_⟩
  · rw [← NId_fam c prog o1 ρ]
    have := hgrow M
    show M < NId c o1 r.id (Rq c.B R.q + 2 * M)
    omega
  · intro g F hinj hF i j hij heq
    have hseg' := PassSystem.Seg.act (turtleSystem c prog o1) g hseg
    have hout' : ¬ (turtleSystem c prog o1).owned ((turtleSystem c prog o1).actT g
        ((turtleSystem c prog o1).std ((turtleSystem c prog o1).typ ρ) (Rq c.B R.q + 2 * M)))
        ((turtleSystem c prog o1).enters ((turtleSystem c prog o1).actC g
          ((turtleSystem c prog o1).portOut ρ (Rq c.B R.q + 2 * M)))) := by
      rw [(turtleSystem c prog o1).enters_act, (turtleSystem c prog o1).owned_act]
      exact hout
    have hgap := period_gt (turtleSystem c prog o1) hseg' hout' F hinj hF i j hij heq
    have hN : M < (turtleSystem c prog o1).N ρ (Rq c.B R.q + 2 * M) := by
      rw [← NId_fam c prog o1 ρ]
      have := hgrow M
      show M < NId c o1 r.id (Rq c.B R.q + 2 * M)
      omega
    omega

end

section
open TurtleO2 TurtleO1 TurtleO46 TurtleSound

theorem TurtleSound.rootFacts_parity {c : Cert} {ix : Idx} (hix : c.index = some ix) (h3 : checkO3 c ix = true)
    {o1 : List O1Pass} {r : O6Root} (R : RootFacts c ix o1 r) : portParity c r.id = R.q := by
  obtain ⟨pin, _, _, h1', _⟩ := checkO3_sound h3 R.p ((findPass_iff c ix hix r.id R.p).mp R.hp).1
  have hid := ((findPass_iff c ix hix r.id R.p).mp R.hp).2
  have := R.hq
  unfold famParity at this
  rw [h1'] at this
  rw [hid] at h1'
  rw [portParity_of hix _ pin h1']
  simpa using this

/-- **O6, the closed recurrence of a root, in the model** (`dim M + 3` steps from the first level of its
parity class; dim M = `famCount c q`, the number of families of parity q) -/
theorem TurtleSound.root_recurrence (c : Cert) (o1 : List O1Pass) (o6 : List O6Root)
    (hc : checkCertificate c = true) (h46 : checkO46 c o1 o6 = true) (r : O6Root) (hr : r ∈ o6) :
    NId c o1 r.id (Rq c.B (portParity c r.id)) = r.N0 ∧
    ∀ s, s < famCount c (portParity c r.id) + 3 →
      (NId c o1 r.id (Rq c.B (portParity c r.id) + 2 * s + 2) : ℤ) =
        r.a * NId c o1 r.id (Rq c.B (portParity c r.id) + 2 * s) + r.b := by
  obtain ⟨ix, hix, -, -, h3, -⟩ := checkCertificate_sound c hc
  obtain ⟨ix', hix', hroots⟩ := checkO46_sound c o1 o6 h46
  rw [hix] at hix'
  cases hix'
  obtain ⟨R⟩ := hroots r hr
  rw [rootFacts_parity hix h3 R]
  exact ⟨R.hN0, R.hrec⟩

end

-- the namespaces of the checkers stay open so that the `#print axioms` lines appended by LeanAssist resolve
open TurtleO2 TurtleO1 TurtleO46

/-! ## O6 at every level of the parity class (Cayley–Hamilton) -/

section
open TurtleO2 TurtleO1 TurtleO46 TurtleSound
set_option linter.unnecessarySeqFocus false

/-- `ofList` succeeds ⇒ the keys of the list are distinct -/
theorem TurtleO2.BTree.ofList_nodup {α : Type} (xs : List (ℕ × α)) (t : BTree α) (h : BTree.ofList xs = some t) :
    (xs.map Prod.fst).Nodup := by
  unfold BTree.ofList at h
  simp only at h
  split_ifs at h with h1 h2
  have hs := BTree.pairwise_of_sortedStrict _ (by simpa using h1)
  have hnd : ((BTree.msort 64 xs).map Prod.fst).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hs.imp (fun h => Nat.ne_of_lt h)
  exact ((BTree.msort_perm 64 xs).map Prod.fst).nodup_iff.mp hnd

/-- the ids of the pass families of parity q, in the order of the pass table -/
def TurtleSound.famIds (c : Cert) (q : ℕ) : List ℕ :=
  (c.passes.filter (fun p => (findPortC c p.id).map (·.parity) == some q)).map (·.id)

/-- the grandchildren of a family (entry ids, with multiplicity): the row of the two-level expansion -/
def TurtleSound.grandIds (c : Cert) (id : ℕ) : List ℕ :=
  match findPassC c id with
  | some p => p.children.flatMap (fun ch => match findPassC c ch.entry with
      | some pa => pa.children.map (·.entry)
      | none => [])
  | none => []

theorem TurtleSound.famIds_length (c : Cert) (q : ℕ) : (famIds c q).length = famCount c q := by
  simp [famIds, famCount]

theorem TurtleSound.famIds_nodup {c : Cert} {ix : Idx} (hix : c.index = some ix) (q : ℕ) : (famIds c q).Nodup := by
  unfold Cert.index at hix
  split at hix
  · rename_i tp tq _ h2
    have h := BTree.ofList_nodup _ _ h2
    rw [List.map_map] at h
    unfold famIds
    exact (h.sublist (List.Sublist.map _ List.filter_sublist))
  · cases hix

theorem TurtleSound.mem_famIds {c : Cert} {ix : Idx} (hix : c.index = some ix) (q id : ℕ) (p : Port) (pa : Pass)
    (hpa : findPass ix id = some pa) (hp : findPort ix id = some p) (hq : p.parity = q) : id ∈ famIds c q := by
  obtain ⟨hm, rfl⟩ := (findPass_iff c ix hix id pa).mp hpa
  unfold famIds
  refine List.mem_map.mpr ⟨pa, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩
  rw [findPortC_eq hix, hp]
  simp [hq]

/-- two levels of the length recursion: N(id, m+2) = Σ_{grandchildren} N(·, m) -/
theorem TurtleSound.NId_two (c : Cert) (o1 : List O1Pass) (id m : ℕ) (hm : c.B ≤ m) :
    NId c o1 id (m + 2) = ((grandIds c id).map (fun y => NId c o1 y m)).sum := by
  unfold grandIds
  cases hp : findPassC c id with
  | none =>
    have : famOf c id = none := by simp [famOf, hp]
    simp [NId, this]
  | some p =>
    rw [show m + 2 = (m + 1) + 1 by omega, NId_succ c o1 id (m + 1) p hp (by omega)]
    simp only [List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ch _
    simp only [Function.comp]
    cases hpa : findPassC c ch.entry with
    | none =>
      have : famOf c ch.entry = none := by simp [famOf, hpa]
      simp [NId, this]
    | some pa =>
      rw [NId_succ c o1 ch.entry m pa hpa hm, List.map_map]
      rfl

/-- a sum over a list of members of a duplicate-free list `ids`, as a sum over the positions of `ids` -/
theorem TurtleSound.sum_eq_count_sum (ids : List ℕ) (hnd : ids.Nodup) (f : ℕ → ℤ) :
    ∀ L : List ℕ, (∀ y ∈ L, y ∈ ids) →
      (L.map f).sum = ∑ j : Fin ids.length, (L.count ids[j] : ℤ) * f ids[j]
  | [], _ => by simp
  | a :: L, hL => by
    rw [List.map_cons, List.sum_cons, sum_eq_count_sum ids hnd f L (fun y hy => hL y (List.mem_cons_of_mem _ hy))]
    simp only [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨j0, hj0, hja⟩ := List.getElem_of_mem (hL a List.mem_cons_self)
    rw [Finset.sum_eq_single (⟨j0, hj0⟩ : Fin ids.length)]
    · simp [hja]
    · intro j _ hj
      have : ids[j] ≠ a := by
        intro h
        apply hj
        exact Fin.ext ((hnd.getElem_inj_iff).mp (h.trans hja.symm))
      have this' : ids[(j : ℕ)] ≠ a := by simpa [Fin.getElem_fin] using this
      simp only [Fin.getElem_fin, beq_iff_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul,
        zero_mul]
      rw [if_neg (Ne.symm this')]
    · simp

/-- **O6 at every level**: the closed recurrence of a root accepted by `checkO46` holds at every level of
its parity class (`CayleyHamiltonRecurrence.affine_of_initial`: the lengths of the class obey
N(m+2) = M N(m), and the checker verified dim M + 3 ≥ dim M + 1 steps) -/
theorem TurtleSound.root_recurrence_all (c : Cert) (o1 : List O1Pass) (o6 : List O6Root)
    (hc : checkCertificate c = true) (h46 : checkO46 c o1 o6 = true) (hside : checkSide c o1 = true)
    (r : O6Root) (hr : r ∈ o6) :
    ∀ s, (NId c o1 r.id (Rq c.B (portParity c r.id) + 2 * s + 2) : ℤ) =
        r.a * NId c o1 r.id (Rq c.B (portParity c r.id) + 2 * s) + r.b := by
  obtain ⟨ix, hix, -, -, h3, -⟩ := checkCertificate_sound c hc
  obtain ⟨-, hpar2, -⟩ := checkSide_sound c o1 hside
  obtain ⟨-, hrec⟩ := root_recurrence c o1 o6 hc h46 r hr
  obtain ⟨ix', hix', hroots⟩ := checkO46_sound c o1 o6 h46
  rw [hix] at hix'
  cases hix'
  obtain ⟨R⟩ := hroots r hr
  have hq := rootFacts_parity hix h3 R
  rw [hq] at hrec ⊢
  have hnd : (famIds c R.q).Nodup := famIds_nodup hix R.q
  -- the grandchildren of a family of parity q are families of parity q
  have hclosed : ∀ i : Fin (famIds c R.q).length, ∀ y ∈ grandIds c (famIds c R.q)[i], y ∈ famIds c R.q := by
    intro i y hy
    have hi : (famIds c R.q)[i] ∈ famIds c R.q := List.getElem_mem _
    generalize (famIds c R.q)[i] = idi at hi hy
    unfold famIds at hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hpm, hpq⟩ := List.mem_filter.mp hp
    have hpid := (findPass_iff c ix hix p.id p).mpr ⟨hpm, rfl⟩
    simp only [grandIds, findPassC_eq hix, hpid, List.mem_flatMap] at hy
    obtain ⟨ch, hch, hy⟩ := hy
    obtain ⟨pin, _, _, h1, _, _, _, _, _, _, hchs⟩ := checkO3_sound h3 p hpm
    obtain ⟨a, _, _, pa, e1, _, _, e4, _, _, _, _, _, ha, _⟩ := hchs ch hch
    rw [e4] at hy
    obtain ⟨gc, hgc, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hpam, hpaid⟩ := (findPass_iff c ix hix ch.entry pa).mp e4
    obtain ⟨pin', _, _, h1', _, _, _, _, _, _, hchs'⟩ := checkO3_sound h3 pa hpam
    rw [hpaid, e1] at h1'
    cases h1'
    obtain ⟨a'', _, _, pa'', e1'', _, _, e4'', _, _, _, _, _, ha'', _⟩ := hchs' gc hgc
    have hpinq : pin.parity = R.q := by
      rw [findPortC_eq hix, h1] at hpq; simpa using hpq
    have h2 : pin.parity < 2 := hpar2 pin ((findPort_iff c ix hix p.id pin).mp h1).1
    exact mem_famIds hix R.q gc.entry a'' pa'' e4'' e1'' (by omega)
  -- the orbit x (s+1) = M x(s) of the lengths of the class
  have hm0 : c.B ≤ Rq c.B R.q := Rq_ge c.B R.q
  let M : Matrix (Fin (famIds c R.q).length) (Fin (famIds c R.q).length) ℤ :=
    fun i j => ((grandIds c (famIds c R.q)[i]).count (famIds c R.q)[j] : ℤ)
  let x : ℕ → Fin (famIds c R.q).length → ℤ := fun s i => (NId c o1 (famIds c R.q)[i] (Rq c.B R.q + 2 * s) : ℤ)
  have hx : ∀ s, x (s + 1) = M.mulVec (x s) := by
    intro s
    funext i
    have := sum_eq_count_sum (famIds c R.q) hnd (fun y => (NId c o1 y (Rq c.B R.q + 2 * s) : ℤ))
      (grandIds c (famIds c R.q)[i]) (hclosed i)
    simp only [x, M, Matrix.mulVec, dotProduct]
    rw [show Rq c.B R.q + 2 * (s + 1) = (Rq c.B R.q + 2 * s) + 2 by omega, NId_two c o1 _ _ (by omega),
      Nat.cast_list_sum, List.map_map]
    exact this
  -- the root is a family of the class
  obtain ⟨pin, _, _, h1, _⟩ := checkO3_sound h3 R.p ((findPass_iff c ix hix r.id R.p).mp R.hp).1
  have hpid := ((findPass_iff c ix hix r.id R.p).mp R.hp).2
  rw [hpid] at h1
  have hpin : pin.parity = R.q := by rw [← portParity_of hix _ pin h1, hq]
  have hrmem : r.id ∈ famIds c R.q := mem_famIds hix R.q r.id pin R.p R.hp h1 hpin
  obtain ⟨i0, hi0, hri⟩ := List.getElem_of_mem hrmem
  have hall := CayleyHamiltonRecurrence.affine_of_initial M x hx ⟨i0, hi0⟩ r.a r.b (by
    intro s hs
    simp only [x, Fin.getElem_fin, hri]
    rw [show Rq c.B R.q + 2 * (s + 1) = Rq c.B R.q + 2 * s + 2 by omega]
    exact hrec s (by rw [← famIds_length]; omega))
  intro s
  have := hall s
  simp only [x, Fin.getElem_fin, hri, show Rq c.B R.q + 2 * (s + 1) = Rq c.B R.q + 2 * s + 2 by omega] at this
  exact this

end
