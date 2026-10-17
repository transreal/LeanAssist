import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs

/-!
# PassInduction -- the induction H(m) of the unboundedness proof on an abstract pass system

`proof_unbounded.md`, "Proof of H(m) for all m ≥ B".  The geometry of the Penrose substitution
is abstracted into a structure `PassSystem`:

* pass families `Fam` with a parity, a type `typ`, children `(slot, child family)`, and ports
  `portIn π m`, `portOut π m` (crossings) at every level `m`; lengths `N π m`;
* placed supertiles `Tile`, the standard supertile `std τ m`, the child isometries
  `G τ j m` acting on crossings, tiles and rhombs (`actC`, `actT`, `actR`), the type `slotTyp τ j`
  of the child in slot `j`;
* rhombs `Rh`, the rhomb `enters c` that a crossing leads into, ownership `owned X r`, the
  sub-tile relation `sub Y X`, and the turtle step `next X c`: the next crossing of the turtle
  after the crossing `c`, computed in the tile `X` (meaningful when `c` leads into a rhomb owned
  by `X`: the geometry of that rhomb is determined by `X`);
* the facts of the geometry taken as fields: `enters`, `owned`, `next` are equivariant under the
  isometries; `next` is local (in a sub-tile that owns the rhomb entered, the step is the step of
  the sub-tile); ownership of a sub-tile refines ownership (`owned_sub`); the placed children are
  sub-tiles (`child_sub`); the ports obey `port (m+2) = Φ (port m) + δ` from the lowest level of
  their parity class, and `G_{j,m+2} (Φ x + d) = Φ (G_{j,m} x) + ρ_j d` (`G_rec`).

`Cross` is an additive group so that Lemma 1 (`AffineRecurrence.lean`, copied here as
`PassInduction.affine_unique` / `parity_class_unique` because loose files cannot import each
other) lifts the port identities (a), (b), (c) from the two lowest levels of each parity class
(obligation O2, `O2At`) to all levels.

`PassInduction.H_all` derives `H m` for every `m ≥ B` from
O1 (`H B`), O2 at two levels, O3 (closure: children non-empty, of the opposite parity and of the
type of their slot), the recursion of the lengths, and Lemma 2 (the exit property, taken as a
hypothesis in the form the paper proves it: given `H m`, the exit crossing of the last child,
placed in the parent of level `m + 1`, leads to a rhomb not owned by the parent).
`PassInduction.distinct` is the determinism argument of Theorem U(1): the crossings of a segment
are pairwise distinct.  `PassInduction.N_two_level` is the two-level recursion
`N(π, m+2) = Σ_{grandchildren} N(·, m)` behind the matrix `M` of O6.

`PassInduction.toy` is a two-family model that satisfies every field and every hypothesis of
`H_all` (`PassInduction.toy_H`), so the hypotheses are jointly consistent: the theorem is not vacuous.

Checked with Mathlib (`LeanCheckFile`); axioms `propext` and `Quot.sound` only.
Theorems carry qualified names (no `namespace` block) so that the `#print axioms` lines LeanAssist
appends at the end of the file resolve them.
-/

/-- An abstract pass-substitution system: the data and the geometric facts used by the
induction H(m). -/
structure PassSystem (Cross : Type) [AddGroup Cross] where
  /-- pass families (identified with their entry port family) -/
  Fam : Type
  /-- supertile types -/
  Typ : Type
  /-- child slots -/
  Slot : Type
  /-- placed supertiles -/
  Tile : Type
  /-- rhombs -/
  Rh : Type
  /-- orientation-preserving isometries -/
  Iso : Type
  /-- base level -/
  B : ℕ
  parity : Fam → ℕ
  typ : Fam → Typ
  /-- the children (slot, child family) of a pass family, in order -/
  children : Fam → List (Slot × Fam)
  portIn : Fam → ℕ → Cross
  portOut : Fam → ℕ → Cross
  /-- the lengths N(π, m) -/
  N : Fam → ℕ → ℕ
  /-- the standard supertile of a type at a level -/
  std : Typ → ℕ → Tile
  /-- the type of the child in a slot -/
  slotTyp : Typ → Slot → Typ
  /-- G_{j,m}: child frame (level m − 1) → parent frame (level m) -/
  G : Typ → Slot → ℕ → Iso
  /-- the rhomb a crossing leads into -/
  enters : Cross → Rh
  owned : Tile → Rh → Prop
  /-- the next crossing after `c`, computed in the tile -/
  next : Tile → Cross → Cross
  sub : Tile → Tile → Prop
  actC : Iso → Cross → Cross
  actT : Iso → Tile → Tile
  actR : Iso → Rh → Rh
  /-- the map x ↦ φ² x of the port recurrence -/
  Φ : Cross → Cross
  dIn : Fam → Cross
  dOut : Fam → Cross
  /-- ρ^{k_j}: the rotation part of G_{j,m} applied to a port delta -/
  rot : Typ → Slot → Cross → Cross
  enters_act : ∀ g c, enters (actC g c) = actR g (enters c)
  owned_act : ∀ g X r, owned (actT g X) (actR g r) ↔ owned X r
  next_act : ∀ g X c, owned X (enters c) → next (actT g X) (actC g c) = actC g (next X c)
  next_sub : ∀ X Y c, sub Y X → owned Y (enters c) → next X c = next Y c
  owned_sub : ∀ X Y r, sub Y X → owned Y r → owned X r
  child_sub : ∀ τ j m, sub (actT (G τ j (m + 1)) (std (slotTyp τ j) m)) (std τ (m + 1))
  portIn_rec : ∀ π m, (if B % 2 = parity π then B else B + 1) ≤ m →
    portIn π (m + 2) = Φ (portIn π m) + dIn π
  portOut_rec : ∀ π m, (if B % 2 = parity π then B else B + 1) ≤ m →
    portOut π (m + 2) = Φ (portOut π m) + dOut π
  G_rec : ∀ τ j m x d, actC (G τ j (m + 2)) (Φ x + d) = Φ (actC (G τ j m) x) + rot τ j d

/-! ## Lemma 1 (copy of `AffineRecurrence.lean`) -/

theorem PassInduction.affine_unique {V : Type} [AddGroup V] (M : V → V) (d d' : V) (u v : ℕ → V)
    (hu : ∀ n, u (n + 1) = M (u n) + d) (hv : ∀ n, v (n + 1) = M (v n) + d')
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : d = d' ∧ ∀ n, u n = v n := by
  have hd : d = d' := by
    have h := h1
    rw [hu 0, hv 0, h0] at h
    exact add_left_cancel h
  refine ⟨hd, ?_⟩
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hu k, hv k, ih, hd]

theorem PassInduction.parity_class_unique {V : Type} [AddGroup V] (M : V → V) (d d' : V)
    (u v : ℕ → V) (m₀ : ℕ)
    (hu : ∀ m, m₀ ≤ m → u (m + 2) = M (u m) + d)
    (hv : ∀ m, m₀ ≤ m → v (m + 2) = M (v m) + d')
    (h0 : u m₀ = v m₀) (h1 : u (m₀ + 2) = v (m₀ + 2)) :
    ∀ m, m₀ ≤ m → m % 2 = m₀ % 2 → u m = v m := by
  have key := PassInduction.affine_unique M d d'
    (fun s => u (m₀ + 2 * s)) (fun s => v (m₀ + 2 * s))
    (fun s => by
      show u (m₀ + 2 * (s + 1)) = M (u (m₀ + 2 * s)) + d
      rw [show m₀ + 2 * (s + 1) = (m₀ + 2 * s) + 2 by omega]
      exact hu _ (by omega))
    (fun s => by
      show v (m₀ + 2 * (s + 1)) = M (v (m₀ + 2 * s)) + d'
      rw [show m₀ + 2 * (s + 1) = (m₀ + 2 * s) + 2 by omega]
      exact hv _ (by omega))
    (by simpa using h0)
    (by simpa using h1)
  intro m hm hpar
  rw [show m = m₀ + 2 * ((m - m₀) / 2) by omega]
  exact key.2 _

/-! ## definitions -/

namespace PassSystem

variable {Cross : Type} [AddGroup Cross] (S : PassSystem Cross)

/-- the lowest child level `n ≥ B` of an inductive step for a parent of parity `q`
(`n + 1 ≡ q`; `n₀` of Lemma 2) -/
def n0 (q : ℕ) : ℕ := if S.B % 2 = q then S.B + 1 else S.B

/-- the crossings of the turtle from `c` in the tile `X`: `c`, `next X c`, `next X (next X c)`, … -/
def trace (X : S.Tile) (c : Cross) : ℕ → Cross
  | 0 => c
  | k + 1 => S.next X (trace X c k)

/-- a segment of the turtle's run in `X`: the crossings number `0, …, N − 1` from `c` lead into
rhombs owned by `X` (the first is the entry crossing, the others the first `N − 1` S-moves) and
the `N`-th crossing is `e` -/
structure Seg (X : S.Tile) (c : Cross) (N : ℕ) (e : Cross) : Prop where
  inside : ∀ k, k < N → S.owned X (S.enters (S.trace X c k))
  exit : S.trace X c N = e

/-- H(m): for every family of parity `m mod 2`, in the standard supertile of its type the entry
port leads into an owned rhomb, the turtle performs exactly `N(π, m)` S-moves, the first
`N − 1` inside, the `N`-th being the exit port, which leads outside -/
def H (m : ℕ) : Prop := ∀ π, S.parity π = m % 2 →
  0 < S.N π m ∧ S.Seg (S.std (S.typ π) m) (S.portIn π m) (S.N π m) (S.portOut π m) ∧
    ¬ S.owned (S.std (S.typ π) m) (S.enters (S.portOut π m))

/-- the entry port of a child pass at child level `n`, placed in the parent frame (level `n + 1`) -/
def placedIn (τ : S.Typ) (n : ℕ) (ch : S.Slot × S.Fam) : Cross :=
  S.actC (S.G τ ch.1 (n + 1)) (S.portIn ch.2 n)

/-- the exit port of a child pass, placed in the parent frame -/
def placedOut (τ : S.Typ) (n : ℕ) (ch : S.Slot × S.Fam) : Cross :=
  S.actC (S.G τ ch.1 (n + 1)) (S.portOut ch.2 n)

/-- Σ of the lengths of a list of children at level `n` -/
def childSum (n : ℕ) : List (S.Slot × S.Fam) → ℕ
  | [] => 0
  | ch :: rest => S.N ch.2 n + childSum n rest

/-- identities (b): the placed exit of each child is the placed entry of the next -/
def linked (τ : S.Typ) (n : ℕ) : List (S.Slot × S.Fam) → Prop
  | [] => True
  | [_] => True
  | ch :: ch' :: rest => S.placedOut τ n ch = S.placedIn τ n ch' ∧ linked τ n (ch' :: rest)

/-- the placed exit of the last child of `ch0 :: L` -/
def lastOut (τ : S.Typ) (n : ℕ) (ch0 : S.Slot × S.Fam) : List (S.Slot × S.Fam) → Cross
  | [] => S.placedOut τ n ch0
  | ch :: rest => lastOut τ n ch rest

/-- the port identities (a), (b), (c) of a family at child level `n` (parent level `n + 1`) -/
def O2At (π : S.Fam) (n : ℕ) : Prop :=
  match S.children π with
  | [] => True
  | ch0 :: L =>
    S.portIn π (n + 1) = S.placedIn (S.typ π) n ch0 ∧ S.linked (S.typ π) n (ch0 :: L) ∧
      S.portOut π (n + 1) = S.lastOut (S.typ π) n ch0 L

/-- a sequence obeying `u (n+2) = Φ (u n) + d` from index `n₀` on -/
def Aff (u : ℕ → Cross) (n0 : ℕ) : Prop := ∃ d, ∀ n, n0 ≤ n → u (n + 2) = S.Φ (u n) + d

end PassSystem

/-! ## segments: concatenation, sub-tiles, isometries -/

section

variable {Cross : Type} [AddGroup Cross] (S : PassSystem Cross)

theorem PassSystem.trace_add (X : S.Tile) (c : Cross) (N k : ℕ) :
    S.trace X c (N + k) = S.trace X (S.trace X c N) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show S.next X (S.trace X c (N + k)) = S.next X (S.trace X (S.trace X c N) k)
    rw [ih]

theorem PassSystem.Seg.concat {X : S.Tile} {c e e' : Cross} {N N' : ℕ}
    (h1 : S.Seg X c N e) (h2 : S.Seg X e N' e') : S.Seg X c (N + N') e' where
  inside := by
    intro k hk
    by_cases hkN : k < N
    · exact h1.inside k hkN
    · rw [show k = N + (k - N) by omega, S.trace_add, h1.exit]
      exact h2.inside (k - N) (by omega)
  exit := by rw [S.trace_add, h1.exit, h2.exit]

/-- locality: while the turtle enters rhombs owned by a sub-tile, its crossings in the tile are
those computed in the sub-tile -/
theorem PassSystem.trace_sub {X Y : S.Tile} (hsub : S.sub Y X) {c : Cross} {n : ℕ}
    (hin : ∀ k, k < n → S.owned Y (S.enters (S.trace Y c k))) :
    ∀ k, k ≤ n → S.trace X c k = S.trace Y c k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    show S.next X (S.trace X c k) = S.next Y (S.trace Y c k)
    rw [ih (by omega)]
    exact S.next_sub X Y _ hsub (hin k (by omega))

/-- a segment of a sub-tile is a segment of the tile -/
theorem PassSystem.Seg.lift {X Y : S.Tile} (hsub : S.sub Y X) {c e : Cross} {N : ℕ}
    (h : S.Seg Y c N e) : S.Seg X c N e where
  inside := by
    intro k hk
    rw [S.trace_sub hsub h.inside k (by omega)]
    exact S.owned_sub X Y _ hsub (h.inside k hk)
  exit := by rw [S.trace_sub hsub h.inside N (Nat.le_refl N)]; exact h.exit

/-- equivariance: the crossings in an isometric copy are the images of the crossings -/
theorem PassSystem.trace_act (g : S.Iso) {X : S.Tile} {c : Cross} {n : ℕ}
    (hin : ∀ k, k < n → S.owned X (S.enters (S.trace X c k))) :
    ∀ k, k ≤ n → S.trace (S.actT g X) (S.actC g c) k = S.actC g (S.trace X c k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    show S.next (S.actT g X) (S.trace (S.actT g X) (S.actC g c) k) =
      S.actC g (S.next X (S.trace X c k))
    rw [ih (by omega)]
    exact S.next_act g X _ (hin k (by omega))

theorem PassSystem.Seg.act (g : S.Iso) {X : S.Tile} {c e : Cross} {N : ℕ} (h : S.Seg X c N e) :
    S.Seg (S.actT g X) (S.actC g c) N (S.actC g e) where
  inside := by
    intro k hk
    rw [S.trace_act g h.inside k (by omega), S.enters_act, S.owned_act]
    exact h.inside k hk
  exit := by rw [S.trace_act g h.inside N (Nat.le_refl N), h.exit]

/-- Theorem U(1), determinism: the crossings of a segment that ends with an exit are pairwise
distinct (a repeated crossing would keep the turtle inside forever) -/
theorem PassInduction.distinct {X : S.Tile} {c e : Cross} {N : ℕ} (h : S.Seg X c N e)
    (hout : ¬ S.owned X (S.enters e)) :
    ∀ k k', k < k' → k' ≤ N → S.trace X c k ≠ S.trace X c k' := by
  intro k k' hkk' hk'N heq
  have hshift : ∀ t, S.trace X c (k + t) = S.trace X c (k' + t) := by
    intro t
    induction t with
    | zero => simpa using heq
    | succ t ih =>
      show S.next X (S.trace X c (k + t)) = S.next X (S.trace X c (k' + t))
      rw [ih]
  have h1 := hshift (N - k')
  rw [show k' + (N - k') = N by omega, h.exit] at h1
  have h2 := h.inside (k + (N - k')) (by omega)
  rw [h1] at h2
  exact hout h2

/-! ## one inductive step: the children's segments, placed and concatenated -/

/-- one child pass placed in the parent: H(n) for the child family gives a segment of the parent
tile of level `n + 1` from the placed entry to the placed exit -/
theorem PassSystem.child_seg {n : ℕ} (hH : S.H n) (τ : S.Typ) (ch : S.Slot × S.Fam)
    (hpar : S.parity ch.2 = n % 2) (htyp : S.typ ch.2 = S.slotTyp τ ch.1) :
    0 < S.N ch.2 n ∧
      S.Seg (S.std τ (n + 1)) (S.placedIn τ n ch) (S.N ch.2 n) (S.placedOut τ n ch) := by
  obtain ⟨hpos, hseg, -⟩ := hH ch.2 hpar
  refine ⟨hpos, ?_⟩
  have h1 := PassSystem.Seg.act S (S.G τ ch.1 (n + 1)) hseg
  rw [htyp] at h1
  exact PassSystem.Seg.lift S (S.child_sub τ ch.1 n) h1

/-- the chain of child passes `ch0 :: L`, linked by (b): a segment of the parent tile from the
placed entry of the first child to the placed exit of the last, of length Σ N(child, n) -/
theorem PassSystem.chain {n : ℕ} (hH : S.H n) (τ : S.Typ) (L : List (S.Slot × S.Fam)) :
    ∀ ch0 : S.Slot × S.Fam,
      (∀ ch ∈ ch0 :: L, S.parity ch.2 = n % 2 ∧ S.typ ch.2 = S.slotTyp τ ch.1) →
      S.linked τ n (ch0 :: L) →
      0 < S.childSum n (ch0 :: L) ∧
        S.Seg (S.std τ (n + 1)) (S.placedIn τ n ch0) (S.childSum n (ch0 :: L))
          (S.lastOut τ n ch0 L) := by
  induction L with
  | nil =>
    intro ch0 hch _
    obtain ⟨h1, h2⟩ := hch ch0 (by simp)
    obtain ⟨hpos, hseg⟩ := S.child_seg hH τ ch0 h1 h2
    refine ⟨?_, ?_⟩
    · show 0 < S.N ch0.2 n + 0
      omega
    · show S.Seg (S.std τ (n + 1)) (S.placedIn τ n ch0) (S.N ch0.2 n + 0) (S.placedOut τ n ch0)
      rw [Nat.add_zero]
      exact hseg
  | cons ch1 rest ih =>
    intro ch0 hch hlk
    obtain ⟨h1, h2⟩ := hch ch0 (by simp)
    obtain ⟨hpos, hseg⟩ := S.child_seg hH τ ch0 h1 h2
    simp only [PassSystem.linked] at hlk
    obtain ⟨hlink, hlk'⟩ := hlk
    obtain ⟨hpos', hseg'⟩ := ih ch1 (fun ch hm => hch ch (List.mem_cons_of_mem ch0 hm)) hlk'
    refine ⟨?_, ?_⟩
    · show 0 < S.N ch0.2 n + S.childSum n (ch1 :: rest)
      omega
    · show S.Seg (S.std τ (n + 1)) (S.placedIn τ n ch0) (S.N ch0.2 n + S.childSum n (ch1 :: rest))
        (S.lastOut τ n ch1 rest)
      rw [hlink] at hseg
      exact PassSystem.Seg.concat S hseg hseg'

/-- the inductive step m → m + 1 with the identities (a), (b), (c) at child level m -/
theorem PassSystem.step (m : ℕ) (hH : S.H m)
    (hO2 : ∀ π, S.parity π = (m + 1) % 2 → S.O2At π m)
    (hO3 : ∀ π, S.children π ≠ [] ∧
      ∀ ch ∈ S.children π, S.parity ch.2 = 1 - S.parity π ∧ S.typ ch.2 = S.slotTyp (S.typ π) ch.1)
    (hN : ∀ π, S.N π (m + 1) = S.childSum m (S.children π))
    (hL2 : ∀ π, S.parity π = (m + 1) % 2 → ∀ ch0 L, S.children π = ch0 :: L →
      ¬ S.owned (S.std (S.typ π) (m + 1)) (S.enters (S.lastOut (S.typ π) m ch0 L))) :
    S.H (m + 1) := by
  intro π hπ
  obtain ⟨hne, hch⟩ := hO3 π
  obtain ⟨ch0, L, hcl⟩ : ∃ ch0 L, S.children π = ch0 :: L := by
    cases h : S.children π with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, l, rfl⟩
  have ho2 := hO2 π hπ
  simp only [PassSystem.O2At, hcl] at ho2
  obtain ⟨ha, hb, hc⟩ := ho2
  have hch' : ∀ ch ∈ ch0 :: L, S.parity ch.2 = m % 2 ∧ S.typ ch.2 = S.slotTyp (S.typ π) ch.1 := by
    intro ch hm'
    rw [← hcl] at hm'
    obtain ⟨hp, ht⟩ := hch ch hm'
    exact ⟨by omega, ht⟩
  obtain ⟨hpos, hseg⟩ := S.chain hH (S.typ π) L ch0 hch' hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hN π, hcl]; exact hpos
  · rw [hN π, hcl, ha, hc]; exact hseg
  · rw [hc]; exact hL2 π hπ ch0 L hcl

/-! ## O2 at two levels ⇒ O2 at all levels (Lemma 1) -/

theorem PassSystem.Aff.unique {u v : ℕ → Cross} {n0 : ℕ} (hu : S.Aff u n0) (hv : S.Aff v n0)
    (h0 : u n0 = v n0) (h1 : u (n0 + 2) = v (n0 + 2)) :
    ∀ n, n0 ≤ n → n % 2 = n0 % 2 → u n = v n := by
  obtain ⟨d, hd⟩ := hu
  obtain ⟨d', hd'⟩ := hv
  exact PassInduction.parity_class_unique S.Φ d d' u v n0 hd hd' h0 h1

theorem PassSystem.aff_portIn (π : S.Fam) :
    S.Aff (fun n => S.portIn π (n + 1)) (S.n0 (S.parity π)) :=
  ⟨S.dIn π, fun n hn => by
    show S.portIn π (n + 2 + 1) = S.Φ (S.portIn π (n + 1)) + S.dIn π
    rw [show n + 2 + 1 = n + 1 + 2 by omega]
    exact S.portIn_rec π (n + 1) (by unfold PassSystem.n0 at hn; split_ifs at hn ⊢ <;> omega)⟩

theorem PassSystem.aff_portOut (π : S.Fam) :
    S.Aff (fun n => S.portOut π (n + 1)) (S.n0 (S.parity π)) :=
  ⟨S.dOut π, fun n hn => by
    show S.portOut π (n + 2 + 1) = S.Φ (S.portOut π (n + 1)) + S.dOut π
    rw [show n + 2 + 1 = n + 1 + 2 by omega]
    exact S.portOut_rec π (n + 1) (by unfold PassSystem.n0 at hn; split_ifs at hn ⊢ <;> omega)⟩

theorem PassSystem.aff_placedIn (τ : S.Typ) (ch : S.Slot × S.Fam) (q : ℕ) (hq : q ≤ 1)
    (hp : S.parity ch.2 = 1 - q) : S.Aff (fun n => S.placedIn τ n ch) (S.n0 q) :=
  ⟨S.rot τ ch.1 (S.dIn ch.2), fun n hn => by
    show S.actC (S.G τ ch.1 (n + 2 + 1)) (S.portIn ch.2 (n + 2)) =
      S.Φ (S.actC (S.G τ ch.1 (n + 1)) (S.portIn ch.2 n)) + S.rot τ ch.1 (S.dIn ch.2)
    rw [S.portIn_rec ch.2 n (by rw [hp]; unfold PassSystem.n0 at hn; split_ifs at hn ⊢ <;> omega),
      show n + 2 + 1 = n + 1 + 2 by omega]
    exact S.G_rec τ ch.1 (n + 1) _ _⟩

theorem PassSystem.aff_placedOut (τ : S.Typ) (ch : S.Slot × S.Fam) (q : ℕ) (hq : q ≤ 1)
    (hp : S.parity ch.2 = 1 - q) : S.Aff (fun n => S.placedOut τ n ch) (S.n0 q) :=
  ⟨S.rot τ ch.1 (S.dOut ch.2), fun n hn => by
    show S.actC (S.G τ ch.1 (n + 2 + 1)) (S.portOut ch.2 (n + 2)) =
      S.Φ (S.actC (S.G τ ch.1 (n + 1)) (S.portOut ch.2 n)) + S.rot τ ch.1 (S.dOut ch.2)
    rw [S.portOut_rec ch.2 n (by rw [hp]; unfold PassSystem.n0 at hn; split_ifs at hn ⊢ <;> omega),
      show n + 2 + 1 = n + 1 + 2 by omega]
    exact S.G_rec τ ch.1 (n + 1) _ _⟩

theorem PassSystem.aff_lastOut (τ : S.Typ) (q : ℕ) (hq : q ≤ 1) (L : List (S.Slot × S.Fam)) :
    ∀ ch0, (∀ ch ∈ ch0 :: L, S.parity ch.2 = 1 - q) →
      S.Aff (fun n => S.lastOut τ n ch0 L) (S.n0 q) := by
  induction L with
  | nil =>
    intro ch0 h
    exact S.aff_placedOut τ ch0 q hq (h ch0 (by simp))
  | cons ch rest ih =>
    intro ch0 h
    exact ih ch (fun c hc => h c (List.mem_cons_of_mem ch0 hc))

theorem PassSystem.linked_lift (τ : S.Typ) (q : ℕ) (hq : q ≤ 1) (L : List (S.Slot × S.Fam))
    (hL : ∀ ch ∈ L, S.parity ch.2 = 1 - q)
    (h0 : S.linked τ (S.n0 q) L) (h1 : S.linked τ (S.n0 q + 2) L) :
    ∀ n, S.n0 q ≤ n → n % 2 = S.n0 q % 2 → S.linked τ n L := by
  induction L with
  | nil => intro n _ _; trivial
  | cons ch rest ih =>
    cases rest with
    | nil => intro n _ _; trivial
    | cons ch' rest' =>
      intro n hn hpar
      simp only [PassSystem.linked] at h0 h1 ⊢
      obtain ⟨e0, l0⟩ := h0
      obtain ⟨e1, l1⟩ := h1
      refine ⟨?_, ih (fun c hc => hL c (List.mem_cons_of_mem ch hc)) l0 l1 n hn hpar⟩
      exact PassSystem.Aff.unique S (S.aff_placedOut τ ch q hq (hL ch (by simp)))
        (S.aff_placedIn τ ch' q hq (hL ch' (by simp))) e0 e1 n hn hpar

/-- O2 at the two lowest child levels of the parity class lifts to every child level of the
class (Lemma 1 applied to (a), (b), (c)) -/
theorem PassSystem.O2At_lift (π : S.Fam) (hq : S.parity π ≤ 1)
    (hO3 : ∀ ch ∈ S.children π, S.parity ch.2 = 1 - S.parity π)
    (h0 : S.O2At π (S.n0 (S.parity π))) (h1 : S.O2At π (S.n0 (S.parity π) + 2)) :
    ∀ n, S.n0 (S.parity π) ≤ n → n % 2 = S.n0 (S.parity π) % 2 → S.O2At π n := by
  intro n hn hpar
  rcases hcl : S.children π with _ | ⟨ch0, L⟩
  · simp [PassSystem.O2At, hcl]
  · simp only [PassSystem.O2At, hcl] at h0 h1 ⊢
    obtain ⟨a0, b0, c0⟩ := h0
    obtain ⟨a1, b1, c1⟩ := h1
    have hL : ∀ ch ∈ ch0 :: L, S.parity ch.2 = 1 - S.parity π := by
      intro ch hc; rw [← hcl] at hc; exact hO3 ch hc
    refine ⟨?_, ?_, ?_⟩
    · exact PassSystem.Aff.unique S (S.aff_portIn π)
        (S.aff_placedIn (S.typ π) ch0 (S.parity π) hq (hL ch0 (by simp))) a0 a1 n hn hpar
    · exact S.linked_lift (S.typ π) (S.parity π) hq (ch0 :: L) hL b0 b1 n hn hpar
    · exact PassSystem.Aff.unique S (S.aff_portOut π)
        (S.aff_lastOut (S.typ π) (S.parity π) hq L ch0 hL) c0 c1 n hn hpar

/-! ## the induction -/

/-- H(m) for every m ≥ B from O1, O2 (two levels per parity class), O3, the recursion of the
lengths, and Lemma 2 (exit property, as a hypothesis). -/
theorem PassInduction.H_all
    (hO1 : S.H S.B)
    (hO2 : ∀ π, S.O2At π (S.n0 (S.parity π)) ∧ S.O2At π (S.n0 (S.parity π) + 2))
    (hO3 : ∀ π, S.children π ≠ [] ∧
      ∀ ch ∈ S.children π, S.parity ch.2 = 1 - S.parity π ∧ S.typ ch.2 = S.slotTyp (S.typ π) ch.1)
    (hN : ∀ π m, S.B ≤ m → S.N π (m + 1) = S.childSum m (S.children π))
    (hL2 : ∀ m, S.B ≤ m → S.H m → ∀ π, S.parity π = (m + 1) % 2 → ∀ ch0 L,
      S.children π = ch0 :: L →
      ¬ S.owned (S.std (S.typ π) (m + 1)) (S.enters (S.lastOut (S.typ π) m ch0 L))) :
    ∀ m, S.B ≤ m → S.H m := by
  have key : ∀ k, S.H (S.B + k) := by
    intro k
    induction k with
    | zero => rw [Nat.add_zero]; exact hO1
    | succ k ih =>
      have hm : S.B ≤ S.B + k := Nat.le_add_right _ _
      rw [show S.B + (k + 1) = (S.B + k) + 1 by omega]
      apply S.step (S.B + k) ih
      · intro π hπ
        have hq : S.parity π ≤ 1 := by omega
        exact S.O2At_lift π hq (fun ch hc => ((hO3 π).2 ch hc).1) (hO2 π).1 (hO2 π).2 (S.B + k)
          (by unfold PassSystem.n0; split_ifs <;> omega) (by unfold PassSystem.n0; split_ifs <;> omega)
      · exact hO3
      · exact fun π => hN π (S.B + k) hm
      · exact hL2 (S.B + k) hm ih
  intro m hm
  have h := key (m - S.B)
  rwa [show S.B + (m - S.B) = m by omega] at h

/-- the two-level recursion behind the matrix `M` of O6:
`N(π, m+2) = Σ_{children ch} Σ_{children of ch} N(·, m)` -/
theorem PassInduction.N_two_level
    (hN : ∀ π m, S.B ≤ m → S.N π (m + 1) = S.childSum m (S.children π))
    (π : S.Fam) (m : ℕ) (hm : S.B ≤ m) :
    S.N π (m + 2) = ((S.children π).map (fun ch => S.childSum m (S.children ch.2))).sum := by
  have h := hN π (m + 1) (by omega)
  rw [show m + 1 + 1 = m + 2 by omega] at h
  rw [h]
  generalize S.children π = L
  induction L with
  | nil => rfl
  | cons ch rest ih =>
    simp only [PassSystem.childSum, List.map_cons, List.sum_cons]
    rw [hN ch.2 m hm, ih]

end

/-! ## non-vacuity: a toy pass system that satisfies every hypothesis of `H_all` -/

/-- Two pass families `false`, `true` of parities 0 and 1, each the single child of the other;
every pass has length 1: its entry crossing leads into the rhomb 0 (owned by every tile) and its
exit crossing into the rhomb 1 (owned by none). -/
def PassInduction.toy : PassSystem ℤ where
  Fam := Bool
  Typ := Unit
  Slot := Unit
  Tile := ℕ
  Rh := ℤ
  Iso := Unit
  B := 0
  parity b := if b then 1 else 0
  typ _ := ()
  children b := [((), !b)]
  portIn _ _ := 0
  portOut _ _ := 1
  N _ _ := 1
  std _ m := m
  slotTyp _ _ := ()
  G _ _ _ := ()
  enters c := c
  owned _ r := r = 0
  next _ c := c + 1
  sub _ _ := True
  actC _ c := c
  actT _ X := X
  actR _ r := r
  Φ x := x
  dIn _ := 0
  dOut _ := 0
  rot _ _ d := d
  enters_act _ _ := rfl
  owned_act _ _ _ := Iff.rfl
  next_act _ _ _ _ := rfl
  next_sub _ _ _ _ _ := rfl
  owned_sub _ _ _ _ h := h
  child_sub _ _ _ := trivial
  portIn_rec _ _ _ := by simp
  portOut_rec _ _ _ := by simp
  G_rec _ _ _ _ _ := rfl

/-- `H_all` applies to the toy system: its hypotheses (O1, O2, O3, the length recursion and
Lemma 2) are jointly satisfiable. -/
theorem PassInduction.toy_H : ∀ m, 0 ≤ m → PassInduction.toy.H m := by
  apply PassInduction.H_all PassInduction.toy
  · intro π _
    refine ⟨Nat.one_pos, ⟨fun k hk => ?_, rfl⟩, (by decide : ¬ ((1 : ℤ) = 0))⟩
    have hk' : k < 1 := hk
    obtain rfl : k = 0 := by omega
    exact (rfl : (0 : ℤ) = 0)
  · intro π
    exact ⟨(⟨rfl, trivial, rfl⟩ : (0 : ℤ) = 0 ∧ True ∧ (1 : ℤ) = 1),
      (⟨rfl, trivial, rfl⟩ : (0 : ℤ) = 0 ∧ True ∧ (1 : ℤ) = 1)⟩
  · intro π
    refine ⟨List.cons_ne_nil _ _, fun ch hc => ?_⟩
    have hc' : ch = ((), !π) := List.mem_singleton.mp hc
    subst hc'
    cases π <;> exact ⟨rfl, rfl⟩
  · intro _ _ _
    rfl
  · intro m _ _ π _ ch0 L hcl
    cases L with
    | nil => exact (by decide : ¬ ((1 : ℤ) = 0))
    | cons x xs =>
      have h' : [((), !π)] = ch0 :: x :: xs := hcl
      exact absurd (List.cons.inj h').2 (List.cons_ne_nil x xs).symm

