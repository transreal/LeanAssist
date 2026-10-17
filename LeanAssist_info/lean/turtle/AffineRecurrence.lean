import Mathlib.Algebra.Group.Basic

/-!
# AffineRecurrence -- Lemma 1 of the unboundedness proof (proof_unbounded.md)

Two sequences in an additive group that obey affine recurrences with the *same* map `M` but
possibly different constants, `u (n+1) = M (u n) + d` and `v (n+1) = M (v n) + d'`, and agree at
two consecutive indices, have the same constant and agree everywhere.

In the turtle proof `V = Z[ζ]` (as an additive group), `M = multiplication by φ²`, and the
sequences are the two sides of a port identity, indexed by the levels of one parity class.
`M` is an arbitrary map `V → V`: no linearity is needed.

Checked with Mathlib (LeanAssist: `LeanCheckFile`), no `sorry`; `affine_unique` depends on no
axiom, the parity-class versions on `propext` / `Quot.sound` only (through `omega` / `simp`).
The theorems carry qualified names instead of a `namespace` block so that the `#print axioms`
lines LeanAssist appends at the end of the file resolve them.
-/

variable {V : Type*} [AddGroup V]

/-- Lemma 1 (abstract form): affine recurrences with the same map that agree at `0` and `1`
have the same constant and agree at every index. -/
theorem AffineRecurrence.affine_unique (M : V → V) (d d' : V) (u v : ℕ → V)
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

/-- Lemma 1 as used in O2: sequences indexed by the levels `m ≡ m₀ (mod 2)`, `m ≥ m₀`,
with `u (m+2) = M (u m) + d`.  Agreement at `m₀` and `m₀ + 2` gives agreement at
`m₀ + 2 s` for every `s`. -/
theorem AffineRecurrence.parity_class_unique (M : V → V) (d d' : V) (u v : ℕ → V) (m₀ : ℕ)
    (hu : ∀ m, m₀ ≤ m → u (m + 2) = M (u m) + d)
    (hv : ∀ m, m₀ ≤ m → v (m + 2) = M (v m) + d')
    (h0 : u m₀ = v m₀) (h1 : u (m₀ + 2) = v (m₀ + 2)) :
    d = d' ∧ ∀ s, u (m₀ + 2 * s) = v (m₀ + 2 * s) := by
  have key := AffineRecurrence.affine_unique M d d'
    (fun s => u (m₀ + 2 * s)) (fun s => v (m₀ + 2 * s))
    (fun s => by
      show u (m₀ + 2 * (s + 1)) = M (u (m₀ + 2 * s)) + d
      have : m₀ + 2 * (s + 1) = (m₀ + 2 * s) + 2 := by omega
      rw [this]
      exact hu _ (by omega))
    (fun s => by
      show v (m₀ + 2 * (s + 1)) = M (v (m₀ + 2 * s)) + d'
      have : m₀ + 2 * (s + 1) = (m₀ + 2 * s) + 2 := by omega
      rw [this]
      exact hv _ (by omega))
    (by simpa using h0)
    (by simpa using h1)
  exact key

/-- The same statement with the level written as `m ≥ m₀`, `m ≡ m₀ (mod 2)`. -/
theorem AffineRecurrence.parity_class_unique' (M : V → V) (d d' : V) (u v : ℕ → V) (m₀ : ℕ)
    (hu : ∀ m, m₀ ≤ m → u (m + 2) = M (u m) + d)
    (hv : ∀ m, m₀ ≤ m → v (m + 2) = M (v m) + d')
    (h0 : u m₀ = v m₀) (h1 : u (m₀ + 2) = v (m₀ + 2)) :
    d = d' ∧ ∀ m, m₀ ≤ m → m % 2 = m₀ % 2 → u m = v m := by
  obtain ⟨hd, h⟩ := AffineRecurrence.parity_class_unique M d d' u v m₀ hu hv h0 h1
  refine ⟨hd, ?_⟩
  intro m hm hpar
  have : m = m₀ + 2 * ((m - m₀) / 2) := by omega
  rw [this]
  exact h _
