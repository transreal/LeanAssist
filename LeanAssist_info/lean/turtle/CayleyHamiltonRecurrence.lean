import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# CayleyHamiltonRecurrence -- the logical part of obligation O6 (proof_unbounded.md)

O6 of the unboundedness proof: the vector `N(m)` of the lengths of the pass families of one
parity class obeys `N(m+2) = M N(m)` with a fixed integer matrix `M` (the two-level expansion of
the pass table, computed and checked by `TurtleO46_template.lean`).  For one family `i` the
sequence `y_s = N_i(m₀+2s+2) − a N_i(m₀+2s) − b` then satisfies a linear recurrence of order
`≤ dim M + 1`, so if it vanishes for `dim M + 1` consecutive `s` it vanishes identically and the
closed recurrence `N_i(m+2) = a N_i(m) + b` holds at every level of the parity class.

* `zero_of_initial`: a sequence in which `d` consecutive zeros force the next value to be zero,
  and which starts with `d` zeros, is identically zero (induction);
* `charpoly_recurrence`: for `x (s+1) = M *ᵥ x s`, every linear functional `w ⬝ᵥ x s` of the
  orbit satisfies the recurrence given by the coefficients of the characteristic polynomial of
  `M` (Cayley–Hamilton, `Matrix.aeval_self_charpoly`);
* `monic_recurrence_zero`: the same for a monic linear recurrence of order `d` with `d` zeros
  (the form of the statement in the paper);
* `affine_of_initial`: the statement used in the proof, with `n + 1` consecutive steps as the
  hypothesis; `affine_of_initial'` with the `dim M + 2` steps of the paper (`verify_cert.py` and
  the Lean checker verify `dim M + 3`, which implies both).

Same conventions as `AffineRecurrence.lean` (Lemma 1): checked with Mathlib through
`LeanCheckFile`, qualified theorem names so that the appended `#print axioms` lines resolve.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (through Mathlib's finite sums and matrices).
-/

open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

/-- A sequence in which any `d` consecutive zeros force the next value to vanish, and whose first
`d` values vanish, is identically zero. -/
theorem CayleyHamiltonRecurrence.zero_of_initial (d : ℕ) (y : ℕ → R)
    (hrec : ∀ s, (∀ k, k < d → y (s + k) = 0) → y (s + d) = 0)
    (h0 : ∀ s, s < d → y s = 0) : ∀ s, y s = 0 := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    by_cases hs : s < d
    · exact h0 s hs
    · have hsd : s = (s - d) + d := by omega
      rw [hsd]
      exact hrec (s - d) (fun k hk => ih (s - d + k) (by omega))

/-- The form stated in the paper: a sequence that obeys a monic linear recurrence of order `d`,
`Σ_{k<d} c k · y (s+k) + y (s+d) = 0`, and starts with `d` zeros vanishes identically. -/
theorem CayleyHamiltonRecurrence.monic_recurrence_zero (d : ℕ) (c : ℕ → R) (y : ℕ → R)
    (hrec : ∀ s, ∑ k ∈ range d, c k * y (s + k) + y (s + d) = 0)
    (h0 : ∀ s, s < d → y s = 0) : ∀ s, y s = 0 :=
  CayleyHamiltonRecurrence.zero_of_initial d y (fun s hz => by
    have h := hrec s
    rw [Finset.sum_eq_zero (fun k hk => by rw [hz k (Finset.mem_range.mp hk), mul_zero]),
      zero_add] at h
    exact h) h0

/-- The orbit `x (s+1) = M *ᵥ x s` is `x s = M ^ s *ᵥ x 0`; more generally
`x (s + k) = M ^ k *ᵥ x s`. -/
theorem CayleyHamiltonRecurrence.orbit_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (x : ℕ → Fin n → R) (hx : ∀ s, x (s + 1) = M *ᵥ x s) (s k : ℕ) :
    x (s + k) = M ^ k *ᵥ x s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show s + (k + 1) = (s + k) + 1 by omega, hx, ih, mulVec_mulVec, ← pow_succ']

/-- Cayley–Hamilton for the orbit: every linear functional `w ⬝ᵥ x s` of an orbit
`x (s+1) = M *ᵥ x s` satisfies the linear recurrence whose coefficients are those of the
characteristic polynomial of `M` (order `n = dim M`, leading coefficient 1). -/
theorem CayleyHamiltonRecurrence.charpoly_recurrence {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (x : ℕ → Fin n → R) (hx : ∀ s, x (s + 1) = M *ᵥ x s) (w : Fin n → R) (s : ℕ) :
    ∑ k ∈ range (n + 1), M.charpoly.coeff k * (w ⬝ᵥ x (s + k)) = 0 := by
  have hCH : ∑ k ∈ range (n + 1), M.charpoly.coeff k • M ^ k = 0 := by
    nontriviality R
    have h := M.aeval_self_charpoly
    rw [aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin] at h
    exact h
  have hsum : (∑ k ∈ range (n + 1), M.charpoly.coeff k • M ^ k) *ᵥ x s
      = ∑ k ∈ range (n + 1), M.charpoly.coeff k • (M ^ k *ᵥ x s) := by
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl (fun k _ => smul_mulVec _ _ _)
  calc ∑ k ∈ range (n + 1), M.charpoly.coeff k * (w ⬝ᵥ x (s + k))
      = w ⬝ᵥ ∑ k ∈ range (n + 1), M.charpoly.coeff k • (M ^ k *ᵥ x s) := by
        rw [dotProduct_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [CayleyHamiltonRecurrence.orbit_pow M x hx s k, dotProduct_smul, smul_eq_mul]
    _ = w ⬝ᵥ ((∑ k ∈ range (n + 1), M.charpoly.coeff k • M ^ k) *ᵥ x s) := by rw [hsum]
    _ = 0 := by rw [hCH, zero_mulVec, dotProduct_zero]

/-- The leading coefficient of the characteristic polynomial of an `n × n` matrix is 1. -/
theorem CayleyHamiltonRecurrence.charpoly_coeff_dim {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpoly.coeff n = 1 := by
  nontriviality R
  have h := M.charpoly_monic.leadingCoeff
  rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at h

/-- O6: if `x (s+1) = M *ᵥ x s` (`M` an `n × n` matrix) and the component `i` satisfies the
closed affine recurrence `x (s+1) i = a * x s i + b` for `s = 0, …, n`, then it satisfies it for
every `s`.  (`y s = x (s+1) i − a x s i − b` obeys a linear recurrence of order `n + 1` by
Cayley–Hamilton; `n + 1` consecutive zeros therefore propagate.) -/
theorem CayleyHamiltonRecurrence.affine_of_initial {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (x : ℕ → Fin n → R) (hx : ∀ s, x (s + 1) = M *ᵥ x s) (i : Fin n) (a b : R)
    (h0 : ∀ s, s < n + 1 → x (s + 1) i = a * x s i + b) :
    ∀ s, x (s + 1) i = a * x s i + b := by
  -- z s = x (s+1) i − a x s i is the linear functional w ⬝ᵥ x s, w = row i of M − a·1
  have hz : ∀ s, (M i - a • Pi.single i 1) ⬝ᵥ x s = x (s + 1) i - a * x s i := by
    intro s
    rw [sub_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul, hx s]
    rfl
  have hrec : ∀ s, (∀ k, k < n + 1 → x (s + k + 1) i - a * x (s + k) i - b = 0) →
      x (s + (n + 1) + 1) i - a * x (s + (n + 1)) i - b = 0 := by
    intro s hk
    have hzb : ∀ k, k ≤ n → (M i - a • Pi.single i 1) ⬝ᵥ x (s + k) = b := by
      intro k hk'
      have h := hk k (by omega)
      rw [hz]
      linear_combination h
    have e1 := CayleyHamiltonRecurrence.charpoly_recurrence M x hx (M i - a • Pi.single i 1) s
    have e2 := CayleyHamiltonRecurrence.charpoly_recurrence M x hx (M i - a • Pi.single i 1) (s + 1)
    rw [Finset.sum_range_succ, CayleyHamiltonRecurrence.charpoly_coeff_dim, one_mul] at e1 e2
    have hs1 : ∑ k ∈ range n, M.charpoly.coeff k * ((M i - a • Pi.single i 1) ⬝ᵥ x (s + k))
        = ∑ k ∈ range n, M.charpoly.coeff k * b :=
      Finset.sum_congr rfl (fun k hk => by rw [hzb k (Finset.mem_range.mp hk).le])
    have hs2 : ∑ k ∈ range n, M.charpoly.coeff k * ((M i - a • Pi.single i 1) ⬝ᵥ x (s + 1 + k))
        = ∑ k ∈ range n, M.charpoly.coeff k * b :=
      Finset.sum_congr rfl (fun k hk => by
        rw [show s + 1 + k = s + (k + 1) by omega, hzb (k + 1) (Finset.mem_range.mp hk)])
    rw [hs1, hzb n le_rfl] at e1
    rw [hs2] at e2
    have hlast : (M i - a • Pi.single i 1) ⬝ᵥ x (s + 1 + n) = b := by linear_combination e2 - e1
    rw [hz, show s + 1 + n = s + (n + 1) by omega] at hlast
    linear_combination hlast
  have hzero := CayleyHamiltonRecurrence.zero_of_initial (n + 1)
    (fun s => x (s + 1) i - a * x s i - b) hrec
    (fun s hs => by
      show x (s + 1) i - a * x s i - b = 0
      linear_combination h0 s hs)
  intro s
  have h := hzero s
  simp only at h
  linear_combination h

/-- O6 with the hypothesis of the paper (`dim M + 2` consecutive steps; the checkers verify
`dim M + 3`). -/
theorem CayleyHamiltonRecurrence.affine_of_initial' {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (x : ℕ → Fin n → R) (hx : ∀ s, x (s + 1) = M *ᵥ x s) (i : Fin n) (a b : R)
    (h0 : ∀ s, s < n + 2 → x (s + 1) i = a * x s i + b) :
    ∀ s, x (s + 1) i = a * x s i + b :=
  CayleyHamiltonRecurrence.affine_of_initial M x hx i a b (fun s hs => h0 s (by omega))
