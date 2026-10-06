import Mathlib

/-!
# Two tools for the valuation of a Hankel determinant

These are the two elementary ingredients of the programme described in `ZETA7_STATUS.md`
for bounding `v₂(Δ_K(ζ₂(7)))` from below.

* `Hankel2.norm_det_le_max_perm` — the ultrametric Leibniz bound: over `ℚ_[p]`,
  `‖det M‖ ≤ max_σ ∏_i ‖M i (σ i)‖`, i.e. `v_p(det M) ≥ min_σ ∑_i v_p(M i (σ i))`.  This is
  what turns entrywise valuation estimates into a determinant estimate.

* `Hankel2.det_moment_basis_change` — the Bhargava-basis mechanism: replacing the monomials
  `x^i` by any other polynomial basis `p_i = ∑_j T_{ji} x^j` changes the moment matrix into
  `Tᵀ M T`, so the determinant is multiplied by `(det T)²`; for a unimodular integral `T`
  the determinant is unchanged, while the entries `L(p_i p_k)` can have a much larger
  valuation than the raw moments `μ_{i+k}`.
-/

namespace Hankel2

open Finset Matrix

/-- **Ultrametric Leibniz bound.**  The `p`-adic size of a determinant is at most the largest
size of a Leibniz term. -/
theorem norm_det_le_max_perm {p : ℕ} [Fact p.Prime] {K : ℕ} (M : Matrix (Fin K) (Fin K) ℚ_[p])
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ σ : Equiv.Perm (Fin K), ∏ i, ‖M (σ i) i‖ ≤ C) :
    ‖M.det‖ ≤ C := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun σ _ => ?_
  have hnorm : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ∏ i, ‖M (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
      simp [hs, Units.smul_def, norm_prod]
  rw [hnorm]
  exact h σ

/-- **Change of polynomial basis in a moment determinant.**  If `p_i = ∑_j T_{ji} x^j`, the
matrix of the moments `L(p_i p_k)` is `Tᵀ M T`, so its determinant is `(det T)²·det M`. -/
theorem det_moment_basis_change {R : Type*} [CommRing R] (K : ℕ) (μ : ℕ → R)
    (T : Matrix (Fin K) (Fin K) R) :
    (Matrix.of fun i k : Fin K => ∑ a : Fin K, ∑ b : Fin K,
        T a i * T b k * μ ((a : ℕ) + (b : ℕ))).det
      = T.det ^ 2 * (Matrix.of fun i j : Fin K => μ ((i : ℕ) + (j : ℕ))).det := by
  have hmat : (Matrix.of fun i k : Fin K => ∑ a : Fin K, ∑ b : Fin K,
      T a i * T b k * μ ((a : ℕ) + (b : ℕ)))
      = Tᵀ * (Matrix.of fun i j : Fin K => μ ((i : ℕ) + (j : ℕ))) * T := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

end Hankel2
