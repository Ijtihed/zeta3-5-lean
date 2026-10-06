import RequestProject.Zeta7.Hankel2.Valuation

/-!
# The Bhargava lower bound for the valuation of a Hankel determinant

This is the algebraic half of **Theorem A** of `ZETA7_STATUS.md`
(`v₂ Δ_K(ζ₂(7)) ≥ 2 ∑_{i<K} v₂(i!) + K·(8n + 6 v₂(n!) + 1 − O(log n))`).

For any `ℚ_[p]`-linear functional `L` on polynomials, write `C_i = x(x-1)⋯(x-i+1)/i!` for
the binomial polynomials.  If every entry `L(C_i C_k)`, `i, k < K`, has `p`-adic size at
most `c`, then the Hankel determinant of the moments `μ_e = L(x^e)` satisfies

  `‖det[μ_{i+j}]‖ ≤ c^K · ∏_{i<K} ‖i!‖²`,

i.e. `v_p(det) ≥ K·v + 2∑_{i<K} v_p(i!)`.  The factor `∏‖i!‖²` is the Vandermonde (Bhargava
factorial) gain; it is what makes the 2-adic decay of the ζ₂(7) Hankel determinant of size
`15 n²` rather than `14 n²`.

The analytic half — the uniform entry bound for the Volkenborn functional of the
construction, via Mahler expansions — is proved on paper in `ZETA7_STATUS.md` and checked
numerically in `hankel2/binom_bound.py`; it is not formalized.
-/

namespace Hankel2

open Finset Matrix Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The binomial polynomial `C_i(x) = x(x-1)⋯(x-i+1)/i!` over `ℚ_[p]`. -/
noncomputable def binomPoly (p : ℕ) [Fact p.Prime] (i : ℕ) : Polynomial ℚ_[p] :=
  Polynomial.C ((i.factorial : ℚ_[p])⁻¹) * descPochhammer ℚ_[p] i

lemma binomPoly_natDegree (i : ℕ) : (binomPoly p i).natDegree = i := by
  unfold binomPoly
  rw [Polynomial.natDegree_C_mul, descPochhammer_natDegree]
  exact inv_ne_zero (by exact_mod_cast (Nat.factorial_pos i).ne')

lemma binomPoly_coeff_self (i : ℕ) :
    (binomPoly p i).coeff i = ((i.factorial : ℚ_[p]))⁻¹ := by
  unfold binomPoly
  rw [Polynomial.coeff_C_mul]
  have h := (monic_descPochhammer ℚ_[p] i)
  have hc : (descPochhammer ℚ_[p] i).coeff i = 1 := by
    have := h.coeff_natDegree
    rwa [descPochhammer_natDegree] at this
  rw [hc, mul_one]

lemma binomPoly_coeff_eq_zero {i a : ℕ} (h : i < a) : (binomPoly p i).coeff a = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [binomPoly_natDegree]; exact h

/-- The (upper triangular) matrix of coefficients of `C_0, …, C_{K-1}`. -/
noncomputable def binomMat (p : ℕ) [Fact p.Prime] (K : ℕ) : Matrix (Fin K) (Fin K) ℚ_[p] :=
  Matrix.of fun a i => (binomPoly p i).coeff a

lemma binomMat_det (K : ℕ) :
    (binomMat p K).det = ∏ i : Fin K, ((i : ℕ).factorial : ℚ_[p])⁻¹ := by
  rw [Matrix.det_of_upperTriangular]
  · simp [binomMat, binomPoly_coeff_self]
  · intro i j hij
    simp only [binomMat, Matrix.of_apply]
    exact binomPoly_coeff_eq_zero hij

lemma binomPoly_eq_sum (K : ℕ) (i : Fin K) :
    binomPoly p i = ∑ a : Fin K, Polynomial.C ((binomMat p K) a i) * X ^ (a : ℕ) := by
  conv_lhs => rw [(binomPoly p i).as_sum_range' K (by
    rw [binomPoly_natDegree]; exact i.isLt)]
  rw [← Fin.sum_univ_eq_sum_range (fun a => Polynomial.monomial a ((binomPoly p i).coeff a)) K]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [binomMat, Polynomial.C_mul_X_pow_eq_monomial]

lemma L_binom_mul (K : ℕ) (L : Polynomial ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p]) (i k : Fin K) :
    L (binomPoly p i * binomPoly p k) =
      ∑ a : Fin K, ∑ b : Fin K, (binomMat p K) a i * (binomMat p K) b k *
        L (X ^ ((a : ℕ) + (b : ℕ))) := by
  rw [binomPoly_eq_sum K i, binomPoly_eq_sum K k, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : Polynomial.C ((binomMat p K) a i) * X ^ (a : ℕ) *
      (Polynomial.C ((binomMat p K) b k) * X ^ (b : ℕ)) =
      ((binomMat p K) a i * (binomMat p K) b k) • X ^ ((a : ℕ) + (b : ℕ)) := by
    rw [Polynomial.smul_eq_C_mul, pow_add, Polynomial.C_mul]; ring
  rw [this, map_smul, smul_eq_mul]

/-- **Bhargava lower bound (algebraic half of Theorem A).**  If all entries `L(C_i C_k)`
(`i, k < K`) of the binomial-basis moment matrix have `p`-adic norm at most `c`, then the
Hankel determinant of the moments `L(x^e)` has norm at most `c^K ∏_{i<K} ‖i!‖²`. -/
theorem norm_hankel_det_le_of_binom (K : ℕ) (L : Polynomial ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (c : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ i k : ℕ, i < K → k < K → ‖L (binomPoly p i * binomPoly p k)‖ ≤ c) :
    ‖(Matrix.of fun i j : Fin K => L (X ^ ((i : ℕ) + (j : ℕ)))).det‖ ≤
      c ^ K * ∏ i : Fin K, ‖((i : ℕ).factorial : ℚ_[p])‖ ^ 2 := by
  set H := (Matrix.of fun i j : Fin K => L (X ^ ((i : ℕ) + (j : ℕ))))
  set G := (Matrix.of fun i k : Fin K => ∑ a : Fin K, ∑ b : Fin K,
        (binomMat p K) a i * (binomMat p K) b k * L (X ^ ((a : ℕ) + (b : ℕ))))
  have hG : G.det = (binomMat p K).det ^ 2 * H.det :=
    det_moment_basis_change K (fun e => L (X ^ e)) (binomMat p K)
  have hGnorm : ‖G.det‖ ≤ c ^ K := by
    refine norm_det_le_max_perm G (c ^ K) (pow_nonneg hc K) fun σ => ?_
    calc ∏ i, ‖G (σ i) i‖ ≤ ∏ _i : Fin K, c := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
          simp only [G, Matrix.of_apply]
          rw [← L_binom_mul]
          exact hentry _ _ (σ i).isLt i.isLt
      _ = c ^ K := by simp
  have hdetT : (binomMat p K).det ≠ 0 := by
    rw [binomMat_det]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      inv_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hH : H.det = G.det * (∏ i : Fin K, ((i : ℕ).factorial : ℚ_[p])) ^ 2 := by
    rw [hG, binomMat_det, Finset.prod_inv_distrib]
    have : (∏ i : Fin K, ((i : ℕ).factorial : ℚ_[p])) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
  rw [hH, norm_mul, norm_pow, norm_prod, ← Finset.prod_pow]
  exact mul_le_mul_of_nonneg_right hGnorm
    (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)

end Hankel2
