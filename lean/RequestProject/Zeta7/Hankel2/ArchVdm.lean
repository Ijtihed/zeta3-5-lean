import RequestProject.Zeta7.Hankel2.ArchL1

/-!
# Archimedean size of generalized confluent Vandermonde minors (for paper Lemma 6.2)

For real points `x : Fin K → ℝ` and Taylor orders `b : Fin K → ℕ`,
`E_b = [C(i, b_c) x_c^{i − b_c}]_{i, c}` is the coefficient of `∏ y_c^{b_c}` in the Vandermonde
`∏_{c<c'} (x_{c'} + y_{c'} − x_c − y_c)`.  Bounding this coefficient by the `ℓ¹` norm and using
submultiplicativity gives

  `|det E_b| ≤ ∏_{c<c'} (|x_{c'} − x_c| + 2)`          (`abs_det_confluent_le`).

This replaces the Cauchy estimate of paper Lemma 6.2 (2): the error `ln(|d|+2) − ln|d| ≤ 2/|d|`
is summable to `O(log n)` per node exactly like `ln(|d| + 1/5) − ln|d|`.
-/

open MvPolynomial Finset Matrix

namespace Hankel2.ArchB

theorem prod_monomial_eq' {R σ ι : Type*} [CommRing R] (s : Finset ι) (f : ι → σ →₀ ℕ)
    (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, prod_insert hj, sum_insert hj, ih, monomial_mul]

/-- The coefficient of `∏_c y_c^{b_c}` in `∏_c (x_c + y_c)^{m_c}`. -/
theorem coeff_prod_linear_pow' {R : Type*} [CommRing R] {K : ℕ} (x : Fin K → R) (m b : Fin K → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm b)
        (∏ c, (MvPolynomial.C (x c) + MvPolynomial.X c) ^ m c) =
      ∏ c, (((m c).choose (b c) : ℕ) * x c ^ (m c - b c) : R) := by
  classical
  have hexp : ∀ c, (MvPolynomial.C (x c) + MvPolynomial.X c) ^ m c =
      ∑ j ∈ range (m c + 1), monomial (Finsupp.single c j)
        (x c ^ (m c - j) * ((m c).choose j : R)) := by
    intro c
    rw [add_comm, add_pow]
    refine sum_congr rfl fun j _ => ?_
    rw [← map_pow, X_pow_eq_monomial,
      ← map_natCast (MvPolynomial.C (σ := Fin K) (R := R))]
    calc monomial (Finsupp.single c j) 1 *
          MvPolynomial.C (x c ^ (m c - j)) * MvPolynomial.C (((m c).choose j : ℕ) : R)
        = MvPolynomial.C (x c ^ (m c - j) * ((m c).choose j : R)) *
            monomial (Finsupp.single c j) 1 := by simp only [map_mul]; ring
      _ = _ := by rw [C_mul_monomial, mul_one]
  simp_rw [hexp]
  rw [prod_univ_sum]
  simp_rw [prod_monomial_eq']
  rw [coeff_sum]
  have key : ∀ β : Fin K → ℕ, (∑ c, Finsupp.single c (β c) = Finsupp.equivFunOnFinite.symm b) ↔
      β = b := by
    intro β
    constructor
    · intro h; funext c
      have := congrArg (fun f : Fin K →₀ ℕ => f c) h
      simpa [Finsupp.finset_sum_apply, Finsupp.single_apply] using this
    · rintro rfl; ext c
      simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [coeff_monomial, key]
  rw [sum_ite_eq']
  split_ifs with hb
  · refine prod_congr rfl fun c _ => ?_
    ring
  · symm
    simp only [Fintype.mem_piFinset, mem_range, not_forall, not_lt] at hb
    obtain ⟨c, hc⟩ := hb
    refine prod_eq_zero (mem_univ c) ?_
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **Archimedean confluent Vandermonde bound.** -/
theorem abs_det_confluent_le {K : ℕ} (x : Fin K → ℝ) (b : Fin K → ℕ) :
    |(Matrix.of fun (i c : Fin K) => (((i : ℕ).choose (b c) : ℕ) : ℝ) *
        x c ^ ((i : ℕ) - b c)).det| ≤ ∏ c, ∏ c' ∈ Ioi c, (|x c' - x c| + 2) := by
  classical
  set v : Fin K → MvPolynomial (Fin K) ℝ :=
    fun c => MvPolynomial.C (x c) + MvPolynomial.X c with hv
  set Eb : Matrix (Fin K) (Fin K) ℝ := Matrix.of fun (i c : Fin K) =>
    (((i : ℕ).choose (b c) : ℕ) : ℝ) * x c ^ ((i : ℕ) - b c) with hEb
  have hcoeff : coeff (Finsupp.equivFunOnFinite.symm b) (vandermonde v).det = Eb.det := by
    rw [← det_transpose, det_apply, det_apply Eb, coeff_sum]
    refine sum_congr rfl fun σ _ => ?_
    simp only [transpose_apply, vandermonde_apply]
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← map_intCast
      (MvPolynomial.C (σ := Fin K) (R := ℝ)), coeff_C_mul]
    simp only [hv]
    rw [coeff_prod_linear_pow']
    simp only [hEb, Matrix.of_apply]
  have hbound : mvl1 (vandermonde v).det ≤ ∏ c, ∏ c' ∈ Ioi c, (|x c' - x c| + 2) := by
    rw [det_vandermonde]
    refine (mvl1_prod_le _ _).trans (prod_le_prod (fun c _ => mvl1_nonneg _) fun c _ => ?_)
    refine (mvl1_prod_le _ _).trans (prod_le_prod (fun c _ => mvl1_nonneg _) fun c' _ => ?_)
    have e : v c' - v c = MvPolynomial.C (x c' - x c) + (MvPolynomial.X c' - MvPolynomial.X c) := by
      simp only [hv, map_sub]; ring
    rw [e]
    refine (mvl1_add_le _ _).trans ?_
    rw [mvl1_C]
    have := mvl1_sub_le (MvPolynomial.X c' : MvPolynomial (Fin K) ℝ) (MvPolynomial.X c)
    rw [mvl1_X, mvl1_X] at this
    linarith
  rw [← hcoeff]
  exact (abs_coeff_le_mvl1 _ _).trans hbound

end Hankel2.ArchB
