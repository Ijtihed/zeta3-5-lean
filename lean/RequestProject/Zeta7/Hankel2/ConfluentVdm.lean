import Mathlib

/-!
# `p`-adic size of generalized confluent Vandermonde minors (for paper Theorem 7.1)

For points `x : Fin K → ℚ_[p]`, Taylor orders `b : Fin K → ℕ` and weights `w : Fin K → ℕ`, let
`E_b = [C(i, b_c) x_c^{i − b_c}]_{i, c}`.  If `e c c'` (for `c < c'`) satisfies
`‖x_{c'} − x_c‖ ≤ p^{−e}` and `e ≤ w_c, w_{c'}`, then

  `‖det E_b‖ · p^{−∑_c b_c w_c} ≤ p^{−∑_{c<c'} e c c'}`       (`norm_det_confluent_le`).

This is the "unit assignment" step of paper Theorem 7.1 in weighted-Gauss-norm form: `det E_b` is
the coefficient of `∏ y_c^{b_c}` in the Vandermonde `∏_{c<c'} (x_{c'} + y_{c'} − x_c − y_c)`.
After the substitution `y_c = p^{w_c} z_c` every factor is `p^{e c c'}` times a polynomial with
`ℤ_p`-integral coefficients.
-/

open MvPolynomial Finset Matrix

namespace Hankel2

variable {p : ℕ} [Fact p.Prime]

/-- `F` has all coefficients in `ℤ_p`. -/
def IntMv {σ : Type*} (F : MvPolynomial σ ℚ_[p]) : Prop := ∀ α, ‖F.coeff α‖ ≤ 1

namespace IntMv

variable {σ : Type*}

theorem add {F G : MvPolynomial σ ℚ_[p]} (hF : IntMv F) (hG : IntMv G) : IntMv (F + G) :=
  fun α => by
    rw [coeff_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF α) (hG α))

theorem neg {F : MvPolynomial σ ℚ_[p]} (hF : IntMv F) : IntMv (-F) :=
  fun α => by rw [coeff_neg, norm_neg]; exact hF α

theorem sub {F G : MvPolynomial σ ℚ_[p]} (hF : IntMv F) (hG : IntMv G) : IntMv (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem C {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) : IntMv (MvPolynomial.C a : MvPolynomial σ ℚ_[p]) :=
  fun α => by
    classical
    rw [coeff_C]; split_ifs
    · exact ha
    · simp

theorem X (i : σ) : IntMv (MvPolynomial.X i : MvPolynomial σ ℚ_[p]) :=
  fun α => by
    classical
    rw [coeff_X']; split_ifs <;> simp

theorem mul {F G : MvPolynomial σ ℚ_[p]} (hF : IntMv F) (hG : IntMv G) : IntMv (F * G) :=
  fun α => by
    classical
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hF _) (norm_nonneg _) (hG _)

theorem prod {ι : Type*} (s : Finset ι) {F : ι → MvPolynomial σ ℚ_[p]}
    (hF : ∀ i ∈ s, IntMv (F i)) : IntMv (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntMv.C (σ := σ) (a := (1 : ℚ_[p])) (by simp)
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (hF a (mem_insert_self _ _)).mul (ih fun i hi => hF i (mem_insert_of_mem hi))

end IntMv

theorem norm_p_pow (e : ℕ) : ‖((p : ℚ_[p]) ^ e)‖ = ((p : ℝ)⁻¹) ^ e := by
  rw [norm_pow, Padic.norm_p]

theorem prod_monomial_eq {σ ι : Type*} (s : Finset ι) (f : ι → σ →₀ ℕ) (a : ι → ℚ_[p]) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, prod_insert hj, sum_insert hj, ih, monomial_mul]

/-- The coefficient of `∏_c y_c^{b_c}` in `∏_c (x_c + q_c y_c)^{m_c}`. -/
theorem coeff_prod_linear_pow {K : ℕ} (x q : Fin K → ℚ_[p]) (m b : Fin K → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm b)
        (∏ c, (MvPolynomial.C (x c) + MvPolynomial.C (q c) * MvPolynomial.X c) ^ m c) =
      ∏ c, (((m c).choose (b c) : ℕ) * x c ^ (m c - b c) * q c ^ (b c) : ℚ_[p]) := by
  classical
  have hexp : ∀ c, (MvPolynomial.C (x c) + MvPolynomial.C (q c) * MvPolynomial.X c) ^ m c =
      ∑ j ∈ range (m c + 1), monomial (Finsupp.single c j)
        (q c ^ j * x c ^ (m c - j) * ((m c).choose j : ℚ_[p])) := by
    intro c
    rw [add_comm, add_pow]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← map_pow, ← map_pow, X_pow_eq_monomial,
      ← map_natCast (MvPolynomial.C (σ := Fin K) (R := ℚ_[p]))]
    calc MvPolynomial.C (q c ^ j) * monomial (Finsupp.single c j) 1 *
          MvPolynomial.C (x c ^ (m c - j)) * MvPolynomial.C (((m c).choose j : ℕ) : ℚ_[p])
        = MvPolynomial.C (q c ^ j * x c ^ (m c - j) * ((m c).choose j : ℚ_[p])) *
            monomial (Finsupp.single c j) 1 := by simp only [map_mul]; ring
      _ = _ := by rw [C_mul_monomial, mul_one]
  simp_rw [hexp]
  rw [prod_univ_sum]
  simp_rw [prod_monomial_eq]
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

/-- **The weighted Vandermonde bound.** -/
theorem norm_det_confluent_le {K : ℕ} (x : Fin K → ℚ_[p]) (b w : Fin K → ℕ)
    (e : Fin K → Fin K → ℕ)
    (hx : ∀ c c', c < c' → ‖x c' - x c‖ ≤ ((p : ℝ)⁻¹) ^ e c c')
    (hw : ∀ c c', c < c' → e c c' ≤ w c ∧ e c c' ≤ w c') :
    ‖(Matrix.of fun (i c : Fin K) => (((i : ℕ).choose (b c) : ℕ) : ℚ_[p]) *
        x c ^ ((i : ℕ) - b c)).det‖ * ((p : ℝ)⁻¹) ^ (∑ c, b c * w c) ≤
      ((p : ℝ)⁻¹) ^ (∑ c, ∑ c' ∈ Ioi c, e c c') := by
  classical
  set q : Fin K → ℚ_[p] := fun c => (p : ℚ_[p]) ^ w c with hq
  set v : Fin K → MvPolynomial (Fin K) ℚ_[p] :=
    fun c => MvPolynomial.C (x c) + MvPolynomial.C (q c) * MvPolynomial.X c with hv
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- factorisation of the Vandermonde
  set L : Fin K → Fin K → MvPolynomial (Fin K) ℚ_[p] := fun c c' =>
    MvPolynomial.C ((x c' - x c) / (p : ℚ_[p]) ^ e c c') +
      MvPolynomial.C ((p : ℚ_[p]) ^ (w c' - e c c')) * MvPolynomial.X c' -
      MvPolynomial.C ((p : ℚ_[p]) ^ (w c - e c c')) * MvPolynomial.X c with hL
  have hfac : ∀ c c', c < c' → v c' - v c =
      MvPolynomial.C ((p : ℚ_[p]) ^ e c c') * L c c' := by
    intro c c' hcc
    obtain ⟨h1, h2⟩ := hw c c' hcc
    simp only [hv, hL, hq, mul_add, mul_sub, ← mul_assoc, ← map_mul]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hp0), ← pow_add, ← pow_add,
      Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2, map_sub]
    ring
  have hLint : ∀ c c', c < c' → IntMv (L c c') := by
    intro c c' hcc
    refine ((IntMv.C ?_).add ((IntMv.C ?_).mul (IntMv.X _))).sub ((IntMv.C ?_).mul (IntMv.X _))
    · rw [norm_div, norm_p_pow, div_le_one (pow_pos (inv_pos.2 (by
        exact_mod_cast (Fact.out : p.Prime).pos)) _)]; exact hx c c' hcc
    · rw [norm_p_pow]; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by
        exact_mod_cast (Fact.out : p.Prime).one_lt.le))
    · rw [norm_p_pow]; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by
        exact_mod_cast (Fact.out : p.Prime).one_lt.le))
  set G := ∏ c, ∏ c' ∈ Ioi c, L c c' with hG
  have hGint : IntMv G := IntMv.prod _ fun c _ => IntMv.prod _ fun c' hc' =>
    hLint c c' (mem_Ioi.1 hc')
  have hdetM : (vandermonde v).det =
      MvPolynomial.C ((p : ℚ_[p]) ^ (∑ c, ∑ c' ∈ Ioi c, e c c')) * G := by
    rw [det_vandermonde]
    have : ∀ c, ∏ c' ∈ Ioi c, (v c' - v c) =
        MvPolynomial.C ((p : ℚ_[p]) ^ (∑ c' ∈ Ioi c, e c c')) * ∏ c' ∈ Ioi c, L c c' := by
      intro c
      rw [prod_congr rfl fun c' hc' => hfac c c' (mem_Ioi.1 hc'), prod_mul_distrib, ← map_prod,
        prod_pow_eq_pow_sum]
    rw [prod_congr rfl fun c _ => this c, prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum]
  -- the coefficient of `∏ y_c^{b_c}`
  set Eb : Matrix (Fin K) (Fin K) ℚ_[p] := Matrix.of fun (i c : Fin K) =>
    (((i : ℕ).choose (b c) : ℕ) : ℚ_[p]) * x c ^ ((i : ℕ) - b c) with hEb
  have hcoeff : coeff (Finsupp.equivFunOnFinite.symm b) (vandermonde v).det =
      (∏ c, q c ^ b c) * Eb.det := by
    rw [← det_transpose, det_apply, det_apply Eb, coeff_sum, mul_sum]
    refine sum_congr rfl fun σ _ => ?_
    simp only [transpose_apply, vandermonde_apply]
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← map_intCast
      (MvPolynomial.C (σ := Fin K) (R := ℚ_[p])), coeff_C_mul]
    simp only [hv]
    rw [coeff_prod_linear_pow]
    simp only [hEb, Matrix.of_apply]
    rw [mul_left_comm, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun c _ => ?_
    ring
  have hnorm : ‖coeff (Finsupp.equivFunOnFinite.symm b) (vandermonde v).det‖ ≤
      ((p : ℝ)⁻¹) ^ (∑ c, ∑ c' ∈ Ioi c, e c c') := by
    rw [hdetM, coeff_C_mul, norm_mul, norm_p_pow]
    exact mul_le_of_le_one_right (by positivity) (hGint _)
  have hq : ‖∏ c, q c ^ b c‖ = ((p : ℝ)⁻¹) ^ (∑ c, b c * w c) := by
    rw [norm_prod, ← prod_pow_eq_pow_sum]
    refine prod_congr rfl fun c _ => ?_
    rw [norm_pow, hq, norm_p_pow, ← pow_mul, mul_comm]
  rw [hcoeff, norm_mul, hq] at hnorm
  rw [mul_comm]; exact hnorm

end Hankel2
