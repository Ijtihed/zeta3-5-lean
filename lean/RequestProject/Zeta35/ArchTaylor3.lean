import RequestProject.Zeta35.InputDefs
import RequestProject.Zeta7.Hankel2.ArchTaylor

/-!
# Archimedean bounds for the local data (start of N, Theorem 4.1; W, Lemma 4.1)

The first, purely local, ingredients of the archimedean bound, for the weight without zeros:

* `Hser_eq_prod`: `u⁴ W(−k + u) = ∏_{k' ≠ k} (k' − k + u)^{-4}`;
* `Hk_zero_eq`: `h_k = H_k[0] = ∏_{k' ≠ k} (k' − k)^{-4}`, so `ln|h_k| = −4 ∑_{k' ≠ k} ln|k' − k|`
  (`log_abs_Hk_zero`);
* `abs_Hk_le`: `|H_k[b]| ≤ |h_k| Λ^b` with `Λ = 4|S|` (every pole contributes `4/|k' − k| ≤ 4`);
* `abs_hsum3_le`, `abs_Sk_le`: `|S_k(M)| ≤ M 3^{M+1} ζ(2)` for `M ≥ 1`;
* `abs_alphaC_le`, `abs_betaC_le`, `l1_cPoly_le`: `‖c_{k,m}‖₁ = |β_{k,m}| + |α_{k,m}| ≤ Q |h_k|` with
  `Q = 2·10⁵ Λ³`, `Λ = 4(2R+1)`, for every node `k` and `m ≤ 3`.

These are the `p = 3`, `d = 1` analogues of `Hankel2.ArchB.abs_Hk_le`, `abs_HS_le` and
`l1_cPoly_le`.
-/

open Finset Hankel2 Hankel2.ArchB

namespace Zeta35.Arch

section PF

variable (S : Finset ℤ)

theorem Hser_eq_prod (k : ℤ) :
    PF.Hser S k = ∏ k' ∈ S.erase k,
      ((PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X)⁻¹) ^ 4 := by
  unfold PF.Hser
  rw [PowerSeries.inv_eq_iff_mul_eq_one (PF.constantCoeff_Ek S k), PF.Ek,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k' hk' => ?_
  have hne : (((k' - k : ℤ) : ℚ)) ≠ 0 := by
    have := Finset.ne_of_mem_erase hk'
    exact_mod_cast sub_ne_zero.2 this
  rw [← mul_pow, PowerSeries.inv_mul_cancel _ (by push_cast at hne; simpa using hne), one_pow]

theorem Hk_zero_eq (k : ℤ) :
    PF.Hk S k 0 = ∏ k' ∈ S.erase k, (((k' - k : ℤ) : ℚ)⁻¹) ^ 4 := by
  unfold PF.Hk
  rw [Hser_eq_prod, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [map_pow, PowerSeries.constantCoeff_inv]
  simp

/-- **`|H_k[b]| ≤ |h_k| Λ^b`**, `Λ = 4|S|`. -/
theorem abs_Hk_le (k : ℤ) (b : ℕ) :
    |((PF.Hk S k b : ℚ) : ℝ)| ≤ |((PF.Hk S k 0 : ℚ) : ℝ)| * (4 * (S.card : ℝ)) ^ b := by
  have hfac : ∀ k' ∈ S.erase k, SerBound
      (((PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X)⁻¹) ^ 4)
      ((|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ 4)
      ((4 : ℕ) * (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹) := by
    intro k' hk'
    have hne : (((k' - k : ℤ) : ℚ)) ≠ 0 := by
      have := Finset.ne_of_mem_erase hk'
      exact_mod_cast sub_ne_zero.2 this
    exact (SerBound.inv_lin hne).pow (by positivity) (by positivity) 4
  have hall := SerBound.prod (S.erase k) hfac (fun _ _ => by positivity)
    (fun _ _ => by positivity)
  have hA : ∏ k' ∈ S.erase k, (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ 4 =
      |((PF.Hk S k 0 : ℚ) : ℝ)| := by
    rw [Hk_zero_eq]
    push_cast
    rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun k' _ => by rw [abs_pow, abs_inv]
  have hΛ : ∑ k' ∈ S.erase k, ((4 : ℕ) : ℝ) * (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ≤
      4 * (S.card : ℝ) := by
    calc _ ≤ ∑ _k' ∈ S.erase k, (4 : ℝ) := by
          refine Finset.sum_le_sum fun k' hk' => ?_
          have hne : (k' - k : ℤ) ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hk')
          have h1 : (1 : ℝ) ≤ |((k' - k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
          have e : (Rat.cast ((k' - k : ℤ) : ℚ) : ℝ) = ((k' - k : ℤ) : ℝ) := by push_cast; ring
          rw [e]
          have : |((k' - k : ℤ) : ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
          push_cast at this ⊢
          linarith
      _ = 4 * ((S.erase k).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 4 * (S.card : ℝ) := by
          have : ((S.erase k).card : ℝ) ≤ S.card := by
            exact_mod_cast Finset.card_erase_le
          linarith
  have h := (hall.mono (prod_nonneg fun _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity) hΛ) b
  rw [hA, ← Hser_eq_prod] at h
  exact h

/-- `ln|h_k| = −4 ∑_{k' ≠ k} ln|k' − k|` (exact). -/
theorem log_abs_Hk_zero (k : ℤ) :
    Real.log |((PF.Hk S k 0 : ℚ) : ℝ)| = -4 * ∑ k' ∈ S.erase k, Real.log |((k' - k : ℤ) : ℝ)| := by
  rw [Hk_zero_eq]
  push_cast
  rw [Finset.abs_prod, Real.log_prod (fun k' hk' => ?_), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [abs_pow, abs_inv, Real.log_pow, Real.log_inv]; push_cast; ring
  · have hne : (k' - k : ℤ) ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hk')
    have : ((k' : ℝ) - k) ≠ 0 := by exact_mod_cast hne
    positivity

end PF

/-! ### The harmonic sums -/

theorem abs_hsum3_le (N M : ℕ) (hM : 1 ≤ M) :
    |((hsum3 N M : ℚ) : ℝ)| ≤ Real.pi ^ 2 / 6 := by
  unfold hsum3
  push_cast
  have hnn : 0 ≤ ∑ m ∈ (range (3 * N)).filter (fun m => ¬ 3 ∣ m), (((m : ℝ) ^ (M + 1))⁻¹) :=
    sum_nonneg fun _ _ => by positivity
  rw [abs_of_nonneg hnn]
  calc ∑ m ∈ (range (3 * N)).filter (fun m => ¬ 3 ∣ m), (((m : ℝ) ^ (M + 1))⁻¹)
      ≤ ∑ m ∈ (range (3 * N)).filter (fun m => ¬ 3 ∣ m), 1 / (m : ℝ) ^ 2 := by
        refine sum_le_sum fun m hm => ?_
        have hm0 : m ≠ 0 := by
          rintro rfl; simp at hm
        have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm0
        rw [one_div]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))
    _ ≤ Real.pi ^ 2 / 6 :=
        sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- **`|S_k(M)| ≤ M 3^{M+1} ζ(2)`** for `M ≥ 1`. -/
theorem abs_Sk_le (k : ℤ) (M : ℕ) (hM : 1 ≤ M) :
    |((Sk k M : ℚ) : ℝ)| ≤ M * 3 ^ (M + 1) * (Real.pi ^ 2 / 6) := by
  have h := abs_hsum3_le k.natAbs M hM
  have hp : 0 ≤ (M : ℝ) * 3 ^ (M + 1) := by positivity
  unfold Sk
  split_ifs
  · push_cast
    simp only [abs_mul, abs_neg, Nat.abs_cast, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left h hp
  · push_cast
    simp only [abs_mul, abs_neg, Nat.abs_cast, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left h hp
  · simp; positivity

/-! ### The local factors `c_{k,m} = β_{k,m} + X α_{k,m}` -/

/-- `Λ = 4(2R+1)`. -/
def LamZ (n : ℕ) : ℝ := 4 * (2 * R n + 1 : ℕ)

theorem one_le_LamZ (n : ℕ) : 1 ≤ LamZ n := by
  unfold LamZ
  have : (1 : ℝ) ≤ ((2 * R n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
  linarith

theorem abs_Hk_le' (n : ℕ) (k : ℤ) (b : ℕ) :
    |((Hk n k b : ℚ) : ℝ)| ≤ |((Hk n k 0 : ℚ) : ℝ)| * LamZ n ^ b := by
  have := abs_Hk_le (nodes n) k b
  rw [card_nodes] at this
  exact this

theorem abs_Hk_le_cube (n : ℕ) (k : ℤ) {b : ℕ} (hb : b ≤ 3) :
    |((Hk n k b : ℚ) : ℝ)| ≤ |((Hk n k 0 : ℚ) : ℝ)| * LamZ n ^ 3 :=
  (abs_Hk_le' n k b).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_LamZ n) hb) (abs_nonneg _))

theorem abs_alphaC_le (n : ℕ) (k : ℤ) (m : ℕ) :
    |((alphaC n k m : ℚ) : ℝ)| ≤ 2916 * LamZ n ^ 3 * |((Hk n k 0 : ℚ) : ℝ)| := by
  unfold alphaC
  split_ifs with hm
  · push_cast
    rw [abs_mul, abs_neg]
    have := abs_Hk_le_cube n k (b := 1 - m) (by omega)
    norm_num
    nlinarith [abs_nonneg ((Hk n k 0 : ℚ) : ℝ)]
  · simp only [Rat.cast_zero, abs_zero]
    have := one_le_LamZ n
    positivity

theorem abs_betaC_le (n : ℕ) (k : ℤ) (m : ℕ) :
    |((betaC n k m : ℚ) : ℝ)| ≤ 120000 * LamZ n ^ 3 * |((Hk n k 0 : ℚ) : ℝ)| := by
  set h := |((Hk n k 0 : ℚ) : ℝ)|
  have hh : 0 ≤ h := abs_nonneg _
  have hL := one_le_LamZ n
  have hz : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  unfold betaC
  push_cast
  rw [abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Icc 1 (4 - m), |(i : ℝ) * ((Hk n k (4 - i - m) : ℚ) : ℝ) * ((Sk k (i + 1) : ℚ) : ℝ)|
      ≤ ∑ _i ∈ Icc 1 (4 - m), 30000 * LamZ n ^ 3 * h := by
        refine sum_le_sum fun i hi => ?_
        obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have hH := abs_Hk_le_cube n k (b := 4 - i - m) (by omega)
        have hS := abs_Sk_le k (i + 1) (by omega)
        have hi' : (i : ℝ) ≤ 4 := by exact_mod_cast (by omega : i ≤ 4)
        have hS' : ((i + 1 : ℕ) : ℝ) * 3 ^ (i + 1 + 1) * (Real.pi ^ 2 / 6) ≤ 5 * 729 * 2 := by
          have h5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          have h3 : (3 : ℝ) ^ (i + 1 + 1) ≤ 3 ^ 6 :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
          calc ((i + 1 : ℕ) : ℝ) * 3 ^ (i + 1 + 1) * (Real.pi ^ 2 / 6)
              ≤ 5 * 3 ^ 6 * 2 := by gcongr
            _ = 5 * 729 * 2 := by norm_num
        have hSS := hS.trans hS'
        have hHL : 0 ≤ h * LamZ n ^ 3 := by positivity
        calc (i : ℝ) * |((Hk n k (4 - i - m) : ℚ) : ℝ)| * |((Sk k (i + 1) : ℚ) : ℝ)|
            ≤ 4 * (h * LamZ n ^ 3) * (5 * 729 * 2) := by
              gcongr
          _ ≤ 30000 * LamZ n ^ 3 * h := by nlinarith [hHL]
    _ ≤ 120000 * LamZ n ^ 3 * h := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have h4 : ((4 - m + 1 - 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : 4 - m + 1 - 1 ≤ 4)
        have h0 : 0 ≤ 30000 * LamZ n ^ 3 * h := by positivity
        calc ((4 - m + 1 - 1 : ℕ) : ℝ) * (30000 * LamZ n ^ 3 * h) ≤ 4 * (30000 * LamZ n ^ 3 * h) :=
              mul_le_mul_of_nonneg_right h4 h0
          _ = 120000 * LamZ n ^ 3 * h := by ring

/-- **`‖c_{k,m}‖₁ ≤ Q |h_k|`** with `Q = 2·10⁵ Λ³`. -/
theorem l1_cPoly_le (n : ℕ) (k : ℤ) (m : ℕ) :
    l1 (cPoly n k m) ≤ 200000 * LamZ n ^ 3 * |((Hk n k 0 : ℚ) : ℝ)| := by
  have hL := one_le_LamZ n
  have hh : 0 ≤ |((Hk n k 0 : ℚ) : ℝ)| := abs_nonneg _
  unfold cPoly
  split_ifs with hm
  · refine (ArchB.l1_add_le _ _).trans ?_
    rw [ArchB.l1_C]
    refine (add_le_add le_rfl (ArchB.l1_mul_le _ _)).trans ?_
    rw [ArchB.l1_C]
    have hX : l1 (Polynomial.X : Polynomial ℚ) = 1 := by
      simp [l1, Finset.sum_range_succ, Polynomial.coeff_X]
    rw [hX, mul_one]
    have := abs_alphaC_le n k m
    have := abs_betaC_le n k m
    have : 0 ≤ LamZ n ^ 3 * |((Hk n k 0 : ℚ) : ℝ)| := by positivity
    nlinarith
  · rw [ArchB.l1_zero]; positivity

end Zeta35.Arch
