import Mathlib

/-!
# Bounds for the Euler–Mascheroni constant: `0.5772 ≤ γ ≤ 0.5773`

With `u_m = H_m − ln m − 1/(2m) + 1/(12 m²)` and `v_m = u_m − 1/(120 m⁴)`:

* `uS_succ_le`: `u_{m+1} ≤ u_m` for `m ≥ 1` (lower bound `ln(1 + 1/m) ≥ 2y + 2y³/3`,
  `y = 1/(2m+1)`, from the series `hasSum_log_one_add_inv`);
* `vS_le_succ`: `v_m ≤ v_{m+1}` for `m ≥ 1` (upper bound
  `ln(1 + 1/m) ≤ 2y + 2y³/3 + 2y⁵/5 + 2y⁷/(7(1 − y²))`);
* both sequences tend to `γ` (`Real.tendsto_eulerMascheroniSeq'`), so `v_4 ≤ γ ≤ u_4`;
* with `ln 2 ∈ (0.6931471803, 0.6931471808)` this gives **`eulerMascheroni_bounds`**.
-/

open Real Filter Topology Finset

namespace Hankel2.EulerGamma

/-- `u_m = H_m − ln m − 1/(2m) + 1/(12 m²)`. -/
noncomputable def uS (m : ℕ) : ℝ := harmonic m - Real.log m - 1 / (2 * m) + 1 / (12 * (m : ℝ) ^ 2)

/-- `v_m = u_m − 1/(120 m⁴)`. -/
noncomputable def vS (m : ℕ) : ℝ := uS m - 1 / (120 * (m : ℝ) ^ 4)

theorem log_one_add_inv_ge {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ Real.log (1 + a⁻¹) := by
  have h := hasSum_log_one_add_inv ha
  have hy : 0 < 1 / (2 * a + 1) := by positivity
  have := sum_le_hasSum (range 2) (fun i _ => by positivity) h
  simp only [sum_range_succ, sum_range_zero] at this
  norm_num at this ⊢
  linarith

theorem log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ 2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 +
      2 / 5 * (1 / (2 * a + 1)) ^ 5 +
      2 / 7 * (1 / (2 * a + 1)) ^ 7 / (1 - (1 / (2 * a + 1)) ^ 2) := by
  set y := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h := hasSum_log_one_add_inv ha
  rw [← hy] at h
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) with hf
  have h3 := (hasSum_nat_add_iff' 3).mpr h
  have hg : HasSum (fun k : ℕ => 2 / 7 * y ^ 7 * (y ^ 2) ^ k) (2 / 7 * y ^ 7 / (1 - y ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 / 7 * y ^ 7)
    simpa [div_eq_mul_inv] using this
  have hle := hasSum_le (fun k => by
    show f (k + 3) ≤ 2 / 7 * y ^ 7 * (y ^ 2) ^ k
    simp only [hf]
    have e : y ^ (2 * (k + 3) + 1) = y ^ 7 * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [e]
    have hk : (0 : ℝ) ≤ k := by positivity
    have : 2 * (1 / (2 * ((k + 3 : ℕ) : ℝ) + 1)) ≤ 2 / 7 := by
      push_cast
      have h7 : (7 : ℝ) ≤ 2 * ((k : ℝ) + 3) + 1 := by linarith
      have := one_div_le_one_div_of_le (by norm_num) h7
      linarith
    have hp : 0 ≤ y ^ 7 * (y ^ 2) ^ k := by positivity
    nlinarith) h3 hg
  simp only [sum_range_succ, sum_range_zero, hf] at hle
  norm_num at hle ⊢
  linarith

theorem uS_succ_le {m : ℕ} (hm : 1 ≤ m) : uS (m + 1) ≤ uS m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog := log_one_add_inv_ge hm0
  have e : Real.log ((m + 1 : ℕ) : ℝ) = Real.log m + Real.log (1 + (m : ℝ)⁻¹) := by
    rw [← Real.log_mul hm0.ne' (by positivity)]
    congr 1; push_cast; field_simp
  unfold uS
  rw [harmonic_succ, e]
  push_cast
  have key : 1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * m) +
      1 / (12 * ((m : ℝ) + 1) ^ 2) - 1 / (12 * (m : ℝ) ^ 2) ≤
      2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * (m : ℝ) + 1)) ^ 3 := by
    rw [← sub_nonneg]
    have ex : 2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * (m : ℝ) + 1)) ^ 3 -
        (1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * m) +
          1 / (12 * ((m : ℝ) + 1) ^ 2) - 1 / (12 * (m : ℝ) ^ 2)) =
        (2 * m ^ 2 + 2 * m + 1) / (12 * m ^ 2 * (m + 1) ^ 2 * (2 * m + 1) ^ 3) := by
      field_simp; ring
    rw [ex]; positivity
  push_cast at hlog
  rw [inv_eq_one_div]
  linarith

theorem vS_le_succ {m : ℕ} (hm : 1 ≤ m) : vS m ≤ vS (m + 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog := log_one_add_inv_le hm0
  have e : Real.log ((m + 1 : ℕ) : ℝ) = Real.log m + Real.log (1 + (m : ℝ)⁻¹) := by
    rw [← Real.log_mul hm0.ne' (by positivity)]
    congr 1; push_cast; field_simp
  unfold vS uS
  rw [harmonic_succ, e]
  push_cast
  have key : 2 * (1 / (2 * (m : ℝ) + 1)) + 2 / 3 * (1 / (2 * (m : ℝ) + 1)) ^ 3 +
      2 / 5 * (1 / (2 * (m : ℝ) + 1)) ^ 5 +
      2 / 7 * (1 / (2 * (m : ℝ) + 1)) ^ 7 / (1 - (1 / (2 * (m : ℝ) + 1)) ^ 2) ≤
      1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * m) +
        1 / (12 * ((m : ℝ) + 1) ^ 2) - 1 / (12 * (m : ℝ) ^ 2) +
        1 / (120 * (m : ℝ) ^ 4) - 1 / (120 * ((m : ℝ) + 1) ^ 4) := by
    rw [← sub_nonneg]
    have h1 : (1 : ℝ) - (1 / (2 * (m : ℝ) + 1)) ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 := by
      field_simp; ring
    rw [h1]
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have ex : 1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (2 * m) +
        1 / (12 * ((m : ℝ) + 1) ^ 2) - 1 / (12 * (m : ℝ) ^ 2) +
        1 / (120 * (m : ℝ) ^ 4) - 1 / (120 * ((m : ℝ) + 1) ^ 4) -
        (2 * (1 / (2 * (m : ℝ) + 1)) + 2 / 3 * (1 / (2 * (m : ℝ) + 1)) ^ 3 +
          2 / 5 * (1 / (2 * (m : ℝ) + 1)) ^ 5 +
          2 / 7 * (1 / (2 * (m : ℝ) + 1)) ^ 7 / (4 * m * (m + 1) / (2 * m + 1) ^ 2)) =
        (640 * m ^ 6 + 1920 * m ^ 5 + 2354 * m ^ 4 + 1508 * m ^ 3 + 532 * m ^ 2 + 98 * m + 7) /
          (840 * m ^ 4 * (m + 1) ^ 4 * (2 * m + 1) ^ 5) := by
      field_simp; ring
    rw [ex]; positivity
  rw [inv_eq_one_div]
  linarith

theorem uS_eq {m : ℕ} (hm : 1 ≤ m) :
    uS m = eulerMascheroniSeq' m + (-(1 / 2) * (1 / (m : ℝ)) + 1 / 12 * (1 / (m : ℝ)) * (1 / (m : ℝ))) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [eulerMascheroniSeq', if_neg (by omega), uS]
  field_simp; ring

theorem tendsto_uS : Tendsto uS atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h := tendsto_eulerMascheroniSeq'.add ((h1.const_mul (-(1 / 2))).add ((h1.const_mul (1 / 12)).mul h1))
  have e : eulerMascheroniConstant + (-(1 / 2) * 0 + 1 / 12 * 0 * 0) = eulerMascheroniConstant := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (uS_eq hm).symm

theorem tendsto_vS : Tendsto vS atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h := tendsto_uS.sub ((h1.pow 4).const_mul (1 / 120))
  have e : eulerMascheroniConstant - 1 / 120 * 0 ^ 4 = eulerMascheroniConstant := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  simp only [vS]
  field_simp

theorem eulerMascheroni_le_uS4 : eulerMascheroniConstant ≤ uS 4 := by
  have hA : Antitone fun k : ℕ => uS (k + 4) :=
    antitone_nat_of_succ_le fun k => uS_succ_le (m := k + 4) (by omega)
  have hT : Tendsto (fun k : ℕ => uS (k + 4)) atTop (𝓝 eulerMascheroniConstant) :=
    tendsto_uS.comp (tendsto_add_atTop_nat 4)
  exact hA.le_of_tendsto hT 0

theorem vS4_le_eulerMascheroni : vS 4 ≤ eulerMascheroniConstant := by
  have hM : Monotone fun k : ℕ => vS (k + 4) :=
    monotone_nat_of_le_succ fun k => vS_le_succ (m := k + 4) (by omega)
  have hT : Tendsto (fun k : ℕ => vS (k + 4)) atTop (𝓝 eulerMascheroniConstant) :=
    tendsto_vS.comp (tendsto_add_atTop_nat 4)
  exact hM.ge_of_tendsto hT 0

theorem uS4_eq : uS 4 = 25 / 12 - 2 * Real.log 2 - 1 / 8 + 1 / 192 := by
  have hh : (harmonic 4 : ℝ) = 25 / 12 := by
    simp only [harmonic, sum_range_succ, sum_range_zero]; norm_num
  have hl : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [uS, hh, hl]; norm_num

/-- **`0.5772 ≤ γ ≤ 0.5773`** (Mathlib-only; `γ = Real.eulerMascheroniConstant`). -/
theorem eulerMascheroni_bounds :
    (0.5772 : ℝ) ≤ eulerMascheroniConstant ∧ eulerMascheroniConstant ≤ 0.5773 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor
  · refine le_trans ?_ vS4_le_eulerMascheroni
    rw [vS, uS4_eq]; norm_num; linarith
  · refine eulerMascheroni_le_uS4.trans ?_
    rw [uS4_eq]; norm_num; linarith

theorem eulerMascheroni_ge : (0.5772 : ℝ) ≤ eulerMascheroniConstant := eulerMascheroni_bounds.1

theorem eulerMascheroni_le : eulerMascheroniConstant ≤ 0.5773 := eulerMascheroni_bounds.2

end Hankel2.EulerGamma
