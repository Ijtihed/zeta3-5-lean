import RequestProject.Zeta35.DenAssembly
import RequestProject.Zeta35.ArchProfile
import RequestProject.Zeta7.Hankel2.EulerGamma

/-!
# The certificate bound `c(κ) ≤ 71.2` on `[5.9, 6]` (the field `table_c`)

With `rest(κ) = stepBound + 3κ/20 + 2/400` (`cRest35`; `stepBound ≈ 196.7616` is the
kernel-checked step sum of the certificate) and `M₀ = −γ − ½ ln 3`:

  `c(κ) = [κ(12 − κ)(M₀ − ln 20) + rest(κ)] / ln 2 ≤ 71.2`  for `κ ∈ [5.9, 6]`

(**`table_c_holds`**), using `γ ≥ 0.5772`, `ln 3 > 1.0986`, `ln 20 > 2.9955`, `ln 2 > 0.6931471803`
and `κ(12 − κ) ≥ 35.99`.
-/

namespace Zeta35.Den

/-- `ln 20 > 2.9955`, from `e < 2.7182818286` and `e^{0.0045} ≥ 1.0045`. -/
theorem log_twenty_gt : (2.9955 : ℝ) < Real.log 20 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have h3 : Real.exp 3 < 2.7182818286 ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    have : Real.exp 1 * Real.exp 1 * Real.exp 1 = Real.exp 1 ^ 3 := by ring
    rw [this]
    exact pow_lt_pow_left₀ he he0.le (by norm_num)
  have hs : (1.0045 : ℝ) ≤ Real.exp 0.0045 := by
    have := Real.add_one_le_exp (0.0045 : ℝ); linarith
  have hsplit : Real.exp 3 = Real.exp 2.9955 * Real.exp 0.0045 := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos 2.9955
  nlinarith

/-- `κ(12 − κ) ≥ 35.99` on `[5.9, 6]`. -/
theorem kappa_lower {κ : ℝ} (h1 : 5.9 ≤ κ) (h2 : κ ≤ 6) : 35.99 ≤ κ * (12 - κ) := by
  nlinarith

/-- **The certificate bound** (the field `table_c`): `c(κ) ≤ 71.2` on `[5.9, 6]`. -/
theorem table_c_holds : ∀ κ : ℝ, 5.9 ≤ κ → κ ≤ 6 → cConst mertens3Const cRest35 κ ≤ 71.2 := by
  intro κ h1 h2
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  obtain ⟨hγ, -⟩ := Hankel2.EulerGamma.eulerMascheroni_bounds
  obtain ⟨hl3, -⟩ := log_three_bounds
  have hl20 := log_twenty_gt
  have hm : mertens3Const - Real.log 20 ≤ -4.122 := by
    unfold mertens3Const; linarith
  have hA := kappa_lower h1 h2
  have hAm : κ * (12 - κ) * (mertens3Const - Real.log 20) ≤ 35.99 * (-4.122) := by
    have hm0 : mertens3Const - Real.log 20 < 0 := by linarith
    nlinarith
  unfold cConst cRest35 stepBound
  rw [div_le_iff₀ hl2']
  push_cast
  nlinarith

end Zeta35.Den
