import RequestProject.Zeta35.InputDefs

/-!
# The profile `σ_κ ≡ κ/3` (paper N, Theorem 4.1; CLAIMS T7, elementary closed forms)

* `logPot3_one`: `𝓛1(x) = (3/2 + x) ln(3/2 + x) + (3/2 − x) ln(3/2 − x) − 3`;
* `Lone_bounds`: `3 ln(3/2) − 3 ≤ 𝓛1(x) ≤ 3 ln 3 − 3` on `[−3/2, 3/2]` (a range of `3 ln 2`);
* `integral_Lone`: `J = ⟨1, 𝓛1⟩ = 9 ln 3 − 27/2`;
* `Fenergy3_sigmaK`: `F[σ_κ] = J (κ²/9 − 4κ/3)`;
* `gap3_sigmaK_le`: `gap(σ_κ) ≤ 3κ(4 − 2κ/3) ln 2` for `0 ≤ κ ≤ 6` (it is `0` at `κ = 6`);
* `Fdag_sigmaK_le`: `(F[σ_κ] + gap(σ_κ))/ln 2 ≤ (54 − 36 ln 3)/ln 2 + 3κ(4 − 2κ/3)`;
* `log_three_bounds`: `1.0986 < ln 3 < 1.0987`.
-/

open Real MeasureTheory Set

namespace Zeta35

/-- The closed form of `𝓛1`. -/
noncomputable def Lone (x : ℝ) : ℝ :=
  (3 / 2 + x) * Real.log (3 / 2 + x) + (3 / 2 - x) * Real.log (3 / 2 - x) - 3

theorem continuous_Lone : Continuous Lone := by
  unfold Lone
  have h := Real.continuous_mul_log
  exact ((h.comp (continuous_const.add continuous_id)).add
    (h.comp (continuous_const.sub continuous_id))).sub continuous_const

theorem logPot3_one (x : ℝ) : logPot3 (fun _ => 1) x = Lone x := by
  rw [logPot3]
  simp only [mul_one, Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left (fun u => Real.log u) x, integral_log]
  have : Real.log (x - 3 / 2) = Real.log (3 / 2 - x) := by
    rw [← Real.log_neg_eq_log]; ring_nf
  rw [Lone, show x - -3 / 2 = 3 / 2 + x by ring, this]
  ring

theorem mul_log_le_mul_log_three {a : ℝ} (ha0 : 0 ≤ a) (ha3 : a ≤ 3) :
    a * Real.log a ≤ a * Real.log 3 := by
  rcases ha0.lt_or_eq with ha | ha
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log ha ha3) ha.le
  · subst ha; simp

theorem mul_log_ge {a : ℝ} (ha0 : 0 ≤ a) :
    a * Real.log (3 / 2) + a - 3 / 2 ≤ a * Real.log a := by
  rcases ha0.lt_or_eq with ha | ha
  · have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < a / (3 / 2) by positivity)
    rw [Real.log_div ha.ne' (by norm_num)] at h1
    have h2 : a * (1 - (a / (3 / 2))⁻¹) = a - 3 / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]
  · subst ha; norm_num

theorem Lone_bounds {x : ℝ} (hx1 : -3 / 2 ≤ x) (hx2 : x ≤ 3 / 2) :
    3 * Real.log (3 / 2) - 3 ≤ Lone x ∧ Lone x ≤ 3 * Real.log 3 - 3 := by
  unfold Lone
  constructor
  · have := mul_log_ge (a := 3 / 2 + x) (by linarith)
    have := mul_log_ge (a := 3 / 2 - x) (by linarith)
    nlinarith
  · have := mul_log_le_mul_log_three (a := 3 / 2 + x) (by linarith) (by linarith)
    have := mul_log_le_mul_log_three (a := 3 / 2 - x) (by linarith) (by linarith)
    nlinarith

/-- `|𝓛1(x) − c₀| ≤ (3/2) ln 2` on `[−3/2, 3/2]`, with `c₀` the midpoint of the range. -/
theorem abs_Lone_sub_le {x : ℝ} (hx1 : -3 / 2 ≤ x) (hx2 : x ≤ 3 / 2) :
    |Lone x - (3 * Real.log 3 - 3 * Real.log 2 / 2 - 3)| ≤ 3 / 2 * Real.log 2 := by
  obtain ⟨h1, h2⟩ := Lone_bounds hx1 hx2
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  rw [h32] at h1
  rw [abs_le]; constructor <;> linarith

/-- `∫_0^3 u ln u du = (9/2) ln 3 − 9/4`. -/
theorem integral_mul_log_zero_three : ∫ u in (0 : ℝ)..3, u * Real.log u = 9 / 2 * Real.log 3 - 9 / 4 := by
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 3, HasDerivAt (fun u => u ^ 2 / 2 * Real.log u - u ^ 2 / 4)
      (u * Real.log u) u := by
    intro u hu
    have hu0 : u ≠ 0 := hu.1.ne'
    have h := (((hasDerivAt_pow 2 u).div_const 2).mul (Real.hasDerivAt_log hu0)).sub
      ((hasDerivAt_pow 2 u).div_const 4)
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun u : ℝ => u ^ 2 / 2 * Real.log u - u ^ 2 / 4) (Icc 0 3) := by
    have : (fun u : ℝ => u ^ 2 / 2 * Real.log u - u ^ 2 / 4) =
        fun u => u / 2 * (u * Real.log u) - u ^ 2 / 4 := by
      funext u; ring
    rw [this]
    exact ((continuous_id.div_const 2).mul Real.continuous_mul_log |>.sub
      ((continuous_pow 2).div_const 4)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv
    (Real.continuous_mul_log.intervalIntegrable _ _)]
  simp
  ring

/-- **`J = ⟨1, 𝓛1⟩ = 9 ln 3 − 27/2`.** -/
theorem integral_Lone : ∫ x in (-3 / 2 : ℝ)..(3 / 2), Lone x = 9 * Real.log 3 - 27 / 2 := by
  have hc := Real.continuous_mul_log
  have i1 : IntervalIntegrable (fun x : ℝ => (3 / 2 + x) * Real.log (3 / 2 + x)) volume
      (-3 / 2) (3 / 2) :=
    (hc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => (3 / 2 - x) * Real.log (3 / 2 - x)) volume
      (-3 / 2) (3 / 2) :=
    (hc.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  unfold Lone
  rw [intervalIntegral.integral_sub (i1.add i2) intervalIntegrable_const,
    intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_comp_add_left (fun u => u * Real.log u),
    intervalIntegral.integral_comp_sub_left (fun u => u * Real.log u)]
  norm_num
  rw [integral_mul_log_zero_three]
  ring

theorem logPot3_const (c x : ℝ) : logPot3 (fun _ => c) x = c * Lone x := by
  rw [← logPot3_one, logPot3, logPot3, ← intervalIntegral.integral_const_mul]
  congr 1; funext y; ring

theorem pairing3_const (c : ℝ) (g : ℝ → ℝ) :
    pairing3 (fun _ => c) g = c * ∫ x in (-3 / 2 : ℝ)..(3 / 2), g x := by
  rw [pairing3, intervalIntegral.integral_const_mul]

theorem Upot3_eq (x : ℝ) : Upot3 x = -4 * Lone x := by rw [Upot3, logPot3_one]

/-- **`F[σ_κ] = J (κ²/9 − 4κ/3)`**, `J = 9 ln 3 − 27/2`. -/
theorem Fenergy3_sigmaK (κ : ℝ) :
    Fenergy3 (sigmaK κ) = (9 * Real.log 3 - 27 / 2) * (κ ^ 2 / 9 - 4 * κ / 3) := by
  unfold sigmaK
  rw [Fenergy3, pairing3_const, pairing3_const]
  simp only [Upot3_eq, logPot3_const]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_Lone]
  ring

theorem intervalIntegrable_of_feasible {κ : ℝ} {σ : ℝ → ℝ} (h : Feasible3 κ σ) :
    IntervalIntegrable σ volume (-3 / 2) (3 / 2) := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (4 : ℝ)) intervalIntegrable_const
    h.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have := h.2.1 x
  show ‖σ x‖ ≤ 4
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

/-- **`gap(σ_κ) ≤ 3κ(4 − 2κ/3) ln 2`** for `0 ≤ κ ≤ 6`. -/
theorem gap3_sigmaK_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ6 : κ ≤ 6) :
    gap3 κ (sigmaK κ) ≤ 3 * κ * (4 - 2 * κ / 3) * Real.log 2 := by
  have hA : 0 ≤ 4 - 2 * κ / 3 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Real.sSup_le ?_ (by positivity)
  rintro g ⟨σ', hσ', rfl⟩
  set A := 4 - 2 * κ / 3
  set B := 3 / 2 * Real.log 2
  set c₀ := 3 * Real.log 3 - 3 * Real.log 2 / 2 - 3
  have hP : ∀ x, Pgrad3 (sigmaK κ) x = -A * Lone x := by
    intro x; unfold sigmaK; rw [Pgrad3, Upot3_eq, logPot3_const]; ring
  have hσ'i := intervalIntegrable_of_feasible hσ'
  have hLi : IntervalIntegrable Lone volume (-3 / 2) (3 / 2) :=
    continuous_Lone.intervalIntegrable _ _
  have hlhs : IntervalIntegrable (fun x => Pgrad3 (sigmaK κ) x * (σ' x - sigmaK κ x)) volume
      (-3 / 2) (3 / 2) := by
    simp only [hP, sigmaK]
    exact (hσ'i.sub intervalIntegrable_const).continuousOn_mul
      ((continuous_const.mul continuous_Lone).continuousOn)
  have hrhs : IntervalIntegrable (fun x => A * B * (σ' x + κ / 3) - A * c₀ * (σ' x - κ / 3))
      volume (-3 / 2) (3 / 2) :=
    ((hσ'i.add intervalIntegrable_const).const_mul _).sub
      ((hσ'i.sub intervalIntegrable_const).const_mul _)
  have hmono : pairing3 (Pgrad3 (sigmaK κ)) (fun x => σ' x - sigmaK κ x) ≤
      ∫ x in (-3 / 2 : ℝ)..(3 / 2), (A * B * (σ' x + κ / 3) - A * c₀ * (σ' x - κ / 3)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) hlhs hrhs fun x hx => ?_
    rw [hP]
    unfold sigmaK
    have hb := abs_Lone_sub_le hx.1 hx.2
    have hs := (hσ'.2.1 x).1
    have hk : 0 ≤ κ / 3 := by positivity
    have hd : |σ' x - κ / 3| ≤ σ' x + κ / 3 := by
      rw [abs_le]; constructor <;> linarith
    have key : -(Lone x - c₀) * (σ' x - κ / 3) ≤ B * (σ' x + κ / 3) := by
      calc -(Lone x - c₀) * (σ' x - κ / 3) ≤ |Lone x - c₀| * |σ' x - κ / 3| := by
            rw [← abs_mul, neg_mul]; exact neg_le_abs _
        _ ≤ B * (σ' x + κ / 3) := mul_le_mul hb hd (abs_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left key hA]
  refine hmono.trans (le_of_eq ?_)
  have hint : ∫ x in (-3 / 2 : ℝ)..(3 / 2), σ' x = κ := hσ'.2.2
  rw [intervalIntegral.integral_sub ((hσ'i.add intervalIntegrable_const).const_mul _)
      ((hσ'i.sub intervalIntegrable_const).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hσ'i intervalIntegrable_const,
    intervalIntegral.integral_sub hσ'i intervalIntegrable_const, hint]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **`F†(κ) ≤ (54 − 36 ln 3)/ln 2 + 3κ(4 − 2κ/3)`** for the profile `σ_κ`, `0 ≤ κ ≤ 6`.
At `κ = 6` this is `4(27/2 − 9 ln 3)/ln 2 = 20.846882…` bits. -/
theorem Fdag_sigmaK_le {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ6 : κ ≤ 6) (hl3 : Real.log 3 ≤ 1.5) :
    (Fenergy3 (sigmaK κ) + gap3 κ (sigmaK κ)) / Real.log 2 ≤
      (54 - 36 * Real.log 3) / Real.log 2 + 3 * κ * (4 - 2 * κ / 3) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Fenergy3_sigmaK, div_le_iff₀ hl2, add_mul, div_mul_cancel₀ _ hl2.ne']
  have hg := gap3_sigmaK_le hκ0 hκ6
  have hJ : 0 ≤ 27 / 2 - 9 * Real.log 3 := by linarith
  have hk : κ * (12 - κ) ≤ 36 := by nlinarith [sq_nonneg (κ - 6)]
  nlinarith [mul_le_mul_of_nonneg_left hk hJ]

/-! ### `ln 3` -/

/-- `1.0986 < ln 3 < 1.0987` (from the series of `ln(1 − 1/3)` and `ln 2`). -/
theorem log_three_bounds : 1.0986 < Real.log 3 ∧ Real.log 3 < 1.0987 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num [abs_of_pos]) 10
  have h23 : Real.log (1 - 1 / 3) = Real.log 2 - Real.log 3 := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h23] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  rw [abs_le] at h
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> nlinarith [h.1, h.2]

end Zeta35
