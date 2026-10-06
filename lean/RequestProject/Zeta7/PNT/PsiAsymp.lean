module

public import RequestProject.Zeta7.PNT.Laplace

/-!
# The prime number theorem: `ψ(x) ~ x` and `θ(x) ~ x`

From the convergence of `J(T) = ∫₀^T (ψ(eᵗ)e⁻ᵗ - 1) dt` (`tendsto_integral_chebF`) and the
monotonicity of `ψ` (Newman's Tauberian step, in the variable `t = log x`):
if `ψ(x) ≥ λx` with `λ > 1`, then `J(log x + log λ) - J(log x) ≥ λ - 1 - log λ > 0`, and
if `ψ(x) ≤ λx` with `λ < 1`, then `J(log x) - J(log x + log λ) ≤ 1 - λ + log λ < 0`.

* **`tendsto_psi_div`**: `ψ(x)/x → 1`;
* **`tendsto_theta_div`**: `θ(x)/x → 1` (using `|ψ - θ| ≤ 2√x log x`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real

namespace PNT

open Chebyshev

theorem intervalIntegrable_chebF (a b : ℝ) : IntervalIntegrable chebF volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => Real.log 4 + 5) intervalIntegrable_const
    measurable_chebF.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have := norm_chebF_le t
  rwa [Complex.norm_real] at this

/-- Cauchy criterion for `J`. -/
theorem chebF_cauchy {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ a b : ℝ, T₀ ≤ a → T₀ ≤ b → |∫ t in a..b, chebF t| < ε := by
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp tendsto_integral_chebF (ε / 2) (by positivity)
  refine ⟨T₀, fun a b ha hb => ?_⟩
  rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_chebF 0 b)
    (intervalIntegrable_chebF 0 a)]
  have h1 := hT₀ a ha
  have h2 := hT₀ b hb
  rw [Real.dist_eq] at h1 h2
  rw [abs_lt] at h1 h2 ⊢; constructor <;> linarith

/-- `∫_a^b (λ e^{c-t} - 1) dt = λ(e^{c-a} - e^{c-b}) - (b - a)`. -/
theorem integral_lin_exp (l c a b : ℝ) :
    ∫ t in a..b, (l * Real.exp (c - t) - 1) = l * (Real.exp (c - a) - Real.exp (c - b)) - (b - a) := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun t => -(l * Real.exp (c - t)) - t) (f' := fun t => l * Real.exp (c - t) - 1)
    (fun t _ => by
      have h := (((hasDerivAt_const t c).sub (hasDerivAt_id t)).exp.const_mul l).neg.sub
        (hasDerivAt_id t)
      convert h using 1; simp)
    ((by fun_prop : Continuous fun t => l * Real.exp (c - t) - 1).intervalIntegrable _ _)
  rw [this]; ring

theorem pos_of_ne_one {l : ℝ} (hl : 0 < l) (hl1 : l ≠ 1) : 0 < l - 1 - Real.log l := by
  linarith [Real.log_lt_sub_one_of_pos hl hl1]

/-- Upper bound: `ψ(x) < λx` eventually, for `λ > 1`. -/
theorem eventually_psi_lt {l : ℝ} (hl : 1 < l) : ∀ᶠ x in atTop, ψ x < l * x := by
  obtain ⟨T₀, hT₀⟩ := chebF_cauchy (pos_of_ne_one (by linarith) hl.ne')
  filter_upwards [eventually_ge_atTop (Real.exp T₀)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  by_contra hcon
  push_neg at hcon
  set t0 := Real.log x
  set L := Real.log l
  have hL : 0 < L := Real.log_pos hl
  have ht0 : T₀ ≤ t0 := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hbound : ∀ t ∈ Icc t0 (t0 + L), l * Real.exp (t0 - t) - 1 ≤ chebF t := by
    intro t ht
    unfold chebF
    have h1 : x ≤ Real.exp t := by rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr ht.1
    have h2 : l * x ≤ ψ (Real.exp t) := hcon.trans (psi_mono h1)
    have h3 : l * Real.exp (t0 - t) = l * x * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]; ring
    rw [h3]
    have := Real.exp_pos (-t)
    nlinarith
  have hint := intervalIntegral.integral_mono_on (by linarith) ((by fun_prop :
    Continuous fun t => l * Real.exp (t0 - t) - 1).intervalIntegrable _ _)
    (intervalIntegrable_chebF _ _) hbound
  rw [integral_lin_exp] at hint
  have hval : l * (Real.exp (t0 - t0) - Real.exp (t0 - (t0 + L))) - (t0 + L - t0) =
      l - 1 - Real.log l := by
    rw [sub_self, Real.exp_zero, show t0 - (t0 + L) = -L by ring, Real.exp_neg,
      Real.exp_log (by linarith)]
    field_simp; ring
  rw [hval] at hint
  have := hT₀ t0 (t0 + L) ht0 (by linarith)
  have := le_abs_self (∫ t in t0..t0 + L, chebF t)
  linarith

/-- Lower bound: `ψ(x) > λx` eventually, for `0 < λ < 1`. -/
theorem eventually_lt_psi {l : ℝ} (hl0 : 0 < l) (hl : l < 1) : ∀ᶠ x in atTop, l * x < ψ x := by
  obtain ⟨T₀, hT₀⟩ := chebF_cauchy (pos_of_ne_one hl0 hl.ne)
  set L := -Real.log l
  have hL : 0 < L := by have := Real.log_neg hl0 hl; simp only [L]; linarith
  filter_upwards [eventually_ge_atTop (Real.exp (T₀ + L))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  by_contra hcon
  push_neg at hcon
  set t0 := Real.log x
  have ht0 : T₀ + L ≤ t0 := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hbound : ∀ t ∈ Icc (t0 - L) t0, chebF t ≤ l * Real.exp (t0 - t) - 1 := by
    intro t ht
    unfold chebF
    have h1 : Real.exp t ≤ x := by rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr ht.2
    have h2 : ψ (Real.exp t) ≤ l * x := (psi_mono h1).trans hcon
    have h3 : l * Real.exp (t0 - t) = l * x * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]; ring
    rw [h3]
    have := Real.exp_pos (-t)
    nlinarith
  have hint := intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_chebF _ _)
    ((by fun_prop : Continuous fun t => l * Real.exp (t0 - t) - 1).intervalIntegrable _ _) hbound
  rw [integral_lin_exp] at hint
  have hval : l * (Real.exp (t0 - (t0 - L)) - Real.exp (t0 - t0)) - (t0 - (t0 - L)) =
      -(l - 1 - Real.log l) := by
    rw [sub_self, Real.exp_zero, show t0 - (t0 - L) = L by ring]
    simp only [L, Real.exp_neg, Real.exp_log hl0]
    field_simp; ring
  rw [hval] at hint
  have := hT₀ (t0 - L) t0 (by linarith) (by linarith)
  have := neg_abs_le (∫ t in t0 - L..t0, chebF t)
  linarith

/-- **The prime number theorem** (Chebyshev `ψ` form): `ψ(x)/x → 1`. -/
theorem tendsto_psi_div : Tendsto (fun x : ℝ => ψ x / x) atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set l := max a (1 / 2)
    have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hl1 : l < 1 := max_lt ha (by norm_num)
    filter_upwards [eventually_lt_psi hl0 hl1, eventually_gt_atTop 0] with x hx hx0
    rw [lt_div_iff₀ hx0]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le) hx
  · filter_upwards [eventually_psi_lt hb, eventually_gt_atTop 0] with x hx hx0
    rwa [div_lt_iff₀ hx0]

theorem tendsto_log_div_sqrt : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow]

/-- **The prime number theorem** (Chebyshev `θ` form): `θ(x)/x → 1`. -/
theorem tendsto_theta_div : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) := by
  have h2 : Tendsto (fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
    simpa using tendsto_log_div_sqrt.const_mul 2
  have hdiff : Tendsto (fun x : ℝ => ψ x / x - θ x / x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have h := abs_psi_sub_theta_le_sqrt_mul_log hx
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    calc |ψ x - θ x| ≤ 2 * Real.sqrt x * Real.log x := h
      _ = 2 * (Real.log x / Real.sqrt x) * (Real.sqrt x * Real.sqrt x) := by field_simp
      _ = 2 * (Real.log x / Real.sqrt x) * x := by rw [hs]
  have := tendsto_psi_div.sub hdiff
  simpa using this

end PNT
