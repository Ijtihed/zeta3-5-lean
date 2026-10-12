module

public import RequestProject.Zeta7.PNT.PsiAsymp

/-!
# Mertens' theorem for `Λ` with the constant: `∑_{n ≤ x} Λ(n)/n = log x - γ + o(1)`

Partial summation gives `∑_{n ≤ x} Λ(n)/n = ψ(x)/x + ∫₁^x ψ(t)/t² dt`
(`sum_vonMangoldt_div_eq`); the substitution `t = eᵘ` turns `∫₁^x (ψ(t) - t)/t² dt` into
`∫₀^{log x} (ψ(eᵘ)e⁻ᵘ - 1) du` (`integral_psi_sub_div_sq`), which tends to `-(γ + 1)`
(`tendsto_integral_chebF`).  Hence **`tendsto_sum_vonMangoldt_div_sub_log`**.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real

namespace PNT

open Chebyshev ArithmeticFunction

theorem measurable_psi : Measurable ψ := psi_mono.measurable

theorem integrableOn_psi_div_sq {x : ℝ} :
    IntegrableOn (fun t => ψ t / t ^ 2) (Ioc 1 x) := by
  refine Integrable.mono' (g := fun _ => Real.log 4 + 4) (integrableOn_const
    (by simp))
    ((measurable_psi.div (by fun_prop)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  have ht0 : 0 < t := lt_trans one_pos ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := psi_nonneg t; positivity),
    div_le_iff₀ (by positivity)]
  have h1 := psi_le_const_mul_self ht0.le
  have h2 : t ≤ t ^ 2 := by nlinarith [ht.1]
  have : 0 ≤ Real.log 4 + 4 := by have := Real.log_pos (by norm_num : (1:ℝ) < 4); linarith
  nlinarith

/-- Partial summation. -/
theorem sum_vonMangoldt_div_eq (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / n = ψ x / x + ∫ t in Ioc 1 x, ψ t / t ^ 2 := by
  have h := sum_mul_eq_sub_integral_mul₀ (𝕜 := ℝ) (c := fun n => Λ n) (f := fun t => t⁻¹)
    (by simp) x (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      rw [show deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ from funext fun t => deriv_inv]
      exact (ContinuousOn.integrableOn_Icc (continuousOn_of_forall_continuousAt fun t ht =>
        ((continuous_pow 2).continuousAt.inv₀ (by have := ht.1; positivity)).neg)))
  simp only [show deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ from funext fun t => deriv_inv,
    ← psi_eq_sum_Icc] at h
  rw [show (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / n) = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * Λ k from
    Finset.sum_congr rfl fun k _ => by ring, h]
  rw [sub_eq_add_neg, ← integral_neg]
  congr 1
  · ring
  · exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring

theorem image_exp_Ioc (L : ℝ) : Real.exp '' Ioc 0 L = Ioc 1 (Real.exp L) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨Real.one_lt_exp_iff.mpr ht.1, Real.exp_le_exp.mpr ht.2⟩
  · intro hx
    have hx0 : 0 < x := lt_trans one_pos hx.1
    refine ⟨Real.log x, ⟨Real.log_pos hx.1, ?_⟩, Real.exp_log hx0⟩
    rw [Real.log_le_iff_le_exp hx0]; exact hx.2

/-- Substitution `t = eᵘ`. -/
theorem integral_psi_sub_div_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Ioc 1 x, (ψ t - t) / t ^ 2 = ∫ u in (0 : ℝ)..Real.log x, chebF u := by
  have hx0 : 0 < x := by linarith
  rw [intervalIntegral.integral_of_le (Real.log_nonneg hx)]
  conv_lhs => rw [← Real.exp_log hx0, ← image_exp_Ioc]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  simp only [abs_of_pos (Real.exp_pos u), smul_eq_mul, chebF]
  have h1 : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  rw [Real.exp_neg]
  field_simp

theorem sum_vonMangoldt_div_sub_log_eq {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / n) - Real.log x =
      ψ x / x + ∫ u in (0 : ℝ)..Real.log x, chebF u := by
  have hx0 : 0 < x := by linarith
  rw [sum_vonMangoldt_div_eq x, ← integral_psi_sub_div_sq hx]
  have hint2 : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc 1 x) :=
    (ContinuousOn.integrableOn_Icc (a := (1 : ℝ)) (b := x)
      (continuousOn_of_forall_continuousAt fun (t : ℝ) (ht : t ∈ Icc 1 x) =>
      continuousAt_inv₀ (by linarith [ht.1] : t ≠ 0))).mono_set Ioc_subset_Icc_self
  have hsplit : ∫ t in Ioc 1 x, ψ t / t ^ 2 =
      (∫ t in Ioc 1 x, (ψ t - t) / t ^ 2) + ∫ t in Ioc 1 x, t⁻¹ := by
    rw [← integral_add]
    · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have : t ≠ 0 := by linarith [ht.1]
      field_simp; ring
    · refine IntegrableOn.congr_fun (integrableOn_psi_div_sq.sub hint2) (fun t ht => ?_)
        measurableSet_Ioc
      have : t ≠ 0 := by linarith [ht.1]
      simp only [Pi.sub_apply]
      field_simp
    · exact hint2
  have hlog : ∫ t in Ioc 1 x, t⁻¹ = Real.log x := by
    rw [← intervalIntegral.integral_of_le hx, integral_inv_of_pos one_pos hx0, div_one]
  rw [hsplit, hlog]; ring

/-- **Mertens' theorem for `Λ`, with constant**: `∑_{n ≤ x} Λ(n)/n - log x → -γ`. -/
theorem tendsto_sum_vonMangoldt_div_sub_log :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / n) - Real.log x) atTop
      (𝓝 (-eulerMascheroniConstant)) := by
  have h := tendsto_psi_div.add (tendsto_integral_chebF.comp tendsto_log_atTop)
  rw [show (1 : ℝ) + -(eulerMascheroniConstant + 1) = -eulerMascheroniConstant by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [sum_vonMangoldt_div_sub_log_eq hx]; rfl

end PNT
