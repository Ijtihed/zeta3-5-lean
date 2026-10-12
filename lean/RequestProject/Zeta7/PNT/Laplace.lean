module

public import RequestProject.Zeta7.PNT.Newman
public import RequestProject.Zeta7.PNT.ZetaLog

/-!
# The Laplace transform of `ψ(eᵗ)e⁻ᵗ - 1` and the convergence of `∫ (ψ(eᵗ)e⁻ᵗ - 1) dt`

`chebF t = ψ(eᵗ) e⁻ᵗ - 1` is bounded and measurable; for `Re z > 0` its Laplace transform is
`newmanG z = L(Λ, z+1)/(z+1) - 1/z` (`laplace_chebF`).  Newman's theorem then gives
**`tendsto_integral_chebF`**: `∫₀^T (ψ(eᵗ)e⁻ᵗ - 1) dt → -(γ + 1)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set

namespace PNT

open Chebyshev

/-- `ψ(eᵗ) e⁻ᵗ - 1`. -/
noncomputable def chebF (t : ℝ) : ℝ := ψ (Real.exp t) * Real.exp (-t) - 1

theorem psi_exp_mul_le (t : ℝ) : ψ (Real.exp t) * Real.exp (-t) ≤ Real.log 4 + 4 := by
  have h := psi_le_const_mul_self (Real.exp_pos t).le
  have := Real.exp_pos (-t)
  calc ψ (Real.exp t) * Real.exp (-t) ≤ (Real.log 4 + 4) * Real.exp t * Real.exp (-t) := by
        gcongr
    _ = Real.log 4 + 4 := by rw [mul_assoc, ← Real.exp_add]; simp

theorem psi_exp_mul_nonneg (t : ℝ) : 0 ≤ ψ (Real.exp t) * Real.exp (-t) :=
  mul_nonneg (psi_nonneg _) (Real.exp_pos _).le

theorem norm_chebF_le (t : ℝ) : ‖(chebF t : ℂ)‖ ≤ Real.log 4 + 5 := by
  rw [norm_real, Real.norm_eq_abs, chebF, abs_le]
  have h1 := psi_exp_mul_le t
  have h2 := psi_exp_mul_nonneg t
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  constructor <;> linarith

theorem measurable_chebF : Measurable chebF := by
  unfold chebF
  exact ((psi_mono.measurable.comp Real.measurable_exp).mul (by fun_prop)).sub_const 1

theorem psi_eq_sum_Icc_one (x : ℝ) :
    (ψ x : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) := by
  rw [psi]; push_cast; rfl

theorem image_exp_Ioi_zero : Real.exp '' Ioi 0 = Ioi 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩; exact Real.one_lt_exp_iff.mpr ht
  · intro hx
    have hx0 : 0 < x := lt_trans one_pos hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log hx0⟩

theorem ofReal_exp_cpow (t : ℝ) (w : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ w = cexp (t * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log
    (Real.exp_pos t).le, Real.log_exp]

/-- The Mellin form of the `L`-series of `Λ`. -/
theorem integral_psi_cpow {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (ψ x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have h1 : ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k = ψ n := by
      rw [psi, Nat.floor_natCast]; rfl
    rw [h1, Real.norm_of_nonneg (psi_nonneg _), Real.rpow_one, Real.norm_of_nonneg (by positivity)]
    exact psi_le_const_mul_self (by positivity)
  rw [LSeries_eq_mul_integral_of_nonneg _ zero_le_one hs hO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg), mul_div_cancel_left₀ _ hs0]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [psi_eq_sum_Icc_one]

/-- Change of variables `x = eᵗ`. -/
theorem integral_psi_exp {z : ℂ} :
    ∫ t in Ioi (0 : ℝ), (ψ (Real.exp t) : ℂ) * cexp (-(z + 1) * t) =
      ∫ x in Ioi (1 : ℝ), (ψ x : ℂ) * (x : ℂ) ^ (-(z + 1 + 1)) := by
  rw [← image_exp_Ioi_zero, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [abs_of_pos (Real.exp_pos t), real_smul, ofReal_exp_cpow]
  rw [ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2; ring

theorem laplace_chebF {z : ℂ} (hz : 0 < z.re) :
    newmanG z = ∫ t in Ioi 0, (chebF t : ℂ) * cexp (-z * t) := by
  have hs : 1 < (z + 1).re := by simp; linarith
  have hint1 : IntegrableOn (fun t : ℝ => cexp (-z * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
  have hint2 : IntegrableOn (fun t : ℝ => (ψ (Real.exp t) : ℂ) * cexp (-(z + 1) * t)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0).const_mul
      (Real.log 4 + 4)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (psi_mono.measurable.comp Real.measurable_exp)).mul
        (by fun_prop)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t _ => ?_
      rw [norm_mul, norm_exp, norm_real, Real.norm_of_nonneg (psi_nonneg _)]
      have : (-(z + 1) * (t : ℂ)).re = -z.re * t + -t := by simp; ring
      rw [this, Real.exp_add, ← mul_assoc, mul_comm _ (Real.exp (-z.re * t)), mul_assoc,
        mul_comm (Real.exp (-z.re * t))]
      gcongr
      exact psi_exp_mul_le t
  have hpt : ∀ t : ℝ, (chebF t : ℂ) * cexp (-z * t) =
      (ψ (Real.exp t) : ℂ) * cexp (-(z + 1) * t) - cexp (-z * t) := by
    intro t
    simp only [chebF]
    push_cast
    have : cexp (-(z + 1) * t) = cexp (-t) * cexp (-z * t) := by
      rw [← Complex.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [hpt]
  rw [integral_sub hint2 hint1, integral_psi_exp, integral_psi_cpow hs,
    integral_exp_mul_complex_Ioi (by simp; linarith), newmanG_eq hz]
  simp

/-- **Convergence of `∫₀^∞ (ψ(eᵗ)e⁻ᵗ - 1) dt`**, with value `-(γ + 1)` (Newman's theorem). -/
theorem tendsto_integral_chebF :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, chebF t) atTop
      (𝓝 (-(Real.eulerMascheroniConstant + 1))) := by
  have h := newman_tauberian (fun t => (chebF t : ℂ))
    (Complex.measurable_ofReal.comp measurable_chebF) (Real.log 4 + 5)
    (fun t _ => norm_chebF_le t) newmanU isOpen_newmanU (fun z hz => half_subset_newmanU hz)
    newmanG differentiableOn_newmanG (fun z hz => laplace_chebF hz)
  rw [newmanG_zero] at h
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, intervalIntegral.integral_ofReal, ofReal_re] at h2
  simpa using h2

end PNT
