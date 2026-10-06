import RequestProject.Zeta7.Hankel2.MahlerSeries
import RequestProject.Zeta7.Hankel2.Criterion

/-!
# Existence of the Volkenborn integrals of `(t + c)^{-m}`

For `‖c‖ > 1` the function `t ↦ (t + c)^{-m}` is analytic on `ℤ_p`:
`(t + c)^{-m} = c^{-m} ∑_i C(i+m-1, m-1) (-t/c)^i`.  Its Mahler coefficients
`a_j = Δ^j f(0)` therefore satisfy `‖a_j‖ ≤ ‖c‖^{-m-j}` (because `Δ^j(t^i)(0)` is an integer and
vanishes for `i < j`), so `‖a_j/(j+1)‖ → 0` and the Mahler-series theorem
`Hankel2.hasVolkenborn_mahler` gives the existence of the Volkenborn integral.

This removes the classical existence hypothesis (Volkenborn's theorem for strictly
differentiable functions) from all statements about inverse powers:

* `Hankel2.exists_hasVolkenborn_inv_pow` — `∫_{ℤ_p} (t + c)^{-m} dt` exists for `‖c‖ > 1`;
* `Hankel2.exists_hasVolkenborn_half` — in particular for `c = 1/2`, `p = 2`.
-/

namespace Hankel2

open Filter Finset Topology

variable {p : ℕ} [Fact p.Prime]

/-- `‖N‖_p ≥ 1/N` for a positive integer `N`. -/
theorem inv_le_norm_natCast {N : ℕ} (hN : 0 < N) : (N : ℝ)⁻¹ ≤ ‖(N : ℚ_[p])‖ := by
  have h := one_le_abs_mul_padic_norm p (N : ℤ) (by exact_mod_cast hN.ne')
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast at h
  rw [abs_of_pos hN'] at h
  rw [inv_le_iff_one_le_mul₀ hN']
  simpa [mul_comm] using h

/-- The finite differences of a power at `0` are integers: `Δ^j(x^i)(0) = ∑_l ±C(j,l) l^i`. -/
theorem fwdDiff_iter_pow_zero_eq_int (i j : ℕ) :
    (fwdDiff 1)^[j] (fun x : ℚ_[p] => x ^ i) 0 =
      ((∑ l ∈ range (j + 1), ((-1 : ℤ) ^ (j - l) * j.choose l) * (l : ℤ) ^ i : ℤ) : ℚ_[p]) := by
  rw [fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [zsmul_eq_mul]

theorem norm_fwdDiff_iter_pow_zero_le (i j : ℕ) :
    ‖(fwdDiff 1)^[j] (fun x : ℚ_[p] => x ^ i) 0‖ ≤ 1 := by
  rw [fwdDiff_iter_pow_zero_eq_int]
  exact Padic.norm_int_le_one _

/-- **Existence of the Volkenborn integral of `(t + c)^{-m}`** for `‖c‖ > 1`. -/
theorem exists_hasVolkenborn_inv_pow {c : ℚ_[p]} (hc : 1 < ‖c‖) (m : ℕ) :
    ∃ I, HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    refine ⟨1, ?_⟩
    have : volkSum p (fun t => ((t + c) ^ 0)⁻¹) = fun _ => 1 := by
      funext N
      simp only [volkSum, pow_zero, inv_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
      push_cast
      exact inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
    rw [HasVolkenborn, this]
    exact tendsto_const_nhds
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  set f : ℚ_[p] → ℚ_[p] := fun t => ((t + c) ^ m)⁻¹ with hf
  set F : ℕ → ℚ_[p] := fun l => f l with hF
  set a : ℕ → ℚ_[p] := fun j => (fwdDiff 1)^[j] F 0 with ha
  set ρ : ℝ := ‖c‖⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ hc
  -- the power-series coefficients
  set g : ℕ → ℚ_[p] := fun i => (c ^ m)⁻¹ * ((i + (m - 1)).choose (m - 1) : ℚ_[p]) * (-c⁻¹) ^ i
    with hg
  -- the power series at a natural number
  have hser : ∀ l : ℕ, HasSum (fun i => g i * (l : ℚ_[p]) ^ i) (F l) := by
    intro l
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    set r : ℚ_[p] := -(l : ℚ_[p]) * c⁻¹ with hr
    have hrn : ‖r‖ < 1 := by
      rw [hr, norm_mul, norm_neg, norm_inv]
      have hl : ‖(l : ℚ_[p])‖ ≤ 1 := by
        simpa using Padic.norm_int_le_one (p := p) (l : ℤ)
      calc ‖(l : ℚ_[p])‖ * ‖c‖⁻¹ ≤ 1 * ‖c‖⁻¹ := by gcongr
        _ < 1 := by rw [one_mul]; exact hρ1
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hrn).mul_left ((c ^ (k + 1))⁻¹)
    have hval : (c ^ (k + 1))⁻¹ * (1 / (1 - r) ^ (k + 1)) = F l := by
      simp only [hF, hf, hr]
      have hlc : (l : ℚ_[p]) + c ≠ 0 :=
        add_ne_zero_of_norm_lt (by simpa using Padic.norm_int_le_one (p := p) (l : ℤ)) hc
      have : (1 - -(l : ℚ_[p]) * c⁻¹) = ((l : ℚ_[p]) + c) * c⁻¹ := by
        field_simp; ring
      rw [this, mul_pow, inv_pow]
      field_simp
    rw [hval] at h
    refine h.congr_fun fun i => ?_
    simp only [hg, hr, Nat.add_sub_cancel]
    rw [mul_pow, neg_pow, neg_pow]
    ring
  -- the Mahler coefficients as power series
  have hmahl : ∀ j, HasSum (fun i => g i * (fwdDiff 1)^[j] (fun x : ℚ_[p] => x ^ i) 0) (a j) := by
    intro j
    have hsum := hasSum_sum (s := range (j + 1)) fun l (_ : l ∈ range (j + 1)) =>
      (hser l).mul_left (((-1 : ℤ) ^ (j - l) * j.choose l : ℤ) : ℚ_[p])
    have hA : a j = ∑ l ∈ range (j + 1), (((-1 : ℤ) ^ (j - l) * j.choose l : ℤ) : ℚ_[p]) * F l := by
      simp only [ha]
      rw [fwdDiff_iter_eq_sum_shift]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [zsmul_eq_mul]
    rw [hA]
    refine hsum.congr_fun fun i => ?_
    rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zsmul_eq_mul]
    ring
  -- the bound on the Mahler coefficients
  have hbound : ∀ j, ‖a j‖ ≤ ‖c‖⁻¹ ^ m * ρ ^ j := by
    intro j
    rw [← (hmahl j).tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    by_cases hij : i < j
    · rw [fwdDiff_iter_pow_eq_zero_of_lt hij]
      simp only [Pi.zero_apply, mul_zero, norm_zero]
      positivity
    · push_neg at hij
      rw [norm_mul]
      have h1 : ‖g i‖ ≤ ‖c‖⁻¹ ^ m * ρ ^ i := by
        simp only [hg, norm_mul, norm_inv, norm_pow, norm_neg]
        have hch : ‖((i + (m - 1)).choose (m - 1) : ℚ_[p])‖ ≤ 1 :=
          IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
        calc (‖c‖ ^ m)⁻¹ * ‖((i + (m - 1)).choose (m - 1) : ℚ_[p])‖ * ‖c‖⁻¹ ^ i
            ≤ (‖c‖ ^ m)⁻¹ * 1 * ‖c‖⁻¹ ^ i := by gcongr
          _ = ‖c‖⁻¹ ^ m * ρ ^ i := by rw [hρ, inv_pow]; ring
      have h2 : ρ ^ i ≤ ρ ^ j := pow_le_pow_of_le_one hρ0 hρ1.le hij
      calc ‖g i‖ * ‖(fwdDiff 1)^[j] (fun x : ℚ_[p] => x ^ i) 0‖
          ≤ (‖c‖⁻¹ ^ m * ρ ^ i) * 1 :=
            mul_le_mul h1 (norm_fwdDiff_iter_pow_zero_le i j) (norm_nonneg _) (by positivity)
        _ ≤ ‖c‖⁻¹ ^ m * ρ ^ j := by rw [mul_one]; gcongr
  -- decay of `a_j / (j+1)`
  have hdecay : Tendsto (fun j : ℕ => ‖a j / (j + 1)‖) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => ‖c‖⁻¹ ^ m * (((j : ℝ) + 1) * ρ ^ j)) atTop (𝓝 0) := by
      have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
      have h3 : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * ρ ^ j) atTop (𝓝 0) := by
        have := h1.add h2
        simp only [add_zero] at this
        refine this.congr fun j => ?_
        ring
      simpa using h3.const_mul (‖c‖⁻¹ ^ m)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hn : (((j + 1 : ℕ) : ℝ))⁻¹ ≤ ‖((j + 1 : ℕ) : ℚ_[p])‖ := inv_le_norm_natCast (by omega)
    push_cast at hn
    have hnpos : 0 < ‖(j : ℚ_[p]) + 1‖ := lt_of_lt_of_le (by positivity) hn
    rw [norm_div, div_le_iff₀ hnpos]
    calc ‖a j‖ ≤ ‖c‖⁻¹ ^ m * ρ ^ j := hbound j
      _ = ‖c‖⁻¹ ^ m * (((j : ℝ) + 1) * ρ ^ j) * ((j : ℝ) + 1)⁻¹ := by field_simp
      _ ≤ ‖c‖⁻¹ ^ m * (((j : ℝ) + 1) * ρ ^ j) * ‖(j : ℚ_[p]) + 1‖ := by gcongr
  -- the Mahler expansion
  have hnewton : ∀ t : ℕ, f t = ∑ j ∈ range (t + 1), a j * ((t.choose j : ℕ) : ℚ_[p]) := by
    intro t
    have := shift_eq_sum_fwdDiff_iter (1 : ℕ) F t 0
    simp only [zero_add, smul_eq_mul, mul_one] at this
    change F t = _
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nsmul_eq_mul, mul_comm]
  exact ⟨_, hasVolkenborn_mahler a f hnewton hdecay⟩

/-- Existence of `∫_{ℤ₂} (t + 1/2)^{-m} dt` for every `m`. -/
theorem exists_hasVolkenborn_half (m : ℕ) :
    ∃ I, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) I :=
  exists_hasVolkenborn_inv_pow norm_half_2 m

end Hankel2
