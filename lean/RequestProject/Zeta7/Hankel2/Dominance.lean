import Mathlib

/-!
# Non-vanishing at rational points by `p`-adic dominance of the constant coefficient

If the constant coefficient of a rational polynomial `F` is strictly `p`-adically larger than every
other coefficient, then `F` has no zero `r` with `|r|_p ≤ 1`, i.e. no rational zero whose denominator
is prime to `p`.

This is the algebraic step of the non-vanishing criterion of `ZETA7_STATUS.md` (family 3, task (b)):
for the parity factors `A_M(X)`, `B_M(X)` of the 2-adic Hankel determinant one observes (exactly, for
`n ≤ 25`) that `v_p(F(0)) < v_p([Xⁱ]F)` for all `i ≥ 1` and all primes `p ≤ 2n`; so if `ζ₂(7) = a/b`,
any such prime `p ∤ b` gives `F(a/b) ≠ 0`.
-/

open Polynomial

namespace Hankel2

theorem padicNorm_pow_le_one {p : ℕ} [Fact p.Prime] {r : ℚ} (hr : padicNorm p r ≤ 1) :
    ∀ k : ℕ, padicNorm p (r ^ k) ≤ 1
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, padicNorm.mul]
      exact mul_le_one₀ (padicNorm_pow_le_one hr k) (padicNorm.nonneg _) hr

/-- **`p`-adic dominance of the constant term forces non-vanishing.**
If `‖[Xⁱ]F‖_p < ‖F(0)‖_p` for every `i ≥ 1`, then `F(r) ≠ 0` for every rational `r` with
`‖r‖_p ≤ 1`. -/
theorem eval_ne_zero_of_padic_dominant {p : ℕ} [hp : Fact p.Prime] (F : ℚ[X])
    (hdom : ∀ i, 1 ≤ i → padicNorm p (F.coeff i) < padicNorm p (F.coeff 0))
    {r : ℚ} (hr : padicNorm p r ≤ 1) : F.eval r ≠ 0 := by
  have h0 : 0 < padicNorm p (F.coeff 0) :=
    lt_of_le_of_lt (padicNorm.nonneg _) (hdom 1 le_rfl)
  have htail : padicNorm p (∑ i ∈ Finset.range F.natDegree, F.coeff (i + 1) * r ^ (i + 1))
      < padicNorm p (F.coeff 0) := by
    rcases Nat.eq_zero_or_pos F.natDegree with hd | hd
    · simp [hd, h0]
    · refine padicNorm.sum_lt ?_ ?_
      · exact ⟨0, Finset.mem_range.mpr hd⟩
      · intro i _
        rw [padicNorm.mul]
        calc padicNorm p (F.coeff (i + 1)) * padicNorm p (r ^ (i + 1))
            ≤ padicNorm p (F.coeff (i + 1)) * 1 :=
              mul_le_mul_of_nonneg_left (padicNorm_pow_le_one hr _) (padicNorm.nonneg _)
          _ < padicNorm p (F.coeff 0) := by rw [mul_one]; exact hdom _ (Nat.succ_pos _)
  intro hzero
  have hsplit : F.eval r = F.coeff 0 +
      ∑ i ∈ Finset.range F.natDegree, F.coeff (i + 1) * r ^ (i + 1) := by
    rw [eval_eq_sum_range, Finset.sum_range_succ']
    simp [add_comm]
  rw [hzero] at hsplit
  have : F.coeff 0 = -∑ i ∈ Finset.range F.natDegree, F.coeff (i + 1) * r ^ (i + 1) := by
    linarith
  rw [this, padicNorm.neg] at htail
  exact lt_irrefl _ htail

/-- A rational number whose (reduced) denominator is prime to `p` has `‖r‖_p ≤ 1`. -/
theorem padicNorm_le_one_of_not_dvd_den {p : ℕ} [hp : Fact p.Prime] {r : ℚ}
    (h : ¬ p ∣ r.den) : padicNorm p r ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hr : r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
  rw [hr, padicNorm.div]
  have hden : padicNorm p (r.den : ℚ) = 1 := by
    have := padicNorm.nat_eq_one_iff (p := p) r.den
    exact this.mpr h
  rw [hden, div_one]
  exact_mod_cast padicNorm.of_int r.num

/-- **Non-vanishing criterion** in the form used for the Hankel factors: if the constant coefficient
of `F ∈ ℚ[X]` is strictly `p`-adically dominant, then `F(a/b) ≠ 0` whenever `p ∤ b`. -/
theorem eval_ne_zero_of_padic_dominant_of_not_dvd_den {p : ℕ} [Fact p.Prime] (F : ℚ[X])
    (hdom : ∀ i, 1 ≤ i → padicNorm p (F.coeff i) < padicNorm p (F.coeff 0))
    {r : ℚ} (h : ¬ p ∣ r.den) : F.eval r ≠ 0 :=
  eval_ne_zero_of_padic_dominant F hdom (padicNorm_le_one_of_not_dvd_den h)

end Hankel2
