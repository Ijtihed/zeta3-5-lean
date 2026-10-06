import RequestProject.Zeta35.Poly3

/-!
# The analytic core of N, Theorem 3.1 (one derivative, `p = 3`)

For a polynomial `Q` of degree `≤ D` with profile `M` and an admissible `Φ` (products of powers of
`(u + 3t)^{-1}`, `3 ∤ u`), `t ↦ (Q Φ)'(t + a)` has a Volkenborn integral of norm `≤ M · D · (D + 1)`:
one derivative costs `log₃ D`, integration costs `log₃(D+1)` (`exists_hasVolkenborn_deriv`).
This is the `p = 3`, one-derivative analogue of `Hankel2.exists_hasVolkenborn_iteratedDeriv_three`.
-/

open Filter Finset Topology Polynomial

namespace Zeta35.M3

open Hankel2

local notation "Δ₃" => fwdDiff (1 : ℚ_[3])

/-- A polynomial whose values at the naturals are `3`-integral has profile `1` up to its degree. -/
theorem prof_of_norm_le_one {Q : ℚ_[3][X]} {D : ℕ} (hQ : Q.natDegree ≤ D)
    (hint : ∀ x : ℕ, ‖Q.eval (x : ℚ_[3])‖ ≤ 1) :
    Prof (polyW 1 D) fun y => Q.eval y := by
  intro x j
  unfold polyW
  split_ifs with hj
  · rw [fwdDiff_iter_eq_sum_shift]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [zsmul_eq_mul, norm_mul]
    have h1 : ‖(((-1 : ℤ) ^ (j - k) * (j.choose k : ℤ) : ℤ) : ℚ_[3])‖ ≤ 1 :=
      Padic.norm_int_le_one _
    have h2 : ‖Q.eval ((x : ℚ_[3]) + k • (1 : ℚ_[3]))‖ ≤ 1 := by
      rw [nsmul_eq_mul, mul_one]
      have := hint (x + k); push_cast at this; exact this
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  · rw [fwdDiff_iter_eq_zero_of_degree_lt (by omega : Q.natDegree < j)]
    simp

/-- **The analytic core of N, Theorem 3.1.** -/
theorem exists_hasVolkenborn_deriv (Q : ℚ_[3][X]) {D : ℕ} (hD : 1 ≤ D)
    (hQ : Q.natDegree ≤ D) {M : ℝ} (hM : 0 ≤ M) (hp : Prof (polyW M D) fun y => Q.eval y)
    {Φ : ℚ_[3] → ℚ_[3]} (hΦ : Adm Φ) (a : ℚ_[3]) :
    ∃ I, HasVolkenborn 3
        (fun t => deriv (fun s => Q.eval (s - a) * Φ (s - a)) (t + a)) I ∧
      ‖I‖ ≤ M * (D : ℝ) * ((D : ℝ) + 1) := by
  obtain ⟨Φ1, hΦ1, hd0⟩ := hΦ.hasDerivAt
  set Q1 := derivative Q
  set G0 : ℚ_[3] → ℚ_[3] := fun u => Q.eval u * Φ u
  set G1 : ℚ_[3] → ℚ_[3] := fun u => Q1.eval u * Φ u + Q.eval u * Φ1 u
  set V := Metric.ball (0 : ℚ_[3]) 3
  have g0 : ∀ u ∈ V, HasDerivAt G0 (G1 u) u := fun u hu =>
    ((Q.hasDerivAt u).mul (hd0 u hu))
  have hint : ∀ t : ℕ, G1 t = deriv (fun s => Q.eval (s - a) * Φ (s - a)) ((t : ℚ_[3]) + a) := by
    intro t
    have hmem : ((t : ℚ_[3]) + a) - a ∈ V := by
      rw [add_sub_cancel_right, Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_natCast_le_one _ _) (by norm_num)
    have := (g0 _ hmem).comp_sub_const ((t : ℚ_[3]) + a) a
    rw [this.deriv, add_sub_cancel_right]
  have hMD : 0 ≤ M * (D : ℝ) := mul_nonneg hM (Nat.cast_nonneg _)
  have hQ1 : Prof (polyW (M * D) D) fun y => Q1.eval y := hp.polyDeriv hQ hM
  have hQ0 : Prof (polyW (M * D) D) fun y => Q.eval y := by
    refine hp.mono fun j => polyW_mono ?_ D j
    have h1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  have hG1 : Prof (fun j => M * (D : ℝ) * geo (j - D)) G1 := by
    have e : G1 = (fun u => Q1.eval u) * Φ + (fun u => Q.eval u) * Φ1 := by
      funext u; simp only [G1, Pi.add_apply, Pi.mul_apply]
    rw [e]
    exact (hQ1.polyW_mul_geo hMD hΦ.prof).add (hQ0.polyW_mul_geo hMD hΦ1.prof)
  obtain ⟨I, hI, hIn⟩ := exists_hasVolkenborn_of_prof hMD hG1
  refine ⟨I, ?_, hIn⟩
  have hvs : volkSum 3 G1 = volkSum 3
      (fun t => deriv (fun s => Q.eval (s - a) * Φ (s - a)) (t + a)) := by
    funext N; simp only [volkSum, hint]
  rwa [HasVolkenborn, ← hvs]

end Zeta35.M3
