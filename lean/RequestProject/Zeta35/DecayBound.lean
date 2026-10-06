import RequestProject.Zeta35.InputDefs

/-!
# The asymptotic size of the decay exponent (paper N, Theorem 3.1, last sentence)

N, Theorem 3.1 gives `v₃(Δ_K(ζ₃(5))) ≥ 2 ∑_{i<K} v₃(i!_S) + K(4(3n+1) − log₃ D − log₃(D+1))`
(`decayExp`).  Here we prove the elementary consequence used in the assembly:

* `vS_ge`: `v₃(i!_S) ≥ −i/4 − 7/4 − ⌊log₃ i⌋`;
* `decayExp_ge`: for `K ≥ 2`, `decayExp n K ≥ 12 n K − K²/4 − 4 K log₃(2K − 1)`, i.e.
  `(12κ − κ²/4) n² − O(n log n)` for `K = κ n`.
-/

open Finset

namespace Zeta35

/-- `⌊a/d⌋ ≥ a/d − 1`. -/
theorem natDiv_ge (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d - 1 ≤ ((a / d : ℕ) : ℝ) := by
  have h := Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (a : ℝ) = d * ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) := by exact_mod_cast h.symm
  have hr' : ((a % d : ℕ) : ℝ) < d := by exact_mod_cast hr
  rw [div_sub_one hdR.ne', div_le_iff₀ hdR, e]
  nlinarith

theorem vS_ge (i : ℕ) : -(i : ℝ) / 4 - 7 / 4 - (Nat.log 3 i : ℝ) ≤ (vS i : ℝ) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [vS]; norm_num
  set J := Nat.log 3 i with hJdef
  have hJ1 : i < 3 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) i
  have hJi : J + 1 ≤ i + 1 := by
    have h1 : J < 3 ^ J := Nat.lt_pow_self (by norm_num)
    have h2 : 3 ^ J ≤ i := Nat.pow_log_le_self 3 hi.ne'
    omega
  have hsub : ∑ j ∈ range (J + 1), (((i / (2 * 3 ^ j) : ℕ) : ℤ) : ℝ) ≤
      ∑ j ∈ range (i + 1), (((i / (2 * 3 ^ j) : ℕ) : ℤ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hJi)
      (fun j _ _ => by positivity)
  have hfl : ∑ j ∈ range (J + 1), ((i : ℝ) / (2 * 3 ^ j) - 1) ≤
      ∑ j ∈ range (J + 1), (((i / (2 * 3 ^ j) : ℕ) : ℤ) : ℝ) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := natDiv_ge i (2 * 3 ^ j) (by positivity)
    push_cast at this ⊢
    exact this
  have hgeom : ∑ j ∈ range (J + 1), ((i : ℝ) / (2 * 3 ^ j) - 1) =
      3 * i / 4 * (1 - (1 / 3 : ℝ) ^ (J + 1)) - (J + 1) := by
    rw [Finset.sum_sub_distrib]
    have : ∑ j ∈ range (J + 1), (i : ℝ) / (2 * 3 ^ j) = (i / 2) * ∑ j ∈ range (J + 1), (1 / 3 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_div_pow]; field_simp
    rw [this, geom_sum_eq (by norm_num)]
    simp
    ring
  have hsmall : 3 * (i : ℝ) / 4 * (1 / 3 : ℝ) ^ (J + 1) ≤ 3 / 4 := by
    have h3 : (i : ℝ) < 3 ^ (J + 1) := by exact_mod_cast hJ1
    rw [one_div_pow]
    have hp : (0 : ℝ) < 3 ^ (J + 1) := by positivity
    rw [show 3 * (i : ℝ) / 4 * (1 / 3 ^ (J + 1)) = (3 / 4) * (i / 3 ^ (J + 1)) by ring]
    have : (i : ℝ) / 3 ^ (J + 1) ≤ 1 := by rw [div_le_one hp]; exact h3.le
    nlinarith
  have hv : (vS i : ℝ) = -(i : ℝ) + ∑ j ∈ range (i + 1), (((i / (2 * 3 ^ j) : ℕ) : ℤ) : ℝ) := by
    simp [vS]
  rw [hv]
  have : 3 * (i : ℝ) / 4 * (1 - (1 / 3 : ℝ) ^ (J + 1)) - (J + 1) ≤
      ∑ j ∈ range (i + 1), (((i / (2 * 3 ^ j) : ℕ) : ℤ) : ℝ) := by
    rw [← hgeom]; exact hfl.trans hsub
  push_cast at this ⊢
  nlinarith

theorem natLog_le_logb (K : ℕ) (hK : 0 < K) : (Nat.log 3 K : ℝ) ≤ Real.logb 3 K := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hK)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 3 hK.ne'

theorem sum_vS_ge (K : ℕ) (hK : 0 < K) :
    -((K : ℝ) * (K - 1) / 8) - K * (7 / 4 + Real.logb 3 K) ≤ ∑ i ∈ range K, (vS i : ℝ) := by
  have hL := natLog_le_logb K hK
  have h1 : ∀ i ∈ range K, -(i : ℝ) / 4 - 7 / 4 - Real.logb 3 K ≤ (vS i : ℝ) := by
    intro i hi
    have hiK : i ≤ K := (Finset.mem_range.1 hi).le
    have := vS_ge i
    have h2 : (Nat.log 3 i : ℝ) ≤ Nat.log 3 K := by exact_mod_cast Nat.log_mono_right hiK
    linarith
  have hsum : ∀ N : ℕ, ∑ i ∈ range N, (-(i : ℝ) / 4 - 7 / 4 - Real.logb 3 K) =
      -((N : ℝ) * (N - 1) / 8) - N * (7 / 4 + Real.logb 3 K) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [← hsum]
  exact Finset.sum_le_sum h1

/-- **The decay exponent is `(12κ − κ²/4) n² − O(n log n)`**: for `K ≥ 2`,
`decayExp n K ≥ 12 n K − K²/4 − 4 K log₃(2K − 1)`. -/
theorem decayExp_ge (n K : ℕ) (hK : 2 ≤ K) :
    12 * (n : ℝ) * K - (K : ℝ) ^ 2 / 4 - 4 * K * Real.logb 3 (2 * K - 1) ≤ decayExp n K := by
  have hK0 : 0 < K := by omega
  have hS := sum_vS_ge K hK0
  have hD : ((2 * K - 2 : ℕ) : ℝ) = 2 * K - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hl1 : Real.logb 3 ((2 * K - 2 : ℕ) : ℝ) ≤ Real.logb 3 (2 * K - 1) := by
    rw [hD]; exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hl2 : Real.logb 3 K ≤ Real.logb 3 (2 * K - 1) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hl3 : Real.logb 3 (((2 * K - 2 : ℕ) : ℝ) + 1) = Real.logb 3 (2 * K - 1) := by
    rw [hD]; ring_nf
  rw [decayExp, hl3]
  have hKn : (0 : ℝ) ≤ K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl1 hKn, mul_le_mul_of_nonneg_left hl2 hKn]

end Zeta35
