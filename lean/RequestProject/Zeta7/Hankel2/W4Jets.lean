import Mathlib
import RequestProject.Zeta7.Hankel2.W3Gram
import RequestProject.Zeta7.Hankel2.W2Local

/-!
# W4, polynomial part: jets at a partner node

`ZETA7_STATUS.md`, round (e) §2 (Lemma W4, special pairs).  If a polynomial `F` with `p`-integral jets
at `c` vanishes to order `N` at `c`, then its jets at a `p`-close point `c + d` (`v_p(d) ≥ 1`) satisfy
`v_p(F_j(c + d)) ≥ N - j` (`padicNorm_jet_shift_le`).  Jets of a product are the convolution of the
jets (`jet_mul`), so vanishing orders add (`jet_mul_eq_zero`).
-/

open Polynomial

namespace Hankel2.W3

variable {p : ℕ} [hp : Fact p.Prime]

/-- Jets at `c + d` in terms of jets at `c`: `F_j(c + d) = Σ_m F_m(c) C(m, j) d^{m-j}`. -/
theorem hasseDeriv_eval_add (F : ℚ[X]) (c d : ℚ) (j : ℕ) :
    (hasseDeriv j F).eval (c + d) = ∑ m ∈ Finset.range ((taylor c F).natDegree + 1),
      (hasseDeriv m F).eval c * (m.choose j : ℚ) * d ^ (m - j) := by
  rw [← taylor_coeff, add_comm c d, ← taylor_taylor, taylor_coeff]
  conv_lhs => rw [(taylor c F).as_sum_range' _ (Nat.lt_succ_self _)]
  simp only [map_sum, hasseDeriv_monomial, eval_finset_sum, eval_monomial, taylor_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Jets at a partner node.**  If `|F_m(c)|_p ≤ 1` for all `m`, `F_m(c) = 0` for `m < N`, and
`|d|_p ≤ p⁻¹`, then `|F_j(c + d)|_p ≤ p^{j - N}`. -/
theorem padicNorm_jet_shift_le (F : ℚ[X]) (c d : ℚ) (N j : ℕ)
    (hint : ∀ m, padicNorm p ((hasseDeriv m F).eval c) ≤ 1)
    (hvan : ∀ m < N, (hasseDeriv m F).eval c = 0) (hd : padicNorm p d ≤ (p : ℚ)⁻¹) :
    padicNorm p ((hasseDeriv j F).eval (c + d)) ≤ (p : ℚ) ^ ((j : ℤ) - N) := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  rw [hasseDeriv_eval_add]
  refine padicNorm.sum_le' (fun m _ => ?_) (zpow_pos hp0 _).le
  by_cases hmN : m < N
  · rw [hvan m hmN]; simp [(zpow_pos hp0 _).le]
  by_cases hmj : m < j
  · rw [Nat.choose_eq_zero_of_lt hmj]; simp [(zpow_pos hp0 _).le]
  push_neg at hmN hmj
  rw [padicNorm.mul, padicNorm.mul]
  have hc : padicNorm p ((m.choose j : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
  have hdpow : padicNorm p (d ^ (m - j)) ≤ (p : ℚ) ^ ((j : ℤ) - N) := by
    rw [W2.padicNorm_pow' (p := p)]
    calc padicNorm p d ^ (m - j) ≤ ((p : ℚ)⁻¹) ^ (m - j) :=
          pow_le_pow_left₀ (padicNorm.nonneg _) hd _
      _ = (p : ℚ) ^ (-((m - j : ℕ) : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (p : ℚ) ^ ((j : ℤ) - N) := zpow_le_zpow_right₀ h1.le (by push_cast [hmj]; omega)
  calc padicNorm p ((hasseDeriv m F).eval c) * padicNorm p ((m.choose j : ℕ) : ℚ) *
        padicNorm p (d ^ (m - j))
      ≤ 1 * (p : ℚ) ^ ((j : ℤ) - N) :=
        mul_le_mul (mul_le_one₀ (hint m) (padicNorm.nonneg _) hc) hdpow (padicNorm.nonneg _)
          zero_le_one
    _ = (p : ℚ) ^ ((j : ℤ) - N) := one_mul _

/-- Jets of a product: `(FG)_j = Σ_{a + b = j} F_a G_b`. -/
theorem jet_mul (F G : ℚ[X]) (c : ℚ) (j : ℕ) :
    (hasseDeriv j (F * G)).eval c =
      ∑ ab ∈ Finset.antidiagonal j, (hasseDeriv ab.1 F).eval c * (hasseDeriv ab.2 G).eval c := by
  rw [hasseDeriv_mul, eval_finset_sum]
  simp

/-- Vanishing orders add. -/
theorem jet_mul_eq_zero (F G : ℚ[X]) (c : ℚ) (A B j : ℕ) (hF : ∀ m < A, (hasseDeriv m F).eval c = 0)
    (hG : ∀ m < B, (hasseDeriv m G).eval c = 0) (hj : j < A + B) :
    (hasseDeriv j (F * G)).eval c = 0 := by
  rw [jet_mul]
  refine Finset.sum_eq_zero fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  by_cases ha : ab.1 < A
  · rw [hF _ ha, zero_mul]
  · rw [hG _ (by omega), mul_zero]

end Hankel2.W3
