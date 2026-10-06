import RequestProject.Zeta35.MainR2
import RequestProject.Zeta35.LocalBlocks
import RequestProject.Zeta7.Hankel2.W3Family3
import RequestProject.Zeta7.Hankel2.W4Jets
import RequestProject.Zeta7.Hankel2.WeightCert

/-!
# Non-vanishing (N, §6): valuation bookkeeping

`VB ℓ q e` means `v_ℓ(q) ≥ e`, i.e. `|q|_ℓ ≤ ℓ^{-e}` (with `q = 0` allowed).  We collect the
ultrametric rules used in the weighted-valuation argument of N, Theorem 6.2.
-/

open Polynomial Finset

namespace Zeta35.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `v_ℓ(q) ≥ e`. -/
def VB (ℓ : ℕ) (q : ℚ) (e : ℤ) : Prop := padicNorm ℓ q ≤ (ℓ : ℚ) ^ (-e)

theorem one_lt_l : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt

theorem l_pos : (0 : ℚ) < ℓ := by linarith [one_lt_l (ℓ := ℓ)]

theorem VB.mono {q : ℚ} {e e' : ℤ} (h : VB ℓ q e) (he : e' ≤ e) : VB ℓ q e' :=
  h.trans (zpow_le_zpow_right₀ (one_lt_l (ℓ := ℓ)).le (by omega))

theorem VB_zero (e : ℤ) : VB ℓ 0 e := by
  simp only [VB, padicNorm.zero]; exact (zpow_pos l_pos _).le

theorem VB.mul {q r : ℚ} {e f : ℤ} (hq : VB ℓ q e) (hr : VB ℓ r f) : VB ℓ (q * r) (e + f) := by
  unfold VB at *
  rw [padicNorm.mul, neg_add, zpow_add₀ (l_pos (ℓ := ℓ)).ne']
  exact mul_le_mul hq hr (padicNorm.nonneg _) (zpow_pos l_pos _).le

omit hℓ in
theorem VB.neg {q : ℚ} {e : ℤ} (h : VB ℓ q e) : VB ℓ (-q) e := by
  unfold VB at *; rwa [padicNorm.neg]

theorem VB.add {q r : ℚ} {e : ℤ} (hq : VB ℓ q e) (hr : VB ℓ r e) : VB ℓ (q + r) e :=
  padicNorm.nonarchimedean.trans (max_le hq hr)

theorem VB.sub {q r : ℚ} {e : ℤ} (hq : VB ℓ q e) (hr : VB ℓ r e) : VB ℓ (q - r) e := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

theorem VB.sum {α : Type*} (s : Finset α) (f : α → ℚ) {e : ℤ} (h : ∀ i ∈ s, VB ℓ (f i) e) :
    VB ℓ (∑ i ∈ s, f i) e :=
  padicNorm.sum_le' h (zpow_pos l_pos _).le

theorem VB_int (z : ℤ) : VB ℓ (z : ℚ) 0 := by
  unfold VB; rw [neg_zero, zpow_zero]; exact padicNorm.of_int z

theorem VB_nat (m : ℕ) : VB ℓ (m : ℚ) 0 := by
  have := VB_int (ℓ := ℓ) (m : ℤ); simpa using this

theorem VB_one : VB ℓ 1 0 := by simpa using VB_nat (ℓ := ℓ) 1

theorem padicNorm_l_zpow (z : ℤ) : padicNorm ℓ ((ℓ : ℚ) ^ z) = (ℓ : ℚ) ^ (-z) := by
  have := Hankel2.W3.padicNorm_zpow_mul (p := ℓ) z 1
  simpa using this

theorem VB_l_zpow (z : ℤ) : VB ℓ ((ℓ : ℚ) ^ z) z := by
  unfold VB; rw [padicNorm_l_zpow]

theorem VB_l_pow (m : ℕ) : VB ℓ ((ℓ : ℚ) ^ m) m := by
  have := VB_l_zpow (ℓ := ℓ) (m : ℤ); simpa using this

theorem VB.pow {q : ℚ} {e : ℤ} (h : VB ℓ q e) (m : ℕ) : VB ℓ (q ^ m) (m * e) := by
  induction m with
  | zero => simpa using VB_one
  | succ m ih =>
      rw [pow_succ, show ((m + 1 : ℕ) : ℤ) * e = m * e + e by push_cast; ring]
      exact ih.mul h

/-- `|q|_ℓ < 1 ↔ v_ℓ(q) ≥ 1`. -/
theorem VB_one_iff (q : ℚ) : VB ℓ q 1 ↔ padicNorm ℓ q < 1 := by
  constructor
  · intro h; exact h.trans_lt (zpow_lt_one_of_neg₀ one_lt_l (by norm_num))
  · intro h
    rcases eq_or_ne q 0 with rfl | hq
    · exact VB_zero 1
    unfold VB
    rw [padicNorm.eq_zpow_of_nonzero hq] at h ⊢
    have h1 := one_lt_l (ℓ := ℓ)
    have : -padicValRat ℓ q < 0 := by
      by_contra hc; push_neg at hc
      exact absurd h (not_lt.mpr (one_le_zpow₀ h1.le hc))
    exact zpow_le_zpow_right₀ h1.le (by omega)

omit hℓ in
theorem VB_zero_iff (q : ℚ) : VB ℓ q 0 ↔ padicNorm ℓ q ≤ 1 := by
  simp [VB]

/-- A natural number prime to `ℓ` is an `ℓ`-adic unit, and so is its inverse. -/
theorem VB_inv_nat {m : ℕ} (hm : ¬ ℓ ∣ m) : VB ℓ ((m : ℚ)⁻¹) 0 := by
  unfold VB
  rw [Hankel2.W2.padicNorm_inv, (padicNorm.nat_eq_one_iff m).2 hm, inv_one, neg_zero, zpow_zero]

theorem VB_inv_int {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : VB ℓ ((m : ℚ)⁻¹) 0 := by
  unfold VB
  rw [Hankel2.W2.padicNorm_inv, (padicNorm.int_eq_one_iff m).2 hm, inv_one, neg_zero, zpow_zero]

theorem padicNorm_inv_int_eq {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : padicNorm ℓ ((m : ℚ)⁻¹) = 1 := by
  rw [Hankel2.W2.padicNorm_inv, (padicNorm.int_eq_one_iff m).2 hm, inv_one]

end Zeta35.NV
