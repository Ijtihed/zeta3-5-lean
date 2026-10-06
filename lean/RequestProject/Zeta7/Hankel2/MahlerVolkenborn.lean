import RequestProject.Zeta7.Hankel2.Volkenborn
import RequestProject.Zeta7.Hankel2.Bhargava

/-!
# The Volkenborn integral of the binomial polynomials

`∫_{ℤ_p} C(t, c) dt = (-1)^c / (c+1)`, where `C(t, c) = t(t-1)⋯(t-c+1)/c!`.

This is the basic formula behind the analytic half of Theorem A in `ZETA7_STATUS.md`:
for a Mahler series `f = ∑ f_c C(t,c)` one gets `∫ f = ∑ f_c (-1)^c/(c+1)`, so the Volkenborn
integral loses at most `log_p(c+1)` on the `c`-th Mahler coefficient.  Here the formula
is proved directly from the Riemann sums (`volkSum`): by the hockey-stick identity
`p^{-N} ∑_{t<p^N} C(t,c) = C(p^N - 1, c)/(c+1)`, and `C(p^N - 1, c) → C(-1, c) = (-1)^c`
`p`-adically.
-/

namespace Hankel2

open Filter Finset Topology Polynomial

variable {p : ℕ} [Fact p.Prime]

lemma sum_range_choose_eq (M c : ℕ) :
    ∑ t ∈ range M, t.choose c = M.choose (c + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ', add_comm]

lemma binomPoly_eval_nat (c t : ℕ) :
    (binomPoly p c).eval ((t : ℕ) : ℚ_[p]) = ((t.choose c : ℕ) : ℚ_[p]) := by
  unfold binomPoly
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have : ((c.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos c).ne'
  field_simp

lemma binomPoly_eval_neg_one (c : ℕ) : (binomPoly p c).eval (-1 : ℚ_[p]) = (-1) ^ c := by
  unfold binomPoly
  have h := ascPochhammer_eval_neg_eq_descPochhammer (R := ℚ_[p]) (-1) c
  rw [neg_neg, ascPochhammer_eval_one] at h
  have hc : ((c.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos c).ne'
  have hd : (descPochhammer ℚ_[p] c).eval (-1) = (-1) ^ c * (c.factorial : ℚ_[p]) := by
    have h1 : ((-1 : ℚ_[p]) ^ c) * (-1) ^ c = 1 := by
      rw [← mul_pow]; norm_num
    calc (descPochhammer ℚ_[p] c).eval (-1)
        = ((-1 : ℚ_[p]) ^ c * (-1) ^ c) * (descPochhammer ℚ_[p] c).eval (-1) := by
          rw [h1, one_mul]
      _ = (-1) ^ c * (c.factorial : ℚ_[p]) := by rw [mul_assoc, ← h]
  rw [eval_mul, eval_C, hd]
  field_simp

/-- **The Volkenborn integral of a binomial polynomial**:
`∫_{ℤ_p} C(t,c) dt = (-1)^c/(c+1)`. -/
theorem hasVolkenborn_binomPoly (c : ℕ) :
    HasVolkenborn p (fun t => (binomPoly p c).eval t) ((-1) ^ c / (c + 1)) := by
  unfold HasVolkenborn
  have hsum : ∀ N : ℕ, volkSum p (fun t => (binomPoly p c).eval t) N =
      (binomPoly p c).eval ((((p ^ N : ℕ) : ℚ_[p])) - 1) / (c + 1) := by
    intro N
    unfold volkSum
    simp_rw [binomPoly_eval_nat]
    rw [← Nat.cast_sum, sum_range_choose_eq]
    have hpos : 1 ≤ p ^ N := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    obtain ⟨m, hm⟩ : ∃ m, p ^ N = m + 1 := ⟨p ^ N - 1, by omega⟩
    have hkey := Nat.add_one_mul_choose_eq m c
    rw [← hm] at hkey
    have hcast : ((p : ℚ_[p]) ^ N) = ((m : ℚ_[p]) + 1) := by
      have := congrArg (fun k : ℕ => (k : ℚ_[p])) hm
      push_cast at this; exact this
    have hsub : (((p ^ N : ℕ) : ℚ_[p])) - 1 = (m : ℚ_[p]) := by
      push_cast; rw [hcast]; ring
    rw [hsub, binomPoly_eval_nat, hcast, hm]
    have hkey' : ((m : ℚ_[p]) + 1) * (m.choose c : ℚ_[p]) =
        ((m + 1).choose (c + 1) : ℚ_[p]) * ((c : ℚ_[p]) + 1) := by
      rw [hm] at hkey
      exact_mod_cast hkey
    have hm1 : (m : ℚ_[p]) + 1 ≠ 0 := by
      rw [← hcast]; exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hc1 : (c : ℚ_[p]) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
    field_simp
    linear_combination (-1 : ℚ_[p]) * hkey'
  rw [show volkSum p (fun t => (binomPoly p c).eval t) = fun N =>
      (binomPoly p c).eval ((((p ^ N : ℕ) : ℚ_[p])) - 1) / (c + 1) from funext hsum]
  have hlim : Tendsto (fun N : ℕ => (((p ^ N : ℕ) : ℚ_[p])) - 1) atTop (𝓝 (0 - 1)) :=
    (tendsto_p_pow_zero p).sub tendsto_const_nhds
  rw [zero_sub] at hlim
  have hcont := ((binomPoly p c).continuous.tendsto (-1)).comp hlim
  rw [binomPoly_eval_neg_one] at hcont
  exact hcont.div_const _

end Hankel2
