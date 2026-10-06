import RequestProject.Zeta7.Hankel2.MahlerVolkenborn

/-!
# The Volkenborn integral of a Mahler series

If `f(t) = ∑_c a_c C(t,c)` on the natural numbers (a Mahler series; for `t ∈ ℕ` the sum is
finite) and `‖a_c/(c+1)‖ → 0`, then `f` has Volkenborn integral `∑_c a_c (-1)^c/(c+1)`, and
this integral has norm at most `sup_c ‖a_c/(c+1)‖`.

This is the interchange of the limit with the Mahler series that the analytic half of
Theorem A in `ZETA7_STATUS.md` uses: combined with `Hankel2.hasVolkenborn_binomPoly` it shows that
the Volkenborn integral loses at most `log_p (c+1)` on the `c`-th Mahler coefficient.
The Volkenborn Riemann sums only see the values of `f` at natural numbers, so the hypothesis
on `f` is stated there.
-/

namespace Hankel2

open Filter Finset Topology Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The Riemann sum of a binomial coefficient: `p^{-N} ∑_{t<p^N} C(t,c) = C(p^N-1,c)/(c+1)`. -/
lemma volkSum_choose (c N : ℕ) :
    ((p : ℚ_[p]) ^ N)⁻¹ * ∑ t ∈ range (p ^ N), ((t.choose c : ℕ) : ℚ_[p]) =
      (((p ^ N - 1).choose c : ℕ) : ℚ_[p]) / (c + 1) := by
  rw [← Nat.cast_sum, sum_range_choose_eq]
  have hpos : 1 ≤ p ^ N := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, p ^ N = m + 1 := ⟨p ^ N - 1, by omega⟩
  have hkey := Nat.add_one_mul_choose_eq m c
  have hcast : ((p : ℚ_[p]) ^ N) = ((m : ℚ_[p]) + 1) := by
    have := congrArg (fun k : ℕ => (k : ℚ_[p])) hm
    push_cast at this; exact this
  rw [hcast, hm, Nat.add_sub_cancel]
  have hkey' : ((m : ℚ_[p]) + 1) * (m.choose c : ℚ_[p]) =
      ((m + 1).choose (c + 1) : ℚ_[p]) * ((c : ℚ_[p]) + 1) := by
    exact_mod_cast hkey
  have hm1 : (m : ℚ_[p]) + 1 ≠ 0 := by
    rw [← hcast]; exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hc1 : (c : ℚ_[p]) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c
  field_simp
  linear_combination (-1 : ℚ_[p]) * hkey'

/-- `C(p^N - 1, c) → (-1)^c` `p`-adically. -/
lemma tendsto_choose_pow_sub_one (c : ℕ) :
    Tendsto (fun N : ℕ => (((p ^ N - 1).choose c : ℕ) : ℚ_[p])) atTop (𝓝 ((-1) ^ c)) := by
  have hlim : Tendsto (fun N : ℕ => (((p ^ N : ℕ) : ℚ_[p])) - 1) atTop (𝓝 (0 - 1)) :=
    (tendsto_p_pow_zero p).sub tendsto_const_nhds
  rw [zero_sub] at hlim
  have hcont := ((binomPoly p c).continuous.tendsto (-1)).comp hlim
  rw [binomPoly_eval_neg_one] at hcont
  refine hcont.congr fun N => ?_
  have hpos : 1 ≤ p ^ N := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  simp only [Function.comp]
  rw [← binomPoly_eval_nat]
  congr 1
  push_cast [hpos]
  ring

lemma norm_term_eq (a : ℕ → ℚ_[p]) (c : ℕ) :
    ‖a c * (-1) ^ c / (c + 1)‖ = ‖a c / (c + 1)‖ := by
  rw [mul_div_right_comm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]

/-- **Volkenborn integral of a Mahler series.**  If `f(t) = ∑_{c ≤ t} a_c C(t,c)` for every
natural `t` and `‖a_c/(c+1)‖ → 0`, then `∫_{ℤ_p} f = ∑_c a_c (-1)^c/(c+1)`. -/
theorem hasVolkenborn_mahler (a : ℕ → ℚ_[p]) (f : ℚ_[p] → ℚ_[p])
    (hf : ∀ t : ℕ, f t = ∑ c ∈ range (t + 1), a c * ((t.choose c : ℕ) : ℚ_[p]))
    (ha : Tendsto (fun c : ℕ => ‖a c / (c + 1)‖) atTop (𝓝 0)) :
    HasVolkenborn p f (∑' c, a c * (-1) ^ c / (c + 1)) := by
  set P : ℕ → ℕ := fun N => p ^ N with hP
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- the Riemann sums, rewritten through the Mahler expansion
  have hvs : ∀ N, volkSum p f N =
      ∑ c ∈ range (P N), a c * ((((P N - 1).choose c : ℕ) : ℚ_[p]) / (c + 1)) := by
    intro N
    unfold volkSum
    have hin : ∀ t ∈ range (P N), f t =
        ∑ c ∈ range (P N), a c * ((t.choose c : ℕ) : ℚ_[p]) := by
      intro t ht
      rw [hf t]
      apply Finset.sum_subset
      · intro c hc; simp only [mem_range] at hc ht ⊢; omega
      · intro c _ hc
        simp only [mem_range, not_lt] at hc
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [Finset.sum_congr rfl hin, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, volkSum_choose]
  set g : ℕ → ℚ_[p] := fun c => a c * (-1) ^ c / (c + 1) with hg
  have hgs : Summable g := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    simpa [hg, norm_term_eq] using ha
  have hPt : Tendsto P atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp1
  have hT : Tendsto (fun N => ∑ c ∈ range (P N), g c) atTop (𝓝 (∑' c, g c)) :=
    hgs.tendsto_sum_tsum_nat.comp hPt
  -- the difference of the two sums tends to zero
  set h : ℕ → ℕ → ℚ_[p] := fun c N =>
    a c / (c + 1) * ((((P N - 1).choose c : ℕ) : ℚ_[p]) - (-1) ^ c) with hh
  have hD : Tendsto (fun N => ∑ c ∈ range (P N), h c N) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨c0, hc0⟩ := eventually_atTop.1
      (ha.eventually (ge_mem_nhds (half_pos hε)))
    have hfin : Tendsto (fun N => ∑ c ∈ range c0, h c N) atTop (𝓝 0) := by
      have : Tendsto (fun N => ∑ c ∈ range c0, h c N) atTop
          (𝓝 (∑ c ∈ range c0, a c / (c + 1) * ((-1) ^ c - (-1) ^ c))) := by
        apply tendsto_finset_sum
        intro c _
        exact tendsto_const_nhds.mul ((tendsto_choose_pow_sub_one c).sub tendsto_const_nhds)
      simpa using this
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hfin (ε / 2) (half_pos hε)
    refine ⟨max N1 c0, fun N hN => ?_⟩
    have hc0P : c0 ≤ P N := by
      have := Nat.lt_pow_self hp1 (n := N)
      simp only [hP]; omega
    rw [dist_zero_right, ← Finset.sum_range_add_sum_Ico _ hc0P]
    have h1 : ‖∑ c ∈ range c0, h c N‖ < ε / 2 := by
      simpa [dist_zero_right] using hN1 N (le_of_max_le_left hN)
    have h2 : ‖∑ c ∈ Ico c0 (P N), h c N‖ ≤ ε / 2 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun c hc => ?_
      have hcc : c0 ≤ c := (Finset.mem_Ico.1 hc).1
      simp only [hh, norm_mul]
      have hb : ‖(((P N - 1).choose c : ℕ) : ℚ_[p]) - (-1) ^ c‖ ≤ 1 := by
        rw [sub_eq_add_neg]
        refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
        · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
        · simp
      calc ‖a c / (c + 1)‖ * ‖(((P N - 1).choose c : ℕ) : ℚ_[p]) - (-1) ^ c‖
          ≤ ‖a c / (c + 1)‖ * 1 := by gcongr
        _ ≤ ε / 2 := by rw [mul_one]; exact hc0 c hcc
    calc ‖∑ c ∈ range c0, h c N + ∑ c ∈ Ico c0 (P N), h c N‖
        ≤ max ‖∑ c ∈ range c0, h c N‖ ‖∑ c ∈ Ico c0 (P N), h c N‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ < ε := max_lt (by linarith) (by linarith)
  have hsum := hT.add hD
  rw [add_zero] at hsum
  unfold HasVolkenborn
  refine hsum.congr fun N => ?_
  rw [hvs N, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hg, hh]
  ring

/-- **Norm bound for the Volkenborn integral of a Mahler series**:
`‖∑_c a_c (-1)^c/(c+1)‖ ≤ B` whenever every `‖a_c/(c+1)‖ ≤ B`. -/
theorem norm_mahler_integral_le (a : ℕ → ℚ_[p]) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ c : ℕ, ‖a c / (c + 1)‖ ≤ B) :
    ‖∑' c, a c * (-1) ^ c / (c + 1)‖ ≤ B := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB fun c => ?_
  rw [norm_term_eq]
  exact h c

end Hankel2
