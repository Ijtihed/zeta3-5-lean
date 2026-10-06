import RequestProject.Zeta35.Mahler3

/-!
# Profiles of polynomials, products and Volkenborn integrals for `p = 3`

Port of `Hankel2.PolyProfile` from `ℚ₂` to `ℚ₃`: one derivative of a polynomial of degree `≤ D`
costs a factor `D` (`Prof.polyDeriv`), a polynomial that is `ℤ₃`-valued on `ℕ` has profile `1` up to
its degree (`prof_of_intValued33`), products with an admissible function have profile
`M · 3^{−(c−D)⁺}` (`Prof.polyW_mul_geo`), and integration costs `log₃(D+1)`
(`exists_hasVolkenborn_of_prof`).
-/

open Filter Finset Topology Polynomial

namespace Zeta35.M3

open Hankel2

local notation "Δ₃" => fwdDiff (1 : ℚ_[3])

/-! ### The derivative of a polynomial through finite differences -/

theorem natCast_three_pow_ne_zero (m : ℕ) : (((3 ^ m : ℕ) : ℚ_[3])) ≠ 0 := by
  exact_mod_cast (pow_pos (by norm_num : 0 < 3) m).ne'

/-- **`Q' = log(1 + Δ) Q`** for polynomials of degree `≤ D`. -/
theorem eval_derivative_eq_sum (Q : ℚ_[3][X]) {D : ℕ} (hQ : Q.natDegree ≤ D) (x : ℚ_[3]) :
    (derivative Q).eval x =
      ∑ i ∈ range D, ((-1) ^ i / ((i : ℚ_[3]) + 1)) * (Δ₃)^[i + 1] (fun y => Q.eval y) x := by
  set f : ℚ_[3] → ℚ_[3] := fun y => Q.eval y with hf
  -- Newton's formula, truncated at `D`
  have hN : ∀ N : ℕ, D ≤ N → f (x + N) =
      ∑ k ∈ range (D + 1), ((N.choose k : ℕ) : ℚ_[3]) * (Δ₃)^[k] f x := by
    intro N hND
    have h := shift_eq_sum_fwdDiff_iter (1 : ℚ_[3]) f N x
    rw [nsmul_eq_mul, mul_one] at h
    rw [h]
    have hsub : range (D + 1) ⊆ range (N + 1) := by
      intro k hk; simp only [mem_range] at hk ⊢; omega
    rw [← Finset.sum_subset hsub (fun k _ hk => by
      simp only [mem_range, not_lt] at hk
      rw [fwdDiff_iter_eq_zero_of_degree_lt (by omega : Q.natDegree < k)]
      simp)]
    exact Finset.sum_congr rfl fun k _ => by rw [nsmul_eq_mul]
  -- the slopes along `h = 3^m`
  set s : ℕ → ℚ_[3] := fun m => ((3 ^ m : ℕ) : ℚ_[3]) with hs
  have hslope : ∀ m : ℕ, D ≤ 3 ^ m → (s m)⁻¹ • (f (x + s m) - f x) =
      ∑ i ∈ range D, ((((3 ^ m - 1).choose i : ℕ) : ℚ_[3]) / ((i : ℚ_[3]) + 1)) *
        (Δ₃)^[i + 1] f x := by
    intro m hm
    rw [hs, hN _ hm, Finset.sum_range_succ', smul_eq_mul]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Function.iterate_zero, id_eq,
      add_sub_cancel_right]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpos : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hkey := Nat.add_one_mul_choose_eq (3 ^ m - 1) i
    rw [Nat.sub_add_cancel hpos] at hkey
    have hkey' : (((3 ^ m : ℕ) : ℚ_[3])) * (((3 ^ m - 1).choose i : ℕ) : ℚ_[3]) =
        (((3 ^ m).choose (i + 1) : ℕ) : ℚ_[3]) * ((i : ℚ_[3]) + 1) := by exact_mod_cast hkey
    have h2 := natCast_three_pow_ne_zero m
    have hi : (i : ℚ_[3]) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    field_simp
    linear_combination (Δ₃)^[i + 1] f x * hkey'.symm
  -- the limits
  have hs0 : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_p_pow_zero 3, Eventually.of_forall fun m => ?_⟩
    exact natCast_three_pow_ne_zero m
  have hL := ((Q.hasDerivAt x).tendsto_slope_zero).comp hs0
  have hR : Tendsto (fun m => ∑ i ∈ range D, ((((3 ^ m - 1).choose i : ℕ) : ℚ_[3]) /
      ((i : ℚ_[3]) + 1)) * (Δ₃)^[i + 1] f x) atTop
      (𝓝 (∑ i ∈ range D, ((-1) ^ i / ((i : ℚ_[3]) + 1)) * (Δ₃)^[i + 1] f x)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    exact ((tendsto_choose_pow_sub_one (p := 3) i).div_const _).mul_const _
  have hev : ∀ᶠ m in atTop, (s m)⁻¹ • (f (x + s m) - f x) =
      ∑ i ∈ range D, ((((3 ^ m - 1).choose i : ℕ) : ℚ_[3]) / ((i : ℚ_[3]) + 1)) *
        (Δ₃)^[i + 1] f x := by
    filter_upwards [eventually_ge_atTop D] with m hm
    exact hslope m (le_trans hm (Nat.lt_pow_self (by norm_num)).le)
  exact tendsto_nhds_unique (hL.congr' hev) hR

/-! ### Polynomial profiles -/

/-- The polynomial weight: `M` up to `D`, `0` beyond. -/
noncomputable def polyW (M : ℝ) (D j : ℕ) : ℝ := if j ≤ D then M else 0

theorem norm_inv_natCast_succ_le (i : ℕ) : ‖((i : ℚ_[3]) + 1)⁻¹‖ ≤ (i : ℝ) + 1 := by
  have h := inv_le_norm_natCast (p := 3) (N := i + 1) (Nat.succ_pos i)
  push_cast at h
  rw [norm_inv]
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hn : 0 < ‖(i : ℚ_[3]) + 1‖ := lt_of_lt_of_le (by positivity) h
  rw [inv_le_comm₀ hn hpos]
  exact h

/-- **One derivative costs a factor `D`.** -/
theorem Prof.polyDeriv {Q : ℚ_[3][X]} {D : ℕ} (hQ : Q.natDegree ≤ D) {M : ℝ} (hM : 0 ≤ M)
    (hp : Prof (polyW M D) fun y => Q.eval y) :
    Prof (polyW (M * D) D) fun y => (derivative Q).eval y := by
  intro x j
  have hfun : (fun y => (derivative Q).eval y) = ∑ i ∈ range D,
      ((-1) ^ i / ((i : ℚ_[3]) + 1)) • (Δ₃)^[i + 1] (fun y => Q.eval y) := by
    funext y; rw [eval_derivative_eq_sum Q hQ y, Finset.sum_apply]; rfl
  rw [hfun, fwdDiff_iter_finset_sum, Finset.sum_apply]
  have hMD : 0 ≤ M * D := mul_nonneg hM (Nat.cast_nonneg _)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (by unfold polyW; split_ifs <;> simp [hMD]) fun i hi => ?_
  rw [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul, ← Function.iterate_add_apply,
    norm_mul]
  have hc : ‖(-1 : ℚ_[3]) ^ i / ((i : ℚ_[3]) + 1)‖ ≤ D := by
    rw [div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine le_trans (norm_inv_natCast_succ_le i) ?_
    have := mem_range.1 hi
    exact_mod_cast this
  have hq := hp x (j + (i + 1))
  unfold polyW at hq ⊢
  split_ifs at hq ⊢ with h1 h2 h2
  · calc ‖(-1 : ℚ_[3]) ^ i / ((i : ℚ_[3]) + 1)‖ * ‖(Δ₃)^[j + (i + 1)] (fun y => Q.eval y) x‖
        ≤ D * M := mul_le_mul hc hq (norm_nonneg _) (Nat.cast_nonneg _)
      _ = M * D := mul_comm _ _
  · have : ‖(Δ₃)^[j + (i + 1)] (fun y => Q.eval y) (x : ℚ_[3])‖ = 0 :=
      le_antisymm hq (norm_nonneg _)
    rw [this, mul_zero]; exact hMD
  · omega
  · have : ‖(Δ₃)^[j + (i + 1)] (fun y => Q.eval y) (x : ℚ_[3])‖ = 0 :=
      le_antisymm hq (norm_nonneg _)
    rw [this, mul_zero]

theorem Prof.polyDeriv_iter {Q : ℚ_[3][X]} {D : ℕ} (hQ : Q.natDegree ≤ D) {M : ℝ} (hM : 0 ≤ M)
    (hp : Prof (polyW M D) fun y => Q.eval y) (a : ℕ) :
    Prof (polyW (M * D ^ a) D) fun y => (derivative^[a] Q).eval y := by
  induction a with
  | zero => simpa using hp
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    have hdeg : (derivative^[a] Q).natDegree ≤ D := by
      refine le_trans ?_ hQ
      clear ih
      induction a with
      | zero => simp
      | succ a iha => rw [Function.iterate_succ_apply']; exact natDegree_derivative_le _ |>.trans
                        (Nat.sub_le _ _) |>.trans iha
    have := ih.polyDeriv hdeg (by positivity)
    rwa [pow_succ, ← mul_assoc]

/-- An integer-valued (on `ℕ`) polynomial of degree `≤ D` has profile `1` up to `D`. -/
theorem prof_of_intValued3 {Q : ℚ_[3][X]} {D : ℕ} (hQ : Q.natDegree ≤ D)
    (hint : ∀ x : ℕ, ∃ m : ℤ, Q.eval (x : ℚ_[3]) = m) :
    Prof (polyW 1 D) fun y => Q.eval y := by
  intro x j
  unfold polyW
  split_ifs with hj
  · choose m hm using hint
    rw [fwdDiff_iter_eq_sum_shift]
    have e : ∑ k ∈ range (j + 1), (((-1 : ℤ) ^ (j - k) * (j.choose k : ℤ)) •
        Q.eval ((x : ℚ_[3]) + k • (1 : ℚ_[3]))) =
        ((∑ k ∈ range (j + 1), (-1 : ℤ) ^ (j - k) * (j.choose k : ℤ) * m (x + k) : ℤ) :
          ℚ_[3]) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [nsmul_eq_mul, mul_one, zsmul_eq_mul, ← hm (x + k)]
      push_cast; ring
    rw [e]
    exact Padic.norm_int_le_one _
  · rw [fwdDiff_iter_eq_zero_of_degree_lt (by omega : Q.natDegree < j)]
    simp

theorem Prof.const_mul {w : ℕ → ℝ} {f : ℚ_[3] → ℚ_[3]} (hf : Prof w f) (c : ℚ_[3]) :
    Prof (fun j => ‖c‖ * w j) fun y => c * f y := by
  intro x j
  have e : (fun y => c * f y) = c • f := rfl
  rw [e, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hf x j) (norm_nonneg _)

theorem polyW_mono {M M' : ℝ} (h : M ≤ M') (D j : ℕ) : polyW M D j ≤ polyW M' D j := by
  unfold polyW; split_ifs <;> simp [h]

/-- **Products**: a polynomial profile times a geometric profile. -/
theorem Prof.polyW_mul_geo {u v : ℚ_[3] → ℚ_[3]} {M : ℝ} {D : ℕ} (hM : 0 ≤ M)
    (hu : Prof (polyW M D) u) (hv : Prof geo v) :
    Prof (fun j => M * geo (j - D)) (u * v) := by
  refine hu.mul hv fun i k hk => ?_
  unfold polyW
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hM
    unfold geo
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  · rw [zero_mul]; exact mul_nonneg hM (geo_nonneg _)

/-! ### Integration -/

theorem succ_mul_geo_le (c D : ℕ) : ((c : ℝ) + 1) * geo (c - D) ≤ (D : ℝ) + 1 := by
  unfold geo
  rcases le_or_gt c D with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, mul_one]; exact_mod_cast Nat.succ_le_succ h
  · obtain ⟨m, rfl⟩ : ∃ m, c = D + m := ⟨c - D, by omega⟩
    rw [Nat.add_sub_cancel_left, inv_pow]
    have h2 : (0 : ℝ) < 3 ^ m := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ h2]
    have hm : (m : ℝ) + 1 ≤ 3 ^ m := by
      have := Nat.lt_pow_self (n := m) (a := 3) (by norm_num)
      exact_mod_cast this
    push_cast
    nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem tendsto_succ_mul_geo (D : ℕ) :
    Tendsto (fun c : ℕ => ((c : ℝ) + 1) * geo (c - D)) atTop (𝓝 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h3 := ((h1.add h2).const_mul ((3 : ℝ) ^ D))
  rw [add_zero, mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop D] with c hc
  unfold geo
  obtain ⟨m, rfl⟩ : ∃ m, c = D + m := ⟨c - D, by omega⟩
  rw [Nat.add_sub_cancel_left]
  simp only [inv_pow, pow_add]
  have : (3 : ℝ) ^ D ≠ 0 := by positivity
  field_simp

/-- **Integration**: a function with profile `M · 3^{−(c−D)⁺}` has a Volkenborn integral of
norm at most `M (D + 1)`. -/
theorem exists_hasVolkenborn_of_prof {h : ℚ_[3] → ℚ_[3]} {M : ℝ} {D : ℕ} (hM : 0 ≤ M)
    (hp : Prof (fun j => M * geo (j - D)) h) :
    ∃ I, HasVolkenborn 3 h I ∧ ‖I‖ ≤ M * ((D : ℝ) + 1) := by
  set a : ℕ → ℚ_[3] := fun c => (Δ₃)^[c] h 0 with ha
  have hf : ∀ t : ℕ, h t = ∑ c ∈ range (t + 1), a c * ((t.choose c : ℕ) : ℚ_[3]) := by
    intro t
    have := shift_eq_sum_fwdDiff_iter (1 : ℚ_[3]) h t 0
    rw [zero_add, nsmul_eq_mul, mul_one] at this
    rw [this]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [nsmul_eq_mul, mul_comm]
  have hbd : ∀ c : ℕ, ‖a c / ((c : ℚ_[3]) + 1)‖ ≤ M * (((c : ℝ) + 1) * geo (c - D)) := by
    intro c
    rw [div_eq_mul_inv, norm_mul]
    have h0 := hp 0 c
    simp only [Nat.cast_zero] at h0
    calc ‖a c‖ * ‖((c : ℚ_[3]) + 1)⁻¹‖ ≤ (M * geo (c - D)) * ((c : ℝ) + 1) :=
          mul_le_mul h0 (norm_inv_natCast_succ_le c) (norm_nonneg _)
            (mul_nonneg hM (geo_nonneg _))
      _ = M * (((c : ℝ) + 1) * geo (c - D)) := by ring
  have hlim : Tendsto (fun c : ℕ => ‖a c / ((c : ℚ_[3]) + 1)‖) atTop (𝓝 0) := by
    have := (tendsto_succ_mul_geo D).const_mul M
    rw [mul_zero] at this
    exact squeeze_zero (fun c => norm_nonneg _) hbd this
  refine ⟨_, hasVolkenborn_mahler a h hf hlim, ?_⟩
  refine norm_mahler_integral_le a (by positivity) fun c => ?_
  exact (hbd c).trans (mul_le_mul_of_nonneg_left (succ_mul_geo_le c D) hM)

end Zeta35.M3
