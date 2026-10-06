import RequestProject.Zeta7.Hankel2.ArchReduction
import RequestProject.Zeta7.Hankel2.LogPotCells

/-!
# Discrete comparisons for paper Lemma 6.4 (a), (b)

All the sums here run over the integer nodes; the continuum side is compared cell by cell in
`ContEnergy.lean`.  With `I`-cells `0 ≤ m < n` and `O`-cells `m ∈ [−n, 2n) \ [0, n)`:

* `log_abs_h_le` (Lemma 6.4 (a), upper half): for odd `n` and `−n ≤ k < 2n`,
  `ln|h_k| ≤ 2 ∑_{m ∈ I} ln(|k−m| − 1) − 4 ∑_{m ∈ O} ln(|k−m| + 1) + 60(1 + ln n)`;
* `Bk_le_log_sub_one` (for Lemma 6.4 (b)): `B(d) ≤ ln(|d| − 1) + 3/|d|` for integers `d`;
* `log_add_one_le_Bk`: `ln(|d| + 1) ≤ B(d) + 1/|d|`.

The comparisons are exact reindexings (shifts of the summation index away from `k` by `1` or
`2`, `sum_comp_le_of_injOn`) plus `O(1)` boundary terms, so the error is `O(log n)` per node.
-/

open Finset

namespace Hankel2.ArchB

open Fam3

/-! ### A reindexing inequality -/

theorem sum_comp_le_of_injOn {S T : Finset ℤ} (τ : ℤ → ℤ) (hτ : Set.InjOn τ S) (F : ℤ → ℝ)
    (hF : ∀ t ∈ T, 0 ≤ F t) :
    ∑ j ∈ S, F (τ j) ≤ ∑ t ∈ T, F t + ∑ j ∈ S.filter (fun j => τ j ∉ T), F (τ j) := by
  classical
  rw [← sum_filter_add_sum_filter_not S (fun j => τ j ∈ T)]
  suffices key : ∑ j ∈ S.filter (fun j => τ j ∈ T), F (τ j) ≤ ∑ t ∈ T, F t by linarith
  rw [← sum_image (s := S.filter (fun j => τ j ∈ T)) (g := τ) (f := F)
    (fun a ha b hb h => hτ (mem_filter.1 ha).1 (mem_filter.1 hb).1 h)]
  refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t ht _ => hF t ht)
  obtain ⟨j, hj, rfl⟩ := mem_image.1 ht
  exact (mem_filter.1 hj).2

theorem log_abs_sub_one_nonneg (d : ℤ) : 0 ≤ Real.log (|(d : ℝ)| - 1) := by
  by_cases h : |d| ≤ 1
  · rw [log_abs_sub_one_eq_zero h]
  · refine Real.log_nonneg ?_
    have : (2 : ℝ) ≤ |(d : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by have := not_le.mp h; linarith : 2 ≤ |d|)
    linarith

theorem log_abs_sub_one_le_add_one (d : ℤ) :
    Real.log (|(d : ℝ)| - 1) ≤ Real.log (|(d : ℝ)| + 1) := by
  by_cases h : |d| ≤ 1
  · rw [log_abs_sub_one_eq_zero h]; exact Real.log_nonneg (by linarith [abs_nonneg (d : ℝ)])
  · have : (2 : ℝ) ≤ |(d : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by have := not_le.mp h; linarith : 2 ≤ |d|)
    exact Real.log_le_log (by linarith) (by linarith)

/-! ### Kernel comparisons -/

theorem Bk_le_log_sub_one (d : ℤ) :
    Bk d ≤ Real.log (|(d : ℝ)| - 1) + 3 * (1 / |(d : ℝ)|) := by
  rcases eq_or_ne d 0 with rfl | h0
  · simp [Bk_zero]
  by_cases h1 : |d| ≤ 1
  · rw [log_abs_sub_one_eq_zero h1]
    have hd : |(d : ℝ)| = 1 := by
      have : |d| = 1 := by have := abs_pos.2 h0; omega
      rw [← Int.cast_abs, this]; simp
    rw [hd]
    unfold Bk
    have : Real.log (1 + (d : ℝ) ^ 2) = Real.log 2 := by
      congr 1; rw [← sq_abs, hd]; norm_num
    rw [this]; have := Real.log_two_lt_d9; norm_num; linarith
  · have h2 : (2 : ℝ) ≤ |(d : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by have := not_le.mp h1; linarith : 2 ≤ |d|)
    set a := |(d : ℝ)| with ha
    have hapos : 0 < a := by linarith
    -- `B(d) ≤ ln a + 1/(2a²)`
    have hB : Bk d ≤ Real.log a + 1 / (2 * a ^ 2) := by
      unfold Bk
      have e : 1 + (d : ℝ) ^ 2 = a ^ 2 * (1 + 1 / a ^ 2) := by
        rw [ha, sq_abs]; field_simp; ring
      rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / a ^ 2 by positivity)
      push_cast
      have : Real.log (1 + 1 / a ^ 2) ≤ 1 / a ^ 2 := by linarith
      have e2 : 1 / (2 * a ^ 2) = (1 / a ^ 2) / 2 := by field_simp
      rw [e2]; linarith
    -- `ln a ≤ ln(a − 1) + 2/a`
    have hL : Real.log a ≤ Real.log (a - 1) + 2 / a := by
      have hpos : 0 < a - 1 := by linarith
      have hne : a - 1 ≠ 0 := hpos.ne'
      have e : a = (a - 1) * (a / (a - 1)) := by field_simp
      conv_lhs => rw [e]
      rw [Real.log_mul hpos.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < a / (a - 1) by positivity)
      have h3 : a / (a - 1) - 1 ≤ 2 / a := by
        rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos hapos]; nlinarith
      linarith
    have h4 : 1 / (2 * a ^ 2) ≤ 1 / a := by
      rw [div_le_div_iff₀ (by positivity) hapos]; nlinarith
    have e5 : 3 * (1 / a) = 2 / a + 1 / a := by ring
    linarith

theorem log_add_one_le_Bk (d : ℤ) :
    Real.log (|(d : ℝ)| + 1) ≤ Bk d + 1 / |(d : ℝ)| := by
  rcases eq_or_ne d 0 with rfl | h0
  · simp [Bk_zero]
  · have hpos : 0 < |(d : ℝ)| := abs_pos.2 (by exact_mod_cast h0)
    have e : |(d : ℝ)| + 1 = |(d : ℝ)| * (1 + 1 / |(d : ℝ)|) := by field_simp
    rw [e, Real.log_mul hpos.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / |(d : ℝ)| by positivity)
    have := log_abs_le_Bk (d : ℝ)
    linarith

/-! ### `ln |h_k|` -/

/-- `h_k` as a real number. -/
noncomputable def hZ (n : ℕ) (k : ℤ) : ℝ := ((Hk n k 0 : ℚ) : ℝ)

theorem log_abs_hZ (hn : n % 2 = 1) (k : ℤ) :
    Real.log |hZ n k| = Real.log |((n : ℝ) - 2 * k)| +
      ∑ j ∈ range n, 6 * Real.log |((j : ℝ) + 1 / 2 - k)| -
      ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, 4 * Real.log |((k' : ℝ) - k)| := by
  have h1 : ((n : ℝ) - 2 * k) ≠ 0 := by
    have := lin_ne_zero hn k; exact_mod_cast this
  have hj : ∀ j ∈ range n, ((j : ℝ) + 1 / 2 - k) ≠ 0 := fun j _ => by
    intro h
    have h' : (((2 * (j : ℤ) + 1 - 2 * k : ℤ)) : ℝ) = 0 := by push_cast; linarith
    have : (2 * (j : ℤ) + 1 - 2 * k : ℤ) = 0 := by exact_mod_cast h'
    omega
  have hk' : ∀ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, ((k' : ℝ) - k) ≠ 0 := fun k' hk' => by
    have := sub_ne_zero.2 (ne_of_mem_erase hk'); exact_mod_cast this
  have e : hZ n k = ((n : ℝ) - 2 * k) * (∏ j ∈ range n, ((j : ℝ) + 1 / 2 - k) ^ 6) *
      ∏ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, (((k' : ℝ) - k)⁻¹) ^ 4 := by
    rw [hZ, Hk_zero_eq]; push_cast; rfl
  rw [e, abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod,
    Real.log_mul (mul_ne_zero (abs_ne_zero.2 h1) (prod_ne_zero_iff.2 fun j hj' => by
      rw [abs_ne_zero]; exact pow_ne_zero _ (hj j hj'))) (prod_ne_zero_iff.2 fun k' hk'' => by
      rw [abs_ne_zero]; exact pow_ne_zero _ (inv_ne_zero (hk' k' hk''))),
    Real.log_mul (abs_ne_zero.2 h1) (prod_ne_zero_iff.2 fun j hj' => by
      rw [abs_ne_zero]; exact pow_ne_zero _ (hj j hj')),
    Real.log_prod (fun j hj' => by rw [abs_ne_zero]; exact pow_ne_zero _ (hj j hj')),
    Real.log_prod (fun k' hk'' => by rw [abs_ne_zero]; exact pow_ne_zero _ (inv_ne_zero (hk' k' hk'')))]
  simp only [abs_pow, Real.log_pow, abs_inv, Real.log_inv]
  simp only [mul_neg, sum_neg_distrib]
  ring

/-! ### Lemma 6.4 (a): the upper bound for `ln |h_k|` -/

/-- The `O`-cells `[−n, 2n) \ [0, n)`. -/
def Oset (n : ℕ) : Finset ℤ := (Ico (-(n : ℤ)) (2 * n)).filter fun m => ¬ (0 ≤ m ∧ m < n)

/-- `A_k = ∑_{0 ≤ m < n} ln(|k − m| − 1)`. -/
noncomputable def Asum (n : ℕ) (k : ℤ) : ℝ := ∑ m ∈ Ico (0 : ℤ) n, Real.log (|((k - m : ℤ) : ℝ)| - 1)

/-- `O_k = ∑_{m ∈ O} ln(|k − m| + 1)`. -/
noncomputable def Osum (n : ℕ) (k : ℤ) : ℝ := ∑ m ∈ Oset n, Real.log (|((k - m : ℤ) : ℝ)| + 1)

theorem card_le_four_of_subset {s : Finset ℤ} {a b c d : ℤ} (h : s ⊆ {a, b, c, d}) :
    s.card ≤ 4 := by
  refine (card_le_card h).trans ?_
  refine (card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
  simp

theorem sum_le_card_mul {s : Finset ℤ} {g : ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hg : ∀ j ∈ s, g j ≤ B)
    {N : ℕ} (hs : s.card ≤ N) : ∑ j ∈ s, g j ≤ N * B := by
  calc ∑ j ∈ s, g j ≤ ∑ _j ∈ s, B := sum_le_sum hg
    _ = s.card * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ N * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hB

theorem log_dist_add_one_le {n : ℕ} (hn : 0 < n) {k m : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n))
    (hm : m ∈ Icc (-(n : ℤ)) (2 * n)) : Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤ Real.log (4 * n) := by
  simp only [mem_Ico, mem_Icc] at hk hm
  refine Real.log_le_log (by positivity) ?_
  have : |k - m| ≤ 3 * n := by rw [abs_le]; omega
  have h' : ((|k - m| : ℤ) : ℝ) ≤ ((3 * n : ℤ) : ℝ) := by exact_mod_cast this
  rw [Int.cast_abs] at h'
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h' ⊢; linarith

/-- The half-integer product: `∑_{j<n} ln|j + ½ − k| ≤ A_k + 4 ln(4n)`. -/
theorem half_sum_le {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    ∑ j ∈ range n, Real.log |((j : ℝ) + 1 / 2 - k)| ≤ Asum n k + 4 * Real.log (4 * n) := by
  -- termwise
  have h1 : ∑ j ∈ range n, Real.log |((j : ℝ) + 1 / 2 - k)| ≤
      ∑ m ∈ Ico (0 : ℤ) n, Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
    have e : ∑ m ∈ Ico (0 : ℤ) n, Real.log (|((k - m : ℤ) : ℝ)| + 1) =
        ∑ j ∈ range n, Real.log (|((k - (j : ℤ) : ℤ) : ℝ)| + 1) := by
      refine sum_bij (fun m _ => m.toNat) ?_ ?_ ?_ ?_
      · intro m hm; simp only [mem_Ico] at hm; simp only [mem_range]; omega
      · intro a ha b hb h; simp only at h; simp only [mem_Ico] at ha hb; omega
      · intro j hj; simp only [mem_range] at hj
        exact ⟨j, by simp only [mem_Ico]; omega, by simp⟩
      · intro m hm; simp only [mem_Ico] at hm
        rw [Int.toNat_of_nonneg hm.1]
    rw [e]
    refine sum_le_sum fun j _ => ?_
    have hpos : 0 < |((j : ℝ) + 1 / 2 - k)| := by
      refine abs_pos.2 fun h => ?_
      have h' : (((2 * (j : ℤ) + 1 - 2 * k : ℤ)) : ℝ) = 0 := by push_cast; linarith
      have : (2 * (j : ℤ) + 1 - 2 * k : ℤ) = 0 := by exact_mod_cast h'
      omega
    refine Real.log_le_log hpos ?_
    have e2 : ((j : ℝ) + 1 / 2 - k) = -(((k - (j : ℤ) : ℤ) : ℝ)) + 1 / 2 := by push_cast; ring
    rw [e2]
    have := abs_add_le (-(((k - (j : ℤ) : ℤ) : ℝ))) (1 / 2)
    rw [abs_neg] at this
    have : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith
  -- the shift `j ↦ j ± 2`
  set τ : ℤ → ℤ := fun j => if k ≤ j then j + 2 else j - 2 with hτ
  have hinj : Set.InjOn τ (Ico (0 : ℤ) n) := by
    intro a _ b _ h
    simp only [hτ] at h
    split_ifs at h <;> omega
  have hF : ∀ t ∈ Ico (0 : ℤ) n, 0 ≤ Real.log (|((k - t : ℤ) : ℝ)| - 1) :=
    fun t _ => log_abs_sub_one_nonneg _
  have hsh := sum_comp_le_of_injOn τ hinj (fun t => Real.log (|((k - t : ℤ) : ℝ)| - 1)) hF
  have hval : ∀ j, Real.log (|((k - τ j : ℤ) : ℝ)| - 1) = Real.log (|((k - j : ℤ) : ℝ)| + 1) := by
    intro j
    congr 1
    have : |k - τ j| = |k - j| + 2 := by
      simp only [hτ]; split_ifs with h
      · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; ring
      · rw [abs_of_pos (by omega), abs_of_pos (by omega)]; ring
    have h' : ((|k - τ j| : ℤ) : ℝ) = ((|k - j| + 2 : ℤ) : ℝ) := by rw [this]
    rw [Int.cast_abs, Int.cast_add, Int.cast_abs] at h'
    rw [h']; push_cast; ring
  simp only [hval] at hsh
  have hout : ∑ j ∈ (Ico (0 : ℤ) n).filter (fun j => τ j ∉ Ico (0 : ℤ) n),
      Real.log (|((k - j : ℤ) : ℝ)| + 1) ≤ 4 * Real.log (4 * n) := by
    refine sum_le_card_mul (B := Real.log (4 * n)) (Real.log_nonneg (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)) (fun j hj => ?_) ?_
    · simp only [mem_filter, mem_Ico] at hj
      exact log_dist_add_one_le hn hk (by simp only [mem_Icc]; omega)
    · refine card_le_four_of_subset (a := 0) (b := 1) (c := (n : ℤ) - 2) (d := (n : ℤ) - 1) ?_
      intro j hj
      simp only [mem_filter, mem_Ico, hτ] at hj
      simp only [mem_insert, mem_singleton]
      split_ifs at hj <;> omega
  unfold Asum
  linarith

/-- The integer product: `∑_{k' ≠ k} ln|k' − k| ≥ ∑_{m ∈ [−n,2n)} ln(|k − m| + 1) − ln(4n)`. -/
theorem int_sum_ge {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) - Real.log (4 * n) ≤
      ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, Real.log |((k' : ℝ) - k)| := by
  set τ : ℤ → ℤ := fun m => if k ≤ m then m + 1 else m - 1 with hτ
  have hinj : Set.InjOn τ (Ico (-(n : ℤ)) (2 * n)) := by
    intro a _ b _ h
    simp only [hτ] at h
    split_ifs at h <;> omega
  have hF : ∀ t ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, 0 ≤ Real.log |((k - t : ℤ) : ℝ)| := by
    intro t ht
    have hne : k - t ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_of_mem_erase ht))
    refine Real.log_nonneg ?_
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
  have hsh := sum_comp_le_of_injOn τ hinj (fun t => Real.log |((k - t : ℤ) : ℝ)|) hF
  have hval : ∀ m, Real.log |((k - τ m : ℤ) : ℝ)| = Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
    intro m
    congr 1
    have : |k - τ m| = |k - m| + 1 := by
      simp only [hτ]; split_ifs with h
      · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; ring
      · rw [abs_of_pos (by omega), abs_of_pos (by omega)]; ring
    have h' : ((|k - τ m| : ℤ) : ℝ) = ((|k - m| + 1 : ℤ) : ℝ) := by rw [this]
    rw [Int.cast_abs, Int.cast_add, Int.cast_abs] at h'
    rw [h']; push_cast; ring
  simp only [hval] at hsh
  have hout : ∑ m ∈ (Ico (-(n : ℤ)) (2 * n)).filter (fun m => τ m ∉ (Icc (-(n : ℤ)) (2 * n)).erase k),
      Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤ ((1 : ℕ) : ℝ) * Real.log (4 * n) := by
    refine sum_le_card_mul (B := Real.log (4 * n)) (Real.log_nonneg (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)) (fun j hj => ?_) ?_
    · simp only [mem_filter, mem_Ico] at hj
      exact log_dist_add_one_le hn hk (by simp only [mem_Icc]; omega)
    · refine (card_le_card (t := {-(n : ℤ)}) fun m hm => ?_).trans (by simp)
      rw [mem_filter] at hm
      obtain ⟨hm1, hm2⟩ := hm
      simp only [mem_Ico] at hm1 hk
      simp only [mem_singleton]
      by_contra hne
      apply hm2
      rw [mem_erase, mem_Icc]
      simp only [hτ]
      split_ifs <;> refine ⟨by omega, by omega, by omega⟩
  have hsym : ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, Real.log |((k' : ℝ) - k)| =
      ∑ t ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, Real.log |((k - t : ℤ) : ℝ)| := by
    refine sum_congr rfl fun t _ => ?_
    push_cast; rw [abs_sub_comm]
  rw [hsym]
  simp only [Nat.cast_one, one_mul] at hout
  linarith

/-- **Lemma 6.4 (a), discrete half**: `ln|h_k| ≤ 2A_k − 4O_k + 60(1 + ln n)`. -/
theorem log_abs_h_le {n : ℕ} (hn : n % 2 = 1) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    Real.log |hZ n k| ≤ 2 * Asum n k - 4 * Osum n k + 60 * (1 + Real.log n) := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  rw [log_abs_hZ hn k]
  have hH := half_sum_le hn0 hk
  have hI := int_sum_ge hn0 hk
  -- the linear factor
  have hlin : Real.log |((n : ℝ) - 2 * k)| ≤ Real.log (5 * n) := by
    have hne : ((n : ℝ) - 2 * k) ≠ 0 := by have := lin_ne_zero hn k; exact_mod_cast this
    refine Real.log_le_log (abs_pos.2 hne) ?_
    simp only [mem_Ico] at hk
    have : |(n : ℤ) - 2 * k| ≤ 5 * n := by rw [abs_le]; omega
    have h' : ((|(n : ℤ) - 2 * k| : ℤ) : ℝ) ≤ ((5 * n : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at h'; push_cast at h'; exact h'
  -- split `[−n, 2n)` into `I` and `O`
  have hsplit : Asum n k + Osum n k ≤
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
    rw [← sum_filter_add_sum_filter_not (Ico (-(n : ℤ)) (2 * n)) (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ))]
    have hI' : (Ico (-(n : ℤ)) (2 * n)).filter (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ)) = Ico (0 : ℤ) n := by
      ext m; simp only [mem_filter, mem_Ico]; omega
    rw [hI']
    unfold Asum Osum Oset
    have := sum_le_sum fun m (_ : m ∈ Ico (0 : ℤ) n) => log_abs_sub_one_le_add_one (k - m)
    linarith
  have e1 : ∑ j ∈ range n, 6 * Real.log |((j : ℝ) + 1 / 2 - k)| =
      6 * ∑ j ∈ range n, Real.log |((j : ℝ) + 1 / 2 - k)| := by rw [mul_sum]
  have e2 : ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, 4 * Real.log |((k' : ℝ) - k)| =
      4 * ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, Real.log |((k' : ℝ) - k)| := by rw [mul_sum]
  rw [e1, e2]
  -- constants
  have hl4 : Real.log (4 * n) ≤ 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 4 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / Real.exp 1 by positivity)
      rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
      have he := Real.exp_one_gt_d9
      have : 4 / Real.exp 1 ≤ 4 / 2.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith)
      linarith
    linarith
  have hl5 : Real.log (5 * n) ≤ 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 5 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / Real.exp 1 by positivity)
      rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
      have he := Real.exp_one_gt_d9
      have : 5 / Real.exp 1 ≤ 5 / 2.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith)
      linarith
    linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  nlinarith

end Hankel2.ArchB
