import RequestProject.Zeta7.Hankel2.ContDiscrete

/-!
# Paper Lemma 6.4 (continuum limit): the per-node bounds

For odd `n`, a feasible `σ` (`0 ≤ σ ≤ 4`, `∫ σ = K/n`) and a node `k` with `−n ≤ k < 2n`:

* `n2_int_Pgrad_ge` (Lemma 6.4 (a)+(b), lower bound for the gradient on the cell `J_k`):
  `n² ∫_{J_k} P_σ ≥ 6n ln n − 2K ln n + 2A_k − 4O_k + 2W_k − 180`, where
  `W_k = ∑_m cav_m(σ) ln(|k−m| − 1)`;
* `g_le` : `ln|h_k| + 2 (B s̃)_k ≤ n² ∫_{J_k} P_σ + (2K − 6n) ln n + 400 (1 + ln n)`,
  with `s̃_m = cav_m(σ) = n ∫_{J_m} σ` (and `s̃_{2n} = 0`).

The error is `O(log n)` per node, uniformly in `k`, `K` and `σ`.
-/

open MeasureTheory Finset

namespace Hankel2.ArchB

open Fam3

/-! ### Integrability on `[−1, 2]` -/

theorem ii_of_bdd_on {g : ℝ → ℝ} {C : ℝ} (hg : Measurable g)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |g x| ≤ C) {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b)
    (hb2 : b ≤ 2) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact hb x ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem integral_split_cells' {g : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hg : ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 2 → IntervalIntegrable g volume a b) :
    ∫ y in (-1 : ℝ)..2, g y =
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), g y := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun i : ℕ => ((i : ℝ) - n) / n) (n := 3 * n) (fun k hk => by
      refine hg _ _ ?_ ?_ ?_
      · rw [le_div_iff₀ hn']; have : (0 : ℝ) ≤ k := by positivity
        linarith
      · exact div_le_div_of_nonneg_right (by push_cast; linarith) hn'.le
      · rw [div_le_iff₀ hn']
        have : ((k + 1 : ℕ) : ℝ) ≤ 3 * n := by exact_mod_cast hk
        linarith)
  simp only at h
  have e0 : (((0 : ℕ) : ℝ) - n) / n = -1 := by field_simp; simp
  have e1 : ((((3 * n : ℕ)) : ℝ) - n) / n = 2 := by push_cast; field_simp; ring
  rw [e0, e1] at h
  rw [← h]
  refine sum_bij (fun i _ => (i : ℤ) - n) ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_range] at hi; simp only [mem_Ico]; omega
  · intro i _ j _ hij; simp only at hij; omega
  · intro m hm
    simp only [mem_Ico] at hm
    refine ⟨(m + n).toNat, by simp only [mem_range]; omega, ?_⟩
    show (((m + n).toNat : ℕ) : ℤ) - n = m
    omega
  · intro i _
    have e : ((((i : ℤ) - n : ℤ)) : ℝ) = (i : ℝ) - n := by push_cast; ring
    rw [e]
    congr 1
    push_cast; ring

theorem cell_sub {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    -1 ≤ (k : ℝ) / n ∧ ((k : ℝ) + 1) / n ≤ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mem_Ico] at hk
  have h1 : ((-(n : ℤ) : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
  have h2 : ((k + 1 : ℤ) : ℝ) ≤ ((2 * n : ℤ) : ℝ) := by exact_mod_cast hk.2
  push_cast at h1 h2
  constructor
  · rw [le_div_iff₀ hn']; linarith
  · rw [div_le_iff₀ hn']; linarith

/-! ### The indicator functions -/

theorem measurable_indI : Measurable indI :=
  (measurable_const.indicator measurableSet_Ioo)

theorem measurable_indO : Measurable indO :=
  (measurable_const.indicator (measurableSet_Icc.union measurableSet_Icc))

theorem indI_bounds (y : ℝ) : 0 ≤ indI y ∧ indI y ≤ 1 := by
  unfold indI; by_cases h : y ∈ Set.Ioo (0 : ℝ) 1 <;> simp [h]

theorem indO_bounds (y : ℝ) : 0 ≤ indO y ∧ indO y ≤ 1 := by
  unfold indO; by_cases h : y ∈ Set.Icc (-1 : ℝ) 0 ∪ Set.Icc 1 2 <;> simp [h]

theorem cav_indI {n : ℕ} (hn : 0 < n) (m : ℤ) :
    cav indI n m = if 0 ≤ m ∧ m < n then 1 else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cav
  split_ifs with h
  · have : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), indI y =
        ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume 1] with y hy1 hy
      rw [Set.uIoc_of_le (cell_le hn m)] at hy
      obtain ⟨hy2, hy3⟩ := hy
      have h0 : (0 : ℝ) ≤ m := by exact_mod_cast h.1
      have h1 : ((m + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      push_cast at h1
      unfold indI
      rw [Set.indicator_of_mem]
      · rfl
      · constructor
        · exact lt_of_le_of_lt (div_nonneg h0 hn'.le) hy2
        · have : y ≤ 1 := hy3.trans (by rw [div_le_one hn']; linarith)
          exact lt_of_le_of_ne this hy1
    rw [this, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    field_simp; ring
  · have : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), indI y =
        ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun y hy => ?_)
      rw [Set.uIoc_of_le (cell_le hn m)] at hy
      obtain ⟨hy2, hy3⟩ := hy
      unfold indI
      rw [Set.indicator_of_notMem]
      rintro ⟨hy4, hy5⟩
      rcases not_and_or.1 h with h' | h'
      · have : ((m + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (show m + 1 ≤ 0 by omega)
        push_cast at this
        have : y ≤ 0 := hy3.trans (div_nonpos_of_nonpos_of_nonneg this hn'.le)
        linarith
      · have : (n : ℝ) ≤ m := by exact_mod_cast (show (n : ℤ) ≤ m by omega)
        have : 1 ≤ (m : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
        linarith
    rw [this]; simp

theorem cav_indO {n : ℕ} (hn : 0 < n) {m : ℤ} (hm : m ∈ Ico (-(n : ℤ)) (2 * n)) :
    cav indO n m = if 0 ≤ m ∧ m < n then 0 else 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mem_Ico] at hm
  unfold cav
  split_ifs with h
  · have : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), indO y =
        ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume 1] with y hy1 hy
      rw [Set.uIoc_of_le (cell_le hn m)] at hy
      obtain ⟨hy2, hy3⟩ := hy
      have h0 : (0 : ℝ) ≤ m := by exact_mod_cast h.1
      have h1 : ((m + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      push_cast at h1
      have hy0 : 0 < y := lt_of_le_of_lt (div_nonneg h0 hn'.le) hy2
      have hyl : y < 1 := lt_of_le_of_ne (hy3.trans (by rw [div_le_one hn']; linarith)) hy1
      unfold indO
      rw [Set.indicator_of_notMem]
      rintro (⟨_, h5⟩ | ⟨h4, _⟩) <;> linarith
    rw [this]; simp
  · have : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), indO y =
        ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun y hy => ?_)
      rw [Set.uIoc_of_le (cell_le hn m)] at hy
      obtain ⟨hy2, hy3⟩ := hy
      unfold indO
      rw [Set.indicator_of_mem]
      · rfl
      rcases not_and_or.1 h with h' | h'
      · left
        have h1 : ((-(n : ℤ) : ℤ) : ℝ) ≤ m := by exact_mod_cast hm.1
        have h2 : ((m + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (show m + 1 ≤ 0 by omega)
        push_cast at h1 h2
        constructor
        · have : -1 ≤ (m : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
          linarith
        · exact hy3.trans (div_nonpos_of_nonpos_of_nonneg h2 hn'.le)
      · right
        have h1 : (n : ℝ) ≤ m := by exact_mod_cast (show (n : ℤ) ≤ m by omega)
        have h2 : ((m + 1 : ℤ) : ℝ) ≤ ((2 * n : ℤ) : ℝ) := by exact_mod_cast (show m + 1 ≤ 2 * n by omega)
        push_cast at h2
        constructor
        · have : 1 ≤ (m : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
          linarith
        · exact hy3.trans (by rw [div_le_iff₀ hn']; linarith)
    rw [this, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    field_simp; ring

/-! ### The gradient `P_σ` -/

theorem measurable_Pgrad {σ : ℝ → ℝ} (hσm : Measurable σ) : Measurable (Pgrad σ) := by
  unfold Pgrad
  exact (((measurable_logPot measurable_indI).const_mul 2).sub
    ((measurable_logPot measurable_indO).const_mul 4)).add
    ((measurable_logPot hσm).const_mul 2)

theorem abs_Pgrad_le {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |Pgrad σ x| ≤ 252 := by
  have h1 := abs_logPot_le measurable_indI (fun y => (indI_bounds y).1) (fun y => (indI_bounds y).2) hx
  have h2 := abs_logPot_le measurable_indO (fun y => (indO_bounds y).1) (fun y => (indO_bounds y).2) hx
  have h3 := abs_logPot_le hσm (fun y => (hσ y).1) (fun y => (hσ y).2) hx
  unfold Pgrad
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `W_k = ∑_m cav_m(σ) ln(|k − m| − 1)`. -/
noncomputable def Wsum (n : ℕ) (σ : ℝ → ℝ) (k : ℤ) : ℝ :=
  ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| - 1)

theorem filter_I_eq (n : ℕ) :
    (Ico (-(n : ℤ)) (2 * n)).filter (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ)) = Ico (0 : ℤ) n := by
  ext m; simp only [mem_filter, mem_Ico]; omega

theorem sum_cav_indI_log {n : ℕ} (hn : 0 < n) (k : ℤ) :
    ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav indI n m * Real.log (|((k - m : ℤ) : ℝ)| - 1) =
      Asum n k := by
  simp_rw [cav_indI hn, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, filter_I_eq]; rfl

theorem sum_cav_indO_log {n : ℕ} (hn : 0 < n) (k : ℤ) :
    ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav indO n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) =
      Osum n k := by
  rw [sum_congr rfl fun m hm => by rw [cav_indO hn hm]]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [sum_ite, sum_const_zero, zero_add]; rfl

theorem n_int_indI {n : ℕ} (hn : 0 < n) : (n : ℝ) * ∫ y in (-1 : ℝ)..2, indI y = n := by
  rw [← sum_cav measurable_indI (M := 1) (fun y => by
    rw [abs_of_nonneg (indI_bounds y).1]; exact (indI_bounds y).2) hn]
  simp_rw [cav_indI hn]
  rw [← sum_filter_add_sum_filter_not _ (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ))]
  rw [sum_congr rfl fun m hm => if_pos (mem_filter.1 hm).2,
    sum_congr rfl fun m hm => if_neg (mem_filter.1 hm).2, sum_const_zero, add_zero, sum_const,
    filter_I_eq, Int.card_Ico, nsmul_eq_mul, mul_one]
  simp

theorem n_int_indO {n : ℕ} (hn : 0 < n) : (n : ℝ) * ∫ y in (-1 : ℝ)..2, indO y = 2 * n := by
  rw [← sum_cav measurable_indO (M := 1) (fun y => by
    rw [abs_of_nonneg (indO_bounds y).1]; exact (indO_bounds y).2) hn]
  rw [sum_congr rfl fun m hm => by rw [cav_indO hn hm]]
  rw [← sum_filter_add_sum_filter_not _ (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ))]
  rw [sum_congr rfl fun m hm => if_pos (mem_filter.1 hm).2,
    sum_congr rfl fun m hm => if_neg (mem_filter.1 hm).2, sum_const_zero, zero_add, sum_const,
    nsmul_eq_mul, mul_one]
  have h := card_filter_add_card_filter_not (s := Ico (-(n : ℤ)) (2 * n))
    (fun m : ℤ => 0 ≤ m ∧ m < (n : ℤ))
  rw [filter_I_eq, Int.card_Ico, Int.card_Ico] at h
  have : ((Ico (-(n : ℤ)) (2 * n)).filter (fun m : ℤ => ¬ (0 ≤ m ∧ m < (n : ℤ)))).card = 2 * n := by
    omega
  rw [this]; push_cast; ring

/-- **Pointwise lower bound for `n P_σ` on the cell `J_k`.** -/
theorem n_Pgrad_ge {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, σ y = K) {k : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    6 * n * Real.log n - 2 * K * Real.log n + 2 * Asum n k - 4 * Osum n k + 2 * Wsum n σ k - 180
      ≤ n * Pgrad σ x := by
  have hI := logPot_lower measurable_indI (fun y => (indI_bounds y).1) (fun y => (indI_bounds y).2)
    (fun y => by rw [abs_of_nonneg (indI_bounds y).1]; exact (indI_bounds y).2) hn hx
  have hO := logPot_upper measurable_indO (fun y => (indO_bounds y).1)
    (fun y => by rw [abs_of_nonneg (indO_bounds y).1]; exact (indO_bounds y).2) hn hx
  have hS := logPot_lower hσm (fun y => (hσ y).1) (fun y => (hσ y).2)
    (fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2) hn hx
  rw [n_int_indI hn, sum_cav_indI_log hn] at hI
  rw [n_int_indO hn, sum_cav_indO_log hn] at hO
  rw [hmass] at hS
  unfold Pgrad
  have e : (n : ℝ) * (2 * logPot indI x - 4 * logPot indO x + 2 * logPot σ x) =
      2 * (n * logPot indI x) - 4 * (n * logPot indO x) + 2 * (n * logPot σ x) := by ring
  rw [e]
  unfold Wsum
  linarith

/-- **Integrated lower bound**: `n² ∫_{J_k} P_σ ≥ …`. -/
theorem n2_int_Pgrad_ge {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, σ y = K) {k : ℤ}
    (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    6 * n * Real.log n - 2 * K * Real.log n + 2 * Asum n k - 4 * Osum n k + 2 * Wsum n σ k - 180
      ≤ (n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Pgrad σ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hk1, hk2⟩ := cell_sub hn hk
  set L := 6 * n * Real.log n - 2 * K * Real.log n + 2 * Asum n k - 4 * Osum n k +
    2 * Wsum n σ k - 180
  have hint : IntervalIntegrable (Pgrad σ) volume ((k : ℝ) / n) (((k : ℝ) + 1) / n) :=
    ii_of_bdd_on (measurable_Pgrad hσm) (fun x hx => abs_Pgrad_le hσm hσ hx) hk1 (cell_le hn k) hk2
  have h := intervalIntegral.integral_mono_on (cell_le hn k) intervalIntegrable_const
    (hint.const_mul (n : ℝ)) (fun x hx => n_Pgrad_ge (K := K) hn hσm hσ hmass hx)
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at h
  have e : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by field_simp; ring
  rw [e] at h
  have : L = (n : ℝ) * (1 / n * L) := by field_simp
  rw [this, sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hn'.le

/-! ### The discrete profile `s̃` and the gradient `g_k = ln|h_k| + 2 (B s̃)_k` -/

/-- `s̃_m = cav_m(σ) = n ∫_{J_m} σ` for `m < 2n`, `s̃_{2n} = 0`. -/
noncomputable def wZ (n : ℕ) (σ : ℝ → ℝ) (m : ℤ) : ℝ := if m < 2 * n then cav σ n m else 0

/-- `(B s̃)_k = ∑_m B(k − m) s̃_m`. -/
noncomputable def BwZ (n : ℕ) (σ : ℝ → ℝ) (k : ℤ) : ℝ :=
  ∑ m ∈ Fam3PF.nodes n, Bk ((k - m : ℤ) : ℝ) * wZ n σ m

theorem filter_Ico_eq (n : ℕ) : (Fam3PF.nodes n).filter (fun m : ℤ => m < 2 * n) =
    Ico (-(n : ℤ)) (2 * n) := by
  ext m; simp only [Fam3PF.nodes, mem_filter, mem_Icc, mem_Ico]; omega

theorem sum_nodes_wZ (n : ℕ) (σ : ℝ → ℝ) (F : ℤ → ℝ) :
    ∑ m ∈ Fam3PF.nodes n, wZ n σ m * F m = ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n m * F m := by
  simp only [wZ, ite_mul, zero_mul]
  rw [← sum_filter, filter_Ico_eq]

theorem wZ_nonneg {n : ℕ} (hn : 0 < n) {σ : ℝ → ℝ} (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (m : ℤ) :
    0 ≤ wZ n σ m := by
  unfold wZ; split_ifs
  · exact cav_nonneg (fun y => (hσ y).1) hn m
  · exact le_rfl

theorem wZ_le {n : ℕ} (hn : 0 < n) {σ : ℝ → ℝ} (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (m : ℤ) : wZ n σ m ≤ 4 := by
  unfold wZ; split_ifs
  · exact cav_le hσm (fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2) (fun y => (hσ y).2) hn m
  · norm_num

theorem sum_wZ {n : ℕ} (hn : 0 < n) {σ : ℝ → ℝ} (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) :
    ∑ m ∈ Fam3PF.nodes n, wZ n σ m = n * ∫ y in (-1 : ℝ)..2, σ y := by
  have := sum_nodes_wZ n σ (fun _ => 1)
  simp only [mul_one] at this
  rw [this, sum_cav hσm (fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2) hn]

theorem sum_nodes_inv_le {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    ∑ m ∈ Fam3PF.nodes n, 1 / |((k - m : ℤ) : ℝ)| ≤ 2 * (1 + Real.log (3 * n)) := by
  rw [← add_sum_erase _ _ hk]
  simp only [sub_self, Int.cast_zero, abs_zero, div_zero, zero_add]
  exact LemmaB.sum_inv_dist_le n k hk

theorem log_three_mul_le {n : ℕ} (hn : 0 < n) : Real.log (3 * n) ≤ 2 + Real.log n := by
  rw [Real.log_mul (by norm_num) (by positivity)]
  have : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  linarith

theorem BwZ_le {n : ℕ} (hn : 0 < n) {σ : ℝ → ℝ} (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    BwZ n σ k ≤ Wsum n σ k + 24 * (1 + Real.log (3 * n)) := by
  unfold BwZ
  have h1 : ∑ m ∈ Fam3PF.nodes n, Bk ((k - m : ℤ) : ℝ) * wZ n σ m ≤
      ∑ m ∈ Fam3PF.nodes n, wZ n σ m * Real.log (|((k - m : ℤ) : ℝ)| - 1) +
        ∑ m ∈ Fam3PF.nodes n, 12 * (1 / |((k - m : ℤ) : ℝ)|) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun m _ => ?_
    have hB := Bk_le_log_sub_one (k - m)
    have hw0 := wZ_nonneg hn hσ m
    have hw4 := wZ_le hn hσm hσ m
    have hinv : 0 ≤ 1 / |((k - m : ℤ) : ℝ)| := by positivity
    have : Bk ((k - m : ℤ) : ℝ) * wZ n σ m ≤
        (Real.log (|((k - m : ℤ) : ℝ)| - 1) + 3 * (1 / |((k - m : ℤ) : ℝ)|)) * wZ n σ m :=
      mul_le_mul_of_nonneg_right hB hw0
    nlinarith
  have h2 := sum_nodes_inv_le hk
  rw [sum_nodes_wZ] at h1
  rw [← mul_sum] at h1
  unfold Wsum
  linarith

/-- **The gradient at a cell node**: `g_k ≤ n² ∫_{J_k} P_σ + (2K − 6n) ln n + 400(1 + ln n)`. -/
theorem g_le {σ : ℝ → ℝ} {n K : ℕ} (hn : n % 2 = 1) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, σ y = K) {k : ℤ}
    (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    Real.log |hZ n k| + 2 * BwZ n σ k ≤
      (n : ℝ) ^ 2 * (∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Pgrad σ x) +
        (2 * K - 6 * n) * Real.log n + 400 * (1 + Real.log n) := by
  have hn0 : 0 < n := by omega
  have hkn : k ∈ Fam3PF.nodes n := by
    simp only [mem_Ico] at hk; simp only [Fam3PF.nodes, mem_Icc]; omega
  have h1 := log_abs_h_le hn hk
  have h2 := BwZ_le hn0 hσm hσ hkn
  have h3 := n2_int_Pgrad_ge (K := K) hn0 hσm hσ hmass hk
  have h4 := log_three_mul_le hn0
  have h5 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
  nlinarith

/-- **Crude bound at any node** (used for the last node `k = 2n`). -/
theorem g_le_crude {σ : ℝ → ℝ} {n : ℕ} (hn : n % 2 = 1) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    Real.log |hZ n k| + 2 * BwZ n σ k ≤
      (6 * n + 1 + 2 * (n * ∫ y in (-1 : ℝ)..2, σ y)) * (2 + Real.log n) := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  simp only [Fam3PF.nodes, mem_Icc] at hk
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
  -- `ln |h_k|`
  have hh : Real.log |hZ n k| ≤ (6 * n + 1) * (2 + Real.log n) := by
    rw [log_abs_hZ hn k]
    have hlin : Real.log |((n : ℝ) - 2 * k)| ≤ 2 + Real.log n := by
      have hne : ((n : ℝ) - 2 * k) ≠ 0 := by have := lin_ne_zero hn k; exact_mod_cast this
      refine (Real.log_le_log (abs_pos.2 hne) ?_).trans hl5
      have : |(n : ℤ) - 2 * k| ≤ 5 * n := by rw [abs_le]; omega
      have h' : ((|(n : ℤ) - 2 * k| : ℤ) : ℝ) ≤ ((5 * n : ℤ) : ℝ) := by exact_mod_cast this
      rw [Int.cast_abs] at h'; push_cast at h'; exact h'
    have hhalf : ∑ j ∈ range n, 6 * Real.log |((j : ℝ) + 1 / 2 - k)| ≤ n * (6 * (2 + Real.log n)) := by
      calc _ ≤ ∑ _j ∈ range n, 6 * (2 + Real.log n) := sum_le_sum fun j hj => by
            simp only [mem_range] at hj
            have hpos : 0 < |((j : ℝ) + 1 / 2 - k)| := by
              refine abs_pos.2 fun h => ?_
              have h' : (((2 * (j : ℤ) + 1 - 2 * k : ℤ)) : ℝ) = 0 := by push_cast; linarith
              have : (2 * (j : ℤ) + 1 - 2 * k : ℤ) = 0 := by exact_mod_cast h'
              omega
            have : |((j : ℝ) + 1 / 2 - k)| ≤ 4 * n := by
              have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
              have hk1 : (-(n : ℝ)) ≤ k := by exact_mod_cast hk.1
              have hk2 : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk.2
              rw [abs_le]; constructor <;> linarith
            have := (Real.log_le_log hpos this).trans hl4
            linarith
        _ = n * (6 * (2 + Real.log n)) := by rw [sum_const, card_range, nsmul_eq_mul]
    have hint : 0 ≤ ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, 4 * Real.log |((k' : ℝ) - k)| :=
      sum_nonneg fun k' hk' => by
        have hne : k' - k ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hk')
        have : (1 : ℝ) ≤ |((k' : ℝ) - k)| := by
          have := Int.one_le_abs hne
          have h' : ((|k' - k| : ℤ) : ℝ) ≥ 1 := by exact_mod_cast this
          rw [Int.cast_abs] at h'; push_cast at h'; linarith
        have := Real.log_nonneg this
        linarith
    nlinarith
  -- `(B s̃)_k`
  have hB : BwZ n σ k ≤ (n * ∫ y in (-1 : ℝ)..2, σ y) * (2 + Real.log n) := by
    unfold BwZ
    rw [← sum_wZ hn0 hσm hσ, sum_mul]
    refine sum_le_sum fun m hm => ?_
    simp only [Fam3PF.nodes, mem_Icc] at hm
    have hw0 := wZ_nonneg hn0 hσ m
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hw0
    have hd : |((k - m : ℤ) : ℝ)| ≤ 3 * n := by
      rw [← Int.cast_abs]
      have : |k - m| ≤ 3 * n := by rw [abs_le]; omega
      exact_mod_cast this
    unfold Bk
    have h1 : 1 + ((k - m : ℤ) : ℝ) ^ 2 ≤ (4 * n) ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((k - m : ℤ) : ℝ)]
    have h2 : Real.log (1 + ((k - m : ℤ) : ℝ) ^ 2) ≤ 2 * Real.log (4 * n) := by
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this ⊢; linarith
    linarith
  nlinarith

end Hankel2.ArchB
