import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# Cell estimates for the logarithmic potential (for paper Lemma 6.4)

For `n ≥ 1` cut `[−1, 2]` into the cells `J_m = [m/n, (m+1)/n]`, `−n ≤ m < 2n`, and put
`cav f n m = n ∫_{J_m} f` (the cell mass, times `n`).  For measurable `f` with `0 ≤ f ≤ M` and
`x ∈ J_k`:

* **upper bound** (`logPot_upper`):
  `n 𝓛f(x) ≤ −(n ∫ f) ln n + ∑_m cav_m ln(|k − m| + 1)`;
* **lower bound** (`logPot_lower`):
  `n 𝓛f(x) ≥ −(n ∫ f) ln n + ∑_m cav_m ln(|k − m| − 1) − 18 M`

(with Lean's `ln 0 = ln(−1) = 0` for the neighbouring cells).  Both are exact comparisons of the
kernel `ln|x − y|` on `J_k × J_m` with `ln(|k−m| ± 1) − ln n`; the neighbouring cells are handled
with the explicit primitive `∫ ln t = t ln t − t`.  We also prove that `𝓛f` is measurable
(`measurable_logPot`) and bounded by `18 M` on `[−1, 2]` (`abs_logPot_le`).
-/

open MeasureTheory Finset

namespace Hankel2.ArchB

/-! ### Integrability -/

theorem ii_bdd_mul {g h : ℝ → ℝ} {a b C : ℝ} (hg : IntervalIntegrable g volume a b)
    (hh : Measurable h) (hb : ∀ y, |h y| ≤ C) :
    IntervalIntegrable (fun y => g y * h y) volume a b := by
  rw [intervalIntegrable_iff] at *
  have := hg.bdd_mul (f := h) hh.aestronglyMeasurable (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]; exact hb y)
  simpa [mul_comm] using this

theorem ii_log_sub (x a b : ℝ) : IntervalIntegrable (fun y => Real.log |x - y|) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := x - a) (b := x - b)).comp_sub_left x
  simp only [sub_sub_cancel] at h
  simpa [Real.log_abs] using h

theorem ii_logmul {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf : ∀ y, |f y| ≤ M) (x a b : ℝ) :
    IntervalIntegrable (fun y => Real.log |x - y| * f y) volume a b :=
  ii_bdd_mul (ii_log_sub x a b) hfm hf

theorem ii_of_bdd {g : ℝ → ℝ} {C : ℝ} (hg : Measurable g) (hb : ∀ y, |g y| ≤ C) (a b : ℝ) :
    IntervalIntegrable g volume a b := by
  have := ii_bdd_mul (g := fun _ => (1 : ℝ)) (h := g) intervalIntegrable_const hg hb (a := a) (b := b)
  simpa using this

/-! ### Cells -/

/-- The cell mass `cav f n m = n ∫_{m/n}^{(m+1)/n} f`. -/
noncomputable def cav (f : ℝ → ℝ) (n : ℕ) (m : ℤ) : ℝ :=
  n * ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), f y

theorem cell_le {n : ℕ} (hn : 0 < n) (m : ℤ) : (m : ℝ) / n ≤ ((m : ℝ) + 1) / n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right (by linarith) this.le

theorem cav_nonneg {f : ℝ → ℝ} (hf0 : ∀ y, 0 ≤ f y) {n : ℕ} (hn : 0 < n) (m : ℤ) :
    0 ≤ cav f n m := by
  unfold cav
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (cell_le hn m) fun y _ => hf0 y)

theorem cav_le {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf : ∀ y, |f y| ≤ M) (hfM : ∀ y, f y ≤ M)
    {n : ℕ} (hn : 0 < n) (m : ℤ) : cav f n m ≤ M := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cav
  have h := intervalIntegral.integral_mono_on (cell_le hn m) (ii_of_bdd hfm hf _ _)
    (intervalIntegrable_const (c := M)) (fun y _ => hfM y)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have e : ((m : ℝ) + 1) / n - (m : ℝ) / n = 1 / n := by field_simp; ring
  rw [e] at h
  calc (n : ℝ) * ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), f y ≤ n * (1 / n * M) :=
        mul_le_mul_of_nonneg_left h hn'.le
    _ = M := by field_simp

/-- `∫_{−1}^{2} g = ∑_{−n ≤ m < 2n} ∫_{J_m} g`. -/
theorem integral_split_cells {g : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hg : ∀ a b : ℝ, IntervalIntegrable g volume a b) :
    ∫ y in (-1 : ℝ)..2, g y =
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), g y := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun i : ℕ => ((i : ℝ) - n) / n) (n := 3 * n) (fun k _ => hg _ _)
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

/-- The sum of the cell masses is `n ∫ f`. -/
theorem sum_cav {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf : ∀ y, |f y| ≤ M) {n : ℕ}
    (hn : 0 < n) : ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav f n m = n * ∫ y in (-1 : ℝ)..2, f y := by
  rw [integral_split_cells hn (fun a b => ii_of_bdd hfm hf a b), mul_sum]
  rfl

/-! ### The kernel on a pair of cells -/

theorem cell_dist {n : ℕ} (hn : 0 < n) {k m : ℤ} {x y : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n))
    (hy : y ∈ Set.Icc ((m : ℝ) / n) (((m : ℝ) + 1) / n)) :
    (k : ℝ) - m - 1 ≤ n * (x - y) ∧ n * (x - y) ≤ (k : ℝ) - m + 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [div_le_iff₀ hn'] at hx1 hy1
  rw [le_div_iff₀ hn'] at hx2 hy2
  constructor <;> nlinarith

theorem cell_abs_le {n : ℕ} (hn : 0 < n) {k m : ℤ} {x y : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n))
    (hy : y ∈ Set.Icc ((m : ℝ) / n) (((m : ℝ) + 1) / n)) :
    |x - y| ≤ (|((k - m : ℤ) : ℝ)| + 1) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := cell_dist hn hx hy
  have e : ((k - m : ℤ) : ℝ) = (k : ℝ) - m := by push_cast; ring
  rw [e]
  have h3 : n * (x - y) ≤ |(k : ℝ) - m| + 1 := by have := le_abs_self ((k : ℝ) - m); linarith
  have h4 : -(|(k : ℝ) - m| + 1) ≤ n * (x - y) := by have := neg_abs_le ((k : ℝ) - m); linarith
  calc |x - y| = |n * (x - y)| / n := by rw [abs_mul, abs_of_pos hn']; field_simp
    _ ≤ (|(k : ℝ) - m| + 1) / n := div_le_div_of_nonneg_right (abs_le.2 ⟨h4, h3⟩) hn'.le

theorem cell_abs_ge {n : ℕ} (hn : 0 < n) {k m : ℤ} {x y : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n))
    (hy : y ∈ Set.Icc ((m : ℝ) / n) (((m : ℝ) + 1) / n)) :
    (|((k - m : ℤ) : ℝ)| - 1) / n ≤ |x - y| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := cell_dist hn hx hy
  have e : ((k - m : ℤ) : ℝ) = (k : ℝ) - m := by push_cast; ring
  rw [e]
  have h3 : |(k : ℝ) - m| - 1 ≤ |n * (x - y)| := by
    rcases le_total 0 ((k : ℝ) - m) with h | h
    · rw [abs_of_nonneg h]
      calc (k : ℝ) - m - 1 ≤ n * (x - y) := h1
        _ ≤ |n * (x - y)| := le_abs_self _
    · rw [abs_of_nonpos h]
      calc -((k : ℝ) - m) - 1 ≤ -(n * (x - y)) := by linarith
        _ ≤ |n * (x - y)| := neg_le_abs _
  calc (|(k : ℝ) - m| - 1) / n ≤ |n * (x - y)| / n := div_le_div_of_nonneg_right h3 hn'.le
    _ = |x - y| := by rw [abs_mul, abs_of_pos hn']; field_simp

/-! ### Upper bound, one cell -/

theorem cell_upper {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, |f y| ≤ M) {n : ℕ} (hn : 0 < n) {k m : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y ≤
      (Real.log (|((k - m : ℤ) : ℝ)| + 1) - Real.log n) * cav f n m / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c := Real.log (|((k - m : ℤ) : ℝ)| + 1) - Real.log n
  have hrhs : c * cav f n m / n = ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), c * f y := by
    rw [intervalIntegral.integral_const_mul, cav]; field_simp
  rw [hrhs]
  refine intervalIntegral.integral_mono_ae_restrict (cell_le hn m) (ii_logmul hfm hf _ _ _)
    ((ii_of_bdd hfm hf _ _).const_mul c) ?_
  have hae : ∀ᵐ y ∂(volume.restrict (Set.Icc ((m : ℝ) / n) (((m : ℝ) + 1) / n))), y ≠ x :=
    ae_restrict_of_ae (Measure.ae_ne volume x)
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with y hyx hy
  refine mul_le_mul_of_nonneg_right ?_ (hf0 y)
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hyx.symm)
  have h1 := cell_abs_le hn hx hy
  calc Real.log |x - y| ≤ Real.log ((|((k - m : ℤ) : ℝ)| + 1) / n) := Real.log_le_log hpos h1
    _ = c := by rw [Real.log_div (by positivity) hn'.ne']

/-! ### Lower bound, one cell -/

theorem cell_lower_far {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, |f y| ≤ M) {n : ℕ} (hn : 0 < n) {k m : ℤ} (hkm : 2 ≤ |k - m|) {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    (Real.log (|((k - m : ℤ) : ℝ)| - 1) - Real.log n) * cav f n m / n ≤
      ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c := Real.log (|((k - m : ℤ) : ℝ)| - 1) - Real.log n
  have hrhs : c * cav f n m / n = ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), c * f y := by
    rw [intervalIntegral.integral_const_mul, cav]; field_simp
  rw [hrhs]
  have hd : (2 : ℝ) ≤ |((k - m : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hkm
  refine intervalIntegral.integral_mono_on (cell_le hn m)
    ((ii_of_bdd hfm hf _ _).const_mul c) (ii_logmul hfm hf _ _ _) fun y hy => ?_
  refine mul_le_mul_of_nonneg_right ?_ (hf0 y)
  have h1 := cell_abs_ge hn hx hy
  have hpos : 0 < (|((k - m : ℤ) : ℝ)| - 1) / n := div_pos (by linarith) hn'
  calc c = Real.log ((|((k - m : ℤ) : ℝ)| - 1) / n) := by
        rw [Real.log_div (by linarith) hn'.ne']
    _ ≤ Real.log |x - y| := Real.log_le_log hpos h1

theorem abs_mul_log_le_two {u : ℝ} (hu : |u| ≤ 2) : |u * Real.log u| ≤ 2 := by
  rcases le_total |u| 1 with h1 | h1
  · rcases eq_or_ne u 0 with rfl | h0
    · simp
    · have := Real.abs_log_mul_self_lt |u| (abs_pos.2 h0) h1
      rw [Real.log_abs] at this
      rw [abs_mul] at this ⊢
      rw [abs_abs] at this
      linarith
  · have hl0 : 0 ≤ Real.log u := by rw [← Real.log_abs]; exact Real.log_nonneg h1
    have hl1 : Real.log u ≤ 1 := by
      rw [← Real.log_abs]
      calc Real.log |u| ≤ Real.log 2 := Real.log_le_log (by linarith) hu
        _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
    rw [abs_mul, abs_of_nonneg hl0]
    nlinarith [abs_nonneg u]

theorem mul_log_div (u : ℝ) {n : ℝ} (hn : 0 < n) :
    u / n * Real.log (u / n) = (u * Real.log u - u * Real.log n) / n := by
  rcases eq_or_ne u 0 with rfl | h0
  · simp
  · rw [Real.log_div h0 hn.ne']; ring

/-- `∫_{J_m} ln|x − y| dy ≥ −(5 + ln n)/n` for the neighbouring cells. -/
theorem integral_log_near {n : ℕ} (hn : 0 < n) {k m : ℤ} (hkm : |k - m| ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    -(5 + Real.log n) / n ≤ ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left (fun t => Real.log t) x, integral_log]
  set u1 := n * x - m with hu1
  have hb : x - (m : ℝ) / n = u1 / n := by rw [hu1]; field_simp
  have ha : x - ((m : ℝ) + 1) / n = (u1 - 1) / n := by rw [hu1]; field_simp; ring
  rw [hb, ha, mul_log_div _ hn', mul_log_div _ hn']
  obtain ⟨hx1, hx2⟩ := hx
  rw [div_le_iff₀ hn'] at hx1
  rw [le_div_iff₀ hn'] at hx2
  have hkm' : ((|k - m| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hkm
  rw [Int.cast_abs, abs_le] at hkm'
  push_cast at hkm'
  have hu1b : |u1| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have hu0b : |u1 - 1| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have e1 := abs_mul_log_le_two hu1b
  have e0 := abs_mul_log_le_two hu0b
  rw [abs_le] at e1 e0
  rw [div_le_iff₀ hn']
  have : ((u1 * Real.log u1 - u1 * Real.log n) / n - ((u1 - 1) * Real.log (u1 - 1) -
      (u1 - 1) * Real.log n) / n - u1 / n + (u1 - 1) / n) * n =
      u1 * Real.log u1 - (u1 - 1) * Real.log (u1 - 1) - Real.log n - 1 := by
    field_simp; ring
  rw [this]
  linarith [e1.1, e0.2]

theorem cell_lower_near {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hf : ∀ y, |f y| ≤ M) {n : ℕ} (hn : 0 < n) {k m : ℤ}
    (hkm : |k - m| ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    -Real.log n * cav f n m / n - 6 * M / n ≤
      ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  set g : ℝ → ℝ := fun y => -Real.log n * f y + M * Real.log |x - y| + (M * Real.log n - M)
  have hgi : IntervalIntegrable g volume ((m : ℝ) / n) (((m : ℝ) + 1) / n) :=
    (((ii_of_bdd hfm hf _ _).const_mul _).add ((ii_log_sub x _ _).const_mul M)).add
      intervalIntegrable_const
  set I1 := ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), f y with hI1
  set I2 := ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| with hI2
  have hint : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), g y =
      -Real.log n * I1 + M * I2 + (M * Real.log n - M) / n := by
    simp only [g]
    rw [intervalIntegral.integral_add (((ii_of_bdd hfm hf _ _).const_mul _).add
      ((ii_log_sub x _ _).const_mul M)) intervalIntegrable_const,
      intervalIntegral.integral_add ((ii_of_bdd hfm hf _ _).const_mul _)
      ((ii_log_sub x _ _).const_mul M), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have e1 : ((m : ℝ) + 1) / n - (m : ℝ) / n = 1 / n := by field_simp; ring
    rw [e1]; ring
  have hcav : cav f n m = n * I1 := rfl
  have hlow := integral_log_near hn hkm hx
  have hle : ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), g y ≤
      ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y := by
    refine intervalIntegral.integral_mono_ae_restrict (cell_le hn m) hgi
      (ii_logmul hfm hf _ _ _) ?_
    have hae : ∀ᵐ y ∂(volume.restrict (Set.Icc ((m : ℝ) / n) (((m : ℝ) + 1) / n))), y ≠ x :=
      ae_restrict_of_ae (Measure.ae_ne volume x)
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with y hyx hy
    have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hyx.symm)
    have h1 := cell_abs_le hn hx hy
    have hkm' : |((k - m : ℤ) : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast hkm
    have ha1 : Real.log |x - y| + Real.log n ≤ 1 := by
      rw [← Real.log_mul hpos.ne' hn'.ne']
      have : |x - y| * n ≤ 2 := by
        rw [le_div_iff₀ hn'] at h1; linarith
      calc Real.log (|x - y| * n) ≤ Real.log 2 := Real.log_le_log (by positivity) this
        _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have key : f y * (Real.log |x - y| + Real.log n) ≥ M * (Real.log |x - y| + Real.log n) - M := by
      rcases le_total 0 (Real.log |x - y| + Real.log n) with ha | ha
      · have : 0 ≤ f y * (Real.log |x - y| + Real.log n) := mul_nonneg (hf0 y) ha
        nlinarith
      · nlinarith [hfM y, hf0 y]
    simp only [g]
    nlinarith
  rw [hint] at hle
  have : M * (-(5 + Real.log n) / n) ≤ M * ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n),
      Real.log |x - y| := mul_le_mul_of_nonneg_left hlow hM
  have e : -Real.log n * cav f n m / n - 6 * M / n =
      -Real.log n * I1 + M * (-(5 + Real.log n) / n) + (M * Real.log n - M) / n := by
    rw [hcav]; field_simp; ring
  linarith

/-! ### The full potential -/

theorem logPot_eq_sum {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf : ∀ y, |f y| ≤ M) {n : ℕ}
    (hn : 0 < n) (x : ℝ) :
    logPot f x = ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
      ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y :=
  integral_split_cells hn (fun a b => ii_logmul hfm hf x a b)

/-- **Upper bound for `n 𝓛f(x)`**, `x ∈ J_k`. -/
theorem logPot_upper {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, |f y| ≤ M) {n : ℕ} (hn : 0 < n) {k : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    n * logPot f x ≤ -(n * ∫ y in (-1 : ℝ)..2, f y) * Real.log n +
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav f n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logPot_eq_sum hfm hf hn, ← sum_cav hfm hf hn, mul_sum, neg_mul, sum_mul,
    ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_le_sum fun m _ => ?_
  have := cell_upper hfm hf0 hf hn (m := m) hx
  have e : (n : ℝ) * ((Real.log (|((k - m : ℤ) : ℝ)| + 1) - Real.log n) * cav f n m / n) =
      -(cav f n m * Real.log n) + cav f n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
    field_simp; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_left this hn'.le

theorem log_abs_sub_one_eq_zero {d : ℤ} (hd : |d| ≤ 1) : Real.log (|(d : ℝ)| - 1) = 0 := by
  have h : |d| = 0 ∨ |d| = 1 := by have := abs_nonneg d; omega
  rcases h with h | h
  · have : |(d : ℝ)| = 0 := by rw [← Int.cast_abs, h]; simp
    rw [this]; simp
  · have : |(d : ℝ)| = 1 := by rw [← Int.cast_abs, h]; simp
    rw [this]; simp

theorem card_near_le (n : ℕ) (k : ℤ) :
    ((Ico (-(n : ℤ)) (2 * n)).filter fun m => |k - m| ≤ 1).card ≤ 3 := by
  refine (card_le_card (s := (Ico (-(n : ℤ)) (2 * n)).filter fun m => |k - m| ≤ 1)
    (t := Icc (k - 1) (k + 1)) fun m hm => ?_).trans ?_
  · simp only [mem_filter] at hm
    simp only [mem_Icc]
    rw [abs_le] at hm; omega
  · rw [Int.card_Icc]; omega

/-- **Lower bound for `n 𝓛f(x)`**, `x ∈ J_k`. -/
theorem logPot_lower {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) (hf : ∀ y, |f y| ≤ M) {n : ℕ} (hn : 0 < n) {k : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    -(n * ∫ y in (-1 : ℝ)..2, f y) * Real.log n +
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav f n m * Real.log (|((k - m : ℤ) : ℝ)| - 1) - 18 * M ≤
      n * logPot f x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  set ind : ℤ → ℝ := fun m => if |k - m| ≤ 1 then 1 else 0 with hind
  have hcell : ∀ m, (Real.log (|((k - m : ℤ) : ℝ)| - 1) - Real.log n) * cav f n m / n -
      6 * M / n * ind m ≤ ∫ y in ((m : ℝ) / n)..(((m : ℝ) + 1) / n), Real.log |x - y| * f y := by
    intro m
    by_cases h : |k - m| ≤ 1
    · have := cell_lower_near hfm hf0 hfM hf hn h hx
      simp only [hind, if_pos h, log_abs_sub_one_eq_zero h, mul_one, zero_sub]
      linarith
    · have := cell_lower_far hfm hf0 hf hn (by have := not_le.mp h; linarith) hx
      simp only [hind, if_neg h, mul_zero, sub_zero]
      exact this
  have hsum : ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m ≤ 3 := by
    rw [← sum_filter_add_sum_filter_not _ (fun m => |k - m| ≤ 1)]
    have h1 : ∑ m ∈ (Ico (-(n : ℤ)) (2 * n)).filter (fun m => |k - m| ≤ 1), ind m =
        ((Ico (-(n : ℤ)) (2 * n)).filter fun m => |k - m| ≤ 1).card := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      refine sum_congr rfl fun m hm => ?_
      simp only [mem_filter] at hm
      simp [hind, hm.2]
    have h2 : ∑ m ∈ (Ico (-(n : ℤ)) (2 * n)).filter (fun m => ¬ |k - m| ≤ 1), ind m = 0 :=
      sum_eq_zero fun m hm => by simp only [mem_filter] at hm; simp [hind, hm.2]
    rw [h1, h2, add_zero]
    exact_mod_cast card_near_le n k
  rw [logPot_eq_sum hfm hf hn]
  have hmain := sum_le_sum fun m (_ : m ∈ Ico (-(n : ℤ)) (2 * n)) => hcell m
  rw [sum_sub_distrib, ← mul_sum] at hmain
  have hmain' := mul_le_mul_of_nonneg_left hmain hn'.le
  rw [← sum_cav hfm hf hn]
  have e : (n : ℝ) * (∑ m ∈ Ico (-(n : ℤ)) (2 * n),
      (Real.log (|((k - m : ℤ) : ℝ)| - 1) - Real.log n) * cav f n m / n -
      6 * M / n * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m) =
      -(∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav f n m) * Real.log n +
      ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav f n m * Real.log (|((k - m : ℤ) : ℝ)| - 1) -
      6 * M * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m := by
    rw [mul_sub, mul_sum, neg_mul, sum_mul, ← sum_neg_distrib, ← sum_add_distrib]
    have : (n : ℝ) * (6 * M / n * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m) =
        6 * M * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m := by field_simp
    rw [this]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    field_simp; ring
  rw [e] at hmain'
  have : 6 * M * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), ind m ≤ 18 * M := by nlinarith
  linarith

/-! ### Measurability and boundedness -/

theorem measurable_logPot {f : ℝ → ℝ} (hfm : Measurable f) : Measurable (logPot f) := by
  have hF : StronglyMeasurable (Function.uncurry fun x y : ℝ => Real.log |x - y| * f y) := by
    refine Measurable.stronglyMeasurable ?_
    change Measurable fun p : ℝ × ℝ => Real.log |p.1 - p.2| * f p.2
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.log |p.1 - p.2|).mul
      (hfm.comp measurable_snd)
  have h := hF.integral_prod_right (ν := volume.restrict (Set.Ioc (-1 : ℝ) 2))
  have e : logPot f = fun x => ∫ y, Real.log |x - y| * f y ∂(volume.restrict (Set.Ioc (-1 : ℝ) 2)) := by
    funext x
    rw [logPot, intervalIntegral.integral_of_le (by norm_num)]
  rw [e]
  exact h.measurable

theorem mem_some_cell {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) :
    ∃ k : ℤ, -1 ≤ k ∧ k ≤ 1 ∧ x ∈ Set.Icc ((k : ℝ) / (1 : ℕ)) (((k : ℝ) + 1) / (1 : ℕ)) := by
  obtain ⟨h1, h2⟩ := hx
  by_cases a : x ≤ 0
  · exact ⟨-1, by norm_num, by norm_num, by simp; constructor <;> linarith⟩
  by_cases b : x ≤ 1
  · exact ⟨0, by norm_num, by norm_num, by simp; constructor <;> linarith⟩
  · exact ⟨1, by norm_num, le_rfl, by simp; constructor <;> linarith⟩

/-- `|𝓛f(x)| ≤ 18 M` on `[−1, 2]` for `0 ≤ f ≤ M`. -/
theorem abs_logPot_le {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hfM : ∀ y, f y ≤ M) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |logPot f x| ≤ 18 * M := by
  have hf : ∀ y, |f y| ≤ M := fun y => by rw [abs_of_nonneg (hf0 y)]; exact hfM y
  have hM : 0 ≤ M := (hf0 0).trans (hfM 0)
  obtain ⟨k, hk1, hk2, hxk⟩ := mem_some_cell hx
  have hup := logPot_upper hfm hf0 hf one_pos hxk
  have hlo := logPot_lower hfm hf0 hfM hf one_pos hxk
  simp only [Nat.cast_one, one_mul, Real.log_one, mul_zero, zero_add] at hup hlo
  have hcav0 : ∀ m, 0 ≤ cav f 1 m := fun m => cav_nonneg hf0 one_pos m
  have hcavM : ∀ m, cav f 1 m ≤ M := fun m => cav_le hfm hf hfM one_pos m
  have hIco : Ico (-1 : ℤ) (2 * 1) = {-1, 0, 1} := by decide
  rw [hIco] at hup hlo
  have hl : ∀ m ∈ ({-1, 0, 1} : Finset ℤ), 0 ≤ Real.log (|((k - m : ℤ) : ℝ)| - 1) := by
    intro m hm
    by_cases h : |k - m| ≤ 1
    · rw [log_abs_sub_one_eq_zero h]
    · refine Real.log_nonneg ?_
      have : (2 : ℝ) ≤ |((k - m : ℤ) : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast (by have := not_le.mp h; linarith : 2 ≤ |k - m|)
      linarith
  have hu : ∀ m ∈ ({-1, 0, 1} : Finset ℤ), Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤ 3 / 2 := by
    intro m hm
    have hb : |((k - m : ℤ) : ℝ)| ≤ 2 := by
      rw [← Int.cast_abs]
      simp only [mem_insert, mem_singleton] at hm
      have : |k - m| ≤ 2 := by rw [abs_le]; rcases hm with rfl | rfl | rfl <;> omega
      exact_mod_cast this
    calc Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤ Real.log 3 :=
          Real.log_le_log (by positivity) (by linarith)
      _ ≤ 3 / 2 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / Real.exp 1 by positivity)
          rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
          have he := Real.exp_one_gt_d9
          have : 3 / Real.exp 1 ≤ 3 / 2.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            (by linarith)
          linarith
  have hS1 : ∑ m ∈ ({-1, 0, 1} : Finset ℤ), cav f 1 m * Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤
      3 * (M * (3 / 2)) := by
    calc _ ≤ ∑ _m ∈ ({-1, 0, 1} : Finset ℤ), M * (3 / 2) := sum_le_sum fun m hm =>
          mul_le_mul (hcavM m) (hu m hm) (by
            have := hl m hm
            exact Real.log_nonneg (by linarith [abs_nonneg ((k - m : ℤ) : ℝ)]))
            hM
      _ = 3 * (M * (3 / 2)) := by simp
  have hS2 : 0 ≤ ∑ m ∈ ({-1, 0, 1} : Finset ℤ), cav f 1 m * Real.log (|((k - m : ℤ) : ℝ)| - 1) :=
    sum_nonneg fun m hm => mul_nonneg (hcav0 m) (hl m hm)
  rw [abs_le]
  constructor <;> nlinarith

end Hankel2.ArchB
