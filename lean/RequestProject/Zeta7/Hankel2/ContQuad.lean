import RequestProject.Zeta7.Hankel2.ContEnergy

/-!
# Paper Lemma 6.4 (c) and the gap term

* `Q_bound` (Lemma 6.4 (c), the quadratic term):
  `n² ⟨σ, 𝓛σ⟩ ≤ −K² ln n + ∑_{k,m} s̃_k s̃_m B(k − m) + 8K(1 + ln 3n)`;
* `P_bound` (the linear term against an integer profile): for `0 ≤ s_k ≤ 4`, `K − 4 ≤ ∑ s_k ≤ K`,
  `∑_{k<2n} s_k n² ∫_{J_k} P_σ ≤ n² (F[σ] + gap(σ) + ⟨σ, 𝓛σ⟩) + 3024 n`.
  The profile `s/n` is turned into a feasible competitor `σ''` for `gap(σ)` (a step function,
  corrected to the exact mass `κ` by a convex combination with the constant `4`).
-/

open MeasureTheory Finset

namespace Hankel2.ArchB

open Fam3

/-! ### Integrability of the relevant products -/

theorem abs_logPot_σ_le {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |logPot σ x| ≤ 72 := by
  have := abs_logPot_le hσm (fun y => (hσ y).1) (fun y => (hσ y).2) hx
  linarith

theorem ii_mul_on {f g : ℝ → ℝ} {A B : ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ A) (hgb : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |g x| ≤ B) {a b : ℝ} (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 2) : IntervalIntegrable (fun x => f x * g x) volume a b :=
  ii_of_bdd_on (C := A * B) (hf.mul hg) (fun x hx => by
    rw [abs_mul]
    exact mul_le_mul (hfb x) (hgb x hx) (abs_nonneg _) ((abs_nonneg _).trans (hfb x))) ha hab hb

/-! ### The quadratic term -/

theorem Q_bound {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, σ y = K) :
    (n : ℝ) ^ 2 * pairing σ (logPot σ) ≤ -(K : ℝ) ^ 2 * Real.log n +
      ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n, wZ n σ k * wZ n σ m * Bk ((k - m : ℤ) : ℝ) +
      8 * K * (1 + Real.log (3 * n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hσb : ∀ y, |σ y| ≤ 4 := fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2
  set U : ℤ → ℝ := fun k => -(K : ℝ) * Real.log n +
    ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) with hU
  -- per cell
  have hcell : ∀ k ∈ Ico (-(n : ℤ)) (2 * n),
      (n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), σ x * logPot σ x ≤
        cav σ n k * U k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := cell_sub hn hk
    have hint1 : IntervalIntegrable (fun x => σ x * ((n : ℝ) * logPot σ x)) volume
        ((k : ℝ) / n) (((k : ℝ) + 1) / n) := by
      have := ii_mul_on hσm (measurable_logPot hσm) hσb (fun x hx => abs_logPot_σ_le hσm hσ hx)
        hk1 (cell_le hn k) hk2
      simpa [mul_left_comm] using this.const_mul (n : ℝ)
    have hint2 : IntervalIntegrable (fun x => σ x * U k) volume ((k : ℝ) / n) (((k : ℝ) + 1) / n) :=
      (ii_of_bdd hσm hσb _ _).mul_const _
    have h := intervalIntegral.integral_mono_on (cell_le hn k) hint1 hint2 fun x hx => by
      refine mul_le_mul_of_nonneg_left ?_ (hσ x).1
      have := logPot_upper hσm (fun y => (hσ y).1) hσb hn hx
      rw [hmass] at this
      simp only [hU]; linarith
    rw [intervalIntegral.integral_mul_const] at h
    have e1 : ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), σ x * ((n : ℝ) * logPot σ x) =
        n * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), σ x * logPot σ x := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
    rw [e1] at h
    have e2 : cav σ n k * U k = (n : ℝ) * ((∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), σ x) * U k) := by
      rw [cav]; ring
    rw [e2, sq, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hn'.le
  -- sum over cells
  have hsplit : pairing σ (logPot σ) = ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
      ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), σ x * logPot σ x :=
    integral_split_cells' hn fun a b ha hab hb =>
      ii_mul_on hσm (measurable_logPot hσm) hσb (fun x hx => abs_logPot_σ_le hσm hσ hx) ha hab hb
  have hsum : (n : ℝ) ^ 2 * pairing σ (logPot σ) ≤ ∑ k ∈ Ico (-(n : ℤ)) (2 * n), cav σ n k * U k := by
    rw [hsplit, mul_sum]; exact sum_le_sum hcell
  have hcavK : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), cav σ n k = K := by rw [sum_cav hσm hσb hn, hmass]
  -- the kernel replacement
  have hker : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), cav σ n k * U k ≤ -(K : ℝ) ^ 2 * Real.log n +
      ∑ k ∈ Ico (-(n : ℤ)) (2 * n), ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
        cav σ n k * cav σ n m * Bk ((k - m : ℤ) : ℝ) + 8 * K * (1 + Real.log (3 * n)) := by
    have e : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), cav σ n k * U k = -(K : ℝ) ^ 2 * Real.log n +
        ∑ k ∈ Ico (-(n : ℤ)) (2 * n), ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
          cav σ n k * cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) := by
      simp only [hU, mul_add, sum_add_distrib, mul_sum]
      rw [← sum_mul, hcavK]
      congr 1
      · ring
      · refine sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    rw [e]
    have hterm : ∀ k ∈ Ico (-(n : ℤ)) (2 * n), ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
        cav σ n k * cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤
        ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n k * cav σ n m * Bk ((k - m : ℤ) : ℝ) +
          cav σ n k * (8 * (1 + Real.log (3 * n))) := by
      intro k hk
      have hk0 := cav_nonneg (fun y => (hσ y).1) hn k
      have hinv : ∑ m ∈ Ico (-(n : ℤ)) (2 * n), 1 / |((k - m : ℤ) : ℝ)| ≤ 2 * (1 + Real.log (3 * n)) := by
        have hkn : k ∈ Fam3PF.nodes n := by
          simp only [mem_Ico] at hk; simp only [Fam3PF.nodes, mem_Icc]; omega
        refine le_trans (sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ => by positivity)
          (sum_nodes_inv_le hkn)
        simp only [mem_Ico] at hm; simp only [Fam3PF.nodes, mem_Icc]; omega
      have h1 : ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
          cav σ n k * cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤
          ∑ m ∈ Ico (-(n : ℤ)) (2 * n), (cav σ n k * cav σ n m * Bk ((k - m : ℤ) : ℝ) +
            cav σ n k * (4 * (1 / |((k - m : ℤ) : ℝ)|))) := by
        refine sum_le_sum fun m _ => ?_
        have hm0 := cav_nonneg (fun y => (hσ y).1) hn m
        have hm4 := cav_le hσm hσb (fun y => (hσ y).2) hn m
        have hl := log_add_one_le_Bk (k - m)
        have hinv' : 0 ≤ 1 / |((k - m : ℤ) : ℝ)| := by positivity
        have : cav σ n k * cav σ n m * Real.log (|((k - m : ℤ) : ℝ)| + 1) ≤
            cav σ n k * cav σ n m * (Bk ((k - m : ℤ) : ℝ) + 1 / |((k - m : ℤ) : ℝ)|) :=
          mul_le_mul_of_nonneg_left hl (mul_nonneg hk0 hm0)
        have : cav σ n k * cav σ n m * (1 / |((k - m : ℤ) : ℝ)|) ≤
            cav σ n k * (4 * (1 / |((k - m : ℤ) : ℝ)|)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm4 hinv') hk0
        nlinarith
      rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
      have : cav σ n k * (4 * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), 1 / |((k - m : ℤ) : ℝ)|) ≤
          cav σ n k * (8 * (1 + Real.log (3 * n))) :=
        mul_le_mul_of_nonneg_left (by linarith) hk0
      linarith
    have := sum_le_sum hterm
    rw [sum_add_distrib, ← sum_mul, hcavK] at this
    linarith
  -- back to the nodes
  have hconv : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), ∑ m ∈ Ico (-(n : ℤ)) (2 * n),
      cav σ n k * cav σ n m * Bk ((k - m : ℤ) : ℝ) =
      ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n, wZ n σ k * wZ n σ m * Bk ((k - m : ℤ) : ℝ) := by
    have h1 : ∀ k, ∑ m ∈ Fam3PF.nodes n, wZ n σ k * wZ n σ m * Bk ((k - m : ℤ) : ℝ) =
        wZ n σ k * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n m * Bk ((k - m : ℤ) : ℝ) := by
      intro k
      rw [← sum_nodes_wZ n σ (fun m => Bk ((k - m : ℤ) : ℝ)), mul_sum]
      refine sum_congr rfl fun m _ => by ring
    simp_rw [h1]
    rw [sum_nodes_wZ n σ (fun k => ∑ m ∈ Ico (-(n : ℤ)) (2 * n), cav σ n m * Bk ((k - m : ℤ) : ℝ))]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun m _ => by ring
  rw [← hconv]
  linarith

/-! ### The linear term against an integer profile -/

/-- The step function of a profile: `s_k` on `(k/n, (k+1)/n]`. -/
noncomputable def stepFn (n : ℕ) (s : ℤ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Ioc (-1 : ℝ) 2 then s (⌈(n : ℝ) * x⌉ - 1) else 0

theorem stepFn_cell {n : ℕ} (hn : 0 < n) (s : ℤ → ℝ) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n))
    {x : ℝ} (hx : x ∈ Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) : stepFn n s x = s k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hk1, hk2⟩ := cell_sub hn hk
  have hx1 : (k : ℝ) < n * x := by
    have := hx.1; rw [div_lt_iff₀ hn'] at this; linarith
  have hx2 : (n : ℝ) * x ≤ k + 1 := by
    have := hx.2; rw [le_div_iff₀ hn'] at this; linarith
  have hin : x ∈ Set.Ioc (-1 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc : ⌈(n : ℝ) * x⌉ = k + 1 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  simp only [stepFn, if_pos hin, hc, add_sub_cancel_right]

theorem abs_integral_le_of_bdd {f : ℝ → ℝ} {C : ℝ} (hf : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |f x| ≤ C) :
    |∫ x in (-1 : ℝ)..2, f x| ≤ 3 * C := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 2) (C := C) (f := f)
    (fun x hx => by
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact hf x ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs] at this
  norm_num at this; linarith

theorem P_bound {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hF : Feasible ((K : ℝ) / n) σ)
    (hK : (K : ℝ) / n ≤ 3) (s : ℤ → ℝ) (hs : ∀ k, 0 ≤ s k ∧ s k ≤ 4)
    (hsum1 : (K : ℝ) - 4 ≤ ∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k)
    (hsum2 : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k ≤ K) :
    ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
        s k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Pgrad σ x) ≤
      (n : ℝ) ^ 2 * (Fenergy σ + gapF ((K : ℝ) / n) σ + pairing σ (logPot σ)) + 3024 * n := by
  obtain ⟨hσm, hσ, hmass⟩ := hF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set κ := (K : ℝ) / n with hκ
  have hσb : ∀ y, |σ y| ≤ 4 := fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2
  set P := Pgrad σ with hP
  have hPm : Measurable P := measurable_Pgrad hσm
  have hPb : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |P x| ≤ 252 := fun x hx => abs_Pgrad_le hσm hσ hx
  set σ' := stepFn n s with hσ'
  have hσ'b : ∀ x, 0 ≤ σ' x ∧ σ' x ≤ 4 := fun x => by
    simp only [hσ', stepFn]; split_ifs
    · exact hs _
    · exact ⟨le_rfl, by norm_num⟩
  have hσ'a : ∀ x, |σ' x| ≤ 4 := fun y => by rw [abs_of_nonneg (hσ'b y).1]; exact (hσ'b y).2
  have hσ'm : Measurable σ' := by
    have : Measurable (fun x : ℝ => s (⌈(n : ℝ) * x⌉ - 1)) := by fun_prop
    exact Measurable.ite measurableSet_Ioc this measurable_const
  -- the two cell sums
  have hPσ' : ∫ x in (-1 : ℝ)..2, σ' x * P x = ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
      s k * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), P x := by
    rw [integral_split_cells' hn fun a b ha hab hb => ii_mul_on hσ'm hPm hσ'a hPb ha hab hb]
    refine sum_congr rfl fun k hk => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (cell_le hn k)] at hx
    simp only [hσ', stepFn_cell hn s hk hx]
  have hm1 : ∫ x in (-1 : ℝ)..2, σ' x = (∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k) / n := by
    rw [integral_split_cells' hn fun a b _ _ _ => ii_of_bdd hσ'm hσ'a a b, sum_div]
    refine sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_congr_ae (g := fun _ => s k)
      (Filter.Eventually.of_forall fun x hx => by
        rw [Set.uIoc_of_le (cell_le hn k)] at hx
        exact stepFn_cell hn s hk hx)]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp; ring
  set m1 := ∫ x in (-1 : ℝ)..2, σ' x with hm1def
  have hm1a : κ - 4 / n ≤ m1 := by
    rw [hm1, hκ, div_sub_div_same]; exact div_le_div_of_nonneg_right hsum1 hn'.le
  have hm1b : m1 ≤ κ := by rw [hm1, hκ]; exact div_le_div_of_nonneg_right hsum2 hn'.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : 4 / (n : ℝ) ≤ 4 := by rw [div_le_iff₀ hn']; linarith
  -- the mass correction
  set lam := (12 - κ) / (12 - m1) with hlam
  have hden : 0 < 12 - m1 := by linarith
  have hlam1 : 1 - lam = (κ - m1) / (12 - m1) := by rw [hlam]; field_simp; ring
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hden.le
  have hlamle : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
  have hlamn : 1 - lam ≤ 1 / n := by
    rw [hlam1, div_le_div_iff₀ hden hn']
    have : (κ - m1) * n ≤ 4 := by
      have := mul_le_mul_of_nonneg_right (show κ - m1 ≤ 4 / n by linarith) hn'.le
      rwa [div_mul_cancel₀ _ hn'.ne'] at this
    nlinarith
  set σ'' : ℝ → ℝ := fun x => lam * σ' x + (1 - lam) * 4 with hσ''
  have hfeas : Feasible κ σ'' := by
    refine ⟨(hσ'm.const_mul lam).add measurable_const, fun x => ?_, ?_⟩
    · obtain ⟨h0, h4⟩ := hσ'b x
      constructor
      · simp only [hσ'']; nlinarith
      · simp only [hσ'']; nlinarith
    · simp only [hσ'']
      rw [intervalIntegral.integral_add ((ii_of_bdd hσ'm hσ'a _ _).const_mul lam)
        intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul, ← hm1def, hlam]
      field_simp; ring
  -- the gap inequality
  have hbdd : BddAbove {g | ∃ σ₁, Feasible κ σ₁ ∧ g = pairing (Pgrad σ) (fun x => σ₁ x - σ x)} := by
    refine ⟨3 * (252 * 8), ?_⟩
    rintro g ⟨σ₁, ⟨_, h1, _⟩, rfl⟩
    refine le_trans (le_abs_self _) (abs_integral_le_of_bdd fun x hx => ?_)
    rw [abs_mul]
    refine mul_le_mul (hPb x hx) ?_ (abs_nonneg _) (by norm_num)
    rw [abs_le]; constructor <;> linarith [(h1 x).1, (h1 x).2, (hσ x).1, (hσ x).2]
  have hgap : pairing P (fun x => σ'' x - σ x) ≤ gapF κ σ :=
    le_csSup hbdd ⟨σ'', hfeas, rfl⟩
  -- integrability facts
  have iP : IntervalIntegrable P volume (-1) 2 :=
    ii_of_bdd_on hPm hPb (le_refl _) (by norm_num) (le_refl _)
  have iPσ' : IntervalIntegrable (fun x => σ' x * P x) volume (-1) 2 :=
    ii_mul_on hσ'm hPm hσ'a hPb (le_refl _) (by norm_num) (le_refl _)
  have iσP : IntervalIntegrable (fun x => σ x * P x) volume (-1) 2 :=
    ii_mul_on hσm hPm hσb hPb (le_refl _) (by norm_num) (le_refl _)
  set X := ∫ x in (-1 : ℝ)..2, σ' x * P x with hX
  set Y := ∫ x in (-1 : ℝ)..2, σ x * P x with hY
  -- the pairing with the competitor
  have hpair : pairing P (fun x => σ'' x - σ x) =
      lam * X + (1 - lam) * 4 * (∫ x in (-1 : ℝ)..2, P x) - Y := by
    unfold pairing
    have e : (fun x => P x * (σ'' x - σ x)) =
        fun x => (lam * (σ' x * P x) + (1 - lam) * 4 * P x) - σ x * P x := by
      funext x; simp only [hσ'']; ring
    rw [e, intervalIntegral.integral_sub ((iPσ'.const_mul lam).add (iP.const_mul _)) iσP,
      intervalIntegral.integral_add (iPσ'.const_mul lam) (iP.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the energy identity
  have hA : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |2 * logPot indI x - 4 * logPot indO x| ≤ 108 := by
    intro x hx
    have h1 := abs_logPot_le measurable_indI (fun y => (indI_bounds y).1)
      (fun y => (indI_bounds y).2) hx
    have h2 := abs_logPot_le measurable_indO (fun y => (indO_bounds y).1)
      (fun y => (indO_bounds y).2) hx
    rw [abs_le] at *; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hAm : Measurable fun x => 2 * logPot indI x - 4 * logPot indO x :=
    ((measurable_logPot measurable_indI).const_mul 2).sub
      ((measurable_logPot measurable_indO).const_mul 4)
  have hYF : Y = Fenergy σ + pairing σ (logPot σ) := by
    unfold Fenergy pairing
    have i1 := ii_mul_on hσm hAm hσb hA (le_refl (-1 : ℝ)) (by norm_num) (le_refl 2)
    have i2 := ii_mul_on hσm (measurable_logPot hσm) hσb (fun x hx => abs_logPot_σ_le hσm hσ hx)
      (le_refl (-1 : ℝ)) (by norm_num) (le_refl 2)
    rw [hY, add_assoc, ← two_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add i1 (i2.const_mul 2)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hP, Pgrad]; ring
  -- the correction term
  have hcorr : |X - 4 * ∫ x in (-1 : ℝ)..2, P x| ≤ 3024 := by
    rw [hX, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iPσ'
      (iP.const_mul _)]
    have := abs_integral_le_of_bdd (C := 1008) (f := fun x => σ' x * P x - 4 * P x) fun x hx => by
      have e : σ' x * P x - 4 * P x = (σ' x - 4) * P x := by ring
      show |σ' x * P x - 4 * P x| ≤ 1008
      rw [e, abs_mul]
      have : |σ' x - 4| ≤ 4 := by
        rw [abs_le]; constructor <;> linarith [(hσ'b x).1, (hσ'b x).2]
      calc |σ' x - 4| * |P x| ≤ 4 * 252 := mul_le_mul this (hPb x hx) (abs_nonneg _) (by norm_num)
        _ = 1008 := by norm_num
    linarith
  have hXle : X ≤ gapF κ σ + Y + 3024 / n := by
    have hdecomp : X = pairing P (fun x => σ'' x - σ x) + Y +
        (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x) := by rw [hpair]; ring
    have h1 : (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x) ≤ 3024 / n := by
      have hl0 : 0 ≤ 1 - lam := by linarith
      calc (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x)
          ≤ (1 - lam) * 3024 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcorr) hl0
        _ ≤ 1 / n * 3024 := mul_le_mul_of_nonneg_right hlamn (by norm_num)
        _ = 3024 / n := by ring
    linarith
  have hLHS : ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
      s k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Pgrad σ x) = (n : ℝ) ^ 2 * X := by
    rw [show X = _ from hPσ', mul_sum]; refine sum_congr rfl fun k _ => by ring
  have hR : Fenergy σ + gapF κ σ + pairing σ (logPot σ) = Y + gapF κ σ := by rw [hYF]; ring
  rw [hLHS, hR]
  have : (n : ℝ) ^ 2 * (3024 / n) = 3024 * n := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hXle (sq_nonneg (n : ℝ))]

end Hankel2.ArchB
