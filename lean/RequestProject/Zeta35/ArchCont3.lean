import RequestProject.Zeta35.ArchShift3

/-!
# The discrete energy against the continuum profile (N, Theorem 4.1; port of P, Lemmas 6.3–6.4)

We work in the translated frame: the nodes `|k| ≤ 3n/2` of N become `k + n/2 ∈ [−n, 2n]`
(`Fam3PF.nodes n`), whose cells `[k/n, (k+1)/n]` tile `[−1, 2]`.  For the weight without zeros
`ln|h_k| = −4 ∑_{k' ≠ k} ln|k' − k|` (`LZ`).

* `LZ_le`: `LZ_k ≤ −4 ∑_m ln(|k − m| + 1) + 4 ln(4n)`;
* `nPh_ge`, `n2_int_Ph_ge`: lower bounds for `n Ph_σ` on a cell;
* `gZ_le`: `g_k = LZ_k + 2(B s̃)_k ≤ n² ∫_{J_k} Ph_σ + (2K − 12n) ln n + 300(1 + ln n)`;
* `gZ_le_crude`: `g_k ≤ 2K(2 + ln n)` at every node;
* **`EBZ_le_cont`**: for `κ = K/n ≤ 6`, every `σ` feasible on `[−3/2, 3/2]` and every real
  profile `0 ≤ s ≤ 4` with `∑ s = K`:
  `E_B(s) ≤ (K² − 12Kn) ln n + n² (F₃[σ] + gap₃(σ)) + 5000 n (1 + ln n)`.
-/

open MeasureTheory Finset Hankel2 Hankel2.ArchB

namespace Zeta35.Arch

/-- `ln|h_k| = −4 ∑_{k' ≠ k} ln|k' − k|` in the translated frame. -/
noncomputable def LZ (n : ℕ) (k : ℤ) : ℝ :=
  -4 * ∑ k' ∈ (Fam3PF.nodes n).erase k, Real.log |((k' - k : ℤ) : ℝ)|

theorem LZ_le {n : ℕ} (hn : 0 < n) {k : ℤ} (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    LZ n k ≤ -4 * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) +
      4 * Real.log (4 * n) := by
  have h := int_sum_ge hn hk
  have e : ∑ k' ∈ (Icc (-(n : ℤ)) (2 * n)).erase k, Real.log |((k' : ℝ) - k)| =
      ∑ k' ∈ (Fam3PF.nodes n).erase k, Real.log |((k' - k : ℤ) : ℝ)| := by
    simp only [Fam3PF.nodes]; push_cast; rfl
  rw [e] at h
  unfold LZ
  linarith

theorem LZ_nonpos (n : ℕ) (k : ℤ) : LZ n k ≤ 0 := by
  unfold LZ
  have : 0 ≤ ∑ k' ∈ (Fam3PF.nodes n).erase k, Real.log |((k' - k : ℤ) : ℝ)| := by
    refine sum_nonneg fun k' hk' => Real.log_nonneg ?_
    have hne : k' - k ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hk')
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
  linarith

theorem cav_one {n : ℕ} (hn : 0 < n) (m : ℤ) : cav (fun _ => (1 : ℝ)) n m = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cav
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  field_simp; ring

theorem n_int_one {n : ℕ} : (n : ℝ) * ∫ _y in (-1 : ℝ)..2, (1 : ℝ) = 3 * n := by
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring

/-- **Pointwise lower bound for `n Ph_σ` on the cell `J_k`.** -/
theorem nPh_ge {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, shf σ y = K) {k : ℤ}
    {x : ℝ} (hx : x ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    12 * n * Real.log n - 2 * K * Real.log n -
        4 * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) +
        2 * Wsum n (shf σ) k - 144 ≤ n * Ph σ x := by
  have hsm : Measurable (shf σ) := hσm.comp (measurable_id.sub measurable_const)
  have hO := logPot_upper (f := fun _ => (1 : ℝ)) (M := 1) measurable_const
    (fun _ => zero_le_one) (fun _ => by norm_num) hn hx
  have hS := logPot_lower (f := shf σ) (M := 4) hsm (fun y => (hσ _).1) (fun y => (hσ _).2)
    (fun y => by show |σ (y - 1 / 2)| ≤ 4; rw [abs_of_nonneg (hσ _).1]; exact (hσ _).2) hn hx
  rw [n_int_one] at hO
  simp only [cav_one hn, one_mul] at hO
  rw [hmass] at hS
  rw [Ph_eq]
  have e : (n : ℝ) * (-4 * logPot (fun _ => 1) x + 2 * logPot (shf σ) x) =
      -4 * (n * logPot (fun _ => 1) x) + 2 * (n * logPot (shf σ) x) := by ring
  rw [e]
  unfold Wsum
  linarith

/-- **Integrated lower bound**: `n² ∫_{J_k} Ph_σ ≥ …`. -/
theorem n2_int_Ph_ge {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, shf σ y = K) {k : ℤ}
    (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    12 * n * Real.log n - 2 * K * Real.log n -
        4 * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) +
        2 * Wsum n (shf σ) k - 144 ≤
      (n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Ph σ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hk1, hk2⟩ := cell_sub hn hk
  set L := 12 * n * Real.log n - 2 * K * Real.log n -
    4 * ∑ m ∈ Ico (-(n : ℤ)) (2 * n), Real.log (|((k - m : ℤ) : ℝ)| + 1) +
    2 * Wsum n (shf σ) k - 144
  have hint : IntervalIntegrable (Ph σ) volume ((k : ℝ) / n) (((k : ℝ) + 1) / n) :=
    ii_of_bdd_on (measurable_Ph hσm) (fun x hx => abs_Ph_le hσm hσ hx) hk1 (cell_le hn k) hk2
  have h := intervalIntegral.integral_mono_on (cell_le hn k) intervalIntegrable_const
    (hint.const_mul (n : ℝ)) (fun x hx => nPh_ge (K := K) hn hσm hσ hmass hx)
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at h
  have e : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by field_simp; ring
  rw [e] at h
  have : L = (n : ℝ) * (1 / n * L) := by field_simp
  rw [this, sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hn'.le

theorem log_four_mul_le {n : ℕ} (hn : 0 < n) : Real.log (4 * n) ≤ 2 + Real.log n := by
  rw [Real.log_mul (by norm_num) (by positivity)]
  have : Real.log 4 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / Real.exp 1 by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
    have he := Real.exp_one_gt_d9
    have : 4 / Real.exp 1 ≤ 4 / 2.7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith)
    linarith
  linarith

/-- **The gradient at a cell node**:
`g_k ≤ n² ∫_{J_k} Ph_σ + (2K − 12n) ln n + 300(1 + ln n)`. -/
theorem gZ_le {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) (hmass : (n : ℝ) * ∫ y in (-1 : ℝ)..2, shf σ y = K) {k : ℤ}
    (hk : k ∈ Ico (-(n : ℤ)) (2 * n)) :
    LZ n k + 2 * BwZ n (shf σ) k ≤
      (n : ℝ) ^ 2 * (∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Ph σ x) +
        (2 * K - 12 * n) * Real.log n + 300 * (1 + Real.log n) := by
  have hsm : Measurable (shf σ) := hσm.comp (measurable_id.sub measurable_const)
  have hkn : k ∈ Fam3PF.nodes n := by
    simp only [mem_Ico] at hk; simp only [Fam3PF.nodes, mem_Icc]; omega
  have h1 := LZ_le hn hk
  have h2 := BwZ_le hn hsm (fun x => hσ _) hkn
  have h3 := n2_int_Ph_ge (K := K) hn hσm hσ hmass hk
  have h4 := log_three_mul_le hn
  have h4' := log_four_mul_le hn
  have h5 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  nlinarith

theorem Bk_le_log_one_add_abs (d : ℝ) : Bk d ≤ Real.log (1 + |d|) := by
  unfold Bk
  have h : Real.log (1 + d ^ 2) ≤ Real.log ((1 + |d|) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [sq_abs d, abs_nonneg d])
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- **Crude bound at any node** (used for the last node `k = 2n`). -/
theorem gZ_le_crude {σ : ℝ → ℝ} {n : ℕ} (hn : 0 < n) (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    LZ n k + 2 * BwZ n (shf σ) k ≤
      2 * (n * ∫ y in (-1 : ℝ)..2, shf σ y) * (2 + Real.log n) := by
  have hsm : Measurable (shf σ) := hσm.comp (measurable_id.sub measurable_const)
  have hs : ∀ x, 0 ≤ shf σ x ∧ shf σ x ≤ 4 := fun x => hσ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := LZ_nonpos n k
  have hB : BwZ n (shf σ) k ≤ (n * ∫ y in (-1 : ℝ)..2, shf σ y) * (2 + Real.log n) := by
    unfold BwZ
    rw [← sum_wZ hn hsm hs, sum_mul]
    refine sum_le_sum fun m hm => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (wZ_nonneg hn hs m)
    refine (Bk_le_log_one_add_abs _).trans ?_
    refine (Real.log_le_log (by positivity) (?_ : 1 + |((k - m : ℤ) : ℝ)| ≤ 4 * n)).trans
      (log_four_mul_le hn)
    simp only [Fam3PF.nodes, mem_Icc] at hk hm
    have : |k - m| ≤ 3 * n := by rw [abs_le]; omega
    have h' : ((|k - m| : ℤ) : ℝ) ≤ ((3 * n : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at h'
    push_cast at h' ⊢; linarith
  linarith

/-- The explicit `O(n log n)` error. -/
noncomputable def errC3 (n : ℕ) : ℝ := 5000 * n * (1 + Real.log n)

theorem nodes_eq_insert' (n : ℕ) :
    Fam3PF.nodes n = insert (2 * (n : ℤ)) (Ico (-(n : ℤ)) (2 * n)) := by
  ext k; simp only [Fam3PF.nodes, mem_Icc, mem_insert, mem_Ico]; omega

/-- **The continuum bound for the discrete energy** (port of P, Lemmas 6.3–6.4, weight without
zeros, node interval `[−3/2, 3/2]` translated to `[−1, 2]`). -/
theorem EBZ_le_cont {σ : ℝ → ℝ} {n K : ℕ} (hn : 0 < n) (hF : Feasible3 ((K : ℝ) / n) σ)
    (hK : (K : ℝ) / n ≤ 6) (sZ : ℤ → ℝ) (hsZb : ∀ k, 0 ≤ sZ k ∧ sZ k ≤ 4)
    (hsK : ∑ k ∈ Fam3PF.nodes n, sZ k = K) :
    ∑ k ∈ Fam3PF.nodes n, sZ k * LZ n k +
        ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n, sZ k * sZ m * Bk ((k - m : ℤ) : ℝ) ≤
      ((K : ℝ) ^ 2 - 12 * K * n) * Real.log n +
        (n : ℝ) ^ 2 * (Fenergy3 σ + gap3 ((K : ℝ) / n) σ) + errC3 n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hFs := feasible_shf hF
  obtain ⟨hσm, hσ, hmass3⟩ := hF
  obtain ⟨hsm, hs, hmass⟩ := hFs
  have hmassK : (n : ℝ) * ∫ y in (-1 : ℝ)..2, shf σ y = K := by rw [hmass]; field_simp
  have hKn : (K : ℝ) ≤ 6 * n := by rwa [div_le_iff₀ hn'] at hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  set F := Fam3PF.nodes n with hFdef
  set w0 : ℤ → ℝ := fun k => wZ n (shf σ) k with hw0
  have hsumw0 : ∑ k ∈ F, w0 k = K := by
    simp only [hw0]; rw [sum_wZ hn hsm hs, hmassK]
  have hlin := quadratic_log_le_linearization F (fun k => (k : ℝ)) sZ w0 (by rw [hsK, hsumw0])
  have hB : ∀ k m : ℤ, Real.log (1 + ((k : ℝ) - m) ^ 2) / 2 = Bk ((k - m : ℤ) : ℝ) := by
    intro k m; simp only [Bk]; push_cast; rfl
  simp only [hB] at hlin
  set Q0 := ∑ k ∈ F, ∑ m ∈ F, wZ n (shf σ) k * wZ n (shf σ) m * Bk ((k - m : ℤ) : ℝ) with hQ0
  have hBw : ∀ k, ∑ m ∈ F, Bk ((k - m : ℤ) : ℝ) * w0 m = BwZ n (shf σ) k := fun k => rfl
  have hcross : ∑ k ∈ F, (sZ k - w0 k) * ∑ m ∈ F, Bk ((k - m : ℤ) : ℝ) * w0 m =
      ∑ k ∈ F, sZ k * BwZ n (shf σ) k - Q0 := by
    simp_rw [hBw, sub_mul, sum_sub_distrib]
    congr 1
    rw [hQ0]
    refine sum_congr rfl fun k _ => ?_
    unfold BwZ; rw [mul_sum]; refine sum_congr rfl fun m _ => by simp only [hw0]; ring
  rw [hcross] at hlin
  set G : ℤ → ℝ := fun k => LZ n k + 2 * BwZ n (shf σ) k with hG
  have hstep1 : ∑ k ∈ F, sZ k * LZ n k + ∑ k ∈ F, ∑ m ∈ F, sZ k * sZ m * Bk ((k - m : ℤ) : ℝ) ≤
      ∑ k ∈ F, sZ k * G k - Q0 := by
    have e : ∑ k ∈ F, sZ k * G k =
        ∑ k ∈ F, sZ k * LZ n k + 2 * ∑ k ∈ F, sZ k * BwZ n (shf σ) k := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      simp only [hG]; ring
    rw [e]
    linarith
  have hsplit : ∑ k ∈ F, sZ k * G k =
      sZ (2 * n) * G (2 * n) + ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k * G k := by
    rw [hFdef, nodes_eq_insert', sum_insert (by simp)]
  have hsumZ : sZ (2 * n) + ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k = K := by
    rwa [hFdef, nodes_eq_insert', sum_insert (by simp)] at hsK
  set S := ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k with hS
  have hS1 : (K : ℝ) - 4 ≤ S := by linarith [(hsZb (2 * n)).2]
  have hS2 : S ≤ K := by linarith [(hsZb (2 * n)).1]
  -- the last node
  have hlast : sZ (2 * n) * G (2 * n) ≤ 48 * n * (2 + Real.log n) := by
    have hg := gZ_le_crude hn hσm hσ (k := 2 * n)
      (by simp only [Fam3PF.nodes, mem_Icc]; omega)
    rw [hmassK] at hg
    have hB0 : 0 ≤ 2 * (K : ℝ) * (2 + Real.log n) := by positivity
    have h1 : sZ (2 * n) * G (2 * n) ≤ 4 * (2 * (K : ℝ) * (2 + Real.log n)) := by
      calc sZ (2 * n) * G (2 * n) ≤ sZ (2 * n) * (2 * (K : ℝ) * (2 + Real.log n)) :=
            mul_le_mul_of_nonneg_left hg (hsZb _).1
        _ ≤ 4 * (2 * (K : ℝ) * (2 + Real.log n)) :=
            mul_le_mul_of_nonneg_right (hsZb _).2 hB0
    have h3 : 2 * (K : ℝ) * (2 + Real.log n) ≤ 12 * n * (2 + Real.log n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  -- the interior nodes
  have hint : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k * G k ≤
      ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
        sZ k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Ph σ x) +
      S * ((2 * K - 12 * n) * Real.log n + 300 * (1 + Real.log n)) := by
    rw [hS, sum_mul, ← sum_add_distrib]
    refine sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (gZ_le hn hσm hσ hmassK hk) (hsZb k).1
    simp only [hG]; linarith
  have hP := P_bound_gen (σ := shf σ) (P := Ph σ) (C := 216) (G := gap3 ((K : ℝ) / n) σ) hn
    ⟨hsm, hs, hmass⟩ hK (measurable_Ph hσm) (fun x hx => abs_Ph_le hσm hσ hx)
    (fun σ' h' => pairing_Ph_le_gap3 hσm hσ h') sZ hsZb hS1 hS2
  have hQ := Q_bound hn hsm hs hmassK
  have hFe := Fenergy3_eq hσm hσ
  have hl3 := log_three_mul_le hn
  have hA : S * ((2 * K - 12 * n) * Real.log n) ≤
      (2 * (K : ℝ) ^ 2 - 12 * K * n) * Real.log n + 48 * n * Real.log n := by
    have h1 : 0 ≤ (S - (K - 4)) * ((12 * n - 2 * K) * Real.log n) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hL)
    nlinarith [h1, mul_nonneg hK0 hL]
  have hA2 : S * (300 * (1 + Real.log n)) ≤ 1800 * n * (1 + Real.log n) := by
    have : S ≤ 6 * n := by linarith
    have := mul_le_mul_of_nonneg_right this (show 0 ≤ 300 * (1 + Real.log n) by positivity)
    linarith
  have hA3 : 8 * (K : ℝ) * (1 + Real.log (3 * n)) ≤ 144 * n * (1 + Real.log n) := by
    have : 8 * (K : ℝ) * (1 + Real.log (3 * n)) ≤ 8 * (6 * n) * (3 + Real.log n) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 * n
        by linarith)]) (by positivity)
    linarith [mul_nonneg hn'.le hL]
  have hQ0eq : Q0 = ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n,
      wZ n (shf σ) k * wZ n (shf σ) m * Bk ((k - m : ℤ) : ℝ) := rfl
  rw [← hQ0eq] at hQ
  unfold errC3
  have hnL0 := mul_nonneg hn'.le hL
  rw [hFe]
  linarith [hstep1, hsplit, hlast, hint, hP, hQ, hA, hA2, hA3]

end Zeta35.Arch
