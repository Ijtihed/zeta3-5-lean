import RequestProject.Zeta35.Main

/-!
# Round 2 assembly: the corrected archimedean field

The field `Zeta35Inputs.arch` is false whenever `hankelPoly n K = 0` (Lean has `Real.log 0 = 0`,
while N, Theorem 4.1 is meant with `ln 0 = −∞`).  `Zeta35InputsR2` is `Zeta35Inputs` with the
single change that `arch` carries the extra hypothesis `hankelPoly n K ≠ 0`.  The assembly uses
`arch` only at `K = 4(3n+1−ℓ)`, where `nonvanishing` gives `Δ_K(r) ≠ 0`, hence `Δ_K ≠ 0`.
-/

open Polynomial Finset Filter Topology

namespace Zeta35

open Hankel2

/-- **The inputs of N still missing (round 2)**: as `Zeta35Inputs`, except that `arch` is only
required for `Δ_K ≠ 0` (N, Theorem 4.1 with the convention `ln 0 = −∞`). -/
structure Zeta35InputsR2 where
  /-- (i) **N, Theorem 3.1 (3-adic decay)**. -/
  decay : ∀ n K : ℕ, Even n → 2 ≤ K → K ≤ 6 * n + 2 →
    ‖aeval (zeta3 5) (hankelPoly n K)‖ ≤ (3 : ℝ) ^ (-decayExp n K)
  /-- (ii) **N, Theorem 4.1 (archimedean size)** for `κ = K/n ∈ [5.9, 6]`, profile `σ_κ ≡ κ/3`,
  for `Δ_K ≠ 0`. -/
  arch : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
    (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → hankelPoly n K ≠ 0 →
      Real.log (l1 (hankelPoly n K)) ≤
        (((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy3 (sigmaK ((K : ℝ) / n)) +
              gap3 ((K : ℝ) / n) (sigmaK ((K : ℝ) / n)))
          + ε * (n : ℝ) ^ 2
  /-- The `κ`-dependent part `rest(κ)` of `c(κ)`. -/
  cRest : ℝ → ℝ
  /-- (iii-b) **N, Theorem 5.1**. -/
  thm_5_1 : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertens3Sum Y - Real.log Y) atTop (𝓝 M₀) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
      (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 3) →
        ∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.logb 2 ℓ ≤
          ((K : ℝ) / n) * (12 - (K : ℝ) / n) * (n : ℝ) ^ 2 * Real.logb 2 n
            + cConst M₀ cRest ((K : ℝ) / n) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2
  /-- (iii-c) **The certificate bound** `c(κ) ≤ 71.2` on `[5.9, 6]`. -/
  table_c : ∀ κ : ℝ, 5.9 ≤ κ → κ ≤ 6 → cConst mertens3Const cRest κ ≤ 71.2
  /-- (iv) **N, Theorem 6.2 (non-vanishing)**. -/
  nonvanishing : ∀ n ℓ : ℕ, Even n → ℓ.Prime → R n < ℓ → 7 ≤ ℓ → 3 * (ℓ - R n) ≤ ℓ →
    ∀ r : ℚ, ¬ ℓ ∣ r.den → (hankelPoly n (4 * (3 * n + 1 - ℓ))).eval r ≠ 0

/-- Every `Zeta35Inputs` gives a `Zeta35InputsR2` (the new `arch` is weaker). -/
def Zeta35Inputs.toR2 (I : Zeta35Inputs) : Zeta35InputsR2 where
  decay := I.decay
  arch ε hε := by
    obtain ⟨N, hN⟩ := I.arch ε hε
    exact ⟨N, fun n K h1 h2 h3 h4 _ => hN n K h1 h2 h3 h4⟩
  cRest := I.cRest
  thm_5_1 := I.thm_5_1
  table_c := I.table_c
  nonvanishing := I.nonvanishing

/-- **`ζ₃(5)` is irrational**, from the corrected inputs `Zeta35InputsR2` (paper N, §7). -/
theorem zeta3_five_irrational_R2 (I : Zeta35InputsR2) : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) := by
  intro r hr
  obtain ⟨NB, hNB⟩ := I.arch (1 / 10) (by norm_num)
  obtain ⟨NT, hNT⟩ := I.thm_5_1 mertens3Const tendsto_mertens3 (1 / 10) (by norm_num)
  obtain ⟨N0, hN0⟩ := aux_prime3 r.den r.den_pos
  have hB1 : (1 : ℝ) ≤ (denNumMax r : ℝ) := by
    have : (1 : ℤ) ≤ denNumMax r := le_max_of_le_right (by exact_mod_cast r.den_pos)
    exact_mod_cast this
  have hlB : 0 ≤ Real.logb 2 (denNumMax r) := Real.logb_nonneg (by norm_num) hB1
  obtain ⟨NL, hNL⟩ := eventually_lower_order3 100 (6 * Real.logb 2 (denNumMax r)) (by norm_num)
    (by positivity)
  set m : ℕ := NB + NT + N0 + NL + 1000 with hm_def
  set n : ℕ := 2 * m with hn_def
  have hn : Even n := ⟨m, by omega⟩
  have hn1000 : (1000 : ℝ) ≤ n := by
    have : 1000 ≤ n := by omega
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by linarith
  have hnNB : NB ≤ n := by omega
  have hnNT : NT ≤ n := by omega
  have hnN0 : N0 ≤ n := by omega
  have hnNL : NL ≤ n := by omega
  have hRn : R n = 3 * m := by rw [R, hn_def]; omega
  clear_value n m
  obtain ⟨ℓ, hℓ, hℓlo, hℓhi, hℓ11, hℓb⟩ := hN0 n hnN0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- the admissibility conditions, in `ℕ`
  have hlo : 3 * m + 1 ≤ ℓ := by
    have : ((3 * m : ℕ) : ℝ) < (ℓ : ℝ) := by push_cast; rw [hn_def] at hℓlo; push_cast at hℓlo; linarith
    exact_mod_cast this
  have hhi : 25 * ℓ ≤ 76 * m := by
    have : ((25 * ℓ : ℕ) : ℝ) ≤ ((76 * m : ℕ) : ℝ) := by
      push_cast; rw [hn_def] at hℓhi; push_cast at hℓhi; linarith
    exact_mod_cast this
  set K : ℕ := 4 * (3 * n + 1 - ℓ) with hK_def
  have hK6 : K ≤ 6 * n := by omega
  have hKlo : 59 * n ≤ 10 * K := by omega
  have hK2 : 2 ≤ K := by omega
  have hKK : K = 4 * (3 * n + 1 - ℓ) := hK_def
  clear_value K
  set κ : ℝ := (K : ℝ) / n with hκ_def
  have hKκ : (K : ℝ) = κ * n := by rw [hκ_def]; field_simp
  have hκ1 : (5.9 : ℝ) ≤ κ := by
    rw [hκ_def, le_div_iff₀ hnR]
    have : ((59 * n : ℕ) : ℝ) ≤ ((10 * K : ℕ) : ℝ) := by exact_mod_cast hKlo
    push_cast at this; linarith
  have hκ2 : κ ≤ 6 := by
    rw [hκ_def, div_le_iff₀ hnR]
    have : ((K : ℕ) : ℝ) ≤ ((6 * n : ℕ) : ℝ) := by exact_mod_cast hK6
    push_cast at this; linarith
  -- non-vanishing (N, Theorem 6.2)
  have hΔr : (hankelPoly n K).eval r ≠ 0 := by
    rw [hKK]
    exact I.nonvanishing n ℓ hn hℓ (by omega) (by omega) (by omega) r hℓb
  have hdeg := natDegree_hankelPoly_le n K
  have hΔK0 : hankelPoly n K ≠ 0 := fun h => hΔr (by rw [h, eval_zero])
  have hLB := hNB n K hnNB hn hκ1 hκ2 hΔK0
  have hTsum := hNT n K hnNT hn hκ1 hκ2
  have hLT : ∀ q : ℕ, q.Prime → q ≠ 3 → negTop (gaussVal q (hankelPoly n K)) ≤ TP q n K :=
    fun q hq hq3 => tree_field_holds n K q hq hq3
  have hA0 := I.decay n K hn hK2 (by omega)
  rw [hr] at hA0
  have hdecay := decayExp_ge n K hK2
  generalize hankelPoly n K = Δ at hΔr hdeg hLB hLT hA0
  rw [← hκ_def] at hLB hTsum
  have hΔ0 : Δ ≠ 0 := fun h => hΔr (by rw [h, eval_zero])
  have hΔζ : aeval (r : ℚ_[3]) Δ = ((Δ.eval r : ℚ) : ℚ_[3]) := by
    rw [show (r : ℚ_[3]) = algebraMap ℚ ℚ_[3] r from rfl, aeval_algebraMap_apply,
      coe_aeval_eq_eval]
    rfl
  have hne : aeval (r : ℚ_[3]) Δ ≠ 0 := by rw [hΔζ]; exact_mod_cast hΔr
  -- the criterion (N, Lemma 2.3)
  obtain ⟨S, E, hSE, hcrit⟩ := pden_criterion 3 Δ hdeg r hne
  have hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3 := fun q hq => ⟨(hSE q hq).1, (hSE q hq).2.1⟩
  have hTS := hTsum S hS
  have hEle : ∀ q ∈ S, (E q : ℝ) ≤ TPplus q n K := by
    intro q hq
    obtain ⟨hqp, hq3, hEq⟩ := hSE q hq
    obtain ⟨g, hg⟩ := gaussVal_eq_coe' hΔ0 q
    have hT := hLT q hqp hq3
    rw [hg] at hT
    have h1 := hEq g hg
    have h2 := max_neg_le_TPplus hT
    exact_mod_cast h1.trans h2
  -- (iii) the denominators, in bits
  have hdpos : 0 < ∏ q ∈ S, (q : ℝ) ^ E q :=
    Finset.prod_pos fun q hq => pow_pos (by exact_mod_cast (hS q hq).1.pos) _
  have hdlog : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) ≤
      ∑ q ∈ S, (TPplus q n K : ℝ) * Real.logb 2 q := by
    rw [Real.logb_prod S _
      (fun q hq => pow_ne_zero _ (by exact_mod_cast (hS q hq).1.ne_zero))]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Real.logb_pow]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hS q hq).1.one_lt.le
    exact mul_le_mul_of_nonneg_right (hEle q hq) (Real.logb_nonneg (by norm_num) hq1)
  have hc := I.table_c κ hκ1 hκ2
  have hT2 : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) ≤
      κ * (12 - κ) * (n : ℝ) ^ 2 * Real.logb 2 n + 71.2 * (n : ℝ) ^ 2 + 1 / 10 * (n : ℝ) ^ 2 := by
    have h2 : cConst mertens3Const I.cRest κ * (n : ℝ) ^ 2 ≤ 71.2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith [hdlog.trans hTS]
  -- (ii) the archimedean size, in bits
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  have hl1pos : 0 < l1 Δ := l1_pos' hΔ0
  have hl3 : Real.log 3 ≤ 1.5 := by have := log_three_bounds.2; linarith
  have hFd := Fdag_sigmaK_le (κ := κ) (by linarith) hκ2 hl3
  set Fd : ℝ := (54 - 36 * Real.log 3) / Real.log 2 + 3 * κ * (4 - 2 * κ / 3) with hFd_def
  have hB2 : Real.logb 2 (l1 Δ) ≤
      (κ ^ 2 - 12 * κ) * (n : ℝ) ^ 2 * Real.logb 2 n + Fd * (n : ℝ) ^ 2 +
        3 / 20 * (n : ℝ) ^ 2 := bits_B3 hFd hLB
  -- (i) the decay, in bits
  have hnormpos : 0 < ‖aeval (r : ℚ_[3]) Δ‖ := norm_pos_iff.mpr hne
  have hA2 : Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ ≤
      -(Real.logb 2 3 * (12 * κ - κ ^ 2 / 4) * (n : ℝ) ^ 2) +
        100 * (n : ℝ) * (1 + Real.logb 2 n) := decay_bits hnormpos hK2 hK6 hA0
  -- the height of `r`
  have hBK : Real.logb 2 ((denNumMax r : ℝ) ^ K) ≤ 6 * Real.logb 2 (denNumMax r) * n := by
    rw [Real.logb_pow]
    have : (K : ℝ) ≤ 6 * n := by
      have : ((K : ℕ) : ℝ) ≤ ((6 * n : ℕ) : ℝ) := by exact_mod_cast hK6
      push_cast at this; linarith
    calc (K : ℝ) * Real.logb 2 (denNumMax r) ≤ (6 * n) * Real.logb 2 (denNumMax r) :=
          mul_le_mul_of_nonneg_right this hlB
      _ = 6 * Real.logb 2 (denNumMax r) * n := by ring
  -- the margin
  have hmargin := budget (c := 71.2) hκ1 hκ2 le_rfl
  have hNLn := hNL n hnNL
  have hN2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsum : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) + Real.logb 2 (l1 Δ) +
      Real.logb 2 ((denNumMax r : ℝ) ^ K) + Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ < 0 :=
    assembly_arith3 hN2 hT2 hB2 hBK hA2 (by linarith [hmargin]) (by linarith [hNLn])
  -- assemble: the product in the criterion is `< 1`
  have hBKpos : 0 < (denNumMax r : ℝ) ^ K := pow_pos (by linarith) _
  have hYpos : 0 < (∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K *
      ‖aeval (r : ℚ_[3]) Δ‖ := by positivity
  have hlogY : Real.logb 2 ((∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K *
      ‖aeval (r : ℚ_[3]) Δ‖) = Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) + Real.logb 2 (l1 Δ) +
      Real.logb 2 ((denNumMax r : ℝ) ^ K) + Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ := by
    rw [Real.logb_mul (by positivity) hnormpos.ne', Real.logb_mul (by positivity)
      hBKpos.ne', Real.logb_mul hdpos.ne' hl1pos.ne']
  rw [← hlogY, Real.logb_neg_iff (by norm_num) hYpos] at hsum
  exact absurd hcrit (not_le.mpr hsum)

end Zeta35
