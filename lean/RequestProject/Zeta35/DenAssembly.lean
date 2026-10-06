import RequestProject.Zeta35.DenSmallSum
import RequestProject.Zeta35.DenCertC
import RequestProject.Zeta35.PrimeInputs

/-!
# Denominators: **N, Theorem 5.1** (assembly; W §3, Thm 3.9; P §8.5)

With `rest(κ) = stepBound + 3κ/20 + 2/400` (`cRest35`, `stepBound` the kernel-checked step sum of
the certificate), for every `ε > 0` and all large even `n`, `κ = K/n ∈ [5.9, 6]`, and every set
`S` of primes `ℓ ≠ 3`:

  `∑_{ℓ ∈ S} max(T_ℓ, 0) log₂ ℓ ≤ κ(12 − κ) n² log₂ n + c(κ) n² + ε n²`,
  `c(κ) = [κ(12 − κ)(M₀ − ln 20) + rest(κ)] / ln 2`  (**`thm_5_1_holds`**).

Assembly: primes `ℓ ≤ n/20` by Lemma A1 / the single-level bound (`sum_small_le3`; main term
`K(12n + 4 − K) · mertens3Sum(n/20)`, Lemma A1 errors `O(n^{3/2} log n)`, single-level errors
`3K θ(n/20) + 4 ∑ ℓ ln ℓ ≤ (3κ/20 + 2/400 + o(1)) n²`); primes `ℓ > n/20` by the checked
certificate (`sum_large_le3`, `cells_bound`: `max(T_ℓ, 0) ≤ n h + E` on each subcell and
`θ(b n) − θ(a n) = (b − a) n + o(n)`).
-/

open Filter Topology Finset Chebyshev

namespace Zeta35.Den

/-- The `κ`-dependent part `rest(κ)` of `c(κ)`: the certified step sum plus `3κ/20 + 2/400`. -/
noncomputable def cRest35 (κ : ℝ) : ℝ := (stepBound : ℝ) + 3 * κ / 20 + 2 / 400

/-- `∑_cells h`, a fixed constant of the certificate. -/
noncomputable def Hsum : ℝ := cellSum (fun _ r => (r.2.2.1 : ℝ)) (1 / 20) certL

theorem h_nonneg_of_mem {c : ℚ × SubRec} (hc : c ∈ cells (1 / 20) certL) : (0 : ℝ) ≤ c.2.2.2.1 := by
  have := (subOK_sound (subOK_of_mem_cells certL_blk.1 c hc)).2.2.2.1
  exact_mod_cast this

theorem Hsum_nonneg : 0 ≤ Hsum := by
  have h := cellSum_le (fun _ _ => (0 : ℝ)) (fun _ r => (r.2.2.1 : ℝ)) certL (1 / 20)
    (fun c hc => h_nonneg_of_mem hc)
  have h0 := cellSum_mul 0 (fun _ _ => (1 : ℝ)) certL (1 / 20)
  simp only [zero_mul] at h0
  unfold Hsum; linarith

/-- **Primes `ℓ > n/20`** via the checked certificate. -/
theorem sum_large_le3 {n K : ℕ} (hn : Even n) (hn0 : 1800 < n) (hK : K ≤ 6 * n) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime) :
    ∑ ℓ ∈ S.filter (fun ℓ => ¬ 20 * ℓ ≤ n), (TPplus ℓ n K : ℝ) * Real.log ℓ ≤
      cellSum (fun a r => ((n : ℝ) * r.2.2.1 + Ecst) * (θ ((r.1 : ℝ) * n) - θ ((a : ℝ) * n)))
        (1 / 20) certL := by
  classical
  obtain ⟨hch, hlast, -⟩ := certL_blk
  have hn0' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set S2 := S.filter (fun ℓ => ¬ 20 * ℓ ≤ n)
  rw [← sum_filter_add_sum_filter_not S2 (fun ℓ => ℓ ≤ 5 * n)]
  have hzero : ∑ ℓ ∈ S2.filter (fun ℓ => ¬ ℓ ≤ 5 * n), (TPplus ℓ n K : ℝ) * Real.log ℓ = 0 := by
    refine sum_eq_zero fun ℓ hℓ => ?_
    simp only [S2, mem_filter] at hℓ
    haveI : Fact ℓ.Prime := ⟨hS ℓ hℓ.1.1⟩
    rw [TPplus_eq_zero_of_large3 (by omega) K]; simp
  rw [hzero, add_zero]
  set f' : ℕ → ℝ := fun p => if p.Prime then (TPplus p n K : ℝ) * Real.log p else 0
  have hPf : ∑ ℓ ∈ S2.filter (fun ℓ => ℓ ≤ 5 * n), (TPplus ℓ n K : ℝ) * Real.log ℓ =
      ∑ ℓ ∈ S2.filter (fun ℓ => ℓ ≤ 5 * n), f' ℓ := by
    refine sum_congr rfl fun ℓ hℓ => ?_
    simp only [S2, mem_filter] at hℓ
    simp only [f', if_pos (hS ℓ hℓ.1.1)]
  rw [hPf]
  refine sum_le_cellSum (n : ℝ) f' _ certL (1 / 20) hch ?_ _ ?_
  · intro c hc Q hQ
    obtain ⟨ha20, hab, hb5⟩ := mem_cells_ge hch c hc
    have hok := subOK_of_mem_cells hch c hc
    have hh := h_nonneg_of_mem hc
    have hcoef : 0 ≤ (n : ℝ) * c.2.2.2.1 + Ecst := by
      have : (0 : ℝ) ≤ Ecst := by unfold Ecst; positivity
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hh) this
    have ha20' : (1 / 20 : ℝ) ≤ c.1 := by
      have := (Rat.cast_le (K := ℝ)).2 ha20; push_cast at this; exact this
    rw [← sum_filter_add_sum_filter_not Q Nat.Prime]
    have hnp : ∑ p ∈ Q.filter (fun p => ¬ p.Prime), f' p = 0 :=
      sum_eq_zero fun p hp => by simp only [f', if_neg (mem_filter.1 hp).2]
    rw [hnp, add_zero]
    calc ∑ p ∈ Q.filter Nat.Prime, f' p
        ≤ ∑ p ∈ Q.filter Nat.Prime, ((n : ℝ) * c.2.2.2.1 + Ecst) * Real.log p := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter] at hp
          simp only [f', if_pos hp.2]
          obtain ⟨hq1, hq2⟩ := hQ p hp.1
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          exact TPplus_le_cell hn hn0 hK hp.2 hok ha20' (by rw [lt_div_iff₀ hn0']; linarith)
            (by rw [div_le_iff₀ hn0']; linarith)
      _ = ((n : ℝ) * c.2.2.2.1 + Ecst) * ∑ p ∈ Q.filter Nat.Prime, Real.log p := by rw [mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          refine Hankel2.sum_log_le_theta_sub _ ?_ fun p hp => ?_
          · have : (c.1 : ℝ) ≤ c.2.1 := by exact_mod_cast hab.le
            exact mul_le_mul_of_nonneg_right this hn0'.le
          · rw [mem_filter] at hp
            exact ⟨hp.2, (hQ p hp.1).1, (hQ p hp.1).2⟩
  · intro p hp
    simp only [S2, mem_filter] at hp
    rw [hlast]
    refine ⟨?_, ?_⟩
    · have : (n : ℝ) < 20 * p := by exact_mod_cast (show n < 20 * p by omega)
      push_cast; linarith
    · have : (p : ℝ) ≤ 5 * n := by exact_mod_cast hp.2
      push_cast; linarith

/-- **The cells**: `∑_cells (n h + E)(θ(b n) − θ(a n)) ≤ stepBound n² + 10 δ Hsum n² +
E((1 + δ) 5n + C₁)` once `|θ(y) − y| ≤ δ y` for `y ≥ n/20`. -/
theorem cells_bound {n : ℕ} {δ C1 : ℝ} (hn : 0 < (n : ℝ)) (hδ : 0 ≤ δ)
    (hθa : ∀ y, (n : ℝ) / 20 ≤ y → |θ y - y| ≤ δ * y)
    (hθu : ∀ y, 0 ≤ y → θ y ≤ (1 + δ) * y + C1) :
    cellSum (fun a r => ((n : ℝ) * r.2.2.1 + Ecst) * (θ ((r.1 : ℝ) * n) - θ ((a : ℝ) * n)))
        (1 / 20) certL ≤
      (stepBound : ℝ) * (n : ℝ) ^ 2 + 10 * δ * Hsum * (n : ℝ) ^ 2 + Ecst * ((1 + δ) * (5 * n) + C1) := by
  obtain ⟨hch, hlast, hstep⟩ := certL_blk
  have hsplit : (fun (a : ℚ) (r : SubRec) => ((n : ℝ) * r.2.2.1 + Ecst) *
      (θ ((r.1 : ℝ) * n) - θ ((a : ℝ) * n))) = fun (a : ℚ) (r : SubRec) =>
        (n : ℝ) * (r.2.2.1 * (θ ((r.1 : ℝ) * n) - θ ((a : ℝ) * n))) +
          ((fun x : ℚ => Ecst * θ ((x : ℝ) * n)) r.1 - (fun x : ℚ => Ecst * θ ((x : ℝ) * n)) a) := by
    funext a r; ring
  rw [hsplit, cellSum_add, cellSum_mul, cellSum_telescope (fun x : ℚ => Ecst * θ ((x : ℝ) * n)),
    hlast]
  simp only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_one]
  -- the `E` part
  have hE0 : (0 : ℝ) ≤ Ecst := by unfold Ecst; positivity
  have hθ0 : 0 ≤ θ ((1 / 20 : ℝ) * n) := theta_nonneg _
  have hθ5 : θ ((5 : ℝ) * n) ≤ (1 + δ) * (5 * n) + C1 := hθu _ (by positivity)
  have hEpart : Ecst * θ ((5 : ℝ) * n) - Ecst * θ ((1 / 20 : ℝ) * n) ≤
      Ecst * ((1 + δ) * (5 * n) + C1) := by
    have := mul_le_mul_of_nonneg_left hθ5 hE0
    have := mul_nonneg hE0 hθ0
    linarith
  -- the main part
  have hcell : ∀ c ∈ cells (1 / 20) certL,
      (c.2.2.2.1 : ℝ) * (θ ((c.2.1 : ℝ) * n) - θ ((c.1 : ℝ) * n)) ≤
        (n : ℝ) * ((c.2.2.2.1 : ℝ) * ((c.2.1 : ℝ) - c.1)) + (10 * δ * n) * (c.2.2.2.1 : ℝ) := by
    intro c hc
    obtain ⟨ha20, hab, hb5⟩ := mem_cells_ge hch c hc
    rw [hlast] at hb5
    have hh := h_nonneg_of_mem hc
    have ha20' : (1 / 20 : ℝ) ≤ c.1 := by
      have := (Rat.cast_le (K := ℝ)).2 ha20; push_cast at this; exact this
    have hab' : (c.1 : ℝ) < c.2.1 := by exact_mod_cast hab
    have hb5' : (c.2.1 : ℝ) ≤ 5 := by
      have := (Rat.cast_le (K := ℝ)).2 hb5; push_cast at this; exact this
    have v1 := mul_le_mul_of_nonneg_right ha20' hn.le
    have v2 := mul_le_mul_of_nonneg_right hab'.le hn.le
    have u1 := (abs_le.1 (hθa ((c.2.1 : ℝ) * n) (by linarith))).2
    have u2 := (abs_le.1 (hθa ((c.1 : ℝ) * n) (by linarith))).1
    have hdiff : θ ((c.2.1 : ℝ) * n) - θ ((c.1 : ℝ) * n) ≤ ((c.2.1 : ℝ) - c.1) * n + 10 * δ * n := by
      have : δ * ((c.2.1 : ℝ) * n) + δ * ((c.1 : ℝ) * n) ≤ 10 * δ * n := by
        have : δ * n * ((c.2.1 : ℝ) + c.1) ≤ δ * n * 10 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left hdiff hh
    linarith
  have hmain := cellSum_le (fun a r => (r.2.2.1 : ℝ) * (θ ((r.1 : ℝ) * n) - θ ((a : ℝ) * n)))
    (fun a r => (n : ℝ) * ((r.2.2.1 : ℝ) * ((r.1 : ℝ) - a)) + (10 * δ * n) * (r.2.2.1 : ℝ))
    certL (1 / 20) hcell
  rw [cellSum_add, cellSum_mul, cellSum_mul, cellSum_stepSum] at hmain
  have hstep' : ((stepSum (1 / 20) certL : ℚ) : ℝ) ≤ stepBound := by exact_mod_cast hstep
  have hHs : cellSum (fun _ r => (r.2.2.1 : ℝ)) (1 / 20) certL = Hsum := rfl
  rw [hHs] at hmain
  have h1 : (n : ℝ) * (n * ((stepSum (1 / 20) certL : ℚ) : ℝ) + 10 * δ * n * Hsum) ≤
      (stepBound : ℝ) * (n : ℝ) ^ 2 + 10 * δ * Hsum * (n : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hstep' (by positivity : (0 : ℝ) ≤ n * n)
    linarith
  have h2 := mul_le_mul_of_nonneg_left hmain hn.le
  linarith

theorem kappa_bound (κ : ℝ) : κ * (12 - κ) ≤ 36 := by nlinarith [sq_nonneg (κ - 6)]

/-- `log(5n) ≤ δ √n` for all large `n`. -/
theorem log5_le_eps_sqrt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log (5 * n) ≤ δ * Real.sqrt n := by
  obtain ⟨N, hN⟩ := Hankel2.log_le_eps_sqrt (δ := δ / 2) (by positivity)
  refine ⟨N + 1, fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h := hN n (by omega)
  have h4 : Real.log (5 * n) ≤ Real.log (4 * n) + Real.log 4 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have h44 : Real.log 4 ≤ Real.log (4 * n) := Real.log_le_log (by norm_num) (by nlinarith)
  linarith

/-- `−γ − ½ ln 3 − ln 20 ≤ −1`. -/
theorem mertens3Const_sub_le : mertens3Const - Real.log 20 ≤ -1 := by
  unfold mertens3Const
  have h20 : 1 < Real.log 20 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have := Real.one_half_lt_eulerMascheroniConstant
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  linarith

/-- The single-level error terms: `3K θ(n/20) + 4 ∑_{ℓ ≤ n/20} ℓ ln ℓ`. -/
theorem single_errors_le {n K : ℕ} {κ δ C1 C2 : ℝ} (hn0 : 0 < (n : ℝ)) (hKk : (K : ℝ) = κ * n)
    (hκ2 : κ ≤ 6) (hδ : 0 ≤ δ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hθu : ∀ y, 0 ≤ y → θ y ≤ (1 + δ) * y + C1)
    (hpl : ∀ X : ℝ, 0 ≤ X → ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime, (p : ℝ) * Real.log p ≤
        (1 / 2 + 2 * δ) * X ^ 2 + C2 * X) :
    ∑ ℓ ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ ≤
      3 * κ / 20 * (n : ℝ) ^ 2 + 2 / 400 * (n : ℝ) ^ 2 + δ * (n : ℝ) ^ 2 + (18 * C1 + C2 / 5) * n := by
  set P20 := (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime
  have hκ0 : 0 ≤ κ := by
    by_contra h; push_neg at h
    have : (K : ℝ) < 0 := by rw [hKk]; exact mul_neg_of_neg_of_pos h hn0
    linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have e : ∑ ℓ ∈ P20, (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ
      = 3 * (K : ℝ) * ∑ ℓ ∈ P20, Real.log ℓ + 4 * ∑ ℓ ∈ P20, (ℓ : ℝ) * Real.log ℓ := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun p _ => by ring
  rw [e]
  have hth : ∑ ℓ ∈ P20, Real.log ℓ ≤ θ ((n : ℝ) / 20) := by
    have := Hankel2.sum_log_le_theta_sub P20 (x := 0) (y := (n : ℝ) / 20) (by positivity)
      (fun p hp => by
        simp only [P20, mem_filter, mem_range] at hp
        refine ⟨hp.2, by exact_mod_cast hp.2.pos, ?_⟩
        exact (Nat.le_floor_iff (by positivity)).1 (Nat.lt_succ_iff.1 hp.1))
    rwa [theta_eq_zero_of_lt_two (x := 0) (by norm_num), sub_zero] at this
  have hθ20 := hθu ((n : ℝ) / 20) (by positivity)
  have hpl20 := hpl ((n : ℝ) / 20) (by positivity)
  have s1 : 3 * (K : ℝ) * ∑ ℓ ∈ P20, Real.log ℓ ≤ 3 * (K : ℝ) * ((1 + δ) * ((n : ℝ) / 20) + C1) :=
    mul_le_mul_of_nonneg_left (hth.trans hθ20) (by positivity)
  have s2 : 3 * (K : ℝ) * ((1 + δ) * ((n : ℝ) / 20) + C1) ≤
      3 * κ / 20 * (n : ℝ) ^ 2 + 18 / 20 * δ * (n : ℝ) ^ 2 + 18 * C1 * n := by
    rw [hKk]
    have a1 : κ * ((n : ℝ) ^ 2 * δ) ≤ 6 * ((n : ℝ) ^ 2 * δ) :=
      mul_le_mul_of_nonneg_right hκ2 (by positivity)
    have a2 : κ * (n * C1) ≤ 6 * (n * C1) := mul_le_mul_of_nonneg_right hκ2 (by positivity)
    linarith
  have : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
  have : 0 ≤ C2 * (n : ℝ) := by positivity
  linarith

/-- **All primes `ℓ > n/20`**: `∑ max(T_ℓ, 0) ln ℓ ≤ stepBound n² + 10 δ Hsum n² + E((1 + δ) 5n + C₁)`. -/
theorem large_total_le {n K : ℕ} (hn : Even n) (hn0 : 1800 < n) (hK : K ≤ 6 * n) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime) {δ C1 : ℝ} (hδ : 0 ≤ δ)
    (hθa : ∀ y, (n : ℝ) / 20 ≤ y → |θ y - y| ≤ δ * y)
    (hθu : ∀ y, 0 ≤ y → θ y ≤ (1 + δ) * y + C1) :
    ∑ ℓ ∈ S.filter (fun ℓ => ¬ 20 * ℓ ≤ n), (TPplus ℓ n K : ℝ) * Real.log ℓ ≤
      (stepBound : ℝ) * (n : ℝ) ^ 2 + 10 * δ * Hsum * (n : ℝ) ^ 2 + Ecst * ((1 + δ) * (5 * n) + C1) :=
  (sum_large_le3 hn hn0 hK S hS).trans
    (cells_bound (by exact_mod_cast (show 0 < n by omega)) hδ hθa hθu)

set_option maxHeartbeats 1600000 in
/-- **N, Theorem 5.1** (the field `thm_5_1`), with `rest(κ) = cRest35 κ`. -/
theorem thm_5_1_holds : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertens3Sum Y - Real.log Y) atTop (𝓝 M₀) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
      (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 3) →
        ∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.logb 2 ℓ ≤
          ((K : ℝ) / n) * (12 - (K : ℝ) / n) * (n : ℝ) ^ 2 * Real.logb 2 n
            + cConst M₀ cRest35 ((K : ℝ) / n) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2 := by
  intro M₀ hM ε hε
  have hM0 : M₀ = mertens3Const := tendsto_nhds_unique hM tendsto_mertens3
  have hθ := PNT.tendsto_theta_div
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨η, hη_def⟩ : ∃ η, η = ε * Real.log 2 := ⟨_, rfl⟩
  have hη : 0 < η := hη_def ▸ mul_pos hε hl2
  obtain ⟨Hs, hHs_eq⟩ : ∃ Hs, Hs = Hsum := ⟨_, rfl⟩
  have hHs : 0 ≤ Hs := hHs_eq ▸ Hsum_nonneg
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = min (1 / 2 : ℝ) (η / (2 * (302 + 10 * Hs))) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ lt_min (by norm_num) (div_pos hη (by positivity))
  have hδ1 : δ ≤ 1 / 2 := hδ_def ▸ min_le_left _ _
  have hδη : δ * (302 + 10 * Hs) ≤ η / 2 := by
    have := min_le_right (1 / 2 : ℝ) (η / (2 * (302 + 10 * Hs)))
    rw [← hδ_def, le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨y0, hy01, hθa⟩ := Hankel2.theta_approx hθ hδ
  obtain ⟨C1, hC1, hθu⟩ := Hankel2.theta_upper_all hθ hδ
  obtain ⟨C2, hC2, hpl⟩ := Hankel2.sum_mul_log_le hθ hδ
  have hev := (hM.eventually (Iio_mem_nhds (show M₀ < M₀ + δ by linarith)))
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 hev
  obtain ⟨NL, hNL⟩ := log5_le_eps_sqrt hδ
  obtain ⟨B, hB_def⟩ : ∃ B, B = 18 * C1 + C2 / 5 + Ecst * (5 * (1 + δ) + C1) := ⟨_, rfl⟩
  have hE0 : (0 : ℝ) ≤ Ecst := by unfold Ecst; positivity
  have hB : 0 ≤ B := by rw [hB_def]; positivity
  refine ⟨1801 + NL + ⌈20 * y0⌉₊ + ⌈20 * |x0|⌉₊ + ⌈2 * B / η⌉₊, ?_⟩
  intro n K hn heven hκ1 hκ2 S hS
  have hn1800 : 1800 < n := by omega
  have hnr : (1801 : ℝ) ≤ n := by exact_mod_cast (show 1801 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0n : 20 * y0 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈20 * y0⌉₊ ≤ n by omega))
  have hx0n : 20 * |x0| ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈20 * |x0|⌉₊ ≤ n by omega))
  have hBn : 2 * B / η ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2 * B / η⌉₊ ≤ n by omega))
  obtain ⟨κ, hκ_def⟩ : ∃ κ, κ = (K : ℝ) / n := ⟨_, rfl⟩
  rw [← hκ_def] at hκ1 hκ2 ⊢
  have hKk : (K : ℝ) = κ * n := by rw [hκ_def]; field_simp
  have hκ0 : 0 ≤ κ := by linarith
  have hK6 : K ≤ 6 * n := by
    have : (K : ℝ) ≤ 6 * n := by rw [hKk]; exact mul_le_mul_of_nonneg_right hκ2 hn0.le
    exact_mod_cast this
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK6
  -- reduce to natural logarithms
  set c0 := M₀ - Real.log 20 with hc0_def
  have hc0 : c0 + δ ≤ 0 := by rw [hc0_def, hM0]; have := mertens3Const_sub_le; linarith
  have hlhs : ∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.logb 2 ℓ =
      (∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.log ℓ) / Real.log 2 := by
    rw [sum_div]; refine sum_congr rfl fun p _ => ?_; rw [Real.logb]; ring
  have hrhs : κ * (12 - κ) * (n : ℝ) ^ 2 * Real.logb 2 n + cConst M₀ cRest35 κ * (n : ℝ) ^ 2 +
      ε * (n : ℝ) ^ 2 =
      (κ * (12 - κ) * (n : ℝ) ^ 2 * Real.log n
        + (κ * (12 - κ) * c0 + (stepBound : ℝ) + 3 * κ / 20 + 2 / 400) * (n : ℝ) ^ 2
        + η * (n : ℝ) ^ 2) / Real.log 2 := by
    rw [Real.logb, cConst, cRest35, hη_def, hc0_def]; field_simp; ring
  rw [hlhs, hrhs]
  refine div_le_div_of_nonneg_right ?_ hl2.le
  rw [← sum_filter_add_sum_filter_not S (fun ℓ => 20 * ℓ ≤ n)]
  have hS' : ∀ ℓ ∈ S, ℓ.Prime := fun ℓ h => (hS ℓ h).1
  have h1 := sum_small_le3 heven hK6 S hS
  -- the main term
  have hmert : mertens3Sum ((n : ℝ) / 20) ≤ Real.log n + c0 + δ := by
    have := hx0 ((n : ℝ) / 20) (by have := le_abs_self x0; linarith)
    rw [Real.log_div (by positivity) (by norm_num)] at this
    rw [hc0_def]; linarith
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hKc : 0 ≤ (K : ℝ) * (12 * n + 4 - K) := by
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hKr (show (0:ℝ) ≤ K by positivity)]
  have hmain : (K : ℝ) * (12 * n + 4 - K) * mertens3Sum ((n : ℝ) / 20) ≤
      κ * (12 - κ) * (n : ℝ) ^ 2 * Real.log n + κ * (12 - κ) * c0 * (n : ℝ) ^ 2 +
        36 * δ * (n : ℝ) ^ 2 + 24 * n * Real.log n := by
    have s1 := mul_le_mul_of_nonneg_left hmert hKc
    have e : (K : ℝ) * (12 * n + 4 - K) * (Real.log n + c0 + δ) =
        κ * (12 - κ) * (n : ℝ) ^ 2 * Real.log n + κ * (12 - κ) * c0 * (n : ℝ) ^ 2
          + κ * (12 - κ) * ((n : ℝ) ^ 2 * δ) + 4 * (κ * n) * Real.log n
          + 4 * (κ * n) * (c0 + δ) := by
      rw [hKk]; ring
    have t1 : κ * (12 - κ) * ((n : ℝ) ^ 2 * δ) ≤ 36 * ((n : ℝ) ^ 2 * δ) :=
      mul_le_mul_of_nonneg_right (kappa_bound κ) (by positivity)
    have t2 : 4 * (κ * n) * (c0 + δ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc0
    have t3 : 4 * (κ * n) * Real.log n ≤ 24 * n * Real.log n := by
      have : 0 ≤ (n : ℝ) * Real.log n := by positivity
      have := mul_le_mul_of_nonneg_right hκ2 this; linarith
    linarith
  -- the Lemma A1 errors
  have hA1 := sum_sqRange_le (K := K) (n := n) (by omega) hK6
    ((range (⌊(n : ℝ) / 20⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ 2 * ℓ ^ 2 ≤ 9 * n))
    (fun ℓ hℓ => (mem_filter.1 hℓ).2)
  have hlog5 := hNL n (by omega)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsq1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
  have hA1' : 240 * n * Real.sqrt n * Real.log (5 * n) ≤ 240 * δ * (n : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog5 (show 0 ≤ 240 * (n : ℝ) * Real.sqrt n by positivity)
    have e : 240 * (n : ℝ) * Real.sqrt n * (δ * Real.sqrt n) = 240 * δ * n * (Real.sqrt n * Real.sqrt n) := by
      ring
    rw [e, hsq] at this
    linarith
  have hLn : 24 * n * Real.log n ≤ 24 * δ * (n : ℝ) ^ 2 := by
    have hsqn : Real.sqrt n ≤ n := by
      have := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg (n : ℝ)); linarith
    have hl : Real.log n ≤ Real.log (5 * n) :=
      Real.log_le_log hn0 (le_mul_of_one_le_left hn0.le (by norm_num))
    have : Real.log n ≤ δ * n := by
      have := mul_le_mul_of_nonneg_left hsqn hδ.le
      linarith
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 24 * (n : ℝ) by positivity)
    linarith
  -- the single-level errors
  have hE2 := single_errors_le (n := n) (K := K) hn0 hKk hκ2 hδ.le hC1 hC2 hθu hpl
  -- the cells
  have hcells_err : Ecst * ((1 + δ) * (5 * n) + C1) ≤ Ecst * (5 * (1 + δ) + C1) * n := by
    have : C1 * 1 ≤ C1 * n := mul_le_mul_of_nonneg_left (by linarith) hC1
    have := mul_le_mul_of_nonneg_left this hE0
    linarith
  have hBn' : B * n ≤ η / 2 * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hη] at hBn
    have := mul_le_mul_of_nonneg_right hBn hn0.le
    linarith
  have hδn : δ * (302 + 10 * Hs) * (n : ℝ) ^ 2 ≤ η / 2 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hδη (by positivity)
  rw [hB_def] at hBn'
  have h23 := large_total_le heven hn1800 hK6 S hS' hδ.le (fun y hy => hθa y (by linarith)) hθu
  rw [← hHs_eq] at h23
  clear hHs_eq
  have hδn2 : 0 ≤ δ * (n : ℝ) ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  linarith

end Zeta35.Den
