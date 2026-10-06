module

public import RequestProject.Zeta7.PNT.MertensLambda

/-!
# From `Λ` to primes: `∑_{p ≤ x} log p/(p - 1) = log x - γ + o(1)`

* `sum_vonMangoldt_div_eq_sum_primes`: `∑_{n ≤ N} Λ(n)/n = ∑_{p ≤ N} ∑_{k=1}^{K_p} log p/p^k`,
  `K_p = ⌊log_p N⌋`;
* `primeTerm_sub_le`: `0 ≤ log p/(p-1) - ∑_{k=1}^{K_p} log p/p^k ≤ 2 log p/(p √N)`;
* `primeSum_sub_le`: the total difference is `≤ 2 log N (1 + log N)/√N`;
* **`tendsto_primeSum_sub_log`**: `∑_{p ≤ x} log p/(p-1) - log x → -γ`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real

namespace PNT

open Chebyshev ArithmeticFunction

/-- `∑_{p ≤ N} log p/(p - 1)`. -/
noncomputable def primeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)

theorem sum_vonMangoldt_div_eq_sum_primes (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, Λ n / n =
      ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k := by
  rw [Finset.sum_sigma', ← Finset.sum_filter_of_ne (p := IsPrimePow) (s := Finset.Icc 0 N)
    (f := fun n => Λ n / n)
    (fun n _ h => vonMangoldt_ne_zero_iff.mp (fun h0 => h (by simp [h0])))]
  symm
  refine Finset.sum_bij (fun x _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨_, hpN⟩, hp⟩, hk1, hkK⟩ := hx
    have hN : N ≠ 0 := by have := hp.two_le; omega
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
    refine ⟨(Nat.pow_le_pow_right hp.pos hkK).trans (Nat.pow_log_le_self p hN),
      hp.isPrimePow.pow (by omega)⟩
  · rintro ⟨p, k⟩ hx ⟨q, m⟩ hy h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx hy h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj' hx.1.2 hy.1.2 (by omega) (by omega) h
    subst h1; subst h2; rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn.2
    refine ⟨⟨p, k⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
    refine ⟨⟨(Nat.le_self_pow (by omega) p).trans hn.1.2, hp⟩, hk, ?_⟩
    exact Nat.le_log_of_pow_le hp.one_lt hn.1.2
  · rintro ⟨p, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hx.1.2]
    push_cast; ring

theorem geom_sum_Icc {r : ℝ} (hr : 1 < r) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, 1 / r ^ k = (1 - 1 / r ^ K) / (r - 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : r - 1 ≠ 0 := by linarith
    have h2 : r ^ K ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
    ring

/-- The contribution of one prime. -/
theorem primeTerm_eq {p : ℕ} (hp : p.Prime) (K : ℕ) :
    Real.log p / ((p : ℝ) - 1) - ∑ k ∈ Finset.Icc 1 K, Real.log p / (p : ℝ) ^ k =
      Real.log p / ((p : ℝ) ^ K * ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h := geom_sum_Icc hp1 K
  have : ∑ k ∈ Finset.Icc 1 K, Real.log p / (p : ℝ) ^ k =
      Real.log p * ∑ k ∈ Finset.Icc 1 K, 1 / (p : ℝ) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, h]
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ^ K ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp
  ring

theorem primeTerm_sub_le {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    0 ≤ Real.log p / ((p : ℝ) - 1) -
        ∑ k ∈ Finset.Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k ∧
      Real.log p / ((p : ℝ) - 1) -
        ∑ k ∈ Finset.Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k ≤
      2 * Real.log p / (p * Real.sqrt N) := by
  rw [primeTerm_eq hp]
  set K := Nat.log p N
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hK : 1 ≤ K := Nat.log_pos hp.one_lt hpN
  have hpK : 0 < (p : ℝ) ^ K := by positivity
  refine ⟨div_nonneg hlog (mul_nonneg hpK.le (by linarith)), ?_⟩
  -- `p^(K+1) > N` and `p^(K+1) ≥ p²`, hence `p^(K+1) ≥ p √N`
  have hA1 : (N : ℝ) < (p : ℝ) ^ (K + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt N
  have hA2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (K + 1) := pow_le_pow_right₀ hp1.le (by omega)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hA3 : (p : ℝ) * Real.sqrt N ≤ (p : ℝ) ^ (K + 1) := by
    have hsq : ((p : ℝ) * Real.sqrt N) ^ 2 ≤ ((p : ℝ) ^ (K + 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN0]
      have : 0 ≤ (p : ℝ) ^ (K + 1) := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hpos : 0 < (p : ℝ) * Real.sqrt N := by
    have : 0 < (N : ℝ) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hp.one_lt.le.trans hpN
      linarith
    positivity
  rw [div_le_div_iff₀ (mul_pos hpK (by linarith)) hpos]
  have : (p : ℝ) ^ (K + 1) ≤ 2 * ((p : ℝ) ^ K * ((p : ℝ) - 1)) := by
    rw [pow_succ]; nlinarith
  nlinarith

/-- The `Λ`-sum `∑_{n ≤ N} Λ(n)/n`. -/
noncomputable def lamSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 0 N, Λ n / n

theorem primeSum_sub_lamSum_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ primeSum N - lamSum N ∧
      primeSum N - lamSum N ≤ 2 * Real.log N * (1 + Real.log N) / Real.sqrt N := by
  have hdiff : primeSum N - lamSum N = ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime,
      (Real.log p / ((p : ℝ) - 1) -
        ∑ k ∈ Finset.Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k) := by
    rw [primeSum, lamSum, sum_vonMangoldt_div_eq_sum_primes, Finset.sum_sub_distrib]
  have hmem : ∀ p ∈ (Finset.Icc 0 N).filter Nat.Prime, p.Prime ∧ p ≤ N := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨hp.2, hp.1.2⟩
  rw [hdiff]
  refine ⟨Finset.sum_nonneg fun p hp => (primeTerm_sub_le (hmem p hp).1 (hmem p hp).2).1, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  calc _ ≤ ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, 2 * Real.log p / (p * Real.sqrt N) :=
        Finset.sum_le_sum fun p hp => (primeTerm_sub_le (hmem p hp).1 (hmem p hp).2).2
    _ ≤ ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, 2 * Real.log N / Real.sqrt N * (1 / (p : ℝ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hp, hpN⟩ := hmem p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have : Real.log p ≤ Real.log N :=
          Real.log_le_log hp0 (by exact_mod_cast hpN)
        rw [show 2 * Real.log N / Real.sqrt N * (1 / (p : ℝ)) =
          2 * Real.log N / (p * Real.sqrt N) by field_simp]
        gcongr
    _ = 2 * Real.log N / Real.sqrt N *
          ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, (1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.log N / Real.sqrt N * ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
          fun _ _ _ => by positivity) (by positivity)
        intro p hp
        obtain ⟨hp, hpN⟩ := hmem p hp
        simp only [Finset.mem_Icc]; exact ⟨hp.one_lt.le, hpN⟩
    _ ≤ 2 * Real.log N / Real.sqrt N * (1 + Real.log N) := by
        gcongr
        have h := harmonic_le_one_add_log N
        rw [harmonic_eq_sum_Icc] at h
        push_cast at h
        simpa [one_div] using h
    _ = 2 * Real.log N * (1 + Real.log N) / Real.sqrt N := by ring

theorem tendsto_log_sq_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x ^ 2 / Real.sqrt x) atTop (𝓝 0) := by
  have := (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) 2 (by norm_num)).tendsto_div_nhds_zero
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem tendsto_bound_nat :
    Tendsto (fun N : ℕ => 2 * Real.log N * (1 + Real.log N) / Real.sqrt N) atTop (𝓝 0) := by
  have h := (tendsto_log_div_sqrt.const_mul 2).add (tendsto_log_sq_div_sqrt.const_mul 2)
  simp only [mul_zero, add_zero] at h
  refine (h.comp tendsto_natCast_atTop_atTop).congr fun N => ?_
  simp only [Function.comp]
  ring

theorem primeSum_eq {N : ℕ} (hN : 2 ≤ N) :
    primeSum N = Real.log 2 +
      ∑ p ∈ Finset.Icc 3 N with p.Prime, Real.log p / ((p : ℝ) - 1) := by
  have hset : (Finset.Icc 0 N).filter Nat.Prime =
      insert 2 ((Finset.Icc 3 N).filter Nat.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨_, hpN⟩, hp⟩
      rcases hp.eq_two_or_odd' with h | h
      · exact Or.inl h
      · right
        have := hp.two_le
        refine ⟨⟨?_, hpN⟩, hp⟩
        rcases (show p = 2 ∨ 3 ≤ p by omega) with h2 | h3
        · subst h2; exact absurd h (by decide)
        · exact h3
    · rintro (rfl | ⟨⟨h3, hpN⟩, hp⟩)
      · exact ⟨⟨by omega, hN⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, hpN⟩, hp⟩
  rw [primeSum, hset, Finset.sum_insert (by simp)]
  norm_num

/-- **Mertens' theorem with constant, over odd primes**:
`∑_{3 ≤ p ≤ x} log p/(p - 1) - log x → -γ - log 2`. -/
theorem tendsto_mertens_odd :
    Tendsto (fun x : ℝ => (∑ p ∈ Finset.Icc 3 ⌊x⌋₊ with p.Prime, Real.log p / ((p : ℝ) - 1)) -
      Real.log x) atTop (𝓝 (-eulerMascheroniConstant - Real.log 2)) := by
  have hD : Tendsto (fun x : ℝ => primeSum ⌊x⌋₊ - lamSum ⌊x⌋₊) atTop (𝓝 0) := by
    have hB := tendsto_bound_nat.comp (tendsto_nat_floor_atTop (α := ℝ))
    refine squeeze_zero' ?_ ?_ hB
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact (primeSum_sub_lamSum_bounds (Nat.one_le_floor_iff _ |>.mpr hx)).1
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact (primeSum_sub_lamSum_bounds (Nat.one_le_floor_iff _ |>.mpr hx)).2
  have h := (hD.add tendsto_sum_vonMangoldt_div_sub_log).sub_const (Real.log 2)
  rw [show (0 : ℝ) + -eulerMascheroniConstant - Real.log 2 =
    -eulerMascheroniConstant - Real.log 2 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  rw [primeSum_eq hN, lamSum]
  ring

end PNT
