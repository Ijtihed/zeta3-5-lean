import RequestProject.Zeta35.DenLarge

/-!
# Denominators (N, Theorem 5.1), step 10: the primes `ℓ ≤ n/20`

For a prime `ℓ` (`n` even, `K ≤ 6n`), Lemma A1 (`lemmaA1_plus3`, used for `2ℓ² ≤ 9n`) and the
single-level bound (`prop85_plus3`, for `9n < 2ℓ²`) give (`small_term`)

  `max(T_ℓ, 0) ln ℓ ≤ K(12n + 4 − K) ln ℓ/(ℓ − 1) + [2ℓ² ≤ 9n] (6K L_ℓ + 24n) ln ℓ + (3K + 4ℓ) ln ℓ`.

`sum_sqRange_le` bounds the Lemma A1 error terms by `240 n √n ln(5n)`.
-/

open Finset Chebyshev

namespace Zeta35.Den

theorem fourR_eq {n : ℕ} (hn : Even n) : (4 * (2 * R n + 1) : ℝ) = 12 * n + 4 := by
  have : 2 * R n = 3 * n := R_of_even hn
  have : (2 * R n : ℝ) = 3 * n := by exact_mod_cast this
  linarith

/-- The bound for one prime `ℓ`. -/
theorem small_term {n K ℓ : ℕ} (hn : Even n) (hK : K ≤ 6 * n) (hℓ : ℓ.Prime) :
    (TPplus ℓ n K : ℝ) * Real.log ℓ ≤
      (K : ℝ) * (12 * n + 4 - K) * (Real.log ℓ / ((ℓ : ℝ) - 1))
        + (if 2 * ℓ ^ 2 ≤ 9 * n then (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ else 0)
        + (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hR : 2 * R n = 3 * n := R_of_even hn
  have hRr : (16 * R n : ℝ) = 24 * n := by
    have : (2 * R n : ℝ) = 3 * n := by exact_mod_cast hR
    linarith
  have hK12 : K ≤ 4 * (2 * R n + 1) := by omega
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
  have hlog : 0 ≤ Real.log ℓ := Real.log_natCast_nonneg ℓ
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  have hKc : 0 ≤ (K : ℝ) * (12 * n + 4 - K) := by
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hE : 0 ≤ (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ := by positivity
  have e1 : (K : ℝ) * (12 * n + 4 - K) * (Real.log ℓ / ((ℓ : ℝ) - 1)) =
      (K : ℝ) * (12 * n + 4 - K) / (ℓ - 1) * Real.log ℓ := by
    field_simp
  rw [e1]
  split_ifs with hsq
  · have h := lemmaA1_plus3 (p := ℓ) n K hK12
    rw [fourR_eq hn, hRr] at h
    have := mul_le_mul_of_nonneg_right h hlog
    nlinarith
  · push_neg at hsq
    have h := prop85_plus3 (p := ℓ) (n := n) (by omega) hK12
    rw [fourR_eq hn] at h
    have hdiv : (K : ℝ) * (12 * n + 4 - K) / ℓ ≤ (K : ℝ) * (12 * n + 4 - K) / (ℓ - 1) :=
      div_le_div_of_nonneg_left hKc (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_right (h.trans (by linarith [hdiv] :
      _ ≤ (K : ℝ) * (12 * n + 4 - K) / (ℓ - 1) + 3 * K + 4 * ℓ)) hlog
    nlinarith

/-- `L_ℓ ln ℓ ≤ ln(5n)`. -/
theorem Lp3_mul_log_le {ℓ n : ℕ} (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) :
    (Lp3 ℓ n : ℝ) * Real.log ℓ ≤ Real.log (5 * n) := by
  have hne : 9 * n / 2 ≠ 0 := by omega
  have hpow : ℓ ^ Lp3 ℓ n ≤ 9 * n / 2 := Nat.pow_log_le_self ℓ hne
  have h' : ((ℓ ^ Lp3 ℓ n : ℕ) : ℝ) ≤ 5 * n := by
    have : ℓ ^ Lp3 ℓ n ≤ 5 * n := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((ℓ ^ Lp3 ℓ n : ℕ) : ℝ) := by
    have : 0 < ℓ ^ Lp3 ℓ n := Nat.pow_pos (by omega)
    exact_mod_cast this
  have := Real.log_le_log hpos h'
  push_cast at this
  rwa [Real.log_pow] at this

/-- The Lemma A1 error terms over the primes with `2ℓ² ≤ 9n`: `O(n^{3/2} log n)`. -/
theorem sum_sqRange_le {n K : ℕ} (hn : 1 ≤ n) (hK : K ≤ 6 * n) (P : Finset ℕ)
    (hP : ∀ ℓ ∈ P, ℓ.Prime ∧ 2 * ℓ ^ 2 ≤ 9 * n) :
    ∑ ℓ ∈ P, (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ ≤
      240 * n * Real.sqrt n * Real.log (5 * n) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl5 : 0 ≤ Real.log (5 * n) := Real.log_nonneg (by linarith)
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
  have hterm : ∀ ℓ ∈ P, (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ ≤
      60 * n * Real.log (5 * n) := by
    intro ℓ hℓ
    obtain ⟨hpr, hsq⟩ := hP ℓ hℓ
    have hℓ5 : (ℓ : ℝ) ≤ 5 * n := by
      have : ℓ ≤ 5 * n := by nlinarith [hpr.two_le]
      exact_mod_cast this
    have hlp : Real.log ℓ ≤ Real.log (5 * n) :=
      Real.log_le_log (by exact_mod_cast hpr.pos) hℓ5
    have hL := Lp3_mul_log_le hpr.two_le hn
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have e : (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ =
        6 * (K : ℝ) * ((Lp3 ℓ n : ℝ) * Real.log ℓ) + 24 * n * Real.log ℓ := by ring
    rw [e]
    have h1 : 6 * (K : ℝ) * ((Lp3 ℓ n : ℝ) * Real.log ℓ) ≤ 6 * (K : ℝ) * Real.log (5 * n) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have h2 : 24 * (n : ℝ) * Real.log ℓ ≤ 24 * n * Real.log (5 * n) :=
      mul_le_mul_of_nonneg_left hlp (by positivity)
    have h3 : 6 * (K : ℝ) * Real.log (5 * n) ≤ 36 * n * Real.log (5 * n) := by nlinarith
    linarith
  have hcard : (P.card : ℝ) ≤ 4 * Real.sqrt n := by
    have hsub : P ⊆ range (Nat.sqrt (9 * n) + 1) := by
      intro ℓ hℓ
      obtain ⟨_, hsq⟩ := hP ℓ hℓ
      rw [mem_range]
      exact Nat.lt_succ_of_le (Nat.le_sqrt'.2 (by nlinarith))
    have h1 : (P.card : ℝ) ≤ Nat.sqrt (9 * n) + 1 := by
      have := card_le_card hsub
      rw [card_range] at this
      exact_mod_cast this
    have h2 : (Nat.sqrt (9 * n) : ℝ) ≤ Real.sqrt (9 * n) := by
      have := Real.nat_sqrt_le_real_sqrt (a := 9 * n)
      push_cast at this; exact this
    have h3 : Real.sqrt (9 * n) = 3 * Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num)]
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h4 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hnr
    linarith
  calc _ ≤ ∑ ℓ ∈ P, 60 * (n : ℝ) * Real.log (5 * n) := sum_le_sum hterm
    _ = P.card * (60 * (n : ℝ) * Real.log (5 * n)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (4 * Real.sqrt n) * (60 * (n : ℝ) * Real.log (5 * n)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 240 * n * Real.sqrt n * Real.log (5 * n) := by ring

/-- **The primes `ℓ ≤ n/20`** in a set `S` of primes `≠ 3`: the main terms sum to at most
`K(12n + 4 − K) · mertens3Sum(n/20)`. -/
theorem sum_small_le3 {n K : ℕ} (hn : Even n) (hK : K ≤ 6 * n) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 3) :
    ∑ ℓ ∈ S.filter (fun ℓ => 20 * ℓ ≤ n), (TPplus ℓ n K : ℝ) * Real.log ℓ ≤
      (K : ℝ) * (12 * n + 4 - K) * mertens3Sum ((n : ℝ) / 20)
      + ∑ ℓ ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ 2 * ℓ ^ 2 ≤ 9 * n),
          (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ
      + ∑ ℓ ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ := by
  classical
  set T1 := S.filter (fun ℓ => 20 * ℓ ≤ n)
  have hKr : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
  have hKc : 0 ≤ (K : ℝ) * (12 * n + 4 - K) := by
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hfl : ∀ ℓ ∈ T1, ℓ ∈ range (⌊(n : ℝ) / 20⌋₊ + 1) := by
    intro ℓ hℓ
    simp only [T1, mem_filter] at hℓ
    rw [mem_range]
    refine Nat.lt_succ_of_le (Nat.le_floor ?_)
    have : ((20 * ℓ : ℕ) : ℝ) ≤ n := by exact_mod_cast hℓ.2
    push_cast at this; linarith
  refine (sum_le_sum fun ℓ hℓ => small_term hn hK (hS ℓ (mem_filter.1 hℓ).1).1).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have ha : ∑ ℓ ∈ T1, Real.log ℓ / ((ℓ : ℝ) - 1) ≤ mertens3Sum ((n : ℝ) / 20) := by
    unfold mertens3Sum
    apply sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      have h1 := hfl ℓ hℓ
      simp only [T1, mem_filter] at hℓ
      obtain ⟨hpr, h3⟩ := hS ℓ hℓ.1
      simp only [mem_filter, mem_Icc, mem_range] at h1 ⊢
      exact ⟨⟨hpr.two_le, by omega⟩, hpr, h3⟩
    · intro ℓ hℓ _
      simp only [mem_filter, mem_Icc] at hℓ
      have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.1.1
      exact div_nonneg (Real.log_natCast_nonneg ℓ) (by linarith)
  have hb : ∑ ℓ ∈ T1, (if 2 * ℓ ^ 2 ≤ 9 * n then (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ
      else 0) ≤ ∑ ℓ ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ 2 * ℓ ^ 2 ≤ 9 * n),
          (6 * (K : ℝ) * Lp3 ℓ n + 24 * n) * Real.log ℓ := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      simp only [mem_filter] at hℓ ⊢
      exact ⟨hfl ℓ hℓ.1, (hS ℓ (mem_filter.1 hℓ.1).1).1, hℓ.2⟩
    · intro ℓ _ _
      have := Real.log_natCast_nonneg ℓ
      positivity
  have hc : ∑ ℓ ∈ T1, (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ ≤
      ∑ ℓ ∈ (range (⌊(n : ℝ) / 20⌋₊ + 1)).filter Nat.Prime, (3 * (K : ℝ) + 4 * ℓ) * Real.log ℓ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      rw [mem_filter]
      exact ⟨hfl ℓ hℓ, (hS ℓ (mem_filter.1 hℓ).1).1⟩
    · intro ℓ _ _
      have := Real.log_natCast_nonneg ℓ
      positivity
  have := mul_le_mul_of_nonneg_left ha hKc
  linarith

end Zeta35.Den
