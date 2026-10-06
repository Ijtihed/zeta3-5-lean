import RequestProject.Zeta7.Hankel2.ContAssembly

/-!
# Paper Theorem 6.1 (Lemma B): the archimedean `ℓ¹` bound

Combining the discrete reduction (Lemma 6.2, `lemma62`) with the linearisation and the continuum
limit (Lemmas 6.3–6.4, `EB_le_cont`):

* `errR_le`: `𝓔(n, K) ≤ 403 n (1 + ln n)` for `K ≤ 3n`;
* `nlogn_le_eps_sq`: `C n (1 + ln n) ≤ ε n²` for all large `n`;
* **`lemma_B_exp_general`**: for every `ε > 0` there is `N` such that for all odd `n ≥ N`,
  all `K` with `K/n ≤ 3` and all feasible `σ` (no piecewise-constancy needed),
  `‖Δ_K‖₁ ≤ exp((κ² − 6κ) n² ln n + n² (F[σ] + gap(σ)) + ε n²)`;
* `lemma_B_exp`: the same, in exactly the shape of the field `lemma_B` of `Zeta27InputsR4`
  (with `exp` on the right instead of `ln` on the left, i.e. with the convention `ln 0 = −∞`);
* **`lemma_B_holds_of_ne`**: the field `lemma_B` verbatim (natural `ln`), under the extra
  hypothesis `Δ_K ≠ 0`.  (With Lean's convention `Real.log 0 = 0`, the literal field says
  nothing true about `K` with `Δ_K = 0`, since its right side tends to `−∞`.)
-/

open Finset

namespace Hankel2.ArchB

open Fam3

theorem log_Qn_le {n : ℕ} (hn : 0 < n) : Real.log (Qn n) ≤ 41 + 4 * Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 : 0 < Qn n := by unfold Qn LamA; positivity
  have hQ : Qn n ≤ 2 ^ 41 * (n : ℝ) ^ 4 := by
    unfold Qn LamA
    have h1 : (2 * (n : ℝ) + 1) ≤ 2 ^ 2 * n := by linarith
    have h2 : (6 + 24 * (n : ℝ)) ≤ 2 ^ 5 * n := by linarith
    have h3 : (6 + 24 * (n : ℝ)) ^ 3 ≤ (2 ^ 5 * n) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
    calc (10 : ℝ) ^ 7 * (2 * n + 1) * (6 + 24 * n) ^ 3 ≤ 2 ^ 24 * (2 ^ 2 * n) * (2 ^ 5 * n) ^ 3 := by
          gcongr; norm_num
      _ = 2 ^ 41 * (n : ℝ) ^ 4 := by ring
  calc Real.log (Qn n) ≤ Real.log (2 ^ 41 * (n : ℝ) ^ 4) := Real.log_le_log hQ0 hQ
    _ = 41 * Real.log 2 + 4 * Real.log n := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    _ ≤ 41 + 4 * Real.log n := by have := Real.log_two_lt_d9; linarith

theorem errR_le {n K : ℕ} (hn : 0 < n) (hK : (K : ℝ) ≤ 3 * n) :
    errR n K ≤ 403 * n * (1 + Real.log n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hQ := log_Qn_le hn
  have h3 := log_three_mul_le hn
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h24 : Real.log 24 ≤ 23 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 24 by norm_num); linarith
  have h24' : 0 < Real.log 24 := Real.log_pos (by norm_num)
  unfold errR
  have e1 : (K : ℝ) * (Real.log (Qn n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) ≤
      3 * n * (93 + 20 * Real.log n) := by
    calc (K : ℝ) * (Real.log (Qn n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2)
        ≤ K * (93 + 20 * Real.log n) := mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ 3 * n * (93 + 20 * Real.log n) := mul_le_mul_of_nonneg_right hK (by linarith)
  have e2 : (3 * (n : ℝ) + 1) * (Real.log 24 + 8 * Real.log 2) ≤ 4 * n * 31 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hL]

theorem one_add_log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : 1 + Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have h := Real.log_le_sub_one_of_pos hs
  have e : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
  linarith

theorem nlogn_le_eps_sq (C : ℝ) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → C * n * (1 + Real.log n) ≤ ε * (n : ℝ) ^ 2 := by
  refine ⟨⌈(2 * C / ε) ^ 2⌉₊, fun n hN hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hNn : (2 * C / ε) ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hsN : 2 * C / ε ≤ Real.sqrt n := by
    rw [show 2 * C / ε = Real.sqrt ((2 * C / ε) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hNn
  have h2C : 2 * C ≤ ε * Real.sqrt n := by
    have := (div_le_iff₀ hε).1 hsN; linarith [mul_comm (Real.sqrt n) ε]
  have hlog := one_add_log_le_two_sqrt hn1
  calc C * n * (1 + Real.log n) ≤ C * n * (2 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (2 * C) * (n * Real.sqrt n) := by ring
    _ ≤ (ε * Real.sqrt n) * (n * Real.sqrt n) := mul_le_mul_of_nonneg_right h2C (by positivity)
    _ = ε * (Real.sqrt n * Real.sqrt n) * n := by ring
    _ = ε * (n : ℝ) ^ 2 := by rw [hsq]; ring

/-- **Paper Theorem 6.1 (Lemma B), exponential form**, uniformly in `κ = K/n ≤ 3` and in the
feasible profile `σ`.  No piecewise-constancy of `σ` and no lower bound on `κ` are needed. -/
theorem lemma_B_exp_general : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → n % 2 = 1 →
    (K : ℝ) / n ≤ 3 → ∀ σ : ℝ → ℝ, Feasible ((K : ℝ) / n) σ →
      l1 (hankelPoly n K) ≤ Real.exp
        ((((K : ℝ) / n) ^ 2 - 6 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy σ + gapF ((K : ℝ) / n) σ) + ε * (n : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N, hN⟩ := nlogn_le_eps_sq 5403 (by norm_num) hε
  refine ⟨N, fun n K hNn hn hK σ hσ => ?_⟩
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hKn : (K : ℝ) ≤ 3 * n := by rwa [div_le_iff₀ hn'] at hK
  have h62 := lemma62 hn _ (fun s hs => EB_le_cont hn hσ hK hs)
  refine h62.trans (Real.exp_le_exp.2 ?_)
  have h1 := errR_le hn0 hKn
  have h2 := hN n hNn hn0
  unfold errC
  nlinarith

/-- **Paper Theorem 6.1**, in exactly the shape of the field `lemma_B` of `Zeta27InputsR4`, but
with `‖Δ_K‖₁ ≤ exp(…)` in place of `ln ‖Δ_K‖₁ ≤ …` (the faithful reading when `Δ_K = 0`). -/
theorem lemma_B_exp : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → n % 2 = 1 →
    (2.8 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 3 → ∀ σ : ℝ → ℝ, Feasible ((K : ℝ) / n) σ →
      PiecewiseConst m σ →
      l1 (hankelPoly n K) ≤ Real.exp
        ((((K : ℝ) / n) ^ 2 - 6 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy σ + gapF ((K : ℝ) / n) σ) + ε * (n : ℝ) ^ 2) := by
  intro _ ε hε
  obtain ⟨N, hN⟩ := lemma_B_exp_general ε hε
  exact ⟨N, fun n K hNn hn _ hK σ hσ _ => hN n K hNn hn hK σ hσ⟩

theorem l1_pos_of_ne {F : Polynomial ℚ} (hF : F ≠ 0) : 0 < l1 F := by
  unfold l1
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun i => |((F.coeff i : ℚ) : ℝ)|)
    (fun i _ => abs_nonneg _) (mem_range.2 (Nat.lt_succ_self F.natDegree)))
  simp only [abs_pos, ne_eq, Rat.cast_eq_zero]
  exact Polynomial.leadingCoeff_ne_zero.2 hF

/-- **Paper Theorem 6.1 (Lemma B)**: the field `lemma_B` of `Zeta27InputsR4` verbatim, for every
`K` with `Δ_K ≠ 0`. -/
theorem lemma_B_holds_of_ne : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n →
    n % 2 = 1 → (2.8 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 3 → hankelPoly n K ≠ 0 →
    ∀ σ : ℝ → ℝ, Feasible ((K : ℝ) / n) σ → PiecewiseConst m σ →
      Real.log (l1 (hankelPoly n K)) ≤
        (((K : ℝ) / n) ^ 2 - 6 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy σ + gapF ((K : ℝ) / n) σ) + ε * (n : ℝ) ^ 2 := by
  intro m ε hε
  obtain ⟨N, hN⟩ := lemma_B_exp m ε hε
  refine ⟨N, fun n K hNn hn h1 h2 hne σ hσ hP => ?_⟩
  rw [Real.log_le_iff_le_exp (l1_pos_of_ne hne)]
  exact hN n K hNn hn h1 h2 σ hσ hP

end Hankel2.ArchB
