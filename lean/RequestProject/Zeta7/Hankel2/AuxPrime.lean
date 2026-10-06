import Mathlib

/-!
# The auxiliary prime (paper Lemma 10.1) from the prime number theorem

`Hankel2.aux_prime`: if `θ(x) = x + o(x)` (Chebyshev's `θ`), then for every integer `b ≥ 1` there
is `n₀(b)` such that for every `n ≥ n₀(b)` there is a prime `p` with `1.75n + ½ ≤ p ≤ 1.8n`,
`p > 11` and `p ∤ b`.

Proof: `θ(1.8n) − θ(1.75n + ½) ≥ 0.05n − o(n) > log b` for large `n`, while the primes of the
window dividing `b` contribute at most `log b` to this difference.
-/

open Filter Topology Finset

namespace Hankel2

open Chebyshev in
/-- `θ(x) = θ(y) + ∑_{y < p ≤ x} log p`. -/
theorem theta_window (y x : ℝ) (hxy : y ≤ x) :
    θ x = θ y + ∑ p ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ with p.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [sum_filter, sum_filter, sum_filter, Finset.sum_Ioc_consecutive _ (Nat.zero_le _)
    (Nat.floor_mono hxy)]

/-- If all primes of `W` divide `b > 0`, then `∑_{p ∈ W} log p ≤ log b`. -/
theorem sum_log_le_of_dvd (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (b : ℕ) (hb : 0 < b)
    (hdvd : ∀ p ∈ W, p ∣ b) : ∑ p ∈ W, Real.log p ≤ Real.log b := by
  have h := Finset.prod_primes_dvd b (fun p hp => (Nat.prime_iff.mp (hW p hp))) hdvd
  have hpos : 0 < ∏ p ∈ W, p := Finset.prod_pos fun p hp => (hW p hp).pos
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (hW p hp).ne_zero)]
  rw [← Nat.cast_prod]
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast Nat.le_of_dvd hb h

open Chebyshev in
/-- **Lemma 10.1** (auxiliary prime), from `θ(x) ∼ x`. -/
theorem aux_prime (hθ : Tendsto (fun x : ℝ => theta x / x) atTop (𝓝 1)) (b : ℕ) (hb : 0 < b) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ p : ℕ, p.Prime ∧ (1.75 : ℝ) * n + 1 / 2 ≤ p ∧
      (p : ℝ) ≤ 1.8 * n ∧ 11 < p ∧ ¬ p ∣ b := by
  have hev := hθ.eventually (Ioo_mem_nhds (by norm_num : (0.99 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 1.01))
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hev
  refine ⟨⌈X0⌉₊ + ⌈100 * Real.log b⌉₊ + 200, fun n hn => ?_⟩
  have hn1 : (⌈X0⌉₊ : ℝ) + ⌈100 * Real.log b⌉₊ + 200 ≤ n := by exact_mod_cast hn
  have c1 : (0 : ℝ) ≤ ⌈X0⌉₊ := by positivity
  have c2 : (0 : ℝ) ≤ ⌈100 * Real.log b⌉₊ := by positivity
  have hX0n : X0 ≤ n := by linarith [Nat.le_ceil X0]
  have hlb : 100 * Real.log b ≤ n := by linarith [Nat.le_ceil (100 * Real.log b)]
  have hn10 : (200 : ℝ) ≤ n := by linarith
  set y : ℝ := 1.75 * n + 1 / 2
  set x : ℝ := 1.8 * n
  have hy0 : 0 ≤ y := by positivity
  have hxy : y ≤ x := by simp only [x, y]; linarith
  have hy1 := hX0 y (by simp only [y]; linarith)
  have hx1 := hX0 x (by simp only [x]; linarith)
  have hypos : 0 < y := by positivity
  have hxpos : 0 < x := by simp only [x]; positivity
  rw [lt_div_iff₀ hypos, div_lt_iff₀ hypos] at hy1
  rw [lt_div_iff₀ hxpos, div_lt_iff₀ hxpos] at hx1
  have hwin := theta_window y x hxy
  by_contra hcon
  push_neg at hcon
  have hdvd : ∀ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, p ∣ b := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hp⟩ := hp
    have hpy : y < p := (Nat.floor_lt hy0).1 h1
    have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff hxpos.le).1 h2
    have h11 : 11 < p := by
      have : (11 : ℝ) < p := by simp only [y] at hpy; linarith
      exact_mod_cast this
    exact hcon p hp hpy.le hpx h11
  have hsum := sum_log_le_of_dvd _ (fun p hp => (mem_filter.1 hp).2) b hb hdvd
  simp only [x, y] at hy1 hx1 hwin hsum
  linarith

end Hankel2
