import RequestProject.Zeta35.InputDefs
import RequestProject.Zeta7.Hankel2.AuxPrime
import RequestProject.Zeta7.PNT.PsiAsymp
import RequestProject.Zeta7.PNT.MertensPrime

/-!
# The prime-number-theorem inputs for `ζ₃(5)` (paper N, §§5, 7; CLAIMS T5, T8)

Both are *derived* from the theorems proved in `RequestProject/Zeta7/PNT/`:

* `aux_prime3` (N, §7, the auxiliary prime): from `θ(x) ∼ x` (`PNT.tendsto_theta_div`), for every
  `b ≥ 1` and all large `n` there is a prime `ℓ` with `1.5 n + ½ ≤ ℓ ≤ 1.52 n`, `ℓ > 11`, `ℓ ∤ b`;
* `tendsto_mertens3` (N, Theorem 5.1, assembly): Mertens' theorem with the term `ℓ = 3` removed,
  `∑_{ℓ ≤ Y, ℓ ≠ 3} ln ℓ/(ℓ − 1) = ln Y − γ − ½ ln 3 + o(1)`, from `PNT.tendsto_mertens_odd` by adding
  `ln 2` and subtracting `½ ln 3`.
-/

open Filter Topology Finset

namespace Zeta35

open Hankel2

open Chebyshev in
/-- **The auxiliary prime** (N, §7; CLAIMS T8), from the prime number theorem. -/
theorem aux_prime3 (b : ℕ) (hb : 0 < b) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ ℓ : ℕ, ℓ.Prime ∧ (1.5 : ℝ) * n + 1 / 2 ≤ ℓ ∧
      (ℓ : ℝ) ≤ 1.52 * n ∧ 11 < ℓ ∧ ¬ ℓ ∣ b := by
  have hθ := PNT.tendsto_theta_div
  have hev := hθ.eventually (Ioo_mem_nhds (by norm_num : (0.999 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 1.001))
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hev
  refine ⟨⌈X0⌉₊ + ⌈1000 * Real.log b⌉₊ + 2000, fun n hn => ?_⟩
  have hn1 : (⌈X0⌉₊ : ℝ) + ⌈1000 * Real.log b⌉₊ + 2000 ≤ n := by exact_mod_cast hn
  have c1 : (0 : ℝ) ≤ ⌈X0⌉₊ := by positivity
  have c2 : (0 : ℝ) ≤ ⌈1000 * Real.log b⌉₊ := by positivity
  have hX0n : X0 ≤ n := by linarith [Nat.le_ceil X0]
  have hlb : 1000 * Real.log b ≤ n := by linarith [Nat.le_ceil (1000 * Real.log b)]
  have hn10 : (2000 : ℝ) ≤ n := by linarith
  set y : ℝ := 1.5 * n + 1 / 2
  set x : ℝ := 1.52 * n
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

/-- For `⌊Y⌋ ≥ 3`: `mertens3Sum Y = mertensSum Y + ln 2 − ½ ln 3`. -/
theorem mertens3Sum_eq {Y : ℝ} (hY : 3 ≤ ⌊Y⌋₊) :
    mertens3Sum Y = mertensSum Y + Real.log 2 - Real.log 3 / 2 := by
  set f : ℕ → ℝ := fun ℓ => Real.log ℓ / ((ℓ : ℝ) - 1) with hf
  have h2 : Icc 2 ⌊Y⌋₊ = insert 2 (Icc 3 ⌊Y⌋₊) := by
    ext x; simp only [mem_insert, mem_Icc]; omega
  have h3mem : 3 ∈ (Icc 3 ⌊Y⌋₊).filter Nat.Prime := by
    simp only [mem_filter, mem_Icc]; exact ⟨⟨le_rfl, hY⟩, Nat.prime_three⟩
  have hsplit : ((Icc 3 ⌊Y⌋₊).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ 3)) =
      ((Icc 3 ⌊Y⌋₊).filter Nat.Prime).erase 3 := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc]; tauto
  have hA : mertens3Sum Y = f 2 + ∑ ℓ ∈ (Icc 3 ⌊Y⌋₊).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ 3), f ℓ := by
    rw [mertens3Sum, h2, Finset.filter_insert, if_pos ⟨Nat.prime_two, by norm_num⟩,
      Finset.sum_insert (by simp)]
  have hB : mertensSum Y = f 3 + ∑ ℓ ∈ (Icc 3 ⌊Y⌋₊).filter (fun ℓ => ℓ.Prime ∧ ℓ ≠ 3), f ℓ := by
    rw [hsplit, mertensSum, Finset.add_sum_erase _ _ h3mem]
  rw [hA, hB]
  simp only [hf]
  norm_num
  ring

/-- **Mertens' theorem with `ℓ = 3` removed** (N, Theorem 5.1, assembly; CLAIMS T5):
`∑_{ℓ ≤ Y, ℓ ≠ 3} ln ℓ / (ℓ − 1) − ln Y → −γ − ½ ln 3`. -/
theorem tendsto_mertens3 :
    Tendsto (fun Y : ℝ => mertens3Sum Y - Real.log Y) atTop (𝓝 mertens3Const) := by
  have h := (PNT.tendsto_mertens_odd).add_const (Real.log 2 - Real.log 3 / 2)
  have hconst : -Real.eulerMascheroniConstant - Real.log 2 + (Real.log 2 - Real.log 3 / 2) =
      mertens3Const := by rw [mertens3Const]; ring
  rw [hconst] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with Y hY
  have hY3 : 3 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  rw [mertens3Sum_eq hY3, mertensSum]
  ring

end Zeta35
