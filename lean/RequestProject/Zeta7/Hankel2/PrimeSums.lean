import RequestProject.Zeta7.Hankel2.AuxPrime
import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# Prime sums from the prime number theorem (paper §8.4–§8.5)

Elementary consequences of the two analytic inputs `θ(x) = x + o(x)` and
`∑_{3 ≤ p ≤ x} ln p/(p−1) = ln x − γ − ln 2 + o(1)` used in the assembly of Theorem 8.1:

* `theta_approx`: `|θ(y) − y| ≤ δ y` for large `y`;
* `theta_upper_all`, `theta_lower_all`: the same with an additive constant, for all `y ≥ 0`;
* `sum_log_le_theta_sub`: primes in `(x, y]` contribute at most `θ(y) − θ(x)`;
* `sum_mul_log_eq`: `∑_{p ≤ M} p ln p = ∑_{m < M} (θ(M) − θ(m))`;
* `sum_mul_log_le`: `∑_{p ≤ X} p ln p ≤ (1/2 + 2δ) X² + C X`;
* `mertens_upper`: `∑_{3 ≤ p ≤ x} ln p/(p−1) ≤ ln x − γ − ln 2 + δ` for large `x`;
* `log_le_eps_sqrt`: `ln(4n) ≤ δ √n` for large `n`.
-/

open Filter Topology Finset Chebyshev

namespace Hankel2

section PrimeSums

variable (hθ : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
include hθ

/-- `|θ(y) − y| ≤ δ y` for all large `y`. -/
theorem theta_approx {δ : ℝ} (hδ : 0 < δ) : ∃ y0 : ℝ, 1 ≤ y0 ∧ ∀ y, y0 ≤ y → |θ y - y| ≤ δ * y := by
  have hev := hθ.eventually (Ioo_mem_nhds (by linarith : 1 - δ < 1) (by linarith : (1 : ℝ) < 1 + δ))
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hev
  refine ⟨max X0 1, le_max_right _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 < y := by linarith
  obtain ⟨h1, h2⟩ := hX0 y ((le_max_left _ _).trans hy)
  rw [lt_div_iff₀ hy0] at h1
  rw [div_lt_iff₀ hy0] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- `θ(y) ≤ (1 + δ) y + C` for all `y ≥ 0`. -/
theorem theta_upper_all {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, 0 ≤ y → θ y ≤ (1 + δ) * y + C := by
  obtain ⟨y0, hy0, h⟩ := theta_approx hθ hδ
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 * y0, by positivity, fun y hy => ?_⟩
  rcases le_total y0 y with hy' | hy'
  · have := (abs_le.1 (h y hy')).2
    nlinarith [mul_nonneg hl4 (by linarith : (0 : ℝ) ≤ y0)]
  · have := theta_le_log4_mul_x hy
    nlinarith [mul_le_mul_of_nonneg_left hy' hl4]

/-- `(1 − δ) y − C ≤ θ(y)` for all `y ≥ 0`. -/
theorem theta_lower_all {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, 0 ≤ y → (1 - δ) * y - C ≤ θ y := by
  obtain ⟨y0, hy0, h⟩ := theta_approx hθ hδ
  refine ⟨y0, by linarith, fun y hy => ?_⟩
  rcases le_total y0 y with hy' | hy'
  · have := (abs_le.1 (h y hy')).1
    nlinarith
  · have := theta_nonneg y
    nlinarith

omit hθ in
/-- A finite set of primes in `(x, y]` contributes at most `θ(y) − θ(x)`. -/
theorem sum_log_le_theta_sub (P : Finset ℕ) {x y : ℝ} (hxy : x ≤ y)
    (hP : ∀ p ∈ P, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y) :
    ∑ p ∈ P, Real.log p ≤ θ y - θ x := by
  rw [theta_window x y hxy, add_sub_cancel_left]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hP p hp
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, h1⟩
    · rcases le_or_gt 0 x with hx | hx
      · exact (Nat.floor_lt hx).2 h2
      · rw [Nat.floor_of_nonpos hx.le]; exact h1.pos
    · exact Nat.le_floor h3
  · intro p hp _
    exact Real.log_natCast_nonneg p

omit hθ in
theorem theta_natCast_succ (M : ℕ) :
    θ ((M + 1 : ℕ) : ℝ) = θ (M : ℝ) + if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) else 0 := by
  rw [theta_window (M : ℝ) ((M + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.le_succ M)]
  simp only [Nat.floor_natCast, Nat.Ioc_succ_singleton, sum_filter, sum_singleton]

omit hθ in
/-- `∑_{p ≤ M} p ln p = ∑_{m < M} (θ(M) − θ(m))`. -/
theorem sum_mul_log_eq (M : ℕ) :
    ∑ p ∈ (range (M + 1)).filter Nat.Prime, (p : ℝ) * Real.log p =
      ∑ m ∈ range M, (θ (M : ℝ) - θ (m : ℝ)) := by
  induction M with
  | zero => simp [sum_filter]
  | succ M ih =>
    rw [range_add_one (n := M + 1), filter_insert]
    rw [sum_range_succ]
    have hs : ∀ m ∈ range M, θ ((M + 1 : ℕ) : ℝ) - θ (m : ℝ) =
        (θ (M : ℝ) - θ (m : ℝ)) + (θ ((M + 1 : ℕ) : ℝ) - θ (M : ℝ)) := fun m _ => by ring
    rw [sum_congr rfl hs, sum_add_distrib, ← ih, sum_const, card_range, nsmul_eq_mul,
      theta_natCast_succ M]
    split_ifs with hp
    · rw [sum_insert (by simp)]
      push_cast; ring
    · simp

/-- `∑_{p ≤ X} p ln p ≤ (1/2 + 2δ) X² + C X` for all `X ≥ 0` (`δ > 0`). -/
theorem sum_mul_log_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter Nat.Prime, (p : ℝ) * Real.log p ≤
        (1 / 2 + 2 * δ) * X ^ 2 + C * X := by
  obtain ⟨C1, hC1, h1⟩ := theta_upper_all hθ hδ
  obtain ⟨C2, hC2, h2⟩ := theta_lower_all hθ hδ
  refine ⟨C1 + C2 + 1, by positivity, fun X hX => ?_⟩
  set M := ⌊X⌋₊
  rw [sum_mul_log_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hMX : (M : ℝ) ≤ X := Nat.floor_le hX
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hup := h1 M hM0
  have hlow : ∑ m ∈ range M, ((1 - δ) * (m : ℝ) - C2) ≤ ∑ m ∈ range M, θ (m : ℝ) :=
    sum_le_sum fun m _ => h2 m (by positivity)
  rw [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hlow
  have hid : (∑ m ∈ range M, (m : ℝ)) * 2 = M * (M - 1) := by
    have := sum_range_id_mul_two M
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h]; simp
    · have : ((∑ i ∈ range M, i : ℕ) : ℝ) * 2 = (M : ℝ) * ((M - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub h, Nat.cast_one] at this; push_cast at this; exact this
  have key : (M : ℝ) * θ (M : ℝ) - ∑ m ∈ range M, θ (m : ℝ) ≤
      (1 / 2 + 2 * δ) * (M : ℝ) ^ 2 + (C1 + C2 + 1) * M := by
    have e1 : (M : ℝ) * θ (M : ℝ) ≤ M * ((1 + δ) * M + C1) := mul_le_mul_of_nonneg_left hup hM0
    nlinarith [mul_nonneg hM0 hM0, mul_nonneg (mul_nonneg hM0 hM0) hδ.le]
  have hsq : (M : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hM0 hMX 2
  have : (1 / 2 + 2 * δ) * (M : ℝ) ^ 2 ≤ (1 / 2 + 2 * δ) * X ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have : (C1 + C2 + 1) * (M : ℝ) ≤ (C1 + C2 + 1) * X := mul_le_mul_of_nonneg_left hMX (by positivity)
  linarith

end PrimeSums

/-- `∑_{3 ≤ p ≤ x} ln p/(p−1) ≤ ln x − γ − ln 2 + δ` for all large `x`. -/
theorem mertens_upper
    (hM : Tendsto (fun x : ℝ => mertensSum x - Real.log x) atTop
      (𝓝 (-Real.eulerMascheroniConstant - Real.log 2))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      mertensSum x ≤ Real.log x - Real.eulerMascheroniConstant - Real.log 2 + δ := by
  have hev := hM.eventually (Iio_mem_nhds (by linarith :
    -Real.eulerMascheroniConstant - Real.log 2 < -Real.eulerMascheroniConstant - Real.log 2 + δ))
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 hev
  exact ⟨x0, fun x hx => by have := hx0 x hx; exact le_of_lt (by linarith [show mertensSum x - Real.log x < _ from this])⟩

/-- `ln(4n) ≤ δ √n` for all large `n`. -/
theorem log_le_eps_sqrt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log (4 * n) ≤ δ * Real.sqrt n := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by linarith : 0 < δ / 2)
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 h
  refine ⟨⌈x0⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (⌈x0⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (1 : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) ⌈x0⌉₊]
  have hx : x0 ≤ 4 * (n : ℝ) := by linarith [Nat.le_ceil x0]
  have := hx0 _ hx
  have hl : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  linarith

end Hankel2
