import Mathlib

/-!
# The discrete logarithmic kernel is conditionally negative definite

This file supplies the "discrete CND step" of Lemma B (the archimedean bound for the 2-adic
Hankel determinants of family 2, see `ZETA7_STATUS.md`).

* `Hankel2.sum_log_one_add_sq_nonpos`: for arbitrary real nodes `x i` and real weights `τ i` of
  total mass zero, `∑ᵢ ∑ⱼ τᵢ τⱼ log (1 + (xᵢ - xⱼ)²) ≤ 0`.
  The proof is elementary: with `wₓ = (1/2 - x i)/(3/2 + x i)` (a Cayley transform, `‖wₓ‖ < 1`)
  one has `1 + (x - y)² = ‖1 - wₓ conj w_y‖² ‖3/2 + x i‖² ‖3/2 + y i‖² / 4`; the last three
  factors drop out against a mass-zero weight, and `-log ‖1 - z‖ = Re ∑ₙ zⁿ/n` turns the rest
  into `-∑ₙ ‖∑ᵢ τᵢ wᵢⁿ‖²/n ≤ 0`.
* `Hankel2.sum_offdiag_log_abs_le`: the version with the true kernel `log |xᵢ - xⱼ|` on distinct
  nodes, with the explicit error `∑_{i ≠ j} |τᵢ τⱼ| / (2 (xᵢ - xⱼ)²)`.
* `Hankel2.sum_offdiag_log_abs_int_le`: for integer nodes the error is at most
  `(π²/6) ∑ τᵢ²`, i.e. "the discrete log matrix is CND up to its diagonal".
* `Hankel2.quadratic_log_le_linearization`: the Lagrangian form used in Lemma B: for any two
  profiles of equal total mass, the quadratic energy with kernel `½ log (1 + d²)` is bounded by
  its linearization at the second profile.
-/

open Complex Finset
open scoped ComplexConjugate

namespace Hankel2

/-- The Cayley-type point attached to a real node `x`. -/
noncomputable def cayW (x : ℝ) : ℂ := (1 / 2 - x * I) / (3 / 2 + x * I)

/-- The companion factor `3/2 + x i`. -/
noncomputable def cayB (x : ℝ) : ℂ := 3 / 2 + x * I

lemma cayB_ne_zero (x : ℝ) : cayB x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [cayB] at this

lemma normSq_cayB (x : ℝ) : normSq (cayB x) = 9 / 4 + x ^ 2 := by
  simp [cayB, normSq_apply]; ring

lemma norm_cayW_lt_one (x : ℝ) : ‖cayW x‖ < 1 := by
  have hb : 0 < ‖cayB x‖ := norm_pos_iff.mpr (cayB_ne_zero x)
  have h1 : ‖(1 / 2 - x * I : ℂ)‖ < ‖cayB x‖ := by
    have e1 : ‖(1 / 2 - x * I : ℂ)‖ ^ 2 = 1 / 4 + x ^ 2 := by
      rw [Complex.sq_norm]; simp [normSq_apply]; ring
    have e2 : ‖cayB x‖ ^ 2 = 9 / 4 + x ^ 2 := by rw [Complex.sq_norm, normSq_cayB]
    have : ‖(1 / 2 - x * I : ℂ)‖ ^ 2 < ‖cayB x‖ ^ 2 := by rw [e1, e2]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  unfold cayW
  rw [norm_div, div_lt_one (by simpa [cayB] using hb)]
  simpa [cayB] using h1

lemma conj_cayW (y : ℝ) : conj (cayW y) = (1 / 2 + y * I) / (3 / 2 - y * I) := by
  simp [cayW, map_div₀, conj_ofReal, conj_I, sub_eq_add_neg, map_ofNat]

lemma conj_cayB (y : ℝ) : conj (cayB y) = 3 / 2 - y * I := by
  simp [cayB, conj_ofReal, conj_I, sub_eq_add_neg, map_ofNat]

lemma cay_identity (x y : ℝ) :
    (1 - cayW x * conj (cayW y)) * (cayB x * conj (cayB y)) = 2 * (1 + ((x - y : ℝ) : ℂ) * I) := by
  have hy : conj (cayB y) ≠ 0 := by simpa using cayB_ne_zero y
  have hx' : (3 / 2 + (x : ℂ) * I) ≠ 0 := by simpa [cayB] using cayB_ne_zero x
  have hy' : (3 / 2 - (y : ℂ) * I) ≠ 0 := by rwa [conj_cayB] at hy
  have hP : cayW x * conj (cayW y) * (cayB x * conj (cayB y)) =
      (1 / 2 - x * I) * (1 / 2 + y * I) := by
    rw [conj_cayW, conj_cayB]; unfold cayW cayB
    rw [div_mul_div_comm, div_mul_cancel₀ _ (mul_ne_zero hx' hy')]
  rw [sub_mul, one_mul, hP, conj_cayB]; unfold cayB; push_cast; ring

lemma norm_one_sub_cay_pos (x y : ℝ) : 0 < ‖1 - cayW x * conj (cayW y)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have h1 : cayW x * conj (cayW y) = 1 := by linear_combination -h
  have : ‖cayW x * conj (cayW y)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    have a := norm_cayW_lt_one x
    have b := norm_cayW_lt_one y
    calc ‖cayW x‖ * ‖cayW y‖ ≤ ‖cayW x‖ * 1 := by gcongr
      _ < 1 := by simpa using a
  rw [h1] at this; simp at this

/-- The key identity: the kernel splits into a "rank-one" part and `log ‖1 - w conj w'‖`. -/
lemma log_one_add_sq_eq (x y : ℝ) :
    Real.log (1 + (x - y) ^ 2) =
      2 * (Real.log ‖1 - cayW x * conj (cayW y)‖ + Real.log ‖cayB x‖ + Real.log ‖cayB y‖
        - Real.log 2) := by
  have hn : ‖(1 - cayW x * conj (cayW y)) * (cayB x * conj (cayB y))‖ =
      2 * ‖(1 + ((x - y : ℝ) : ℂ) * I)‖ := by
    rw [cay_identity]; simp
  have hsq : ‖(1 + ((x - y : ℝ) : ℂ) * I)‖ ^ 2 = 1 + (x - y) ^ 2 := by
    rw [Complex.sq_norm]; simp [normSq_apply]; ring
  have h0 := norm_one_sub_cay_pos x y
  have hbx : 0 < ‖cayB x‖ := norm_pos_iff.mpr (cayB_ne_zero x)
  have hby : 0 < ‖cayB y‖ := norm_pos_iff.mpr (cayB_ne_zero y)
  rw [norm_mul, norm_mul, Complex.norm_conj] at hn
  have : 1 + (x - y) ^ 2 = (‖1 - cayW x * conj (cayW y)‖ * ‖cayB x‖ * ‖cayB y‖ / 2) ^ 2 := by
    rw [← hsq]
    have : ‖(1 + ((x - y : ℝ) : ℂ) * I)‖ =
        ‖1 - cayW x * conj (cayW y)‖ * (‖cayB x‖ * ‖cayB y‖) / 2 := by linarith
    rw [this]; ring
  rw [this, Real.log_pow, Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  push_cast; ring

/-- `∑ᵢ∑ⱼ τᵢτⱼ Re((wᵢ conj wⱼ)ⁿ/n) = ‖∑ τᵢ wᵢⁿ‖² / n ≥ 0`. -/
lemma sum_sum_re_pow_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℂ) (τ : ι → ℝ) (n : ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * ((w i * conj (w j)) ^ n / (n : ℂ)).re := by
  set S : ℂ := ∑ i ∈ s, (τ i : ℂ) * w i ^ n with hS
  have key : ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * ((w i * conj (w j)) ^ n / (n : ℂ)).re =
      (S * conj S / (n : ℂ)).re := by
    have e : S * conj S / (n : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s, ((τ i * τ j : ℝ) : ℂ) * ((w i * conj (w j)) ^ n / (n : ℂ)) := by
      rw [hS, map_sum, Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, conj_ofReal, map_pow, mul_pow]
      push_cast; ring
    rw [e, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [key, Complex.mul_conj]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : ((normSq S : ℂ) / (n : ℂ)) = ((normSq S / n : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
    exact div_nonneg (normSq_nonneg _) (by positivity)

/-- `∑ᵢ∑ⱼ τᵢτⱼ log ‖1 - wᵢ conj wⱼ‖ ≤ 0` for points of the open unit disc. -/
lemma sum_sum_log_norm_one_sub_nonpos {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ < 1) (τ : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log ‖1 - w i * conj (w j)‖ ≤ 0 := by
  have hz : ∀ i j, ‖w i * conj (w j)‖ < 1 := by
    intro i j
    rw [norm_mul, Complex.norm_conj]
    calc ‖w i‖ * ‖w j‖ ≤ ‖w i‖ * 1 := by gcongr; exact (hw j).le
      _ < 1 := by simpa using hw i
  have hs : ∀ i j, HasSum (fun n : ℕ => ((w i * conj (w j)) ^ n / (n : ℂ)).re)
      (-Real.log ‖1 - w i * conj (w j)‖) := by
    intro i j
    have := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log (hz i j))
    simpa [Complex.log_re] using this
  have htot : HasSum (fun n : ℕ => ∑ i ∈ s, ∑ j ∈ s,
      τ i * τ j * ((w i * conj (w j)) ^ n / (n : ℂ)).re)
      (∑ i ∈ s, ∑ j ∈ s, τ i * τ j * (-Real.log ‖1 - w i * conj (w j)‖)) := by
    apply hasSum_sum; intro i _
    apply hasSum_sum; intro j _
    exact (hs i j).mul_left _
  have hnn := htot.nonneg (fun n => sum_sum_re_pow_nonneg s w τ n)
  have : ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * (-Real.log ‖1 - w i * conj (w j)‖) =
      -∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log ‖1 - w i * conj (w j)‖ := by
    simp [mul_neg, Finset.sum_neg_distrib]
  linarith

/-- **Discrete CND of the logarithmic kernel.**  For any real nodes and any real weights of
total mass zero, `∑ᵢ ∑ⱼ τᵢ τⱼ log (1 + (xᵢ - xⱼ)²) ≤ 0`. -/
theorem sum_log_one_add_sq_nonpos {ι : Type*} (s : Finset ι) (x τ : ι → ℝ)
    (hτ : ∑ i ∈ s, τ i = 0) :
    ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log (1 + (x i - x j) ^ 2) ≤ 0 := by
  set f : ι → ℝ := fun i => Real.log ‖cayB (x i)‖
  have e : ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log (1 + (x i - x j) ^ 2) =
      2 * ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log ‖1 - cayW (x i) * conj (cayW (x j))‖
      + 2 * (∑ i ∈ s, τ i * f i) * (∑ j ∈ s, τ j) + 2 * (∑ i ∈ s, τ i) * (∑ j ∈ s, τ j * f j)
      - 2 * Real.log 2 * (∑ i ∈ s, τ i) * (∑ j ∈ s, τ j) := by
    simp only [log_one_add_sq_eq, f, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, hτ]
  have := sum_sum_log_norm_one_sub_nonpos s (fun i => cayW (x i))
    (fun i => norm_cayW_lt_one (x i)) τ
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  linarith

/-- **The true logarithmic kernel on distinct nodes.**  For pairwise distinct real nodes and
weights of total mass zero,
`∑_{i ≠ j} τᵢ τⱼ log |xᵢ - xⱼ| ≤ ∑_{i ≠ j} |τᵢ τⱼ| / (2 (xᵢ - xⱼ)²)`. -/
theorem sum_offdiag_log_abs_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x τ : ι → ℝ)
    (hx : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i ≠ x j) (hτ : ∑ i ∈ s, τ i = 0) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, τ i * τ j * Real.log |x i - x j| ≤
      ∑ i ∈ s, ∑ j ∈ s.erase i, |τ i * τ j| / (2 * (x i - x j) ^ 2) := by
  have hmain := sum_log_one_add_sq_nonpos s x τ hτ
  -- the diagonal of the smooth kernel vanishes
  have hdiag : ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log (1 + (x i - x j) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, τ i * τ j * Real.log (1 + (x i - x j) ^ 2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase s _ hi]
    simp
  have hpt : ∀ i ∈ s, ∀ j ∈ s.erase i,
      τ i * τ j * Real.log |x i - x j| ≤
        τ i * τ j * Real.log (1 + (x i - x j) ^ 2) / 2 + |τ i * τ j| / (2 * (x i - x j) ^ 2) := by
    intro i hi j hj
    have hij : x i - x j ≠ 0 := sub_ne_zero.mpr (hx i hi j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj).symm)
    set d := x i - x j
    have hd2 : 0 < d ^ 2 := by positivity
    -- log |d| = ½ log(1+d²) - ½ log(1 + 1/d²)
    have hsplit : Real.log |d| = Real.log (1 + d ^ 2) / 2 - Real.log (1 + 1 / d ^ 2) / 2 := by
      have h1 : 1 + d ^ 2 = d ^ 2 * (1 + 1 / d ^ 2) := by field_simp; ring
      rw [h1, Real.log_mul hd2.ne' (by positivity), Real.log_pow]
      simp [Real.log_abs]; ring
    have hlog0 : 0 ≤ Real.log (1 + 1 / d ^ 2) := Real.log_nonneg (by
      have : 0 ≤ 1 / d ^ 2 := by positivity
      linarith)
    have hlog1 : Real.log (1 + 1 / d ^ 2) ≤ 1 / d ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / d ^ 2 by positivity)
      linarith
    rw [hsplit]
    have hab : -(τ i * τ j) ≤ |τ i * τ j| := neg_le_abs _
    have : -(τ i * τ j) * (Real.log (1 + 1 / d ^ 2) / 2) ≤ |τ i * τ j| * (1 / d ^ 2 / 2) := by
      calc -(τ i * τ j) * (Real.log (1 + 1 / d ^ 2) / 2)
          ≤ |τ i * τ j| * (Real.log (1 + 1 / d ^ 2) / 2) := by
            apply mul_le_mul_of_nonneg_right hab; positivity
        _ ≤ |τ i * τ j| * (1 / d ^ 2 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    have e2 : |τ i * τ j| / (2 * d ^ 2) = |τ i * τ j| * (1 / d ^ 2 / 2) := by
      field_simp
    rw [e2]; nlinarith [this]
  calc ∑ i ∈ s, ∑ j ∈ s.erase i, τ i * τ j * Real.log |x i - x j|
      ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, (τ i * τ j * Real.log (1 + (x i - x j) ^ 2) / 2
          + |τ i * τ j| / (2 * (x i - x j) ^ 2)) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpt i hi j hj
    _ = (∑ i ∈ s, ∑ j ∈ s.erase i, τ i * τ j * Real.log (1 + (x i - x j) ^ 2)) / 2
          + ∑ i ∈ s, ∑ j ∈ s.erase i, |τ i * τ j| / (2 * (x i - x j) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, |τ i * τ j| / (2 * (x i - x j) ^ 2) := by
        rw [← hdiag]; linarith

/-- **Linearization (Lagrangian) bound.**  With the CND kernel `B(x,y) = ½ log (1 + (x-y)²)`,
for any two real profiles `σ, σ₀` of equal total mass the quadratic energy of `σ` is at most
its linearization at `σ₀`. -/
theorem quadratic_log_le_linearization {ι : Type*} (s : Finset ι) (x σ σ₀ : ι → ℝ)
    (hmass : ∑ i ∈ s, σ i = ∑ i ∈ s, σ₀ i) :
    ∑ i ∈ s, ∑ j ∈ s, σ i * σ j * (Real.log (1 + (x i - x j) ^ 2) / 2) ≤
      ∑ i ∈ s, ∑ j ∈ s, σ₀ i * σ₀ j * (Real.log (1 + (x i - x j) ^ 2) / 2)
      + 2 * ∑ i ∈ s, (σ i - σ₀ i) * ∑ j ∈ s, (Real.log (1 + (x i - x j) ^ 2) / 2) * σ₀ j := by
  set τ : ι → ℝ := fun i => σ i - σ₀ i
  have hτ : ∑ i ∈ s, τ i = 0 := by simp [τ, Finset.sum_sub_distrib, hmass]
  have hcnd := sum_log_one_add_sq_nonpos s x τ hτ
  set B : ι → ι → ℝ := fun i j => Real.log (1 + (x i - x j) ^ 2) / 2
  have hB : ∀ i j, B i j = B j i := by
    intro i j; simp only [B]; ring_nf
  -- expand σ = σ₀ + τ
  have hexp : ∑ i ∈ s, ∑ j ∈ s, σ i * σ j * B i j =
      ∑ i ∈ s, ∑ j ∈ s, σ₀ i * σ₀ j * B i j
      + 2 * ∑ i ∈ s, τ i * ∑ j ∈ s, B i j * σ₀ j
      + (∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log (1 + (x i - x j) ^ 2)) / 2 := by
    have hsym : ∑ i ∈ s, ∑ j ∈ s, σ₀ i * τ j * B i j = ∑ i ∈ s, ∑ j ∈ s, τ i * σ₀ j * B i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hB]; ring
    have h1 : ∑ i ∈ s, ∑ j ∈ s, σ i * σ j * B i j =
        ∑ i ∈ s, ∑ j ∈ s, σ₀ i * σ₀ j * B i j + ∑ i ∈ s, ∑ j ∈ s, σ₀ i * τ j * B i j
        + ∑ i ∈ s, ∑ j ∈ s, τ i * σ₀ j * B i j + ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * B i j := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [τ]; ring
    rw [h1, hsym]
    have h2 : ∑ i ∈ s, ∑ j ∈ s, τ i * σ₀ j * B i j = ∑ i ∈ s, τ i * ∑ j ∈ s, B i j * σ₀ j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : ∑ i ∈ s, ∑ j ∈ s, τ i * τ j * B i j =
        (∑ i ∈ s, ∑ j ∈ s, τ i * τ j * Real.log (1 + (x i - x j) ^ 2)) / 2 := by
      simp only [Finset.sum_div, B]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2, h3]; ring
  change ∑ i ∈ s, ∑ j ∈ s, σ i * σ j * B i j ≤
      ∑ i ∈ s, ∑ j ∈ s, σ₀ i * σ₀ j * B i j + 2 * ∑ i ∈ s, τ i * ∑ j ∈ s, B i j * σ₀ j
  rw [hexp]
  linarith

/-- For distinct integer nodes, `∑_{j ≠ i} 1/(i - j)² ≤ π²/3`. -/
lemma sum_erase_inv_sq_le (s : Finset ℤ) (i : ℤ) :
    ∑ j ∈ s.erase i, 1 / ((i : ℝ) - j) ^ 2 ≤ Real.pi ^ 2 / 3 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s.erase i) (fun j => j < i)]
  have h1 : ∑ j ∈ (s.erase i).filter (fun j => j < i), 1 / ((i : ℝ) - j) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    have e : ∑ j ∈ (s.erase i).filter (fun j => j < i), 1 / ((i : ℝ) - j) ^ 2 =
        ∑ m ∈ ((s.erase i).filter (fun j => j < i)).image (fun j => (i - j).toNat),
          1 / (m : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_filter] at hj
        have h := Int.toNat_of_nonneg (show 0 ≤ i - j by omega)
        have : ((i - j).toNat : ℝ) = (i : ℝ) - j := by exact_mod_cast h
        rw [this]
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only at hab
        omega
    rw [e]; exact sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two
  have h2 : ∑ j ∈ (s.erase i).filter (fun j => ¬ j < i), 1 / ((i : ℝ) - j) ^ 2 ≤
      Real.pi ^ 2 / 6 := by
    have e : ∑ j ∈ (s.erase i).filter (fun j => ¬ j < i), 1 / ((i : ℝ) - j) ^ 2 =
        ∑ m ∈ ((s.erase i).filter (fun j => ¬ j < i)).image (fun j => (j - i).toNat),
          1 / (m : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_filter] at hj
        have h := Int.toNat_of_nonneg (show 0 ≤ j - i by omega)
        have : ((j - i).toNat : ℝ) = (j : ℝ) - i := by exact_mod_cast h
        rw [this]; ring
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        simp only at hab
        omega
    rw [e]; exact sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two
  linarith

/-- **Integer nodes.**  For distinct integer nodes and weights of total mass zero,
`∑_{i ≠ j} τᵢ τⱼ log |i - j| ≤ (π²/6) ∑ τᵢ²`. -/
theorem sum_offdiag_log_abs_int_le (s : Finset ℤ) (τ : ℤ → ℝ) (hτ : ∑ i ∈ s, τ i = 0) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, τ i * τ j * Real.log |(i : ℝ) - j| ≤
      Real.pi ^ 2 / 6 * ∑ i ∈ s, τ i ^ 2 := by
  have hgen := sum_offdiag_log_abs_le s (fun i : ℤ => (i : ℝ)) τ
    (fun i _ j _ hij h => hij (by simpa using h)) hτ
  refine le_trans hgen ?_
  -- |ab| ≤ (a² + b²)/2, then symmetrize
  have hpt : ∀ i ∈ s, ∀ j ∈ s.erase i, |τ i * τ j| / (2 * ((i : ℝ) - j) ^ 2) ≤
      τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) + τ j ^ 2 / (4 * ((i : ℝ) - j) ^ 2) := by
    intro i _ j _
    have hab : |τ i * τ j| / 2 ≤ (τ i ^ 2 + τ j ^ 2) / 4 := by
      rw [abs_mul]; nlinarith [sq_nonneg (|τ i| - |τ j|), sq_abs (τ i), sq_abs (τ j)]
    have hd : 0 ≤ ((i : ℝ) - j) ^ 2 := sq_nonneg _
    have e1 : |τ i * τ j| / (2 * ((i : ℝ) - j) ^ 2) = (|τ i * τ j| / 2) / ((i : ℝ) - j) ^ 2 := by
      rw [div_div]
    have e2 : τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) + τ j ^ 2 / (4 * ((i : ℝ) - j) ^ 2) =
        ((τ i ^ 2 + τ j ^ 2) / 4) / ((i : ℝ) - j) ^ 2 := by
      rw [div_div, ← add_div]
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hab hd
  have hfull : ∀ (f : ℤ → ℤ → ℝ), (∀ i, f i i = 0) →
      ∑ i ∈ s, ∑ j ∈ s.erase i, f i j = ∑ i ∈ s, ∑ j ∈ s, f i j := by
    intro f hf
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_erase s (hf i)
  have hA : ∑ i ∈ s, ∑ j ∈ s.erase i, τ j ^ 2 / (4 * ((i : ℝ) - j) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s.erase i, τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) := by
    rw [hfull _ (fun i => by simp), hfull _ (fun i => by simp), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : ∀ i ∈ s, ∑ j ∈ s.erase i, τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) ≤
      τ i ^ 2 / 4 * (Real.pi ^ 2 / 3) := by
    intro i _
    have : ∑ j ∈ s.erase i, τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) =
        τ i ^ 2 / 4 * ∑ j ∈ s.erase i, 1 / ((i : ℝ) - j) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (sum_erase_inv_sq_le s i) (by positivity)
  calc ∑ i ∈ s, ∑ j ∈ s.erase i, |τ i * τ j| / (2 * ((fun i : ℤ => (i : ℝ)) i -
          (fun i : ℤ => (i : ℝ)) j) ^ 2)
      ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, (τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) +
          τ j ^ 2 / (4 * ((i : ℝ) - j) ^ 2)) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpt i hi j hj
    _ = 2 * ∑ i ∈ s, ∑ j ∈ s.erase i, τ i ^ 2 / (4 * ((i : ℝ) - j) ^ 2) := by
        simp only [Finset.sum_add_distrib]; rw [hA]; ring
    _ ≤ 2 * ∑ i ∈ s, τ i ^ 2 / 4 * (Real.pi ^ 2 / 3) := by
        gcongr with i hi; exact hB i hi
    _ = Real.pi ^ 2 / 6 * ∑ i ∈ s, τ i ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
end Hankel2
