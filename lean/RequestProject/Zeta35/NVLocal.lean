import RequestProject.Zeta35.NVHarm

/-!
# Non-vanishing (N, §6): the local expansions at a paired node

At a node `k` whose class modulo `ℓ` contains exactly one other node `k + δ` (`δ = ±ℓ`), the series
`u⁴ W(−k + u) = E_k(u)^{-1}` factors as `(u + δ)^{-4} · Y(u)` with `Y` an `ℓ`-integral series with
unit constant term `y₀ = ∏_{k' ≠ k, k+δ} (k' − k)^{-4}` (`Hser_eq_mate`, `PUnitS_mate`).  Hence
(`coeff_mate`) `ℓ^{4+b} H_k[b] ≡ (−ε)^b C(b+3,3) y₀ (mod ℓ)` with `δ = εℓ`.

`local_const` turns this into the leading terms of the pole parts of the local constants:
`ℓ^{10−a} β^ℓ_{k,a} ≡ y₀ · λ_a (mod ℓ)` with an explicit rational `λ_a` (no `ℓ` in it).
-/

open Polynomial Finset PowerSeries

namespace Zeta35.NV

/-- `E_k(u)^{-1} = (u + δ)^{-4} · (∏_{k' ≠ k, k + δ} (u + k' − k)^4)^{-1}`. -/
theorem Hser_eq_mate (S : Finset ℤ) {k δ : ℤ} (hkd : k + δ ∈ S) (hδ : δ ≠ 0) :
    PF.Hser S k = Blocks.invSub ((-δ : ℤ) : ℚ) 4 *
      (∏ k' ∈ (S.erase k).erase (k + δ),
        (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ 4)⁻¹ := by
  unfold PF.Hser PF.Ek
  rw [← Finset.mul_prod_erase (S.erase k) _ (Finset.mem_erase.2 ⟨by omega, hkd⟩),
    PowerSeries.mul_inv_rev, mul_comm]
  congr 1
  unfold Blocks.invSub
  congr 1
  have : ((k + δ - k : ℤ) : ℚ) = (δ : ℚ) := by push_cast; ring
  rw [this]
  have h2 : (PowerSeries.C (((-δ : ℤ) : ℚ)) - PowerSeries.X : ℚ⟦X⟧) =
      -(PowerSeries.C ((δ : ℚ)) + PowerSeries.X) := by
    push_cast; rw [map_neg]; ring
  rw [h2]; ring

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem PUnitS_mate (s : Finset ℤ) (k : ℤ) (hs : ∀ k' ∈ s, ¬ (ℓ : ℤ) ∣ (k' - k)) :
    Hankel2.W2.PUnitS ℓ
      (∏ k' ∈ s, (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ 4)⁻¹ := by
  refine Hankel2.W2.PUnitS.inv (Hankel2.W2.PUnitS.prod _ _ fun k' hk' => ?_)
  exact (Hankel2.W2.PUnitS.C_add_X ((padicNorm.int_eq_one_iff _).2 (hs k' hk'))).pow 4

theorem constantCoeff_mate (s : Finset ℤ) (k : ℤ) :
    constantCoeff (∏ k' ∈ s, (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ 4)⁻¹ =
      ((∏ k' ∈ s, (k' - k) ^ 4 : ℤ) : ℚ)⁻¹ := by
  rw [PowerSeries.constantCoeff_inv, map_prod]
  push_cast
  simp

/-- The term identity `ℓ^{4+b} ((eℓ)^{i+4})^{-1} = e^i ℓ^{b−i}` for `e = ±1`, `i ≤ b`. -/
theorem pow_mate_identity (e : ℚ) (he : e = 1 ∨ e = -1) (i b : ℕ) (hib : i ≤ b) :
    (ℓ : ℚ) ^ (4 + b) * ((e * ℓ) ^ (i + 3 + 1))⁻¹ = e ^ i * (ℓ : ℚ) ^ (b - i) := by
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hb : (ℓ : ℚ) ^ (4 + b) = (ℓ : ℚ) ^ (i + 3 + 1) * (ℓ : ℚ) ^ (b - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hb, mul_pow, mul_inv, show i + 3 + 1 = i + 4 by ring]
  have he2 : e ^ i * e ^ i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; rcases he with rfl | rfl <;> norm_num
  have he4 : e ^ (i + 4) = e ^ i := by
    rw [pow_add]; rcases he with rfl | rfl <;> norm_num
  have hei : (e ^ i)⁻¹ = e ^ i := by
    exact inv_eq_of_mul_eq_one_right he2
  rw [he4, hei]
  field_simp

/-- **The leading coefficients at a paired node**: with `δ = εℓ` (`ε = ±1`) and `Y` `ℓ`-integral,
`ℓ^{4+b} [u^b] ((u+δ)^{-4} Y) ≡ (−ε)^b C(b+3,3) Y(0) (mod ℓ)`, and it is `ℓ`-integral. -/
theorem coeff_mate (ε : ℚ) (hε : ε = 1 ∨ ε = -1) (δ : ℤ) (hδ : (δ : ℚ) = ε * ℓ)
    (Y : ℚ⟦X⟧) (hY : Hankel2.W2.PInt ℓ Y) (b : ℕ) :
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * coeff b (Blocks.invSub ((-δ : ℤ) : ℚ) 4 * Y) -
      (-ε) ^ b * ((b + 3).choose 3 : ℚ) * constantCoeff Y) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * coeff b (Blocks.invSub ((-δ : ℤ) : ℚ) 4 * Y)) 0 := by
  have hc : ((-δ : ℤ) : ℚ) = (-ε) * ℓ := by push_cast; rw [hδ]; ring
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hc0 : ((-δ : ℤ) : ℚ) ≠ 0 := by
    rw [hc]; rcases hε with rfl | rfl <;> simp [hl0]
  have he : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  have hYi : ∀ m, VB ℓ (coeff m Y) 0 := fun m => (VB_zero_iff _).2 (hY m)
  have hterm : ∀ i ∈ range (b + 1), (ℓ : ℚ) ^ (4 + b) *
      (coeff i (Blocks.invSub ((-δ : ℤ) : ℚ) 4) * coeff (b - i) Y) =
      ((i + 3).choose 3 : ℚ) * (-ε) ^ i * ((ℓ : ℚ) ^ (b - i) * coeff (b - i) Y) := by
    intro i hi
    have hib : i ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show (4 : ℕ) = 3 + 1 from rfl, Blocks.coeff_invSub_pow hc0, hc]
    have := pow_mate_identity (ℓ := ℓ) (-ε) he i b hib
    calc (ℓ : ℚ) ^ (4 + b) * (((i + 3).choose 3 : ℚ) * (((-ε) * ℓ) ^ (i + 3 + 1))⁻¹ *
          coeff (b - i) Y)
        = ((i + 3).choose 3 : ℚ) * ((ℓ : ℚ) ^ (4 + b) * (((-ε) * ℓ) ^ (i + 3 + 1))⁻¹) *
          coeff (b - i) Y := by ring
      _ = _ := by rw [this]; ring
  have hsum : (ℓ : ℚ) ^ (4 + b) * coeff b (Blocks.invSub ((-δ : ℤ) : ℚ) 4 * Y) =
      ∑ i ∈ range b, ((i + 3).choose 3 : ℚ) * (-ε) ^ i * ((ℓ : ℚ) ^ (b - i) * coeff (b - i) Y) +
        (-ε) ^ b * ((b + 3).choose 3 : ℚ) * constantCoeff Y := by
    rw [Blocks.coeff_mul_range, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_range_succ,
      Nat.sub_self, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]
    ring
  have hrest : VB ℓ (∑ i ∈ range b, ((i + 3).choose 3 : ℚ) * (-ε) ^ i *
      ((ℓ : ℚ) ^ (b - i) * coeff (b - i) Y)) 1 := by
    refine VB.sum _ _ fun i hi => ?_
    have hib : 1 ≤ b - i := by have := Finset.mem_range.mp hi; omega
    have h1 : VB ℓ ((-ε) ^ i) 0 := by
      rcases he with h | h <;> rw [h]
      · simpa using VB_one (ℓ := ℓ)
      · have := (VB_one (ℓ := ℓ)).neg.pow i; simpa using this
    have h2 := ((VB_nat (ℓ := ℓ) ((i + 3).choose 3)).mul h1).mul
      (((VB_l_pow (ℓ := ℓ) (b - i)).mono (show (1 : ℤ) ≤ ((b - i : ℕ) : ℤ) by exact_mod_cast hib)).mul (hYi (b - i)))
    simpa using h2
  have hlead : VB ℓ ((-ε) ^ b * ((b + 3).choose 3 : ℚ) * constantCoeff Y) 0 := by
    have h1 : VB ℓ ((-ε) ^ b) 0 := by
      rcases he with h | h <;> rw [h]
      · simpa using VB_one (ℓ := ℓ)
      · have := (VB_one (ℓ := ℓ)).neg.pow b; simpa using this
    have := (h1.mul (VB_nat (ℓ := ℓ) ((b + 3).choose 3))).mul
      (by have := hYi 0; rwa [coeff_zero_eq_constantCoeff_apply] at this)
    simpa using this
  rw [hsum]
  refine ⟨by simpa using hrest, ?_⟩
  exact (hrest.mono (by norm_num)).add hlead

/-- **The leading term of a pole-part local constant** (abstract form).  Suppose
`ℓ^{4+b} H_b ≡ ρ_b y₀ (mod ℓ)` with `ρ_b, y₀` integral, `σ_M` integral and `C ⊆ {1,2}`.  Then
`β_a = −∑_{i=1}^{4−a} i H_{4−i−a} σ_{i+1} (i+1) 3^{i+2} ∑_{c ∈ C} (cℓ)^{-(i+2)}` satisfies
`ℓ^{10−a} β_a ≡ y₀ λ_a (mod ℓ)`, `λ_a = −∑_i ∑_c i σ_{i+1} (i+1) 3^{i+2} c^{-(i+2)} ρ_{4−i−a}`. -/
theorem local_const (hℓ2 : ℓ ≠ 2) (Hb ρ σ : ℕ → ℚ) (y0 : ℚ) (Cs : Finset ℕ)
    (hC : ∀ c ∈ Cs, c = 1 ∨ c = 2) (hρ : ∀ b, VB ℓ (ρ b) 0) (hy0 : VB ℓ y0 0)
    (hσ : ∀ M, VB ℓ (σ M) 0) (hH : ∀ b, VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hb b - ρ b * y0) 1)
    (a : ℕ) (ha : a < 4) :
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * (-∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hb (4 - i - a) *
        (σ (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
          ∑ c ∈ Cs, (((c : ℚ) * ℓ) ^ (i + 1 + 1))⁻¹)) -
      y0 * (-∑ i ∈ Icc 1 (4 - a), ∑ c ∈ Cs, (i : ℚ) * σ (i + 1) * ((i + 1 : ℕ) : ℚ) *
        3 ^ (i + 1 + 1) * ((c : ℚ) ^ (i + 1 + 1))⁻¹ * ρ (4 - i - a))) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * (-∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hb (4 - i - a) *
        (σ (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
          ∑ c ∈ Cs, (((c : ℚ) * ℓ) ^ (i + 1 + 1))⁻¹))) 0 := by
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  -- the coefficient `κ_{i,c} = i σ_{i+1} (i+1) 3^{i+2} c^{-(i+2)}` is integral
  set κ : ℕ → ℕ → ℚ := fun i c => (i : ℚ) * σ (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
    ((c : ℚ) ^ (i + 1 + 1))⁻¹ with hκ
  have hκi : ∀ i, ∀ c ∈ Cs, VB ℓ (κ i c) 0 := by
    intro i c hc
    have hcinv : VB ℓ ((c : ℚ)⁻¹) 0 := by
      refine VB_inv_nat fun hd => ?_
      rcases hC c hc with rfl | rfl
      · exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp hd)
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 hd)
    have h3 : VB ℓ ((3 : ℚ) ^ (i + 1 + 1)) 0 := by
      have := (VB_nat (ℓ := ℓ) 3).pow (i + 1 + 1); simpa using this
    have := ((((VB_nat (ℓ := ℓ) i).mul (hσ (i + 1))).mul (VB_nat (ℓ := ℓ) (i + 1))).mul h3).mul
      (hcinv.pow (i + 1 + 1))
    simp only [hκ, ← inv_pow]; simpa using this
  -- the exact identity
  have hid : (ℓ : ℚ) ^ (10 - a) * (-∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hb (4 - i - a) *
        (σ (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
          ∑ c ∈ Cs, (((c : ℚ) * ℓ) ^ (i + 1 + 1))⁻¹)) =
      -∑ i ∈ Icc 1 (4 - a), ∑ c ∈ Cs, κ i c * ((ℓ : ℚ) ^ (4 + (4 - i - a)) * Hb (4 - i - a)) := by
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc0 : (c : ℚ) ≠ 0 := by rcases hC c hc with rfl | rfl <;> norm_num
    have hpow : (ℓ : ℚ) ^ (10 - a) = (ℓ : ℚ) ^ (4 + (4 - i - a)) * (ℓ : ℚ) ^ (i + 1 + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, hκ, mul_pow, mul_inv]
    field_simp
  rw [hid]
  have hlim : y0 * (-∑ i ∈ Icc 1 (4 - a), ∑ c ∈ Cs, (i : ℚ) * σ (i + 1) * ((i + 1 : ℕ) : ℚ) *
        3 ^ (i + 1 + 1) * ((c : ℚ) ^ (i + 1 + 1))⁻¹ * ρ (4 - i - a)) =
      -∑ i ∈ Icc 1 (4 - a), ∑ c ∈ Cs, κ i c * (ρ (4 - i - a) * y0) := by
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hκ]; ring
  rw [hlim]
  constructor
  · rw [show ∀ A B : ℚ, -A - -B = -(A - B) by intros; ring]
    refine VB.neg ?_
    rw [← Finset.sum_sub_distrib]
    refine VB.sum _ _ fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine VB.sum _ _ fun c hc => ?_
    rw [← mul_sub]
    simpa using (hκi i c hc).mul (hH (4 - i - a))
  · refine VB.neg (VB.sum _ _ fun i _ => VB.sum _ _ fun c hc => ?_)
    have h1 : VB ℓ ((ℓ : ℚ) ^ (4 + (4 - i - a)) * Hb (4 - i - a)) 0 := by
      have := (hH (4 - i - a)).mono (by norm_num : (0 : ℤ) ≤ 1)
      have h2 := this.add ((hρ (4 - i - a)).mul hy0)
      simpa using h2
    simpa using (hκi i c hc).mul h1

end Zeta35.NV
