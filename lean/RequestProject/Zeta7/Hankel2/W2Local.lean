import Mathlib

/-!
# W2: local valuations of the harmonic-sum constants (family 3)

`ZETA7_STATUS.md`, rounds (e) and (h).  Family 3:
`W(t) = (2t+n)(t+1/2)_n^6 / ∏_{k'=-n}^{2n} (t+k')^4`.  At the node `t = -k` put `t = -k + u`; the Taylor
series of `(t+k)^4 W(t)` in `u` is

  `H_k(u) = (2u + n - 2k) · ∏_{j<n} (u + j + 1/2 - k)^6 · ∏_{k' ≠ k} (u + k' - k)^{-4}`   (`fam3H n k`).

At an odd prime `p` the harmonic-sum constants of a harmonic-sum (HS) node carry exactly one `p`-term,
`(2/q)^M` with `q = p` (right nodes) or `q = -p` (left nodes, with an overall sign), and the `p`-part of the
constants of the functional at the node is (up to that sign)

  `c_a = - Σ_{i=1}^{4-a} i(i+1)(i+2)(i+3) (2/q)^{i+4} [u^{4-i-a}] H_k(u)`     (`hsConst q (fam3H n k) a`).

**Lemma W2** (proved here for every odd `n` and every prime `p` with `7n+2 ≤ 4p` and `p ≤ 2n-1`):

* special right nodes `n + (p+1)/2 ≤ k ≤ 2n` and special left nodes `-n ≤ k ≤ -(p+1)/2`:
  `|c_a|_p = p^{12-a}` for `a = 0,1,2,3` (valuations `(-12,-11,-10,-9)`);
* generic right nodes `(p+1)/2 ≤ k ≤ n + (p-1)/2`, `2k ≠ n + p`:
  `|c_0|_p ≤ p^5`, `|c_1|_p = p^5`, `|c_2|_p = p^4`, `|c_3|_p = p^3`;
* the node `g*` (`2k = n + p`): `|c_0|_p = p^5`, `|c_1|_p = p^4`, `|c_2|_p ≤ p^2`, `|c_3|_p = p^2`.

Also proved (`w4_generic_pair_coeff`, `w4_special_pair_coeff`): the local pair expansions used in W4,
`[u^m] (u - q)^{-4} (u - q/2)^6 ∈ p^{2-m} ℤ_p` and `[u^m] (u - q)^{-4} ∈ p^{-4-m} ℤ_p` for `v_p(q) = 1`.

The proof factors `H_k = Y · S` with `Y` a `p`-integral power series with unit constant term (all Taylor
factors whose constant is a `p`-adic unit) and `S` the `p`-small factors, which after the substitution
`u = q z` become a fixed rational series `G` (`S = s · G(u/q)`).  Then
`c_a = -s Σ_r q^{-(8-a-r)} Y_r N_{a,r}(G)` with explicit integers `N_{a,r}(G)`.
-/

open PowerSeries

namespace Hankel2
namespace W2

/-! ### `p`-integral power series -/

section Integral

variable (p : ℕ) [Fact p.Prime]

/-- All coefficients are `p`-integral. -/
def PInt (f : ℚ⟦X⟧) : Prop := ∀ m, padicNorm p (coeff m f) ≤ 1

/-- `p`-integral with a `p`-adic unit as constant term. -/
def PUnitS (f : ℚ⟦X⟧) : Prop := PInt p f ∧ padicNorm p (constantCoeff f) = 1

variable {p}

theorem PInt.mul {f g : ℚ⟦X⟧} (hf : PInt p f) (hg : PInt p g) : PInt p (f * g) := by
  intro m
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one₀ (hf _) (padicNorm.nonneg _) (hg _)

theorem PUnitS.mul {f g : ℚ⟦X⟧} (hf : PUnitS p f) (hg : PUnitS p g) : PUnitS p (f * g) :=
  ⟨hf.1.mul hg.1, by rw [map_mul, padicNorm.mul, hf.2, hg.2, one_mul]⟩

omit [Fact p.Prime] in
theorem PUnitS.one : PUnitS p (1 : ℚ⟦X⟧) := by
  refine ⟨fun m => ?_, by simp⟩
  rw [coeff_one]; split_ifs <;> simp

theorem PUnitS.pow {f : ℚ⟦X⟧} (hf : PUnitS p f) (e : ℕ) : PUnitS p (f ^ e) := by
  induction e with
  | zero => simpa using PUnitS.one
  | succ e ih => rw [pow_succ]; exact ih.mul hf

theorem PUnitS.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ⟦X⟧) (hf : ∀ i ∈ s, PUnitS p (f i)) :
    PUnitS p (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _ _ ha hb => ha.mul hb) PUnitS.one hf

theorem padicNorm_inv (q : ℚ) : padicNorm p q⁻¹ = (padicNorm p q)⁻¹ := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]

theorem PUnitS.inv {f : ℚ⟦X⟧} (hf : PUnitS p f) : PUnitS p f⁻¹ := by
  have h0 : padicNorm p (constantCoeff f)⁻¹ = 1 := by rw [padicNorm_inv, hf.2, inv_one]
  have hint : ∀ m, padicNorm p (coeff m f⁻¹) ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rw [coeff_inv]
      split_ifs with hm
      · exact h0.le
      · rw [padicNorm.mul, padicNorm.neg, h0, one_mul]
        refine padicNorm.sum_le' (fun x hx => ?_) zero_le_one
        split_ifs with hlt
        · rw [padicNorm.mul]
          exact mul_le_one₀ (hf.1 _) (padicNorm.nonneg _) (ih _ hlt)
        · simp
  refine ⟨hint, ?_⟩
  have : constantCoeff f⁻¹ = (constantCoeff f)⁻¹ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv, if_pos rfl]
  rw [this, h0]

omit [Fact p.Prime] in
theorem PUnitS.C_add_C_mul_X {c d : ℚ} (hc : padicNorm p c = 1) (hd : padicNorm p d ≤ 1) :
    PUnitS p (C c + C d * X) := by
  refine ⟨fun m => ?_, by simpa using hc⟩
  rcases m with _ | _ | m
  · simpa using hc.le
  · simpa using hd
  · simp

omit [Fact p.Prime] in
theorem PUnitS.C_add_X {c : ℚ} (hc : padicNorm p c = 1) : PUnitS p (C c + X) := by
  simpa using PUnitS.C_add_C_mul_X (p := p) (d := 1) hc (by simp)

end Integral

/-! ### The harmonic-sum constants and their reduction to integers `N_{a,r}` -/

/-- The `p`-part of the constants of the functional at an HS node:
`c_a = - Σ_{i=0}^{3-a} (i+1)(i+2)(i+3)(i+4) (2/q)^{i+5} [u^{3-i-a}] H`. -/
noncomputable def hsConst (q : ℚ) (H : ℚ⟦X⟧) (a : ℕ) : ℚ :=
  -∑ i ∈ Finset.range (4 - a), ((i + 1) * (i + 2) * (i + 3) * (i + 4) : ℚ) * (2 / q) ^ (i + 5) *
    coeff (3 - i - a) H

/-- The integers `N_{a,r}(G) = Σ_i (i+1)(i+2)(i+3)(i+4) 2^{i+5} [z^{3-i-a-r}] G`. -/
noncomputable def Ncoef (a r : ℕ) (G : ℚ⟦X⟧) : ℚ :=
  ∑ i ∈ Finset.range (4 - a - r), ((i + 1) * (i + 2) * (i + 3) * (i + 4) : ℚ) * 2 ^ (i + 5) *
    coeff (3 - i - a - r) G

theorem hsConst_eq (q s : ℚ) (Y G : ℚ⟦X⟧) (a : ℕ) (ha : a ≤ 3) :
    hsConst q (Y * (C s * rescale q⁻¹ G)) a =
      -s * ∑ r ∈ Finset.range (4 - a), q⁻¹ ^ (8 - a - r) * coeff r Y * Ncoef a r G := by
  interval_cases a <;>
  simp [hsConst, Ncoef, coeff_mul, coeff_rescale, Finset.sum_range_succ,
    Finset.Nat.antidiagonal_succ, div_eq_mul_inv] <;> ring

/-! ### From the integers `N_{a,r}` to valuations -/

section Val

variable {p : ℕ} [Fact p.Prime]

theorem padicNorm_pow' (q : ℚ) (e : ℕ) : padicNorm p (q ^ e) = padicNorm p q ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

theorem one_le_p : (1 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le

theorem hsConst_term_le {q : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) {Y : ℚ⟦X⟧} (hY : PInt p Y)
    {N : ℚ} (hN : padicNorm p N ≤ 1) (e : ℕ) :
    padicNorm p (q⁻¹ ^ e * coeff r Y * N) ≤ (p : ℚ) ^ e := by
  rw [padicNorm.mul, padicNorm.mul, padicNorm_pow', padicNorm_inv, hq, inv_inv]
  have h1 : (0 : ℚ) ≤ (p : ℚ) ^ e := by positivity
  calc (p : ℚ) ^ e * padicNorm p (coeff r Y) * padicNorm p N ≤ (p : ℚ) ^ e * 1 * 1 := by
        gcongr
        exacts [padicNorm.nonneg _, hY r]
    _ = _ := by ring

/-- Upper bound: `|c_a|_p ≤ |s|_p p^b` as soon as every `r` with `N_{a,r} ≠ 0` has `8 - a - r ≤ b`. -/
theorem norm_hsConst_le {q s : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) {Y G : ℚ⟦X⟧} (hY : PInt p Y)
    {a : ℕ} (ha : a ≤ 3) (hN : ∀ r, padicNorm p (Ncoef a r G) ≤ 1) (b : ℕ)
    (hb : ∀ r < 4 - a, Ncoef a r G = 0 ∨ 8 - a - r ≤ b) :
    padicNorm p (hsConst q (Y * (C s * rescale q⁻¹ G)) a) ≤ padicNorm p s * (p : ℚ) ^ b := by
  rw [hsConst_eq q s Y G a ha, padicNorm.mul, padicNorm.neg]
  refine mul_le_mul_of_nonneg_left ?_ (padicNorm.nonneg _)
  refine padicNorm.sum_le' (fun r hr => ?_) (pow_nonneg (Nat.cast_nonneg _) _)
  rcases hb r (Finset.mem_range.1 hr) with h | h
  · simp [h]
  · exact (hsConst_term_le hq hY (hN r) _).trans (pow_le_pow_right₀ one_le_p h)

theorem padicNorm_add_eq_of_lt {x y : ℚ} (hxy : padicNorm p x < padicNorm p y) :
    padicNorm p (x + y) = padicNorm p y := by
  rw [padicNorm.add_eq_max_of_ne hxy.ne, max_eq_right hxy.le]

/-- Exact value: `|c_a|_p = |s|_p p^{8-a}` when `Y` has unit constant term and `N_{a,0}` is a unit. -/
theorem norm_hsConst_eq {q s : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) {Y G : ℚ⟦X⟧} (hY : PUnitS p Y)
    {a : ℕ} (ha : a ≤ 3) (hN : ∀ r, padicNorm p (Ncoef a r G) ≤ 1)
    (hN0 : padicNorm p (Ncoef a 0 G) = 1) :
    padicNorm p (hsConst q (Y * (C s * rescale q⁻¹ G)) a) = padicNorm p s * (p : ℚ) ^ (8 - a) := by
  rw [hsConst_eq q s Y G a ha, padicNorm.mul, padicNorm.neg]
  congr 1
  obtain ⟨t, ht⟩ : ∃ t, 4 - a = t + 1 := ⟨3 - a, by omega⟩
  rw [ht, Finset.sum_range_succ']
  have h0 : padicNorm p (q⁻¹ ^ (8 - a - 0) * coeff 0 Y * Ncoef a 0 G) = (p : ℚ) ^ (8 - a) := by
    rw [padicNorm.mul, padicNorm.mul, padicNorm_pow', padicNorm_inv, hq, inv_inv, hN0,
      coeff_zero_eq_constantCoeff_apply, hY.2]
    simp
  rw [padicNorm_add_eq_of_lt, h0]
  rw [h0]
  refine lt_of_le_of_lt (padicNorm.sum_le' (t := (p : ℚ) ^ (7 - a)) (fun r hr => ?_)
    (by positivity)) ?_
  · exact (hsConst_term_le hq hY.1 (hN _) _).trans (pow_le_pow_right₀ one_le_p (by omega))
  · exact pow_lt_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt) (by omega)

end Val

/-! ### The three model series `G` and their integers `N_{a,r}` -/

section Model

/-- `(z - 1)^{-4}`: the special-node model. -/
noncomputable def Gsp : ℚ⟦X⟧ := ((C (-1 : ℚ) + X)⁻¹) ^ 4

/-- `(z - 1)^{-4} (z - 1/2)^6`: the generic-node model. -/
noncomputable def Ggen : ℚ⟦X⟧ := Gsp * (C (-1 / 2 : ℚ) + X) ^ 6

/-- `(z - 1)^{-4} (z - 1/2)^6 (2z - 1)`: the model at `g*`. -/
noncomputable def Gst : ℚ⟦X⟧ := Ggen * (C (-1 : ℚ) + C 2 * X)

theorem inv_C_neg_one_add_X : (C (-1 : ℚ) + X)⁻¹ = mk fun _ => (-1 : ℚ) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  ext n
  rcases n with _ | n
  · simp [mul_add]
  · simp [mul_add, coeff_succ_mul_X, coeff_one]

theorem Gsp_coeff : coeff 0 Gsp = 1 ∧ coeff 1 Gsp = 4 ∧ coeff 2 Gsp = 10 ∧ coeff 3 Gsp = 20 := by
  simp only [Gsp, inv_C_neg_one_add_X]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num

theorem lin6_coeff : coeff 0 ((C (-1 / 2 : ℚ) + X) ^ 6) = 1 / 64 ∧
    coeff 1 ((C (-1 / 2 : ℚ) + X) ^ 6) = -3 / 16 ∧
    coeff 2 ((C (-1 / 2 : ℚ) + X) ^ 6) = 15 / 16 ∧ coeff 3 ((C (-1 / 2 : ℚ) + X) ^ 6) = -5 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ, coeff_X] <;> norm_num

theorem Ggen_coeff : coeff 0 Ggen = 1 / 64 ∧ coeff 1 Ggen = -1 / 8 ∧ coeff 2 Ggen = 11 / 32 ∧
    coeff 3 Ggen = -5 / 16 := by
  obtain ⟨h0, h1, h2, h3⟩ := Gsp_coeff
  obtain ⟨l0, l1, l2, l3⟩ := lin6_coeff
  simp only [Ggen]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map] <;> simp [h0, h1, h2, h3, l0, l1, l2, l3] <;> norm_num

theorem Gst_coeff : coeff 0 Gst = -1 / 64 ∧ coeff 1 Gst = 5 / 32 ∧ coeff 2 Gst = -19 / 32 ∧
    coeff 3 Gst = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := Ggen_coeff
  simp only [Gst]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map] <;> simp [h0, h1, h2, h3] <;> norm_num

theorem Ncoef_eq_zero_of_le {a r : ℕ} (G : ℚ⟦X⟧) (h : 4 - a ≤ r) : Ncoef a r G = 0 := by
  simp [Ncoef, show 4 - a - r = 0 by omega]

variable {p : ℕ} [Fact p.Prime]

/-- The leading integers `N_{a,0}`. -/
theorem Ncoef_values :
    Ncoef 0 0 Gsp = 491520 ∧ Ncoef 1 0 Gsp = 84480 ∧ Ncoef 2 0 Gsp = 10752 ∧ Ncoef 3 0 Gsp = 768 ∧
    Ncoef 0 0 Ggen = 0 ∧ Ncoef 1 0 Ggen = 24 ∧ Ncoef 2 0 Ggen = 24 ∧ Ncoef 3 0 Ggen = 12 ∧
    Ncoef 0 0 Gst = 48 ∧ Ncoef 1 0 Gst = 24 ∧ Ncoef 2 0 Gst = 0 ∧ Ncoef 3 0 Gst = -12 := by
  obtain ⟨h0, h1, h2, h3⟩ := Gsp_coeff
  obtain ⟨g0, g1, g2, g3⟩ := Ggen_coeff
  obtain ⟨s0, s1, s2, s3⟩ := Gst_coeff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [Ncoef, Finset.sum_range_succ, h0, h1, h2, h3, g0, g1, g2, g3, s0, s1, s2, s3] <;> norm_num

theorem Ncoef_shift (a r : ℕ) (G : ℚ⟦X⟧) : Ncoef a r G = Ncoef (a + r) 0 G := by
  simp only [Ncoef, Nat.sub_sub, Nat.sub_zero, add_assoc]

variable {p : ℕ} [Fact p.Prime]

/-- All `N_{a,r}` of the three models are `p`-integral (they are integers). -/
theorem Ncoef_le_one {G : ℚ⟦X⟧} (hG : G = Gsp ∨ G = Ggen ∨ G = Gst) (a r : ℕ) :
    padicNorm p (Ncoef a r G) ≤ 1 := by
  rw [Ncoef_shift]
  obtain ⟨v0, v1, v2, v3, w0, w1, w2, w3, u0, u1, u2, u3⟩ := Ncoef_values
  have hi : ∀ z : ℤ, padicNorm p (z : ℚ) ≤ 1 := fun z => padicNorm.of_int z
  by_cases hm : 4 ≤ a + r
  · simp [Ncoef_eq_zero_of_le G (show 4 - (a + r) ≤ 0 by omega)]
  have : a + r = 0 ∨ a + r = 1 ∨ a + r = 2 ∨ a + r = 3 := by omega
  rcases hG with rfl | rfl | rfl <;> rcases this with h | h | h | h <;> rw [h]
  · rw [v0]; exact_mod_cast hi 491520
  · rw [v1]; exact_mod_cast hi 84480
  · rw [v2]; exact_mod_cast hi 10752
  · rw [v3]; exact_mod_cast hi 768
  · rw [w0]; exact_mod_cast hi 0
  · rw [w1]; exact_mod_cast hi 24
  · rw [w2]; exact_mod_cast hi 24
  · rw [w3]; exact_mod_cast hi 12
  · rw [u0]; exact_mod_cast hi 48
  · rw [u1]; exact_mod_cast hi 24
  · rw [u2]; exact_mod_cast hi 0
  · rw [u3]; exact_mod_cast hi (-12)

theorem smooth_prime_le {q a b c d e : ℕ} (hq : q.Prime) (h : q ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) :
    q ≤ 11 := by
  simp only [hq.dvd_mul] at h
  rcases h with (((h | h) | h) | h) | h <;>
    have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h) <;> omega

/-- A `{2,3,5,7,11}`-smooth integer is a unit at every prime `p ≥ 13`. -/
theorem padicNorm_smooth (hp : 13 ≤ p) (a b c d e : ℕ) :
    padicNorm p ((2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e : ℕ) : ℚ) = 1 := by
  rw [padicNorm.nat_eq_one_iff]
  intro h
  have := smooth_prime_le (Fact.out : p.Prime) h
  omega

end Model

/-! ### Scaling `u = q z` -/

section Scaling

theorem rescale_C' (w c : ℚ) : rescale w (C c) = C c := by
  ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]

theorem rescale_lin (w c d : ℚ) : rescale w (C c + C d * X) = C c + C (d * w) * X := by
  simp [rescale_X, map_mul, rescale_C']
  ring

theorem rescale_inv' (w : ℚ) (f : ℚ⟦X⟧) (hf : constantCoeff f ≠ 0) :
    rescale w f⁻¹ = (rescale w f)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]
  · rwa [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]

theorem C_mul_inv (a : ℚ) (f : ℚ⟦X⟧) : (C a * f)⁻¹ = C a⁻¹ * f⁻¹ := by
  rw [PowerSeries.mul_inv_rev, C_inv, mul_comm]

theorem scale_inv_lin {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ (C (-1 : ℚ) + X)⁻¹ = C q * (C (-q) + X)⁻¹ := by
  rw [rescale_inv' _ _ (by simp)]
  have : rescale q⁻¹ (C (-1 : ℚ) + X) = C q⁻¹ * (C (-q) + X) := by
    have := rescale_lin q⁻¹ (-1) 1
    simp only [map_one, one_mul] at this
    rw [this, mul_add, ← map_mul]
    congr 2; field_simp
  rw [this, C_mul_inv, inv_inv]

theorem scale_lin_half {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ (C (-1 / 2 : ℚ) + X) = C q⁻¹ * (C (-q / 2) + X) := by
  have := rescale_lin q⁻¹ (-1 / 2) 1
  simp only [map_one, one_mul] at this
  rw [this, mul_add, ← map_mul]
  congr 2; field_simp

theorem scale_lin_two {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ (C (-1 : ℚ) + C 2 * X) = C q⁻¹ * (C (-q) + C 2 * X) := by
  rw [rescale_lin, mul_add, ← map_mul, ← mul_assoc, ← map_mul]
  congr 2
  · field_simp
  · congr 1; ring

theorem rescale_Gsp {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ Gsp = C (q ^ 4) * ((C (-q) + X)⁻¹) ^ 4 := by
  rw [Gsp, map_pow, scale_inv_lin hq, mul_pow, map_pow]

theorem rescale_Ggen {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ Ggen = C (q ^ 4 * q⁻¹ ^ 6) * (((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6) := by
  rw [Ggen, map_mul, rescale_Gsp hq, map_pow (rescale q⁻¹), scale_lin_half hq, mul_pow]
  simp only [map_mul, map_pow]; ring

theorem rescale_Gst {q : ℚ} (hq : q ≠ 0) :
    rescale q⁻¹ Gst = C (q ^ 4 * q⁻¹ ^ 6 * q⁻¹) *
      (((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6 * (C (-q) + C 2 * X)) := by
  rw [Gst, map_mul, rescale_Ggen hq, scale_lin_two hq]
  simp only [map_mul]; ring

/-- Special nodes: `(u - q)^{-4} = q^{-4} G_sp(u/q)`. -/
theorem S_sp {q : ℚ} (hq : q ≠ 0) :
    ((C (-q) + X)⁻¹) ^ 4 = C (q⁻¹ ^ 4) * rescale q⁻¹ Gsp := by
  rw [rescale_Gsp hq, ← mul_assoc, ← map_mul, show q⁻¹ ^ 4 * q ^ 4 = 1 by field_simp, map_one,
    one_mul]

/-- Generic nodes: `(u - q)^{-4} (u - q/2)^6 = q^2 G_gen(u/q)`. -/
theorem S_gen {q : ℚ} (hq : q ≠ 0) :
    ((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6 = C (q ^ 2) * rescale q⁻¹ Ggen := by
  rw [rescale_Ggen hq, ← mul_assoc, ← map_mul, show q ^ 2 * (q ^ 4 * q⁻¹ ^ 6) = 1 by field_simp,
    map_one, one_mul]

/-- The node `g*`: `(u - q)^{-4} (u - q/2)^6 (2u - q) = q^3 G_st(u/q)`. -/
theorem S_st {q : ℚ} (hq : q ≠ 0) :
    ((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6 * (C (-q) + C 2 * X) =
      C (q ^ 3) * rescale q⁻¹ Gst := by
  rw [rescale_Gst hq, ← mul_assoc, ← map_mul,
    show q ^ 3 * (q ^ 4 * q⁻¹ ^ 6 * q⁻¹) = 1 by field_simp, map_one, one_mul]

end Scaling

/-! ### The family-3 local series `H_k` and its factorization at each node type -/

section Family

/-- The Taylor series in `u` of `(t + k)^4 W(t)` at `t = -k + u`, for family 3,
`W(t) = (2t+n)(t+1/2)_n^6 / ∏_{k'=-n}^{2n} (t+k')^4`:
`H_k(u) = (2u + n - 2k) ∏_{j<n} (u + j + 1/2 - k)^6 ∏_{k' ∈ [-n,2n], k' ≠ k} (u + k' - k)^{-4}`. -/
noncomputable def fam3H (n : ℕ) (k : ℤ) : ℚ⟦X⟧ :=
  (C ((n : ℚ) - 2 * k) + C 2 * X) * (∏ j ∈ Finset.range n, (C ((j : ℚ) + 1 / 2 - k) + X) ^ 6) *
    ∏ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, ((C ((k' - k : ℤ) : ℚ) + X)⁻¹) ^ 4

/-- Numerator factor `(u + j + 1/2 - k)^6`. -/
noncomputable def numF (k : ℤ) (j : ℕ) : ℚ⟦X⟧ := (C ((j : ℚ) + 1 / 2 - k) + X) ^ 6

/-- Denominator factor `(u + k' - k)^{-4}`. -/
noncomputable def denF (k k' : ℤ) : ℚ⟦X⟧ := ((C ((k' - k : ℤ) : ℚ) + X)⁻¹) ^ 4

/-- The linear factor `2u + n - 2k`. -/
noncomputable def linF (n : ℕ) (k : ℤ) : ℚ⟦X⟧ := C ((n : ℚ) - 2 * k) + C 2 * X

theorem fam3H_eq (n : ℕ) (k : ℤ) : fam3H n k =
    linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, denF k k' := rfl

variable {p : ℕ} [Fact p.Prime]

theorem padicNorm_int_eq_one {d : ℤ} (h : ¬ (p : ℤ) ∣ d) : padicNorm p (d : ℚ) = 1 :=
  (padicNorm.int_eq_one_iff d).2 h

theorem padicNorm_two_eq_one (hp2 : p ≠ 2) : padicNorm p (2 : ℚ) = 1 := by
  have := (padicNorm.nat_eq_one_iff (p := p) 2).2
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h))
  exact_mod_cast this

theorem numF_unit (hp2 : p ≠ 2) {k : ℤ} {j : ℕ} (h : ¬ (p : ℤ) ∣ (2 * j + 1 - 2 * k)) :
    PUnitS p (numF k j) := by
  have e : (j : ℚ) + 1 / 2 - k = ((2 * j + 1 - 2 * k : ℤ) : ℚ) / 2 := by push_cast; ring
  refine PUnitS.pow (PUnitS.C_add_X ?_) 6
  rw [e, padicNorm.div, padicNorm_int_eq_one h, padicNorm_two_eq_one hp2, div_one]

theorem denF_unit {k k' : ℤ} (h : ¬ (p : ℤ) ∣ (k' - k)) : PUnitS p (denF k k') :=
  PUnitS.pow (PUnitS.inv (PUnitS.C_add_X (padicNorm_int_eq_one h))) 4

theorem linF_unit (hp2 : p ≠ 2) {n : ℕ} {k : ℤ} (h : ¬ (p : ℤ) ∣ (n - 2 * k)) :
    PUnitS p (linF n k) := by
  refine PUnitS.C_add_C_mul_X ?_ (padicNorm_two_eq_one hp2).le
  have e : (n : ℚ) - 2 * k = ((n - 2 * k : ℤ) : ℚ) := by push_cast; ring
  rw [e, padicNorm_int_eq_one h]

/-- An integer of absolute value `< 3P` other than `0, ±P, ±2P` is not divisible by `P`. -/
theorem not_dvd_of_small {P d : ℤ} (hP : 0 < P) (h1 : -(3 * P) < d) (h2 : d < 3 * P) (h0 : d ≠ 0)
    (hp : d ≠ P) (hm : d ≠ -P) (h2p : d ≠ 2 * P) (hm2 : d ≠ -(2 * P)) : ¬ P ∣ d := by
  rintro ⟨m, rfl⟩
  have : -3 < m := by nlinarith
  have : m < 3 := by nlinarith
  interval_cases m <;> omega

theorem padicNorm_natCast_self : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime

omit [Fact p.Prime] in
theorem p_ge_13 {n : ℕ} (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    13 ≤ p := by omega

theorem p_odd (h13 : 13 ≤ p) : p % 2 = 1 :=
  (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)

end Family

/-! ### Lemma W2 -/

section Main

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem padicNorm_ofNat_smooth (hp : 13 ≤ p) {m : ℕ} (a b c d e : ℕ)
    (hm : m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e) : padicNorm p (m : ℚ) = 1 := by
  rw [hm]; exact padicNorm_smooth hp a b c d e

theorem Nsp_unit (hp : 13 ≤ p) {a : ℕ} (ha : a ≤ 3) : padicNorm p (Ncoef a 0 Gsp) = 1 := by
  obtain ⟨v0, v1, v2, v3, -⟩ := Ncoef_values
  interval_cases a
  · rw [v0]; exact_mod_cast padicNorm_ofNat_smooth (m := 491520) hp 15 1 1 0 0 (by norm_num)
  · rw [v1]; exact_mod_cast padicNorm_ofNat_smooth (m := 84480) hp 9 1 1 0 1 (by norm_num)
  · rw [v2]; exact_mod_cast padicNorm_ofNat_smooth (m := 10752) hp 9 1 0 1 0 (by norm_num)
  · rw [v3]; exact_mod_cast padicNorm_ofNat_smooth (m := 768) hp 8 1 0 0 0 (by norm_num)

theorem padicNorm_neg_natCast_self : padicNorm p (-(p : ℚ)) = (p : ℚ)⁻¹ := by
  rw [padicNorm.neg, padicNorm_natCast_self]

/-- **W2, special right nodes** `n + (p+1)/2 ≤ k ≤ 2n`: `|c_a|_p = p^{12-a}`, i.e.
`v_p(c_a) = -(12 - a)` for `a = 0, 1, 2, 3`. -/
theorem w2_special_right (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ k) (hk2 : k ≤ 2 * n) {a : ℕ} (ha : a ≤ 3) :
    padicNorm p (hsConst p (fam3H n k) a) = (p : ℚ) ^ (12 - a) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hP : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  have hY : PUnitS p (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') := by
    refine PUnitS.mul (PUnitS.mul ?_ ?_) ?_
    · apply linF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      apply numF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun k' hk' => ?_)
      simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
      apply denF_unit; apply not_dvd_of_small <;> omega
  rw [hsplit, S_sp hP, norm_hsConst_eq padicNorm_natCast_self hY ha
    (Ncoef_le_one (Or.inl rfl) a) (Nsp_unit h13 ha), padicNorm_pow', padicNorm_inv,
    padicNorm_natCast_self, inv_inv, ← pow_add]
  congr 1; omega

/-- **W2, special left nodes** `-n ≤ k ≤ -(p+1)/2` (pole parameter `q = -p`): `|c_a|_p = p^{12-a}`. -/
theorem w2_special_left (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : -(n : ℤ) ≤ k) (hk2 : k ≤ -(((p : ℤ) + 1) / 2)) {a : ℕ} (ha : a ≤ 3) :
    padicNorm p (hsConst (-(p : ℚ)) (fam3H n k) a) = (p : ℚ) ^ (12 - a) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hP : -(p : ℚ) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
  have hmem : k + p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k + p) = ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') *
      ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  have hY : PUnitS p (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') := by
    refine PUnitS.mul (PUnitS.mul ?_ ?_) ?_
    · apply linF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      apply numF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun k' hk' => ?_)
      simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
      apply denF_unit; apply not_dvd_of_small <;> omega
  rw [hsplit, S_sp hP, norm_hsConst_eq padicNorm_neg_natCast_self hY ha
    (Ncoef_le_one (Or.inl rfl) a) (Nsp_unit h13 ha), padicNorm_pow', padicNorm_inv,
    padicNorm_neg_natCast_self, inv_inv, ← pow_add]
  congr 1; omega

theorem padicNorm_natCast_pow_mul (e b : ℕ) (hb : e ≤ b) :
    padicNorm p ((p : ℚ) ^ e) * (p : ℚ) ^ b = (p : ℚ) ^ (b - e) := by
  have hP : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicNorm_pow', padicNorm_natCast_self, inv_pow]
  rw [← Nat.sub_add_cancel hb, pow_add, Nat.add_sub_cancel]
  field_simp

omit [Fact p.Prime] in
/-- The numerator index `j₀ = k - (p+1)/2`: its factor `u + j₀ + 1/2 - k = u - p/2` is the midpoint zero. -/
theorem numF_mid {k : ℤ} {j0 : ℕ} (hodd : p % 2 = 1) (hj0 : (j0 : ℤ) = k - ((p : ℤ) + 1) / 2) :
    numF k j0 = (C (-(p : ℚ) / 2) + X) ^ 6 := by
  have hh : 2 * (((p : ℤ) + 1) / 2) = p + 1 := by omega
  have hq : ((j0 : ℤ) : ℚ) = (k : ℚ) - (((((p : ℤ) + 1) / 2 : ℤ)) : ℚ) := by rw [hj0]; push_cast; ring
  have hq2 : (2 : ℚ) * ((((p : ℤ) + 1) / 2 : ℤ) : ℚ) = p + 1 := by exact_mod_cast hh
  have : (j0 : ℚ) + 1 / 2 - k = -(p : ℚ) / 2 := by
    have e : (j0 : ℚ) = ((j0 : ℤ) : ℚ) := by norm_cast
    rw [e, hq]; linarith
  rw [numF, this]

/-- **W2, generic right nodes** `(p+1)/2 ≤ k ≤ n + (p-1)/2`, `2k ≠ n + p`:
`|c_0|_p ≤ p^5`, `|c_1|_p = p^5`, `|c_2|_p = p^4`, `|c_3|_p = p^3`. -/
theorem w2_generic (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : ((p : ℤ) + 1) / 2 ≤ k) (hk2 : k ≤ n + ((p : ℤ) - 1) / 2) (hk3 : 2 * k ≠ n + p) :
    padicNorm p (hsConst p (fam3H n k) 0) ≤ (p : ℚ) ^ 5 ∧
    padicNorm p (hsConst p (fam3H n k) 1) = (p : ℚ) ^ 5 ∧
    padicNorm p (hsConst p (fam3H n k) 2) = (p : ℚ) ^ 4 ∧
    padicNorm p (hsConst p (fam3H n k) 3) = (p : ℚ) ^ 3 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hP : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set j0 : ℕ := (k - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      (((C (-(p : ℚ)) + X)⁻¹) ^ 4 * (C (-(p : ℚ) / 2) + X) ^ 6) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid hodd hj0]
    ring
  have hY : PUnitS p (linF n k * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') := by
    refine PUnitS.mul (PUnitS.mul ?_ ?_) ?_
    · apply linF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun j hj => ?_)
      simp only [Finset.mem_erase, Finset.mem_range] at hj
      have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
      apply numF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun k' hk' => ?_)
      simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
      apply denF_unit; apply not_dvd_of_small <;> omega
  obtain ⟨-, -, -, -, w0, w1, w2, w3, -⟩ := Ncoef_values
  have hNle := fun a => Ncoef_le_one (p := p) (G := Ggen) (Or.inr (Or.inl rfl)) a
  rw [hsplit, S_gen hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (norm_hsConst_le padicNorm_natCast_self hY.1 (by norm_num) (hNle 0) 7 ?_).trans_eq
      (padicNorm_natCast_pow_mul 2 7 (by norm_num))
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exact Or.inl w0
    · exact Or.inr (by omega)
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 1)
      (by rw [w1]; exact_mod_cast padicNorm_ofNat_smooth (m := 24) h13 3 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 2 _ (by norm_num)]
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 2)
      (by rw [w2]; exact_mod_cast padicNorm_ofNat_smooth (m := 24) h13 3 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 2 _ (by norm_num)]
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 3)
      (by rw [w3]; exact_mod_cast padicNorm_ofNat_smooth (m := 12) h13 2 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 2 _ (by norm_num)]

/-- **W2, the node `g*`** (`2k = n + p`, where `2t + n` vanishes at the midpoint as well):
`|c_0|_p = p^5`, `|c_1|_p = p^4`, `|c_2|_p ≤ p^2`, `|c_3|_p = p^2`. -/
theorem w2_gstar (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk : 2 * k = n + p) :
    padicNorm p (hsConst p (fam3H n k) 0) = (p : ℚ) ^ 5 ∧
    padicNorm p (hsConst p (fam3H n k) 1) = (p : ℚ) ^ 4 ∧
    padicNorm p (hsConst p (fam3H n k) 2) ≤ (p : ℚ) ^ 2 ∧
    padicNorm p (hsConst p (fam3H n k) 3) = (p : ℚ) ^ 2 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hP : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set j0 : ℕ := (k - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hlin : linF n k = C (-(p : ℚ)) + C 2 * X := by
    have : (n : ℚ) - 2 * k = -(p : ℚ) := by
      have : (2 * k : ℚ) = n + p := by exact_mod_cast hk
      linarith
    rw [linF, this]
  have hsplit : fam3H n k = ((∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      (((C (-(p : ℚ)) + X)⁻¹) ^ 4 * (C (-(p : ℚ) / 2) + X) ^ 6 * (C (-(p : ℚ)) + C 2 * X)) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid hodd hj0, hlin]
    ring
  have hY : PUnitS p ((∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') := by
    refine PUnitS.mul ?_ ?_
    · refine PUnitS.prod _ _ (fun j hj => ?_)
      simp only [Finset.mem_erase, Finset.mem_range] at hj
      have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
      apply numF_unit hp2; apply not_dvd_of_small <;> omega
    · refine PUnitS.prod _ _ (fun k' hk' => ?_)
      simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
      apply denF_unit; apply not_dvd_of_small <;> omega
  obtain ⟨-, -, -, -, -, -, -, -, u0, u1, u2, u3⟩ := Ncoef_values
  have hNle := fun a => Ncoef_le_one (p := p) (G := Gst) (Or.inr (Or.inr rfl)) a
  rw [hsplit, S_st hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 0)
      (by rw [u0]; exact_mod_cast padicNorm_ofNat_smooth (m := 48) h13 4 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 3 _ (by norm_num)]
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 1)
      (by rw [u1]; exact_mod_cast padicNorm_ofNat_smooth (m := 24) h13 3 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 3 _ (by norm_num)]
  · refine (norm_hsConst_le padicNorm_natCast_self hY.1 (by norm_num) (hNle 2) 5 ?_).trans_eq
      (padicNorm_natCast_pow_mul 3 5 (by norm_num))
    intro r hr
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exact Or.inl u2
    · exact Or.inr (by omega)
  · rw [norm_hsConst_eq padicNorm_natCast_self hY (by norm_num) (hNle 3)
      (by rw [u3, padicNorm.neg]
          exact_mod_cast padicNorm_ofNat_smooth (m := 12) h13 2 1 0 0 0 (by norm_num)),
      padicNorm_natCast_pow_mul 3 _ (by norm_num)]

end Main

/-! ### The local pair expansions used in W4 -/

section PairExpansions

variable {p : ℕ} [Fact p.Prime]

theorem Gsp_unit : PUnitS p Gsp :=
  PUnitS.pow (PUnitS.inv (PUnitS.C_add_X (by simp))) 4

theorem Ggen_unit (hp2 : p ≠ 2) : PUnitS p Ggen := by
  refine Gsp_unit.mul (PUnitS.pow (PUnitS.C_add_X ?_) 6)
  rw [neg_div, padicNorm.neg, padicNorm.div, padicNorm.one, padicNorm_two_eq_one hp2, div_one]

theorem coeff_C_mul_rescale_le {q s : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) {G : ℚ⟦X⟧} (hG : PInt p G)
    (m : ℕ) : padicNorm p (coeff m (C s * rescale q⁻¹ G)) ≤ padicNorm p s * (p : ℚ) ^ m := by
  rw [coeff_C_mul, coeff_rescale, padicNorm.mul, padicNorm.mul, padicNorm_pow', padicNorm_inv, hq,
    inv_inv]
  have := hG m
  have h0 : (0 : ℚ) ≤ padicNorm p s * (p : ℚ) ^ m :=
    mul_nonneg (padicNorm.nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  nlinarith [padicNorm.nonneg (p := p) s, padicNorm.nonneg (p := p) (coeff m G)]

/-- **W4, generic pairs**: `[u^m] (u - q)^{-4} (u - q/2)^6 ∈ p^{2-m} ℤ_p` when `v_p(q) = 1`. -/
theorem w4_generic_pair_coeff (hp2 : p ≠ 2) {q : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) (m : ℕ) :
    padicNorm p (coeff m (((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6)) ≤
      (p : ℚ)⁻¹ ^ 2 * (p : ℚ) ^ m := by
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq; exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hq.symm)
  rw [S_gen hq0]
  refine (coeff_C_mul_rescale_le hq (Ggen_unit hp2).1 m).trans_eq ?_
  rw [padicNorm_pow', hq]

/-- **W4, special pairs**: `[u^m] (u - q)^{-4} ∈ p^{-4-m} ℤ_p` when `v_p(q) = 1`. -/
theorem w4_special_pair_coeff {q : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) (m : ℕ) :
    padicNorm p (coeff m (((C (-q) + X)⁻¹) ^ 4)) ≤ (p : ℚ) ^ 4 * (p : ℚ) ^ m := by
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq; exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hq.symm)
  rw [S_sp hq0]
  refine (coeff_C_mul_rescale_le hq Gsp_unit.1 m).trans_eq ?_
  rw [padicNorm_pow', padicNorm_inv, hq, inv_inv]

end PairExpansions

end W2
end Hankel2
