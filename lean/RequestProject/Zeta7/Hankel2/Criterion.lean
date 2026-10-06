import Mathlib

/-!
# The `p`-adic product-formula criterion

This is the arithmetic half of the 2-adic Hankel construction described in
`HANKEL2_ZETA7.md`.  It is the exact analogue, on the `p`-adic side, of the archimedean
criterion `Zeta5.irrational_of_integer_poly_decay`.

**The criterion.**  Let `ζ ∈ ℚ_[p]` and let `Q ∈ ℤ[X]` have degree at most `K`.  If `ζ`
were a rational number `r = a/b`, then `b ^ K · Q(r)` would be a rational integer; it is
nonzero as soon as `Q(ζ) ≠ 0`, so the product formula forces

`‖Q(ζ)‖_p · |b ^ K Q(r)|_∞ ≥ 1`,

and the archimedean factor is at most `L(Q) · max(|a|, b) ^ K`, where `L(Q) = ∑ |Q_i|` is
the length of `Q` (its `ℓ¹` height; `L(Q) ≤ (K+1)·H(Q)` for the naive height `H`).

Hence a family of integer polynomials whose `p`-adic values at `ζ` are *smaller* than
`1 / (L(Q) · B ^ K)` for every bound `B` proves that `ζ` is not a rational number.  In the
notation of `HANKEL2_ZETA7.md`, with `d = v₂ Q(ζ)` and `h = log₂ L(Q)`, the requirement is

`d > h + K·log₂ max(|a|, b)`.

Everything here is proved unconditionally; what remains open for `ζ₂(7)` is the *analytic*
half, namely the asymptotics of `d` and `h` for the Hankel family (see `ZETA7_STATUS.md`).

The main results are

* `Hankel2.one_le_length_mul_norm` — the finite, quantitative form of the criterion;
* `Hankel2.not_rat_of_padic_smallness` — its infinite form: a number admitting such
  polynomials for every bound `B` is not rational.
-/

namespace Hankel2

open Polynomial Finset

variable {p : ℕ}

/-- The **length** (the `ℓ¹` height) of an integer polynomial, `L(Q) = ∑ᵢ |Qᵢ|`. -/
def plength (Q : Polynomial ℤ) : ℤ :=
  ∑ i ∈ range (Q.natDegree + 1), |Q.coeff i|

theorem plength_nonneg (Q : Polynomial ℤ) : 0 ≤ plength Q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The length can be computed over any range containing the degree. -/
theorem plength_eq_sum_range (Q : Polynomial ℤ) {K : ℕ} (hK : Q.natDegree ≤ K) :
    plength Q = ∑ i ∈ range (K + 1), |Q.coeff i| := by
  rw [plength]
  refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
  · simp only [mem_range] at hi ⊢
    omega
  · simp only [mem_range, not_lt] at hi
    rw [Q.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]

/-- `max (|num r|, den r)`, the quantity that measures the size of the rational number
`r` in the criterion. -/
def denNumMax (r : ℚ) : ℤ := max |r.num| (r.den : ℤ)

/-- The numerator obtained by clearing denominators in `Q(r)`:
`clearDenom Q K r = ∑_{i ≤ K} Qᵢ · num(r)ⁱ · den(r)^{K-i}`. -/
def clearDenom (Q : Polynomial ℤ) (K : ℕ) (r : ℚ) : ℤ :=
  ∑ i ∈ range (K + 1), Q.coeff i * r.num ^ i * (r.den : ℤ) ^ (K - i)

/-- `clearDenom` really is `den ^ K · Q(r)`. -/
theorem clearDenom_cast (Q : Polynomial ℤ) {K : ℕ} (hK : Q.natDegree ≤ K) (r : ℚ) :
    ((clearDenom Q K r : ℤ) : ℚ) = (r.den : ℚ) ^ K * aeval r Q := by
  have hden : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.den_nz
  have hQ : aeval r Q = ∑ i ∈ range (K + 1), (Q.coeff i : ℚ) * r ^ i := by
    rw [aeval_def, eval₂_eq_sum_range' (algebraMap ℤ ℚ) (Nat.lt_succ_of_le hK)]
    simp
  rw [hQ, Finset.mul_sum, clearDenom]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ K := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
  have hrd : (r.num : ℚ) = r * (r.den : ℚ) := (Rat.mul_den_eq_num r).symm
  have hsplit : (r.den : ℚ) ^ K = (r.den : ℚ) ^ i * (r.den : ℚ) ^ (K - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, hrd, mul_pow]
  ring

/-- The archimedean bound on the cleared numerator. -/
theorem abs_clearDenom_le (Q : Polynomial ℤ) {K : ℕ} (hK : Q.natDegree ≤ K) (r : ℚ) :
    |clearDenom Q K r| ≤ plength Q * denNumMax r ^ K := by
  set M : ℤ := denNumMax r with hM
  have hM1 : 1 ≤ M := by
    rw [hM, denNumMax]
    exact le_max_of_le_right (by exact_mod_cast r.pos)
  have hM0 : (0 : ℤ) ≤ M := le_trans zero_le_one hM1
  calc |clearDenom Q K r|
      ≤ ∑ i ∈ range (K + 1), |Q.coeff i * r.num ^ i * (r.den : ℤ) ^ (K - i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (K + 1), |Q.coeff i| * M ^ K := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ K := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
        rw [abs_mul, abs_mul, abs_pow, abs_pow]
        have h1 : |r.num| ^ i ≤ M ^ i :=
          pow_le_pow_left₀ (abs_nonneg _) (by rw [hM, denNumMax]; exact le_max_left _ _) i
        have h2 : |(r.den : ℤ)| ^ (K - i) ≤ M ^ (K - i) := by
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
          rw [abs_of_nonneg (by positivity), hM, denNumMax]
          exact le_max_right _ _
        have h3 : |r.num| ^ i * |(r.den : ℤ)| ^ (K - i) ≤ M ^ i * M ^ (K - i) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        have h4 : M ^ i * M ^ (K - i) = M ^ K := by rw [← pow_add]; congr 1; omega
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by rw [← h4]; exact h3) (abs_nonneg _)
    _ = plength Q * M ^ K := by
        rw [← Finset.sum_mul, ← plength_eq_sum_range Q hK]

/-- Casting a `ℚ`-value of an integer polynomial into `ℚ_[p]`. -/
theorem aeval_cast (Q : Polynomial ℤ) (r : ℚ) [Fact p.Prime] :
    aeval ((r : ℚ_[p])) Q = ((aeval r Q : ℚ) : ℚ_[p]) := by
  have h : ((r : ℚ) : ℚ_[p]) = algebraMap ℚ ℚ_[p] r := rfl
  rw [h, aeval_algebraMap_apply]
  rfl

/-- For a nonzero rational integer `N`, `|N|_∞ · ‖N‖_p ≥ 1`: the product formula in the
only form we need. -/
theorem one_le_abs_mul_padic_norm (p : ℕ) [hp : Fact p.Prime] (N : ℤ) (hN : N ≠ 0) :
    (1 : ℝ) ≤ |(N : ℝ)| * ‖(N : ℚ_[p])‖ := by
  have hcast : ((N : ℚ) : ℚ_[p]) = (N : ℚ_[p]) := by push_cast; ring
  have h1 : ‖(N : ℚ_[p])‖ = (padicNorm p (N : ℚ) : ℝ) := by
    rw [← hcast]; exact Padic.eq_padicNorm _
  have hQ0 : ((N : ℚ)) ≠ 0 := by exact_mod_cast hN
  have hv : padicValRat p (N : ℚ) = (padicValInt p N : ℤ) := by
    simp [padicValRat, padicValInt]
  have hdvd : (p : ℤ) ^ (padicValInt p N) ∣ N := by
    have h0 := pow_padicValNat_dvd (p := p) (n := N.natAbs)
    have h2 : ((p : ℤ) ^ padicValNat p N.natAbs) ∣ (N.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr h0
    simpa [padicValInt, Int.natAbs_dvd] using h2
  have hle : ((p : ℝ)) ^ (padicValInt p N) ≤ |(N : ℝ)| := by
    have h2 : ((p : ℤ) ^ (padicValInt p N)) ≤ |N| :=
      Int.le_of_dvd (abs_pos.mpr hN) ((dvd_abs _ _).mpr hdvd)
    have h3 : (((p : ℤ) ^ (padicValInt p N) : ℤ) : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3 ⊢
    exact h3
  have hpos : (0 : ℝ) < (p : ℝ) ^ (padicValInt p N) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  rw [h1, padicNorm, if_neg hQ0, hv]
  push_cast
  rw [zpow_neg, zpow_natCast, le_mul_inv_iff₀ hpos, one_mul]
  exact hle

/-- **The criterion, quantitative form.**  If `Q` is an integer polynomial of degree at
most `K` whose value at the rational number `r` is nonzero, then the `p`-adic size of
`Q(r)` is bounded below by `1 / (L(Q) · max(|num r|, den r) ^ K)`. -/
theorem one_le_length_mul_norm (p : ℕ) [Fact p.Prime] (Q : Polynomial ℤ) {K : ℕ}
    (hK : Q.natDegree ≤ K) (r : ℚ) (hne : aeval ((r : ℚ_[p])) Q ≠ 0) :
    (1 : ℝ) ≤ ((plength Q : ℝ) * (denNumMax r : ℝ) ^ K) *
      ‖aeval ((r : ℚ_[p])) Q‖ := by
  have hQr : aeval r Q ≠ 0 := by
    intro h
    apply hne
    rw [aeval_cast Q r, h]
    simp
  set N : ℤ := clearDenom Q K r with hN
  have hNcast : ((N : ℤ) : ℚ) = (r.den : ℚ) ^ K * aeval r Q := clearDenom_cast Q hK r
  have hN0 : N ≠ 0 := by
    intro h
    rw [h] at hNcast
    have hden : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.den_nz
    simp only [Int.cast_zero] at hNcast
    rcases mul_eq_zero.mp hNcast.symm with h' | h'
    · exact (pow_ne_zero K hden) h'
    · exact hQr h'
  have hprod := one_le_abs_mul_padic_norm p N hN0
  have hNp : ((N : ℚ_[p])) = ((r.den : ℚ_[p])) ^ K * aeval ((r : ℚ_[p])) Q := by
    have h := congrArg (fun x : ℚ => ((x : ℚ_[p]))) hNcast
    simp only [Rat.cast_mul, Rat.cast_pow] at h
    rw [show ((N : ℤ) : ℚ_[p]) = (((N : ℤ) : ℚ) : ℚ_[p]) by push_cast; ring, h, aeval_cast Q r]
    norm_cast
  have hdenle : ‖((r.den : ℚ_[p])) ^ K‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    simpa using (Padic.norm_int_le_one (p := p) (r.den : ℤ))
  have hnorm : ‖(N : ℚ_[p])‖ ≤ ‖aeval ((r : ℚ_[p])) Q‖ := by
    rw [hNp, norm_mul]
    nlinarith [norm_nonneg (aeval ((r : ℚ_[p])) Q), norm_nonneg (((r.den : ℚ_[p])) ^ K)]
  have habs : |(N : ℝ)| ≤ (plength Q : ℝ) * (denNumMax r : ℝ) ^ K := by
    have h := abs_clearDenom_le Q hK r
    have h2 : ((|N| : ℤ) : ℝ) ≤ ((plength Q * denNumMax r ^ K : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h2
    exact h2
  have h1 : (1 : ℝ) ≤ |(N : ℝ)| * ‖aeval ((r : ℚ_[p])) Q‖ :=
    le_trans hprod (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _))
  exact le_trans h1 (mul_le_mul_of_nonneg_right habs (norm_nonneg _))

/-- **The criterion.**  A `p`-adic number admitting, for every bound `B`, an integer
polynomial `Q` of degree at most `K` with `Q(ζ) ≠ 0` and
`L(Q) · B^K · ‖Q(ζ)‖_p < 1`, is not rational. -/
theorem not_rat_of_padic_smallness (p : ℕ) [Fact p.Prime] (ζ : ℚ_[p])
    (H : ∀ B : ℝ, ∃ (K : ℕ) (Q : Polynomial ℤ), Q.natDegree ≤ K ∧ aeval ζ Q ≠ 0 ∧
      (plength Q : ℝ) * B ^ K * ‖aeval ζ Q‖ < 1) :
    ∀ r : ℚ, ζ ≠ (r : ℚ_[p]) := by
  intro r hr
  obtain ⟨K, Q, hK, hne, hsmall⟩ := H ((denNumMax r : ℤ) : ℝ)
  subst hr
  have h := one_le_length_mul_norm p Q hK r hne
  rw [mul_assoc] at hsmall
  rw [mul_assoc] at h
  linarith

end Hankel2
