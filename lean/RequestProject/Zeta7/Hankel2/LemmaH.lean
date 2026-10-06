import Mathlib
import RequestProject.Zeta7.Hankel2.LemmaN

/-!
# Lemma H ⟹ non-vanishing (the lattice route to gap (b))

`ZETA7_STATUS.md`, family 3, gap (b).  At a prime `p` split the `ζ₂(7)`-free Hankel matrix as
`G_β = G_HS + G_rest` (harmonic-sum terms with `p ∣ 2l-1`, and the rest), and let `G_α` be the
`ζ₂(7)`-coefficient Hankel matrix, so that `Δ_K(X) = det (G_HS + G_rest + X • G_α)`.

**Lemma H** (open in general; verified exactly in the cases listed in `ZETA7_STATUS.md`) asserts that
`G_HS` is invertible and that `G_HS⁻¹ G_rest` and `G_HS⁻¹ G_α` have all entries in `pℤ_(p)`.

This file proves, for arbitrary square rational matrices, that the conclusion of Lemma H at a prime `p`
forces `det (G_HS + G_rest + r • G_α) ≠ 0` for every rational `r` whose denominator is prime to `p`
(`det_ne_zero_of_lattice`), and the resulting "for all large `n`" statement
(`det_ne_zero_of_eventually_lattice`), in which the prime is only required to exceed `n`.
-/

open Matrix

namespace Hankel2

section LatticeCertificate

variable {p : ℕ} [hp : Fact p.Prime] {m : Type*} [Fintype m] [DecidableEq m]

/-- The `p`-adic integer attached to a rational number of `p`-adic norm `≤ 1`. -/
noncomputable def ratToPadicInt (q : ℚ) (hq : padicNorm p q ≤ 1) : ℤ_[p] :=
  ⟨(q : ℚ_[p]), by rw [Padic.eq_padicNorm]; exact_mod_cast hq⟩

/-- **Unipotent certificate.**  If every entry of the rational matrix `E` has `p`-adic norm `< 1`, then
`det (1 + E) ≠ 0` (indeed `det (1 + E) ≡ 1 (mod p)`). -/
theorem det_one_add_ne_zero_of_padicNorm_lt_one (E : Matrix m m ℚ)
    (hE : ∀ i j, padicNorm p (E i j) < 1) : (1 + E).det ≠ 0 := by
  let E' : Matrix m m ℤ_[p] := fun i j => ratToPadicInt (E i j) (hE i j).le
  have hE' : ∀ i j, ‖E' i j‖ < 1 := by
    intro i j
    change ‖((E i j : ℚ) : ℚ_[p])‖ < 1
    rw [Padic.eq_padicNorm]; exact_mod_cast hE i j
  have hunit : IsUnit ((1 : Matrix m m ℤ_[p]) + (1 : ℤ_[p]) • E').det :=
    isUnit_det_add_smul 1 E' (by simp) hE' 1
  have hcast : ((((1 : Matrix m m ℤ_[p]) + (1 : ℤ_[p]) • E').det : ℤ_[p]) : ℚ_[p]) =
      (((1 + E).det : ℚ) : ℚ_[p]) := by
    have h1 : ((((1 : Matrix m m ℤ_[p]) + (1 : ℤ_[p]) • E').det : ℤ_[p]) : ℚ_[p]) =
        ((PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).mapMatrix
          ((1 : Matrix m m ℤ_[p]) + (1 : ℤ_[p]) • E')).det := by
      rw [← RingHom.map_det]; rfl
    have h2 : (((1 + E).det : ℚ) : ℚ_[p]) =
        ((Rat.castHom ℚ_[p]).mapMatrix (1 + E)).det := by
      rw [← RingHom.map_det]; rfl
    rw [h1, h2]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp [E', ratToPadicInt]
    · simp [E', ratToPadicInt, hij]
  intro h0
  rw [h0, Rat.cast_zero] at hcast
  have : ((1 : Matrix m m ℤ_[p]) + (1 : ℤ_[p]) • E').det = 0 := by
    exact Subtype.ext (by simpa using hcast)
  rw [this] at hunit
  exact not_isUnit_zero hunit

/-- **Lemma H ⟹ non-vanishing at a rational point.**  Let `G, H, A` be square rational matrices with
`det G ≠ 0`, and suppose every entry of `G⁻¹ * H` and of `G⁻¹ * A` has `p`-adic norm `< 1`.  Then
`det (G + H + r • A) ≠ 0` for every rational `r` whose denominator is prime to `p`.
(Apply with `G = G_HS`, `H = G_rest`, `A = G_α`, `r = ζ₂(7)`.) -/
theorem det_ne_zero_of_lattice (G H A : Matrix m m ℚ) (hG : G.det ≠ 0)
    (hH : ∀ i j, padicNorm p ((G⁻¹ * H) i j) < 1) (hA : ∀ i j, padicNorm p ((G⁻¹ * A) i j) < 1)
    {r : ℚ} (hr : ¬ p ∣ r.den) : (G + H + r • A).det ≠ 0 := by
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hfac : G + H + r • A = G * (1 + (G⁻¹ * H + r • (G⁻¹ * A))) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, Matrix.one_mul, add_assoc]
  have hrn : padicNorm p r ≤ 1 := padicNorm_le_one_of_not_dvd_den hr
  have hE : ∀ i j, padicNorm p ((G⁻¹ * H + r • (G⁻¹ * A)) i j) < 1 := by
    intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine lt_of_le_of_lt padicNorm.nonarchimedean (max_lt (hH i j) ?_)
    rw [padicNorm.mul]
    calc padicNorm p r * padicNorm p ((G⁻¹ * A) i j) ≤ 1 * padicNorm p ((G⁻¹ * A) i j) :=
          mul_le_mul_of_nonneg_right hrn (padicNorm.nonneg _)
      _ < 1 := by rw [one_mul]; exact hA i j
  rw [hfac, Matrix.det_mul]
  exact mul_ne_zero hG (det_one_add_ne_zero_of_padicNorm_lt_one _ hE)

end LatticeCertificate

/-- **Lemma H for all large `n` ⟹ non-vanishing for all large `n`.**  Let `G n, H n, A n` be square
rational matrices (of size `K n`).  Suppose that for every `n ≥ N₀` there is a prime `p > n` such that
`det (G n) ≠ 0` and all entries of `(G n)⁻¹ * H n` and `(G n)⁻¹ * A n` have `p`-adic norm `< 1`.  Then for
every rational `r`, `det (G n + H n + r • A n) ≠ 0` for all `n ≥ max N₀ (den r)`. -/
theorem det_ne_zero_of_eventually_lattice (K : ℕ → ℕ) (G H A : ∀ n, Matrix (Fin (K n)) (Fin (K n)) ℚ)
    (N₀ : ℕ)
    (hN : ∀ n, N₀ ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧ (G n).det ≠ 0 ∧
      (∀ i j, padicNorm p (((G n)⁻¹ * H n) i j) < 1) ∧
      (∀ i j, padicNorm p (((G n)⁻¹ * A n) i j) < 1))
    (r : ℚ) : ∀ n, max N₀ r.den ≤ n → (G n + H n + r • A n).det ≠ 0 := by
  intro n hn
  obtain ⟨p, hp, hnp, hG, hH, hA⟩ := hN n (le_trans (le_max_left _ _) hn)
  haveI : Fact p.Prime := ⟨hp⟩
  apply det_ne_zero_of_lattice (G n) (H n) (A n) hG hH hA
  intro hd
  have h1 := Nat.le_of_dvd r.den_pos hd
  have h2 : r.den ≤ n := le_trans (le_max_right _ _) hn
  omega

end Hankel2
