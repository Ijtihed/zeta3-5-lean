import Mathlib
import RequestProject.Zeta7.Hankel2.LemmaH

/-!
# The weight certificate ⟹ non-vanishing (gap (b), family 3, `K = 10n + 3 - 4p`)

`ZETA7_STATUS.md`, round (e).  In the dual Hermite basis the three Hankel matrices `G_HS`, `G_rest`,
`G_α` satisfy, for weights `ℓ` (integers at special nodes, `5/2` at generic nodes and at `g*`),
`v_p(G[x,y]) + ℓ_x + ℓ_y ≥ 0` (resp. `≥ 1` for `G_rest`, `G_α`), and the weighted `G_HS` has unit
determinant.  Writing `2ℓ_x = a_x + b_x` with integers `a_x, b_x` (for `ℓ_x = 5/2` take `a_x = 2`,
`b_x = 3`), the row/column rescaled matrices `p^{a_i + b_j} G i j` are then `p`-integral.

This file proves, for arbitrary square rational matrices and arbitrary integer exponents, that such a
certificate forces `det (G + H + r • A) ≠ 0` for every rational `r` with `p ∤ den r`
(`det_ne_zero_of_weight_certificate`), and the "for all large `n`, some prime `p > n`" version.
-/

open Matrix

namespace Hankel2

section WeightCertificate

variable {p : ℕ} [hp : Fact p.Prime] {m : Type*} [Fintype m] [DecidableEq m]

/-- Row/column rescaling `M ↦ (p^{a i + b j} M i j)`. -/
def weightScale (p : ℕ) (a b : m → ℤ) (M : Matrix m m ℚ) : Matrix m m ℚ :=
  fun i j => (p : ℚ) ^ (a i + b j) * M i j

theorem weightScale_eq (a b : m → ℤ) (M : Matrix m m ℚ) :
    weightScale p a b M =
      diagonal (fun i => (p : ℚ) ^ a i) * M * diagonal (fun j => (p : ℚ) ^ b j) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  ext i j
  simp [weightScale, diagonal_mul, mul_diagonal, zpow_add₀ hp0]
  ring

theorem det_weightScale (a b : m → ℤ) (M : Matrix m m ℚ) :
    (weightScale p a b M).det =
      (∏ i, (p : ℚ) ^ a i) * M.det * ∏ j, (p : ℚ) ^ b j := by
  rw [weightScale_eq, det_mul, det_mul, det_diagonal, det_diagonal]

omit hp [Fintype m] [DecidableEq m] in
theorem weightScale_add_smul (a b : m → ℤ) (G H A : Matrix m m ℚ) (r : ℚ) :
    weightScale p a b (G + H + r • A) =
      weightScale p a b G + (weightScale p a b H + r • weightScale p a b A) := by
  ext i j
  simp [weightScale]
  ring

/-- **Weight certificate ⟹ non-vanishing.**  Let `G, H, A` be square rational matrices and `a, b`
integer exponents.  Suppose the rescaled matrix `Ĝ = (p^{a i + b j} G i j)` is `p`-integral with
`p`-adic unit determinant, and that the rescaled `H` and `A` have all entries of `p`-adic norm `< 1`.
Then `det (G + H + r • A) ≠ 0` for every rational `r` whose denominator is prime to `p`.
(Apply with `G = G_HS`, `H = G_rest`, `A = G_α` in the dual Hermite basis, `r = ζ₂(7)`.) -/
theorem det_ne_zero_of_weight_certificate (G H A : Matrix m m ℚ) (a b : m → ℤ)
    (hG : ∀ i j, padicNorm p (weightScale p a b G i j) ≤ 1)
    (hdet : padicNorm p (weightScale p a b G).det = 1)
    (hH : ∀ i j, padicNorm p (weightScale p a b H i j) < 1)
    (hA : ∀ i j, padicNorm p (weightScale p a b A i j) < 1)
    {r : ℚ} (hr : ¬ p ∣ r.den) : (G + H + r • A).det ≠ 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set Gs := weightScale p a b G
  set Es := weightScale p a b H + r • weightScale p a b A
  have hrn : padicNorm p r ≤ 1 := padicNorm_le_one_of_not_dvd_den hr
  have hE : ∀ i j, padicNorm p (Es i j) < 1 := by
    intro i j
    simp only [Es, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine lt_of_le_of_lt padicNorm.nonarchimedean (max_lt (hH i j) ?_)
    rw [padicNorm.mul]
    calc padicNorm p r * padicNorm p (weightScale p a b A i j)
        ≤ 1 * padicNorm p (weightScale p a b A i j) :=
          mul_le_mul_of_nonneg_right hrn (padicNorm.nonneg _)
      _ < 1 := by rw [one_mul]; exact hA i j
  let G' : Matrix m m ℤ_[p] := fun i j => ratToPadicInt (Gs i j) (hG i j)
  let E' : Matrix m m ℤ_[p] := fun i j => ratToPadicInt (Es i j) (hE i j).le
  have hcastM : ∀ (M : Matrix m m ℚ) (M' : Matrix m m ℤ_[p]),
      (∀ i j, ((M' i j : ℤ_[p]) : ℚ_[p]) = ((M i j : ℚ) : ℚ_[p])) →
      ((M'.det : ℤ_[p]) : ℚ_[p]) = ((M.det : ℚ) : ℚ_[p]) := by
    intro M M' hMM
    have h1 : ((M'.det : ℤ_[p]) : ℚ_[p]) =
        ((PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).mapMatrix M').det := by
      rw [← RingHom.map_det]; rfl
    have h2 : ((M.det : ℚ) : ℚ_[p]) = ((Rat.castHom ℚ_[p]).mapMatrix M).det := by
      rw [← RingHom.map_det]; rfl
    rw [h1, h2]
    congr 1
    ext i j
    exact hMM i j
  have hE' : ∀ i j, ‖E' i j‖ < 1 := by
    intro i j
    change ‖((Es i j : ℚ) : ℚ_[p])‖ < 1
    rw [Padic.eq_padicNorm]; exact_mod_cast hE i j
  have hGu : IsUnit G'.det := by
    rw [PadicInt.isUnit_iff]
    change ‖((G'.det : ℤ_[p]) : ℚ_[p])‖ = 1
    rw [hcastM Gs G' (fun i j => rfl), Padic.eq_padicNorm]
    exact_mod_cast hdet
  have hunit := isUnit_det_add_smul G' E' hGu hE' 1
  rw [one_smul] at hunit
  have hdet' : (((G' + E').det : ℤ_[p]) : ℚ_[p]) = (((Gs + Es).det : ℚ) : ℚ_[p]) :=
    hcastM (Gs + Es) (G' + E') (fun i j => by
      rw [Matrix.add_apply, Matrix.add_apply, PadicInt.coe_add, Rat.cast_add]
      rfl)
  have hne : (Gs + Es).det ≠ 0 := by
    intro h0
    rw [h0, Rat.cast_zero] at hdet'
    have : (G' + E').det = 0 := Subtype.ext (by simpa using hdet')
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hscale : weightScale p a b (G + H + r • A) = Gs + Es := weightScale_add_smul a b G H A r
  intro h0
  apply hne
  rw [← hscale, det_weightScale, h0, mul_zero, zero_mul]

end WeightCertificate

/-- **Weight certificate for all large `n` ⟹ non-vanishing for all large `n`.**  If for every
`n ≥ N₀` there are a prime `p > n` and integer exponents for which the hypotheses of
`det_ne_zero_of_weight_certificate` hold for `G n, H n, A n`, then for every rational `r`,
`det (G n + H n + r • A n) ≠ 0` for all `n ≥ max N₀ (den r)`. -/
theorem det_ne_zero_of_eventually_weight_certificate (K : ℕ → ℕ)
    (G H A : ∀ n, Matrix (Fin (K n)) (Fin (K n)) ℚ) (N₀ : ℕ)
    (hN : ∀ n, N₀ ≤ n → ∃ p : ℕ, ∃ _ : Fact p.Prime, n < p ∧ ∃ a b : Fin (K n) → ℤ,
      (∀ i j, padicNorm p (weightScale p a b (G n) i j) ≤ 1) ∧
      padicNorm p (weightScale p a b (G n)).det = 1 ∧
      (∀ i j, padicNorm p (weightScale p a b (H n) i j) < 1) ∧
      (∀ i j, padicNorm p (weightScale p a b (A n) i j) < 1))
    (r : ℚ) : ∀ n, max N₀ r.den ≤ n → (G n + H n + r • A n).det ≠ 0 := by
  intro n hn
  obtain ⟨p, hp, hnp, a, b, hG, hdet, hH, hA⟩ := hN n (le_trans (le_max_left _ _) hn)
  apply det_ne_zero_of_weight_certificate (G n) (H n) (A n) a b hG hdet hH hA
  intro hd
  have h1 := Nat.le_of_dvd r.den_pos hd
  have h2 : r.den ≤ n := le_trans (le_max_right _ _) hn
  omega

end Hankel2
