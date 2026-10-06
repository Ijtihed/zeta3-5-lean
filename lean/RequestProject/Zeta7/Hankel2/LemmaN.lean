import Mathlib
import RequestProject.Zeta7.Hankel2.Dominance

/-!
# Lemma N: from `ℓ`-adic dominance to non-vanishing for all (or infinitely many) `n`

`ZETA7_STATUS.md`, family 3, non-vanishing.  Write `F_n(X)` for the Hankel determinant (or one of its
parity factors) of index `n`, a polynomial in `X` (standing for `ζ₂(7)`).

* **Lemma N** (open) asks for a prime `ℓ > n` at which the constant coefficient of `F_n` is strictly
  `ℓ`-adically dominant.  `eval_ne_zero_of_eventually_dominant` and
  `frequently_eval_ne_zero_of_frequently_dominant` prove that Lemma N (for all large `n`, resp. for
  infinitely many `n`) implies `F_n(r) ≠ 0` for every rational `r` (for all large `n`, resp. for
  infinitely many `n`).  No Bertrand postulate is needed once the prime is required to exceed `n`.

* **A certificate for Lemma N.**  If, after rescaling rows and columns, the `X`-free matrix becomes an
  `ℓ`-adic unimodular matrix `G` while the `X`-part becomes a matrix `E` with entries in `ℓℤ_ℓ`, then the
  constant coefficient of `det (G + X E)` is the unit `det G` and every other coefficient lies in
  `ℓℤ_ℓ` (`det_pencil_coeff_zero`, `norm_det_pencil_coeff_lt_one`); in particular
  `det (G + x E)` is a unit for every `x ∈ ℤ_ℓ` (`isUnit_det_add_smul`).
-/

open Polynomial

namespace Hankel2

/-- **Lemma N ⟹ non-vanishing for all large `n`.**  If for every `n ≥ N₀` some prime `p > n` makes the
constant coefficient of `F n` strictly `p`-adically dominant, then for every rational `r`,
`(F n)(r) ≠ 0` as soon as `n ≥ max N₀ (den r)`. -/
theorem eval_ne_zero_of_eventually_dominant (F : ℕ → ℚ[X]) (N₀ : ℕ)
    (hN : ∀ n, N₀ ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧
      ∀ i, 1 ≤ i → padicNorm p ((F n).coeff i) < padicNorm p ((F n).coeff 0))
    (r : ℚ) : ∀ n, max N₀ r.den ≤ n → (F n).eval r ≠ 0 := by
  intro n hn
  obtain ⟨p, hp, hnp, hdom⟩ := hN n (le_trans (le_max_left _ _) hn)
  haveI : Fact p.Prime := ⟨hp⟩
  apply eval_ne_zero_of_padic_dominant_of_not_dvd_den (F n) hdom
  intro hd
  have h1 := Nat.le_of_dvd r.den_pos hd
  have h2 : r.den ≤ n := le_trans (le_max_right _ _) hn
  omega

/-- **Lemma N for infinitely many `n` ⟹ non-vanishing for infinitely many `n`.**  If for arbitrarily
large `n` some prime `p > n` makes the constant coefficient of `F n` strictly `p`-adically dominant, then
for every rational `r` there are arbitrarily large `n` with `(F n)(r) ≠ 0`. -/
theorem frequently_eval_ne_zero_of_frequently_dominant (F : ℕ → ℚ[X])
    (hN : ∀ N, ∃ n, N ≤ n ∧ ∃ p : ℕ, p.Prime ∧ n < p ∧
      ∀ i, 1 ≤ i → padicNorm p ((F n).coeff i) < padicNorm p ((F n).coeff 0))
    (r : ℚ) : ∀ N, ∃ n, N ≤ n ∧ (F n).eval r ≠ 0 := by
  intro N
  obtain ⟨n, hn, p, hp, hnp, hdom⟩ := hN (max N r.den)
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  apply eval_ne_zero_of_padic_dominant_of_not_dvd_den (F n) hdom
  intro hd
  have h1 := Nat.le_of_dvd r.den_pos hd
  have h2 : r.den ≤ n := le_trans (le_max_right _ _) hn
  omega

section Certificate

variable {p : ℕ} [hp : Fact p.Prime] {m : Type*} [Fintype m] [DecidableEq m]

theorem toZMod_eq_zero_of_norm_lt_one {z : ℤ_[p]} (hz : ‖z‖ < 1) : PadicInt.toZMod z = 0 := by
  have : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton.mpr ((PadicInt.norm_lt_one_iff_dvd z).mp hz)
  rw [← PadicInt.ker_toZMod] at this
  exact this

theorem norm_lt_one_of_toZMod_eq_zero {z : ℤ_[p]} (hz : PadicInt.toZMod z = 0) : ‖z‖ < 1 := by
  have : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact hz
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact (PadicInt.norm_lt_one_iff_dvd z).mpr this

theorem mapMatrix_toZMod_eq_zero {E : Matrix m m ℤ_[p]} (hE : ∀ i j, ‖E i j‖ < 1) :
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix E = 0 := by
  ext i j
  simp [toZMod_eq_zero_of_norm_lt_one (hE i j)]

/-- **Pointwise certificate.**  If `det G` is a `p`-adic unit and all entries of `E` lie in `pℤ_p`,
then `det (G + x E)` is a unit for every `x ∈ ℤ_p`. -/
theorem isUnit_det_add_smul (G E : Matrix m m ℤ_[p]) (hG : IsUnit G.det)
    (hE : ∀ i j, ‖E i j‖ < 1) (x : ℤ_[p]) : IsUnit (G + x • E).det := by
  have hmap : PadicInt.toZMod (G + x • E).det = PadicInt.toZMod G.det := by
    rw [RingHom.map_det, RingHom.map_det, map_add]
    have : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix (x • E) = 0 := by
      ext i j
      simp [toZMod_eq_zero_of_norm_lt_one (hE i j)]
    rw [this, add_zero]
  have hGn : ‖G.det‖ = 1 := PadicInt.isUnit_iff.mp hG
  by_contra hcon
  have hlt : ‖(G + x • E).det‖ < 1 := by
    have h := PadicInt.norm_le_one (G + x • E).det
    rcases lt_or_eq_of_le h with h | h
    · exact h
    · exact absurd (PadicInt.isUnit_iff.mpr h) hcon
  have h0 := toZMod_eq_zero_of_norm_lt_one hlt
  rw [hmap] at h0
  have := norm_lt_one_of_toZMod_eq_zero h0
  rw [hGn] at this
  exact lt_irrefl _ this

/-- The pencil `det (G + X E)` as a polynomial over `ℤ_p`. -/
noncomputable def detPencil (G E : Matrix m m ℤ_[p]) : ℤ_[p][X] :=
  ((Polynomial.C : ℤ_[p] →+* ℤ_[p][X]).mapMatrix G +
    (X : ℤ_[p][X]) • (Polynomial.C : ℤ_[p] →+* ℤ_[p][X]).mapMatrix E).det

/-- The constant coefficient of the pencil is `det G`. -/
theorem detPencil_coeff_zero (G E : Matrix m m ℤ_[p]) : (detPencil G E).coeff 0 = G.det := by
  rw [detPencil, coeff_zero_eq_eval_zero, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp

/-- **Certificate for Lemma N.**  If every entry of `E` lies in `pℤ_p`, then every non-constant
coefficient of `det (G + X E)` lies in `pℤ_p`.  Together with `detPencil_coeff_zero` and a unit
`det G`, this is exactly strict `p`-adic dominance of the constant coefficient. -/
theorem norm_detPencil_coeff_lt_one (G E : Matrix m m ℤ_[p]) (hE : ∀ i j, ‖E i j‖ < 1)
    (i : ℕ) (hi : 1 ≤ i) : ‖(detPencil G E).coeff i‖ < 1 := by
  apply norm_lt_one_of_toZMod_eq_zero
  have hmap : Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (detPencil G E) =
      Polynomial.C ((PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix G).det := by
    rw [detPencil, ← coe_mapRingHom, RingHom.map_det, RingHom.map_det]
    congr 1
    ext a b
    simp [toZMod_eq_zero_of_norm_lt_one (hE a b)]
  have := congrArg (fun q => q.coeff i) hmap
  simp only [coeff_map] at this
  rw [this, coeff_C]
  simp [show i ≠ 0 by omega]

end Certificate

end Hankel2
