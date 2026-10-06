import Mathlib

/-!
# W1: the dual Hermite basis is `p`-integral

`ZETA7_STATUS.md`, round (g).  The weight certificate for gap (b) uses the dual basis of the
Hermite (confluent Vandermonde) interpolation problem: jets `0, …, m_i - 1` (Hasse derivatives) at
pairwise distinct nodes `x_i`, total number of conditions `N = Σ m_i`, on polynomials of degree `< N`.
Lemma W1 says that when the nodes are `p`-integral and pairwise distinct mod `p`, this confluent
Vandermonde matrix is invertible over `ℤ_p`, i.e. the dual Hermite basis `E` has `p`-integral
coefficients.

We prove this for an arbitrary finite configuration, with no restriction on the multiplicities
(Hasse derivatives are used, so no factorials appear):

* `X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero`: vanishing jets `0, …, m-1` at `a` give `(X - a)^m ∣ f`.
* `eq_zero_of_hermite_conditions`: over a field, the Hermite conditions determine a polynomial of
  degree `< Σ m_i` uniquely (unisolvence).
* `det_confluentVandermonde_ne_zero`: the confluent Vandermonde determinant is nonzero over a field.
* `isUnit_det_confluentVandermonde_of_residue_injective`: over a local ring, if the nodes are
  pairwise distinct in the residue field, the determinant is a unit.
* `isUnit_confluentVandermonde_padicInt` (**W1**): over `ℤ_[p]`, nodes pairwise distinct mod `p`
  make the confluent Vandermonde matrix a unit, so its inverse (the dual Hermite basis) has entries
  in `ℤ_[p]`.
-/

open Polynomial Matrix

namespace Hankel2

section Divisibility

variable {R : Type*} [CommRing R]

/-- If the Hasse derivatives of orders `0, …, m-1` of `f` vanish at `a`, then `(X - a)^m ∣ f`. -/
theorem X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero (f : R[X]) (a : R) (m : ℕ)
    (h : ∀ j < m, (hasseDeriv j f).eval a = 0) : (X - C a) ^ m ∣ f := by
  have h1 : X ^ m ∣ taylor a f := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [taylor_coeff]
    exact h d hd
  obtain ⟨g, hg⟩ := h1
  refine ⟨taylor (-a) g, ?_⟩
  have := congrArg (taylor (-a)) hg
  rw [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_X_pow] at this
  rw [this, sub_eq_add_neg, C_neg]

end Divisibility

section Field

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- **Hermite unisolvence.**  Over a field, a polynomial of degree `< Σ m_i` whose Hasse derivatives
of orders `< m_i` vanish at pairwise distinct nodes `x_i` is zero. -/
theorem eq_zero_of_hermite_conditions (x : ι → F) (hx : Function.Injective x) (m : ι → ℕ)
    (f : F[X]) (hdeg : f.degree < ((∑ i, m i : ℕ) : WithBot ℕ))
    (h : ∀ i, ∀ j < m i, (hasseDeriv j f).eval (x i) = 0) : f = 0 := by
  by_contra hf
  have hdvd : ∏ i, (X - C (x i)) ^ m i ∣ f := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact ((Polynomial.pairwise_coprime_X_sub_C hx) hij).pow
    · intro i _
      exact X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero f (x i) (m i) (h i)
  have hle := Polynomial.natDegree_le_of_dvd hdvd hf
  have hprod : (∏ i, (X - C (x i)) ^ m i).natDegree = ∑ i, m i := by
    rw [Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
    simp
  rw [hprod] at hle
  rw [Polynomial.degree_eq_natDegree hf] at hdeg
  exact absurd (WithBot.coe_lt_coe.mp hdeg) (not_lt.mpr hle)

end Field

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)

/-- Row index set of the Hermite problem: pairs `(i, j)` with `j < m i` (jet `j` at node `i`). -/
abbrev HermIdx := Σ i : ι, Fin (m i)

/-- The confluent Vandermonde matrix (with Hasse-derivative normalisation) of the Hermite problem.
Row `(i, j)` is the functional `P ↦ (hasseDeriv j P)(x_i)`; column `c` is the monomial `X^(e c)`,
where `e` enumerates the exponents `0, …, N-1`, `N = Σ m_i`. -/
def confluentVandermonde {R : Type*} [CommRing R] (x : ι → R)
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) : Matrix (HermIdx m) (HermIdx m) R :=
  fun r c => ((e c : ℕ).choose r.2 : R) * x r.1 ^ ((e c : ℕ) - r.2)

omit [DecidableEq ι] in
theorem map_confluentVandermonde {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : ι → R)
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) :
    (confluentVandermonde m x e).map φ = confluentVandermonde m (φ ∘ x) e := by
  ext r c
  simp [confluentVandermonde]

omit [DecidableEq ι] in
/-- The rows of the confluent Vandermonde matrix evaluate the Hermite functionals. -/
theorem confluentVandermonde_mulVec {R : Type*} [CommRing R] (x : ι → R)
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) (v : HermIdx m → R) (r : HermIdx m) :
    (confluentVandermonde m x e *ᵥ v) r =
      (hasseDeriv r.2 (∑ c, monomial (e c : ℕ) (v c))).eval (x r.1) := by
  simp only [mulVec, dotProduct, confluentVandermonde, map_sum, hasseDeriv_monomial, eval_finset_sum,
    eval_monomial]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- Over a field, the confluent Vandermonde determinant at pairwise distinct nodes is nonzero. -/
theorem det_confluentVandermonde_ne_zero {F : Type*} [Field F] (x : ι → F)
    (hx : Function.Injective x) (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) :
    (confluentVandermonde m x e).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set f : F[X] := ∑ c, monomial (e c : ℕ) (v c) with hf
  have hcoeff : ∀ c₀, f.coeff (e c₀ : ℕ) = v c₀ := by
    intro c₀
    rw [hf, finset_sum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_single c₀]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro h
      exact hc (e.injective (Fin.ext h))
    · simp
  have hdeg : f.degree < ((∑ i, m i : ℕ) : WithBot ℕ) := by
    have hcard : Fintype.card (HermIdx m) = ∑ i, m i := by simp [Fintype.card_sigma]
    rw [← hcard, ← Polynomial.mem_degreeLT, hf]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [Polynomial.mem_degreeLT]
    refine (degree_monomial_le _ _).trans_lt ?_
    exact_mod_cast (e c).2
  have hzero : f = 0 := by
    refine eq_zero_of_hermite_conditions x hx m f hdeg fun i j hj => ?_
    have := congrFun hv ⟨i, ⟨j, hj⟩⟩
    rw [confluentVandermonde_mulVec, ← hf] at this
    exact this
  apply hv0
  funext c
  rw [← hcoeff c, hzero, coeff_zero]
  rfl

/-- Over a local ring, if the nodes are pairwise distinct in the residue field, the confluent
Vandermonde determinant is a unit. -/
theorem isUnit_det_confluentVandermonde_of_residue_injective {R : Type*} [CommRing R]
    [IsLocalRing R] (x : ι → R) (hx : Function.Injective (IsLocalRing.residue R ∘ x))
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) :
    IsUnit (confluentVandermonde m x e).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    map_confluentVandermonde]
  exact det_confluentVandermonde_ne_zero m _ hx e

variable {p : ℕ} [Fact p.Prime]

/-- **Lemma W1.**  Nodes in `ℤ_[p]` that are pairwise distinct mod `p`: the confluent Vandermonde
matrix of the Hermite problem is invertible over `ℤ_[p]`, so the dual Hermite basis (its inverse)
has `p`-integral coefficients. -/
theorem isUnit_confluentVandermonde_padicInt (x : ι → ℤ_[p])
    (hx : Function.Injective (PadicInt.toZMod ∘ x))
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) :
    IsUnit (confluentVandermonde m x e) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_det_confluentVandermonde_of_residue_injective m x ?_ e
  intro i j hij
  apply hx
  have h : x i - x j ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hij
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero] at h
  exact h

/-- **Lemma W1, integer nodes.**  For integer nodes pairwise distinct mod `p`, `p` does not divide the
confluent Vandermonde determinant. -/
theorem not_dvd_det_confluentVandermonde_int (x : ι → ℤ)
    (hx : Function.Injective (fun i => (x i : ZMod p)))
    (e : HermIdx m ≃ Fin (Fintype.card (HermIdx m))) :
    ¬ (p : ℤ) ∣ (confluentVandermonde m x e).det := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : ((confluentVandermonde m x e).det : ZMod p) =
      (confluentVandermonde m (fun i => (x i : ZMod p)) e).det := by
    have h2 := RingHom.map_det (Int.castRingHom (ZMod p)) (confluentVandermonde m x e)
    rw [RingHom.mapMatrix_apply, map_confluentVandermonde] at h2
    exact h2
  rw [this]
  exact det_confluentVandermonde_ne_zero m _ hx e

end Matrix

end Hankel2
