import RequestProject.Zeta35.NVEntries
import RequestProject.Zeta7.Hankel2.NVFamily3

/-!
# Non-vanishing: N, Theorem 6.2

For even `n` and an admissible prime `ℓ` (`R < ℓ`, `ℓ ≥ 7`, `3(ℓ − R) ≤ ℓ`), and every rational `r`
with `ℓ ∤ den r`, `Δ_K(r) ≠ 0` for `K = 4(3n + 1 − ℓ)` (`nonvanishing_holds`).

Proof (N, §6; W, Lemma 6.2): in the Hermite basis `E` the Gram matrix of `L_r = b + r a` splits as
`G^ℓ + G^{rest} + r G^α`.  With the weights `ϖ = 5 − j₀` the scaled matrix
`[ℓ^{ϖ_x+ϖ_y} L_r(E_x E_y)]` is congruent mod `ℓ` to the block diagonal matrix
`blockdiag(2 y₀(h) G_{j(h)})` (`NVEntries`), whose determinant `∏_h (2 y₀(h))^4 det G_{j(h)}` is an
`ℓ`-adic unit (`Blocks.det_G0/1/2`).  The weight certificate (`Hankel2.det_ne_zero_of_weight_certificate`)
gives `det [L_r(E_x E_y)] ≠ 0`, and the change of basis back to the monomials gives `Δ_K(r) ≠ 0`.
-/

open Polynomial Finset

namespace Zeta35.NV

variable {n ℓ : ℕ}

theorem padicNorm_det_G [Fact ℓ.Prime] (h7 : 7 ≤ ℓ) {j : ℕ} (hj : j ≤ 2) :
    padicNorm ℓ (Blocks.G j).det = 1 := by
  have hne : (Blocks.G j).det ≠ 0 := by
    interval_cases j <;> simp [Blocks.det_G0, Blocks.det_G1, Blocks.det_G2]
  rw [padicNorm.eq_zpow_of_nonzero hne, Blocks.det_G_padicValRat j hj ℓ h7]; simp

/-- The block diagonal leading matrix `blockdiag(2 y₀(h) G_{j(h)})`. -/
noncomputable def Bm (n ℓ : ℕ) : Matrix (HIdx n ℓ) (HIdx n ℓ) ℚ := fun x y =>
  if x.1 = y.1 then 2 * yA n ℓ x.1 * Blocks.Lam (jType ℓ x.1) ((x.2 : ℕ) + y.2) else 0

theorem det_Bm : (Bm n ℓ).det =
    ∏ i : ↥(anch n ℓ), (2 * yA n ℓ i) ^ 4 * (Blocks.G (jType ℓ i)).det := by
  let e : HIdx n ℓ ≃ Fin 4 × ↥(anch n ℓ) :=
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  have : Bm n ℓ = (Matrix.blockDiagonal
      (fun i : ↥(anch n ℓ) => (2 * yA n ℓ i) • Blocks.G (jType ℓ i))).submatrix e e := by
    ext x y
    simp only [Bm, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, e, Equiv.trans_apply,
      Equiv.sigmaEquivProd_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.smul_apply,
      smul_eq_mul, Blocks.G]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.det_smul, Fintype.card_fin]

theorem padicNorm_det_Bm (h : Adm n ℓ) :
    haveI := Fact.mk h.prime; padicNorm ℓ (Bm n ℓ).det = 1 := by
  haveI := Fact.mk h.prime
  rw [det_Bm]
  refine Finset.prod_induction _ (fun q => padicNorm ℓ q = 1)
    (fun a b ha hb => by simp only at ha hb ⊢; rw [padicNorm.mul, ha, hb, mul_one]) (by simp)
    fun i _ => ?_
  simp only
  have h2 : padicNorm ℓ (2 : ℚ) = 1 := by
    have := (padicNorm.nat_eq_one_iff (p := ℓ) 2).2 (fun hd =>
      h.ne_two ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 hd))
    simpa using this
  rw [padicNorm.mul, Hankel2.W2.padicNorm_pow', padicNorm.mul, h2, padicNorm_yA h i.2,
    padicNorm_det_G h.seven (jType_le ℓ i)]
  norm_num

/-- The functional `L_r = b + r a` as a linear map. -/
noncomputable def Lr (n : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun P := bL n P + r * aL n P
  map_add' P Q := by
    simp only [bL, aL, Pjet_add, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c P := by
    have hb : bL n (c • P) = c * bL n P := by
      simp only [bL, Pjet_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
    have ha : aL n (c • P) = c * aL n P := by
      simp only [aL, Pjet_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
    simp only [hb, ha, RingHom.id_apply, smul_eq_mul]
    ring

theorem card_HIdx (h : Adm n ℓ) : Fintype.card (HIdx n ℓ) = 4 * (3 * n + 1 - ℓ) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_coe, anch, Int.card_Icc]
  have h1 := R_of_even h.even
  have h2 := h.lo
  have h3 := h.third
  omega

/-- **N, Theorem 6.2 (non-vanishing).** -/
theorem nv_main (h : Adm n ℓ) (r : ℚ) (hr : ¬ ℓ ∣ r.den) :
    (hankelPoly n (4 * (3 * n + 1 - ℓ))).eval r ≠ 0 := by
  haveI := Fact.mk h.prime
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_basis h
  set Gh : Matrix (HIdx n ℓ) (HIdx n ℓ) ℚ := fun x y => Phi (nodes n) (betaL n ℓ) (E x * E y)
    with hGh
  set Gr : Matrix (HIdx n ℓ) (HIdx n ℓ) ℚ := fun x y => Phi (nodes n) (betaR n ℓ) (E x * E y)
    with hGr
  set Ga : Matrix (HIdx n ℓ) (HIdx n ℓ) ℚ := fun x y => Phi (nodes n) (alphaC n) (E x * E y)
    with hGa
  set Gc : Matrix (HIdx n ℓ) (HIdx n ℓ) ℚ := fun x y =>
    (ℓ : ℚ) ^ (-(wt x + wt y)) * Bm n ℓ x y with hGc
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  have hwGc : Hankel2.weightScale ℓ wt wt Gc = Bm n ℓ := by
    ext x y
    simp only [Hankel2.weightScale, hGc]
    rw [← mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, one_mul]
  have hG : ∀ x y, padicNorm ℓ (Hankel2.weightScale ℓ wt wt Gc x y) ≤ 1 := by
    intro x y
    rw [hwGc]
    unfold Bm
    split_ifs
    · refine (VB_zero_iff _).1 ?_
      have := ((VB_nat (ℓ := ℓ) 2).mul (VB_yA h x.1.2)).mul
        (VB_Lam (ℓ := ℓ) h.ne_two (jType_le ℓ x.1) (s := (x.2 : ℕ) + y.2)
          (by have := x.2.isLt; have := y.2.isLt; omega))
      simpa using this
    · simp
  have hdet : padicNorm ℓ (Hankel2.weightScale ℓ wt wt Gc).det = 1 := by
    rw [hwGc]; exact padicNorm_det_Bm h
  have hH : ∀ x y, padicNorm ℓ (Hankel2.weightScale ℓ wt wt (Gh - Gc + Gr) x y) < 1 := by
    intro x y
    rw [← VB_one_iff]
    have e : Hankel2.weightScale ℓ wt wt (Gh - Gc + Gr) x y =
        ((ℓ : ℚ) ^ (wt x + wt y) * Gh x y - Hankel2.weightScale ℓ wt wt Gc x y) +
          (ℓ : ℚ) ^ (wt x + wt y) * Gr x y := by
      simp only [Hankel2.weightScale, Matrix.add_apply, Matrix.sub_apply]; ring
    rw [e, hwGc]
    refine VB.add ?_ (Gr_bound h E hE1 hE2 x y)
    obtain ⟨i, a⟩ := x
    obtain ⟨i', b⟩ := y
    by_cases hii : i = i'
    · subst hii
      have := Gh_diag h E hE1 hE2 i a b
      simpa [Bm, hGh] using this
    · have := Gh_off h E hE1 hE2 ⟨i, a⟩ ⟨i', b⟩ hii
      simpa [Bm, hii, hGh] using this
  have hA : ∀ x y, padicNorm ℓ (Hankel2.weightScale ℓ wt wt Ga x y) < 1 := by
    intro x y
    rw [← VB_one_iff]
    exact Ga_bound h E hE1 hE2 x y
  have hcert := Hankel2.det_ne_zero_of_weight_certificate Gc (Gh - Gc + Gr) Ga wt wt hG hdet hH hA hr
  have hgram : Gc + (Gh - Gc + Gr) + r • Ga = Matrix.of fun x y => Lr n r (E x * E y) := by
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, Lr, LinearMap.coe_mk, AddHom.coe_mk, bL_eq n ℓ, hGh, hGr, hGa]
    unfold bLh bLr aL Phi
    ring
  rw [hgram] at hcert
  -- change of basis to the monomials
  set K := 4 * (3 * n + 1 - ℓ) with hK
  have hcard := card_HIdx h
  set e := Fintype.equivFinOfCardEq hcard
  set Cm : Matrix (Fin K) (Fin K) ℚ := fun d c => (E (e.symm c)).coeff d
  set Hank : Matrix (Fin K) (Fin K) ℚ := fun i j => Lr n r (X ^ ((i : ℕ) + j))
  have hdegK : ∀ x d, K ≤ d → (E x).coeff d = 0 := fun x d hd => hE3 x d (by omega)
  have hsum : ∀ c, E (e.symm c) = ∑ d : Fin K, Polynomial.C (Cm d c) * X ^ (d : ℕ) :=
    fun c => Hankel2.W3.Fam3.poly_eq_sum_fin _ (hdegK _)
  have hmul : Cm.transpose * Hank * Cm =
      (Matrix.of fun x y => Lr n r (E x * E y)).submatrix e.symm e.symm := by
    ext c c'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Hank]
    rw [hsum c, hsum c', Finset.sum_mul_sum]
    have e2 : ∀ (a b : ℚ) (i j : ℕ),
        Polynomial.C a * X ^ i * (Polynomial.C b * X ^ j) = (a * b) • X ^ (i + j) := by
      intro a b i j; rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul, pow_add]; ring
    simp only [e2, map_sum, map_smul, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hHank : (hankelPoly n K).eval r = Hank.det := by
    unfold hankelPoly
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Hank, Lr]
    ring
  rw [hHank]
  intro h0
  apply hcert
  have h1 := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul,
    Matrix.det_submatrix_equiv_self] at h1
  exact h1.symm

/-- **N, Theorem 6.2**, in exactly the form of the field `nonvanishing` of `Zeta35InputsR2`. -/
theorem nonvanishing_holds : ∀ n ℓ : ℕ, Even n → ℓ.Prime → R n < ℓ → 7 ≤ ℓ →
    3 * (ℓ - R n) ≤ ℓ → ∀ r : ℚ, ¬ ℓ ∣ r.den → (hankelPoly n (4 * (3 * n + 1 - ℓ))).eval r ≠ 0 :=
  fun _ _ hn hℓ hlo h7 h3 r hr => nv_main ⟨hn, hℓ, hlo, h7, h3⟩ r hr

end Zeta35.NV
