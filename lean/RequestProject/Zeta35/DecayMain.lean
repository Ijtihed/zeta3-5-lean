import RequestProject.Zeta35.DecayEntry
import RequestProject.Zeta7.Hankel2.Valuation

/-!
# N, Theorem 3.1 (3-adic decay)

For even `n` and `2 ≤ K ≤ 6n + 2`,
`‖Δ_K(ζ₃(5))‖₃ ≤ 3^{−(2 ∑_{i<K} v₃(i!_S) + K(4(3n+1) − log₃ D − log₃(D+1)))}`, `D = 2K − 2`
(`decay_holds`, the field `decay` of `Zeta35Inputs*`).

Proof: `Δ_K(ζ₃(5)) = det[L(x^{i+j})]` (purity); change to the Bhargava basis `C_i`
(`Zeta35.Bh.bhPoly`), whose leading coefficients have norm `3^{v₃(i!_S)}`; every entry
`L(C_i C_j)` has norm `≤ 3^{−4(3n+1)} D (D+1)` (`Zeta35.M3.norm_L_le`), since `C_i C_j` is
integral at the points `t + a/3`.
-/

open Polynomial Finset Hankel2

namespace Zeta35.Dec

/-- The functional `P ↦ b(P) + a(P) ζ₃(5)`, as a `ℚ`-linear map. -/
noncomputable def Lz (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ_[3] where
  toFun P := (bL n P : ℚ_[3]) + (aL n P : ℚ_[3]) * zeta3 5
  map_add' P Q := by
    have hj : ∀ k a, Pjet (P + Q) k a = Pjet P k a + Pjet Q k a := fun k a => by
      simp [Pjet, PF.Pjet]
    have hb : bL n (P + Q) = bL n P + bL n Q := by
      simp only [bL, hj, mul_add, Finset.sum_add_distrib]
    have ha : aL n (P + Q) = aL n P + aL n Q := by
      simp only [aL, hj, mul_add, Finset.sum_add_distrib]
    rw [hb, ha]; push_cast; ring
  map_smul' c P := by
    have hj : ∀ k a, Pjet (c • P) k a = c * Pjet P k a := fun k a => by
      simp [Pjet, PF.Pjet]
    have hb : bL n (c • P) = c * bL n P := by
      simp only [bL, hj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
    have ha : aL n (c • P) = c * aL n P := by
      simp only [aL, hj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
    rw [hb, ha, RingHom.id_apply, Rat.smul_def]; push_cast; ring

theorem Lz_apply (n : ℕ) (P : ℚ[X]) :
    Lz n P = (bL n P : ℚ_[3]) + (aL n P : ℚ_[3]) * zeta3 5 := rfl

/-- The coefficient matrix `T_{a i} = [x^a] C_i`. -/
noncomputable def Tmat (K : ℕ) : Matrix (Fin K) (Fin K) ℚ_[3] :=
  fun a i => (((Bh.bhPoly i).coeff a : ℚ) : ℚ_[3])

theorem bhPoly_eq_sum (K : ℕ) (i : Fin K) :
    Bh.bhPoly i = ∑ a : Fin K, C ((Bh.bhPoly i).coeff a) * X ^ (a : ℕ) := by
  conv_lhs => rw [(Bh.bhPoly i).as_sum_range' K (by rw [Bh.natDegree_bhPoly]; exact i.isLt)]
  rw [← Fin.sum_univ_eq_sum_range (fun a => monomial a ((Bh.bhPoly i).coeff a)) K]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [C_mul_X_pow_eq_monomial]

theorem Lz_bh_mul (n K : ℕ) (i k : Fin K) :
    Lz n (Bh.bhPoly i * Bh.bhPoly k) =
      ∑ a : Fin K, ∑ b : Fin K, Tmat K a i * Tmat K b k * Lz n (X ^ ((a : ℕ) + (b : ℕ))) := by
  rw [bhPoly_eq_sum K i, bhPoly_eq_sum K k, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : C ((Bh.bhPoly i).coeff a) * X ^ (a : ℕ) * (C ((Bh.bhPoly k).coeff b) * X ^ (b : ℕ)) =
      ((Bh.bhPoly i).coeff a * (Bh.bhPoly k).coeff b) • X ^ ((a : ℕ) + (b : ℕ)) := by
    rw [smul_eq_C_mul, pow_add, C_mul]; ring
  rw [this, map_smul, Rat.smul_def, Tmat, Tmat]
  push_cast; ring

theorem det_Tmat (K : ℕ) :
    (Tmat K).det = ∏ i : Fin K, (((3 : ℚ) ^ (i : ℕ) * ((3 : ℚ) ^ Bh.eS i)⁻¹ : ℚ) : ℚ_[3]) := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Tmat, Bh.leading_bhPoly]
  · intro a i hia
    simp only [Tmat]
    rw [Bh.bhPoly_coeff_eq_zero (show (i : ℕ) < a from hia)]; simp

theorem norm_lead (i : ℕ) :
    ‖(((3 : ℚ) ^ i * ((3 : ℚ) ^ Bh.eS i)⁻¹ : ℚ) : ℚ_[3])‖ = (3 : ℝ) ^ (vS i) := by
  push_cast
  rw [Bh.vS_eq, zpow_add₀ (by norm_num), zpow_neg, zpow_natCast, zpow_natCast]
  simp [M3.norm_three, inv_pow]

/-- The entries `L(C_i C_k)` in the Bhargava basis. -/
theorem norm_entry {n K : ℕ} (hn : Even n) (hK2 : 2 ≤ K) (hK : K ≤ 6 * n + 2) (i k : Fin K) :
    ‖Lz n (Bh.bhPoly i * Bh.bhPoly k)‖ ≤
      (3 : ℝ)⁻¹ ^ (4 * (3 * n + 1)) * ((2 * K - 2 : ℕ) : ℝ) * (((2 * K - 2 : ℕ) : ℝ) + 1) := by
  have hdeg : (Bh.bhPoly i * Bh.bhPoly k).natDegree ≤ 2 * K - 2 := by
    refine (natDegree_mul_le).trans ?_
    rw [Bh.natDegree_bhPoly, Bh.natDegree_bhPoly]
    have := i.isLt; have := k.isLt; omega
  rw [Lz_apply, ← purity_even hn _ (by omega), ← card_nodes_of_even hn]
  refine M3.norm_L_le n _ (by omega) hdeg fun a ha1 ha2 t => ?_
  obtain ⟨m1, h1⟩ := Bh.bhPoly_eval_int i t a ha1 ha2
  obtain ⟨m2, h2⟩ := Bh.bhPoly_eval_int k t a ha1 ha2
  exact ⟨m1 * m2, by rw [eval_mul, h1, h2]; push_cast; ring⟩

/-- The real-number identity behind the final bound. -/
theorem decay_arith (n K : ℕ) (hK2 : 2 ≤ K) :
    ((3 : ℝ)⁻¹ ^ (4 * (3 * n + 1)) * ((2 * K - 2 : ℕ) : ℝ) * (((2 * K - 2 : ℕ) : ℝ) + 1)) ^ K /
        ∏ i : Fin K, ((3 : ℝ) ^ (vS i)) ^ 2 = (3 : ℝ) ^ (-decayExp n K) := by
  set D : ℝ := ((2 * K - 2 : ℕ) : ℝ)
  have hD : 0 < D := by simp only [D]; exact_mod_cast (by omega : 0 < 2 * K - 2)
  have hD1 : 0 < D + 1 := by linarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have eD : D = (3 : ℝ) ^ Real.logb 3 D := (Real.rpow_logb h3 (by norm_num) hD).symm
  have eD1 : D + 1 = (3 : ℝ) ^ Real.logb 3 (D + 1) := (Real.rpow_logb h3 (by norm_num) hD1).symm
  have eP : ∏ i : Fin K, ((3 : ℝ) ^ (vS i)) ^ 2 = (3 : ℝ) ^ (2 * ∑ i ∈ range K, (vS i : ℝ)) := by
    rw [Finset.mul_sum, Real.rpow_sum_of_pos h3, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul_natCast h3.le]
    congr 1; push_cast; ring
  have e3 : (3 : ℝ)⁻¹ ^ (4 * (3 * n + 1)) = (3 : ℝ) ^ (-(4 * (3 * (n : ℝ) + 1))) := by
    rw [Real.rpow_neg (by norm_num), inv_pow]
    congr 1
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  rw [eP, e3]
  have eL : ((3 : ℝ) ^ (-(4 * (3 * (n : ℝ) + 1))) * D * (D + 1)) =
      (3 : ℝ) ^ (-(4 * (3 * (n : ℝ) + 1))) * (3 : ℝ) ^ Real.logb 3 D *
        (3 : ℝ) ^ Real.logb 3 (D + 1) := by rw [← eD, ← eD1]
  rw [eL]
  rw [← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_mul_natCast h3.le, ← Real.rpow_sub h3,
    decayExp]
  congr 1
  simp only [D]
  ring

/-- **N, Theorem 3.1 (3-adic decay).** -/
theorem decay_holds : ∀ n K : ℕ, Even n → 2 ≤ K → K ≤ 6 * n + 2 →
    ‖aeval (zeta3 5) (hankelPoly n K)‖ ≤ (3 : ℝ) ^ (-decayExp n K) := by
  intro n K hn hK2 hK
  rw [aeval_zeta_hankelPoly hn hK]
  set B : ℝ := (3 : ℝ)⁻¹ ^ (4 * (3 * n + 1)) * ((2 * K - 2 : ℕ) : ℝ) *
    (((2 * K - 2 : ℕ) : ℝ) + 1)
  have hB : 0 ≤ B := by positivity
  set H := Matrix.of fun i j : Fin K => Lz n (X ^ ((i : ℕ) + (j : ℕ)))
  have hH : (Matrix.of fun i j : Fin K => L n (X ^ ((i : ℕ) + (j : ℕ)))) = H := by
    ext i j
    simp only [H, Matrix.of_apply, Lz_apply]
    rw [purity_even hn _ (by rw [natDegree_X_pow]; have := i.isLt; have := j.isLt; omega)]
  rw [hH]
  set G := Matrix.of fun i k : Fin K => ∑ a : Fin K, ∑ b : Fin K,
    Tmat K a i * Tmat K b k * Lz n (X ^ ((a : ℕ) + (b : ℕ)))
  have hG : G.det = (Tmat K).det ^ 2 * H.det :=
    det_moment_basis_change K (fun e => Lz n (X ^ e)) (Tmat K)
  have hGn : ‖G.det‖ ≤ B ^ K := by
    refine norm_det_le_max_perm G (B ^ K) (pow_nonneg hB K) fun σ => ?_
    calc ∏ i, ‖G (σ i) i‖ ≤ ∏ _i : Fin K, B := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
          simp only [G, Matrix.of_apply]
          rw [← Lz_bh_mul]
          exact norm_entry hn hK2 hK _ _
      _ = B ^ K := by simp
  have hT : ‖(Tmat K).det‖ = ∏ i : Fin K, (3 : ℝ) ^ (vS i) := by
    rw [det_Tmat, norm_prod]
    exact Finset.prod_congr rfl fun i _ => norm_lead i
  have hTpos : 0 < ‖(Tmat K).det‖ := by rw [hT]; positivity
  have hnorm : ‖H.det‖ = ‖G.det‖ / ‖(Tmat K).det‖ ^ 2 := by
    rw [hG, norm_mul, norm_pow]; field_simp
  rw [hnorm, ← decay_arith n K hK2, hT, ← Finset.prod_pow]
  exact div_le_div_of_nonneg_right hGn (by positivity)

end Zeta35.Dec
