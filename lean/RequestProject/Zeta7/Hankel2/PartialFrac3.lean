import RequestProject.Zeta7.Hankel2.NVFamily3

/-!
# Partial fractions for the family-3 weight (paper §2.2)

Let `W(t) = (2t+n)(t+½)_n^6 / ∏_{k=-n}^{2n} (t+k)^4`.  For a polynomial `F` put
`N_F(t) = F(t)(2t+n)∏_{j<n}(t+j+½)^6` (the numerator of `F W`) and `D(t) = ∏_k (t+k)^4`.

* `Hankel2.Fam3PF.numPoly_eq_sum` — **the partial-fraction identity**: if `deg F ≤ 6n+2`
  (i.e. `deg(F W) ≤ -1`), then
  `N_F = ∑_{k=-n}^{2n} ∑_{i=1}^{4} r_{k,i}(F) (t+k)^{4-i} ∏_{k'≠k} (t+k')^4`,
  i.e. `F W = ∑_k ∑_i r_{k,i}(F) (t+k)^{-i}`, where `r_{k,i}(F) = W3.Fam3.resCoef n F k i` is the
  coefficient of `u^{-i}` of the Laurent expansion of `F W` at `t = -k` (the coefficients used by the
  node functional of `NVFamily3`).
* `Hankel2.Fam3PF.sum_resCoef_one_eq_zero` — **the residue theorem**: if `deg F ≤ 6n+1`
  (i.e. `deg(F W) ≤ -2`), the residues sum to zero: `∑_k r_{k,1}(F) = 0`.

The proof of the identity is Hermite unisolvence (`Hankel2.eq_zero_of_hermite_conditions`): the
difference of the two sides has degree `< 4(3n+1)` and vanishes to order `4` at every node,
by a power-series computation modulo `u^4` at each node.
-/

open Polynomial

namespace Hankel2.Fam3PF

/-- The nodes `k ∈ [-n, 2n]` (the poles of `W` are the points `t = -k`). -/
def nodes (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) (2 * n)

theorem card_nodes (n : ℕ) : (nodes n).card = 3 * n + 1 := by
  rw [nodes, Int.card_Icc]; omega

/-- The numerator `F(t)(2t+n)∏_{j<n}(t+j+½)^6` of `F W`. -/
noncomputable def numPoly (n : ℕ) (F : ℚ[X]) : ℚ[X] :=
  F * (C 2 * X + C (n : ℚ)) * ∏ j ∈ Finset.range n, (X + C ((j : ℚ) + 1 / 2)) ^ 6

/-- The denominator `D(t) = ∏_{k=-n}^{2n} (t+k)^4` of `W`. -/
noncomputable def denPoly (n : ℕ) : ℚ[X] := ∏ k ∈ nodes n, (X + C (k : ℚ)) ^ 4

/-- `D(t)/(t+k)^i = (t+k)^{4-i} ∏_{k'≠k} (t+k')^4`. -/
noncomputable def Dki (n : ℕ) (k : ℤ) (i : ℕ) : ℚ[X] :=
  (X + C (k : ℚ)) ^ (4 - i) * ∏ k' ∈ (nodes n).erase k, (X + C (k' : ℚ)) ^ 4

/-- The power series `∏_{k'≠k} (u + k' - k)^4` (the inverse of the pole part of `H_k`). -/
noncomputable def Ek (n : ℕ) (k : ℤ) : PowerSeries ℚ :=
  ∏ k' ∈ (nodes n).erase k, (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ 4

local notation "ι" => Polynomial.coeToPowerSeries.ringHom (R := ℚ)

theorem ι_X_add_C (a : ℚ) : ι (X + C a) = PowerSeries.C a + PowerSeries.X := by
  rw [map_add, add_comm]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

/-- A truncation identity modulo `u^4`. -/
theorem coeff_mul_eq_sum_trunc (G E : PowerSeries ℚ) {j : ℕ} (hj : j < 4) :
    PowerSeries.coeff j (G * E) =
      ∑ i ∈ Finset.Icc 1 4, PowerSeries.coeff (4 - i) G *
        PowerSeries.coeff j (PowerSeries.X ^ (4 - i) * E) := by
  have hI : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [hI]
  simp only [PowerSeries.coeff_mul]
  interval_cases j <;>
    simp [Finset.Nat.antidiagonal_succ, Finset.sum_insert, Finset.sum_singleton,
      PowerSeries.coeff_X_pow] <;> ring

/-- `r_{k,i}(F) = [u^{4-i}] (F(-k+u) H_k(u))`. -/
theorem resCoef_eq_coeff (n : ℕ) (F : ℚ[X]) (k : ℤ) {i : ℕ} (hi1 : 1 ≤ i) (hi4 : i ≤ 4) :
    W3.Fam3.resCoef n F k i =
      PowerSeries.coeff (4 - i) (ι (taylor (-(k : ℚ)) F) * W2.fam3H n k) := by
  rw [W3.Fam3.resCoef, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h5 : 5 - i = 4 - i + 1 := by omega
  rw [h5]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, taylor_coeff]

theorem taylor_prod {α : Type*} (r : ℚ) (s : Finset α) (f : α → ℚ[X]) :
    taylor r (∏ a ∈ s, f a) = ∏ a ∈ s, taylor r (f a) := by
  exact map_prod (taylorAlgHom r) f s

theorem taylor_X_add_C (r a : ℚ) : taylor r (X + C a) = X + C (a + r) := by
  simp only [map_add, taylor_X, taylor_C]
  ring

theorem fam3H_mul_Ek (n : ℕ) (k : ℤ) :
    W2.fam3H n k * Ek n k = W2.linF n k * ∏ j ∈ Finset.range n, W2.numF k j := by
  rw [W2.fam3H_eq, Ek, show Finset.Icc (-(n : ℤ)) (2 * n) = nodes n from rfl, mul_assoc,
    ← Finset.prod_mul_distrib]
  have h1 : ∀ k' ∈ (nodes n).erase k, W2.denF k k' *
      (PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X) ^ 4 = 1 := by
    intro k' hk'
    have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
    rw [W2.denF, ← mul_pow, PowerSeries.inv_mul_cancel, one_pow]
    simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
    exact_mod_cast sub_ne_zero.mpr hne
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one, mul_one]

/-- The Taylor expansion of the numerator at a node: `N_F(-k+u) = F(-k+u) H_k(u) E_k(u)`. -/
theorem ι_taylor_numPoly (n : ℕ) (F : ℚ[X]) (k : ℤ) :
    ι (taylor (-(k : ℚ)) (numPoly n F)) = ι (taylor (-(k : ℚ)) F) * W2.fam3H n k * Ek n k := by
  rw [mul_assoc, fam3H_mul_Ek, numPoly, taylor_mul, taylor_mul, taylor_prod, map_mul, map_mul,
    map_prod, mul_assoc]
  congr 2
  · rw [map_add, taylor_mul, taylor_C, taylor_X, taylor_C, W2.linF]
    simp only [map_add, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.coe_X]
    simp only [map_sub, map_mul, map_neg, map_natCast, map_intCast, map_ofNat]
    ring
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [taylor_pow, taylor_X_add_C, map_pow, ι_X_add_C, W2.numF]
    congr 3
    ring

/-- At a node `k' ≠ k` the term `D/(t+k')^i` vanishes to order `4` at `t = -k`. -/
theorem X_pow_dvd_taylor_Dki (n : ℕ) {k k' : ℤ} (hk : k ∈ nodes n) (hne : k' ≠ k) (i : ℕ) :
    X ^ 4 ∣ taylor (-(k : ℚ)) (Dki n k' i) := by
  rw [Dki, taylor_mul, taylor_prod]
  refine Dvd.dvd.mul_left ?_ _
  have hmem : k ∈ (nodes n).erase k' := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hk⟩
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  rw [taylor_pow, taylor_X_add_C]
  simp

/-- At the node `k` itself: `D/(t+k)^i` becomes `u^{4-i} E_k(u)`. -/
theorem ι_taylor_Dki_self (n : ℕ) (k : ℤ) (i : ℕ) :
    ι (taylor (-(k : ℚ)) (Dki n k i)) = PowerSeries.X ^ (4 - i) * Ek n k := by
  rw [Dki, taylor_mul, taylor_prod, map_mul, map_prod, taylor_pow, taylor_X_add_C, map_pow, Ek]
  congr 1
  · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  · refine Finset.prod_congr rfl fun k' _ => ?_
    rw [taylor_pow, taylor_X_add_C, map_pow, ι_X_add_C]
    congr 3
    push_cast; ring

/-- The remainder `N_F − ∑_k ∑_i r_{k,i}(F) D/(t+k)^i` of the partial-fraction expansion. -/
noncomputable def pfRem (n : ℕ) (F : ℚ[X]) : ℚ[X] :=
  numPoly n F - ∑ k ∈ nodes n, ∑ i ∈ Finset.Icc 1 4, C (W3.Fam3.resCoef n F k i) * Dki n k i

theorem coeff_eq_ι_coeff (P : ℚ[X]) (j : ℕ) : P.coeff j = PowerSeries.coeff j (ι P) := by
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]

/-- The remainder vanishes to order `4` at every node. -/
theorem hasse_pfRem_eq_zero (n : ℕ) (F : ℚ[X]) {k : ℤ} (hk : k ∈ nodes n) {j : ℕ} (hj : j < 4) :
    (hasseDeriv j (pfRem n F)).eval (-(k : ℚ)) = 0 := by
  rw [← taylor_coeff, pfRem, map_sub, map_sum, coeff_sub, finset_sum_coeff,
    Finset.sum_eq_single k]
  · rw [map_sum, finset_sum_coeff, coeff_eq_ι_coeff, ι_taylor_numPoly,
      coeff_mul_eq_sum_trunc _ _ hj, sub_eq_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
    rw [taylor_mul, taylor_C, coeff_C_mul, coeff_eq_ι_coeff, ι_taylor_Dki_self,
      resCoef_eq_coeff n F k hi1 hi4]
  · intro k' _ hne
    rw [map_sum, finset_sum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [taylor_mul, taylor_C, coeff_C_mul]
    have := (Polynomial.X_pow_dvd_iff.mp (X_pow_dvd_taylor_Dki n hk hne i)) j hj
    rw [this, mul_zero]
  · intro h; exact absurd hk h

theorem natDegree_prod_X_add_C_pow_le {α : Type*} (s : Finset α) (a : α → ℚ) (e : ℕ) :
    (∏ x ∈ s, (X + C (a x)) ^ e).natDegree ≤ e * s.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ x ∈ s, ((X + C (a x)) ^ e).natDegree ≤ ∑ _x ∈ s, e := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine natDegree_pow_le.trans ?_
        rw [natDegree_X_add_C, mul_one]
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem natDegree_numPoly_le (n : ℕ) (F : ℚ[X]) :
    (numPoly n F).natDegree ≤ F.natDegree + 1 + 6 * n := by
  rw [numPoly]
  refine natDegree_mul_le.trans ?_
  have h1 : (C (2 : ℚ) * X + C (n : ℚ)).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (by simp)
    · simp
  have h2 := natDegree_prod_X_add_C_pow_le (Finset.range n) (fun j => (j : ℚ) + 1 / 2) 6
  rw [Finset.card_range] at h2
  have h3 := (natDegree_mul_le (p := F) (q := C (2 : ℚ) * X + C (n : ℚ)))
  omega

theorem natDegree_Dki_le (n : ℕ) {k : ℤ} (hk : k ∈ nodes n) (i : ℕ) :
    (Dki n k i).natDegree ≤ (4 - i) + 12 * n := by
  rw [Dki]
  refine natDegree_mul_le.trans ?_
  have h1 : ((X + C (k : ℚ)) ^ (4 - i)).natDegree ≤ 4 - i := by
    refine natDegree_pow_le.trans ?_; rw [natDegree_X_add_C, mul_one]
  have h2 := natDegree_prod_X_add_C_pow_le ((nodes n).erase k) (fun k' => (k' : ℚ)) 4
  rw [Finset.card_erase_of_mem hk, card_nodes] at h2
  omega

theorem natDegree_pfRem_le (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 2) :
    (pfRem n F).natDegree ≤ 12 * n + 3 := by
  rw [pfRem]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have := natDegree_numPoly_le n F; omega
  · refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    have := natDegree_Dki_le n hk i
    have := (Finset.mem_Icc.mp hi).1
    omega

/-- **The partial-fraction identity** for `F W`, `deg F ≤ 6n + 2`:
`N_F = ∑_{k=-n}^{2n} ∑_{i=1}^{4} r_{k,i}(F) · (t+k)^{4-i} ∏_{k'≠k}(t+k')^4`. -/
theorem numPoly_eq_sum (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 2) :
    numPoly n F =
      ∑ k ∈ nodes n, ∑ i ∈ Finset.Icc 1 4, C (W3.Fam3.resCoef n F k i) * Dki n k i := by
  rw [← sub_eq_zero]
  change pfRem n F = 0
  have hinj : Function.Injective (fun k : nodes n => -((k : ℤ) : ℚ)) := by
    intro a b h
    simp only [neg_inj, Int.cast_inj] at h
    exact Subtype.ext h
  refine eq_zero_of_hermite_conditions (fun k : nodes n => -((k : ℤ) : ℚ)) hinj (fun _ => 4)
    (pfRem n F) ?_ ?_
  · have hsum : (∑ _i : nodes n, 4 : ℕ) = 12 * n + 4 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, card_nodes, smul_eq_mul]; ring
    rw [hsum]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast (Nat.lt_succ_of_le (natDegree_pfRem_le n F hF))
  · intro k j hj
    exact hasse_pfRem_eq_zero n F k.2 hj

theorem Dki_one_monic (n : ℕ) (k : ℤ) : (Dki n k 1).Monic := by
  rw [Dki]
  refine ((monic_X_add_C _).pow _).mul (monic_prod_of_monic _ _ fun k' _ => ?_)
  exact (monic_X_add_C _).pow _

theorem natDegree_Dki_one (n : ℕ) {k : ℤ} (hk : k ∈ nodes n) :
    (Dki n k 1).natDegree = 12 * n + 3 := by
  rw [Dki, Monic.natDegree_mul ((monic_X_add_C _).pow _)
    (monic_prod_of_monic _ _ fun k' _ => (monic_X_add_C _).pow _),
    natDegree_prod_of_monic _ _ fun k' _ => (monic_X_add_C _).pow _]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_erase_of_mem hk, card_nodes]
  omega

/-- **The residue theorem** for `F W` with `deg F ≤ 6n + 1` (i.e. `deg(F W) ≤ −2`): the
residues at the poles sum to zero, `∑_k r_{k,1}(F) = 0`. -/
theorem sum_resCoef_one_eq_zero (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 1) :
    ∑ k ∈ nodes n, W3.Fam3.resCoef n F k 1 = 0 := by
  have h := congrArg (fun P : ℚ[X] => P.coeff (12 * n + 3)) (numPoly_eq_sum n F (by omega))
  simp only [finset_sum_coeff, coeff_C_mul] at h
  have hl : (numPoly n F).coeff (12 * n + 3) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_numPoly_le n F; omega
  rw [hl] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hI : Finset.Icc 1 4 = insert 1 ({2, 3, 4} : Finset ℕ) := by decide
  rw [hI, Finset.sum_insert (by decide)]
  have h1 : (Dki n k 1).coeff (12 * n + 3) = 1 := by
    have := (Dki_one_monic n k).coeff_natDegree
    rwa [natDegree_Dki_one n hk] at this
  have h0 : ∀ i ∈ ({2, 3, 4} : Finset ℕ), (Dki n k i).coeff (12 * n + 3) = 0 := by
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_Dki_le n hk i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  rw [h1, mul_one, Finset.sum_eq_zero fun i hi => by rw [h0 i hi, mul_zero], add_zero]

end Hankel2.Fam3PF
