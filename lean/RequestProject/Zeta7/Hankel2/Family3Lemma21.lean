import RequestProject.Zeta7.Hankel2.Family3

/-!
# Lemma 2.1 (purity / node decomposition), the Hankel polynomial `Δ_K`, and the identification
# with the node functional of `NVFamily3`

Paper §2.2.  For a polynomial `P ∈ ℚ[x]` (`x = t + n/2`) write `P_a(k) = [u^a] P(x_k + u)` for its
Taylor coefficients at the node `x_k = n/2 − k` (`Pjet`), and `H_k[b] = [u^b] W̃_k(u)`,
`W̃_k(u) = u^4 W(−k+u)` (`Hk`, the coefficients of `W2.fam3H`).  With `φ_i = i(i+1)(i+2)`:

* `α_{k,a} = −φ₃·6·2⁷·H_k[1−a]` for `a ≤ 1`, `α_{k,a} = 0` for `a ≥ 2` (paper v4.1 eq. (7), `alphaC`);
* `β_{k,a} = ∑_{i=1}^{4−a} φ_i (i+3) HS(k, i+4) H_k[4−i−a]` (paper v4.1 eq. (8), `betaC`).

**Lemma 2.1** (`Hankel2.Fam3.lemma_2_1`): if `deg P ≤ 6n+1` then the Volkenborn integral defining
`L(P)` exists and
`L(P) = ∑_{k=-n}^{2n} ∑_{a=0}^{3} c_{k,a} P_a(k)`, `c_{k,a} = β_{k,a} + ζ₂(7) α_{k,a}`,
i.e. `L(P) = a(P) ζ₂(7) + b(P)` with `a(P) = ∑ α_{k,a} P_a(k)`, `b(P) = ∑ β_{k,a} P_a(k)`.

**The Hankel polynomial** (paper eq. (1.3)): `Δ_K(X) = det[b(x^{i+j}) + X a(x^{i+j})]_{i,j<K}`
(`hankelPoly`).  For `K ≤ 3n+1`:

* `aeval_zeta_hankelPoly`: `Δ_K(ζ₂(7)) = det[L(x^{i+j})]`;
* `hankelPoly_eval_eq`: for rational `r`, `Δ_K(r) = (−1)^K det[L_r^{node}(t^{i+j})]`, where
  `L_r^{node} = W3.Fam3.nodeFunctional n r` is the node functional of `NVFamily3`.  The
  identification is `nodeFunctional_eq`: `L_r^{node}(P(t + n/2)) = −(r a(P) + b(P))`.
* `hankelPoly_eval_ne_zero`: consequently **Theorem NV (`nv_family3`) applies to the true Hankel
  polynomial**: for odd `n`, a prime `p` with `7n+2 ≤ 4p`, `p+1 ≤ 2n`, `K = 10n+3−4p`, and every
  rational `r` with `p ∤ den r`, `Δ_K(r) ≠ 0`.
-/

open Polynomial Finset

namespace Hankel2.Fam3

/-- `H_k[b] = [u^b] W̃_k(u)`. -/
noncomputable def Hk (n : ℕ) (k : ℤ) (b : ℕ) : ℚ := PowerSeries.coeff b (W2.fam3H n k)

/-- The node `x_k = n/2 − k`. -/
noncomputable def xnode (n : ℕ) (k : ℤ) : ℚ := (n : ℚ) / 2 - k

/-- The Taylor coefficient `P_a(k) = [u^a] P(x_k + u)`. -/
noncomputable def Pjet (n : ℕ) (P : ℚ[X]) (k : ℤ) (a : ℕ) : ℚ := (hasseDeriv a P).eval (xnode n k)

/-- `α_{k,a}` of paper v4.1 eq. (7). -/
noncomputable def alphaC (n : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  if a ≤ 1 then -(phi 3) * 6 * 2 ^ 7 * Hk n k (1 - a) else 0

/-- `β_{k,a}` of paper v4.1 eq. (8). -/
noncomputable def betaC (n : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  ∑ i ∈ Icc 1 (4 - a), phi i * (i + 3) * HS k (i + 4) * Hk n k (4 - i - a)

/-- `a(P) = ∑_k ∑_{a≤3} α_{k,a} P_a(k)`, the coefficient of `ζ₂(7)` in `L(P)`. -/
noncomputable def aL (n : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ Fam3PF.nodes n, ∑ a ∈ range 4, alphaC n k a * Pjet n P k a

/-- `b(P) = ∑_k ∑_{a≤3} β_{k,a} P_a(k)`, the rational part of `L(P)`. -/
noncomputable def bL (n : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ Fam3PF.nodes n, ∑ a ∈ range 4, betaC n k a * Pjet n P k a

/-- **The Hankel polynomial** `Δ_K(X) = det[b(x^{i+j}) + X a(x^{i+j})]_{i,j<K}` (paper (1.3)). -/
noncomputable def hankelPoly (n K : ℕ) : ℚ[X] :=
  (Matrix.of fun i j : Fin K =>
    C (bL n (X ^ ((i : ℕ) + j))) + C (aL n (X ^ ((i : ℕ) + j))) * X).det

/-! ### Change of variable `x = t + n/2` -/

theorem hasse_taylor_eval (P : ℚ[X]) (r s : ℚ) (j : ℕ) :
    (hasseDeriv j (taylor r P)).eval s = (hasseDeriv j P).eval (s + r) := by
  rw [← taylor_coeff, taylor_taylor, taylor_coeff]

theorem resCoef_taylor (n : ℕ) (P : ℚ[X]) (k : ℤ) (i : ℕ) :
    W3.Fam3.resCoef n (taylor ((n : ℚ) / 2) P) k i =
      ∑ j ∈ range (5 - i), Pjet n P k j * Hk n k (4 - i - j) := by
  simp only [W3.Fam3.resCoef, hasse_taylor_eval, Pjet, Hk, xnode]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2; ring

theorem aeval_taylor (P : ℚ[X]) (r : ℚ) (s : ℚ_[2]) :
    aeval s (taylor r P) = aeval (s + (r : ℚ_[2])) P := by
  rw [aeval_def, ← eval_map, map_taylor, taylor_eval, eval_map, ← aeval_def]
  rfl

/-! ### The finite resummations -/

theorem sum4 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Icc 1 4, f i = f 1 + f 2 + f 3 + f 4 := by
  rw [show Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp [add_assoc]

theorem resum_beta (J H S : ℕ → ℚ) :
    ∑ i ∈ Icc 1 4, phi i * (i + 3) * (∑ j ∈ range (5 - i), J j * H (4 - i - j)) * S (i + 4) =
      ∑ a ∈ range 4, (∑ i ∈ Icc 1 (4 - a), phi i * (i + 3) * S (i + 4) * H (4 - i - a)) * J a := by
  rw [sum4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show Icc 1 (4 - 0) = ({1, 2, 3, 4} : Finset ℕ) by decide,
    show Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) by decide,
    show Icc 1 (4 - 2) = ({1, 2} : Finset ℕ) by decide,
    show Icc 1 (4 - 3) = ({1} : Finset ℕ) by decide]
  simp
  ring

theorem resum_alpha (J H : ℕ → ℚ) :
    -(phi 3) * 6 * 2 ^ 7 * ∑ j ∈ range (5 - 3), J j * H (4 - 3 - j) =
      ∑ a ∈ range 4, (if a ≤ 1 then -(phi 3) * 6 * 2 ^ 7 * H (1 - a) else 0) * J a := by
  simp [Finset.sum_range_succ]
  ring

/-- The value of `L(P)` in the node form, `deg P ≤ 6n+1`. -/
theorem hasVolkenborn_famL (n : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 6 * n + 1) :
    HasVolkenborn 2
      (fun t => iteratedDeriv 3 (fun s => aeval (s + (n : ℚ_[2]) / 2) P * W n s) (t + 1 / 2))
      ((aL n P : ℚ_[2]) * zeta2 7 + (bL n P : ℚ_[2])) := by
  set F := taylor ((n : ℚ) / 2) P with hF
  have hFdeg : F.natDegree ≤ 6 * n + 1 := by rw [hF, natDegree_taylor]; exact hP
  have hfun : (fun t : ℚ_[2] => iteratedDeriv 3
      (fun s => aeval (s + (n : ℚ_[2]) / 2) P * W n s) (t + 1 / 2)) =
      fun t => integrandT n F (t + 1 / 2) := by
    funext t
    rw [integrandT]
    congr 1
    funext s
    rw [hF, aeval_taylor]
    push_cast
    rfl
  rw [hfun]
  convert hasVolkenborn_integrandT n F hFdeg using 1
  congr 1
  · congr 1
    rw [aL, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : (∑ a ∈ range 4, alphaC n k a * Pjet n P k a) =
        6 * 2 ^ 7 * (-(phi 3) * ∑ j ∈ range (5 - 3), Pjet n P k j * Hk n k (4 - 3 - j)) := by
      simp only [alphaC]; rw [← resum_alpha]; ring
    rw [hF, resCoef_taylor, hq]
    push_cast
    ring
  · rw [bL, Rat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Rat.cast_sum]
    congr 1
    simp only [hF, resCoef_taylor]
    have := resum_beta (fun j => Pjet n P k j) (fun b => Hk n k b) (fun M => HS k M)
    rw [this]
    rfl

/-- **Lemma 2.1 (purity and node decomposition).**  If `deg P ≤ 6n+1`, then the Volkenborn
integral defining `L(P)` exists, and
`L(P) = ∑_{k=-n}^{2n} ∑_{a=0}^{3} (β_{k,a} + ζ₂(7) α_{k,a}) P_a(k) = a(P) ζ₂(7) + b(P)`. -/
theorem lemma_2_1 (n : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 6 * n + 1) :
    (∃ I, HasVolkenborn 2
      (fun t => iteratedDeriv 3 (fun s => aeval (s + (n : ℚ_[2]) / 2) P * W n s) (t + 1 / 2)) I) ∧
    famL n P = ∑ k ∈ Fam3PF.nodes n, ∑ a ∈ range 4,
      ((betaC n k a : ℚ_[2]) + zeta2 7 * (alphaC n k a : ℚ_[2])) * (Pjet n P k a : ℚ_[2]) ∧
    famL n P = (aL n P : ℚ_[2]) * zeta2 7 + (bL n P : ℚ_[2]) := by
  have h := hasVolkenborn_famL n P hP
  have hL : famL n P = (aL n P : ℚ_[2]) * zeta2 7 + (bL n P : ℚ_[2]) := h.volkInt_eq
  refine ⟨⟨_, h⟩, ?_, hL⟩
  rw [hL, aL, bL]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### Identification with the node functional of `NVFamily3` -/

/-- **The node functional of `NVFamily3` is (minus) the family-3 functional.**  For
`deg P ≤ 6n+1` and rational `r`, `L_r^{node}(P(t+n/2)) = −(r a(P) + b(P))`; in particular
`L(P) = −L^{node}_{ζ₂(7)}(P(t + n/2))` once the node functional is extended linearly in `r`. -/
theorem nodeFunctional_eq (n : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ 6 * n + 1) (r : ℚ) :
    W3.Fam3.nodeFunctional n r (taylor ((n : ℚ) / 2) P) = -(r * aL n P + bL n P) := by
  have hres := Fam3PF.sum_resCoef_one_eq_zero n (taylor ((n : ℚ) / 2) P)
    (by rw [natDegree_taylor]; exact hP)
  have hsplit : W3.Fam3.nodeFunctional n r (taylor ((n : ℚ) / 2) P) =
      r * W3.Fam3.alphaW 1 * ∑ k ∈ Fam3PF.nodes n, W3.Fam3.resCoef n (taylor ((n : ℚ) / 2) P) k 1 +
      ∑ k ∈ Fam3PF.nodes n,
        (r * W3.Fam3.alphaW 3 * W3.Fam3.resCoef n (taylor ((n : ℚ) / 2) P) k 3 +
          ∑ i ∈ Icc 1 4, W3.Fam3.betaW k i * W3.Fam3.resCoef n (taylor ((n : ℚ) / 2) P) k i) := by
    rw [W3.Fam3.nodeFunctional, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum4, sum4]
    simp only [W3.Fam3.alphaW]
    norm_num
    ring
  rw [hsplit, show Fam3PF.nodes n = Finset.Icc (-(n : ℤ)) (2 * n) from rfl] at *
  rw [hres, mul_zero, zero_add, aL, bL, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [resCoef_taylor]
  have hb := resum_beta (fun j => Pjet n P k j) (fun b => Hk n k b) (fun M => HS k M)
  have ha := resum_alpha (fun j => Pjet n P k j) (fun b => Hk n k b)
  have hA : ∑ a ∈ range 4, alphaC n k a * Pjet n P k a =
      -(phi 3) * 6 * 2 ^ 7 * ∑ j ∈ range (5 - 3), Pjet n P k j * Hk n k (4 - 3 - j) := by
    simp only [alphaC]; exact ha.symm
  have hB : ∑ a ∈ range 4, betaC n k a * Pjet n P k a =
      ∑ i ∈ Icc 1 4, phi i * (i + 3) * (∑ j ∈ range (5 - i), Pjet n P k j * Hk n k (4 - i - j)) *
        HS k (i + 4) := by
    simp only [betaC]; exact hb.symm
  rw [hA, hB]
  simp only [W3.Fam3.betaW, W3.Fam3.alphaW, W3.Fam3.cI, phi, HS, sum4]
  norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-! ### Shift invariance of Hankel determinants -/

/-- A Hankel determinant of moments is invariant under the shift `X ↦ X + c`. -/
theorem hankel_det_shift {R : Type*} [CommRing R] [Nontrivial R] (μ : R[X] →ₗ[R] R) (c : R)
    (K : ℕ) :
    (Matrix.of fun i j : Fin K => μ ((X + C c) ^ ((i : ℕ) + j))).det =
      (Matrix.of fun i j : Fin K => μ (X ^ ((i : ℕ) + j))).det := by
  set T : Matrix (Fin K) (Fin K) R := Matrix.of fun a i => ((X + C c) ^ (i : ℕ)).coeff a with hT
  have hmon : ∀ i : ℕ, ((X + C c) ^ i).Monic := fun i => (monic_X_add_C c).pow i
  have hdeg : ∀ i : ℕ, ((X + C c) ^ i).natDegree = i := fun i => by
    exact natDegree_pow_X_add_C i c
  have hsum : ∀ i : Fin K, (X + C c) ^ (i : ℕ) = ∑ a : Fin K, C (T a i) * X ^ (a : ℕ) := by
    intro i
    have e := as_sum_range' ((X + C c) ^ (i : ℕ)) K (by rw [hdeg]; exact i.isLt)
    conv_lhs => rw [e]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hT, C_mul_X_pow_eq_monomial]
  have hentry : ∀ i k : Fin K, μ ((X + C c) ^ ((i : ℕ) + k)) =
      ∑ a : Fin K, ∑ b : Fin K, T a i * T b k * μ (X ^ ((a : ℕ) + (b : ℕ))) := by
    intro i k
    rw [pow_add, hsum i, hsum k, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : C (T a i) * X ^ (a : ℕ) * (C (T b k) * X ^ (b : ℕ)) =
        (T a i * T b k) • X ^ ((a : ℕ) + (b : ℕ)) := by
      rw [smul_eq_C_mul, pow_add, C_mul]; ring
    rw [this, map_smul, smul_eq_mul]
  have hTdet : T.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp only [hT, Matrix.of_apply]
      have := (hmon i).coeff_natDegree
      rwa [hdeg] at this
    · intro i j hij
      simp only [hT, Matrix.of_apply]
      exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hij)
  have h := det_moment_basis_change K (fun e => μ (X ^ e)) T
  rw [hTdet, one_pow, one_mul] at h
  rw [← h]
  congr 1
  ext i k
  simp only [Matrix.of_apply]
  exact hentry i k

/-- The node functional as a `ℚ`-linear map. -/
noncomputable def nodeLin (n : ℕ) (r : ℚ) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun := W3.Fam3.nodeFunctional n r
  map_add' := W3.Fam3.nodeFunctional_add r
  map_smul' := fun a F => by simp [W3.Fam3.nodeFunctional_smul]

/-! ### The Hankel polynomial -/

theorem natDegree_X_pow_le_of_lt {n K : ℕ} (hK : K ≤ 3 * n + 1) (i j : Fin K) :
    (X ^ ((i : ℕ) + j) : ℚ[X]).natDegree ≤ 6 * n + 1 := by
  rw [natDegree_X_pow]; omega

/-- **`Δ_K(ζ₂(7)) = det[L(x^{i+j})]`** for `K ≤ 3n+1`. -/
theorem aeval_zeta_hankelPoly (n K : ℕ) (hK : K ≤ 3 * n + 1) :
    aeval (zeta2 7) (hankelPoly n K) =
      (Matrix.of fun i j : Fin K => famL n (X ^ ((i : ℕ) + j))).det := by
  rw [hankelPoly, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, aeval_C,
    aeval_X, eq_ratCast]
  rw [(lemma_2_1 n _ (natDegree_X_pow_le_of_lt hK i j)).2.2]
  ring

/-- **`Δ_K(r) = (−1)^K det[L_r^{node}(t^{i+j})]`** for rational `r` and `K ≤ 3n+1`: the Hankel
polynomial of `L` evaluated at `r` is, up to sign, the Hankel determinant of the node functional
used in `NVFamily3`. -/
theorem hankelPoly_eval_eq (n K : ℕ) (hK : K ≤ 3 * n + 1) (r : ℚ) :
    (hankelPoly n K).eval r = (-1) ^ K * (W3.Fam3.hankelNode n K r).det := by
  rw [hankelPoly, ← coe_evalRingHom, RingHom.map_det]
  have hent : (evalRingHom r).mapMatrix (Matrix.of fun i j : Fin K =>
      C (bL n (X ^ ((i : ℕ) + j))) + C (aL n (X ^ ((i : ℕ) + j))) * X) =
      -(Matrix.of fun i j : Fin K => nodeLin n r ((X + C ((n : ℚ) / 2)) ^ ((i : ℕ) + j))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.neg_apply,
      coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, nodeLin, LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [← taylor_X_pow, nodeFunctional_eq n _ (natDegree_X_pow_le_of_lt hK i j)]
    ring
  rw [hent, Matrix.det_neg, Fintype.card_fin, hankel_det_shift]
  rfl

/-- **Theorem NV for the true Hankel polynomial.**  For odd `n`, a prime `p` with `7n+2 ≤ 4p`
and `p+1 ≤ 2n`, `K = 10n+3−4p`, and every rational `r` with `p ∤ den r`: `Δ_K(r) ≠ 0`. -/
theorem hankelPoly_eval_ne_zero {n p : ℕ} [Fact p.Prime] (hn : n % 2 = 1)
    (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) (r : ℚ) (hr : ¬ p ∣ r.den) :
    (hankelPoly n (10 * n + 3 - 4 * p)).eval r ≠ 0 := by
  rw [hankelPoly_eval_eq n _ (by omega)]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (W3.Fam3.nv_family3 hn hlow hup r hr)

end Hankel2.Fam3
