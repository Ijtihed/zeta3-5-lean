import RequestProject.Zeta35.NVPairs

/-!
# Non-vanishing (N, §6): valuations of the local constants

At an admissible prime `ℓ` (N, proof of Theorem 6.2):

* at an anchor `k`: `ℓ^{10−a} β^ℓ_{k,a} ≡ y₀(k) · limA(C_k) a (mod ℓ)` (`betaL_anchor`);
* at its partner `k − ℓ`: `ℓ^{10−a} β^ℓ_{k−ℓ,a} ≡ y₀'(k) · limP(C'_k) a (mod ℓ)` (`betaL_partner`);
* at paired nodes: `v(β^{rest}_{k,a}) ≥ a − 7` and `v(α_{k,a}) ≥ a − 5`;
* at singletons: `β^ℓ = 0`, `β^{rest}` and `α` are `ℓ`-integral.
-/

open Polynomial Finset

namespace Zeta35.NV

variable {n ℓ : ℕ}

theorem VB_rho_anchor [Fact ℓ.Prime] (b : ℕ) :
    VB ℓ ((-(-1 : ℚ)) ^ b * ((b + 3).choose 3 : ℚ)) 0 := by
  rw [neg_neg, one_pow, one_mul]; exact VB_nat _

theorem VB_rho_partner [Fact ℓ.Prime] (b : ℕ) :
    VB ℓ ((-(1 : ℚ)) ^ b * ((b + 3).choose 3 : ℚ)) 0 := by
  have := ((VB_one (ℓ := ℓ)).neg.pow b).mul (VB_nat ((b + 3).choose 3)); simpa using this

theorem betaL_anchor (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) (a : ℕ) (ha : a < 4) :
    haveI := Fact.mk h.prime
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * betaL n ℓ k a - yA n ℓ k * limA (Cset ℓ k.natAbs) a) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * betaL n ℓ k a) 0 := by
  haveI := Fact.mk h.prime
  have hpos := anch_pos h hk
  have hab : k.natAbs ≤ ℓ := by omega
  have hb : betaL n ℓ k a = -∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hk n k (4 - i - a) *
      ((fun _ => (-1 : ℚ)) (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
        ∑ c ∈ Cset ℓ k.natAbs, (((c : ℚ) * ℓ) ^ (i + 1 + 1))⁻¹) := by
    unfold betaL
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold SkL
    rw [if_pos hpos.1, hsumL_eq (i + 1) h.ne_three hab]
    push_cast; ring
  rw [hb]
  exact local_const h.ne_two (Hk n k) _ _ (yA n ℓ k) _ (fun c hc => mem_Cset hc) VB_rho_anchor
    (VB_yA h hk) (fun _ => (VB_one (ℓ := ℓ)).neg) (fun b => (Hk_anchor h hk b).1) a ha

theorem betaL_partner (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) (a : ℕ) (ha : a < 4) :
    haveI := Fact.mk h.prime
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * betaL n ℓ (k - ℓ) a -
      yP n ℓ k * limP (Cset ℓ (k - ℓ).natAbs) a) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (10 - a) * betaL n ℓ (k - ℓ) a) 0 := by
  haveI := Fact.mk h.prime
  have hpos := anch_pos h hk
  have hab : (k - ℓ).natAbs ≤ ℓ := by omega
  have hb : betaL n ℓ (k - ℓ) a = -∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hk n (k - ℓ) (4 - i - a) *
      ((fun M : ℕ => (-1 : ℚ) ^ (M + 1)) (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
        ∑ c ∈ Cset ℓ (k - ℓ).natAbs, (((c : ℚ) * ℓ) ^ (i + 1 + 1))⁻¹) := by
    unfold betaL
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold SkL
    rw [if_neg (by omega), if_pos (by omega), hsumL_eq (i + 1) h.ne_three hab]
    push_cast; ring
  rw [hb]
  exact local_const h.ne_two (Hk n (k - ℓ)) _ _ (yP n ℓ k) _ (fun c hc => mem_Cset hc)
    VB_rho_partner (VB_yP h hk) (fun M => (VB_one (ℓ := ℓ)).neg.pow (M + 1) |>.mono (by simp))
    (fun b => (Hk_partner h hk b).1) a ha

theorem betaL_single (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) (a : ℕ) : betaL n ℓ k a = 0 := by
  have hb := single_bound h hk h1 h2
  have h3 := h.third'
  have hS : ∀ M, SkL ℓ k M = 0 := by
    intro M
    have hz : hsumL ℓ k.natAbs M = 0 := hsumL_eq_zero M (by omega)
    unfold SkL; split_ifs <;> simp [hz]
  unfold betaL
  simp [hS]

/-- `v(β^{rest}_{k,a}) ≥ a − 7` whenever `v(H_k[b]) ≥ −4 − b`. -/
theorem betaR_paired [Fact ℓ.Prime] {k : ℤ} (hH : ∀ b, VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n k b) 0)
    (a : ℕ) (ha : a < 4) : VB ℓ (betaR n ℓ k a) ((a : ℤ) - 7) := by
  unfold betaR
  refine VB.neg (VB.sum _ _ fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  have h1 := VB_of_scaled (hH (4 - i - a))
  have h2 := ((VB_nat (ℓ := ℓ) i).mul h1).mul (VB_SkR (ℓ := ℓ) k (i + 1))
  refine h2.mono ?_
  push_cast
  omega

theorem alpha_paired [Fact ℓ.Prime] {k : ℤ} (hH : ∀ b, VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n k b) 0)
    (a : ℕ) : VB ℓ (alphaC n k a) ((a : ℤ) - 5) := by
  unfold alphaC
  split_ifs with ha
  · have h1 := VB_of_scaled (hH (1 - a))
    have h2 := (VB_int (ℓ := ℓ) (-(3 * (4 * 3 ^ 5)))).mul h1
    rw [show (-(3 * (4 * 3 ^ 5)) : ℚ) = ((-(3 * (4 * 3 ^ 5)) : ℤ) : ℚ) by push_cast; ring]
    refine h2.mono ?_
    push_cast
    omega
  · exact VB_zero _

theorem betaR_single (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) (a : ℕ) :
    haveI := Fact.mk h.prime; VB ℓ (betaR n ℓ k a) 0 := by
  haveI := Fact.mk h.prime
  unfold betaR
  refine VB.neg (VB.sum _ _ fun i _ => ?_)
  have := ((VB_nat (ℓ := ℓ) i).mul (Hk_single h hk h1 h2 (4 - i - a))).mul
    (VB_SkR (ℓ := ℓ) k (i + 1))
  simpa using this

theorem alpha_single (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) (a : ℕ) :
    haveI := Fact.mk h.prime; VB ℓ (alphaC n k a) 0 := by
  haveI := Fact.mk h.prime
  unfold alphaC
  split_ifs
  · have := (VB_int (ℓ := ℓ) (-(3 * (4 * 3 ^ 5)))).mul (Hk_single h hk h1 h2 (1 - a))
    rw [show (-(3 * (4 * 3 ^ 5)) : ℚ) = ((-(3 * (4 * 3 ^ 5)) : ℤ) : ℚ) by push_cast; ring]
    exact this.mono (by norm_num)
  · exact VB_zero _

end Zeta35.NV
