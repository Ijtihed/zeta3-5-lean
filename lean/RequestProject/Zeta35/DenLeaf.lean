import RequestProject.Zeta35.TreeBound
import RequestProject.Zeta35.ArchTaylor3
import RequestProject.Zeta7.Hankel2.Leaf82

/-!
# Denominators (N, Theorem 5.1), step 1: Taylor valuations and the leaf bound

Port of `Hankel2.Fam3` (`Taylor72.lean`, `Leaf82.lean`; P, Lemma 7.2 and §8.1; W, Lemmas 3.3–3.4)
to the weight of paper N (`q = 4`, `d = 1`, no zeros, nodes `|k| ≤ R`), for **every** prime `ℓ`
(including `ℓ = 2`; `ℓ = 3` is allowed too, since the factors `3^{M+1}` only help).

* `D_k = −v_ℓ(h_k) = 4 ∑_{m ≠ k} v_ℓ(k − m)` (`Dk3`);
* `norm_Hk_le3`: `v_ℓ(H_k[b]) ≥ −D_k − b λ_ℓ(k)`;
* `norm_Sk_le3`: `v_ℓ(S_k(M)) ≥ −(M+1) · max_{m ≤ 3|k|−1, 3 ∤ m} v_ℓ(m)`;
* if `9n < 2ℓ^{L+1}` (i.e. `9n/2 < ℓ^{L+1}`), all these valuations are `≤ L`, and
  `nv_cPoly_le3`: `v_ℓ(c_{k,a}) ≥ −D_k − (6 − a) L`;
* **`fP_le_sharp3`**: `f_ℓ(k, s) ≤ s D_k + 6 s L − L s (s − 1)`;
* `leaf_lemma3`: `f_ℓ(k, s) ≤ s D_k + 6 s L_ℓ`, `L_ℓ = ⌊log_ℓ (9n/2)⌋` (`Lp3`);
* `fP_le_single3`: if `9n < 2ℓ²` then `f_ℓ(k, s) + s² ≤ s (D_k + 7)`.
-/

open Finset Polynomial Hankel2

namespace Zeta35.Den

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D_k = −v_p(h_k) = 4 ∑_{m ≠ k} v_p(k − m)`. -/
def Dk3 (p n : ℕ) (k : ℤ) : ℤ := 4 * ∑ m ∈ (nodes n).erase k, (padicValInt p (k - m) : ℤ)

/-- The harmonic range of `S_k`: the `1 ≤ m < 3|k|` with `3 ∤ m`. -/
def hsRange3 (k : ℤ) : Finset ℕ := (range (3 * k.natAbs)).filter fun m => ¬ 3 ∣ m

/-- `max_m v_p(m)` over the harmonic range of `S_k`. -/
def hsMax3 (p : ℕ) (k : ℤ) : ℕ := (hsRange3 k).sup fun m => padicValNat p m

/-- `L_p = ⌊log_p (9n/2)⌋`: the least `L` with `9n < 2 p^{L+1}`. -/
def Lp3 (p n : ℕ) : ℕ := Nat.log p (9 * n / 2)

/-! ### `v_p(H_k[b]) ≥ −D_k − b λ_p(k)` -/

theorem serProf_Hser3 (n : ℕ) (k : ℤ) :
    Fam3.SerProf p (PF.Hser (nodes n) k) (Dk3 p n k) (lambdaP p n k) := by
  rw [Arch.Hser_eq_prod]
  have h := Fam3.SerProf.prod (p := p) ((nodes n).erase k)
    (F := fun k' => ((PowerSeries.C ((k' - k : ℤ) : ℚ) + PowerSeries.X)⁻¹) ^ 4)
    (D := fun k' => 4 * (padicValInt p (k - k') : ℤ)) (μ := lambdaP p n k) (fun k' hk' => by
      have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
      have h0 : (((k' - k : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
      have hμ : padicValInt p (k - k') ≤ lambdaP p n k :=
        Finset.le_sup (f := fun m => padicValInt p (k - m)) hk'
      have h1 := Fam3.SerProf.inv_lin (p := p) h0 (v := padicValInt p (k - k')) ?_ hμ
      · have := h1.pow 4
        exact_mod_cast this
      · rw [Fam3.padicNorm_eq_zpow_int (sub_ne_zero.2 hne), padicValInt_sub_comm p])
  refine h.mono (le_of_eq ?_)
  simp only [Dk3, Finset.mul_sum]

/-- **`v_p(H_k[b]) ≥ −D_k − b λ_p(k)`.** -/
theorem norm_Hk_le3 (n : ℕ) (k : ℤ) (b : ℕ) :
    padicNorm p (Hk n k b) ≤ (p : ℚ) ^ (Dk3 p n k + (b : ℤ) * lambdaP p n k) :=
  serProf_Hser3 n k b

/-! ### The harmonic sums -/

theorem norm_hsum3_le (k : ℤ) (M : ℕ) :
    padicNorm p (hsum3 k.natAbs M) ≤ (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) := by
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) := by
    have := Fam3.p_pos_q (p := p); positivity
  unfold hsum3
  refine padicNorm.sum_le' (fun m hm => ?_) hpos
  have hm0 : m ≠ 0 := by
    intro h; subst h; simp at hm
  have hle : padicValNat p m ≤ hsMax3 p k :=
    Finset.le_sup (f := fun m => padicValNat p m) hm
  rw [W2.padicNorm_inv, W2.padicNorm_pow']
  have hmz : ((m : ℤ) : ℚ) = (m : ℚ) := by push_cast; rfl
  rw [← hmz, Fam3.padicNorm_eq_zpow_int (by exact_mod_cast hm0), ← zpow_natCast, ← zpow_mul,
    ← zpow_neg]
  refine zpow_le_zpow_right₀ Fam3.one_le_p_q ?_
  have : (padicValInt p (m : ℤ) : ℤ) = padicValNat p m := by simp [padicValInt]
  rw [this]
  push_cast
  nlinarith

theorem norm_Sk_le3 (k : ℤ) (M : ℕ) :
    padicNorm p (Sk k M) ≤ (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) := by
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) := by
    have := Fam3.p_pos_q (p := p); positivity
  have h := norm_hsum3_le (p := p) k M
  have hc : padicNorm p ((M : ℚ) * 3 ^ (M + 1)) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (M * 3 ^ (M + 1)); push_cast at this; exact this
  unfold Sk
  split_ifs
  · rw [show -(M : ℚ) * 3 ^ (M + 1) * hsum3 k.natAbs M =
      -(((M : ℚ) * 3 ^ (M + 1)) * hsum3 k.natAbs M) by ring, padicNorm.neg, padicNorm.mul]
    calc _ ≤ 1 * (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) :=
          mul_le_mul hc h (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [show (M : ℚ) * (-1) ^ (M + 1) * 3 ^ (M + 1) * hsum3 k.natAbs M =
      (-1) ^ (M + 1) * (((M : ℚ) * 3 ^ (M + 1)) * hsum3 k.natAbs M) by ring, padicNorm.mul,
      padicNorm.mul, W2.padicNorm_pow', padicNorm.neg, padicNorm.one, one_pow, one_mul]
    calc _ ≤ 1 * (p : ℚ) ^ (((M + 1 : ℕ) : ℤ) * hsMax3 p k) :=
          mul_le_mul hc h (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  · simpa using hpos

/-! ### All the relevant valuations are `≤ L` when `9n < 2 p^{L+1}` -/

theorem lambdaP_le3 {n L : ℕ} (hL : 9 * n < 2 * p ^ (L + 1)) {k : ℤ} (hk : k ∈ nodes n) :
    lambdaP p n k ≤ L := by
  refine Finset.sup_le fun m hm => ?_
  have hm' := Finset.mem_Icc.1 (Finset.mem_of_mem_erase hm)
  have hk' := Finset.mem_Icc.1 hk
  have hne : k - m ≠ 0 := sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hm))
  refine Fam3.padicValInt_le_of_natAbs_lt hne ?_
  have hR : 2 * R n ≤ 3 * n := by unfold R; omega
  have : (k - m).natAbs ≤ 2 * R n := by omega
  omega

theorem hsMax_le3 {n L : ℕ} (hL : 9 * n < 2 * p ^ (L + 1)) {k : ℤ} (hk : k ∈ nodes n) :
    hsMax3 p k ≤ L := by
  refine Finset.sup_le fun m hm => ?_
  simp only [hsRange3, mem_filter, mem_range] at hm
  have hk' := Finset.mem_Icc.1 hk
  have hm0 : m ≠ 0 := by rintro rfl; exact hm.2 (dvd_zero 3)
  have hR : 2 * R n ≤ 3 * n := by unfold R; omega
  have hkR : k.natAbs ≤ R n := by omega
  have := Fam3.padicValInt_le_of_natAbs_lt (p := p) (x := (m : ℤ)) (by exact_mod_cast hm0)
    (L := L) (by simp only [Int.natAbs_natCast]; omega)
  simpa [padicValInt] using this

theorem nine_n_lt_pow_Lp3 (n : ℕ) : 9 * n < 2 * p ^ (Lp3 p n + 1) := by
  have h : 9 * n / 2 < p ^ (Lp3 p n + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt (9 * n / 2)
  omega

/-! ### The entries `c_{k,a}` -/

section Entries

variable {n L : ℕ} {k : ℤ}

theorem padicNorm_betaC_le3 (hL : 9 * n < 2 * p ^ (L + 1)) (hk : k ∈ nodes n) {m : ℕ}
    (hm : m ≤ 3) :
    padicNorm p (betaC n k m) ≤ (p : ℚ) ^ (Dk3 p n k + (6 - (m : ℤ)) * L) := by
  have hp0 := Fam3.p_pos_q (p := p)
  unfold betaC
  rw [padicNorm.neg]
  refine padicNorm.sum_le' (fun i hi => ?_) (by positivity)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  rw [padicNorm.mul, padicNorm.mul]
  have h1 : padicNorm p (i : ℚ) ≤ 1 := padicNorm.of_nat i
  have h2 := (norm_Sk_le3 (p := p) k (i + 1)).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q
    (mul_le_mul_of_nonneg_left (show ((hsMax3 p k : ℕ) : ℤ) ≤ (L : ℤ) by
      exact_mod_cast hsMax_le3 (p := p) hL hk) (by positivity)))
  have h3 : padicNorm p (Hk n k (4 - i - m)) ≤
      (p : ℚ) ^ (Dk3 p n k + ((4 - i - m : ℕ) : ℤ) * L) :=
    (norm_Hk_le3 (p := p) n k (4 - i - m)).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q
    (by
      have := lambdaP_le3 (p := p) hL hk
      have : ((4 - i - m : ℕ) : ℤ) * lambdaP p n k ≤ ((4 - i - m : ℕ) : ℤ) * L :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
      linarith))
  calc padicNorm p (i : ℚ) * padicNorm p (Hk n k (4 - i - m)) * padicNorm p (Sk k (i + 1))
      ≤ 1 * (p : ℚ) ^ (Dk3 p n k + ((4 - i - m : ℕ) : ℤ) * L) *
          (p : ℚ) ^ (((i + 1 + 1 : ℕ) : ℤ) * L) := by
        gcongr
        · exact padicNorm.nonneg _
        · exact padicNorm.nonneg _
    _ = (p : ℚ) ^ (Dk3 p n k + (6 - (m : ℤ)) * L) := by
        rw [one_mul, ← zpow_add₀ hp0.ne']
        congr 1
        push_cast [Nat.cast_sub (show m ≤ 4 - i by omega), Nat.cast_sub (show i ≤ 4 by omega)]
        ring

theorem padicNorm_alphaC_le3 (hL : 9 * n < 2 * p ^ (L + 1)) (hk : k ∈ nodes n) {m : ℕ}
    (hm : m ≤ 3) :
    padicNorm p (alphaC n k m) ≤ (p : ℚ) ^ (Dk3 p n k + (6 - (m : ℤ)) * L) := by
  have hp0 := Fam3.p_pos_q (p := p)
  unfold alphaC
  split_ifs with h
  · have hc : -(3 * (4 * 3 ^ 5) : ℚ) = -((2916 : ℕ) : ℚ) := by norm_num
    rw [hc, padicNorm.mul, padicNorm.neg]
    have h1 : padicNorm p ((2916 : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
    have h3 : padicNorm p (Hk n k (1 - m)) ≤ (p : ℚ) ^ (Dk3 p n k + (6 - (m : ℤ)) * L) :=
      (norm_Hk_le3 n k _).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q (by
        have := lambdaP_le3 (p := p) hL hk
        have : ((1 - m : ℕ) : ℤ) * lambdaP p n k ≤ ((1 - m : ℕ) : ℤ) * L :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
        have h8 : ((1 - m : ℕ) : ℤ) * L ≤ (6 - (m : ℤ)) * L :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        linarith))
    calc padicNorm p ((2916 : ℕ) : ℚ) * padicNorm p (Hk n k (1 - m))
        ≤ 1 * (p : ℚ) ^ (Dk3 p n k + (6 - (m : ℤ)) * L) :=
          mul_le_mul h1 h3 (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  · simp; positivity

/-- **The entry bound**: `v_p(c_{k,a}) ≥ −D_k − (6 − a) L`. -/
theorem nv_cPoly_le3 (hL : 9 * n < 2 * p ^ (L + 1)) (hk : k ∈ nodes n) (m : ℕ) :
    nv p (cPoly n k m) ≤ ((Dk3 p n k + (6 - (m : ℤ)) * L : ℤ) : WithBot ℤ) := by
  unfold cPoly
  split_ifs with hm
  · rw [nv_le_iff]
    intro i
    rw [coeff_add, coeff_C, coeff_C_mul_X]
    rcases i with _ | _ | i
    · simpa using Fam3.norm_le_of_padicNorm_le (padicNorm_betaC_le3 hL hk hm)
    · simpa using Fam3.norm_le_of_padicNorm_le (padicNorm_alphaC_le3 hL hk hm)
    · simp; positivity
  · simp

end Entries

/-! ### The minors and the leaf bound -/

section Leaf

variable {n L : ℕ} {k : ℤ}

/-- `−v_p(det C_k[R, {0..s−1}]) ≤ s D_k + 6 s L − L (∑R + C(s,2))`. -/
theorem nv_minorR_le3 (hL : 9 * n < 2 * p ^ (L + 1)) (hk : k ∈ nodes n) (Rs : Finset (Fin 4)) :
    nv p (minorR n k Rs) ≤ (((Rs.card : ℤ) * Dk3 p n k + 6 * Rs.card * L
      - L * ((∑ r ∈ Rs, (r : ℕ) : ℕ) + Rs.card.choose 2 : ℕ) : ℤ) : WithBot ℤ) := by
  unfold minorR
  refine (Fam3.nv_det_le_of_entry _
    (fun i => Dk3 p n k + 6 * L - L * ((Rs.orderEmbOfFin rfl i : Fin 4) : ℕ))
    (fun j => -(L * (j : ℕ) : ℤ)) fun i j => ?_).trans (le_of_eq ?_)
  · simp only [Matrix.of_apply, Cmat]
    refine (nv_cPoly_le3 hL hk _).trans (le_of_eq ?_)
    congr 1
    simp only [Fin.val_castLE]
    push_cast; ring
  · congr 1
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum, sum_neg_distrib,
      ← mul_sum]
    have h1 : ∑ i : Fin Rs.card, (((Rs.orderEmbOfFin rfl i : Fin 4) : ℕ) : ℤ) =
        ∑ r ∈ Rs, (r : ℕ) := by
      exact_mod_cast Fam3.sum_orderEmbOfFin Rs
    have h2 : ∑ i : Fin Rs.card, ((i : ℕ) : ℤ) = Rs.card.choose 2 := by
      exact_mod_cast Fam3.sum_fin_val Rs.card
    rw [h1, h2]
    push_cast; ring

/-- **Sharp leaf bound.** If `9n < 2p^{L+1}` then `f_p(k, s) ≤ s D_k + 6 s L − L s (s − 1)`. -/
theorem fP_le_sharp3 (hL : 9 * n < 2 * p ^ (L + 1)) (hk : k ∈ nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk3 p n k + 6 * s * L - L * s * (s - 1) : ℤ) : WithBot ℤ) := by
  unfold fP
  split_ifs with hs0
  · subst hs0; simp
  refine Finset.sup_le fun j _ => ?_
  have hlamL : lambdaP p n k ≤ L := lambdaP_le3 hL hk
  set B : ℤ := (s : ℤ) * Dk3 p n k + 6 * s * L - L * s * (s - 1)
  have hE : eP p n k s j ≤ ((B - (j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun Rs hRs => ?_
    simp only [mem_filter, mem_univ, true_and] at hRs
    obtain ⟨hRc, hRj⟩ := hRs
    refine (nv_minorR_le3 hL hk Rs).trans (WithBot.coe_le_coe.2 ?_)
    have hc := Fam3.choose_le_sum Rs
    have hj : (j : ℤ) = (∑ r ∈ Rs, (r : ℕ) : ℕ) - Rs.card.choose 2 := by
      rw [← hRj, Fam3.ellR]; push_cast [Nat.cast_sub hc]; ring
    have hch : ((s.choose 2 : ℕ) : ℤ) * 2 = s * (s - 1) := by
      have h2 : s.choose 2 * 2 = s * (s - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
      have h3 : ((s.choose 2 * 2 : ℕ) : ℤ) = ((s * (s - 1) : ℕ) : ℤ) := by rw [h2]
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at h3
      exact h3
    have hlam : ((j * lambdaP p n k : ℕ) : ℤ) ≤ j * L := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlamL) (by positivity)
    rw [hRc] at hj ⊢
    simp only [B]
    have hjL := congrArg (· * (L : ℤ)) hj
    have hchL := congrArg (· * (L : ℤ)) hch
    simp only at hjL hchL
    push_cast at hjL hlam ⊢
    nlinarith
  calc eP p n k s j + (((j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ)
      ≤ ((B - (j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) +
          (((j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) := add_le_add_left hE _
    _ = (B : WithBot ℤ) := by rw [← WithBot.coe_add, sub_add_cancel]

/-- **The leaf lemma** (N, §5; W, Lemma 3.4): `f_ℓ(k, s) ≤ s D_k + 6 s L_ℓ`. -/
theorem leaf_lemma3 (hk : k ∈ nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk3 p n k + 6 * s * Lp3 p n : ℤ) : WithBot ℤ) := by
  refine (fP_le_sharp3 (nine_n_lt_pow_Lp3 n) hk s).trans (WithBot.coe_le_coe.2 ?_)
  have h1 : (0 : ℤ) ≤ (Lp3 p n : ℤ) * s * (s - 1) := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp
    · have : (0 : ℤ) ≤ (s : ℤ) - 1 := by omega
      positivity
  linarith

/-- **Single-level leaf bound.** If `9n < 2ℓ²` then `f_ℓ(k, s) ≤ s D_k + 6 s − s (s − 1)`, i.e.
`f_ℓ(k, s) + s² ≤ s (D_k + 7)`. -/
theorem fP_le_single3 (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk3 p n k + 6 * s - s * (s - 1) : ℤ) : WithBot ℤ) := by
  have := fP_le_sharp3 (L := 1) (by simpa using h9) hk s
  simpa using this

end Leaf

end Zeta35.Den
