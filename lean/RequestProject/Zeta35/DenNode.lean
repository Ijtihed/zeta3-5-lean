import RequestProject.Zeta35.DenSmall

/-!
# Denominators (N, Theorem 5.1), step 3: the node bound for single-level primes

For a single-level prime (`9n < 2ℓ²`) and a node `k` put (N, §5; W, Lemma 3.6)

* `o_k = #{m ≠ k : ℓ ∣ k − m}` (`oK3`), `μ_k = 1[o_k > 0]`;
* `hs_k = 1[ℓ < 3|k|]` (`hsI`): the harmonic denominators of `S_k` are the `m ≤ 3|k| − 1`
  with `3 ∤ m`, so `S_k` is `ℓ`-integral unless `ℓ < 3|k|`.

Then `D_k = 4 o_k` (`Dk3_single`), `λ_ℓ(k) ≤ μ_k`, `max v_ℓ(m) ≤ hs_k`, and

  **`fP_add_sq_le_wnode`**: `f_ℓ(k, s) + s² ≤ w(o_k, hs_k, s)`,

where `w(o, hs, s) = s²` for an `hs`-free singleton (`o = hs = 0`) and `w = s (4(o+1) + 3 hs)`
otherwise.  This is the bound `f⁺ + s² ≤ s(4(o+1) + 3hs)`, `f⁺ = 0` for `hs`-free singletons, of
the round-3 brief.  The proof is a general minor bound `fP_le_gen`: if `v_ℓ(c_{k,a}) ≥ −D − (A−a)L`
for all `a ≤ 3` and `λ_ℓ(k) ≤ L`, then `f_ℓ(k,s) ≤ sD + AsL − Ls(s−1)`.
-/

open Finset Polynomial Hankel2

namespace Zeta35.Den

variable {p : ℕ} [hp : Fact p.Prime]

/-- `o_k = #{m ≠ k : p ∣ k − m}`. -/
def oK3 (p n : ℕ) (k : ℤ) : ℕ := cntL3 n p k

/-- `hs_k = 1[p < 3|k|]`. -/
def hsI (p : ℕ) (k : ℤ) : ℕ := if (p : ℤ) < 3 * |k| then 1 else 0

/-- `μ_k = 1[o_k > 0]`. -/
def muI3 (p n : ℕ) (k : ℤ) : ℕ := if 0 < oK3 p n k then 1 else 0

/-- The node weight `w(o, hs, s)`. -/
def wnode (o hs s : ℕ) : ℤ := if o = 0 ∧ hs = 0 then (s : ℤ) ^ 2 else (s : ℤ) * (4 * o + 4 + 3 * hs)

/-! ### A general minor bound -/

/-- If `−v_p(c_{k,a}) ≤ D + (A − a) L` for every `a ≤ 3` and `λ_p(k) ≤ L`, then
`f_p(k, s) ≤ s D + A s L − L s (s − 1)`. -/
theorem fP_le_gen {n : ℕ} {k : ℤ} (D A : ℤ) (L : ℕ)
    (hc : ∀ m : ℕ, m ≤ 3 → nv p (cPoly n k m) ≤ ((D + (A - m) * L : ℤ) : WithBot ℤ))
    (hlam : lambdaP p n k ≤ L) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * D + A * s * L - L * s * (s - 1) : ℤ) : WithBot ℤ) := by
  have hc' : ∀ m : ℕ, nv p (cPoly n k m) ≤ ((D + (A - m) * L : ℤ) : WithBot ℤ) := by
    intro m
    by_cases hm : m ≤ 3
    · exact hc m hm
    · rw [cPoly_eq_zero (by omega)]; simp [nv, gaussVal, negTop]
  have hminor : ∀ Rs : Finset (Fin 4), nv p (minorR n k Rs) ≤ (((Rs.card : ℤ) * D + A * Rs.card * L
      - L * ((∑ r ∈ Rs, (r : ℕ) : ℕ) + Rs.card.choose 2 : ℕ) : ℤ) : WithBot ℤ) := by
    intro Rs
    unfold minorR
    refine (Fam3.nv_det_le_of_entry _
      (fun i => D + A * L - L * ((Rs.orderEmbOfFin rfl i : Fin 4) : ℕ))
      (fun j => -(L * (j : ℕ) : ℤ)) fun i j => ?_).trans (le_of_eq ?_)
    · simp only [Matrix.of_apply, Cmat]
      refine (hc' _).trans (le_of_eq ?_)
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
  unfold fP
  split_ifs with hs0
  · subst hs0; simp
  refine Finset.sup_le fun j _ => ?_
  set B : ℤ := (s : ℤ) * D + A * s * L - L * s * (s - 1)
  have hE : eP p n k s j ≤ ((B - (j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun Rs hRs => ?_
    simp only [mem_filter, mem_univ, true_and] at hRs
    obtain ⟨hRc, hRj⟩ := hRs
    refine (hminor Rs).trans (WithBot.coe_le_coe.2 ?_)
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
    have hlam' : ((j * lambdaP p n k : ℕ) : ℤ) ≤ j * L := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (by positivity)
    rw [hRc] at hj ⊢
    simp only [B]
    have hjL := congrArg (· * (L : ℤ)) hj
    have hchL := congrArg (· * (L : ℤ)) hch
    simp only at hjL hchL
    push_cast at hjL hlam' ⊢
    nlinarith
  calc eP p n k s j + (((j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ)
      ≤ ((B - (j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) +
          (((j * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) := add_le_add_left hE _
    _ = (B : WithBot ℤ) := by rw [← WithBot.coe_add, sub_add_cancel]

/-! ### The node data for a single-level prime -/

section Single

variable {n : ℕ} {k : ℤ}

theorem one_le_padicValInt_dvd' {x : ℤ} (h : 1 ≤ padicValInt p x) : (p : ℤ) ∣ x := by
  have := (padicValInt_dvd_iff (p := p) 1 x).2 (Or.inr h)
  simpa using this

theorem lambdaP_le_muI3 (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) :
    lambdaP p n k ≤ muI3 p n k := by
  have h1 := lambdaP_le3 (p := p) (L := 1) (by simpa using h9) hk
  rcases Nat.eq_zero_or_pos (lambdaP p n k) with h0 | h0
  · omega
  · obtain ⟨m, hm, hmax⟩ := exists_mem_eq_sup ((nodes n).erase k)
      (by by_contra hne; rw [not_nonempty_iff_eq_empty] at hne; simp [lambdaP, hne] at h0)
      (fun m => padicValInt p (k - m))
    have hv : 1 ≤ padicValInt p (k - m) := by unfold lambdaP at h0; omega
    have hpos : 0 < oK3 p n k := by
      unfold oK3 cntL3
      exact card_pos.2 ⟨m, mem_filter.2 ⟨hm, one_le_padicValInt_dvd' hv⟩⟩
    unfold muI3; rw [if_pos hpos]; omega

theorem hsMax_le_hsI (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) : hsMax3 p k ≤ hsI p k := by
  have h1 := hsMax_le3 (p := p) (L := 1) (by simpa using h9) hk
  rcases Nat.eq_zero_or_pos (hsMax3 p k) with h0 | h0
  · omega
  obtain ⟨m, hm, hmv⟩ := exists_mem_eq_sup (hsRange3 k)
    (by by_contra hne; rw [not_nonempty_iff_eq_empty] at hne; simp [hsMax3, hne] at h0)
    (fun m => padicValNat p m)
  have hv : 1 ≤ padicValNat p m := by unfold hsMax3 at h0; omega
  simp only [hsRange3, mem_filter, mem_range] at hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm.2 (dvd_zero 3)
  have hd : p ∣ m := by
    have := (padicValNat_dvd_iff_le (p := p) hm0 (n := 1)).2 hv
    simpa using this
  have hpm : p ≤ m := Nat.le_of_dvd (by omega) hd
  unfold hsI
  rw [if_pos]
  · omega
  have : (m : ℤ) < 3 * (k.natAbs : ℤ) := by exact_mod_cast hm.1
  rw [Int.abs_eq_natAbs]
  omega

theorem Dk3_single (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) :
    Dk3 p n k = 4 * (oK3 p n k : ℤ) := by
  rw [Dk3_eq_sum_levels hk, ← add_sum_erase _ _ (mem_Icc.2 ⟨le_rfl, by omega⟩), pow_one]
  have hR : 2 * R n < p ^ 2 := by unfold R; omega
  rw [sum_eq_zero fun j hj => ?_]
  · simp [oK3]
  · have hj' := mem_erase.1 hj
    have hj2 : 2 ≤ j := by have := (mem_Icc.1 hj'.2).1; omega
    have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.out.pos hj2
    rw [cntL_eq_zero_of_gt3 (by omega) hk]; simp

omit hp in
theorem oK3_eq_zero_of_muI3 (h : muI3 p n k = 0) : oK3 p n k = 0 := by
  unfold muI3 at h; split_ifs at h with h1; omega

/-- The entry bound at a node in terms of `μ_k` and `hs_k`. -/
theorem nv_cPoly_le_node (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) (A : ℤ) (L : ℕ)
    (hβ : ∀ a i : ℕ, a ≤ 3 → 1 ≤ i → i ≤ 4 - a →
      ((4 - i - a : ℕ) : ℤ) * muI3 p n k + ((i + 1 + 1 : ℕ) : ℤ) * hsI p k ≤ (A - a) * L)
    (hα : ∀ a : ℕ, a ≤ 1 → ((1 - a : ℕ) : ℤ) * muI3 p n k ≤ (A - a) * L) (m : ℕ) (hm : m ≤ 3) :
    nv p (cPoly n k m) ≤ ((Dk3 p n k + (A - m) * L : ℤ) : WithBot ℤ) := by
  have hp0 := Fam3.p_pos_q (p := p)
  have hlam := lambdaP_le_muI3 h9 hk
  have hhs := hsMax_le_hsI h9 hk
  have hβn : padicNorm p (betaC n k m) ≤ (p : ℚ) ^ (Dk3 p n k + (A - m) * L) := by
    unfold betaC
    rw [padicNorm.neg]
    refine padicNorm.sum_le' (fun i hi => ?_) (by positivity)
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    rw [padicNorm.mul, padicNorm.mul]
    have h1 : padicNorm p (i : ℚ) ≤ 1 := padicNorm.of_nat i
    have h2 : padicNorm p (Sk k (i + 1)) ≤ (p : ℚ) ^ (((i + 1 + 1 : ℕ) : ℤ) * hsI p k) :=
      (norm_Sk_le3 (p := p) k (i + 1)).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hhs) (by positivity)))
    have h3 : padicNorm p (Hk n k (4 - i - m)) ≤
        (p : ℚ) ^ (Dk3 p n k + ((4 - i - m : ℕ) : ℤ) * muI3 p n k) :=
      (norm_Hk_le3 (p := p) n k (4 - i - m)).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q (by
        have : ((4 - i - m : ℕ) : ℤ) * lambdaP p n k ≤ ((4 - i - m : ℕ) : ℤ) * muI3 p n k :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (by positivity)
        linarith))
    calc padicNorm p (i : ℚ) * padicNorm p (Hk n k (4 - i - m)) * padicNorm p (Sk k (i + 1))
        ≤ 1 * (p : ℚ) ^ (Dk3 p n k + ((4 - i - m : ℕ) : ℤ) * muI3 p n k) *
            (p : ℚ) ^ (((i + 1 + 1 : ℕ) : ℤ) * hsI p k) := by
          gcongr
          · exact padicNorm.nonneg _
          · exact padicNorm.nonneg _
      _ = (p : ℚ) ^ (Dk3 p n k + (((4 - i - m : ℕ) : ℤ) * muI3 p n k +
            ((i + 1 + 1 : ℕ) : ℤ) * hsI p k)) := by
          rw [one_mul, ← zpow_add₀ hp0.ne']; congr 1; ring
      _ ≤ (p : ℚ) ^ (Dk3 p n k + (A - m) * L) :=
          zpow_le_zpow_right₀ Fam3.one_le_p_q (by linarith [hβ m i hm hi1 hi2])
  have hαn : padicNorm p (alphaC n k m) ≤ (p : ℚ) ^ (Dk3 p n k + (A - m) * L) := by
    unfold alphaC
    split_ifs with h
    · have hc : -(3 * (4 * 3 ^ 5) : ℚ) = -((2916 : ℕ) : ℚ) := by norm_num
      rw [hc, padicNorm.mul, padicNorm.neg]
      have h1 : padicNorm p ((2916 : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
      have h3 : padicNorm p (Hk n k (1 - m)) ≤ (p : ℚ) ^ (Dk3 p n k + (A - m) * L) :=
        (norm_Hk_le3 n k _).trans (zpow_le_zpow_right₀ Fam3.one_le_p_q (by
          have : ((1 - m : ℕ) : ℤ) * lambdaP p n k ≤ ((1 - m : ℕ) : ℤ) * muI3 p n k :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hlam) (by positivity)
          linarith [hα m h]))
      calc padicNorm p ((2916 : ℕ) : ℚ) * padicNorm p (Hk n k (1 - m))
          ≤ 1 * (p : ℚ) ^ (Dk3 p n k + (A - m) * L) :=
            mul_le_mul h1 h3 (padicNorm.nonneg _) zero_le_one
        _ = _ := one_mul _
    · simp; positivity
  unfold cPoly
  rw [if_pos hm, nv_le_iff]
  intro i
  rw [coeff_add, coeff_C, coeff_C_mul_X]
  rcases i with _ | _ | i
  · simpa using Fam3.norm_le_of_padicNorm_le hβn
  · simpa using Fam3.norm_le_of_padicNorm_le hαn
  · simp; positivity

omit hp in
theorem muI3_le_one : muI3 p n k ≤ 1 := by unfold muI3; split_ifs <;> omega

omit hp in
theorem hsI_le_one : hsI p k ≤ 1 := by unfold hsI; split_ifs <;> omega

/-- **The node bound** for a single-level prime: `f_p(k, s) + s² ≤ w(o_k, hs_k, s)`. -/
theorem fP_add_sq_le_wnode (h9 : 9 * n < 2 * p ^ 2) (hk : k ∈ nodes n) (s : ℕ) :
    fP p n k s + (((s : ℤ) ^ 2 : ℤ) : WithBot ℤ) ≤ ((wnode (oK3 p n k) (hsI p k) s : ℤ) : WithBot ℤ) := by
  have hD := Dk3_single h9 hk
  have hlam := lambdaP_le_muI3 h9 hk
  have hmu1 : muI3 p n k ≤ 1 := muI3_le_one
  have hhs1 : hsI p k ≤ 1 := hsI_le_one
  -- the three cases
  have key : ∃ A : ℤ, ∃ L : ℕ, lambdaP p n k ≤ L ∧
      (∀ a i : ℕ, a ≤ 3 → 1 ≤ i → i ≤ 4 - a →
        ((4 - i - a : ℕ) : ℤ) * muI3 p n k + ((i + 1 + 1 : ℕ) : ℤ) * hsI p k ≤ (A - a) * L) ∧
      (∀ a : ℕ, a ≤ 1 → ((1 - a : ℕ) : ℤ) * muI3 p n k ≤ (A - a) * L) ∧
      (s : ℤ) * Dk3 p n k + A * s * L - L * s * (s - 1) + (s : ℤ) ^ 2 ≤
        wnode (oK3 p n k) (hsI p k) s := by
    by_cases hhs : hsI p k = 1
    · refine ⟨6, 1, by omega, fun a i ha hi1 hi2 => ?_, fun a ha => ?_, ?_⟩
      · rw [hhs]
        have : ((4 - i - a : ℕ) : ℤ) * muI3 p n k ≤ ((4 - i - a : ℕ) : ℤ) :=
          by nlinarith [(by exact_mod_cast hmu1 : (muI3 p n k : ℤ) ≤ 1)]
        push_cast [Nat.cast_sub (show a ≤ 4 - i by omega), Nat.cast_sub (show i ≤ 4 by omega)]
          at this ⊢
        linarith
      · have : ((1 - a : ℕ) : ℤ) * muI3 p n k ≤ ((1 - a : ℕ) : ℤ) :=
          by nlinarith [(by exact_mod_cast hmu1 : (muI3 p n k : ℤ) ≤ 1)]
        push_cast [Nat.cast_sub ha] at this ⊢
        linarith
      · unfold wnode
        rw [if_neg (by omega), hD, hhs]
        push_cast; ring_nf; nlinarith
    · have hhs0 : hsI p k = 0 := by omega
      by_cases hmu : muI3 p n k = 1
      · refine ⟨3, 1, by omega, fun a i ha hi1 hi2 => ?_, fun a ha => ?_, ?_⟩
        · rw [hhs0, hmu]
          push_cast [Nat.cast_sub (show a ≤ 4 - i by omega), Nat.cast_sub (show i ≤ 4 by omega)]
          linarith
        · rw [hmu]; push_cast [Nat.cast_sub ha]; linarith
        · have ho : oK3 p n k ≠ 0 := by
            intro h0; unfold muI3 at hmu; rw [if_neg (by omega)] at hmu; omega
          unfold wnode
          rw [if_neg (by omega), hD, hhs0]
          push_cast; ring_nf; nlinarith
      · have hmu0 : muI3 p n k = 0 := by omega
        have ho := oK3_eq_zero_of_muI3 hmu0
        refine ⟨0, 0, by omega, fun a i ha hi1 hi2 => ?_, fun a ha => ?_, ?_⟩
        · rw [hhs0, hmu0]; simp
        · rw [hmu0]; simp
        · unfold wnode
          rw [if_pos ⟨ho, hhs0⟩, hD, ho]
          simp
  obtain ⟨A, L, hL, hβ, hα, hw⟩ := key
  have hf := fP_le_gen (p := p) (n := n) (k := k) (Dk3 p n k) A L
    (nv_cPoly_le_node h9 hk A L hβ hα) hL s
  calc fP p n k s + (((s : ℤ) ^ 2 : ℤ) : WithBot ℤ)
      ≤ (((s : ℤ) * Dk3 p n k + A * s * L - L * s * (s - 1) : ℤ) : WithBot ℤ) +
          (((s : ℤ) ^ 2 : ℤ) : WithBot ℤ) := add_le_add_left hf _
    _ ≤ _ := by rw [← WithBot.coe_add, WithBot.coe_le_coe]; exact hw

end Single

end Zeta35.Den
