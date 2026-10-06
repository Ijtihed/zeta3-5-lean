import RequestProject.Zeta7.Hankel2.Taylor72

/-!
# Paper Lemma 8.2: the leaf lemma (unclipped `e_p`)

For every odd prime `p`, every node `k ∈ [−n, 2n]` and every `1 ≤ s ≤ 4`:

  `f_p(k, s) ≤ s D_k + 12 s L_p`                                   (`leaf_lemma`).

The proof (paper §8.1) goes through the entry bound `v_p(c_{k,a}) ≥ −D_k − (8−a) L`
(`nv_cPoly_le`, from Lemma 7.2), the expansion of the minors `det C_k[R, {0..s−1}]` into products of
entries, and `ℓ λ_p(k) ≤ ℓ L`.  We prove the slightly sharper form

  `f_p(k, s) ≤ s D_k + 8 s L − L s (s−1)`                         (`fP_le_sharp`)

for every `L` with `4n < p^{L+1}` (i.e. all the valuations of Lemma 7.2 are `≤ L`); it gives the leaf
lemma with `L = L_p`, and with `L = 1` the bound `f_p(k,s) + s² ≤ s D_k + 9 s` used for the
single-level primes `p² > 6n` (`fP_le_single`).
-/

open Finset Polynomial

namespace Hankel2.Fam3

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_le_of_padicNorm_le {q : ℚ} {T : ℤ} (h : padicNorm p q ≤ (p : ℚ) ^ T) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ T := by
  rw [Padic.eq_padicNorm]
  have := (Rat.cast_le (K := ℝ)).2 h
  simpa [Rat.cast_zpow] using this

/-! ### The entries `c_{k,a}` -/

section Entries

variable {n L : ℕ} {k : ℤ}

theorem padicNorm_natCast_le_one (m : ℕ) : padicNorm p (m : ℚ) ≤ 1 := padicNorm.of_nat m

theorem padicNorm_betaC_le (hp2 : p ≠ 2) (hL : 4 * n < p ^ (L + 1)) (hk : k ∈ Fam3PF.nodes n)
    {m : ℕ} (hm : m ≤ 3) :
    padicNorm p (betaC n k m) ≤ (p : ℚ) ^ (Dk p n k + (8 - (m : ℤ)) * L) := by
  unfold betaC
  refine padicNorm.sum_le' (fun i hi => ?_) (by have := p_pos_q (p := p); positivity)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  have hc : phi i * ((i : ℚ) + 3) = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
    simp only [phi]; push_cast; ring
  rw [padicNorm.mul, padicNorm.mul, hc]
  have h1 := padicNorm_natCast_le_one (p := p) (i * (i + 1) * (i + 2) * (i + 3))
  have h2 : padicNorm p (HS k (i + 4)) ≤ (p : ℚ) ^ (((i + 4 : ℕ) : ℤ) * L) :=
    (norm_HS_le hp2 k (i + 4)).trans (zpow_le_zpow_right₀ one_le_p_q
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hsMax_le (p := p) hL hk) (by positivity)))
  have h3 : padicNorm p (Hk n k (4 - i - m)) ≤ (p : ℚ) ^ (Dk p n k + ((4 - i - m : ℕ) : ℤ) * L) :=
    (norm_Hk_le hp2 n k _).trans (zpow_le_zpow_right₀ one_le_p_q (by
      have := muK_le (p := p) hL hk
      have : ((4 - i - m : ℕ) : ℤ) * muK p n k ≤ ((4 - i - m : ℕ) : ℤ) * L :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
      linarith))
  have hp0 := p_pos_q (p := p)
  calc padicNorm p ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) * padicNorm p (HS k (i + 4)) *
        padicNorm p (Hk n k (4 - i - m))
      ≤ 1 * (p : ℚ) ^ (((i + 4 : ℕ) : ℤ) * L) * (p : ℚ) ^ (Dk p n k + ((4 - i - m : ℕ) : ℤ) * L) := by
        gcongr
        · exact padicNorm.nonneg _
        · exact padicNorm.nonneg _
    _ = (p : ℚ) ^ (Dk p n k + (8 - (m : ℤ)) * L) := by
        rw [one_mul, ← zpow_add₀ hp0.ne']
        congr 1
        have : i + m ≤ 4 := by omega
        rw [show (4 - i - m : ℕ) = 4 - (i + m) by omega]
        push_cast [Nat.cast_sub this]
        ring

theorem padicNorm_alphaC_le (hp2 : p ≠ 2) (hL : 4 * n < p ^ (L + 1)) (hk : k ∈ Fam3PF.nodes n)
    {m : ℕ} (hm : m ≤ 3) :
    padicNorm p (alphaC n k m) ≤ (p : ℚ) ^ (Dk p n k + (8 - (m : ℤ)) * L) := by
  have hp0 := p_pos_q (p := p)
  unfold alphaC
  split_ifs with h
  · have hc : -(phi 3) * 6 * 2 ^ 7 = -((46080 : ℕ) : ℚ) := by norm_num [phi]
    rw [hc, padicNorm.mul, padicNorm.neg]
    have h1 := padicNorm_natCast_le_one (p := p) 46080
    have h3 : padicNorm p (Hk n k (1 - m)) ≤ (p : ℚ) ^ (Dk p n k + (8 - (m : ℤ)) * L) :=
      (norm_Hk_le hp2 n k _).trans (zpow_le_zpow_right₀ one_le_p_q (by
        have := muK_le (p := p) hL hk
        have : ((1 - m : ℕ) : ℤ) * muK p n k ≤ ((1 - m : ℕ) : ℤ) * L :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
        have h8 : ((1 - m : ℕ) : ℤ) * L ≤ (8 - (m : ℤ)) * L :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        linarith))
    calc padicNorm p ((46080 : ℕ) : ℚ) * padicNorm p (Hk n k (1 - m))
        ≤ 1 * (p : ℚ) ^ (Dk p n k + (8 - (m : ℤ)) * L) :=
          mul_le_mul h1 h3 (padicNorm.nonneg _) zero_le_one
      _ = _ := one_mul _
  · simp; positivity

/-- **The entry bound** (paper §8.1): `v_p(c_{k,a}) ≥ −D_k − (8−a) L` for every `a`
(`c_{k,a} = 0` for `a > 3`). -/
theorem nv_cPoly_le (hp2 : p ≠ 2) (hL : 4 * n < p ^ (L + 1)) (hk : k ∈ Fam3PF.nodes n) (m : ℕ) :
    nv p (cPoly n k m) ≤ ((Dk p n k + (8 - (m : ℤ)) * L : ℤ) : WithBot ℤ) := by
  unfold cPoly
  split_ifs with hm
  · rw [nv_le_iff]
    intro i
    rw [coeff_add, coeff_C, coeff_C_mul_X]
    rcases i with _ | _ | i
    · simpa using norm_le_of_padicNorm_le (padicNorm_betaC_le hp2 hL hk hm)
    · simpa using norm_le_of_padicNorm_le (padicNorm_alphaC_le hp2 hL hk hm)
    · simp; positivity
  · simp

end Entries

/-! ### Determinants with additively separated entry bounds -/

theorem nv_det_le_of_entry {s : ℕ} (M : Matrix (Fin s) (Fin s) ℚ[X]) (a b : Fin s → ℤ)
    (h : ∀ i j, nv p (M i j) ≤ ((a i + b j : ℤ) : WithBot ℤ)) :
    nv p M.det ≤ ((∑ i, a i + ∑ j, b j : ℤ) : WithBot ℤ) := by
  rw [Matrix.det_apply]
  refine (nv_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hsign : nv p (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = nv p (∏ i, M (σ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1, nv_neg]
  rw [hsign]
  refine (nv_prod_le _ _).trans ?_
  calc ∑ i, nv p (M (σ i) i) ≤ ∑ i, (((a (σ i) + b i : ℤ)) : WithBot ℤ) :=
        sum_le_sum fun i _ => h _ _
    _ = ((∑ i, a i + ∑ j, b j : ℤ) : WithBot ℤ) := by
        rw [← WithBot.coe_sum, sum_add_distrib, Equiv.sum_comp σ a]

/-! ### Row sets -/

theorem sum_orderEmbOfFin (R : Finset (Fin 4)) :
    ∑ i : Fin R.card, ((R.orderEmbOfFin rfl i : Fin 4) : ℕ) = ∑ r ∈ R, (r : ℕ) := by
  conv_rhs => rw [← R.map_orderEmbOfFin_univ rfl]
  rw [Finset.sum_map]
  rfl

theorem sum_fin_val (s : ℕ) : ∑ i : Fin s, (i : ℕ) = s.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) s, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_le_sum (R : Finset (Fin 4)) : R.card.choose 2 ≤ ∑ r ∈ R, (r : ℕ) := by
  revert R; decide

theorem card_le_four (R : Finset (Fin 4)) : R.card ≤ 4 := by
  simpa using R.card_le_univ

/-! ### The minors and the leaf lemma -/

section Leaf

variable {n L : ℕ} {k : ℤ}

/-- `−v_p(det C_k[R, {0..s−1}]) ≤ s D_k + 8 s L − L (∑R + C(s,2))`. -/
theorem nv_minorR_le (hp2 : p ≠ 2) (hL : 4 * n < p ^ (L + 1)) (hk : k ∈ Fam3PF.nodes n)
    (R : Finset (Fin 4)) :
    nv p (minorR n k R) ≤ (((R.card : ℤ) * Dk p n k + 8 * R.card * L
      - L * ((∑ r ∈ R, (r : ℕ) : ℕ) + R.card.choose 2 : ℕ) : ℤ) : WithBot ℤ) := by
  unfold minorR
  refine (nv_det_le_of_entry _
    (fun i => Dk p n k + 8 * L - L * ((R.orderEmbOfFin rfl i : Fin 4) : ℕ))
    (fun j => -(L * (j : ℕ) : ℤ)) fun i j => ?_).trans (le_of_eq ?_)
  · simp only [Matrix.of_apply, Cmat]
    refine (nv_cPoly_le hp2 hL hk _).trans (le_of_eq ?_)
    congr 1
    simp only [Fin.val_castLE]
    push_cast; ring
  · congr 1
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, ← mul_sum, sum_neg_distrib,
      ← mul_sum]
    have h1 : ∑ i : Fin R.card, (((R.orderEmbOfFin rfl i : Fin 4) : ℕ) : ℤ) = ∑ r ∈ R, (r : ℕ) := by
      exact_mod_cast sum_orderEmbOfFin R
    have h2 : ∑ i : Fin R.card, ((i : ℕ) : ℤ) = R.card.choose 2 := by
      exact_mod_cast sum_fin_val R.card
    rw [h1, h2]
    push_cast; ring

/-- **Sharp leaf bound.** If `4n < p^{L+1}` then `f_p(k, s) ≤ s D_k + 8 s L − L s (s−1)` for every
`s` and every node `k` (odd `p`). -/
theorem fP_le_sharp (hp2 : p ≠ 2) (hL : 4 * n < p ^ (L + 1)) (hk : k ∈ Fam3PF.nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk p n k + 8 * s * L - L * s * (s - 1) : ℤ) : WithBot ℤ) := by
  unfold fP
  split_ifs with hs0
  · subst hs0; simp
  refine Finset.sup_le fun ℓ _ => ?_
  have hlamL : lambdaP p n k ≤ L := lambdaP_le hL hk
  set B : ℤ := (s : ℤ) * Dk p n k + 8 * s * L - L * s * (s - 1)
  have hE : eP p n k s ℓ ≤ ((B - (ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun R hR => ?_
    simp only [mem_filter, mem_univ, true_and] at hR
    obtain ⟨hRc, hRℓ⟩ := hR
    refine (nv_minorR_le hp2 hL hk R).trans (WithBot.coe_le_coe.2 ?_)
    have hc := choose_le_sum R
    have hℓ : (ℓ : ℤ) = (∑ r ∈ R, (r : ℕ) : ℕ) - R.card.choose 2 := by
      rw [← hRℓ, ellR]; push_cast [Nat.cast_sub hc]; ring
    have hch : ((s.choose 2 : ℕ) : ℤ) * 2 = s * (s - 1) := by
      have h2 : s.choose 2 * 2 = s * (s - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
      have h3 : ((s.choose 2 * 2 : ℕ) : ℤ) = ((s * (s - 1) : ℕ) : ℤ) := by rw [h2]
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at h3
      exact h3
    have hlam : ((ℓ * lambdaP p n k : ℕ) : ℤ) ≤ ℓ * L := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlamL) (by positivity)
    rw [hRc] at hℓ ⊢
    simp only [B]
    have hℓL := congrArg (· * (L : ℤ)) hℓ
    have hchL := congrArg (· * (L : ℤ)) hch
    simp only at hℓL hchL
    push_cast at hℓL hlam ⊢
    nlinarith
  calc eP p n k s ℓ + (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ)
      ≤ ((B - (ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) + (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) :=
        add_le_add_left hE _
    _ = (B : WithBot ℤ) := by rw [← WithBot.coe_add, sub_add_cancel]

/-- **Lemma 8.2 (leaf lemma, unclipped).** For every odd prime `p`, every node `k` and every
`1 ≤ s ≤ 4`: `f_p(k, s) ≤ s D_k + 12 s L_p`.  (The bound holds for every `s`.) -/
theorem leaf_lemma (hp2 : p ≠ 2) (hk : k ∈ Fam3PF.nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk p n k + 12 * s * Lp p n : ℤ) : WithBot ℤ) := by
  refine (fP_le_sharp hp2 (four_n_lt_pow_Lp n) hk s).trans (WithBot.coe_le_coe.2 ?_)
  have h1 : (0 : ℤ) ≤ (Lp p n : ℤ) * s * (s - 1) := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp
    · have : (0 : ℤ) ≤ (s : ℤ) - 1 := by omega
      positivity
  have h2 : (0 : ℤ) ≤ (s : ℤ) * Lp p n := by positivity
  linarith

/-- **Single-level leaf bound.** If `p² > 6n` then `f_p(k, s) ≤ s D_k + 8 s − s (s−1)`, i.e.
`f_p(k,s) + s² ≤ s (D_k + 9)`. -/
theorem fP_le_single (hp2 : p ≠ 2) (h6 : 6 * n < p ^ 2) (hk : k ∈ Fam3PF.nodes n) (s : ℕ) :
    fP p n k s ≤ (((s : ℤ) * Dk p n k + 8 * s - s * (s - 1) : ℤ) : WithBot ℤ) := by
  have := fP_le_sharp hp2 (four_n_lt_pow_one h6) hk s
  simpa using this

end Leaf

end Hankel2.Fam3
