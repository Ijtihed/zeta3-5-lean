import RequestProject.Zeta35.DenCount

/-!
# Denominators (N, Theorem 5.1), step 7: the class sum for a prime `ℓ ∈ (n/20, 9n/2]`

**`sum_psi_le`**: for an odd prime `ℓ` with `2ℓ ≤ 9n`, `n` even, `q` with `qℓ ≤ 3n ≤ (q + 1)ℓ`,
a branch `br` valid at `u = ℓ/n`, and `λ ≥ 0`,

  `∑_{c mod ℓ} ψ(N_c, b_c, λ) ≤ ∑_{i < 4} (n · meas_i(u) + 2) ψ(N_i, b_i, λ) + ψ(q + 2, 0, λ)`.
-/

open Finset

namespace Zeta35.Den

/-- The class of `t` (as a residue `c = t mod ℓ`) has at most `q + [cN(|t|)] + [t = 0 ∧ q odd ∧
w = ℓ]` nodes. -/
theorem clsF_card_le {ℓ n q H : ℕ} (hℓ : ℓ = 2 * H + 1) (hn : Even n)
    (hq1 : q * ℓ ≤ 3 * n) (hq2 : 3 * n ≤ (q + 1) * ℓ) {t : ℤ} (ht1 : -(H : ℤ) ≤ t)
    (ht2 : t ≤ H) :
    ((clsF ℓ n ((t % (ℓ : ℤ)).toNat)).card : ℤ) ≤
      q + (if cNP q ℓ ((R n : ℤ) - (q / 2 : ℕ) * ℓ) |t| then 1 else 0) +
        (if t = 0 ∧ q % 2 = 1 ∧ (R n : ℤ) - (q / 2 : ℕ) * ℓ = ℓ then 1 else 0) := by
  set e : ℕ := q / 2 with he
  set w : ℤ := (R n : ℤ) - e * ℓ with hw
  have hR : 2 * R n = 3 * n := R_of_even hn
  have hR' : 2 * (R n : ℤ) = 3 * n := by exact_mod_cast hR
  have hq1' : (q : ℤ) * ℓ ≤ 3 * n := by exact_mod_cast hq1
  have hq2' : 3 * (n : ℤ) ≤ q * ℓ + ℓ := by
    have : ((3 * n : ℕ) : ℤ) ≤ (((q + 1) * ℓ : ℕ) : ℤ) := by exact_mod_cast hq2
    push_cast at this; linarith
  have hℓ' : (ℓ : ℤ) = 2 * H + 1 := by exact_mod_cast hℓ
  have hQ : (q : ℤ) * ℓ = 2 * ((e : ℤ) * ℓ) + (if q % 2 = 0 then 0 else (ℓ : ℤ)) := by
    rcases Nat.mod_two_eq_zero_or_one q with hq | hq
    · rw [if_pos hq]; have : (q : ℤ) = 2 * e := by omega
      rw [this]; ring
    · rw [if_neg (by omega)]; have : (q : ℤ) = 2 * e + 1 := by omega
      rw [this]; ring
  have hw0 : 0 ≤ w := by split_ifs at hQ <;> omega
  have hwl : w ≤ ℓ := by split_ifs at hQ <;> omega
  have hcard : ((clsF ℓ n ((t % (ℓ : ℤ)).toNat)).card : ℤ) =
      ((#{m ∈ Icc (-(R n : ℤ)) (R n) | m % (ℓ : ℤ) = t % ℓ} : ℕ) : ℤ) := by
    rw [card_clsF]
    unfold clsN3 nodes
    have hc : (((t % (ℓ : ℤ)).toNat : ℕ) : ℤ) = t % ℓ :=
      Int.toNat_of_nonneg (Int.emod_nonneg t (by omega))
    rw [hc]
  rw [hcard]
  have h := card_class_le (ℓ := ℓ) (H := H) (R := R n) (e := e) (w := w) (t := t) hℓ'
    (by positivity) (by positivity) (by rw [hw]; ring) hw0 hwl ht1 ht2
  have habs : |t| = max t (-t) := abs_eq_max_neg
  unfold cNP
  split_ifs at hQ h ⊢ <;> omega

/-- A node `t` with `3|t| ≤ ℓ` makes its class `hs`-free-occupied: `b_c = 1`. -/
theorem bC_eq_one {ℓ n : ℕ} [Fact ℓ.Prime] (hn : Even n) (h9 : 2 * ℓ ≤ 9 * n) {t : ℤ}
    (ht : 3 * |t| ≤ ℓ) : bC ℓ n ((t % (ℓ : ℤ)).toNat) = 1 := by
  have hR : 2 * R n = 3 * n := R_of_even hn
  have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
  have habs : |t| = max t (-t) := abs_eq_max_neg
  have htR : -(R n : ℤ) ≤ t ∧ t ≤ R n := by
    have : (2 * ℓ : ℤ) ≤ 9 * n := by exact_mod_cast h9
    have : 2 * (R n : ℤ) = 3 * n := by exact_mod_cast hR
    omega
  refine le_antisymm (bC_le_one n _) ?_
  set i : Fin (2 * R n + 1) := ⟨(t + R n).toNat, by omega⟩
  have hi : nodeOf n i = t := by simp only [nodeOf, i]; omega
  unfold bC
  refine card_pos.2 ⟨i, mem_filter.2 ⟨?_, by rw [hi]; exact ht⟩⟩
  unfold clsF
  rw [mem_filter, hi]
  refine ⟨mem_univ _, ?_⟩
  exact (Int.toNat_of_nonneg (Int.emod_nonneg t hℓ0.ne')).symm

/-- The type selector: `∑_i [type(t) = i] ψ_i = ψ(q + [cN], [cB])`. -/
theorem sum_typ_eq (q : ℕ) (ℓ w a : ℤ) (lam : ℝ) :
    ∑ i : Fin 4, (if typP q ℓ w i a then psiT (typN q i) (typB i) lam else 0) =
      psiT (q + if cNP q ℓ w a then 1 else 0) (if 3 * a ≤ ℓ then 1 else 0) lam := by
  rw [Fin.sum_univ_four]
  by_cases h1 : cNP q ℓ w a <;> by_cases h2 : 3 * a ≤ ℓ <;>
    simp [typP, typN, typB, h1, h2]

/-- **The class sum for a prime `ℓ ∈ (n/20, 9n/2]`**. -/
theorem sum_psi_le {ℓ n q : ℕ} [hℓp : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hn : Even n) (hn0 : 0 < n)
    (hq1 : q * ℓ ≤ 3 * n) (hq2 : 3 * n ≤ (q + 1) * ℓ) (h9 : 2 * ℓ ≤ 9 * n) (br : Bool)
    (hbr1 : br = true → 0 ≤ sgnF q ((ℓ : ℝ) / n)) (hbr2 : br = false → sgnF q ((ℓ : ℝ) / n) ≤ 0)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑ c ∈ range ℓ, psiT (clsF ℓ n c).card (bC ℓ n c) lam ≤
      ∑ i : Fin 4, ((n : ℝ) * measF q br ((ℓ : ℝ) / n) i + 2) * psiT (typN q i) (typB i) lam
        + psiT (q + 2) 0 lam := by
  obtain ⟨H, hℓ⟩ : ∃ H, ℓ = 2 * H + 1 := by
    rcases hℓp.out.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact h
  set e : ℕ := q / 2 with he
  set w : ℤ := (R n : ℤ) - e * ℓ with hw
  rw [← sum_range_eq_window hℓ (fun c => psiT (clsF ℓ n c).card (bC ℓ n c) lam)]
  -- the per-class bound
  have hper : ∀ t ∈ Icc (-(H : ℤ)) H,
      psiT (clsF ℓ n ((t % (ℓ : ℤ)).toNat)).card (bC ℓ n ((t % (ℓ : ℤ)).toNat)) lam ≤
        (∑ i : Fin 4, (if typP q ℓ w i |t| then psiT (typN q i) (typB i) lam else 0)) +
          (if t = 0 then psiT (q + 2) 0 lam else 0) := by
    intro t ht
    rw [mem_Icc] at ht
    rw [sum_typ_eq]
    set N := (clsF ℓ n ((t % (ℓ : ℤ)).toNat)).card
    set b := bC ℓ n ((t % (ℓ : ℤ)).toNat)
    have hb1 : b ≤ 1 := bC_le_one n _
    have hN := clsF_card_le hℓ hn hq1 hq2 ht.1 ht.2
    have hψ0 := psiT_nonneg (q + 2) 0 lam
    have hψb : psiT N b lam ≤ psiT N 0 lam := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb1 with h | h
      · rw [h]
      · rw [h]; exact psiT_anti_b N lam
    by_cases hedge : t = 0 ∧ q % 2 = 1 ∧ (R n : ℤ) - (q / 2 : ℕ) * ℓ = ℓ
    · rw [if_pos hedge.1]
      have hN2 : N ≤ q + 2 := by
        have : (N : ℤ) ≤ q + 2 := by split_ifs at hN <;> omega
        omega
      have := psiT_mono_N (b := 0) hN2 (by norm_num) hlam
      have h0 := psiT_nonneg (q + if cNP q ℓ w |t| then 1 else 0)
        (if 3 * |t| ≤ (ℓ : ℤ) then 1 else 0) lam
      linarith
    · rw [if_neg hedge] at hN
      have hN' : N ≤ q + if cNP q ℓ w |t| then 1 else 0 := by
        have : (N : ℤ) ≤ q + (if cNP q ℓ w |t| then 1 else 0 : ℕ) := by
          split_ifs at hN ⊢ <;> push_cast <;> omega
        exact_mod_cast this
      have hextra : 0 ≤ (if t = 0 then psiT (q + 2) 0 lam else 0) := by split_ifs <;> simp [hψ0]
      have hmono := psiT_mono_N (b := b) hN' hb1 hlam
      by_cases hB : 3 * |t| ≤ (ℓ : ℤ)
      · rw [if_pos hB]
        have : b = 1 := bC_eq_one hn h9 hB
        rw [this] at hmono ⊢
        linarith
      · rw [if_neg hB]
        have := psiT_mono_N (b := 0) hN' (by norm_num) hlam
        linarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_comm, sum_ite_eq' (Icc (-(H : ℤ)) H) 0]
  rw [if_pos (by simp)]
  refine add_le_add (sum_le_sum fun i _ => ?_) le_rfl
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (psiT_nonneg _ _ _)
  -- the count bound
  have hS := sgnF_mul q (ℓ := ℓ) hn0
  have hcb := count_bound (n := n) (ℓ := ℓ) (H := H) (q := q) (e := e) (w := w) br hℓ hn rfl rfl
    hq1 hq2 (fun h => by
      have := hbr1 h
      have h3 : 0 ≤ 3 * (n : ℝ) * sgnF q ((ℓ : ℝ) / n) := by positivity
      rw [hS] at h3
      split_ifs at h3 ⊢ <;> exact_mod_cast h3)
    (fun h => by
      have := hbr2 h
      have h3 : 3 * (n : ℝ) * sgnF q ((ℓ : ℝ) / n) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) this
      rw [hS] at h3
      split_ifs at h3 ⊢ <;> exact_mod_cast h3) i
  rw [measF_eq_Mint q br hn0 i]
  have : (3 : ℝ) * ((#{t ∈ Icc (-(H : ℤ)) H | typP q ℓ w i |t|} : ℕ) : ℝ) ≤
      (Mint q br n ℓ i : ℝ) + 6 := by exact_mod_cast hcb
  linarith

end Zeta35.Den
