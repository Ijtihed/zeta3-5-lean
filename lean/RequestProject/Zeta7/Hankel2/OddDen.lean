import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# The product-formula criterion with odd denominators (paper Lemma 3.1)

For `Δ ∈ ℚ[X]` of degree `≤ K` and a rational `r` with `Δ(r) ≠ 0`, clearing denominators gives an
integer polynomial `Q = D₀ Δ`, `D₀ = 2^{e} d` with `d` odd, and the criterion
`Hankel2.one_le_length_mul_norm` becomes

  `1 ≤ d · ‖Δ‖₁ · max(|num r|, den r)^K · ‖Δ(r)‖₂`,

where `d = ∏_{q odd} q^{E_q}` and `E_q = max_j v_q(den Δ_j) = max(−v_q(Δ), 0)` is the exponent
of `q` in the denominator of `Δ` (`Hankel2.odd_den_criterion`).  The power of `2` cancels
exactly, as in the paper.
-/

open Polynomial Finset

namespace Hankel2

/-- `v_q(lcm_i f_i) ≤ m` if every `v_q(f_i) ≤ m`. -/
theorem lcm_factorization_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) (q m : ℕ)
    (h : ∀ i ∈ s, (f i).factorization q ≤ m) : (s.lcm f).factorization q ≤ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.lcm_insert]
    have h0 : s.lcm f ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; push_neg
      exact fun i hi => hf i (mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := hf a (mem_insert_self a s)
    change (Nat.lcm (f a) (s.lcm f)).factorization q ≤ m
    rw [Nat.factorization_lcm ha0 h0, Finsupp.sup_apply]
    exact sup_le (h a (mem_insert_self a s))
      (ih (fun i hi => hf i (mem_insert_of_mem hi)) (fun i hi => h i (mem_insert_of_mem hi)))

/-- If `v_q(c) ≥ g` then `v_q(den c) ≤ max(−g, 0)`. -/
theorem den_factorization_le (c : ℚ) (q : ℕ) [hq : Fact q.Prime] (g : ℤ)
    (hg : g ≤ padicValRat q c) : ((c.den.factorization q : ℕ) : ℤ) ≤ max (-g) 0 := by
  rw [Nat.factorization_def _ hq.out]
  by_cases h0 : padicValNat q c.den = 0
  · rw [h0]; simp
  · have hdvd : q ∣ c.den := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 h0)
    have hnum : ¬ (q : ℤ) ∣ c.num := by
      intro hn
      have h1 : q ∣ c.num.natAbs := Int.natCast_dvd.1 hn
      exact hq.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes c.reduced h1 hdvd)
    have hv : padicValInt q c.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have : padicValRat q c = -(padicValNat q c.den : ℤ) := by
      rw [padicValRat, hv]; ring
    rw [this] at hg
    exact le_max_of_le_left (by omega)

/-- Norm factor: `D · ‖D‖₂ = odd part of D`. -/
theorem mul_norm_two_eq_ordCompl (D : ℕ) (hD : D ≠ 0) :
    (D : ℝ) * ‖(D : ℚ_[2])‖ = (ordCompl[2] D : ℕ) := by
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self D 2
  have hodd : ‖((ordCompl[2] D : ℕ) : ℚ_[2])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_ordCompl Nat.prime_two hD)
  set v := D.factorization 2
  set d := ordCompl[2] D
  have h2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
    have := Padic.norm_p (p := 2); push_cast at this; rw [this]; norm_num
  conv_lhs => rw [← hsplit]
  push_cast
  rw [norm_mul, norm_pow, h2, hodd]
  have : (2 : ℝ) ^ v * (1 / 2) ^ v = 1 := by rw [← mul_pow]; norm_num
  calc (2 : ℝ) ^ v * d * ((1 / 2) ^ v * 1) = ((2 : ℝ) ^ v * (1 / 2) ^ v) * d := by ring
    _ = d := by rw [this, one_mul]

/-- Clearing denominators by `D`. -/
theorem exists_int_poly (Δ : ℚ[X]) (D : ℕ) (hD : ∀ i, (Δ.coeff i).den ∣ D) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (D : ℚ) * Δ := by
  have : C (D : ℚ) * Δ ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [coeff_C_mul]
    obtain ⟨k, hk⟩ := hD i
    refine ⟨(Δ.coeff i).num * k, ?_⟩
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
    rw [hk]
    push_cast
    have := Rat.mul_den_eq_num (Δ.coeff i)
    linear_combination (-(k : ℚ)) * this
  obtain ⟨Q, hQ⟩ := this
  exact ⟨Q, hQ⟩

/-- `‖F‖₁` over any range containing the degree. -/
theorem l1_eq_sum_range (F : ℚ[X]) {K : ℕ} (hK : F.natDegree ≤ K) :
    l1 F = ∑ i ∈ range (K + 1), |((F.coeff i : ℚ) : ℝ)| := by
  rw [l1]
  refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
  · simp only [mem_range] at hi ⊢
    omega
  · simp only [mem_range, not_lt] at hi
    rw [F.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

/-- **Lemma 3.1** (the criterion with the odd-denominator ledger). -/
theorem odd_den_criterion (Δ : ℚ[X]) {K : ℕ} (hK : Δ.natDegree ≤ K) (r : ℚ)
    (hne : aeval (r : ℚ_[2]) Δ ≠ 0) :
    ∃ (S : Finset ℕ) (E : ℕ → ℕ),
      (∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ ∀ g : ℤ, gaussVal q Δ = g → (E q : ℤ) ≤ max (-g) 0) ∧
      1 ≤ (∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K * ‖aeval (r : ℚ_[2]) Δ‖ := by
  set D : ℕ := (range (K + 1)).lcm (fun i => (Δ.coeff i).den) with hD_def
  have hD0 : D ≠ 0 := by
    rw [hD_def, Ne, Finset.lcm_eq_zero_iff]; push_neg; exact fun i _ => (Δ.coeff i).den_nz
  have hdvd : ∀ i, (Δ.coeff i).den ∣ D := by
    intro i
    by_cases hi : i ∈ range (K + 1)
    · exact Finset.dvd_lcm hi
    · rw [Δ.coeff_eq_zero_of_natDegree_lt (by simp at hi; omega)]; simp
  obtain ⟨Q, hQ⟩ := exists_int_poly Δ D hdvd
  have hQc : ∀ i, ((Q.coeff i : ℤ) : ℚ) = D * Δ.coeff i := by
    intro i
    have := congrArg (fun P => P.coeff i) hQ
    simpa [coeff_map, coeff_C_mul] using this
  have hQdeg : Q.natDegree ≤ K := by
    have h1 : Q.natDegree = (C (D : ℚ) * Δ).natDegree := by
      rw [← hQ, natDegree_map_eq_of_injective (RingHom.injective_int _)]
    rw [h1]; exact (natDegree_C_mul_le _ _).trans hK
  have hQr : aeval (r : ℚ_[2]) Q = (D : ℚ_[2]) * aeval (r : ℚ_[2]) Δ := by
    have : aeval (r : ℚ_[2]) Q = aeval (r : ℚ_[2]) (Q.map (algebraMap ℤ ℚ)) := by
      rw [aeval_map_algebraMap]
    rw [this, show algebraMap ℤ ℚ = Int.castRingHom ℚ from rfl, hQ]; simp
  have hQne : aeval (r : ℚ_[2]) Q ≠ 0 := by
    rw [hQr]; exact mul_ne_zero (by exact_mod_cast hD0) hne
  have hcrit := one_le_length_mul_norm 2 Q hQdeg r hQne
  have hlen : (plength Q : ℝ) = D * l1 Δ := by
    rw [plength_eq_sum_range Q hQdeg, l1_eq_sum_range Δ hK]; push_cast; rw [mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((Q.coeff i : ℤ) : ℝ) = (D : ℝ) * ((Δ.coeff i : ℚ) : ℝ) := by
      have := congrArg (fun x : ℚ => (x : ℝ)) (hQc i); push_cast at this; exact this
    rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  set d := ordCompl[2] D with hd_def
  have hd0 : d ≠ 0 := (Nat.ordCompl_pos 2 hD0).ne'
  refine ⟨d.primeFactors, d.factorization, ?_, ?_⟩
  · intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact Nat.not_dvd_ordCompl Nat.prime_two hD0 (Nat.dvd_of_mem_primeFactors hq)
    refine ⟨hqp, hq2, fun g hg => ?_⟩
    haveI := Fact.mk hqp
    have hE : d.factorization q = D.factorization q := by
      rw [hd_def, Nat.factorization_ordCompl, Finsupp.erase_ne hq2]
    rw [hE]
    have key : ∀ i ∈ range (K + 1), ((Δ.coeff i).den.factorization q : ℤ) ≤ max (-g) 0 := by
      intro i _
      by_cases hc : Δ.coeff i = 0
      · rw [hc]; simp
      · apply den_factorization_le _ q g
        have : gaussVal q Δ ≤ ((padicValRat q (Δ.coeff i) : ℤ) : WithTop ℤ) :=
          Finset.inf_le (mem_support_iff.2 hc)
        rw [hg] at this; exact_mod_cast this
    have hl : D.factorization q ≤ (max (-g) 0).toNat :=
      lcm_factorization_le (range (K + 1)) (fun i => (Δ.coeff i).den)
        (fun i _ => (Δ.coeff i).den_nz) q (max (-g) 0).toNat
        (fun i hi => by have := key i hi; simp only; omega)
    omega
  · have hprod : (∏ q ∈ d.primeFactors, (q : ℝ) ^ d.factorization q) = d := by
      rw [← Nat.support_factorization]
      exact_mod_cast Nat.factorization_prod_pow_eq_self hd0
    rw [hprod, ← mul_norm_two_eq_ordCompl D hD0]
    rw [hlen, hQr, norm_mul] at hcrit
    calc (1 : ℝ) ≤ _ := hcrit
      _ = _ := by ring

end Hankel2
