import RequestProject.Zeta7.Hankel2.OddDen

/-!
# The product-formula criterion for a general prime `p` (paper N, Lemma 2.3; P, Lemma 3.1)

The `p`-adic analogue of `Hankel2.odd_den_criterion` (which is the case `p = 2`): for `Δ ∈ ℚ[X]`
of degree `≤ K` and a rational `r` with `Δ(r) ≠ 0`,

  `1 ≤ d · ‖Δ‖₁ · max(|num r|, den r)^K · ‖Δ(r)‖_p`,

where `d = ∏_{q ≠ p} q^{E_q}` and `E_q ≤ max(−v_q(Δ), 0)`.  The `p`-part of the content cancels
exactly (`Zeta35.pden_criterion`).  For `p = 3` this is N, Lemma 2.3.
-/

open Polynomial Finset

namespace Zeta35

open Hankel2

/-- `D · ‖D‖_p = ` the prime-to-`p` part of `D`. -/
theorem mul_norm_p_eq_ordCompl (p : ℕ) [hp : Fact p.Prime] (D : ℕ) (hD : D ≠ 0) :
    (D : ℝ) * ‖(D : ℚ_[p])‖ = (ordCompl[p] D : ℕ) := by
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self D p
  have hcop : ‖((ordCompl[p] D : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_ordCompl hp.out hD)
  set v := D.factorization p
  set d := ordCompl[p] D
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  conv_lhs => rw [← hsplit]
  push_cast
  rw [norm_mul, norm_pow, Padic.norm_p, hcop]
  have : (p : ℝ) ^ v * (p : ℝ)⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp0, one_pow]
  calc (p : ℝ) ^ v * d * ((p : ℝ)⁻¹ ^ v * 1) = ((p : ℝ) ^ v * (p : ℝ)⁻¹ ^ v) * d := by ring
    _ = d := by rw [this, one_mul]

/-- **The criterion with the prime-to-`p` denominator ledger** (N, Lemma 2.3 for `p = 3`). -/
theorem pden_criterion (p : ℕ) [hp : Fact p.Prime] (Δ : ℚ[X]) {K : ℕ} (hK : Δ.natDegree ≤ K)
    (r : ℚ) (hne : aeval (r : ℚ_[p]) Δ ≠ 0) :
    ∃ (S : Finset ℕ) (E : ℕ → ℕ),
      (∀ q ∈ S, q.Prime ∧ q ≠ p ∧ ∀ g : ℤ, gaussVal q Δ = g → (E q : ℤ) ≤ max (-g) 0) ∧
      1 ≤ (∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K * ‖aeval (r : ℚ_[p]) Δ‖ := by
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
  have hQr : aeval (r : ℚ_[p]) Q = (D : ℚ_[p]) * aeval (r : ℚ_[p]) Δ := by
    have : aeval (r : ℚ_[p]) Q = aeval (r : ℚ_[p]) (Q.map (algebraMap ℤ ℚ)) := by
      rw [aeval_map_algebraMap]
    rw [this, show algebraMap ℤ ℚ = Int.castRingHom ℚ from rfl, hQ]; simp
  have hQne : aeval (r : ℚ_[p]) Q ≠ 0 := by
    rw [hQr]; exact mul_ne_zero (by exact_mod_cast hD0) hne
  have hcrit := one_le_length_mul_norm p Q hQdeg r hQne
  have hlen : (plength Q : ℝ) = D * l1 Δ := by
    rw [plength_eq_sum_range Q hQdeg, l1_eq_sum_range Δ hK]; push_cast; rw [mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((Q.coeff i : ℤ) : ℝ) = (D : ℝ) * ((Δ.coeff i : ℚ) : ℝ) := by
      have := congrArg (fun x : ℚ => (x : ℝ)) (hQc i); push_cast at this; exact this
    rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  set d := ordCompl[p] D with hd_def
  have hd0 : d ≠ 0 := (Nat.ordCompl_pos p hD0).ne'
  refine ⟨d.primeFactors, d.factorization, ?_, ?_⟩
  · intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqp' : q ≠ p := by
      rintro rfl
      exact Nat.not_dvd_ordCompl hp.out hD0 (Nat.dvd_of_mem_primeFactors hq)
    refine ⟨hqp, hqp', fun g hg => ?_⟩
    haveI := Fact.mk hqp
    have hE : d.factorization q = D.factorization q := by
      rw [hd_def, Nat.factorization_ordCompl, Finsupp.erase_ne hqp']
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
    rw [hprod, ← mul_norm_p_eq_ordCompl p D hD0]
    rw [hlen, hQr, norm_mul] at hcrit
    calc (1 : ℝ) ≤ _ := hcrit
      _ = _ := by ring

end Zeta35
