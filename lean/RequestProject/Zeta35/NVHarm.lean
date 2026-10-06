import RequestProject.Zeta35.NVBasic

/-!
# Non-vanishing (N, §6): the harmonic split of the local constants at a prime `ℓ`

For a prime `ℓ` we split the harmonic sums `∑_{m < 3N, 3 ∤ m} m^{-M-1}` into the terms with `ℓ | m`
(`hsumL`, the *harmonic poles at `ℓ`*) and the others (`hsumR`, `ℓ`-integral).  Correspondingly
`S_k = S^ℓ_k + S^{rest}_k`, `β_{k,a} = β^ℓ_{k,a} + β^{rest}_{k,a}` and `b = b^ℓ + b^{rest}`.

For `N ≤ ℓ` (`ℓ ≠ 3`) the poles are exactly `m = cℓ` with `c ∈ {1, 2}`, `cℓ < 3N` (`hsumL_eq`), and
for `3N ≤ ℓ` there are none (`hsumL_eq_zero`).
-/

open Polynomial Finset

namespace Zeta35.NV

/-- The harmonic poles at `ℓ`: `∑_{m < 3N, 3 ∤ m, ℓ | m} m^{-M-1}`. -/
noncomputable def hsumL (ℓ N M : ℕ) : ℚ :=
  ∑ m ∈ ((range (3 * N)).filter (fun m => ¬ 3 ∣ m)).filter (fun m => ℓ ∣ m), ((m : ℚ) ^ (M + 1))⁻¹

/-- The `ℓ`-integral rest: `∑_{m < 3N, 3 ∤ m, ℓ ∤ m} m^{-M-1}`. -/
noncomputable def hsumR (ℓ N M : ℕ) : ℚ :=
  ∑ m ∈ ((range (3 * N)).filter (fun m => ¬ 3 ∣ m)).filter (fun m => ¬ ℓ ∣ m),
    ((m : ℚ) ^ (M + 1))⁻¹

theorem hsum3_eq (ℓ N M : ℕ) : hsum3 N M = hsumL ℓ N M + hsumR ℓ N M := by
  unfold hsum3 hsumL hsumR; rw [Finset.sum_filter_add_sum_filter_not]

/-- The `ℓ`-pole part of `S_k(M)`. -/
noncomputable def SkL (ℓ : ℕ) (k : ℤ) (M : ℕ) : ℚ :=
  if 0 < k then -(M : ℚ) * 3 ^ (M + 1) * hsumL ℓ k.natAbs M
  else if k < 0 then (M : ℚ) * (-1) ^ (M + 1) * 3 ^ (M + 1) * hsumL ℓ k.natAbs M
  else 0

/-- The `ℓ`-integral part of `S_k(M)`. -/
noncomputable def SkR (ℓ : ℕ) (k : ℤ) (M : ℕ) : ℚ :=
  if 0 < k then -(M : ℚ) * 3 ^ (M + 1) * hsumR ℓ k.natAbs M
  else if k < 0 then (M : ℚ) * (-1) ^ (M + 1) * 3 ^ (M + 1) * hsumR ℓ k.natAbs M
  else 0

theorem Sk_eq (ℓ : ℕ) (k : ℤ) (M : ℕ) : Sk k M = SkL ℓ k M + SkR ℓ k M := by
  unfold Sk SkL SkR; rw [hsum3_eq ℓ]; split_ifs <;> ring

/-- `β^ℓ_{k,a}`: the part of `β_{k,a}` carrying the harmonic poles at `ℓ`. -/
noncomputable def betaL (n ℓ : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  -∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hk n k (4 - i - a) * SkL ℓ k (i + 1)

/-- `β^{rest}_{k,a}`. -/
noncomputable def betaR (n ℓ : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  -∑ i ∈ Icc 1 (4 - a), (i : ℚ) * Hk n k (4 - i - a) * SkR ℓ k (i + 1)

theorem betaC_eq (n ℓ : ℕ) (k : ℤ) (a : ℕ) : betaC n k a = betaL n ℓ k a + betaR n ℓ k a := by
  unfold betaC betaL betaR
  rw [← neg_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Sk_eq ℓ]; ring

/-- `b^ℓ(P) = ∑_k ∑_a β^ℓ_{k,a} P_a(k)`. -/
noncomputable def bLh (n ℓ : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range 4, betaL n ℓ k a * Pjet P k a

/-- `b^{rest}(P) = ∑_k ∑_a β^{rest}_{k,a} P_a(k)`. -/
noncomputable def bLr (n ℓ : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range 4, betaR n ℓ k a * Pjet P k a

theorem bL_eq (n ℓ : ℕ) (P : ℚ[X]) : bL n P = bLh n ℓ P + bLr n ℓ P := by
  unfold bL bLh bLr
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [betaC_eq n ℓ]; ring

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem VB_hsumR (N M : ℕ) : VB ℓ (hsumR ℓ N M) 0 := by
  refine VB.sum _ _ fun m hm => ?_
  have hm' : ¬ ℓ ∣ m := (Finset.mem_filter.mp hm).2
  rw [← inv_pow]
  have := (VB_inv_nat (ℓ := ℓ) hm').pow (M + 1)
  simpa using this

theorem VB_SkR (k : ℤ) (M : ℕ) : VB ℓ (SkR ℓ k M) 0 := by
  have h3 : VB ℓ ((3 : ℚ) ^ (M + 1)) 0 := by
    have := (VB_nat (ℓ := ℓ) 3).pow (M + 1); simpa using this
  have hM := VB_nat (ℓ := ℓ) M
  have hs : VB ℓ ((-1 : ℚ) ^ (M + 1)) 0 := by
    have := ((VB_one (ℓ := ℓ)).neg).pow (M + 1); simpa using this
  unfold SkR
  split_ifs
  · have := ((hM.neg.mul h3).mul (VB_hsumR (ℓ := ℓ) k.natAbs M)); simpa using this
  · have := (((hM.mul hs).mul h3).mul (VB_hsumR (ℓ := ℓ) k.natAbs M)); simpa using this
  · exact VB_zero 0

omit hℓ in
/-- No harmonic poles at `ℓ` when `3N ≤ ℓ`. -/
theorem hsumL_eq_zero {N : ℕ} (M : ℕ) (h : 3 * N ≤ ℓ) : hsumL ℓ N M = 0 := by
  refine Finset.sum_eq_zero fun m hm => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨⟨hm1, h3⟩, hl⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; exact h3 (dvd_zero 3)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hl
  omega

/-- The set `{c ∈ {1,2} : cℓ < 3N}` of harmonic poles `m = cℓ`. -/
def Cset (ℓ N : ℕ) : Finset ℕ := (Icc 1 2).filter (fun c => c * ℓ < 3 * N)

theorem hsumL_eq {N : ℕ} (M : ℕ) (hℓ3 : ℓ ≠ 3) (hN : N ≤ ℓ) :
    hsumL ℓ N M = ∑ c ∈ Cset ℓ N, (((c : ℚ) * ℓ) ^ (M + 1))⁻¹ := by
  have hlpos := hℓ.out.pos
  have hset : ((range (3 * N)).filter (fun m => ¬ 3 ∣ m)).filter (fun m => ℓ ∣ m) =
      (Cset ℓ N).image (fun c => c * ℓ) := by
    ext m
    simp only [Cset, Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm, h3⟩, ⟨c, rfl⟩⟩
      have hc0 : c ≠ 0 := by rintro rfl; exact h3 (by simp)
      have hc3 : c < 3 := by
        by_contra hc; push_neg at hc
        have : 3 * ℓ ≤ ℓ * c := by nlinarith
        omega
      exact ⟨c, ⟨⟨by omega, by omega⟩, by rw [mul_comm]; exact hm⟩, mul_comm _ _⟩
    · rintro ⟨c, ⟨⟨hc1, hc2⟩, hc⟩, rfl⟩
      refine ⟨⟨hc, ?_⟩, dvd_mul_left _ _⟩
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
      · have := Nat.le_of_dvd (by omega) h; interval_cases c
      · exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ.out).1 h).symm
  unfold hsumL
  rw [hset, Finset.sum_image]
  · refine Finset.sum_congr rfl fun c _ => ?_
    push_cast; ring
  · intro c _ c' _ h
    exact Nat.eq_of_mul_eq_mul_right hlpos h

omit hℓ in
theorem mem_Cset {N c : ℕ} (h : c ∈ Cset ℓ N) : c = 1 ∨ c = 2 := by
  simp only [Cset, Finset.mem_filter, Finset.mem_Icc] at h; omega

omit hℓ in
theorem Cset_eq_zero_iff {N : ℕ} : Cset ℓ N = ∅ ↔ ∀ c ∈ Icc 1 2, ¬ c * ℓ < 3 * N := by
  simp [Cset, Finset.filter_eq_empty_iff]

end Zeta35.NV
