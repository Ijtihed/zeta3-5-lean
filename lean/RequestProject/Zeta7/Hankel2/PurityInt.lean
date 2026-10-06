import RequestProject.Zeta7.Hankel2.VolkenbornExist
import RequestProject.Zeta7.Hankel2.Purity
import RequestProject.Zeta7.Hankel2.NVFamily3

/-!
# Purity for all integer pole shifts (paper §2.1, v4.1 eqs. (4)–(5))

* `Hankel2.hasVolkenborn_translate_back` — the backward translation formula (V1):
  `∫ f(t − N) dt = ∫ f(t) dt − ∑_{ℓ=1}^{N} f′(−ℓ)` for `f(t) = (t + c)^{-m}`, `‖c‖ > 1`
  (so `f′(x) = −m (x + c)^{-(m+1)}`).
* `Hankel2.hasVolkenborn_half_shift_int` — for every `k : ℤ`,
  `I_{m,k} = ∫_{ℤ₂} (t + ½ + k)^{-m} dt = m 2^{m+1} ζ₂(m+1) − m HS(k, m+1)`,
  with `HS(k, M) = ∑_{l=1}^{k} (2/(2l−1))^M` for `k ≥ 0` and
  `HS(k, M) = −∑_{l=k+1}^{0} (2/(2l−1))^M` for `k < 0` (`W3.Fam3.hsSum`, paper v4.1 eq. (5)).
* `Hankel2.volkInt_pure_int` — purity for combinations of `(t + ½ + k)^{-m}`, `4 ≤ m ≤ 7`,
  with arbitrary integer shifts `k`, and **no existence hypothesis**.
* `Hankel2.volkInt_pure'` — the original `volkInt_pure` with its existence hypothesis
  discharged.

All existence statements are now proved (`Hankel2.exists_hasVolkenborn_inv_pow`).
-/

namespace Hankel2

open Filter Finset Topology

variable {p : ℕ} [Fact p.Prime]

/-- `‖c - N‖ = ‖c‖ > 1` for a natural `N`. -/
theorem one_lt_norm_sub_nat {c : ℚ_[p]} (hc : 1 < ‖c‖) (N : ℕ) : 1 < ‖c - (N : ℚ_[p])‖ := by
  have hN : ‖(N : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) (N : ℤ)
  have hne : ‖c‖ ≠ ‖-(N : ℚ_[p])‖ := by rw [norm_neg]; intro h; rw [h] at hc; linarith
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne]
  exact lt_of_lt_of_le hc (le_max_left _ _)

/-- **Backward translation (V1).**  For `‖c‖ > 1` and `f(t) = (t + c)^{-m}`,
`∫ f(t − N) dt = ∫ f(t) dt − ∑_{ℓ=1}^{N} f′(−ℓ)`, where `f′(x) = −m (x + c)^{-(m+1)}`. -/
theorem hasVolkenborn_translate_back {c : ℚ_[p]} (hc : 1 < ‖c‖) (m N : ℕ) {I : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I) :
    HasVolkenborn p (fun t => ((t - (N : ℚ_[p]) + c) ^ m)⁻¹)
      (I - ∑ ℓ ∈ Finset.Icc 1 N, (-(m : ℚ_[p]) * ((-(ℓ : ℚ_[p]) + c) ^ (m + 1))⁻¹)) := by
  obtain ⟨J, hJ⟩ := exists_hasVolkenborn_inv_pow (one_lt_norm_sub_nat hc N) m
  have h := hasVolkenborn_shift_nat (one_lt_norm_sub_nat hc N) m hJ N
  have hc' : c - (N : ℚ_[p]) + (N : ℚ_[p]) = c := by ring
  rw [hc'] at h
  have hIJ := hI.unique h
  have hfun : (fun t : ℚ_[p] => ((t - (N : ℚ_[p]) + c) ^ m)⁻¹) = fun t => ((t + (c - N)) ^ m)⁻¹ := by
    funext t; ring_nf
  rw [hfun]
  convert hJ using 1
  rw [hIJ]
  -- reindex `l ↦ ℓ = N - l`
  have hre : ∑ l ∈ range N, ((c - (N : ℚ_[p]) + (l : ℚ_[p])) ^ (m + 1))⁻¹ =
      ∑ ℓ ∈ Finset.Icc 1 N, ((-(ℓ : ℚ_[p]) + c) ^ (m + 1))⁻¹ := by
    refine Finset.sum_nbij' (fun l => N - l) (fun ℓ => N - ℓ) ?_ ?_ ?_ ?_ ?_
    · intro l hl; simp only [mem_range] at hl; simp only [Finset.mem_Icc]; omega
    · intro ℓ hl; simp only [Finset.mem_Icc] at hl; simp only [mem_range]; omega
    · intro l hl; simp only [mem_range] at hl; dsimp only; omega
    · intro ℓ hl; simp only [Finset.mem_Icc] at hl; dsimp only; omega
    · intro l hl
      simp only [mem_range] at hl
      rw [Nat.cast_sub hl.le]
      ring_nf
  rw [hre]
  simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- The harmonic sum `HS(k, M)` of paper v4.1 eqs. (4)–(5). -/
noncomputable abbrev HS (k : ℤ) (M : ℕ) : ℚ := W3.Fam3.hsSum k M (fun _ => True)

theorem HS_nat (N M : ℕ) :
    ((HS N M : ℚ) : ℚ_[2]) = ∑ l ∈ range N, ((1 / 2 + (l : ℚ_[2])) ^ M)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [HS, W3.Fam3.hsSum]
  rw [HS, W3.Fam3.hsSum, if_pos (by exact_mod_cast hN), Finset.filter_true]
  push_cast
  symm
  refine Finset.sum_nbij' (fun l => (l : ℤ) + 1) (fun l => (l - 1).toNat) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [mem_range] at hl; simp only [Finset.mem_Icc]; omega
  · intro l hl; simp only [Finset.mem_Icc] at hl; simp only [mem_range]; omega
  · intro l hl; simp
  · intro l hl; simp only [Finset.mem_Icc] at hl; dsimp only; omega
  · intro l _
    push_cast
    have h : (1 / 2 + (l : ℚ_[2])) ≠ 0 := by
      have : (1 / 2 + (l : ℚ_[2])) = (((2 * l + 1 : ℕ) : ℚ) : ℚ_[2]) / 2 := by push_cast; ring
      rw [this]
      exact div_ne_zero (by exact_mod_cast (by omega : 2 * l + 1 ≠ 0)) two_ne_zero
    rw [show (2 : ℚ_[2]) / (2 * ((l : ℚ_[2]) + 1) - 1) = (1 / 2 + (l : ℚ_[2]))⁻¹ by
      field_simp; ring, inv_pow]

theorem HS_neg (N M : ℕ) :
    ((HS (-(N : ℤ)) M : ℚ) : ℚ_[2]) =
      -∑ l ∈ range N, ((1 / 2 - (N : ℚ_[2]) + (l : ℚ_[2])) ^ M)⁻¹ := by
  have hk : ¬ (0 : ℤ) < -(N : ℤ) := by omega
  rw [HS, W3.Fam3.hsSum, if_neg hk, Finset.filter_true]
  push_cast
  congr 1
  symm
  refine Finset.sum_nbij' (fun l => (l : ℤ) + 1 - N) (fun l => (l + N - 1).toNat) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [mem_range] at hl; simp only [Finset.mem_Icc]; omega
  · intro l hl; simp only [Finset.mem_Icc] at hl; simp only [mem_range]; omega
  · intro l hl; simp only [mem_range] at hl; simp
  · intro l hl; simp only [Finset.mem_Icc] at hl; dsimp only; omega
  · intro l _
    push_cast
    have h : (1 / 2 - (N : ℚ_[2]) + (l : ℚ_[2])) ≠ 0 := by
      intro h0
      have h1 : (((2 * (l : ℤ) + 1 - 2 * N : ℤ) : ℚ) : ℚ_[2]) = 0 := by
        push_cast; linear_combination 2 * h0
      have h2 : ((2 * (l : ℤ) + 1 - 2 * N : ℤ) : ℚ) = 0 := by exact_mod_cast h1
      have h3 : (2 * (l : ℤ) + 1 - 2 * N : ℤ) = 0 := by exact_mod_cast h2
      omega
    rw [show (2 : ℚ_[2]) / (2 * ((l : ℚ_[2]) + 1 - N) - 1) = (1 / 2 - (N : ℚ_[2]) + l)⁻¹ by
      field_simp; ring, inv_pow]

/-- **The integral `I_{m,k}` for every integer shift** (paper v4.1 eqs. (4)–(5)):
`∫_{ℤ₂} (t + ½ + k)^{-m} dt = m 2^{m+1} ζ₂(m+1) − m HS(k, m+1)` for all `k : ℤ`. -/
theorem hasVolkenborn_half_shift_int (m : ℕ) (hm : (m : ℚ_[2]) ≠ 0) (k : ℤ) :
    HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ m)⁻¹)
      ((m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1) - (m : ℚ_[2]) * ((HS k (m + 1) : ℚ) : ℚ_[2])) := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, k = N := ⟨k.toNat, by omega⟩
    rw [HS_nat]
    have := hasVolkenborn_half_shift m hm N (exists_hasVolkenborn_half m)
    simpa using this
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, k = -(N : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hN
    rw [HS_neg]
    obtain ⟨I, hI⟩ := exists_hasVolkenborn_half m
    have hz : (m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1) = I := by
      rw [zeta2]
      simp only [Nat.add_sub_cancel, hI.volkInt_eq]
      field_simp
    rw [hz]
    obtain ⟨J, hJ⟩ := exists_hasVolkenborn_inv_pow (one_lt_norm_sub_nat norm_half_2 N) m
    have h := hasVolkenborn_shift_nat (one_lt_norm_sub_nat norm_half_2 N) m hJ N
    have hc' : (1 / 2 : ℚ_[2]) - (N : ℚ_[2]) + (N : ℚ_[2]) = 1 / 2 := by ring
    rw [hc'] at h
    have hIJ := hI.unique h
    have hfun : (fun t : ℚ_[2] => ((t + (1 / 2 + ((-(N : ℤ) : ℤ) : ℚ_[2]))) ^ m)⁻¹) =
        fun t : ℚ_[2] => ((t + (1 / 2 - (N : ℚ_[2]))) ^ m)⁻¹ := by
      funext t; push_cast; ring_nf
    rw [hfun]
    convert hJ using 1
    rw [hIJ]
    ring

/-- **Purity for all integer shifts.**  For any finite set `S` of integer shifts and
coefficients `c₁, …, c₄`, the Volkenborn integral of
`∑_{k∈S} ∑_{i=1}^{4} c_i(k) (t + ½ + k)^{-(i+3)}` exists and equals
`6·2⁷ (∑_k c₃(k)) ζ₂(7) − ∑_k ∑_i (i+3) c_i(k) HS(k, i+4)`, provided the residue sum
`∑_k c₁(k)` vanishes.  No existence hypothesis is needed. -/
theorem volkInt_pure_int (S : Finset ℤ) (c₁ c₂ c₃ c₄ : ℤ → ℚ_[2])
    (hres : ∑ k ∈ S, c₁ k = 0) :
    HasVolkenborn 2
      (fun t => ∑ k ∈ S,
        (c₁ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹
          + c₂ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹
          + c₃ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹
          + c₄ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹))
      ((6 * 2 ^ 7 * ∑ k ∈ S, c₃ k) * zeta2 7
        - ∑ k ∈ S,
            (4 * c₁ k * ((HS k 5 : ℚ) : ℚ_[2]) + 5 * c₂ k * ((HS k 6 : ℚ) : ℚ_[2])
              + 6 * c₃ k * ((HS k 7 : ℚ) : ℚ_[2]) + 7 * c₄ k * ((HS k 8 : ℚ) : ℚ_[2]))) := by
  classical
  have hz6 : zeta2 6 = 0 :=
    zeta2_even_eq_zero 6 (by decide) (by norm_num) (exists_hasVolkenborn_half _)
      (exists_hasVolkenborn_half _)
  have hz8 : zeta2 8 = 0 :=
    zeta2_even_eq_zero 8 (by decide) (by norm_num) (exists_hasVolkenborn_half _)
      (exists_hasVolkenborn_half _)
  have hterm : ∀ k ∈ S, HasVolkenborn 2
      (fun t => c₁ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹
        + c₂ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹
        + c₃ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹
        + c₄ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹)
      ((4 * 2 ^ 5 * zeta2 5) * c₁ k + (6 * 2 ^ 7 * zeta2 7) * c₃ k
        - (4 * c₁ k * ((HS k 5 : ℚ) : ℚ_[2]) + 5 * c₂ k * ((HS k 6 : ℚ) : ℚ_[2])
              + 6 * c₃ k * ((HS k 7 : ℚ) : ℚ_[2]) + 7 * c₄ k * ((HS k 8 : ℚ) : ℚ_[2]))) := by
    intro k _
    have h := ((((hasVolkenborn_half_shift_int 4 (by norm_num) k).const_mul (c₁ k)).add
      ((hasVolkenborn_half_shift_int 5 (by norm_num) k).const_mul (c₂ k))).add
      ((hasVolkenborn_half_shift_int 6 (by norm_num) k).const_mul (c₃ k))).add
      ((hasVolkenborn_half_shift_int 7 (by norm_num) k).const_mul (c₄ k))
    convert h using 1
    norm_num only [hz6, hz8]
    ring
  have hsum := HasVolkenborn.sum S _ _ hterm
  convert hsum using 1
  have e1 : ∑ x ∈ S, ((4 * 2 ^ 5 * zeta2 5) * c₁ x + (6 * 2 ^ 7 * zeta2 7) * c₃ x) =
      (6 * 2 ^ 7 * ∑ k ∈ S, c₃ k) * zeta2 7 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hres]
    ring
  rw [Finset.sum_sub_distrib, e1]

/-- The original `volkInt_pure`, with its existence hypothesis discharged. -/
theorem volkInt_pure' (M : ℕ) (c₁ c₂ c₃ c₄ : ℕ → ℚ_[2]) (hres : ∑ k ∈ range M, c₁ k = 0) :
    HasVolkenborn 2
      (fun t => ∑ k ∈ range M,
        (c₁ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹
          + c₂ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹
          + c₃ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹
          + c₄ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹))
      ((6 * 2 ^ 7 * ∑ k ∈ range M, c₃ k) * zeta2 7
        - ∑ k ∈ range M,
            (4 * c₁ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹
              + 5 * c₂ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹
              + 6 * c₃ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹
              + 7 * c₄ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹)) :=
  volkInt_pure M c₁ c₂ c₃ c₄ (fun m _ _ => exists_hasVolkenborn_half m) hres

end Hankel2
