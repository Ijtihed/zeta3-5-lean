import RequestProject.Zeta7.Hankel2.Reflection

/-!
# Purity of the 2-adic linear forms

This is the formal version of the key structural observation of `HANKEL2_ZETA7.md` and
`PADIC_ZETA7_REPORT.md`:

> if `R` is a rational function with poles of order at most `4` at the integers and
> `deg R ≤ −2`, then `L(R) = ∫_{ℤ₂} R‴(t+½) dt` is a **pure** linear form in `1` and
> `ζ₂(7)`: no `ζ₂(3)` and no `ζ₂(5)` occur.

After three differentiations a pole of order `i ≤ 4` of `R` becomes a pole of order `i+3`
of `R‴`, so the partial-fraction expansion of `R‴(t+½)` is a combination of the functions
`(t + ½ + k)^{-m}` with `4 ≤ m ≤ 7`.  By the structural lemma
(`Hankel2.hasVolkenborn_shift_nat`) the integral of such a term is
`m·2^{m+1}·ζ₂(m+1)` minus an explicit half-integer sum, so

* `m = 4` contributes `ζ₂(5)`, whose total coefficient is the sum of the residues of `R‴`
  at the simple poles — and this vanishes because `deg R ≤ −2`;
* `m = 5` and `m = 7` contribute `ζ₂(6)` and `ζ₂(8)`, which vanish because the 2-adic zeta
  function vanishes at even arguments;
* `m = 6` contributes `ζ₂(7)`.

`Hankel2.volkInt_pure` is exactly this statement, with the residue condition as the
hypothesis `hres` and with the two classical inputs — existence of the Volkenborn
integrals and the vanishing of `ζ₂` at even arguments — as explicit hypotheses.
-/

namespace Hankel2

open Filter Finset Topology

/-- The Volkenborn integral of a single shifted inverse power at `p = 2`, `c = 1/2`, in
`HasVolkenborn` form. -/
theorem hasVolkenborn_half_shift (m : ℕ) (hm : (m : ℚ_[2]) ≠ 0) (k : ℕ)
    (hI : ∃ I, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) I) :
    HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ m)⁻¹)
      ((m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1)
        - (m : ℚ_[2]) * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ (m + 1))⁻¹) := by
  obtain ⟨I, hI⟩ := hI
  have hz : (m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1) = I := by
    rw [zeta2]
    simp only [Nat.add_sub_cancel, hI.volkInt_eq]
    field_simp
  rw [hz]
  exact hasVolkenborn_shift_nat norm_half_2 m hI k

/-- **Purity of the linear forms.**  A combination of inverse powers `(t + ½ + k)^{-m}`
with `4 ≤ m ≤ 7` — the shape produced by three derivatives of a rational function whose
poles at the integers have order at most `4` — has a Volkenborn integral of the form
`a·ζ₂(7) + b`, with

`a = 6·2⁷·∑ₖ c₃(k)`   and   `b` an explicit half-integer combination,

provided the residue sum `∑ₖ c₁(k)` vanishes (the degree condition `deg R ≤ −2`).  No
`ζ₂(5)` survives.

The only hypotheses are `hex`, the classical existence of the Volkenborn integrals
(Volkenborn's theorem for strictly differentiable functions), and `hres`, the residue
condition.  The vanishing of `ζ₂` at even arguments is *not* assumed: it is proved in
`Reflection.lean` (`Hankel2.zeta2_even_eq_zero`) from the reflection rule. -/
theorem volkInt_pure (M : ℕ) (c₁ c₂ c₃ c₄ : ℕ → ℚ_[2])
    (hex : ∀ m, 4 ≤ m → m ≤ 8 → ∃ I, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) I)
    (hres : ∑ k ∈ range M, c₁ k = 0) :
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
              + 7 * c₄ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹)) := by
  classical
  -- the value of each of the four basic integrals
  have h4 : ∀ k : ℕ, HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹)
      ((4 : ℚ_[2]) * 2 ^ 5 * zeta2 5 - 4 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹) := by
    intro k
    have := hasVolkenborn_half_shift 4 (by norm_num) k (hex 4 le_rfl (by norm_num))
    norm_num at this ⊢
    exact this
  have h5 : ∀ k : ℕ, HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹)
      ((5 : ℚ_[2]) * 2 ^ 6 * zeta2 6 - 5 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹) := by
    intro k
    have := hasVolkenborn_half_shift 5 (by norm_num) k (hex 5 (by norm_num) (by norm_num))
    norm_num at this ⊢
    exact this
  have h6 : ∀ k : ℕ, HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹)
      ((6 : ℚ_[2]) * 2 ^ 7 * zeta2 7 - 6 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹) := by
    intro k
    have := hasVolkenborn_half_shift 6 (by norm_num) k (hex 6 (by norm_num) (by norm_num))
    norm_num at this ⊢
    exact this
  have h7 : ∀ k : ℕ, HasVolkenborn 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹)
      ((7 : ℚ_[2]) * 2 ^ 8 * zeta2 8 - 7 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹) := by
    intro k
    have := hasVolkenborn_half_shift 7 (by norm_num) k (hex 7 (by norm_num) (by norm_num))
    norm_num at this ⊢
    exact this
  -- the even zeta values vanish (proved, not assumed)
  have hz6 : zeta2 6 = 0 :=
    zeta2_even_eq_zero 6 (by decide) (by norm_num)
      (hex 5 (by norm_num) (by norm_num)) (hex 6 (by norm_num) (by norm_num))
  have hz8 : zeta2 8 = 0 :=
    zeta2_even_eq_zero 8 (by decide) (by norm_num)
      (hex 7 (by norm_num) (by norm_num)) (hex 8 (by norm_num) (by norm_num))
  -- assemble
  have hterm : ∀ k ∈ range M, HasVolkenborn 2
      (fun t => c₁ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹
        + c₂ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹
        + c₃ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹
        + c₄ k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹)
      (c₁ k * ((4 : ℚ_[2]) * 2 ^ 5 * zeta2 5 - 4 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹)
        + c₂ k * ((5 : ℚ_[2]) * 2 ^ 6 * zeta2 6
            - 5 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹)
        + c₃ k * ((6 : ℚ_[2]) * 2 ^ 7 * zeta2 7
            - 6 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹)
        + c₄ k * ((7 : ℚ_[2]) * 2 ^ 8 * zeta2 8
            - 7 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹)) := by
    intro k _
    exact (((((h4 k).const_mul (c₁ k)).add ((h5 k).const_mul (c₂ k))).add
      ((h6 k).const_mul (c₃ k))).add ((h7 k).const_mul (c₄ k)))
  have hsum := HasVolkenborn.sum (range M) _ _ hterm
  -- identify the limit
  have hval : (∑ k ∈ range M,
      (c₁ k * ((4 : ℚ_[2]) * 2 ^ 5 * zeta2 5
          - 4 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹)
        + c₂ k * ((5 : ℚ_[2]) * 2 ^ 6 * zeta2 6
            - 5 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹)
        + c₃ k * ((6 : ℚ_[2]) * 2 ^ 7 * zeta2 7
            - 6 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹)
        + c₄ k * ((7 : ℚ_[2]) * 2 ^ 8 * zeta2 8
            - 7 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹)))
      = (6 * 2 ^ 7 * ∑ k ∈ range M, c₃ k) * zeta2 7
        - ∑ k ∈ range M,
            (4 * c₁ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹
              + 5 * c₂ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹
              + 6 * c₃ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹
              + 7 * c₄ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹) := by
    rw [hz6, hz8]
    have hsplit : ∀ k : ℕ, c₁ k * ((4 : ℚ_[2]) * 2 ^ 5 * zeta2 5
          - 4 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹)
        + c₂ k * ((5 : ℚ_[2]) * 2 ^ 6 * 0
            - 5 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹)
        + c₃ k * ((6 : ℚ_[2]) * 2 ^ 7 * zeta2 7
            - 6 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹)
        + c₄ k * ((7 : ℚ_[2]) * 2 ^ 8 * 0
            - 7 * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹)
        = (c₁ k * (4 * 2 ^ 5 * zeta2 5) + c₃ k * (6 * 2 ^ 7 * zeta2 7))
          - (4 * c₁ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 5)⁻¹
              + 5 * c₂ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 6)⁻¹
              + 6 * c₃ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 7)⁻¹
              + 7 * c₄ k * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ 8)⁻¹) := by
      intro k; ring
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hres]
    ring
  rwa [hval] at hsum

end Hankel2
