import RequestProject.Zeta35.Defs
import RequestProject.Zeta7.Hankel2.Reflection
import RequestProject.Zeta7.Hankel2.PurityInt

/-!
# Existence of the basic integrals and `I_M = 0` for odd `M` (paper N, Lemma 2.1; CLAIMS T1)

* `norm_a_div_three`: `‖a/3‖₃ = 3 > 1` for `a = 1, 2`;
* `exists_hasVolkenborn_a`: the Volkenborn integral of `(t + a/3)^{-M}` exists
  (`Hankel2.exists_hasVolkenborn_inv_pow`);
* `hasVolkenborn_reflect_one`: the reflection `t ↦ −1 − t`,
  `∫ (−1 − t + c)^{-m} dt = ∫ (t + c)^{-m} dt` for `‖c‖ > 1`;
* `IM_odd`: **`I_M = 0` for odd `M`**: the reflection maps the term `a` to `−1` times the term
  `3 − a`;
* `IM_four`: `I_4 = 4·3⁵ ζ₃(5)` (by definition).
-/

open Filter Topology Finset

namespace Zeta35

open Hankel2


theorem norm_three : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by
  have := Padic.norm_p (p := 3); push_cast at this; exact this

theorem norm_a_div_three {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) : 1 < ‖(a : ℚ_[3]) / 3‖ := by
  have hna : ‖(a : ℚ_[3])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    interval_cases a <;> decide
  rw [norm_div, hna, norm_three]; norm_num

theorem exists_hasVolkenborn_a {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (M : ℕ) :
    ∃ I, HasVolkenborn 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ M)⁻¹) I :=
  exists_hasVolkenborn_inv_pow (norm_a_div_three ha1 ha2) M

theorem hasVolkenborn_volkInt_a {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (M : ℕ) :
    HasVolkenborn 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ M)⁻¹)
      (volkInt 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ M)⁻¹)) := by
  obtain ⟨I, hI⟩ := exists_hasVolkenborn_a ha1 ha2 M
  rwa [hI.volkInt_eq]

variable {p : ℕ} [Fact p.Prime]

/-- **The reflection `t ↦ −1 − t`**: for `‖c‖ > 1`, `∫ (−t + (c − 1))^{-m} dt = ∫ (t + c)^{-m} dt`. -/
theorem hasVolkenborn_reflect_one {c : ℚ_[p]} (hc : 1 < ‖c‖) (m : ℕ) {I : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I) :
    HasVolkenborn p (fun t => ((-t + (c - 1)) ^ m)⁻¹) I := by
  have hc' : 1 < ‖c - 1‖ := by
    simpa using one_lt_norm_sub_nat hc 1
  obtain ⟨I', hI'⟩ := exists_hasVolkenborn_inv_pow hc' m
  obtain ⟨J', hJ'⟩ := exists_hasVolkenborn_inv_pow hc' (m + 1)
  have h1 := hasVolkenborn_reflect hc' m hI' hJ'
  have h2 := hasVolkenborn_shift hc' m hI'
  rw [show c - 1 + 1 = c by ring] at h2
  have := hI.unique h2
  rw [this]
  convert h1 using 1
  ring

theorem volkInt_a_odd (M : ℕ) (hM : Odd M) :
    volkInt 3 (fun t => ((t + ((1 : ℕ) : ℚ_[3]) / 3) ^ M)⁻¹) =
      -volkInt 3 (fun t => ((t + ((2 : ℕ) : ℚ_[3]) / 3) ^ M)⁻¹) := by
  have h2 := hasVolkenborn_volkInt_a (a := 2) (by norm_num) le_rfl M
  have h1 := hasVolkenborn_volkInt_a (a := 1) le_rfl (by norm_num) M
  have hr := hasVolkenborn_reflect_one (norm_a_div_three (a := 2) (by norm_num) le_rfl) M h2
  have hfun : (fun t : ℚ_[3] => ((-t + (((2 : ℕ) : ℚ_[3]) / 3 - 1)) ^ M)⁻¹) =
      fun t => -(((t + ((1 : ℕ) : ℚ_[3]) / 3) ^ M)⁻¹) := by
    funext t
    have : (-t + (((2 : ℕ) : ℚ_[3]) / 3 - 1)) = -(t + ((1 : ℕ) : ℚ_[3]) / 3) := by
      push_cast; ring
    rw [this, hM.neg_pow, inv_neg]
  rw [hfun] at hr
  have h3 := hr.neg
  simp only [neg_neg] at h3
  rw [h1.unique h3]

/-- **`I_M = 0` for odd `M`** (paper N, Lemma 2.1). -/
theorem IM_odd (M : ℕ) (hM : Odd M) : IM M = 0 := by
  rw [IM, show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide, Finset.sum_pair (by norm_num),
    volkInt_a_odd M hM]
  ring

/-- `I_4 = 4·3⁵ ζ₃(5)` (the normalisation of N, Lemma 2.1). -/
theorem IM_four : IM 4 = 4 * 3 ^ 5 * zeta3 5 := by
  rw [zeta3]
  norm_num
  field_simp

end Zeta35
