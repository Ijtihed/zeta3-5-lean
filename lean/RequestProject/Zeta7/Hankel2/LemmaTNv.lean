import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# The negative Gauss valuation `nv(F) = −v_p(F)` (for paper Theorem 7.1)

`nv p F = negTop (gaussVal p F) ∈ WithBot ℤ` (`= ⊥` iff `F = 0`).  It is characterised by
coefficient norms in `ℚ_[p]` (`nv_le_iff`), and it is subadditive under sums and products:
`nv (F + G) ≤ max`, `nv (∑) ≤ sup`, `nv (F G) ≤ nv F + nv G`, `nv (∏) ≤ ∑`.
-/

open Polynomial Finset

namespace Hankel2

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_rat_le_zpow_iff (q : ℚ) (T : ℤ) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ T ↔ q = 0 ∨ -T ≤ padicValRat p q := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  by_cases hq : q = 0
  · subst hq; simp; positivity
  · rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
    push_cast
    rw [zpow_le_zpow_iff_right₀ hp1]
    simp [hq]; omega

theorem negTop_le_coe_iff (a : WithTop ℤ) (T : ℤ) :
    negTop a ≤ (T : WithBot ℤ) ↔ ((-T : ℤ) : WithTop ℤ) ≤ a := by
  cases a with
  | top => simp [negTop]
  | coe a =>
    change ((-a : ℤ) : WithBot ℤ) ≤ T ↔ _
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe]; omega

/-- `nv p F = −v_p(F)`. -/
noncomputable def nv (p : ℕ) (F : ℚ[X]) : WithBot ℤ := negTop (gaussVal p F)

theorem nv_le_iff (F : ℚ[X]) (T : ℤ) :
    nv p F ≤ (T : WithBot ℤ) ↔ ∀ i, ‖((F.coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ T := by
  rw [nv, negTop_le_coe_iff, gaussVal, Finset.le_inf_iff]
  simp only [norm_rat_le_zpow_iff, mem_support_iff, WithTop.coe_le_coe]
  constructor
  · intro h i
    by_cases hi : F.coeff i = 0
    · exact Or.inl hi
    · exact Or.inr (h i hi)
  · intro h i hi
    exact (h i).resolve_left hi

omit hp in
theorem nv_eq_bot_iff (F : ℚ[X]) : nv p F = ⊥ ↔ F = 0 := by
  constructor
  · intro h
    by_contra hF
    obtain ⟨i, hi⟩ : ∃ i, F.coeff i ≠ 0 := by
      by_contra h'; push_neg at h'; exact hF (Polynomial.ext (by simpa using h'))
    have hle : gaussVal p F ≤ ((padicValRat p (F.coeff i) : ℤ) : WithTop ℤ) :=
      Finset.inf_le (mem_support_iff.2 hi)
    unfold nv at h
    revert h hle
    generalize gaussVal p F = a
    cases a with
    | top => simp
    | coe a => simp [negTop]
  · rintro rfl; simp [nv, gaussVal, negTop]

@[simp] theorem nv_zero : nv p 0 = ⊥ := (nv_eq_bot_iff 0).2 rfl

omit hp in
/-- To bound `nv F` it suffices to bound it by every integer above `B`. -/
theorem nv_le_of_forall {F : ℚ[X]} {B : WithBot ℤ}
    (h : ∀ T : ℤ, B ≤ (T : WithBot ℤ) → nv p F ≤ T) : nv p F ≤ B := by
  induction B with
  | bot =>
    by_contra hne
    rw [le_bot_iff] at hne
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    have := h (a - 1) bot_le
    rw [← ha, WithBot.coe_le_coe] at this
    omega
  | coe B => exact h B le_rfl

theorem nv_add_le (F G : ℚ[X]) : nv p (F + G) ≤ max (nv p F) (nv p G) := by
  refine nv_le_of_forall fun T hT => ?_
  rw [max_le_iff] at hT
  have h1 := (nv_le_iff F T).1 hT.1
  have h2 := (nv_le_iff G T).1 hT.2
  rw [nv_le_iff]
  intro i
  rw [coeff_add, Rat.cast_add]
  exact (Padic.nonarchimedean _ _).trans (max_le (h1 i) (h2 i))

theorem nv_neg (F : ℚ[X]) : nv p (-F) = nv p F := by
  refine le_antisymm (nv_le_of_forall fun T hT => ?_) (nv_le_of_forall fun T hT => ?_) <;>
    rw [nv_le_iff] at hT ⊢ <;> intro i <;>
    simpa [coeff_neg] using hT i

theorem nv_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℚ[X]) :
    nv p (∑ i ∈ s, F i) ≤ s.sup fun i => nv p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sup_insert]
    exact (nv_add_le _ _).trans (max_le_max le_rfl ih)

theorem nv_mul_le (F G : ℚ[X]) : nv p (F * G) ≤ nv p F + nv p G := by
  refine nv_le_of_forall fun T hT => ?_
  induction h1 : nv p F with
  | bot => rw [nv_eq_bot_iff] at h1; subst h1; simp
  | coe a =>
    induction h2 : nv p G with
    | bot => rw [nv_eq_bot_iff] at h2; subst h2; simp
    | coe b =>
      rw [h1, h2, ← WithBot.coe_add, WithBot.coe_le_coe] at hT
      have hF := (nv_le_iff F a).1 h1.le
      have hG := (nv_le_iff G b).1 h2.le
      rw [nv_le_iff]
      intro i
      rw [coeff_mul, Rat.cast_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
      rw [Rat.cast_mul, norm_mul]
      calc ‖((F.coeff x.1 : ℚ) : ℚ_[p])‖ * ‖((G.coeff x.2 : ℚ) : ℚ_[p])‖
          ≤ (p : ℝ) ^ a * (p : ℝ) ^ b :=
            mul_le_mul (hF _) (hG _) (norm_nonneg _) (by positivity)
        _ = (p : ℝ) ^ (a + b) := by
            rw [zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
        _ ≤ (p : ℝ) ^ T :=
            zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) hT

theorem nv_one : nv p (1 : ℚ[X]) = 0 := by
  rw [← C_1, nv, gaussVal, Polynomial.support_C one_ne_zero]
  simp [negTop]; rfl

theorem nv_prod_le {ι : Type*} (s : Finset ι) (F : ι → ℚ[X]) :
    nv p (∏ i ∈ s, F i) ≤ ∑ i ∈ s, nv p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nv_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (nv_mul_le _ _).trans (add_le_add le_rfl ih)

theorem nv_C_le {q : ℚ} {T : ℤ} (h : ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ T) :
    nv p (C q) ≤ T := by
  rw [nv_le_iff]
  intro i
  rw [coeff_C]
  split_ifs
  · exact h
  · simp; positivity

end Hankel2
