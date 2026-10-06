import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# The `ℓ¹` norm on `ℚ[X]` and on real multivariate polynomials (for paper Lemma 6.2)

* `l1_eq_sum_support`, `l1_add_le`, `l1_neg`, `l1_sum_le`, `l1_mul_le` (submultiplicativity),
  `l1_prod_le`, `l1_C`, `l1_det_le` (`‖det M‖₁ ≤ (card ι)! · A^{card ι}` if every entry has
  `‖M_{ij}‖₁ ≤ A`).
* `mvl1` for `MvPolynomial σ ℝ`: `abs_coeff_le_mvl1`, `mvl1_add_le`, `mvl1_mul_le`, `mvl1_prod_le`.
-/

open Polynomial Finset

namespace Hankel2.ArchB

/-! ### `ℚ[X]` -/

theorem l1_eq_sum_support (F : ℚ[X]) : l1 F = ∑ i ∈ F.support, |((F.coeff i : ℚ) : ℝ)| := by
  unfold l1
  symm
  refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
  · simp only [mem_range]
    exact Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hi)
  · simp only [mem_support_iff, not_not] at hi
    simp [hi]

theorem l1_nonneg (F : ℚ[X]) : 0 ≤ l1 F := sum_nonneg fun _ _ => abs_nonneg _

theorem l1_eq_sum_of_superset (F : ℚ[X]) (s : Finset ℕ) (hs : F.support ⊆ s) :
    l1 F = ∑ i ∈ s, |((F.coeff i : ℚ) : ℝ)| := by
  rw [l1_eq_sum_support]
  refine Finset.sum_subset hs (fun i _ hi => ?_)
  simp only [mem_support_iff, not_not] at hi
  simp [hi]

theorem l1_zero : l1 (0 : ℚ[X]) = 0 := by simp [l1]

theorem l1_add_le (F G : ℚ[X]) : l1 (F + G) ≤ l1 F + l1 G := by
  classical
  rw [l1_eq_sum_of_superset (F + G) (F.support ∪ G.support) support_add,
    l1_eq_sum_of_superset F (F.support ∪ G.support) subset_union_left,
    l1_eq_sum_of_superset G (F.support ∪ G.support) subset_union_right, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [coeff_add]; push_cast; exact abs_add_le _ _

theorem l1_neg (F : ℚ[X]) : l1 (-F) = l1 F := by
  rw [l1_eq_sum_support, l1_eq_sum_support, support_neg]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_neg]; push_cast; exact abs_neg _

theorem l1_sum_le {α : Type*} (s : Finset α) (F : α → ℚ[X]) :
    l1 (∑ a ∈ s, F a) ≤ ∑ a ∈ s, l1 (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (l1_add_le _ _).trans (by linarith)

theorem l1_monomial (i : ℕ) (c : ℚ) : l1 (monomial i c) = |(c : ℝ)| := by
  classical
  rw [l1_eq_sum_of_superset _ {i} (support_monomial' i c), sum_singleton, coeff_monomial,
    if_pos rfl]

theorem l1_C (c : ℚ) : l1 (C c) = |(c : ℝ)| := by
  rw [← monomial_zero_left, l1_monomial]

theorem l1_C_mul_X (c : ℚ) : l1 (C c * X) = |(c : ℝ)| := by
  rw [C_mul_X_eq_monomial, l1_monomial]

theorem l1_mul_le (F G : ℚ[X]) : l1 (F * G) ≤ l1 F * l1 G := by
  classical
  conv_lhs => rw [F.as_sum_support, G.as_sum_support, Finset.sum_mul_sum]
  refine (l1_sum_le _ _).trans ?_
  rw [l1_eq_sum_support F, l1_eq_sum_support G, Finset.sum_mul_sum]
  refine sum_le_sum fun i _ => (l1_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  rw [monomial_mul_monomial, l1_monomial]; push_cast; rw [abs_mul]

theorem l1_one : l1 (1 : ℚ[X]) = 1 := by rw [← C_1, l1_C]; simp

theorem l1_prod_le {α : Type*} (s : Finset α) (F : α → ℚ[X]) :
    l1 (∏ a ∈ s, F a) ≤ ∏ a ∈ s, l1 (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1_nonneg _))

theorem l1_zsmul (u : ℤˣ) (F : ℚ[X]) : l1 (u • F) = l1 F := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul, l1_neg]

/-- **Determinant bound**: if every entry has `‖M_{ij}‖₁ ≤ A` then
`‖det M‖₁ ≤ (card ι)! · A^{card ι}`. -/
theorem l1_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) (A : ℝ)
    (hM : ∀ i j, l1 (M i j) ≤ A) :
    l1 M.det ≤ (Fintype.card ι).factorial * A ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (l1_sum_le _ _).trans ?_
  have h1 : ∀ σ : Equiv.Perm ι, l1 (Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤ A ^ Fintype.card ι := by
    intro σ
    rw [l1_zsmul]
    refine (l1_prod_le _ _).trans ?_
    calc ∏ i, l1 (M (σ i) i) ≤ ∏ _i : ι, A :=
          prod_le_prod (fun i _ => l1_nonneg _) (fun i _ => hM _ _)
      _ = A ^ Fintype.card ι := by rw [prod_const, card_univ]
  refine (sum_le_sum fun σ _ => h1 σ).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

/-! ### Real multivariate polynomials -/

/-- `‖F‖₁ = ∑_α |F_α|` for `F ∈ ℝ[y_σ]`. -/
noncomputable def mvl1 {σ : Type*} (F : MvPolynomial σ ℝ) : ℝ := ∑ α ∈ F.support, |F.coeff α|

variable {σ : Type*}

theorem mvl1_nonneg (F : MvPolynomial σ ℝ) : 0 ≤ mvl1 F := sum_nonneg fun _ _ => abs_nonneg _

theorem mvl1_eq_sum_of_superset (F : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ))
    (hs : F.support ⊆ s) : mvl1 F = ∑ α ∈ s, |F.coeff α| := by
  unfold mvl1
  refine Finset.sum_subset hs (fun i _ hi => ?_)
  simp only [MvPolynomial.mem_support_iff, not_not] at hi
  simp [hi]

theorem abs_coeff_le_mvl1 (F : MvPolynomial σ ℝ) (α : σ →₀ ℕ) : |F.coeff α| ≤ mvl1 F := by
  classical
  by_cases h : α ∈ F.support
  · exact single_le_sum (f := fun α => |F.coeff α|) (fun _ _ => abs_nonneg _) h
  · simp only [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, abs_zero]; exact mvl1_nonneg F

theorem mvl1_add_le (F G : MvPolynomial σ ℝ) : mvl1 (F + G) ≤ mvl1 F + mvl1 G := by
  classical
  rw [mvl1_eq_sum_of_superset (F + G) (F.support ∪ G.support) MvPolynomial.support_add,
    mvl1_eq_sum_of_superset F (F.support ∪ G.support) subset_union_left,
    mvl1_eq_sum_of_superset G (F.support ∪ G.support) subset_union_right, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [MvPolynomial.coeff_add]; exact abs_add_le _ _

theorem mvl1_zero : mvl1 (0 : MvPolynomial σ ℝ) = 0 := by simp [mvl1]

theorem mvl1_sum_le {α : Type*} (s : Finset α) (F : α → MvPolynomial σ ℝ) :
    mvl1 (∑ a ∈ s, F a) ≤ ∑ a ∈ s, mvl1 (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvl1_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (mvl1_add_le _ _).trans (by linarith)

theorem mvl1_monomial (α : σ →₀ ℕ) (c : ℝ) : mvl1 (MvPolynomial.monomial α c) = |c| := by
  classical
  rw [mvl1_eq_sum_of_superset _ {α} MvPolynomial.support_monomial_subset, sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem mvl1_mul_le (F G : MvPolynomial σ ℝ) : mvl1 (F * G) ≤ mvl1 F * mvl1 G := by
  classical
  conv_lhs => rw [F.as_sum, G.as_sum, Finset.sum_mul_sum]
  refine (mvl1_sum_le _ _).trans ?_
  rw [mvl1, mvl1, Finset.sum_mul_sum]
  refine sum_le_sum fun i _ => (mvl1_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  rw [MvPolynomial.monomial_mul, mvl1_monomial, abs_mul]

theorem mvl1_one : mvl1 (1 : MvPolynomial σ ℝ) = 1 := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', mvl1_monomial, abs_one]

theorem mvl1_prod_le {α : Type*} (s : Finset α) (F : α → MvPolynomial σ ℝ) :
    mvl1 (∏ a ∈ s, F a) ≤ ∏ a ∈ s, mvl1 (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvl1_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (mvl1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (mvl1_nonneg _))

theorem mvl1_C (c : ℝ) : mvl1 (MvPolynomial.C c : MvPolynomial σ ℝ) = |c| := by
  rw [← MvPolynomial.monomial_zero', mvl1_monomial]

theorem mvl1_X (i : σ) : mvl1 (MvPolynomial.X i : MvPolynomial σ ℝ) = 1 := by
  rw [MvPolynomial.X, mvl1_monomial, abs_one]

theorem mvl1_neg (F : MvPolynomial σ ℝ) : mvl1 (-F) = mvl1 F := by
  unfold mvl1
  rw [MvPolynomial.support_neg]
  refine sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_neg, abs_neg]

theorem mvl1_sub_le (F G : MvPolynomial σ ℝ) : mvl1 (F - G) ≤ mvl1 F + mvl1 G := by
  rw [sub_eq_add_neg]; exact (mvl1_add_le _ _).trans (by rw [mvl1_neg])

end Hankel2.ArchB
