import RequestProject.Zeta35.InputDefs

/-!
# The Bhargava basis for `S = 3⁻¹ ℤ₃^×` (N, Theorem 3.1; CLAIMS T4)

Let `a_0, a_1, … = 1, 2, 4, 5, 7, 8, …` be the positive integers prime to `3` in increasing order
(`aSeq j = 3⌊j/2⌋ + (j mod 2) + 1`), so that `a_{j + 2·3^e} = a_j + 3^{e+1}`.

* `count_ge`: for `y` prime to `3`, `#{j < i : 3^{e+1} | y − a_j} ≥ ⌊i/(2·3^e)⌋` (each block of
  `2·3^e` consecutive `a_j` covers every unit residue mod `3^{e+1}`).
* `pow_dvd_prod`: hence `3^{eS i} | ∏_{j<i} (y − a_j)` with `eS i = ∑_{e ≥ 0} ⌊i/(2·3^e)⌋`
  (`= i + v₃(i!_S)`).
* `bhPoly i = 3^{−eS i} ∏_{j<i} (3x − a_j)` (`C_i(x) = B_i(3x)` up to a `3`-adic unit): degree `i`,
  leading coefficient `3^{i − eS i}` of `3`-adic norm `3^{v₃(i!_S)}`, and **integer-valued** at
  every `t + a/3`, `t ∈ ℕ`, `a ∈ {1, 2}` (`bhPoly_eval_int`).
-/

open Polynomial Finset

namespace Zeta35.Bh

/-- The positive integers prime to `3` in increasing order: `1, 2, 4, 5, 7, 8, …`. -/
def aSeq (j : ℕ) : ℕ := 3 * (j / 2) + j % 2 + 1

/-- `eS i = ∑_{e ≤ i} ⌊i/(2·3^e)⌋ = i + v₃(i!_S)`. -/
def eS (i : ℕ) : ℕ := ∑ e ∈ range (i + 1), i / (2 * 3 ^ e)

theorem vS_eq (i : ℕ) : vS i = -(i : ℤ) + eS i := by
  unfold vS eS; push_cast; ring

theorem aSeq_block (e b r : ℕ) : aSeq (b * (2 * 3 ^ e) + r) = aSeq r + b * 3 ^ (e + 1) := by
  unfold aSeq
  have h1 : (b * (2 * 3 ^ e) + r) / 2 = b * 3 ^ e + r / 2 := by
    rw [show b * (2 * 3 ^ e) + r = r + 2 * (b * 3 ^ e) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
    ring
  have h2 : (b * (2 * 3 ^ e) + r) % 2 = r % 2 := by
    rw [show b * (2 * 3 ^ e) + r = r + 2 * (b * 3 ^ e) by ring, Nat.add_mul_mod_self_left]
  rw [h1, h2, pow_succ]; ring

/-- Every unit residue mod `3^{e+1}` is some `a_r`, `r < 2·3^e`. -/
theorem exists_residue (e : ℕ) (y : ℤ) (hy : ¬ (3 : ℤ) ∣ y) :
    ∃ r < 2 * 3 ^ e, (3 : ℤ) ^ (e + 1) ∣ y - aSeq r := by
  set m : ℤ := (3 : ℤ) ^ (e + 1) with hm
  have hm0 : 0 < m := by positivity
  set ρ : ℤ := y % m with hρ
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ hm0.ne'
  have hρm : ρ < m := Int.emod_lt_of_pos _ hm0
  have hρ3 : ¬ (3 : ℤ) ∣ ρ := by
    intro h
    apply hy
    have h3m : (3 : ℤ) ∣ m := by rw [hm, pow_succ]; exact dvd_mul_left _ _
    have := Int.emod_add_mul_ediv y m
    rw [← this]
    exact dvd_add h (dvd_mul_of_dvd_left h3m _)
  lift ρ to ℕ using hρ0 with ρn hρn
  have hρn3 : ρn % 3 ≠ 0 := by
    intro h; apply hρ3; exact_mod_cast Nat.dvd_of_mod_eq_zero h
  have hm' : (m : ℤ) = ((3 ^ (e + 1) : ℕ) : ℤ) := by rw [hm]; push_cast; ring
  have hρlt : ρn < 3 ^ (e + 1) := by
    have : (ρn : ℤ) < ((3 ^ (e + 1) : ℕ) : ℤ) := by rw [← hm']; exact hρm
    exact_mod_cast this
  refine ⟨2 * (ρn / 3) + (ρn % 3 - 1), ?_, ?_⟩
  · rw [pow_succ] at hρlt
    have : ρn / 3 < 3 ^ e := by omega
    omega
  · have ha : aSeq (2 * (ρn / 3) + (ρn % 3 - 1)) = ρn := by
      unfold aSeq; omega
    rw [ha, hρn]
    exact ⟨y / m, by have := Int.emod_add_mul_ediv y m; linarith⟩

/-- **The counting lemma.** -/
theorem count_ge (e i : ℕ) (y : ℤ) (hy : ¬ (3 : ℤ) ∣ y) :
    i / (2 * 3 ^ e) ≤ ((range i).filter (fun j => (3 : ℤ) ^ (e + 1) ∣ y - aSeq j)).card := by
  obtain ⟨r, hr, hdvd⟩ := exists_residue e y hy
  set N := 2 * 3 ^ e with hN
  have hN0 : 0 < N := by positivity
  rw [← Finset.card_range (i / N)]
  refine Finset.card_le_card_of_injOn (fun b => b * N + r) ?_ ?_
  · intro b hb
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · have h1 : (b + 1) * N ≤ i := by
        have := (Nat.lt_div_iff_mul_lt hN0).1 hb
        have h2 : (b + 1) * N ≤ i / N * N := Nat.mul_le_mul_right _ hb
        exact h2.trans (Nat.div_mul_le_self i N)
      nlinarith
    · rw [hN, aSeq_block]
      push_cast
      have : y - ((aSeq r : ℤ) + (b : ℤ) * 3 ^ (e + 1)) = (y - aSeq r) - b * 3 ^ (e + 1) := by
        ring
      rw [this]
      exact dvd_sub hdvd (dvd_mul_left _ _)
  · intro b _ b' _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hN0 (by omega)

/-- `3^{#{e < E : 3^{e+1} | z}} | z`. -/
theorem pow_card_dvd (E : ℕ) (z : ℤ) :
    (3 : ℤ) ^ ((range E).filter (fun e => (3 : ℤ) ^ (e + 1) ∣ z)).card ∣ z := by
  set s := (range E).filter (fun e => (3 : ℤ) ^ (e + 1) ∣ z)
  rcases s.eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty, pow_zero]; exact one_dvd _
  · set m := s.max' h
    have hm : m ∈ s := s.max'_mem h
    have hdvd : (3 : ℤ) ^ (m + 1) ∣ z := (Finset.mem_filter.mp hm).2
    have hcard : s.card ≤ m + 1 := by
      have : s ⊆ range (m + 1) := fun e he => Finset.mem_range.mpr
        (Nat.lt_succ_of_le (s.le_max' e he))
      simpa using Finset.card_le_card this
    exact (pow_dvd_pow 3 hcard).trans hdvd

/-- **`3^{eS i} | ∏_{j<i} (y − a_j)`** for `y` prime to `3`. -/
theorem pow_dvd_prod (i : ℕ) (y : ℤ) (hy : ¬ (3 : ℤ) ∣ y) :
    (3 : ℤ) ^ eS i ∣ ∏ j ∈ range i, (y - aSeq j) := by
  set c : ℕ → ℕ := fun j =>
    ((range (i + 1)).filter (fun e => (3 : ℤ) ^ (e + 1) ∣ y - aSeq j)).card with hc
  have h1 : (3 : ℤ) ^ (∑ j ∈ range i, c j) ∣ ∏ j ∈ range i, (y - aSeq j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => pow_card_dvd _ _
  have h2 : ∑ j ∈ range i, c j = ∑ e ∈ range (i + 1),
      ((range i).filter (fun j => (3 : ℤ) ^ (e + 1) ∣ y - aSeq j)).card := by
    simp only [hc, Finset.card_filter]
    exact Finset.sum_comm
  have h3 : eS i ≤ ∑ j ∈ range i, c j := by
    rw [h2]; unfold eS
    exact Finset.sum_le_sum fun e _ => count_ge e i y hy
  exact (pow_dvd_pow 3 h3).trans h1

/-! ### The basis polynomials -/

/-- `C_i(x) = 3^{−eS i} ∏_{j<i} (3x − a_j)`. -/
noncomputable def bhPoly (i : ℕ) : ℚ[X] :=
  C (((3 : ℚ) ^ eS i)⁻¹) * ∏ j ∈ range i, (C 3 * X - C (aSeq j : ℚ))

theorem natDegree_bhPoly (i : ℕ) : (bhPoly i).natDegree = i := by
  unfold bhPoly
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ (by norm_num))), natDegree_prod _ _ fun j _ => ?_]
  · simp only [natDegree_sub_C, natDegree_C_mul_X _ (three_ne_zero : (3 : ℚ) ≠ 0)]
    simp
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp at this

theorem leading_bhPoly (i : ℕ) : (bhPoly i).coeff i = (3 : ℚ) ^ i * ((3 : ℚ) ^ eS i)⁻¹ := by
  have hlead : (∏ j ∈ range i, (C 3 * X - C (aSeq j : ℚ))).leadingCoeff = 3 ^ i := by
    rw [leadingCoeff_prod]
    have : ∀ j ∈ range i, (C 3 * X - C (aSeq j : ℚ)).leadingCoeff = 3 := by
      intro j _
      rw [leadingCoeff_sub_of_degree_lt]
      · simp
      · simp only [degree_C_mul_X (three_ne_zero : (3 : ℚ) ≠ 0)]
        exact lt_of_le_of_lt degree_C_le (by decide)
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range]
  have hdeg : (∏ j ∈ range i, (C 3 * X - C (aSeq j : ℚ))).natDegree = i := by
    have := natDegree_bhPoly i
    unfold bhPoly at this
    rwa [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ (by norm_num)))] at this
  unfold bhPoly
  rw [coeff_C_mul]
  have : (∏ j ∈ range i, (C 3 * X - C (aSeq j : ℚ))).coeff i = 3 ^ i := by
    rw [← hlead, Polynomial.leadingCoeff, hdeg]
  rw [this]; ring

theorem bhPoly_coeff_eq_zero {i a : ℕ} (h : i < a) : (bhPoly i).coeff a = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_bhPoly]; exact h)

/-- **`C_i` is integer-valued at `t + a/3`** (`t ∈ ℕ`, `a ∈ {1,2}`). -/
theorem bhPoly_eval_int (i t a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    ∃ m : ℤ, (bhPoly i).eval ((t : ℚ) + a / 3) = m := by
  have hy : ¬ (3 : ℤ) ∣ (3 * t + a : ℤ) := by omega
  obtain ⟨m, hm⟩ := pow_dvd_prod i _ hy
  refine ⟨m, ?_⟩
  unfold bhPoly
  rw [eval_mul, eval_C, eval_prod]
  have e : ∏ j ∈ range i, (C 3 * X - C (aSeq j : ℚ)).eval ((t : ℚ) + a / 3) =
      ((∏ j ∈ range i, ((3 * t + a : ℤ) - aSeq j) : ℤ) : ℚ) := by
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring
  rw [e, hm]
  push_cast
  field_simp

end Zeta35.Bh
