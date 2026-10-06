import RequestProject.Zeta35.Analytic3
import RequestProject.Zeta35.Bhargava3

/-!
# The entry bound of N, Theorem 3.1

For `a ∈ {1, 2}` and `t ∈ ℤ₃`, `W(t + a/3) = 3^{4(2R+1)} ∏_k (a + 3k + 3t)^{-4}`, and the factor
`∏_k (a + 3k + 3t)^{-4}` is admissible (`3 ∤ a + 3k`).  Hence if `P` has degree `≤ D` and is
`3`-integral at the points `t + a/3`, `t ∈ ℕ`, then
`‖∫_{ℤ₃} (P W)'(t + a/3) dt‖ ≤ 3^{-4(2R+1)} · D · (D + 1)` (`norm_volkInt_le`), and the same bound
holds for `L(P)` (`norm_L_le`).
-/

open Filter Finset Topology Polynomial

namespace Zeta35.M3

open Hankel2

/-- The admissible factor `Φ_a(u) = ∏_k ((a + 3k) + 3u)^{-4}`. -/
noncomputable def PhiA (n a : ℕ) (u : ℚ_[3]) : ℚ_[3] :=
  ∏ k ∈ nodes n, ((((a : ℤ) + 3 * k : ℤ) : ℚ_[3]) + 3 * u)⁻¹ ^ 4

theorem adm_PhiA (n a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) : Adm (PhiA n a) := by
  unfold PhiA
  refine Adm.prod _ fun k _ => (Adm.phi _ ?_).pow 4
  omega

theorem W_eq_PhiA (n a : ℕ) (s : ℚ_[3]) :
    W n s = (3 : ℚ_[3]) ^ (4 * (nodes n).card) * PhiA n a (s - (a : ℚ_[3]) / 3) := by
  unfold W PhiA
  rw [pow_mul, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : (((a : ℤ) + 3 * k : ℤ) : ℚ_[3]) + 3 * (s - (a : ℚ_[3]) / 3) = 3 * (s + k) := by
    push_cast; ring
  rw [e, mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (three_ne_zero), one_pow,
    one_mul, inv_pow]

/-- **The entry bound** for one residue class. -/
theorem norm_volkInt_le (n a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (P : ℚ[X]) {D : ℕ} (hD : 1 ≤ D)
    (hP : P.natDegree ≤ D) (hint : ∀ t : ℕ, ∃ m : ℤ, P.eval ((t : ℚ) + a / 3) = m) :
    ‖volkInt 3 (fun t => deriv (fun s => aeval s P * W n s) (t + (a : ℚ_[3]) / 3))‖ ≤
      (3 : ℝ)⁻¹ ^ (4 * (nodes n).card) * D * (D + 1) := by
  set c : ℚ_[3] := (3 : ℚ_[3]) ^ (4 * (nodes n).card)
  set a' : ℚ_[3] := (a : ℚ_[3]) / 3
  set Q0 : ℚ_[3][X] := (P.map (algebraMap ℚ ℚ_[3])).comp (X + C a')
  set Q : ℚ_[3][X] := C c * Q0
  have hQ0deg : Q0.natDegree ≤ D := by
    refine (natDegree_comp_le).trans ?_
    have h1 : (X + C a').natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans ?_; simp
    calc (P.map (algebraMap ℚ ℚ_[3])).natDegree * (X + C a').natDegree ≤ P.natDegree * 1 :=
          Nat.mul_le_mul (natDegree_map_le) h1
      _ ≤ D := by omega
  have hQdeg : Q.natDegree ≤ D := (natDegree_C_mul_le _ _).trans hQ0deg
  have hQ0int : ∀ x : ℕ, ‖Q0.eval (x : ℚ_[3])‖ ≤ 1 := by
    intro x
    obtain ⟨m, hm⟩ := hint x
    have e : Q0.eval (x : ℚ_[3]) = algebraMap ℚ ℚ_[3] (P.eval ((x : ℚ) + a / 3)) := by
      simp only [Q0, a', eval_comp, eval_add, eval_X, eval_C, eval_map]
      rw [← eval₂_at_apply]
      congr 1
      simp
    rw [e, hm]
    simpa using Padic.norm_int_le_one m
  have hc : ‖c‖ = (3 : ℝ)⁻¹ ^ (4 * (nodes n).card) := by
    simp only [c, norm_pow, norm_three]
  have hprof : Prof (polyW ‖c‖ D) fun y => Q.eval y := by
    have h1 := (prof_of_norm_le_one hQ0deg hQ0int).const_mul c
    have e : (fun y => Q.eval y) = fun y => c * Q0.eval y := by
      funext y; simp [Q]
    rw [e]
    refine h1.mono fun j => ?_
    unfold polyW; split_ifs <;> simp
  obtain ⟨I, hI, hIn⟩ := exists_hasVolkenborn_deriv Q hD hQdeg (norm_nonneg c) hprof
    (adm_PhiA n a ha1 ha2) a'
  have hfun : (fun s => aeval s P * W n s) = fun s => Q.eval (s - a') * PhiA n a (s - a') := by
    funext s
    rw [W_eq_PhiA n a s]
    simp only [Q, Q0, eval_mul, eval_C, eval_comp, eval_add, eval_X, sub_add_cancel, eval_map,
      aeval_def]
    ring
  rw [hfun, hI.volkInt_eq, ← hc]
  exact hIn

/-- **The entry bound for `L(P)`.** -/
theorem norm_L_le (n : ℕ) (P : ℚ[X]) {D : ℕ} (hD : 1 ≤ D) (hP : P.natDegree ≤ D)
    (hint : ∀ a : ℕ, 1 ≤ a → a ≤ 2 → ∀ t : ℕ, ∃ m : ℤ, P.eval ((t : ℚ) + a / 3) = m) :
    ‖L n P‖ ≤ (3 : ℝ)⁻¹ ^ (4 * (nodes n).card) * D * (D + 1) := by
  unfold L
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun a ha => ?_
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  exact norm_volkInt_le n a ha1 ha2 P hD hP (hint a ha1 ha2)

end Zeta35.M3
