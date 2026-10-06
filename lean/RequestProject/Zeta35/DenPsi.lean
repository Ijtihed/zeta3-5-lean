import RequestProject.Zeta35.DenClass

/-!
# Denominators (N, Theorem 5.1), step 5: properties of the class maxima `ψ(N, b, λ)`

* `psiT_mono_N`: `ψ(N, b, λ) ≤ ψ(N', b, λ)` for `N ≤ N'`, `b ≤ 1`, `λ ≥ 0`;
* `psiT_anti_b`: `ψ(N, 1, λ) ≤ ψ(N, 0, λ)`;
* `psiT_le_sq`: `ψ(N, b, λ) ≤ (4N + 3)²` for `λ ≥ 0`;
* `psiT_le_of_locOK`: the maximum is attained at any discrete local maximum `S₀` (the function
  `S ↦ V(N, b, S) − λS` is concave), so a computable local check certifies an upper bound.
-/

open Finset

namespace Zeta35.Den

/-- Discrete concavity: a local maximum on `{0, …, M}` is a global maximum there. -/
theorem le_of_concave_local (f : ℕ → ℝ) (hc : ∀ S, f (S + 2) - f (S + 1) ≤ f (S + 1) - f S)
    (M S0 : ℕ) (hl : S0 = 0 ∨ f (S0 - 1) ≤ f S0)
    (hr : S0 = M ∨ f (S0 + 1) ≤ f S0) : ∀ S ≤ M, f S ≤ f S0 := by
  have hanti : Antitone (fun S => f (S + 1) - f S) :=
    antitone_nat_of_succ_le fun S => by simpa [add_assoc] using hc S
  intro S hS
  rcases le_total S S0 with h | h
  · have tele := Finset.sum_range_sub (fun i => f (S + i)) (S0 - S)
    simp only [Nat.add_sub_cancel' h, add_zero] at tele
    rw [← sub_nonneg, ← tele]
    refine sum_nonneg fun i hi => ?_
    rw [mem_range] at hi
    rcases hl with hl | hl
    · omega
    have h1 : f (S0 - 1 + 1) - f (S0 - 1) ≤ f (S + i + 1) - f (S + i) :=
      hanti (show S + i ≤ S0 - 1 by omega)
    rw [show S0 - 1 + 1 = S0 by omega] at h1
    rw [show S + (i + 1) = S + i + 1 by ring]
    linarith
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [h']
    have tele := Finset.sum_range_sub (fun i => f (S0 + i)) (S - S0)
    simp only [Nat.add_sub_cancel' h, add_zero] at tele
    rw [← sub_nonpos, ← tele]
    refine sum_nonpos fun i _ => ?_
    rcases hr with hr | hr
    · omega
    have h1 : f (S0 + i + 1) - f (S0 + i) ≤ f (S0 + 1) - f S0 := hanti (show S0 ≤ S0 + i by omega)
    rw [show S0 + (i + 1) = S0 + i + 1 by ring]
    linarith

theorem Vt_concave (N b S : ℕ) :
    (Vt N b (S + 2) : ℝ) - Vt N b (S + 1) ≤ Vt N b (S + 1) - Vt N b S := by
  unfold Vt
  split_ifs
  · simp
  · push_cast
    have h1 : (min (S + 2) (4 * (N - b)) : ℕ) ≤ min (S + 1) (4 * (N - b)) + 1 := by omega
    have h2 : (min (S + 1) (4 * (N - b)) : ℕ) + min (S + 1) (4 * (N - b)) ≥
        min (S + 2) (4 * (N - b)) + min S (4 * (N - b)) := by omega
    have h2' : ((min (S + 1) (4 * (N - b)) : ℕ) : ℝ) + ((min (S + 1) (4 * (N - b)) : ℕ) : ℝ) ≥
        ((min (S + 2) (4 * (N - b)) : ℕ) : ℝ) + ((min S (4 * (N - b)) : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h2'
    nlinarith

/-- The computable value `V(N, b, S) − λS`. -/
def fQ (N b : ℕ) (lam : ℚ) (S : ℕ) : ℚ := (Vt N b S : ℚ) - lam * S

/-- The computable local-maximum check at `S₀`. -/
def locOK (N b : ℕ) (lam : ℚ) (S0 : ℕ) : Bool :=
  decide (S0 ≤ 4 * N) && (decide (S0 = 0) || decide (fQ N b lam (S0 - 1) ≤ fQ N b lam S0)) &&
    (decide (S0 = 4 * N) || decide (fQ N b lam (S0 + 1) ≤ fQ N b lam S0))

theorem psiT_le_of_locOK {N b : ℕ} {lam : ℚ} {S0 : ℕ} (h : locOK N b lam S0 = true) :
    psiT N b (lam : ℝ) ≤ (fQ N b lam S0 : ℝ) := by
  simp only [locOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hS0, hl⟩, hr⟩ := h
  set f : ℕ → ℝ := fun S => (Vt N b S : ℝ) - lam * S with hf
  have hfQ : ∀ S, (fQ N b lam S : ℝ) = f S := fun S => by simp [fQ, f]
  have hc : ∀ S, f (S + 2) - f (S + 1) ≤ f (S + 1) - f S := by
    intro S; simp only [f]; push_cast
    have := Vt_concave N b S; linarith
  have hl' : S0 = 0 ∨ f (S0 - 1) ≤ f S0 := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · right; rw [← hfQ, ← hfQ]; exact_mod_cast hl
  have hr' : S0 = 4 * N ∨ f (S0 + 1) ≤ f S0 := by
    rcases hr with hr | hr
    · exact Or.inl hr
    · right; rw [← hfQ, ← hfQ]; exact_mod_cast hr
  have key := le_of_concave_local f hc (4 * N) S0 hl' hr'
  rw [hfQ]
  unfold psiT
  refine sup'_le _ _ fun S hS => ?_
  exact key S (by rw [mem_range] at hS; omega)

theorem psiT_anti_b (N : ℕ) (lam : ℝ) : psiT N 1 lam ≤ psiT N 0 lam := by
  unfold psiT
  refine sup'_le _ _ fun S hS => ?_
  refine le_trans ?_ (le_psiT (N := N) (b := 0) (S := S) (by rw [mem_range] at hS; omega) lam)
  have hS' : S ≤ 4 * N := by rw [mem_range] at hS; omega
  have : (Vt N 1 S : ℝ) ≤ Vt N 0 S := by
    have h0 : ¬ (N = 1 ∧ (0 : ℕ) = 1) := fun h => absurd h.2 (by decide)
    unfold Vt
    rw [if_neg h0]
    by_cases h1 : N = 1 ∧ (1 : ℕ) = 1
    · rw [if_pos h1]
      push_cast
      have : (S : ℝ) ≤ 4 * N := by exact_mod_cast hS'
      have h3 : (0 : ℝ) ≤ min (S : ℝ) (4 * ((N - 0 : ℕ) : ℝ)) := by positivity
      have : (0 : ℝ) ≤ S := by positivity
      nlinarith
    · rw [if_neg h1]
      have : (min S (4 * (N - 1)) : ℕ) ≤ min S (4 * (N - 0)) := by omega
      have : ((min S (4 * (N - 1)) : ℕ) : ℤ) ≤ ((min S (4 * (N - 0)) : ℕ) : ℤ) := by exact_mod_cast this
      exact_mod_cast (by linarith : (4 * N * S + 3 * ((min S (4 * (N - 1)) : ℕ) : ℤ) - (S : ℤ) ^ 2) ≤
        4 * N * S + 3 * ((min S (4 * (N - 0)) : ℕ) : ℤ) - (S : ℤ) ^ 2)
  linarith

theorem psiT_mono_N {N N' b : ℕ} (hN : N ≤ N') (hb : b ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    psiT N b lam ≤ psiT N' b lam := by
  unfold psiT
  refine sup'_le _ _ fun S hS => ?_
  have hS' : S ≤ 4 * N := by rw [mem_range] at hS; omega
  by_cases h0 : (N = 1 ∧ b = 1) ∨ N = 0
  · -- the value is `≤ 0 ≤ ψ`
    have hv : (Vt N b S : ℝ) - lam * S ≤ 0 := by
      rcases h0 with h0 | h0
      · unfold Vt; rw [if_pos h0]; simp; positivity
      · have : S = 0 := by omega
        subst this; simp [Vt]
    exact hv.trans (psiT_nonneg N' b lam)
  · refine le_trans ?_ (le_psiT (N := N') (b := b) (S := S) (by omega) lam)
    have h1 : ¬ (N = 1 ∧ b = 1) := fun h => h0 (Or.inl h)
    have h1' : ¬ (N' = 1 ∧ b = 1) := by
      rintro ⟨hN1, hb1⟩; apply h0; left; refine ⟨?_, hb1⟩; push_neg at h0; omega
    unfold Vt
    rw [if_neg h1, if_neg h1']
    have : (min S (4 * (N - b)) : ℕ) ≤ min S (4 * (N' - b)) := by omega
    have : ((min S (4 * (N - b)) : ℕ) : ℝ) ≤ ((min S (4 * (N' - b)) : ℕ) : ℝ) := by exact_mod_cast this
    have : (N : ℝ) * S ≤ N' * S := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by positivity)
    push_cast at *
    linarith

theorem psiT_le_sq (N b : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) : psiT N b lam ≤ (4 * N + 3) ^ 2 := by
  unfold psiT
  refine sup'_le _ _ fun S hS => ?_
  have hS' : (S : ℝ) ≤ 4 * N := by exact_mod_cast (show S ≤ 4 * N by rw [mem_range] at hS; omega)
  have hS0 : (0 : ℝ) ≤ S := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hv : (Vt N b S : ℝ) ≤ (4 * N + 3) * S := by
    unfold Vt
    split_ifs
    · simp; positivity
    · push_cast
      have : ((min S (4 * (N - b)) : ℕ) : ℝ) ≤ S := by exact_mod_cast min_le_left _ _
      push_cast at this
      nlinarith
  have : lam * S ≥ 0 := by positivity
  nlinarith

end Zeta35.Den
