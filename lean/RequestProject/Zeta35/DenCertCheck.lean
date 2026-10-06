import RequestProject.Zeta35.DenCount2

/-!
# Denominators (N, Theorem 5.1), step 8: the certificate checker

A certificate is a chain of subcells `[a, b] ⊆ [1/20, 5]` (`a` = the previous `b`), each with a
record `(b, λ, h, q, br, S₀)`: `λ ≥ 0`, `h ≥ 0`, the integer `q` with `qb ≤ 3 ≤ (q + 1)a`, the
branch `br` of the circle model on `[a, b]`, and for each of the four class types a local maximum
`S₀,i` certifying `ψ(N_i, b_i, λ) ≤ P_i := V(N_i, b_i, S₀,i) − λ S₀,i` (`psiT_le_of_locOK`).
The check (`subOK`) asks, at both ends `u ∈ {a, b}`, `meas_i(u) ≥ 0`, the branch sign, and

  `6λ + ∑_i meas_i(u) P_i ≤ h`.

All these quantities are affine in `u`, so (**`subOK_sound`**) they hold on all of `[a, b]`.
-/

open Finset

namespace Zeta35.Den

/-- A subcell record `(b, λ, h, q, br, [S₀,₀, S₀,₁, S₀,₂, S₀,₃])`. -/
abbrev SubRec := ℚ × ℚ × ℚ × ℕ × Bool × List ℕ

/-- The certified upper bounds `P_i` of `ψ(N_i, b_i, λ)`. -/
def PQ (r : SubRec) (i : Fin 4) : ℚ := fQ (typN r.2.2.2.1 i) (typB i) r.2.1 (r.2.2.2.2.2.getD i 0)

/-- `∑_i meas_i(u) P_i` over `ℚ`. -/
def GQ (r : SubRec) (u : ℚ) : ℚ := ∑ i : Fin 4, measF r.2.2.2.1 r.2.2.2.2.1 u i * PQ r i

/-- The check at one end `u`. -/
def endOK (r : SubRec) (u : ℚ) : Bool :=
  (if r.2.2.2.2.1 then decide (0 ≤ sgnF r.2.2.2.1 u) else decide (sgnF r.2.2.2.1 u ≤ 0)) &&
    decide (∀ i : Fin 4, 0 ≤ measF r.2.2.2.1 r.2.2.2.2.1 u i) &&
    decide (6 * r.2.1 + GQ r u ≤ r.2.2.1)

/-- The check of one subcell `[a, b]`. -/
def subOK (a : ℚ) (r : SubRec) : Bool :=
  decide (0 < a) && decide (a < r.1) && decide (0 ≤ r.2.1) && decide (0 ≤ r.2.2.1) &&
    decide (r.2.2.2.1 * r.1 ≤ 3) && decide (3 ≤ (r.2.2.2.1 + 1) * a) &&
    decide (∀ i : Fin 4, locOK (typN r.2.2.2.1 i) (typB i) r.2.1 (r.2.2.2.2.2.getD i 0) = true) &&
    endOK r a && endOK r r.1

/-! ### Soundness -/

theorem measF_cast (q : ℕ) (br : Bool) (u : ℚ) (i : Fin 4) :
    ((measF q br u i : ℚ) : ℝ) = measF q br (u : ℝ) i := by
  unfold measF
  split_ifs <;> fin_cases i <;> simp

theorem sgnF_cast (q : ℕ) (u : ℚ) : ((sgnF q u : ℚ) : ℝ) = sgnF q (u : ℝ) := by
  unfold sgnF; split_ifs <;> push_cast <;> ring

theorem measF_affine (q : ℕ) (br : Bool) (i : Fin 4) (u : ℝ) :
    measF q br u i = measF q br (0 : ℝ) i + (measF q br (1 : ℝ) i - measF q br (0 : ℝ) i) * u := by
  unfold measF
  split_ifs <;> fin_cases i <;> simp <;> ring

theorem sgnF_affine (q : ℕ) (u : ℝ) :
    sgnF q u = sgnF q (0 : ℝ) + (sgnF q (1 : ℝ) - sgnF q (0 : ℝ)) * u := by
  unfold sgnF; split_ifs <;> ring

/-- An affine function bounded above at both ends is bounded above in between. -/
theorem affine_le {f : ℝ → ℝ} (hf : ∀ u, f u = f 0 + (f 1 - f 0) * u) {a b u M : ℝ}
    (ha : a ≤ u) (hb : u ≤ b) (h1 : f a ≤ M) (h2 : f b ≤ M) : f u ≤ M := by
  rw [hf] at h1 h2 ⊢
  rcases le_total 0 (f 1 - f 0) with h | h
  · have := mul_le_mul_of_nonneg_left hb h; linarith
  · have := mul_le_mul_of_nonpos_left ha h; linarith

theorem affine_ge {f : ℝ → ℝ} (hf : ∀ u, f u = f 0 + (f 1 - f 0) * u) {a b u M : ℝ}
    (ha : a ≤ u) (hb : u ≤ b) (h1 : M ≤ f a) (h2 : M ≤ f b) : M ≤ f u := by
  have := affine_le (f := fun u => -f u) (fun u => by simp only; rw [hf u]; ring) ha hb
    (M := -M) (by simp only; linarith) (by simp only; linarith)
  simp only at this; linarith

/-- The real-valued `∑_i meas_i(u) P_i`. -/
noncomputable def GR (r : SubRec) (u : ℝ) : ℝ :=
  ∑ i : Fin 4, measF r.2.2.2.1 r.2.2.2.2.1 u i * (PQ r i : ℝ)

theorem GR_cast (r : SubRec) (u : ℚ) : ((GQ r u : ℚ) : ℝ) = GR r (u : ℝ) := by
  unfold GQ GR; push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [measF_cast]

theorem GR_affine (r : SubRec) (u : ℝ) : GR r u = GR r 0 + (GR r 1 - GR r 0) * u := by
  unfold GR
  simp only [Fin.sum_univ_four]
  rw [measF_affine _ _ 0 u, measF_affine _ _ 1 u, measF_affine _ _ 2 u, measF_affine _ _ 3 u]
  ring

/-- **Soundness of the subcell check.** -/
theorem subOK_sound {a : ℚ} {r : SubRec} (h : subOK a r = true) :
    0 < a ∧ a < r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2.1 ∧
    (∀ i : Fin 4, psiT (typN r.2.2.2.1 i) (typB i) (r.2.1 : ℝ) ≤ (PQ r i : ℝ)) ∧
    ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (r.1 : ℝ) →
      (r.2.2.2.1 : ℝ) * u ≤ 3 ∧ 3 ≤ ((r.2.2.2.1 : ℝ) + 1) * u ∧
      (r.2.2.2.2.1 = true → 0 ≤ sgnF r.2.2.2.1 u) ∧ (r.2.2.2.2.1 = false → sgnF r.2.2.2.1 u ≤ 0) ∧
      (∀ i : Fin 4, 0 ≤ measF r.2.2.2.1 r.2.2.2.2.1 u i) ∧
      6 * (r.2.1 : ℝ) + GR r u ≤ (r.2.2.1 : ℝ) := by
  simp only [subOK, endOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha0, hab⟩, hlam⟩, hh⟩, hq1⟩, hq2⟩, hloc⟩, ⟨⟨hsa, hma⟩, hGa⟩⟩, ⟨⟨hsb, hmb⟩, hGb⟩⟩ := h
  refine ⟨ha0, hab, hlam, hh, fun i => ?_, fun u hu1 hu2 => ?_⟩
  · have := psiT_le_of_locOK (hloc i)
    unfold PQ; exact this
  set q := r.2.2.2.1
  set br := r.2.2.2.2.1
  have hq1' : (q : ℝ) * (r.1 : ℝ) ≤ 3 := by exact_mod_cast hq1
  have hq2' : 3 ≤ ((q : ℝ) + 1) * (a : ℝ) := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) ≤ q := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hu2 hq0; linarith
  · have := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ q + 1); linarith
  · intro hbr
    rw [hbr] at hsa hsb
    simp only [if_true, decide_eq_true_eq] at hsa hsb
    refine affine_ge (sgnF_affine q) hu1 hu2 ?_ ?_
    · rw [← sgnF_cast]; exact_mod_cast hsa
    · rw [← sgnF_cast]; exact_mod_cast hsb
  · intro hbr
    rw [hbr] at hsa hsb
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hsa hsb
    refine affine_le (sgnF_affine q) hu1 hu2 ?_ ?_
    · rw [← sgnF_cast]; exact_mod_cast hsa
    · rw [← sgnF_cast]; exact_mod_cast hsb
  · intro i
    refine affine_ge (fun u => measF_affine q br i u) hu1 hu2 ?_ ?_
    · rw [← measF_cast]; exact_mod_cast hma i
    · rw [← measF_cast]; exact_mod_cast hmb i
  · have h1 : GR r a ≤ r.2.2.1 - 6 * r.2.1 := by
      rw [← GR_cast]; have := (Rat.cast_le (K := ℝ)).2 hGa; push_cast at this ⊢; linarith
    have h2 : GR r r.1 ≤ r.2.2.1 - 6 * r.2.1 := by
      rw [← GR_cast]; have := (Rat.cast_le (K := ℝ)).2 hGb; push_cast at this ⊢; linarith
    have := affine_le (GR_affine r) hu1 hu2 h1 h2
    linarith

/-! ### Chains of subcells -/

/-- Check of a chain of subcells starting at `a`. -/
def chainOK : ℚ → List SubRec → Bool
  | _, [] => true
  | a, r :: rs => subOK a r && chainOK r.1 rs

/-- The right end of a chain. -/
def lastB : ℚ → List SubRec → ℚ
  | a, [] => a
  | _, r :: rs => lastB r.1 rs

/-- `∑ h (b − a)` over a chain. -/
def stepSum : ℚ → List SubRec → ℚ
  | _, [] => 0
  | a, r :: rs => r.2.2.1 * (r.1 - a) + stepSum r.1 rs

/-- The cells `(a, r)` of a chain. -/
def cells : ℚ → List SubRec → List (ℚ × SubRec)
  | _, [] => []
  | a, r :: rs => (a, r) :: cells r.1 rs

theorem chainOK_append (a : ℚ) (l₁ l₂ : List SubRec) :
    chainOK a (l₁ ++ l₂) = (chainOK a l₁ && chainOK (lastB a l₁) l₂) := by
  induction l₁ generalizing a with
  | nil => simp [chainOK, lastB]
  | cons r rs ih => simp [chainOK, lastB, ih, Bool.and_assoc]

theorem lastB_append (a : ℚ) (l₁ l₂ : List SubRec) :
    lastB a (l₁ ++ l₂) = lastB (lastB a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem stepSum_append (a : ℚ) (l₁ l₂ : List SubRec) :
    stepSum a (l₁ ++ l₂) = stepSum a l₁ + stepSum (lastB a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [stepSum, lastB]
  | cons r rs ih => simp [stepSum, lastB, ih]; ring

theorem subOK_of_mem_cells {a : ℚ} {l : List SubRec} (h : chainOK a l = true) :
    ∀ c ∈ cells a l, subOK c.1 c.2 = true := by
  induction l generalizing a with
  | nil => simp [cells]
  | cons r rs ih =>
    simp only [chainOK, Bool.and_eq_true] at h
    intro c hc
    simp only [cells, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.1
    · exact ih h.2 c hc

theorem le_lastB {a : ℚ} {l : List SubRec} (h : chainOK a l = true) : a ≤ lastB a l := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons r rs ih =>
    simp only [chainOK, Bool.and_eq_true] at h
    have := (subOK_sound h.1).2.1
    exact this.le.trans (ih h.2)

/-- A block of a certificate: checked chain, its end, and a bound on its step sum. -/
def Blk (a : ℚ) (l : List SubRec) (c S : ℚ) : Prop :=
  chainOK a l = true ∧ lastB a l = c ∧ stepSum a l ≤ S

theorem blk_app {a b c S₁ S₂ : ℚ} {l r : List SubRec} (hl : Blk a l b S₁) (hr : Blk b r c S₂) :
    Blk a (l ++ r) c (S₁ + S₂) := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h4, h5, h6⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rw [chainOK_append, h1, h2, h4]; rfl
  · rw [lastB_append, h2, h5]
  · rw [stepSum_append, h2]; linarith

end Zeta35.Den
