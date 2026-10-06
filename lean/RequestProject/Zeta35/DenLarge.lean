import RequestProject.Zeta35.DenCertCheck
import RequestProject.Zeta7.Hankel2.PrimeSums

/-!
# Denominators (N, Theorem 5.1), step 9: primes `ℓ > n/20` from a checked subcell

**`TPplus_le_cell`**: if `ℓ/n` lies in a checked subcell `(a, b]` with record `(b, λ, h, …)`,
`a ≥ 1/20`, `n > 1800` even and `K ≤ 6n`, then `max(T_ℓ, 0) ≤ n h + E` with the absolute constant
`E = 9 · 251²` (weak duality `TP_le_psi`, the class sum `sum_psi_le`, and the check `subOK`).

**`sum_cells_le`**: over a checked chain, the primes `ℓ ∈ (a₀ n, b_last n]` contribute at most
`∑_cells (n h + E)(θ(b n) − θ(a n))`.
-/

open Finset Chebyshev

namespace Zeta35.Den

/-- The absolute constant `E = 9 · 251²` of the large-prime bound. -/
def Ecst : ℝ := 9 * 251 ^ 2

theorem TPplus_nonneg3 (p n K : ℕ) : (0 : ℝ) ≤ TPplus p n K := by
  unfold TPplus
  induction h : TP p n K with
  | bot => simp
  | coe t =>
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simp
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]; simpa using ht

/-- **A prime `ℓ > n/20` in a checked subcell.** -/
theorem TPplus_le_cell {n K ℓ : ℕ} (hn : Even n) (hn0 : 1800 < n) (hK : K ≤ 6 * n)
    (hℓ : ℓ.Prime) {a : ℚ} {r : SubRec} (hok : subOK a r = true) (ha20 : (1 / 20 : ℝ) ≤ a)
    (h1 : (a : ℝ) < (ℓ : ℝ) / n) (h2 : (ℓ : ℝ) / n ≤ r.1) :
    (TPplus ℓ n K : ℝ) ≤ n * (r.2.2.1 : ℝ) + Ecst := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ha0, hab, hlam, hh, hψP, hu⟩ := subOK_sound hok
  have hn0' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh' : (0 : ℝ) ≤ r.2.2.1 := by exact_mod_cast hh
  have hlam' : (0 : ℝ) ≤ r.2.1 := by exact_mod_cast hlam
  have hE : (0 : ℝ) ≤ Ecst := by unfold Ecst; positivity
  have hB : 0 ≤ (n : ℝ) * r.2.2.1 + Ecst := by positivity
  by_cases hbig : 9 * n < 2 * ℓ
  · rw [TPplus_eq_zero_of_large3 hbig K]; simpa using hB
  push_neg at hbig
  have h20 : (n : ℝ) < 20 * ℓ := by
    have := (lt_div_iff₀ hn0').1 (lt_of_le_of_lt ha20 h1); linarith
  have h20' : n < 20 * ℓ := by exact_mod_cast h20
  have h9 : 9 * n < 2 * ℓ ^ 2 := by nlinarith
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨hqu1, hqu2, hbr1, hbr2, hmeas, hG⟩ := hu ((ℓ : ℝ) / n) h1.le h2
  set q := r.2.2.2.1
  set br := r.2.2.2.2.1
  set lam : ℝ := (r.2.1 : ℝ)
  have hq1 : q * ℓ ≤ 3 * n := by
    have : (q : ℝ) * ℓ ≤ 3 * n := by
      have := mul_le_mul_of_nonneg_right hqu1 hn0'.le
      rwa [mul_assoc, div_mul_cancel₀ _ hn0'.ne'] at this
    exact_mod_cast this
  have hq2 : 3 * n ≤ (q + 1) * ℓ := by
    have : 3 * (n : ℝ) ≤ ((q : ℝ) + 1) * ℓ := by
      have := mul_le_mul_of_nonneg_right hqu2 hn0'.le
      rwa [mul_assoc, div_mul_cancel₀ _ hn0'.ne'] at this
    exact_mod_cast this
  have hq60 : q ≤ 60 := by
    have hq1' : (q : ℝ) * r.1 ≤ 3 := by
      have := (subOK_sound hok).2.2.2.2.2 r.1 (by exact_mod_cast hab.le) le_rfl
      exact this.1
    have hb20 : (1 / 20 : ℝ) < r.1 := lt_of_le_of_lt ha20 (by exact_mod_cast hab)
    have : (q : ℝ) * (1 / 20) ≤ 3 := by
      have := mul_le_mul_of_nonneg_left hb20.le (by positivity : (0 : ℝ) ≤ q); linarith
    have : (q : ℝ) ≤ 60 := by linarith
    exact_mod_cast this
  have hsum := sum_psi_le hℓ2 hn (by omega) hq1 hq2 (by omega) br hbr1 hbr2 hlam'
  -- the type bounds
  have hψsq : ∀ (N b : ℕ), N ≤ 62 → psiT N b lam ≤ 251 ^ 2 := by
    intro N b hN
    refine (psiT_le_sq N b hlam').trans ?_
    have : (N : ℝ) ≤ 62 := by exact_mod_cast hN
    nlinarith
  have htyp : ∀ i : Fin 4, typN q i ≤ 62 := fun i => by unfold typN; split_ifs <;> omega
  have hterm : ∀ i : Fin 4, ((n : ℝ) * measF q br ((ℓ : ℝ) / n) i + 2) * psiT (typN q i) (typB i) lam
      ≤ (n : ℝ) * (measF q br ((ℓ : ℝ) / n) i * (PQ r i : ℝ)) + 2 * 251 ^ 2 := by
    intro i
    have hm := hmeas i
    have hP := hψP i
    have hs := hψsq (typN q i) (typB i) (htyp i)
    have h0 := psiT_nonneg (typN q i) (typB i) lam
    have : (n : ℝ) * measF q br ((ℓ : ℝ) / n) i * psiT (typN q i) (typB i) lam ≤
        (n : ℝ) * measF q br ((ℓ : ℝ) / n) i * (PQ r i : ℝ) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have hsum2 : ∑ c ∈ range ℓ, psiT (clsF ℓ n c).card (bC ℓ n c) lam ≤
      (n : ℝ) * GR r ((ℓ : ℝ) / n) + 9 * 251 ^ 2 := by
    refine hsum.trans ?_
    have hq2' := hψsq (q + 2) 0 (by omega)
    have := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin 4))) => hterm i
    rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin] at this
    unfold GR
    simp only [nsmul_eq_mul] at this
    push_cast at this
    linarith
  have hK' : lam * K ≤ 6 * lam * n := by
    have : (K : ℝ) ≤ 6 * n := by exact_mod_cast hK
    nlinarith
  refine TPplus_le_of hB fun t ht => ?_
  have := TP_le_psi h9 K lam t ht
  have hG' : (n : ℝ) * (6 * lam + GR r ((ℓ : ℝ) / n)) ≤ n * r.2.2.1 :=
    mul_le_mul_of_nonneg_left hG hn0'.le
  unfold Ecst
  nlinarith

/-! ### Summing over the cells of a chain -/

/-- `∑_cells g(a, r)` over a chain. -/
noncomputable def cellSum (g : ℚ → SubRec → ℝ) : ℚ → List SubRec → ℝ
  | _, [] => 0
  | a, r :: rs => g a r + cellSum g r.1 rs

/-- **Covering the primes by the cells.** If every cell `(a, r)` of a checked chain bounds the
sum of `f` over any set of primes `p ∈ (a n, b n]`, then the sum over a set of
primes in `(a₀ n, b_last n]` is bounded by the sum over the cells. -/
theorem sum_le_cellSum (n : ℝ) (f : ℕ → ℝ) (g : ℚ → SubRec → ℝ) :
    ∀ (l : List SubRec) (a : ℚ), chainOK a l = true →
      (∀ c ∈ cells a l, ∀ Q : Finset ℕ, (∀ p ∈ Q, (c.1 : ℝ) * n < p ∧ (p : ℝ) ≤ c.2.1 * n) →
        ∑ p ∈ Q, f p ≤ g c.1 c.2) →
      ∀ P : Finset ℕ, (∀ p ∈ P, (a : ℝ) * n < p ∧ (p : ℝ) ≤ lastB a l * n) →
        ∑ p ∈ P, f p ≤ cellSum g a l := by
  intro l
  induction l with
  | nil =>
    intro a _ _ P hP
    have : P = ∅ := by
      ext p; simp only [notMem_empty, iff_false]; intro hp
      have := hP p hp; simp only [lastB] at this; linarith
    simp [this, cellSum]
  | cons r rs ih =>
    intro a hch hg P hP
    simp only [chainOK, Bool.and_eq_true] at hch
    rw [← sum_filter_add_sum_filter_not P (fun p => (p : ℝ) ≤ r.1 * n)]
    simp only [cellSum]
    refine add_le_add ?_ ?_
    · refine hg (a, r) (by simp [cells]) _ fun p hp => ?_
      rw [mem_filter] at hp
      exact ⟨(hP p hp.1).1, hp.2⟩
    · refine ih r.1 hch.2 (fun c hc => hg c (by simp [cells, hc])) _ fun p hp => ?_
      rw [mem_filter] at hp
      exact ⟨lt_of_not_ge hp.2, by simpa [lastB] using (hP p hp.1).2⟩

theorem cellSum_add (g₁ g₂ : ℚ → SubRec → ℝ) :
    ∀ (l : List SubRec) (a : ℚ),
      cellSum (fun a r => g₁ a r + g₂ a r) a l = cellSum g₁ a l + cellSum g₂ a l := by
  intro l; induction l with
  | nil => intro a; simp [cellSum]
  | cons r rs ih => intro a; simp only [cellSum, ih]; ring

theorem cellSum_le (g₁ g₂ : ℚ → SubRec → ℝ) :
    ∀ (l : List SubRec) (a : ℚ), (∀ c ∈ cells a l, g₁ c.1 c.2 ≤ g₂ c.1 c.2) →
      cellSum g₁ a l ≤ cellSum g₂ a l := by
  intro l; induction l with
  | nil => intro a _; simp [cellSum]
  | cons r rs ih =>
    intro a h
    simp only [cellSum]
    exact add_le_add (h (a, r) (by simp [cells])) (ih r.1 fun c hc => h c (by simp [cells, hc]))

theorem cellSum_mul (c : ℝ) (g : ℚ → SubRec → ℝ) :
    ∀ (l : List SubRec) (a : ℚ), cellSum (fun a r => c * g a r) a l = c * cellSum g a l := by
  intro l; induction l with
  | nil => intro a; simp [cellSum]
  | cons r rs ih => intro a; simp only [cellSum, ih]; ring

theorem cellSum_telescope (F : ℚ → ℝ) :
    ∀ (l : List SubRec) (a : ℚ), cellSum (fun a r => F r.1 - F a) a l = F (lastB a l) - F a := by
  intro l; induction l with
  | nil => intro a; simp [cellSum, lastB]
  | cons r rs ih => intro a; simp only [cellSum, lastB, ih]; ring

theorem cellSum_stepSum :
    ∀ (l : List SubRec) (a : ℚ),
      cellSum (fun a r => (r.2.2.1 : ℝ) * ((r.1 : ℝ) - a)) a l = (stepSum a l : ℝ) := by
  intro l; induction l with
  | nil => intro a; simp [cellSum, stepSum]
  | cons r rs ih => intro a; simp only [cellSum, stepSum, ih]; push_cast; ring

theorem mem_cells_ge {a : ℚ} {l : List SubRec} (h : chainOK a l = true) :
    ∀ c ∈ cells a l, a ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 ≤ lastB a l := by
  induction l generalizing a with
  | nil => simp [cells]
  | cons r rs ih =>
    simp only [chainOK, Bool.and_eq_true] at h
    have hab := (subOK_sound h.1).2.1
    intro c hc
    simp only [cells, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨le_rfl, hab, le_lastB h.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih h.2 c hc
      exact ⟨hab.le.trans h1, h2, h3⟩

end Zeta35.Den
