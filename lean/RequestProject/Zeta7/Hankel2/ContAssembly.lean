import RequestProject.Zeta7.Hankel2.ContQuad
import RequestProject.Zeta7.Hankel2.LogCND

/-!
# Paper Lemmas 6.3–6.4: the discrete energy against a continuum profile

**`EB_le_cont`**: for odd `n`, `κ = K/n ≤ 3`, every feasible `σ` (measurable, `0 ≤ σ ≤ 4`,
`∫_{-1}^{2} σ = κ`) and every integer profile `s` (`0 ≤ s_u ≤ 4`, `∑ s_u = K`),
`E_B(s) ≤ (κ² − 6κ) n² ln n + n² (F[σ] + gap(σ)) + 5000 n (1 + ln n)`.

Proof: linearise the quadratic part of `E_B` at the cell averages `s̃_k = n ∫_{J_k} σ`
(Lemma 6.3, `quadratic_log_le_linearization`, which needs the equal mass `∑ s̃ = K`), so that
`E_B(s) ≤ ∑_k s_k g_k − ⟨s̃, B s̃⟩` with `g_k = ln|h_k| + 2 (B s̃)_k`; then bound `g_k` by the
continuum gradient (`g_le`, `g_le_crude`), the linear term by `P_bound` and the quadratic term
by `Q_bound` (Lemma 6.4).  The error is `O(n log n)`, uniformly in `κ ≤ 3`, `σ` and `s`.
-/

open MeasureTheory Finset

namespace Hankel2.ArchB

open Fam3

/-- The integer-indexed version `k ↦ s_{k+n}` of a profile. -/
noncomputable def sZof (n : ℕ) (s : Fin (3 * n + 1) → ℕ) (k : ℤ) : ℝ :=
  s ⟨(k + n).toNat % (3 * n + 1), Nat.mod_lt _ (by omega)⟩

theorem sZof_node (n : ℕ) (s : Fin (3 * n + 1) → ℕ) (u : Fin (3 * n + 1)) :
    sZof n s (nodeOf n u) = s u := by
  unfold sZof nodeOf
  congr 2
  apply Fin.ext
  simp only
  rw [show ((u : ℤ) - n + n).toNat = u by omega, Nat.mod_eq_of_lt u.isLt]

theorem nodes_eq_insert (n : ℕ) :
    Fam3PF.nodes n = insert (2 * (n : ℤ)) (Ico (-(n : ℤ)) (2 * n)) := by
  ext k; simp only [Fam3PF.nodes, mem_Icc, mem_insert, mem_Ico]; omega

/-- **Paper Lemma 6.3, stated consequence**: for real profiles `s`, `s̃` of equal mass,
`E_B(s) ≤ E_B(s̃) + ⟨g, s − s̃⟩` with `g_u = ln|h_u| + 2 (B s̃)_u`. -/
theorem EB_le_linearization (n : ℕ) (s st : Fin (3 * n + 1) → ℝ) (hmass : ∑ u, s u = ∑ u, st u) :
    EB n s ≤ EB n st + ∑ u, (s u - st u) *
      (Real.log |hR n u| + 2 * ∑ v, Bk ((nodeOf n u : ℝ) - nodeOf n v) * st v) := by
  have h := quadratic_log_le_linearization univ (fun u => (nodeOf n u : ℝ)) s st hmass
  unfold EB
  simp only [Bk] at h ⊢
  have e : ∑ u, (s u - st u) * (Real.log |hR n u| + 2 * ∑ v,
      Real.log (1 + ((nodeOf n u : ℝ) - nodeOf n v) ^ 2) / 2 * st v) =
      ∑ u, s u * Real.log |hR n u| - ∑ u, st u * Real.log |hR n u| +
      2 * ∑ u, (s u - st u) * ∑ v, Real.log (1 + ((nodeOf n u : ℝ) - nodeOf n v) ^ 2) / 2 * st v := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => by ring
  rw [e]
  linarith

/-- The explicit `O(n log n)` error of Lemma 6.4. -/
noncomputable def errC (n : ℕ) : ℝ := 5000 * n * (1 + Real.log n)

theorem EB_le_cont {σ : ℝ → ℝ} {n K : ℕ} (hn : n % 2 = 1) (hF : Feasible ((K : ℝ) / n) σ)
    (hK : (K : ℝ) / n ≤ 3) {s : Fin (3 * n + 1) → ℕ} (hs : s ∈ profiles n K) :
    EB n (fun u => (s u : ℝ)) ≤
      (((K : ℝ) / n) ^ 2 - 6 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n +
        (n : ℝ) ^ 2 * (Fenergy σ + gapF ((K : ℝ) / n) σ) + errC n := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨hσm, hσ, hmass⟩ := hF
  have hmassK : (n : ℝ) * ∫ y in (-1 : ℝ)..2, σ y = K := by rw [hmass]; field_simp
  have hKn : (K : ℝ) ≤ 3 * n := by rwa [div_le_iff₀ hn'] at hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range] at hs
  obtain ⟨hs5, hsK⟩ := hs
  set sr : Fin (3 * n + 1) → ℝ := fun u => (s u : ℝ) with hsr
  set x : Fin (3 * n + 1) → ℝ := fun u => (nodeOf n u : ℝ) with hx
  set w0 : Fin (3 * n + 1) → ℝ := fun u => wZ n σ (nodeOf n u) with hw0
  set sZ := sZof n s with hsZ
  have hsZb : ∀ k, 0 ≤ sZ k ∧ sZ k ≤ 4 := fun k => by
    simp only [hsZ, sZof]
    refine ⟨by positivity, ?_⟩
    have := hs5 ⟨(k + n).toNat % (3 * n + 1), Nat.mod_lt _ (by omega)⟩
    exact_mod_cast (show s _ ≤ 4 by omega)
  have hsumsr : ∑ u, sr u = K := by simp only [hsr]; exact_mod_cast hsK
  have hsumw0 : ∑ u, w0 u = K := by
    simp only [hw0]; rw [← sum_nodes_eq n (wZ n σ), sum_wZ hn0 hσm hσ, hmassK]
  have hlin := quadratic_log_le_linearization univ x sr w0 (by rw [hsumsr, hsumw0])
  -- the kernel in `ℤ` form
  have hB : ∀ u v, Real.log (1 + (x u - x v) ^ 2) / 2 = Bk ((nodeOf n u - nodeOf n v : ℤ) : ℝ) := by
    intro u v; simp only [hx, Bk]; push_cast; rfl
  have hBw : ∀ u, ∑ v, Real.log (1 + (x u - x v) ^ 2) / 2 * w0 v = BwZ n σ (nodeOf n u) := by
    intro u; unfold BwZ; rw [sum_nodes_eq]
    exact sum_congr rfl fun v _ => by rw [hB]
  set Q0 := ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n,
    wZ n σ k * wZ n σ m * Bk ((k - m : ℤ) : ℝ) with hQ0
  have hQ0' : ∑ u, ∑ v, w0 u * w0 v * (Real.log (1 + (x u - x v) ^ 2) / 2) = Q0 := by
    rw [hQ0, sum_nodes_eq]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_nodes_eq]
    exact sum_congr rfl fun v _ => by rw [hB]
  have hcross : ∑ u, (sr u - w0 u) * ∑ v, Real.log (1 + (x u - x v) ^ 2) / 2 * w0 v =
      ∑ u, sr u * BwZ n σ (nodeOf n u) - Q0 := by
    rw [← hQ0']
    simp_rw [hBw, sub_mul, sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun u _ => ?_
    rw [← hBw, mul_sum]; refine sum_congr rfl fun v _ => by ring
  have hEB : EB n sr = ∑ u, sr u * Real.log |hR n u| +
      ∑ u, ∑ v, sr u * sr v * (Real.log (1 + (x u - x v) ^ 2) / 2) := rfl
  -- `E_B(s) ≤ ∑_k s_k g_k − Q0`
  set G : ℤ → ℝ := fun k => Real.log |hZ n k| + 2 * BwZ n σ k with hG
  have hstep1 : EB n sr ≤ ∑ k ∈ Fam3PF.nodes n, sZ k * G k - Q0 := by
    have e : ∑ k ∈ Fam3PF.nodes n, sZ k * G k =
        ∑ u, sr u * Real.log |hR n u| + 2 * ∑ u, sr u * BwZ n σ (nodeOf n u) := by
      rw [sum_nodes_eq, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun u _ => ?_
      simp only [hsZ, sZof_node, hG, hsr, hR, hZ]; ring
    rw [hEB, e]
    linarith
  -- split off the last node
  have hsplit : ∑ k ∈ Fam3PF.nodes n, sZ k * G k =
      sZ (2 * n) * G (2 * n) + ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k * G k := by
    rw [nodes_eq_insert, sum_insert (by simp)]
  have hsumZ : sZ (2 * n) + ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k = K := by
    have : ∑ k ∈ Fam3PF.nodes n, sZ k = K := by
      rw [sum_nodes_eq]; simp only [hsZ, sZof_node]; exact_mod_cast hsK
    rwa [nodes_eq_insert, sum_insert (by simp)] at this
  set S := ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k with hS
  have hS1 : (K : ℝ) - 4 ≤ S := by linarith [(hsZb (2 * n)).2]
  have hS2 : S ≤ K := by linarith [(hsZb (2 * n)).1]
  -- the last node
  have hlast : sZ (2 * n) * G (2 * n) ≤ 104 * n * (1 + Real.log n) := by
    have hg := g_le_crude hn hσm hσ (k := 2 * n)
      (by simp only [Fam3PF.nodes, mem_Icc]; omega)
    rw [hmassK] at hg
    have hB0 : 0 ≤ (6 * n + 1 + 2 * (K : ℝ)) * (2 + Real.log n) := by positivity
    have h1 : sZ (2 * n) * G (2 * n) ≤ 4 * ((6 * n + 1 + 2 * (K : ℝ)) * (2 + Real.log n)) := by
      calc sZ (2 * n) * G (2 * n) ≤ sZ (2 * n) * ((6 * n + 1 + 2 * (K : ℝ)) * (2 + Real.log n)) :=
            mul_le_mul_of_nonneg_left hg (hsZb _).1
        _ ≤ 4 * ((6 * n + 1 + 2 * (K : ℝ)) * (2 + Real.log n)) :=
            mul_le_mul_of_nonneg_right (hsZb _).2 hB0
    have h2 : (6 * n + 1 + 2 * (K : ℝ)) ≤ 13 * n := by linarith
    have h3 : (6 * n + 1 + 2 * (K : ℝ)) * (2 + Real.log n) ≤ 13 * n * (2 + Real.log n) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith [mul_nonneg hn'.le hL]
  -- the interior nodes
  have hint : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), sZ k * G k ≤
      ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
        sZ k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), Pgrad σ x) +
      S * ((2 * K - 6 * n) * Real.log n + 400 * (1 + Real.log n)) := by
    rw [hS, sum_mul, ← sum_add_distrib]
    refine sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (g_le hn hσm hσ hmassK hk) (hsZb k).1
    simp only [hG]; linarith
  have hP := P_bound hn0 ⟨hσm, hσ, hmass⟩ hK sZ hsZb hS1 hS2
  have hQ := Q_bound hn0 hσm hσ hmassK
  have hl3 := log_three_mul_le hn0
  -- the arithmetic
  have hA : S * ((2 * K - 6 * n) * Real.log n) ≤
      ((K : ℝ) ^ 2 - 6 * K * n) * Real.log n + K ^ 2 * Real.log n + 24 * n * Real.log n := by
    have h1 : 0 ≤ (S - (K - 4)) * ((6 * n - 2 * K) * Real.log n) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hL)
    linarith [h1, mul_nonneg hK0 hL]
  have hA2 : S * (400 * (1 + Real.log n)) ≤ 1200 * n * (1 + Real.log n) := by
    have : S ≤ 3 * n := by linarith
    have := mul_le_mul_of_nonneg_right this (show 0 ≤ 400 * (1 + Real.log n) by positivity)
    linarith
  have hA3 : 8 * (K : ℝ) * (1 + Real.log (3 * n)) ≤ 72 * n * (1 + Real.log n) := by
    have : 8 * (K : ℝ) * (1 + Real.log (3 * n)) ≤ 8 * (3 * n) * (3 + Real.log n) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 * n
        by linarith)]) (by positivity)
    linarith [mul_nonneg hn'.le hL]
  have hkap : (((K : ℝ) / n) ^ 2 - 6 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 = (K : ℝ) ^ 2 - 6 * K * n := by
    field_simp
  rw [hkap]
  unfold errC
  have : (3024 : ℝ) * n ≤ 3024 * n * (1 + Real.log n) := by linarith [mul_nonneg hn'.le hL]
  linarith [hstep1, hsplit, hlast, hint, hP, hQ, hA, hA2, hA3]

end Hankel2.ArchB
