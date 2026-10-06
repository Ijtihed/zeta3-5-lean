import RequestProject.Zeta35.ArchReduction3
import RequestProject.Zeta35.ArchCont3
import RequestProject.Zeta7.Hankel2.LemmaB61

/-!
# N, Theorem 4.1: the archimedean bound for `ζ₃(5)` (W, Lemma 4.1; P, Theorem 6.1)

* `EB3_eq_EBZ`: for even `n`, the discrete energy over the nodes `|k| ≤ 3n/2` equals the energy
  in the translated frame `[−n, 2n]` (node differences and `ln|h_k|` are translation invariant);
* `EB3_le_cont`: the continuum bound for every integer profile;
* `errR3_le`: `𝓔(n, K) ≤ 500 n (1 + ln n)` for even `n`, `K ≤ 6n`;
* **`arch_exp_general`**: for every `ε > 0` there is `N` such that for all even `n ≥ N`, all `K`
  with `K/n ≤ 6` and every feasible `σ` on `[−3/2, 3/2]`:
  `‖Δ_K‖₁ ≤ exp((κ² − 12κ) n² ln n + n² (F[σ] + gap(σ)) + ε n²)`;
* **`arch_holds`**: the field `arch` of `Zeta35InputsR4` verbatim (profile `σ_κ ≡ κ/3`,
  `Δ_K ≠ 0`).
-/

open Finset Hankel2

namespace Zeta35.Arch

/-- The translated node `u − n ∈ [−n, 2n]` (for even `n`, `2R = 3n`). -/
def zeta (n : ℕ) (u : Fin (2 * R n + 1)) : ℤ := (u : ℤ) - n

theorem sum_zeta {n : ℕ} (hn : Even n) {M : Type*} [AddCommMonoid M] (F : ℤ → M) :
    ∑ u : Fin (2 * R n + 1), F (zeta n u) = ∑ k ∈ Fam3PF.nodes n, F k := by
  have h2R := R_of_even hn
  refine sum_bij (fun u _ => zeta n u) ?_ ?_ ?_ ?_
  · intro u _
    simp only [Fam3PF.nodes, mem_Icc, zeta]
    have := u.isLt
    omega
  · intro u _ v _ h
    simp only [zeta] at h
    exact Fin.ext (by omega)
  · intro k hk
    simp only [Fam3PF.nodes, mem_Icc] at hk
    refine ⟨⟨(k + n).toNat, by omega⟩, mem_univ _, ?_⟩
    simp only [zeta]
    omega
  · intro u _; rfl

theorem nodeOf_sub (n : ℕ) (u v : Fin (2 * R n + 1)) :
    nodeOf n u - nodeOf n v = zeta n u - zeta n v := by
  simp only [nodeOf, zeta]; ring

theorem log_abs_hR3 {n : ℕ} (hn : Even n) (u : Fin (2 * R n + 1)) :
    Real.log |hR3 n u| = LZ n (zeta n u) := by
  have h2R := R_of_even hn
  unfold hR3 Hk
  rw [log_abs_Hk_zero, LZ]
  congr 1
  set d : ℤ := (R n : ℤ) - n with hd
  refine sum_nbij' (fun k => k + d) (fun k => k - d) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_erase, nodes, mem_Icc, nodeOf] at hk
    simp only [mem_erase, Fam3PF.nodes, mem_Icc, zeta, hd]
    omega
  · intro k hk
    simp only [mem_erase, Fam3PF.nodes, mem_Icc, zeta] at hk
    simp only [mem_erase, nodes, mem_Icc, nodeOf, hd]
    omega
  · intro k _; simp
  · intro k _; simp
  · intro k _
    simp only [zeta, nodeOf, hd]
    congr 3; ring

/-- The integer-indexed version `k ↦ s_{k+n}` of a profile. -/
noncomputable def sZ3 (n : ℕ) (s : Fin (2 * R n + 1) → ℕ) (k : ℤ) : ℝ :=
  s ⟨(k + n).toNat % (2 * R n + 1), Nat.mod_lt _ (by omega)⟩

theorem sZ3_zeta {n : ℕ} (s : Fin (2 * R n + 1) → ℕ) (u : Fin (2 * R n + 1)) :
    sZ3 n s (zeta n u) = s u := by
  unfold sZ3 zeta
  congr 2
  apply Fin.ext
  simp only
  rw [show ((u : ℤ) - n + n).toNat = u by omega, Nat.mod_eq_of_lt u.isLt]

theorem EB3_eq_EBZ {n : ℕ} (hn : Even n) (s : Fin (2 * R n + 1) → ℕ) :
    EB3 n (fun u => (s u : ℝ)) =
      ∑ k ∈ Fam3PF.nodes n, sZ3 n s k * LZ n k +
        ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ Fam3PF.nodes n,
          sZ3 n s k * sZ3 n s m * ArchB.Bk ((k - m : ℤ) : ℝ) := by
  unfold EB3
  congr 1
  · rw [← sum_zeta hn]
    refine sum_congr rfl fun u _ => ?_
    rw [sZ3_zeta, log_abs_hR3 hn]
  · rw [← sum_zeta hn]
    refine sum_congr rfl fun u _ => ?_
    rw [← sum_zeta hn]
    refine sum_congr rfl fun v _ => ?_
    rw [sZ3_zeta, sZ3_zeta]
    congr 2
    have := nodeOf_sub n u v
    have h' : ((nodeOf n u - nodeOf n v : ℤ) : ℝ) = ((zeta n u - zeta n v : ℤ) : ℝ) := by
      rw [this]
    push_cast at h' ⊢
    exact h'

/-- **The continuum bound for every integer profile.** -/
theorem EB3_le_cont {σ : ℝ → ℝ} {n K : ℕ} (hn0 : 0 < n) (hn : Even n)
    (hF : Feasible3 ((K : ℝ) / n) σ) (hK : (K : ℝ) / n ≤ 6) {s : Fin (2 * R n + 1) → ℕ}
    (hs : s ∈ profiles n K) :
    EB3 n (fun u => (s u : ℝ)) ≤
      ((K : ℝ) ^ 2 - 12 * K * n) * Real.log n +
        (n : ℝ) ^ 2 * (Fenergy3 σ + gap3 ((K : ℝ) / n) σ) + errC3 n := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range] at hs
  obtain ⟨hs5, hsK⟩ := hs
  rw [EB3_eq_EBZ hn]
  refine EBZ_le_cont hn0 hF hK (sZ3 n s) (fun k => ?_) ?_
  · simp only [sZ3]
    refine ⟨by positivity, ?_⟩
    have := hs5 ⟨(k + n).toNat % (2 * R n + 1), Nat.mod_lt _ (by omega)⟩
    exact_mod_cast (show s _ ≤ 4 by omega)
  · rw [← sum_zeta hn]
    simp only [sZ3_zeta]
    exact_mod_cast hsK

theorem log_Qn3_le {n : ℕ} (hn0 : 0 < n) (hn : Even n) : Real.log (Qn3 n) ≤ 21 + 3 * Real.log n := by
  have h2R := R_of_even hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hQ : Qn3 n ≤ 2 ^ 30 * (n : ℝ) ^ 3 := by
    unfold Qn3 LamZ
    have e : ((2 * R n + 1 : ℕ) : ℝ) = 3 * n + 1 := by
      have : 2 * R n + 1 = 3 * n + 1 := by omega
      rw [this]; push_cast; ring
    rw [e]
    have h1 : 4 * (3 * (n : ℝ) + 1) ≤ 16 * n := by linarith
    have h3 : (4 * (3 * (n : ℝ) + 1)) ^ 3 ≤ (16 * n) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    calc (200000 : ℝ) * (4 * (3 * n + 1)) ^ 3 ≤ 200000 * (16 * n) ^ 3 := by gcongr
      _ ≤ 2 ^ 30 * (n : ℝ) ^ 3 := by nlinarith [pow_pos (by linarith : (0:ℝ) < n) 3]
  calc Real.log (Qn3 n) ≤ Real.log (2 ^ 30 * (n : ℝ) ^ 3) := Real.log_le_log (Qn3_pos n) hQ
    _ = 30 * Real.log 2 + 3 * Real.log n := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    _ ≤ 21 + 3 * Real.log n := by have := Real.log_two_lt_d9; linarith

theorem errR3_le {n K : ℕ} (hn0 : 0 < n) (hn : Even n) (hK : (K : ℝ) ≤ 6 * n) :
    errR3 n K ≤ 500 * n * (1 + Real.log n) := by
  have h2R := R_of_even hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hQ := log_Qn3_le hn0 hn
  have h3 := ArchB.log_three_mul_le hn0
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h24 : Real.log 24 ≤ 4 := by
    have : Real.log 24 < 4 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h4]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 4]
    linarith
  have h24' : 0 < Real.log 24 := Real.log_pos (by norm_num)
  have e2R : ((2 * R n : ℕ) : ℝ) = 3 * n := by rw [h2R]; push_cast; ring
  unfold errR3
  have e2R' : (2 * (R n : ℝ)) = 3 * n := by exact_mod_cast e2R
  rw [e2R']
  have e1 : (K : ℝ) * (Real.log (Qn3 n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) ≤
      6 * n * (72 + 19 * Real.log n) := by
    calc (K : ℝ) * (Real.log (Qn3 n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2)
        ≤ K * (72 + 19 * Real.log n) := mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ 6 * n * (72 + 19 * Real.log n) := mul_le_mul_of_nonneg_right hK (by linarith)
  have e2 : (3 * (n : ℝ) + 1) * (Real.log 24 + 8 * Real.log 2) ≤ 4 * n * 10 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hL]

/-- **N, Theorem 4.1, exponential form**, uniformly in `κ = K/n ≤ 6` and the feasible profile. -/
theorem arch_exp_general : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
    (K : ℝ) / n ≤ 6 → ∀ σ : ℝ → ℝ, Feasible3 ((K : ℝ) / n) σ →
      l1 (hankelPoly n K) ≤ Real.exp
        ((((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy3 σ + gap3 ((K : ℝ) / n) σ) + ε * (n : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ArchB.nlogn_le_eps_sq 5500 (by norm_num) hε
  refine ⟨N + 1, fun n K hNn hn hK σ hσ => ?_⟩
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hKn : (K : ℝ) ≤ 6 * n := by rwa [div_le_iff₀ hn'] at hK
  have h62 := lemma62_3 (n := n) (K := K) _ (fun s hs => EB3_le_cont hn0 hn hσ hK hs)
  refine h62.trans (Real.exp_le_exp.2 ?_)
  have h1 := errR3_le hn0 hn hKn
  have h2 := hN n (by omega) hn0
  have hkap : (((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 =
      (K : ℝ) ^ 2 - 12 * K * n := by field_simp
  rw [hkap]
  unfold errC3
  nlinarith

theorem feasible3_sigmaK {κ : ℝ} (h0 : 0 ≤ κ) (h6 : κ ≤ 6) : Feasible3 κ (sigmaK κ) := by
  refine ⟨measurable_const, fun x => ⟨by simp only [sigmaK]; positivity, by
    simp only [sigmaK]; linarith⟩, ?_⟩
  simp only [sigmaK]
  rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- **N, Theorem 4.1**: the field `arch` of `Zeta35InputsR4` verbatim. -/
theorem arch_holds : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
    (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → hankelPoly n K ≠ 0 →
      Real.log (l1 (hankelPoly n K)) ≤
        (((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy3 (sigmaK ((K : ℝ) / n)) +
              gap3 ((K : ℝ) / n) (sigmaK ((K : ℝ) / n)))
          + ε * (n : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨N, hN⟩ := arch_exp_general ε hε
  refine ⟨N, fun n K hNn hn h59 h6 hne => ?_⟩
  rw [Real.log_le_iff_le_exp (ArchB.l1_pos_of_ne hne)]
  exact hN n K hNn hn h6 _ (feasible3_sigmaK (by linarith) h6)

end Zeta35.Arch
