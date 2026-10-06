import RequestProject.Zeta7.Hankel2.PartialFrac3

/-!
# Towards Lemma B: explicit ingredients of paper Lemma 6.2

Standalone, fully explicit pieces of the proof of Lemma 6.2 (`ln ‖Δ_K‖₁ ≤ max_s E_B(s) + 𝓔_n`):

* **(1) Counting**: `card_profiles_le` — at most `5^{3n+1}` profiles `0 ≤ s_k ≤ 4`.
* **(3) Bell bound for `b ≤ 3`**: `bell_bound` — if `|P₁| ≤ Λ`, `|P₂| ≤ 30·2²`, `|P₃| ≤ 30·2³`, then the first
  three Taylor coefficients `−P₁`, `(P₁² − P₂)/2`, `−(P₁³ − 3P₁P₂ + 2P₃)/6` of `exp(−∑ P_j u^j/j)` are bounded by
  `(Λ + 700)^b`.
* **`Λ_n`-estimate for `P₁`**: `sum_inv_dist_le` — `∑_{m ≠ k} 1/|k − m| ≤ 2(1 + ln 3n)` over the nodes
  `m ∈ [−n, 2n]` (this is the harmonic-sum estimate used for `|P₁|` and in (5)).
* **(5) Kernel replacement**: `kerErr_abs_le` — for integers `d ≠ 0`,
  `|ln(|d| + 1/5) − ½ ln(1 + d²)| ≤ 0.7/|d|`; `sum_kerErr_le` —
  `∑_{m ≠ k} s_m |ε(k − m)| ≤ 6(1 + ln 3n)`; `double_sum_kerErr_le` —
  `∑_{k ≠ m} s_k s_m ε(k − m) ≤ 6K(1 + ln 3n)`.

The Heine–Andreief expansion itself, the Cauchy estimate (2) and the local factors (4) are **not**
formalised here, so Lemma 6.2 as a whole is still open.
-/

open Finset

namespace Hankel2.LemmaB

/-- `Λ_n = 50 + 20 ln(4n)`. -/
noncomputable def LamN (n : ℕ) : ℝ := 50 + 20 * Real.log (4 * n)

/-! ### (1) Counting -/

/-- There are at most `5^{3n+1}` profiles `s : [−n, 2n] → {0,…,4}`. -/
theorem card_profiles_le (n K : ℕ) :
    ((Fintype.piFinset fun _ : Fin (3 * n + 1) => range 5).filter fun s => ∑ i, s i = K).card
      ≤ 5 ^ (3 * n + 1) := by
  refine (card_filter_le _ _).trans ?_
  simp [Fintype.card_piFinset]

/-! ### (3) The Bell bound for `b ≤ 3` -/

/-- The first three Taylor coefficients of `exp(−∑_j P_j u^j / j)` are bounded by `(Λ + 700)^b`
as soon as `|P₁| ≤ Λ`, `|P₂| ≤ 30·2²` and `|P₃| ≤ 30·2³`. -/
theorem bell_bound {P1 P2 P3 Λ : ℝ} (hΛ : 0 ≤ Λ) (h1 : |P1| ≤ Λ) (h2 : |P2| ≤ 30 * 2 ^ 2)
    (h3 : |P3| ≤ 30 * 2 ^ 3) :
    |-P1| ≤ Λ + 700 ∧ |(P1 ^ 2 - P2) / 2| ≤ (Λ + 700) ^ 2 ∧
      |-(P1 ^ 3 - 3 * P1 * P2 + 2 * P3) / 6| ≤ (Λ + 700) ^ 3 := by
  have a1 := abs_nonneg P1
  have a2 := abs_nonneg P2
  refine ⟨by rw [abs_neg]; linarith, ?_, ?_⟩
  · rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    refine (abs_sub _ _).trans ?_
    rw [abs_pow]
    have : |P1| ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ a1 h1 2
    nlinarith
  · rw [abs_div, abs_neg, show |(6 : ℝ)| = 6 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
    have e1 : |P1 ^ 3 - 3 * P1 * P2 + 2 * P3| ≤ |P1| ^ 3 + 3 * |P1| * |P2| + 2 * |P3| := by
      have := abs_add_le (P1 ^ 3 - 3 * P1 * P2) (2 * P3)
      have := abs_sub (P1 ^ 3) (3 * P1 * P2)
      simp only [abs_mul, abs_pow, abs_two, show |(3 : ℝ)| = 3 by norm_num] at *
      linarith
    have b1 : |P1| ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ a1 h1 3
    have b2 : |P1| * |P2| ≤ Λ * 120 := mul_le_mul h1 (by linarith) a2 hΛ
    nlinarith [sq_nonneg Λ, mul_nonneg hΛ (sq_nonneg Λ)]

/-! ### The harmonic estimate over the nodes -/

theorem harmonic_real_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ i ∈ range N, 1 / ((i : ℝ) + 1) := by
  simp [harmonic, Rat.cast_sum]

/-- One side of the node set: `∑_{m ∈ A, m < k} 1/(k − m) ≤ H_{3n}`. -/
theorem sum_inv_dist_left_le (n : ℕ) (k : ℤ) (hk : k ∈ Fam3PF.nodes n) :
    ∑ m ∈ (Fam3PF.nodes n).filter (· < k), 1 / (((k - m : ℤ)) : ℝ) ≤ 1 + Real.log (3 * n) := by
  simp only [Fam3PF.nodes, mem_Icc] at hk
  set A := (Fam3PF.nodes n).filter (· < k)
  have hinj : Set.InjOn (fun m : ℤ => (k - m - 1).toNat) A := by
    intro x hx y hy hxy
    simp only [A, Fam3PF.nodes, coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    omega
  have e : ∑ m ∈ A, 1 / (((k - m : ℤ)) : ℝ) =
      ∑ m ∈ A, 1 / ((((k - m - 1).toNat : ℕ) : ℝ) + 1) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [A, Fam3PF.nodes, mem_filter, mem_Icc] at hm
    congr 1
    have : ((k - m - 1).toNat : ℤ) = k - m - 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((k - m - 1).toNat : ℕ) : ℝ) = ((k - m - 1 : ℤ) : ℝ) := by exact_mod_cast this
    rw [h']; push_cast; ring
  rw [e, ← sum_image (g := fun m : ℤ => (k - m - 1).toNat) (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) hinj]
  have hsub : A.image (fun m : ℤ => (k - m - 1).toNat) ⊆ range (3 * n) := by
    intro i hi
    simp only [A, Fam3PF.nodes, mem_image, mem_filter, mem_Icc, mem_range] at hi ⊢
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
  rw [← harmonic_real_eq]
  exact harmonic_le_one_add_log _ |>.trans (by push_cast; exact le_refl _)

/-- The other side: `∑_{m ∈ A, m > k} 1/(m − k) ≤ H_{3n}`. -/
theorem sum_inv_dist_right_le (n : ℕ) (k : ℤ) (hk : k ∈ Fam3PF.nodes n) :
    ∑ m ∈ (Fam3PF.nodes n).filter (k < ·), 1 / (((m - k : ℤ)) : ℝ) ≤ 1 + Real.log (3 * n) := by
  simp only [Fam3PF.nodes, mem_Icc] at hk
  set A := (Fam3PF.nodes n).filter (k < ·)
  have hinj : Set.InjOn (fun m : ℤ => (m - k - 1).toNat) A := by
    intro x hx y hy hxy
    simp only [A, Fam3PF.nodes, coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    omega
  have e : ∑ m ∈ A, 1 / (((m - k : ℤ)) : ℝ) =
      ∑ m ∈ A, 1 / ((((m - k - 1).toNat : ℕ) : ℝ) + 1) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [A, Fam3PF.nodes, mem_filter, mem_Icc] at hm
    congr 1
    have : ((m - k - 1).toNat : ℤ) = m - k - 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((m - k - 1).toNat : ℕ) : ℝ) = ((m - k - 1 : ℤ) : ℝ) := by exact_mod_cast this
    rw [h']; push_cast; ring
  rw [e, ← sum_image (g := fun m : ℤ => (m - k - 1).toNat) (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) hinj]
  have hsub : A.image (fun m : ℤ => (m - k - 1).toNat) ⊆ range (3 * n) := by
    intro i hi
    simp only [A, Fam3PF.nodes, mem_image, mem_filter, mem_Icc, mem_range] at hi ⊢
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
  rw [← harmonic_real_eq]
  exact harmonic_le_one_add_log _ |>.trans (by push_cast; exact le_refl _)

/-- `∑_{m ≠ k} f(|k − m|)` splits into the two sides. -/
theorem sum_erase_split (n : ℕ) (k : ℤ) (f : ℤ → ℝ) :
    ∑ m ∈ (Fam3PF.nodes n).erase k, f m =
      ∑ m ∈ (Fam3PF.nodes n).filter (· < k), f m + ∑ m ∈ (Fam3PF.nodes n).filter (k < ·), f m := by
  rw [← sum_filter_add_sum_filter_not ((Fam3PF.nodes n).erase k) (· < k)]
  congr 1
  · refine sum_congr ?_ fun _ _ => rfl
    ext m; simp only [mem_filter, mem_erase]; constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'⟩
  · refine sum_congr ?_ fun _ _ => rfl
    ext m; simp only [mem_filter, mem_erase, not_lt]; constructor
    · rintro ⟨⟨h0, h⟩, h'⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'.le⟩

/-- **Harmonic estimate**: `∑_{m ≠ k} 1/|k − m| ≤ 2(1 + ln 3n)` over the nodes `[−n, 2n]`. -/
theorem sum_inv_dist_le (n : ℕ) (k : ℤ) (hk : k ∈ Fam3PF.nodes n) :
    ∑ m ∈ (Fam3PF.nodes n).erase k, 1 / |(((k - m : ℤ)) : ℝ)| ≤ 2 * (1 + Real.log (3 * n)) := by
  rw [sum_erase_split]
  have h1 : ∑ m ∈ (Fam3PF.nodes n).filter (· < k), 1 / |(((k - m : ℤ)) : ℝ)| =
      ∑ m ∈ (Fam3PF.nodes n).filter (· < k), 1 / (((k - m : ℤ)) : ℝ) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter] at hm
    rw [abs_of_pos (by exact_mod_cast (show (0 : ℤ) < k - m by omega))]
  have h2 : ∑ m ∈ (Fam3PF.nodes n).filter (k < ·), 1 / |(((k - m : ℤ)) : ℝ)| =
      ∑ m ∈ (Fam3PF.nodes n).filter (k < ·), 1 / (((m - k : ℤ)) : ℝ) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter] at hm
    rw [abs_of_neg (by exact_mod_cast (show k - m < 0 by omega))]
    push_cast; ring_nf
  rw [h1, h2]
  linarith [sum_inv_dist_left_le n k hk, sum_inv_dist_right_le n k hk]

/-! ### (5) Kernel replacement -/

/-- `ε(d) = ln(|d| + 1/5) − B(d)`, `B(d) = ½ ln(1 + d²)`. -/
noncomputable def kerErr (d : ℤ) : ℝ := Real.log (|(d : ℝ)| + 1 / 5) - Real.log (1 + (d : ℝ) ^ 2) / 2

/-- For integers `d ≠ 0`: `|ε(d)| ≤ 1/(5|d|) + 1/(2d²) ≤ 0.7/|d|`. -/
theorem kerErr_abs_le {d : ℤ} (hd : d ≠ 0) : |kerErr d| ≤ 0.7 / |(d : ℝ)| := by
  set a := |(d : ℝ)| with ha_def
  have ha1 : 1 ≤ a := by
    rw [ha_def, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hd
  have ha0 : 0 < a := by linarith
  have hsq : (d : ℝ) ^ 2 = a ^ 2 := by rw [ha_def, sq_abs]
  -- `0 ≤ ln(a + 1/5) − ln a ≤ 1/(5a)`
  have e1 : Real.log (a + 1 / 5) - Real.log a = Real.log ((a + 1 / 5) / a) :=
    (Real.log_div (by positivity) ha0.ne').symm
  have u1 : Real.log ((a + 1 / 5) / a) ≤ 1 / (5 * a) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (a + 1 / 5) / a by positivity)
    have e : (a + 1 / 5) / a - 1 = 1 / (5 * a) := by field_simp; ring
    linarith
  have l1 : 0 ≤ Real.log ((a + 1 / 5) / a) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  -- `0 ≤ ½ ln(1 + a²) − ln a ≤ 1/(2a²)`
  have e2 : Real.log (1 + a ^ 2) / 2 - Real.log a = Real.log ((1 + a ^ 2) / a ^ 2) / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have u2 : Real.log ((1 + a ^ 2) / a ^ 2) ≤ 1 / a ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + a ^ 2) / a ^ 2 by positivity)
    have e : (1 + a ^ 2) / a ^ 2 - 1 = 1 / a ^ 2 := by field_simp; ring
    linarith
  have l2 : 0 ≤ Real.log ((1 + a ^ 2) / a ^ 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hk : kerErr d = Real.log ((a + 1 / 5) / a) - Real.log ((1 + a ^ 2) / a ^ 2) / 2 := by
    unfold kerErr; rw [← ha_def, hsq]; linarith
  have i1 : 1 / (5 * a) = 0.2 / a := by field_simp; norm_num
  have i2 : 1 / a ^ 2 ≤ 1 / a := by
    rw [div_le_div_iff₀ (by positivity) ha0]; nlinarith
  have i3 : 0 ≤ 1 / a := by positivity
  rw [hk, abs_le]
  have : 0.7 / a = 0.2 / a + 0.5 * (1 / a) := by field_simp; norm_num
  constructor <;> linarith

/-- `∑_{m ≠ k} s_m |ε(k − m)| ≤ 6(1 + ln 3n)` whenever `s_m ≤ 4` for all `m`. -/
theorem sum_kerErr_le (n : ℕ) (k : ℤ) (hk : k ∈ Fam3PF.nodes n) (s : ℤ → ℝ)
    (hs4 : ∀ m, s m ≤ 4) :
    ∑ m ∈ (Fam3PF.nodes n).erase k, s m * |kerErr (k - m)| ≤ 6 * (1 + Real.log (3 * n)) := by
  have hper : ∀ m ∈ (Fam3PF.nodes n).erase k,
      s m * |kerErr (k - m)| ≤ 2.8 * (1 / |(((k - m : ℤ)) : ℝ)|) := by
    intro m hm
    have hkm : k - m ≠ 0 := by have := (mem_erase.1 hm).1; omega
    have h := kerErr_abs_le hkm
    have := mul_le_mul (hs4 m) h (abs_nonneg _) (by norm_num)
    have e : (4 : ℝ) * (0.7 / |(((k - m : ℤ)) : ℝ)|) = 2.8 * (1 / |(((k - m : ℤ)) : ℝ)|) := by ring
    linarith
  refine (sum_le_sum hper).trans ?_
  rw [← mul_sum]
  have := sum_inv_dist_le n k hk
  have hl : 0 ≤ 1 + Real.log (3 * n) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ 3 * n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast h
        linarith
      linarith [Real.log_nonneg this]
  nlinarith

/-- `∑_{k ≠ m} s_k s_m ε(k − m) ≤ 6K(1 + ln 3n)`, `K = ∑ s_k`, for profiles `0 ≤ s ≤ 4`. -/
theorem double_sum_kerErr_le (n : ℕ) (s : ℤ → ℝ) (hs0 : ∀ m, 0 ≤ s m) (hs4 : ∀ m, s m ≤ 4) :
    ∑ k ∈ Fam3PF.nodes n, ∑ m ∈ (Fam3PF.nodes n).erase k, s k * s m * kerErr (k - m) ≤
      6 * (∑ k ∈ Fam3PF.nodes n, s k) * (1 + Real.log (3 * n)) := by
  rw [mul_assoc, sum_mul, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have h := sum_kerErr_le n k hk s hs4
  have : ∑ m ∈ (Fam3PF.nodes n).erase k, s k * s m * kerErr (k - m) ≤
      s k * ∑ m ∈ (Fam3PF.nodes n).erase k, s m * |kerErr (k - m)| := by
    rw [mul_sum]
    refine sum_le_sum fun m _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_abs_self _) (hs0 m)) (hs0 k)
  have := mul_le_mul_of_nonneg_left h (hs0 k)
  linarith

end Hankel2.LemmaB
