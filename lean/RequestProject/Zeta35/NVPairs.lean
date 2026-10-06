import RequestProject.Zeta35.NVLocal
import RequestProject.Zeta35.NVBlockVal

/-!
# Non-vanishing (N, §6): pairs, singletons and the local valuations at an admissible prime

`Adm n ℓ`: `n` even, `ℓ` prime, `R < ℓ`, `ℓ ≥ 7`, `3(ℓ − R) ≤ ℓ` (N, Definition in §6; `ℓ ∤ b` is
imposed separately).  The *anchors* are `k ∈ [ℓ − R, R]`; the anchor `k` and its *partner* `k − ℓ`
form a pair, and all other nodes (`|k| < ℓ − R ≤ ℓ/3`) are *singletons*.

For every node class we prove the valuations of `H_k[b]`, `β^ℓ`, `β^{rest}` and `α` used in N,
Theorem 6.2:

* paired nodes: `v(H_k[b]) ≥ −4 − b`, `ℓ^{10−a} β^ℓ_{k,a} ≡ y₀ λ_a`, `v(β^{rest}_{k,a}) ≥ −7 + a`,
  `v(α_{k,a}) ≥ −5 + a`;
* singletons: `H_k[b]`, `β^{rest}`, `α` integral and `β^ℓ = 0`.
-/

open Polynomial Finset PowerSeries

namespace Zeta35.NV

/-- **Admissible primes** (N, §6), without the condition `ℓ ∤ b`. -/
structure Adm (n ℓ : ℕ) : Prop where
  even : Even n
  prime : ℓ.Prime
  lo : R n < ℓ
  seven : 7 ≤ ℓ
  third : 3 * (ℓ - R n) ≤ ℓ

/-- The anchors `k ∈ [ℓ − R, R]`; the pairs are `{k, k − ℓ}`. -/
def anch (n ℓ : ℕ) : Finset ℤ := Icc ((ℓ : ℤ) - R n) (R n)

theorem mem_nodes {n : ℕ} {k : ℤ} : k ∈ nodes n ↔ -(R n : ℤ) ≤ k ∧ k ≤ R n := by
  simp [nodes]

theorem mem_anch {n ℓ : ℕ} {k : ℤ} : k ∈ anch n ℓ ↔ (ℓ : ℤ) - R n ≤ k ∧ k ≤ R n := by
  simp [anch]

variable {n ℓ : ℕ}

theorem Adm.third' (h : Adm n ℓ) : 3 * ((ℓ : ℤ) - R n) ≤ ℓ := by
  have := h.third; have := h.lo; omega

theorem Adm.ne_two (h : Adm n ℓ) : ℓ ≠ 2 := by have := h.seven; omega

theorem Adm.ne_three (h : Adm n ℓ) : ℓ ≠ 3 := by have := h.seven; omega

theorem anch_mem_nodes (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) : k ∈ nodes n := by
  rw [mem_anch] at hk; rw [mem_nodes]; have := h.lo; omega

theorem anch_sub_mem_nodes (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) : k - ℓ ∈ nodes n := by
  rw [mem_anch] at hk; rw [mem_nodes]; have := h.lo; omega

theorem anch_pos (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) : 0 < k ∧ k < ℓ := by
  rw [mem_anch] at hk; have := h.lo; omega

/-- Two nodes in the same class mod `ℓ` differ by `0` or `±ℓ`. -/
theorem dvd_cases (h : Adm n ℓ) {k k' : ℤ} (hk : k ∈ nodes n) (hk' : k' ∈ nodes n)
    (hd : (ℓ : ℤ) ∣ k' - k) : k' = k ∨ k' = k + ℓ ∨ k' = k - ℓ := by
  rw [mem_nodes] at hk hk'
  obtain ⟨c, hc⟩ := hd
  have hl := h.lo
  have hl0 : (0 : ℤ) < ℓ := by exact_mod_cast h.prime.pos
  have h1 : c < 2 := by
    by_contra hcon; push_neg at hcon
    have : (ℓ : ℤ) * 2 ≤ ℓ * c := mul_le_mul_of_nonneg_left hcon hl0.le
    omega
  have h2 : -2 < c := by
    by_contra hcon; push_neg at hcon
    have : (ℓ : ℤ) * c ≤ ℓ * (-2) := mul_le_mul_of_nonneg_left hcon hl0.le
    omega
  interval_cases c <;> [right; left; right] <;> [right; skip; left] <;> linarith

theorem anch_others (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    ∀ k' ∈ ((nodes n).erase k).erase (k + -(ℓ : ℤ)), ¬ (ℓ : ℤ) ∣ (k' - k) := by
  intro k' hk' hd
  simp only [Finset.mem_erase] at hk'
  obtain ⟨h1, h2, h3⟩ := hk'
  rcases dvd_cases h (anch_mem_nodes h hk) h3 hd with h4 | h4 | h4
  · exact h2 h4
  · rw [mem_nodes] at h3; rw [mem_anch] at hk; have := h.lo; omega
  · exact h1 (by omega)

theorem partner_others (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    ∀ k' ∈ ((nodes n).erase (k - ℓ)).erase (k - ℓ + ℓ), ¬ (ℓ : ℤ) ∣ (k' - (k - ℓ)) := by
  intro k' hk' hd
  simp only [Finset.mem_erase] at hk'
  obtain ⟨h1, h2, h3⟩ := hk'
  rcases dvd_cases h (anch_sub_mem_nodes h hk) h3 hd with h4 | h4 | h4
  · exact h2 h4
  · exact h1 h4
  · rw [mem_nodes] at h3; rw [mem_anch] at hk; have := h.lo; omega

/-- Singletons: `|k| < ℓ − R`. -/
theorem single_bound (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) : -((ℓ : ℤ) - R n) < k ∧ k < (ℓ : ℤ) - R n := by
  rw [mem_nodes] at hk; rw [mem_anch] at h1 h2
  have := h.lo
  constructor
  · by_contra hc; push_neg at hc; exact h2 ⟨by omega, by omega⟩
  · by_contra hc; push_neg at hc; exact h1 ⟨hc, hk.2⟩

theorem single_others (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) : ∀ k' ∈ (nodes n).erase k, ¬ (ℓ : ℤ) ∣ (k' - k) := by
  intro k' hk' hd
  obtain ⟨hne, hk'n⟩ := Finset.mem_erase.mp hk'
  have hb := single_bound h hk h1 h2
  rcases dvd_cases h hk hk'n hd with h4 | h4 | h4
  · exact hne h4
  · rw [mem_nodes] at hk'n; omega
  · rw [mem_nodes] at hk'n; omega

/-! ### The unit constants `y₀` -/

/-- `y₀` at the anchor `k`: `∏_{k' ≠ k, k − ℓ} (k' − k)^{-4}`. -/
noncomputable def yA (n ℓ : ℕ) (k : ℤ) : ℚ :=
  ((∏ k' ∈ ((nodes n).erase k).erase (k + -(ℓ : ℤ)), (k' - k) ^ 4 : ℤ) : ℚ)⁻¹

/-- `y₀` at the partner `k − ℓ`: `∏_{k' ≠ k − ℓ, k} (k' − k + ℓ)^{-4}`. -/
noncomputable def yP (n ℓ : ℕ) (k : ℤ) : ℚ :=
  ((∏ k' ∈ ((nodes n).erase (k - ℓ)).erase (k - ℓ + ℓ), (k' - (k - ℓ)) ^ 4 : ℤ) : ℚ)⁻¹

theorem not_dvd_prod (h : Adm n ℓ) (s : Finset ℤ) (f : ℤ → ℤ) (hs : ∀ k' ∈ s, ¬ (ℓ : ℤ) ∣ f k') :
    ¬ (ℓ : ℤ) ∣ ∏ k' ∈ s, f k' ^ 4 := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp h.prime
  intro hd
  obtain ⟨k', hk', hd'⟩ := (Prime.dvd_finset_prod_iff hp _).1 hd
  exact hs k' hk' (hp.dvd_of_dvd_pow hd')

theorem VB_yA (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    haveI := Fact.mk h.prime; VB ℓ (yA n ℓ k) 0 := by
  haveI := Fact.mk h.prime
  exact VB_inv_int (not_dvd_prod h _ (fun k' => k' - k) (anch_others h hk))

theorem padicNorm_yA (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    haveI := Fact.mk h.prime; padicNorm ℓ (yA n ℓ k) = 1 := by
  haveI := Fact.mk h.prime
  exact padicNorm_inv_int_eq (not_dvd_prod h _ (fun k' => k' - k) (anch_others h hk))

theorem VB_yP (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    haveI := Fact.mk h.prime; VB ℓ (yP n ℓ k) 0 := by
  haveI := Fact.mk h.prime
  exact VB_inv_int (not_dvd_prod h _ (fun k' => k' - (k - ℓ)) (partner_others h hk))

/-- `y₀` at the partner is congruent to `y₀` at the anchor mod `ℓ`. -/
theorem yP_sub_yA (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    haveI := Fact.mk h.prime; VB ℓ (yP n ℓ k - yA n ℓ k) 1 := by
  haveI := Fact.mk h.prime
  have hs : ((nodes n).erase (k - ℓ)).erase (k - ℓ + ℓ) =
      ((nodes n).erase k).erase (k + -(ℓ : ℤ)) := by
    rw [show k - ℓ + ℓ = k by ring, show k + -(ℓ : ℤ) = k - ℓ by ring, Finset.erase_right_comm]
  set s := ((nodes n).erase k).erase (k + -(ℓ : ℤ)) with hsdef
  set A : ℤ := ∏ k' ∈ s, (k' - k) ^ 4 with hA
  set B : ℤ := ∏ k' ∈ s, (k' - (k - ℓ)) ^ 4 with hB
  have hyA : yA n ℓ k = (A : ℚ)⁻¹ := rfl
  have hyP : yP n ℓ k = (B : ℚ)⁻¹ := by unfold yP; rw [hs]
  have hA0 : ¬ (ℓ : ℤ) ∣ A := not_dvd_prod h _ (fun k' => k' - k) (anch_others h hk)
  have hB0 : ¬ (ℓ : ℤ) ∣ B := by
    have := not_dvd_prod h _ (fun k' => k' - (k - ℓ)) (partner_others h hk)
    rwa [hs] at this
  have hAne : (A : ℚ) ≠ 0 := by
    exact_mod_cast fun h0 : A = 0 => hA0 (by rw [h0]; exact dvd_zero _)
  have hBne : (B : ℚ) ≠ 0 := by
    exact_mod_cast fun h0 : B = 0 => hB0 (by rw [h0]; exact dvd_zero _)
  have hdvd : (ℓ : ℤ) ∣ A - B := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp only [hA, hB, Int.cast_prod, Int.cast_pow, Int.cast_sub, Int.cast_natCast,
      ZMod.natCast_self, sub_zero]
  have hAB : VB ℓ ((A - B : ℤ) : ℚ) 1 :=
    (VB_one_iff _).2 ((padicNorm.int_lt_one_iff _).2 hdvd)
  rw [hyA, hyP]
  have e : (B : ℚ)⁻¹ - (A : ℚ)⁻¹ = ((A - B : ℤ) : ℚ) * ((A : ℚ)⁻¹ * (B : ℚ)⁻¹) := by
    push_cast; field_simp
  rw [e]
  simpa using hAB.mul ((VB_inv_int hA0).mul (VB_inv_int hB0))

/-! ### The series `H_k` at paired nodes and at singletons -/

theorem VB_of_scaled {ℓ : ℕ} [Fact ℓ.Prime] {q : ℚ} {m : ℕ} {e : ℤ}
    (h : VB ℓ ((ℓ : ℚ) ^ m * q) e) : VB ℓ q (e - m) := by
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have : q = (ℓ : ℚ) ^ (-(m : ℤ)) * ((ℓ : ℚ) ^ m * q) := by
    rw [← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_mul]
  rw [this]
  have := (VB_l_zpow (ℓ := ℓ) (-(m : ℤ))).mul h
  convert this using 1; ring

theorem Hk_anchor (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) (b : ℕ) :
    haveI := Fact.mk h.prime
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n k b -
      (-(-1 : ℚ)) ^ b * ((b + 3).choose 3 : ℚ) * yA n ℓ k) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n k b) 0 := by
  haveI := Fact.mk h.prime
  have hl0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  have hmem : k + -(ℓ : ℤ) ∈ nodes n := by
    rw [show k + -(ℓ : ℤ) = k - ℓ by ring]; exact anch_sub_mem_nodes h hk
  unfold Hk PF.Hk
  rw [Hser_eq_mate (nodes n) hmem (by omega)]
  have hY := PUnitS_mate (ℓ := ℓ) _ k (anch_others h hk)
  have := coeff_mate (ℓ := ℓ) (-1) (Or.inr rfl) (-(ℓ : ℤ)) (by push_cast; ring) _ hY.1 b
  rw [constantCoeff_mate] at this
  exact this

theorem Hk_partner (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) (b : ℕ) :
    haveI := Fact.mk h.prime
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n (k - ℓ) b -
      (-(1 : ℚ)) ^ b * ((b + 3).choose 3 : ℚ) * yP n ℓ k) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ (4 + b) * Hk n (k - ℓ) b) 0 := by
  haveI := Fact.mk h.prime
  have hl0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  have hmem : k - ℓ + (ℓ : ℤ) ∈ nodes n := by
    rw [show k - ℓ + (ℓ : ℤ) = k by ring]; exact anch_mem_nodes h hk
  unfold Hk PF.Hk
  rw [Hser_eq_mate (nodes n) hmem hl0]
  have hY := PUnitS_mate (ℓ := ℓ) _ (k - ℓ) (partner_others h hk)
  have := coeff_mate (ℓ := ℓ) 1 (Or.inl rfl) (ℓ : ℤ) (by push_cast; ring) _ hY.1 b
  rw [constantCoeff_mate] at this
  exact this

theorem Hk_single (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (h1 : k ∉ anch n ℓ)
    (h2 : k + ℓ ∉ anch n ℓ) (b : ℕ) : haveI := Fact.mk h.prime; VB ℓ (Hk n k b) 0 := by
  haveI := Fact.mk h.prime
  have hY := PUnitS_mate (ℓ := ℓ) _ k (single_others h hk h1 h2)
  exact (VB_zero_iff _).2 (hY.1 b)

end Zeta35.NV
