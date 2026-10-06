import RequestProject.Zeta35.NVType

/-!
# Non-vanishing (N, §6): weighted Gram entries and the leading pair term

* `Phi s c P = ∑_{k ∈ s} ∑_{a < 4} c_{k,a} P_a(k)`: the node functionals `b^ℓ`, `b^{rest}`, `a`.
* `functional_bound`: the ultrametric bound of a weighted Gram entry `ℓ^w Φ(F G)` by its terms
  `ℓ^w c_{k,a₁+a₂} F_{a₁}(k) G_{a₂}(k)` (Leibniz rule for jets).
* `partner_jet`: if the jets of `P` at the anchor `−k` vanish below `s` and `P_s(k) = 1`, then the
  scaled partner jets satisfy `ℓ^{a−s} P_a(k − ℓ) ≡ C(s, a) (mod ℓ)` (the jets of `w^s` at `w = 1`).
* `pair_lead`: **the leading term of a pair** (N, proof of Theorem 6.2):
  `ℓ^{10−s} (∑_a β^ℓ_{k,a} P_a(k) + ∑_a β^ℓ_{k−ℓ,a} P_a(k−ℓ)) ≡ 2 y₀(k) Λ_{j(k)}(w^s) (mod ℓ)`.
-/

open Polynomial Finset

namespace Zeta35.NV

/-- The node functional `Φ_c(P) = ∑_{k ∈ s} ∑_{a < 4} c_{k,a} P_a(k)`. -/
noncomputable def Phi (s : Finset ℤ) (c : ℤ → ℕ → ℚ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ s, ∑ a ∈ range 4, c k a * Pjet P k a

theorem Pjet_mul (F G : ℚ[X]) (k : ℤ) (a : ℕ) :
    Pjet (F * G) k a = ∑ ab ∈ antidiagonal a, Pjet F k ab.1 * Pjet G k ab.2 :=
  Hankel2.W3.jet_mul F G _ a

theorem Pjet_add (F G : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (F + G) k a = Pjet F k a + Pjet G k a := by
  simp [Pjet, PF.Pjet]

theorem Pjet_smul (r : ℚ) (F : ℚ[X]) (k : ℤ) (a : ℕ) : Pjet (r • F) k a = r * Pjet F k a := by
  simp [Pjet, PF.Pjet]

variable {n ℓ : ℕ}

section Bounds

variable [hℓ : Fact ℓ.Prime]

theorem functional_bound (s : Finset ℤ) (c : ℤ → ℕ → ℚ) (F G : ℚ[X]) (w e : ℤ)
    (h : ∀ k ∈ s, ∀ a1 a2 : ℕ, a1 + a2 < 4 →
      VB ℓ ((ℓ : ℚ) ^ w * c k (a1 + a2) * Pjet F k a1 * Pjet G k a2) e) :
    VB ℓ ((ℓ : ℚ) ^ w * Phi s c (F * G)) e := by
  unfold Phi
  rw [Finset.mul_sum]
  refine VB.sum _ _ fun k hk => ?_
  rw [Finset.mul_sum]
  refine VB.sum _ _ fun a ha => ?_
  rw [Pjet_mul, Finset.mul_sum, Finset.mul_sum]
  refine VB.sum _ _ fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  have := h k hk ab.1 ab.2 (by have := Finset.mem_range.mp ha; omega)
  rw [hab] at this
  convert this using 1; ring

theorem term_VB {w e e1 e2 e3 : ℤ} {c J1 J2 : ℚ} (hc : VB ℓ c e1) (h1 : VB ℓ J1 e2)
    (h2 : VB ℓ J2 e3) (he : e ≤ w + e1 + e2 + e3) : VB ℓ ((ℓ : ℚ) ^ w * c * J1 * J2) e :=
  ((((VB_l_zpow (ℓ := ℓ) w).mul hc).mul h1).mul h2).mono (by omega)

end Bounds

/-- `ℓ^{a−s} P_a(k − ℓ) ≡ C(s, a) (mod ℓ)`. -/
theorem partner_jet [hℓ : Fact ℓ.Prime] (k : ℤ) (P : ℚ[X]) (s a : ℕ)
    (hint : ∀ m, VB ℓ (Pjet P k m) 0) (hlow : ∀ m < s, Pjet P k m = 0) (hs : Pjet P k s = 1) :
    VB ℓ ((ℓ : ℚ) ^ ((a : ℤ) - s) * Pjet P (k - ℓ) a - (s.choose a : ℚ)) 1 ∧
    VB ℓ ((ℓ : ℚ) ^ ((a : ℤ) - s) * Pjet P (k - ℓ) a) 0 := by
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hcast : (-((k - ℓ : ℤ) : ℚ)) = -(k : ℚ) + ℓ := by push_cast; ring
  set N := (taylor (-(k : ℚ)) P).natDegree + 1 with hN
  have hexp : Pjet P (k - ℓ) a = ∑ m ∈ range N, Pjet P k m * (m.choose a : ℚ) * (ℓ : ℚ) ^ (m - a) := by
    unfold Pjet PF.Pjet
    rw [hcast, Hankel2.W3.hasseDeriv_eval_add]
  have hsN : s ∈ range N := by
    rw [Finset.mem_range, hN, Nat.lt_succ_iff]
    refine le_natDegree_of_ne_zero ?_
    rw [taylor_coeff]
    have : Pjet P k s = (hasseDeriv s P).eval (-(k : ℚ)) := rfl
    rw [← this, hs]; exact one_ne_zero
  -- the scaled terms
  set T : ℕ → ℚ := fun m => Pjet P k m * (m.choose a : ℚ) *
    ((ℓ : ℚ) ^ ((a : ℤ) - s) * (ℓ : ℚ) ^ (m - a)) with hT
  have hsum : (ℓ : ℚ) ^ ((a : ℤ) - s) * Pjet P (k - ℓ) a = ∑ m ∈ range N, T m := by
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hT]; ring
  have hTs : T s = (s.choose a : ℚ) := by
    simp only [hT, hs, one_mul]
    by_cases has : a ≤ s
    · rw [← zpow_natCast, ← zpow_add₀ hl0, show (a : ℤ) - s + ((s - a : ℕ) : ℤ) = 0 by
        push_cast [has]; ring, zpow_zero, mul_one]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hTm : ∀ m ∈ (range N).erase s, VB ℓ (T m) 1 := by
    intro m hm
    have hms : m ≠ s := Finset.ne_of_mem_erase hm
    rcases lt_or_gt_of_ne hms with hlt | hgt
    · simp only [hT, hlow m hlt, zero_mul]; exact VB_zero 1
    by_cases hma : m < a
    · simp only [hT, Nat.choose_eq_zero_of_lt hma, Nat.cast_zero, mul_zero, zero_mul]
      exact VB_zero 1
    push_neg at hma
    have hp : (ℓ : ℚ) ^ ((a : ℤ) - s) * (ℓ : ℚ) ^ (m - a) = (ℓ : ℚ) ^ ((m : ℤ) - s) := by
      rw [← zpow_natCast, ← zpow_add₀ hl0]; congr 1; push_cast [hma]; ring
    simp only [hT, hp]
    have := ((hint m).mul (VB_nat (ℓ := ℓ) (m.choose a))).mul (VB_l_zpow (ℓ := ℓ) ((m : ℤ) - s))
    exact this.mono (by omega)
  have hrest : VB ℓ (∑ m ∈ (range N).erase s, T m) 1 := VB.sum _ _ hTm
  rw [hsum, ← Finset.add_sum_erase _ _ hsN, hTs]
  refine ⟨by simpa using hrest, ?_⟩
  exact (VB_nat (ℓ := ℓ) _).add (hrest.mono (by norm_num))

/-- **The leading term of a pair** (N, proof of Theorem 6.2). -/
theorem pair_lead (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) (P : ℚ[X]) (s : ℕ) (hs6 : s ≤ 6)
    (hint : haveI := Fact.mk h.prime; ∀ m, VB ℓ (Pjet P k m) 0)
    (hlow : ∀ m < s, Pjet P k m = 0) (hs : Pjet P k s = 1)
    (hmid : ∀ m, s < m → m < 4 → Pjet P k m = 0) :
    haveI := Fact.mk h.prime
    VB ℓ ((ℓ : ℚ) ^ ((10 : ℤ) - s) * (∑ a ∈ range 4, betaL n ℓ k a * Pjet P k a +
        ∑ a ∈ range 4, betaL n ℓ (k - ℓ) a * Pjet P (k - ℓ) a) -
      2 * yA n ℓ k * Blocks.Lam (jType ℓ k) s) 1 := by
  haveI := Fact.mk h.prime
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast h.prime.ne_zero
  set j := jType ℓ k with hj
  have hj2 : j ≤ 2 := jType_le ℓ k
  have hC0 := Cset_anchor h hk
  have hC1 := Cset_partner h hk
  -- the anchor part
  have hanch : ∑ a ∈ range 4, betaL n ℓ k a * Pjet P k a =
      if s < 4 then betaL n ℓ k s else 0 := by
    split_ifs with hs4
    · rw [Finset.sum_eq_single s]
      · rw [hs, mul_one]
      · intro a ha has
        rcases lt_or_gt_of_ne has with h1 | h1
        · rw [hlow a h1, mul_zero]
        · rw [hmid a h1 (Finset.mem_range.mp ha), mul_zero]
      · intro hns; exact absurd (Finset.mem_range.mpr hs4) hns
    · refine Finset.sum_eq_zero fun a ha => ?_
      rw [hlow a (by have := Finset.mem_range.mp ha; omega), mul_zero]
  set A0 : ℚ := if s < 4 then limA (C0j j) s else 0 with hA0
  have hanchV : VB ℓ ((ℓ : ℚ) ^ ((10 : ℤ) - s) * (if s < 4 then betaL n ℓ k s else 0) -
      yA n ℓ k * A0) 1 := by
    rw [hA0]
    split_ifs with hs4
    · have := (betaL_anchor h hk s hs4).1
      rw [hC0] at this
      rwa [show (ℓ : ℚ) ^ ((10 : ℤ) - s) = (ℓ : ℚ) ^ (10 - s) by
        rw [← zpow_natCast]; congr 1; push_cast [show s ≤ 10 by omega]; ring]
    · simpa using VB_zero (ℓ := ℓ) 1
  -- the partner part
  set B0 : ℚ := ∑ a ∈ range 4, limP (C1j j) a * (s.choose a : ℚ) with hB0
  have hpartV : VB ℓ ((ℓ : ℚ) ^ ((10 : ℤ) - s) *
      ∑ a ∈ range 4, betaL n ℓ (k - ℓ) a * Pjet P (k - ℓ) a - yP n ℓ k * B0) 1 := by
    rw [hB0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine VB.sum _ _ fun a ha => ?_
    have ha4 := Finset.mem_range.mp ha
    have hsplit : (ℓ : ℚ) ^ ((10 : ℤ) - s) = (ℓ : ℚ) ^ (10 - a) * (ℓ : ℚ) ^ ((a : ℤ) - s) := by
      rw [← zpow_natCast, ← zpow_add₀ hl0]; congr 1; push_cast [show a ≤ 10 by omega]; ring
    obtain ⟨hb1, hb2⟩ := betaL_partner h hk a ha4
    rw [hC1] at hb1
    obtain ⟨hq1, hq2⟩ := partner_jet (ℓ := ℓ) k P s a hint hlow hs
    set γ := (ℓ : ℚ) ^ (10 - a) * betaL n ℓ (k - ℓ) a
    set Q := (ℓ : ℚ) ^ ((a : ℤ) - s) * Pjet P (k - ℓ) a
    have e : (ℓ : ℚ) ^ ((10 : ℤ) - s) * (betaL n ℓ (k - ℓ) a * Pjet P (k - ℓ) a) -
        yP n ℓ k * (limP (C1j j) a * (s.choose a : ℚ)) =
        (γ - yP n ℓ k * limP (C1j j) a) * Q +
          (yP n ℓ k * limP (C1j j) a) * (Q - (s.choose a : ℚ)) := by
      simp only [γ, Q, hsplit]; ring
    rw [e]
    have hl := (VB_yP h hk).mul (VB_limP (ℓ := ℓ) h.ne_two j a)
    exact (by simpa using hb1.mul hq2 : VB ℓ _ 1).add (by simpa using hl.mul hq1)
  -- assemble
  have hM := Mval_eq j s hj2 hs6
  have hMv : Mval (C0j j) (C1j j) s = A0 + B0 := rfl
  have hB0V : VB ℓ B0 0 :=
    VB.sum _ _ fun a _ => ((VB_limP (ℓ := ℓ) h.ne_two j a).mul (VB_nat _)).mono (by simp)
  have hy := yP_sub_yA h hk
  rw [hanch]
  have e : (ℓ : ℚ) ^ ((10 : ℤ) - s) * ((if s < 4 then betaL n ℓ k s else 0) +
        ∑ a ∈ range 4, betaL n ℓ (k - ℓ) a * Pjet P (k - ℓ) a) - 2 * yA n ℓ k * Blocks.Lam j s =
      ((ℓ : ℚ) ^ ((10 : ℤ) - s) * (if s < 4 then betaL n ℓ k s else 0) - yA n ℓ k * A0) +
      ((ℓ : ℚ) ^ ((10 : ℤ) - s) * ∑ a ∈ range 4, betaL n ℓ (k - ℓ) a * Pjet P (k - ℓ) a -
        yP n ℓ k * B0) + (yP n ℓ k - yA n ℓ k) * B0 := by
    rw [show 2 * yA n ℓ k * Blocks.Lam j s = yA n ℓ k * (2 * Blocks.Lam j s) by ring, ← hM, hMv]
    ring
  rw [e]
  exact (hanchV.add hpartV).add (by simpa using hy.mul hB0V)

end Zeta35.NV
