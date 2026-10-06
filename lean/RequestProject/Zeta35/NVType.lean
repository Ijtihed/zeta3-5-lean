import RequestProject.Zeta35.NVConst

/-!
# Non-vanishing (N, §6): the type of a pair and integrality of the leading values

For an anchor `k ∈ [ℓ − R, R]` the pair `{k, k − ℓ}` has type `j(k) = #{m ∈ {1,2} : mℓ < 3k}`
(`jType`); the harmonic poles at `ℓ` of the anchor are `C0j j` and those of the partner are
`C1j j` (`Cset_anchor`, `Cset_partner`): the levels are `j` and `2 − j`.
-/

open Polynomial Finset

namespace Zeta35.NV

variable {n ℓ : ℕ}

/-- The type `j(k) = #{m ∈ {1,2} : mℓ < 3k}` of the pair with anchor `k`. -/
def jType (ℓ : ℕ) (k : ℤ) : ℕ := if 3 * k < ℓ then 0 else if 3 * k < 2 * ℓ then 1 else 2

theorem jType_le (ℓ : ℕ) (k : ℤ) : jType ℓ k ≤ 2 := by unfold jType; split_ifs <;> omega

theorem mem_Cset_iff {N c : ℕ} :
    c ∈ Cset ℓ N ↔ (c = 1 ∧ ℓ < 3 * N) ∨ (c = 2 ∧ 2 * ℓ < 3 * N) := by
  constructor
  · intro hc
    simp only [Cset, Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    interval_cases c <;> omega
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp [Cset] <;> omega

theorem three_mul_ne (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    3 * k ≠ ℓ ∧ 3 * k ≠ 2 * ℓ := by
  have hpos := anch_pos h hk
  have h3 : ¬ 3 ∣ ℓ := fun hd =>
    h.ne_three ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).1 hd).symm
  constructor
  · intro he
    exact h3 (Int.natCast_dvd_natCast.mp ⟨k, by rw [← he]; push_cast; ring⟩)
  · intro he
    have : (3 : ℤ) ∣ 2 * ℓ := ⟨k, by rw [← he]⟩
    have h2 : 3 ∣ 2 * ℓ := Int.natCast_dvd_natCast.mp (by exact_mod_cast this)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h2 with h4 | h4
    · omega
    · exact h3 h4

theorem Cset_anchor (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    Cset ℓ k.natAbs = C0j (jType ℓ k) := by
  have hpos := anch_pos h hk
  have hne := three_mul_ne h hk
  have hab : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg hpos.1.le
  ext c
  rw [mem_Cset_iff]
  by_cases h1 : 3 * k < ℓ
  · rw [show jType ℓ k = 0 by simp [jType, h1], show C0j 0 = ∅ from rfl]
    simp only [Finset.notMem_empty, iff_false]; omega
  by_cases h2 : 3 * k < 2 * ℓ
  · rw [show jType ℓ k = 1 by simp [jType, h1, h2], show C0j 1 = {1} from rfl,
      Finset.mem_singleton]
    constructor <;> intro hc <;> omega
  · rw [show jType ℓ k = 2 by simp [jType, h1, h2], show C0j 2 = {1, 2} from rfl]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hc <;> omega

theorem Cset_partner (h : Adm n ℓ) {k : ℤ} (hk : k ∈ anch n ℓ) :
    Cset ℓ (k - ℓ).natAbs = C1j (jType ℓ k) := by
  have hpos := anch_pos h hk
  have hne := three_mul_ne h hk
  have hab : (((k - ℓ).natAbs : ℕ) : ℤ) = ℓ - k := by
    rw [Int.natCast_natAbs, abs_of_neg (by omega)]; ring
  ext c
  rw [mem_Cset_iff]
  by_cases h1 : 3 * k < ℓ
  · rw [show jType ℓ k = 0 by simp [jType, h1], show C1j 0 = {1, 2} from rfl]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hc <;> omega
  by_cases h2 : 3 * k < 2 * ℓ
  · rw [show jType ℓ k = 1 by simp [jType, h1, h2], show C1j 1 = {1} from rfl,
      Finset.mem_singleton]
    constructor <;> intro hc <;> omega
  · rw [show jType ℓ k = 2 by simp [jType, h1, h2], show C1j 2 = ∅ from rfl]
    simp only [Finset.notMem_empty, iff_false]; omega

theorem C0j_sub (j : ℕ) : ∀ c ∈ C0j j, c = 1 ∨ c = 2 := by
  intro c hc; unfold C0j at hc; split_ifs at hc <;> simp at hc <;> omega

theorem C1j_sub (j : ℕ) : ∀ c ∈ C1j j, c = 1 ∨ c = 2 := by
  intro c hc; unfold C1j at hc; split_ifs at hc <;> simp at hc <;> omega

variable [hℓ : Fact ℓ.Prime]

theorem VB_limL (hℓ2 : ℓ ≠ 2) (σ : ℕ → ℚ) (ε : ℚ) (hε : ε = 1 ∨ ε = -1) (Cs : Finset ℕ)
    (hC : ∀ c ∈ Cs, c = 1 ∨ c = 2) (hσ : ∀ M, VB ℓ (σ M) 0) (a : ℕ) :
    VB ℓ (limL σ ε Cs a) 0 := by
  unfold limL
  refine VB.neg (VB.sum _ _ fun i _ => VB.sum _ _ fun c hc => ?_)
  have hcinv : VB ℓ ((c : ℚ)⁻¹) 0 := by
    refine VB_inv_nat fun hd => ?_
    rcases hC c hc with rfl | rfl
    · exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp hd)
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 hd)
  have h3 : VB ℓ ((3 : ℚ) ^ (i + 1 + 1)) 0 := by
    have := (VB_nat (ℓ := ℓ) 3).pow (i + 1 + 1); simpa using this
  have he : VB ℓ ((-ε) ^ (4 - i - a)) 0 := by
    rcases hε with rfl | rfl
    · have := (VB_one (ℓ := ℓ)).neg.pow (4 - i - a); simpa using this
    · have := (VB_one (ℓ := ℓ)).pow (4 - i - a); simpa using this
  have := (((((VB_nat (ℓ := ℓ) i).mul (hσ (i + 1))).mul (VB_nat (ℓ := ℓ) (i + 1))).mul h3).mul
    (hcinv.pow (i + 1 + 1))).mul (he.mul (VB_nat (ℓ := ℓ) ((4 - i - a + 3).choose 3)))
  rw [← inv_pow]; simpa using this

theorem VB_limA (hℓ2 : ℓ ≠ 2) (j a : ℕ) : VB ℓ (limA (C0j j) a) 0 :=
  VB_limL hℓ2 _ _ (Or.inr rfl) _ (C0j_sub j) (fun _ => (VB_one (ℓ := ℓ)).neg) a

theorem VB_limP (hℓ2 : ℓ ≠ 2) (j a : ℕ) : VB ℓ (limP (C1j j) a) 0 :=
  VB_limL hℓ2 _ _ (Or.inl rfl) _ (C1j_sub j)
    (fun M => ((VB_one (ℓ := ℓ)).neg.pow (M + 1)).mono (by simp)) a

/-- `Λ_j(w^s)` is `ℓ`-integral (`ℓ ≥ 3`). -/
theorem VB_Lam (hℓ2 : ℓ ≠ 2) {j s : ℕ} (hj : j ≤ 2) (hs : s ≤ 6) : VB ℓ (Blocks.Lam j s) 0 := by
  have h := Mval_eq j s hj hs
  have hM : VB ℓ (Mval (C0j j) (C1j j) s) 0 := by
    unfold Mval
    refine VB.add ?_ (VB.sum _ _ fun t _ => (VB_limP hℓ2 j t).mul (VB_nat _) |>.mono (by simp))
    split_ifs
    · exact VB_limA hℓ2 j s
    · exact VB_zero _
  have h2 : VB ℓ ((2 : ℚ)⁻¹) 0 := by
    have := VB_inv_nat (ℓ := ℓ) (m := 2) fun hd =>
      hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 hd)
    simpa using this
  have : Blocks.Lam j s = (2 : ℚ)⁻¹ * Mval (C0j j) (C1j j) s := by rw [h]; ring
  rw [this]; simpa using h2.mul hM

end Zeta35.NV
