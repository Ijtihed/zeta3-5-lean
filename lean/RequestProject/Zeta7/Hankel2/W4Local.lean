import Mathlib
import RequestProject.Zeta7.Hankel2.W2Local

/-!
# W4, local part: the Taylor coefficients of `H_k` at every node of family 3

`ZETA7_STATUS.md`, round (e) §2 (Lemma W4).  For odd `n` and a prime `p` with `7n + 2 ≤ 4p`,
`p + 1 ≤ 2n` (write `h = (p+1)/2`), every node `k ∈ [-n, 2n]` falls into one of three classes, and the
Taylor coefficients of `H_k = fam3H n k` satisfy `|[u^m] H_k|_p ≤ p^{e + m}` (`HB p H_k e`) with

* `e = 0` at the *lone* nodes `k ∈ [2n - p + 1, p - n - 1]` (no other node `≡ k mod p`):
  `HB_lone`;
* `e = -2` on the *generic pairs*: the generic harmonic-sum nodes and `g*`, `k ∈ [h, n + h - 1]`, and
  their partners `k - p ∈ [h - p, n - h]`; the pole `(u ∓ p)^{-4}` is compensated by the order-6
  numerator zero at the midpoint: `HB_genericClass`;
* `e = 4` on the *special pairs*: the special harmonic-sum nodes `k ∈ [-n, -h] ∪ [n + h, 2n]` and their
  partners `k ∈ [p - n, p - h] ∪ [n - h + 1, 2n - p]`; here only the pole `(u ∓ p)^{-4}` is `p`-small:
  `HB_specialClass`.

In every case all other Taylor factors of `H_k` have `p`-adic unit constants (node combinatorics).
-/

open PowerSeries

namespace Hankel2
namespace W2

section HBound

variable (p : ℕ) [Fact p.Prime]

/-- `|[u^m] H|_p ≤ p^{e + m}` for all `m`. -/
def HB (H : ℚ⟦X⟧) (e : ℤ) : Prop := ∀ m : ℕ, padicNorm p (coeff m H) ≤ (p : ℚ) ^ (e + m)

variable {p}

theorem one_lt_p_rat : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

theorem HB.mul_PInt {Y S : ℚ⟦X⟧} {e : ℤ} (hY : PInt p Y) (hS : HB p S e) : HB p (Y * S) e := by
  intro m
  have h1 := one_lt_p_rat (p := p)
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x hx => ?_) (zpow_pos (by linarith) _).le
  rw [Finset.mem_antidiagonal] at hx
  rw [padicNorm.mul]
  calc padicNorm p (coeff x.1 Y) * padicNorm p (coeff x.2 S) ≤ 1 * (p : ℚ) ^ (e + x.2) :=
        mul_le_mul (hY _) (hS _) (padicNorm.nonneg _) zero_le_one
    _ ≤ (p : ℚ) ^ (e + m) := by
        rw [one_mul]; exact zpow_le_zpow_right₀ h1.le (by omega)

theorem HB_of_PInt {Y : ℚ⟦X⟧} (hY : PInt p Y) : HB p Y 0 := by
  intro m
  refine (hY m).trans ?_
  rw [zero_add, zpow_natCast]
  exact one_le_pow₀ one_lt_p_rat.le

theorem HB_sp {q : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) : HB p (((C (-q) + X)⁻¹) ^ 4) 4 := by
  intro m
  refine (w4_special_pair_coeff hq m).trans_eq ?_
  rw [zpow_add₀ (by linarith [one_lt_p_rat (p := p)]), zpow_natCast]; rfl

theorem HB_gen (hp2 : p ≠ 2) {q : ℚ} (hq : padicNorm p q = (p : ℚ)⁻¹) :
    HB p (((C (-q) + X)⁻¹) ^ 4 * (C (-q / 2) + X) ^ 6) (-2) := by
  intro m
  refine (w4_generic_pair_coeff hp2 hq m).trans_eq ?_
  rw [zpow_add₀ (by linarith [one_lt_p_rat (p := p)]), zpow_natCast, zpow_neg, inv_pow]; rfl

omit [Fact p.Prime] in
theorem PInt_C_add_C_mul_X {c d : ℚ} (hc : padicNorm p c ≤ 1) (hd : padicNorm p d ≤ 1) :
    PInt p (C c + C d * X) := by
  intro m
  rcases m with _ | _ | m
  · simpa using hc
  · simpa using hd
  · simp

theorem padicNorm_natCast_le_one' (m : ℕ) : padicNorm p (m : ℚ) ≤ 1 := padicNorm.of_nat m

end HBound

section Nodes

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

omit [Fact p.Prime] in
/-- The midpoint numerator factor at a partner node `k` of the generic node `k + p`. -/
theorem numF_mid' {k : ℤ} {j0 : ℕ} (hodd : p % 2 = 1) (hj0 : (j0 : ℤ) = k + p - ((p : ℤ) + 1) / 2) :
    numF k j0 = (C (-(-(p : ℚ)) / 2) + X) ^ 6 := by
  have hh : 2 * (((p : ℤ) + 1) / 2) = p + 1 := by omega
  have hq : ((j0 : ℤ) : ℚ) = (k : ℚ) + p - (((((p : ℤ) + 1) / 2 : ℤ)) : ℚ) := by
    rw [hj0]; push_cast; ring
  have hq2 : (2 : ℚ) * ((((p : ℤ) + 1) / 2 : ℤ) : ℚ) = p + 1 := by exact_mod_cast hh
  have : (j0 : ℚ) + 1 / 2 - k = -(-(p : ℚ)) / 2 := by
    have e : (j0 : ℚ) = ((j0 : ℤ) : ℚ) := by norm_cast
    rw [e, hq]; linarith
  rw [numF, this]

/-- **Lone nodes**: `H_k` is `p`-integral. -/
theorem HB_lone (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) {k : ℤ}
    (hk1 : 2 * (n : ℤ) - p + 1 ≤ k) (hk2 : k ≤ (p : ℤ) - n - 1) : HB p (fam3H n k) 0 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  refine HB_of_PInt ?_
  rw [fam3H_eq]
  refine ((PUnitS.mul (PUnitS.mul ?_ ?_) ?_)).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Special harmonic-sum nodes, right** `k ∈ [n + h, 2n]`. -/
theorem HB_special_right (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ k) (hk2 : k ≤ 2 * n) : HB p (fam3H n k) 4 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_sp padicNorm_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Special harmonic-sum nodes, left** `k ∈ [-n, -h]`. -/
theorem HB_special_left (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : -(n : ℤ) ≤ k) (hk2 : k ≤ -(((p : ℤ) + 1) / 2)) : HB p (fam3H n k) 4 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hmem : k + p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k + p) = ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') *
      ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_sp padicNorm_neg_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Partners of the special right nodes**, `k ∈ [n - h + 1, 2n - p]` (partner `k + p`). -/
theorem HB_special_right_partner (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : (n : ℤ) - ((p : ℤ) + 1) / 2 + 1 ≤ k) (hk2 : k ≤ 2 * n - p) :
    HB p (fam3H n k) 4 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hmem : k + p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k + p) = ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') *
      ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_sp padicNorm_neg_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Partners of the special left nodes**, `k ∈ [p - n, p - h]` (partner `k - p`). -/
theorem HB_special_left_partner (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : (p : ℤ) - n ≤ k) (hk2 : k ≤ (p : ℤ) - ((p : ℤ) + 1) / 2) :
    HB p (fam3H n k) 4 := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ Finset.range n, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, hden]; ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_sp padicNorm_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Generic harmonic-sum nodes** `k ∈ [h, n + h - 1]`, `2k ≠ n + p`. -/
theorem HB_generic (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : ((p : ℤ) + 1) / 2 ≤ k) (hk2 : k ≤ n + ((p : ℤ) - 1) / 2) (hk3 : 2 * k ≠ n + p) :
    HB p (fam3H n k) (-2) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  set j0 : ℕ := (k - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      (((C (-(p : ℚ)) + X)⁻¹) ^ 4 * (C (-(p : ℚ) / 2) + X) ^ 6) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid hodd hj0]
    ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_gen hp2 padicNorm_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **The node `g*`** (`2k = n + p`). -/
theorem HB_gstar (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk : 2 * k = n + p) : HB p (fam3H n k) (-2) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  set j0 : ℕ := (k - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k - p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k - p) = ((C (-(p : ℚ)) + X)⁻¹) ^ 4 := by simp [denF]
  have hlin : linF n k = C (-(p : ℚ)) + C 2 * X := by
    have : (n : ℚ) - 2 * k = -(p : ℚ) := by
      have : (2 * k : ℚ) = n + p := by exact_mod_cast hk
      linarith
    rw [linF, this]
  have hsplit : fam3H n k = ((C (-(p : ℚ)) + C 2 * X) * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k - p), denF k k') *
      (((C (-(p : ℚ)) + X)⁻¹) ^ 4 * (C (-(p : ℚ) / 2) + X) ^ 6) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid hodd hj0, hlin]
    ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_gen hp2 padicNorm_natCast_self)
  refine PInt.mul (PInt.mul ?_ ?_) ?_
  · refine PInt_C_add_C_mul_X ?_ ?_
    · rw [padicNorm.neg, padicNorm_natCast_self]; exact inv_le_one_of_one_le₀ one_lt_p_rat.le
    · exact_mod_cast padicNorm_natCast_le_one' 2
  · refine (PUnitS.prod _ _ (fun j hj => ?_)).1
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine (PUnitS.prod _ _ (fun k' hk' => ?_)).1
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **Partners of the generic nodes**, `k ∈ [h - p, n - h]`, `2k ≠ n - p` (partner `k + p`). -/
theorem HB_generic_partner (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk1 : ((p : ℤ) + 1) / 2 - p ≤ k) (hk2 : k ≤ n - ((p : ℤ) + 1) / 2)
    (hk3 : 2 * k ≠ n - p) : HB p (fam3H n k) (-2) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  set j0 : ℕ := (k + p - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k + p - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k + p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k + p) = ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by simp [denF]
  have hsplit : fam3H n k = (linF n k * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') *
      (((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 * (C (-(-(p : ℚ)) / 2) + X) ^ 6) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid' hodd hj0]
    ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_gen hp2 padicNorm_neg_natCast_self)
  refine (PUnitS.mul (PUnitS.mul ?_ ?_) ?_).1
  · apply linF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun j hj => ?_)
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine PUnitS.prod _ _ (fun k' hk' => ?_)
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

/-- **The partner of `g*`** (`2k = n - p`). -/
theorem HB_gstar_partner (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {k : ℤ} (hk : 2 * k = n - p) : HB p (fam3H n k) (-2) := by
  have h13 := p_ge_13 hn hlow hup
  have hodd := p_odd (p := p) h13
  have hp2 : p ≠ 2 := by omega
  set j0 : ℕ := (k + p - ((p : ℤ) + 1) / 2).toNat with hj0def
  have hj0 : (j0 : ℤ) = k + p - ((p : ℤ) + 1) / 2 := Int.toNat_of_nonneg (by omega)
  have hj0mem : j0 ∈ Finset.range n := by simp only [Finset.mem_range]; omega
  have hmem : k + p ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hden : denF k (k + p) = ((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 := by simp [denF]
  have hlin : linF n k = C (p : ℚ) + C 2 * X := by
    have : (n : ℚ) - 2 * k = (p : ℚ) := by
      have : (2 * k : ℚ) = n - p := by exact_mod_cast hk
      linarith
    rw [linF, this]
  have hsplit : fam3H n k = ((C (p : ℚ) + C 2 * X) * (∏ j ∈ (Finset.range n).erase j0, numF k j) *
      ∏ k' ∈ ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k).erase (k + p), denF k k') *
      (((C (-(-(p : ℚ))) + X)⁻¹) ^ 4 * (C (-(-(p : ℚ)) / 2) + X) ^ 6) := by
    rw [fam3H_eq, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hj0mem, hden,
      numF_mid' hodd hj0, hlin]
    ring
  rw [hsplit]
  refine HB.mul_PInt ?_ (HB_gen hp2 padicNorm_neg_natCast_self)
  refine PInt.mul (PInt.mul ?_ ?_) ?_
  · refine PInt_C_add_C_mul_X ?_ ?_
    · rw [padicNorm_natCast_self]; exact inv_le_one_of_one_le₀ one_lt_p_rat.le
    · exact_mod_cast padicNorm_natCast_le_one' 2
  · refine (PUnitS.prod _ _ (fun j hj => ?_)).1
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have : (j : ℤ) ≠ j0 := by exact_mod_cast hj.1
    apply numF_unit hp2; apply not_dvd_of_small <;> omega
  · refine (PUnitS.prod _ _ (fun k' hk' => ?_)).1
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk'
    apply denF_unit; apply not_dvd_of_small <;> omega

end Nodes

end W2
end Hankel2
