import RequestProject.Zeta35.Reflection
import RequestProject.Zeta7.Hankel2.Family3

/-!
# Purity (paper N, Lemma 2.2; W, Lemma 2.2 with `p = 3`, `q = 4`, `d = 1`; CLAIMS T2)

For `deg(P W) ≤ −2` (i.e. `deg P ≤ 4(2R+1) − 2`, which is `12n + 2` for even `n`):

* `hasVolkenborn_term`: each of the two Volkenborn integrals `∫_{ℤ₃} (P W)'(t + a/3) dt`, `a = 1, 2`,
  exists, with an explicit value;
* `purity`: `L(P) = ∑_k ∑_{a ≤ 3} (β_{k,a} + ζ₃(5) α_{k,a}) P_a(k) = b(P) + a(P) ζ₃(5)`;
* `aeval_zeta_hankelPoly`: for even `n` and `K ≤ 6n + 2`, `Δ_K(ζ₃(5)) = det[L(x^{i+j})]_{i,j<K}`.

Proof: partial fractions (`Zeta35.PF.eq_sum`), one derivative on the open set of non-poles, the
integer-shift formula for `∫ (t + a/3 + k)^{-M}` (both signs of `k`), the identification of the
two-residue harmonic sums with `S_k(M)` (`sum_shiftCorr`), `I_3 = I_5 = 0` (`IM_odd`), the
residue theorem for the `I_2` terms, and `I_4 = 4·3⁵ ζ₃(5)`.
-/

open Polynomial Filter Topology Finset

namespace Zeta35

open Hankel2

/-! ### The non-poles and the partial-fraction expansion of `P W` -/

/-- The non-poles of `W`. -/
def nonPoles (n : ℕ) : Set ℚ_[3] := {s | ∀ k ∈ nodes n, s + (k : ℚ_[3]) ≠ 0}

theorem isOpen_nonPoles (n : ℕ) : IsOpen (nonPoles n) := by
  have : nonPoles n = ⋂ k ∈ nodes n, {s : ℚ_[3] | s + (k : ℚ_[3]) ≠ 0} := by
    ext s; simp [nonPoles]
  rw [this]
  exact isOpen_biInter_finset fun k _ =>
    isOpen_ne_fun (continuous_id.add continuous_const) continuous_const

theorem nat_add_a_mem_nonPoles (n t : ℕ) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    (t : ℚ_[3]) + (a : ℚ_[3]) / 3 ∈ nonPoles n := by
  intro k _
  have h := add_ne_zero_of_norm_lt (c := (a : ℚ_[3]) / 3) (x := (t : ℚ_[3]) + (k : ℚ_[3]))
    (by simpa using Padic.norm_int_le_one (p := 3) ((t : ℤ) + k)) (norm_a_div_three ha1 ha2)
  intro h0; apply h; linear_combination h0

theorem aeval_Dki (S : Finset ℤ) (k : ℤ) (i : ℕ) (s : ℚ_[3]) :
    aeval s (PF.Dki S k i) = (s + k) ^ (4 - i) * ∏ k' ∈ S.erase k, (s + k') ^ 4 := by
  simp [PF.Dki, map_prod]

/-- `P W = ∑_k ∑_{i=1}^{4} r_{k,i}(P) (t+k)^{-i}` on the non-poles. -/
theorem PW_eq_sum (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 1 ≤ 4 * (nodes n).card) {s : ℚ_[3]}
    (hs : s ∈ nonPoles n) :
    aeval s P * W n s = ∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
      ((PF.resCoef (nodes n) P k i : ℚ) : ℚ_[3]) * ((s + k) ^ i)⁻¹ := by
  have hpf := congrArg (aeval s) (PF.eq_sum (nodes n) P hP)
  rw [map_sum] at hpf
  have hden : ∏ k ∈ nodes n, (s + (k : ℚ_[3])) ^ 4 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hs k hk)
  rw [W, hpf, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  rw [map_mul, aeval_C, aeval_Dki, ← Finset.mul_prod_erase _ _ hk]
  have hk0 : s + (k : ℚ_[3]) ≠ 0 := hs k hk
  have herase : ∏ k' ∈ (nodes n).erase k, (s + (k' : ℚ_[3])) ^ 4 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' hk' => pow_ne_zero _ (hs k' (Finset.mem_of_mem_erase hk'))
  have h4 : (s + (k : ℚ_[3])) ^ 4 = (s + k) ^ (4 - i) * (s + k) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [h4]
  simp only [eq_ratCast]
  field_simp

/-! ### One derivative -/

theorem hasDerivAt_inv_pow_add3 (a s : ℚ_[3]) (hs : s + a ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    HasDerivAt (fun y => ((y + a) ^ m)⁻¹) (-(m : ℚ_[3]) * ((s + a) ^ (m + 1))⁻¹) s := by
  have h1 := (hasDerivAt_pow m (s + a)).comp s ((hasDerivAt_id s).add_const a)
  have h : HasDerivAt (fun y => ((y + a) ^ m)⁻¹)
      (-((m : ℚ_[3]) * (s + a) ^ (m - 1) * 1) / ((s + a) ^ m) ^ 2) s :=
    h1.inv (by simpa [Function.comp] using pow_ne_zero m hs)
  refine h.congr_deriv ?_
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_one]
  field_simp
  ring

/-- The derivative of the simple-fraction expansion. -/
noncomputable def G1 (n : ℕ) (P : ℚ[X]) (s : ℚ_[3]) : ℚ_[3] :=
  ∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
    ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) * ((s + k) ^ (i + 1))⁻¹

theorem deriv_PW (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 1 ≤ 4 * (nodes n).card) {s : ℚ_[3]}
    (hs : s ∈ nonPoles n) :
    deriv (fun y => aeval y P * W n y) s = G1 n P s := by
  have hev : (fun y => aeval y P * W n y) =ᶠ[𝓝 s] fun y => ∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
      ((PF.resCoef (nodes n) P k i : ℚ) : ℚ_[3]) * ((y + k) ^ i)⁻¹ :=
    Filter.eventuallyEq_of_mem ((isOpen_nonPoles n).mem_nhds hs) fun y hy => PW_eq_sum n P hP hy
  rw [hev.deriv_eq]
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum fun k hk => HasDerivAt.fun_sum fun i hi => ?_
  obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
  have h := (hasDerivAt_inv_pow_add3 (k : ℚ_[3]) s (hs k hk) (m := i) hi1).const_mul
    (((PF.resCoef (nodes n) P k i : ℚ) : ℚ_[3]))
  convert h using 1
  push_cast
  ring

/-! ### Integer shifts of both signs -/

variable {p : ℕ} [Fact p.Prime]

/-- The correction term of the integer-shift formula:
`∫ (t + c + k)^{-M} dt = ∫ (t + c)^{-M} dt − shiftCorr c k M`. -/
noncomputable def shiftCorr (c : ℚ_[p]) (k : ℤ) (M : ℕ) : ℚ_[p] :=
  if 0 ≤ k then (M : ℚ_[p]) * ∑ l ∈ range k.toNat, ((c + (l : ℚ_[p])) ^ (M + 1))⁻¹
  else -(M : ℚ_[p]) * ∑ l ∈ Icc 1 k.natAbs, ((-(l : ℚ_[p]) + c) ^ (M + 1))⁻¹

theorem hasVolkenborn_shift_int {c : ℚ_[p]} (hc : 1 < ‖c‖) (M : ℕ) {I : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ M)⁻¹) I) (k : ℤ) :
    HasVolkenborn p (fun t => ((t + (c + (k : ℚ_[p]))) ^ M)⁻¹) (I - shiftCorr c k M) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, k = N := ⟨k.toNat, by omega⟩
    rw [shiftCorr, if_pos hk]
    simpa using hasVolkenborn_shift_nat hc M hI N
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, k = -(N : ℤ) := ⟨k.natAbs, by omega⟩
    rw [shiftCorr, if_neg hk]
    have h := hasVolkenborn_translate_back hc M N hI
    have hfun : (fun t : ℚ_[p] => ((t - (N : ℚ_[p]) + c) ^ M)⁻¹) =
        fun t => ((t + (c + ((-(N : ℤ) : ℤ) : ℚ_[p]))) ^ M)⁻¹ := by
      funext t; push_cast; ring_nf
    rw [hfun] at h
    convert h using 1
    simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_mul, Finset.sum_neg_distrib,
      ← Finset.mul_sum]

/-! ### The two-residue harmonic sums are `S_k(M)` -/

theorem hsum3_succ (N M : ℕ) :
    hsum3 (N + 1) M = hsum3 N M + (((3 * N + 1 : ℕ) : ℚ) ^ (M + 1))⁻¹ +
      (((3 * N + 2 : ℕ) : ℚ) ^ (M + 1))⁻¹ := by
  unfold hsum3
  rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    if_neg (by omega : ¬ ¬ 3 ∣ 3 * N), if_pos (by omega : ¬ 3 ∣ 3 * N + 1),
    if_pos (by omega : ¬ 3 ∣ 3 * N + 1 + 1)]
  push_cast
  ring

theorem hsum3_zero (M : ℕ) : hsum3 0 M = 0 := by simp [hsum3]

theorem sum_pos_shift_eq (N M : ℕ) :
    ∑ l ∈ range N, (((((1 : ℕ) : ℚ) / 3 + l) ^ (M + 1))⁻¹ + ((((2 : ℕ) : ℚ) / 3 + l) ^ (M + 1))⁻¹)
      = 3 ^ (M + 1) * hsum3 N M := by
  induction N with
  | zero => simp [hsum3_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, hsum3_succ]
      have e1 : (((1 : ℕ) : ℚ) / 3 + (N : ℚ)) = ((3 * N + 1 : ℕ) : ℚ) / 3 := by push_cast; ring
      have e2 : (((2 : ℕ) : ℚ) / 3 + (N : ℚ)) = ((3 * N + 2 : ℕ) : ℚ) / 3 := by push_cast; ring
      rw [e1, e2, div_pow, div_pow, inv_div, inv_div]
      ring

theorem sum_neg_shift_eq (N M : ℕ) :
    ∑ l ∈ Icc 1 N, (((-(l : ℚ) + ((1 : ℕ) : ℚ) / 3) ^ (M + 1))⁻¹ +
      ((-(l : ℚ) + ((2 : ℕ) : ℚ) / 3) ^ (M + 1))⁻¹)
      = (-1) ^ (M + 1) * 3 ^ (M + 1) * hsum3 N M := by
  induction N with
  | zero => simp [hsum3_zero]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, hsum3_succ]
      have e1 : (-((N + 1 : ℕ) : ℚ) + ((1 : ℕ) : ℚ) / 3) = -(((3 * N + 2 : ℕ) : ℚ) / 3) := by
        push_cast; ring
      have e2 : (-((N + 1 : ℕ) : ℚ) + ((2 : ℕ) : ℚ) / 3) = -(((3 * N + 1 : ℕ) : ℚ) / 3) := by
        push_cast; ring
      have h1 : ((-1 : ℚ) ^ (M + 1))⁻¹ = (-1) ^ (M + 1) := by
        rw [← inv_pow, inv_neg, inv_one]
      have key : ∀ x : ℚ, ((-(x / 3)) ^ (M + 1))⁻¹ = (-1) ^ (M + 1) * 3 ^ (M + 1) * (x ^ (M + 1))⁻¹ := by
        intro x
        rw [show (-(x / 3)) ^ (M + 1) = ((-1) ^ (M + 1) * x ^ (M + 1)) / 3 ^ (M + 1) by
          rw [neg_pow, div_pow]; ring, div_eq_mul_inv, mul_inv, mul_inv, inv_inv, h1]
        ring
      rw [e1, e2, key, key]
      ring

/-- **The two residues `a = 1, 2` together give `S_k(M)`**:
`∑_{a=1,2} shiftCorr(a/3, k, M) = −S_k(M)`. -/
theorem sum_shiftCorr (k : ℤ) (M : ℕ) :
    ∑ a ∈ Icc (1 : ℕ) 2, shiftCorr ((a : ℚ_[3]) / 3) k M = -((Sk k M : ℚ) : ℚ_[3]) := by
  rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  by_cases hk : 0 ≤ k
  · rw [shiftCorr, shiftCorr, if_pos hk, if_pos hk, ← mul_add, ← Finset.sum_add_distrib]
    have h := congrArg (fun x : ℚ => (x : ℚ_[3])) (sum_pos_shift_eq k.toNat M)
    push_cast at h ⊢
    rw [h]
    rcases hk.lt_or_eq with hk0 | hk0
    · rw [Sk, if_pos hk0, show k.natAbs = k.toNat by omega]
      push_cast; ring
    · subst hk0
      simp [Sk, hsum3_zero]
  · rw [shiftCorr, shiftCorr, if_neg hk, if_neg hk, ← mul_add, ← Finset.sum_add_distrib]
    have h := congrArg (fun x : ℚ => (x : ℚ_[3])) (sum_neg_shift_eq k.natAbs M)
    push_cast at h ⊢
    rw [h, Sk, if_neg (by omega), if_pos (by omega)]
    push_cast; ring

/-! ### Integration -/

/-- **Existence and value of each of the two integrals** `∫_{ℤ₃} (P W)'(t + a/3) dt`. -/
theorem hasVolkenborn_term (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 1 ≤ 4 * (nodes n).card)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    HasVolkenborn 3 (fun t => deriv (fun s => aeval s P * W n s) (t + (a : ℚ_[3]) / 3))
      (∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
        ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) *
          (volkInt 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ (i + 1))⁻¹) -
            shiftCorr ((a : ℚ_[3]) / 3) k (i + 1))) := by
  have h : HasVolkenborn 3 (fun t => ∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
      ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) *
        ((t + ((a : ℚ_[3]) / 3 + (k : ℚ_[3]))) ^ (i + 1))⁻¹)
      (∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
        ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) *
          (volkInt 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ (i + 1))⁻¹) -
            shiftCorr ((a : ℚ_[3]) / 3) k (i + 1))) := by
    refine HasVolkenborn.sum _ _ _ fun k _ => HasVolkenborn.sum _ _ _ fun i _ => ?_
    exact (hasVolkenborn_shift_int (norm_a_div_three ha1 ha2) (i + 1)
      (hasVolkenborn_volkInt_a ha1 ha2 (i + 1)) k).const_mul _
  refine Fam3.HasVolkenborn.congr_nat (fun t => ?_) h
  show _ = deriv (fun s => aeval s P * W n s) ((t : ℚ_[3]) + (a : ℚ_[3]) / 3)
  rw [deriv_PW n P hP (nat_add_a_mem_nonPoles n t ha1 ha2), G1]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring_nf

/-- The node form of `L(P)` before the evaluation of the `I_M`. -/
theorem L_eq_sum (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 1 ≤ 4 * (nodes n).card) :
    L n P = ∑ k ∈ nodes n, ∑ i ∈ Icc 1 4,
      ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) *
        (IM (i + 1) + ((Sk k (i + 1) : ℚ) : ℚ_[3])) := by
  rw [L, Finset.sum_congr rfl fun a ha => (hasVolkenborn_term n P hP
    (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2).volkInt_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_shiftCorr, IM, sub_neg_eq_add]

/-! ### Resummation into `α`, `β` -/

theorem sum4 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Icc 1 4, f i = f 1 + f 2 + f 3 + f 4 := by
  rw [show Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp [add_assoc]

theorem resum_beta (J H S : ℕ → ℚ) :
    ∑ i ∈ Icc 1 4, (∑ j ∈ range (5 - i), J j * H (4 - i - j)) * (-(i : ℚ)) * S (i + 1) =
      ∑ a ∈ range 4, (-∑ i ∈ Icc 1 (4 - a), (i : ℚ) * H (4 - i - a) * S (i + 1)) * J a := by
  rw [sum4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show Icc 1 (4 - 0) = ({1, 2, 3, 4} : Finset ℕ) by decide,
    show Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) by decide,
    show Icc 1 (4 - 2) = ({1, 2} : Finset ℕ) by decide,
    show Icc 1 (4 - 3) = ({1} : Finset ℕ) by decide]
  simp
  ring

theorem resum_alpha (J H : ℕ → ℚ) :
    -(3 * (4 * 3 ^ 5)) * ∑ j ∈ range (5 - 3), J j * H (4 - 3 - j) =
      ∑ a ∈ range 4, (if a ≤ 1 then -(3 * (4 * 3 ^ 5)) * H (1 - a) else 0) * J a := by
  simp [Finset.sum_range_succ]
  ring

/-- **Purity (N, Lemma 2.2)**, in the form `L(P) = b(P) + a(P) ζ₃(5)`, for `deg(P W) ≤ −2`. -/
theorem L_eq_bL_add_aL (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 2 ≤ 4 * (nodes n).card) :
    L n P = (bL n P : ℚ_[3]) + (aL n P : ℚ_[3]) * zeta3 5 := by
  rw [L_eq_sum n P (by omega)]
  have hres := PF.sum_resCoef_one_eq_zero (nodes n) P hP
  have h3 : IM 3 = 0 := IM_odd 3 (by decide)
  have h5 : IM 5 = 0 := IM_odd 5 (by decide)
  have hsplit : ∀ k ∈ nodes n, ∑ i ∈ Icc 1 4,
      ((PF.resCoef (nodes n) P k i * (-(i : ℚ)) : ℚ) : ℚ_[3]) *
        (IM (i + 1) + ((Sk k (i + 1) : ℚ) : ℚ_[3])) =
      -(PF.resCoef (nodes n) P k 1 : ℚ_[3]) * IM 2 +
        ((∑ a ∈ range 4, betaC n k a * Pjet P k a : ℚ) : ℚ_[3]) +
        ((∑ a ∈ range 4, alphaC n k a * Pjet P k a : ℚ) : ℚ_[3]) * zeta3 5 := by
    intro k _
    have hb := resum_beta (fun j => Pjet P k j) (fun b => Hk n k b) (fun M => Sk k M)
    have ha := resum_alpha (fun j => Pjet P k j) (fun b => Hk n k b)
    have hB : ∑ a ∈ range 4, betaC n k a * Pjet P k a =
        ∑ i ∈ Icc 1 4, PF.resCoef (nodes n) P k i * (-(i : ℚ)) * Sk k (i + 1) := by
      simp only [betaC]; rw [← hb]; rfl
    have hA : ∑ a ∈ range 4, alphaC n k a * Pjet P k a =
        -(3 * (4 * 3 ^ 5)) * PF.resCoef (nodes n) P k 3 := by
      simp only [alphaC]; rw [← ha]; rfl
    rw [hA, hB, sum4, sum4, IM_four] at *
    push_cast
    rw [h3, h5]
    ring
  have hres' : ∑ k ∈ nodes n, (PF.resCoef (nodes n) P k 1 : ℚ_[3]) = 0 := by
    rw [← Rat.cast_sum, hres, Rat.cast_zero]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib, hres', neg_zero, zero_mul,
    zero_add, bL, aL]
  push_cast
  ring

/-- **Purity (N, Lemma 2.2; CLAIMS T2)**: if `deg(P W) ≤ −2`, then both Volkenborn integrals
defining `L(P)` exist, and
`L(P) = ∑_k ∑_{a ≤ 3} (β_{k,a} + ζ₃(5) α_{k,a}) P_a(k) = b(P) + a(P) ζ₃(5)`. -/
theorem purity (n : ℕ) (P : ℚ[X]) (hP : P.natDegree + 2 ≤ 4 * (nodes n).card) :
    (∀ a ∈ Icc (1 : ℕ) 2, ∃ I, HasVolkenborn 3
      (fun t => deriv (fun s => aeval s P * W n s) (t + (a : ℚ_[3]) / 3)) I) ∧
    L n P = ∑ k ∈ nodes n, ∑ a ∈ range 4,
      ((betaC n k a : ℚ_[3]) + zeta3 5 * (alphaC n k a : ℚ_[3])) * (Pjet P k a : ℚ_[3]) ∧
    L n P = (bL n P : ℚ_[3]) + (aL n P : ℚ_[3]) * zeta3 5 := by
  refine ⟨fun a ha => ⟨_, hasVolkenborn_term n P (by omega) (Finset.mem_Icc.mp ha).1
    (Finset.mem_Icc.mp ha).2⟩, ?_, L_eq_bL_add_aL n P hP⟩
  rw [L_eq_bL_add_aL n P hP, aL, bL]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **Purity for even `n`**: for `deg P ≤ 12n + 2`, `L(P) = b(P) + a(P) ζ₃(5)`. -/
theorem purity_even {n : ℕ} (hn : Even n) (P : ℚ[X]) (hP : P.natDegree ≤ 12 * n + 2) :
    L n P = (bL n P : ℚ_[3]) + (aL n P : ℚ_[3]) * zeta3 5 :=
  L_eq_bL_add_aL n P (by rw [card_nodes_of_even hn]; omega)

/-- **`Δ_K(ζ₃(5)) = det[L(x^{i+j})]`** for even `n` and `K ≤ 6n + 2`. -/
theorem aeval_zeta_hankelPoly {n K : ℕ} (hn : Even n) (hK : K ≤ 6 * n + 2) :
    aeval (zeta3 5) (hankelPoly n K) =
      (Matrix.of fun i j : Fin K => L n (X ^ ((i : ℕ) + j))).det := by
  rw [hankelPoly, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, aeval_C,
    aeval_X, eq_ratCast]
  rw [purity_even hn _ (by rw [natDegree_X_pow]; omega)]

end Zeta35
