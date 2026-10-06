import RequestProject.Zeta7.Hankel2.PartialFrac3
import RequestProject.Zeta7.Hankel2.PurityInt

/-!
# The family-3 functional `L(P) = ∫_{ℤ₂} (P W)'''(t + ½) dt` (paper §1, §2)

For odd `n` (the definitions make sense for every `n`) the weight is
`W(t) = (2t+n) (t+½)_n^6 / ∏_{k=-n}^{2n} (t+k)^4` (`Hankel2.Fam3.W`), and for a polynomial
`P ∈ ℚ[x]` in the variable `x = t + n/2`,

  `L(P) = ∫_{ℤ₂} (P W)'''(t + ½) dt`   (`Hankel2.Fam3.famL`),

where `(P W)'''` is the third derivative (`iteratedDeriv 3`) of the `ℚ₂`-valued function
`t ↦ P(t + n/2) W(t)` and `∫_{ℤ₂}` is the Volkenborn integral.

This file proves, for `deg P ≤ 6n + 1`, that the Volkenborn integral exists and equals the
node expansion: with `F(t) = P(t + n/2)`,

  `L(P) = ∑_k ∑_{i=1}^{4} r_{k,i}(F) · (−φ_i) · I_{i+3,k}`,  `φ_i = i(i+1)(i+2)`,

and hence the value `6·2⁷ (∑_k −φ₃ r_{k,3}) ζ₂(7) + ∑_k ∑_i φ_i (i+3) r_{k,i} HS(k, i+4)`
(`Hankel2.Fam3.hasVolkenborn_integrandT`).  The steps are the partial-fraction identity of
`PartialFrac3`, differentiation of `(t+k)^{-i}` three times on the open set of non-poles,
and purity for integer shifts (`Hankel2.volkInt_pure_int`), with the residue theorem killing
`ζ₂(5)`.
-/

open Polynomial Filter Topology Finset

namespace Hankel2.Fam3

/-- The rising factorial `(y)_n = y (y+1) ⋯ (y+n-1)`. -/
def poch {R : Type*} [CommRing R] (y : R) (n : ℕ) : R := ∏ j ∈ range n, (y + j)

/-- The family-3 weight `W(t) = (2t+n)(t+½)_n^6 / ∏_{k=-n}^{2n} (t+k)^4` on `ℚ₂`. -/
noncomputable def W (n : ℕ) (t : ℚ_[2]) : ℚ_[2] :=
  (2 * t + n) * poch (t + 1 / 2) n ^ 6 / ∏ k ∈ Fam3PF.nodes n, (t + k) ^ 4

/-- **The family-3 functional** `L(P) = ∫_{ℤ₂} (P W)'''(t + ½) dt`, for `P ∈ ℚ[x]`,
`x = t + n/2`. -/
noncomputable def famL (n : ℕ) (P : ℚ[X]) : ℚ_[2] :=
  volkInt 2 (fun t => iteratedDeriv 3 (fun s => aeval (s + (n : ℚ_[2]) / 2) P * W n s) (t + 1 / 2))

/-- The same integrand for a polynomial `F` in the variable `t`. -/
noncomputable def integrandT (n : ℕ) (F : ℚ[X]) (t : ℚ_[2]) : ℚ_[2] :=
  iteratedDeriv 3 (fun s => aeval s F * W n s) t

/-- The set of non-poles of `W`. -/
def nonPoles (n : ℕ) : Set ℚ_[2] := {s | ∀ k ∈ Fam3PF.nodes n, s + (k : ℚ_[2]) ≠ 0}

theorem isOpen_nonPoles (n : ℕ) : IsOpen (nonPoles n) := by
  have : nonPoles n = ⋂ k ∈ Fam3PF.nodes n, {s : ℚ_[2] | s + (k : ℚ_[2]) ≠ 0} := by
    ext s; simp [nonPoles]
  rw [this]
  exact isOpen_biInter_finset fun k _ =>
    isOpen_ne_fun (continuous_id.add continuous_const) continuous_const

theorem nat_add_half_mem_nonPoles (n t : ℕ) : (t : ℚ_[2]) + 1 / 2 ∈ nonPoles n := by
  intro k _
  have h := add_ne_zero_of_norm_lt (c := (1 / 2 : ℚ_[2])) (x := (t : ℚ_[2]) + k)
    (by simpa using Padic.norm_int_le_one (p := 2) ((t : ℤ) + k)) norm_half_2
  intro h0; apply h; linear_combination h0

/-! ### Step 1: `F W` as a sum of simple fractions on the non-poles -/

theorem aeval_Dki (n : ℕ) (k : ℤ) (i : ℕ) (s : ℚ_[2]) :
    aeval s (Fam3PF.Dki n k i) =
      (s + k) ^ (4 - i) * ∏ k' ∈ (Fam3PF.nodes n).erase k, (s + k') ^ 4 := by
  simp [Fam3PF.Dki, map_prod]

theorem aeval_numPoly (n : ℕ) (F : ℚ[X]) (s : ℚ_[2]) :
    aeval s (Fam3PF.numPoly n F) = aeval s F * ((2 * s + n) * poch (s + 1 / 2) n ^ 6) := by
  simp only [Fam3PF.numPoly, map_mul, map_prod, map_pow, map_add, aeval_X, aeval_C, poch,
    ← Finset.prod_pow]
  simp only [eq_ratCast, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_div, Rat.cast_one]
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

theorem FW_eq_sum (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 2) {s : ℚ_[2]}
    (hs : s ∈ nonPoles n) :
    aeval s F * W n s = ∑ k ∈ Fam3PF.nodes n, ∑ i ∈ Icc 1 4,
      ((W3.Fam3.resCoef n F k i : ℚ) : ℚ_[2]) * ((s + k) ^ i)⁻¹ := by
  have hpf := congrArg (aeval s) (Fam3PF.numPoly_eq_sum n F hF)
  rw [aeval_numPoly, map_sum] at hpf
  have hden : ∏ k ∈ Fam3PF.nodes n, (s + (k : ℚ_[2])) ^ 4 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hs k hk)
  rw [W, ← mul_div_assoc, hpf, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  rw [map_mul, aeval_C, aeval_Dki, ← Finset.mul_prod_erase _ _ hk]
  have hk0 : s + (k : ℚ_[2]) ≠ 0 := hs k hk
  have herase : ∏ k' ∈ (Fam3PF.nodes n).erase k, (s + (k' : ℚ_[2])) ^ 4 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k' hk' => pow_ne_zero _ (hs k' (Finset.mem_of_mem_erase hk'))
  have h4 : (s + (k : ℚ_[2])) ^ 4 = (s + k) ^ (4 - i) * (s + k) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [h4]
  simp only [eq_ratCast]
  field_simp

/-! ### Step 2: three derivatives -/

/-- `d(i, j) = (−1)^j i(i+1)⋯(i+j−1)`, so that `(d/dt)^j (t+k)^{-i} = d(i,j) (t+k)^{-(i+j)}`. -/
def dco (i j : ℕ) : ℚ := (-1) ^ j * ∏ l ∈ range j, ((i : ℚ) + l)

theorem dco_succ (i j : ℕ) : dco i (j + 1) = -((i : ℚ) + j) * dco i j := by
  simp only [dco, pow_succ, Finset.prod_range_succ]; ring

theorem dco_zero (i : ℕ) : dco i 0 = 1 := by simp [dco]

theorem dco_three (i : ℕ) : dco i 3 = -((i : ℚ) * (i + 1) * (i + 2)) := by
  simp [dco, Finset.prod_range_succ]; ring

/-- The `j`-th derivative of the simple-fraction expansion. -/
noncomputable def Gj (n : ℕ) (F : ℚ[X]) (j : ℕ) (s : ℚ_[2]) : ℚ_[2] :=
  ∑ k ∈ Fam3PF.nodes n, ∑ i ∈ Icc 1 4,
    ((W3.Fam3.resCoef n F k i * dco i j : ℚ) : ℚ_[2]) * ((s + k) ^ (i + j))⁻¹

theorem hasDerivAt_inv_pow_add (a s : ℚ_[2]) (hs : s + a ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    HasDerivAt (fun y => ((y + a) ^ m)⁻¹) (-(m : ℚ_[2]) * ((s + a) ^ (m + 1))⁻¹) s := by
  have h1 := (hasDerivAt_pow m (s + a)).comp s ((hasDerivAt_id s).add_const a)
  have h : HasDerivAt (fun y => ((y + a) ^ m)⁻¹)
      (-((m : ℚ_[2]) * (s + a) ^ (m - 1) * 1) / ((s + a) ^ m) ^ 2) s :=
    h1.inv (by simpa [Function.comp] using pow_ne_zero m hs)
  refine h.congr_deriv ?_
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_one]
  field_simp
  ring

theorem hasDerivAt_Gj (n : ℕ) (F : ℚ[X]) (j : ℕ) {s : ℚ_[2]} (hs : s ∈ nonPoles n) :
    HasDerivAt (Gj n F j) (Gj n F (j + 1) s) s := by
  unfold Gj
  refine HasDerivAt.fun_sum fun k hk => HasDerivAt.fun_sum fun i hi => ?_
  obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
  have h := (hasDerivAt_inv_pow_add (k : ℚ_[2]) s (hs k hk) (m := i + j) (by omega)).const_mul
    (((W3.Fam3.resCoef n F k i * dco i j : ℚ) : ℚ_[2]))
  convert h using 1
  rw [dco_succ]
  push_cast
  ring_nf

theorem iteratedDeriv_FW (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 2) (j : ℕ) :
    ∀ s ∈ nonPoles n, iteratedDeriv j (fun y => aeval y F * W n y) s = Gj n F j s := by
  induction j with
  | zero =>
      intro s hs
      rw [iteratedDeriv_zero, FW_eq_sum n F hF hs, Gj]
      simp [dco_zero]
  | succ j ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun y => aeval y F * W n y) =ᶠ[𝓝 s] Gj n F j :=
        Filter.eventuallyEq_of_mem ((isOpen_nonPoles n).mem_nhds hs) fun y hy => ih y hy
      rw [hev.deriv_eq, (hasDerivAt_Gj n F j hs).deriv]

/-! ### Step 3: integration -/

theorem HasVolkenborn.congr_nat {p : ℕ} [Fact p.Prime] {f g : ℚ_[p] → ℚ_[p]} {I : ℚ_[p]}
    (h : ∀ t : ℕ, f t = g t) (hf : HasVolkenborn p f I) : HasVolkenborn p g I := by
  have : volkSum p f = volkSum p g := by
    funext N; simp only [volkSum, h]
  rwa [HasVolkenborn, ← this]

/-- `φ_i = i(i+1)(i+2)`. -/
def phi (i : ℕ) : ℚ := (i : ℚ) * (i + 1) * (i + 2)

/-- **Purity / node expansion of `L` in the `t`-variable.**  For `deg F ≤ 6n + 1` the
Volkenborn integral of `(F W)'''(t + ½)` exists and equals
`6·2⁷ (∑_k −φ₃ r_{k,3}(F)) ζ₂(7) + ∑_k ∑_{i=1}^{4} φ_i (i+3) r_{k,i}(F) HS(k, i+4)`. -/
theorem hasVolkenborn_integrandT (n : ℕ) (F : ℚ[X]) (hF : F.natDegree ≤ 6 * n + 1) :
    HasVolkenborn 2 (fun t => integrandT n F (t + 1 / 2))
      ((6 * 2 ^ 7 * ∑ k ∈ Fam3PF.nodes n,
          ((-(phi 3) * W3.Fam3.resCoef n F k 3 : ℚ) : ℚ_[2])) * zeta2 7
        + ∑ k ∈ Fam3PF.nodes n, ∑ i ∈ Icc 1 4,
          ((phi i * (i + 3) * W3.Fam3.resCoef n F k i * HS k (i + 4) : ℚ) : ℚ_[2])) := by
  set c : ℕ → ℤ → ℚ_[2] := fun i k => ((W3.Fam3.resCoef n F k i * dco i 3 : ℚ) : ℚ_[2]) with hc
  have hres : ∑ k ∈ Fam3PF.nodes n, c 1 k = 0 := by
    simp only [hc]
    rw [← Rat.cast_sum, ← Finset.sum_mul, Fam3PF.sum_resCoef_one_eq_zero n F hF]
    simp
  have h := volkInt_pure_int (Fam3PF.nodes n) (c 1) (c 2) (c 3) (c 4) hres
  have hI : Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have hsum4 : ∀ f : ℕ → ℚ_[2], ∑ i ∈ Icc 1 4, f i = f 1 + f 2 + f 3 + f 4 := by
    intro f; rw [hI]; simp; ring
  have h2 : HasVolkenborn 2 (fun t => ∑ k ∈ Fam3PF.nodes n,
        (c 1 k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 4)⁻¹
          + c 2 k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 5)⁻¹
          + c 3 k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 6)⁻¹
          + c 4 k * ((t + (1 / 2 + (k : ℚ_[2]))) ^ 7)⁻¹))
      ((6 * 2 ^ 7 * ∑ k ∈ Fam3PF.nodes n,
          ((-(phi 3) * W3.Fam3.resCoef n F k 3 : ℚ) : ℚ_[2])) * zeta2 7
        + ∑ k ∈ Fam3PF.nodes n, ∑ i ∈ Icc 1 4,
          ((phi i * (i + 3) * W3.Fam3.resCoef n F k i * HS k (i + 4) : ℚ) : ℚ_[2])) := by
    convert h using 1
    simp only [hc, dco_three, phi, HS, hsum4]
    norm_num
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, sub_eq_add_neg,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine HasVolkenborn.congr_nat (fun t => ?_) h2
  show _ = integrandT n F ((t : ℚ_[2]) + 1 / 2)
  rw [integrandT, iteratedDeriv_FW n F (by omega) 3 _ (nat_add_half_mem_nonPoles n t), Gj]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hsum4, hc]
  norm_num
  ring_nf

end Hankel2.Fam3
