import Mathlib

/-!
# The local blocks of the non-vanishing argument (paper N, Lemma 6.1; CLAIMS T6)

In the coordinate `w = (t + k)/ℓ` of a pair `{k, k − ℓ}` (node at `0`, mate at `1`, virtual
harmonic poles at `1/3, 2/3`), N defines, for `j ∈ {0, 1, 2}`,

`Λ_j(f) = Res_{w=0} f Σ_{m ≤ j}(m/3 − w)^{−3} / (w⁴(w−1)⁴) − Res_{w=1} f Σ_{m > j}(m/3 − w)^{−3} / (w⁴(w−1)⁴)`,

`m ∈ {1, 2}`, and `G_j = [Λ_j(w^{a+b})]_{a,b<4}`.

Since `w⁴` (resp. `(w−1)⁴`) is the only pole factor at `w = 0` (resp. `w = 1`), the residues are
Taylor coefficients:

* `Res_{w=0} w^e S(w) / (w⁴(w−1)⁴) = [w³] (w^e S(w) (w − 1)^{−4})`,
* `Res_{w=1} w^e S(w) / (w⁴(w−1)⁴) = [v³] ((1+v)^e S(1+v) (1+v)^{−4})` (`w = 1 + v`),

computed here in the power-series ring `ℚ⟦X⟧` (`res0`, `res1`, `Lam`).  We prove

* `coeff_invSub_pow`: `[w^n] (c − w)^{−(t+1)} = C(n+t, t) c^{−(n+t+1)}` (the Laurent coefficients);
* **`det_G0`, `det_G2`: `det G_0 = det G_2 = 3^20/2^12`**, and **`det_G1`: `det G_1 = 3^20·5²`**;
* `det_G_padicValRat`: every `det G_j` is an `ℓ`-adic unit for every prime `ℓ ≥ 7`.
-/

open PowerSeries Finset

namespace Zeta35.Blocks

/-- The geometric series `(c − w)^{−1} = Σ_n c^{−(n+1)} w^n`. -/
noncomputable def geom (c : ℚ) : ℚ⟦X⟧ := mk fun n => (c ^ (n + 1))⁻¹

theorem geom_mul_sub {c : ℚ} (hc : c ≠ 0) : geom c * (C c - X) = 1 := by
  ext n
  rw [mul_sub, map_sub, coeff_mul_C, mul_comm (geom c) X]
  rcases n with _ | n
  · simp [geom, coeff_zero_eq_constantCoeff, hc]
  · rw [coeff_succ_X_mul]
    simp only [geom, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
    field_simp
    ring

/-- `(c − w)^{−s}` in `ℚ⟦X⟧`. -/
noncomputable def invSub (c : ℚ) (s : ℕ) : ℚ⟦X⟧ := ((C c - X) ^ s)⁻¹

theorem invSub_eq {c : ℚ} (hc : c ≠ 0) (s : ℕ) : invSub c s = geom c ^ s := by
  rw [invSub, PowerSeries.inv_eq_iff_mul_eq_one]
  · rw [← mul_pow, geom_mul_sub hc, one_pow]
  · simp [hc]

theorem hockey (t n : ℕ) :
    ∑ i ∈ range (n + 1), (i + t).choose t = (n + t + 1).choose (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, show n + 1 + t + 1 = (n + t + 1) + 1 by ring,
        Nat.choose_succ_succ (n + t + 1) t, show n + 1 + t = n + t + 1 by ring]
      ring

/-- **The Laurent coefficients**: `[w^n] (c − w)^{−(t+1)} = C(n+t, t) c^{−(n+t+1)}`. -/
theorem coeff_geom_pow (c : ℚ) (t n : ℕ) :
    coeff n (geom c ^ (t + 1)) = ((n + t).choose t : ℚ) * (c ^ (n + t + 1))⁻¹ := by
  induction t generalizing n with
  | zero => simp [geom]
  | succ t ih =>
      rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have h : ∀ i ∈ range (n + 1), coeff i (geom c ^ (t + 1)) * coeff (n - i) (geom c) =
          ((i + t).choose t : ℚ) * (c ^ (n + (t + 1) + 1))⁻¹ := by
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [ih, geom, coeff_mk, mul_assoc, ← mul_inv, ← pow_add]
        congr 3
        omega
      rw [Finset.sum_congr rfl h, ← Finset.sum_mul]
      congr 1
      rw [show n + (t + 1) = n + t + 1 by ring]
      exact_mod_cast hockey t n

theorem coeff_invSub_pow {c : ℚ} (hc : c ≠ 0) (t n : ℕ) :
    coeff n (invSub c (t + 1)) = ((n + t).choose t : ℚ) * (c ^ (n + t + 1))⁻¹ := by
  rw [invSub_eq hc, coeff_geom_pow]

theorem coeff_one_add_X_pow (e t : ℕ) : coeff t ((1 + X : ℚ⟦X⟧) ^ e) = (e.choose t : ℚ) := by
  have : ((1 + X : ℚ⟦X⟧) ^ e) = (((1 + Polynomial.X) ^ e : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- `Res_{w=0} w^e Σ_{m ≤ j}(m/3 − w)^{−3} / (w⁴(w−1)⁴) = [w³] w^e Σ_{m≤j}(m/3 − w)^{−3} (w−1)^{−4}`. -/
noncomputable def res0 (j e : ℕ) : ℚ :=
  coeff 3 (X ^ e * (∑ m ∈ (Icc 1 2).filter (fun m => m ≤ j), invSub ((m : ℚ) / 3) 3) *
    ((X - 1) ^ 4)⁻¹)

/-- `Res_{w=1} w^e Σ_{m > j}(m/3 − w)^{−3} / (w⁴(w−1)⁴)`, in the variable `v = w − 1`:
`[v³] (1+v)^e Σ_{m>j}(m/3 − 1 − v)^{−3} (1+v)^{−4}`. -/
noncomputable def res1 (j e : ℕ) : ℚ :=
  coeff 3 ((1 + X) ^ e * (∑ m ∈ (Icc 1 2).filter (fun m => j < m), invSub ((m : ℚ) / 3 - 1) 3) *
    ((1 + X) ^ 4)⁻¹)

/-- `Λ_j(w^e)`. -/
noncomputable def Lam (j e : ℕ) : ℚ := res0 j e - res1 j e

/-- The local block `G_j = [Λ_j(w^{a+b})]_{a,b<4}`. -/
noncomputable def G (j : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := fun a b => Lam j ((a : ℕ) + b)

/-! ### Explicit Laurent coefficients -/

theorem inv_X_sub_one_pow : ((X - 1 : ℚ⟦X⟧) ^ 4)⁻¹ = invSub 1 4 := by
  rw [invSub, map_one]; congr 1; ring

theorem inv_one_add_X_pow : ((1 + X : ℚ⟦X⟧) ^ 4)⁻¹ = invSub (-1) 4 := by
  rw [invSub]; congr 1; simp only [map_neg, map_one]; ring

theorem coeff_mul_range (φ ψ : ℚ⟦X⟧) (n : ℕ) :
    coeff n (φ * ψ) = ∑ i ∈ range (n + 1), coeff i φ * coeff (n - i) ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The `w = 0` residue in explicit Laurent coefficients. -/
theorem res0_eq (j e : ℕ) : res0 j e =
    if e ≤ 3 then ∑ m ∈ (Icc 1 2).filter (fun m => m ≤ j), ∑ i ∈ range (3 - e + 1),
      ((i + 2).choose 2 : ℚ) * (((m : ℚ) / 3) ^ (i + 2 + 1))⁻¹ *
        (((3 - e - i + 3).choose 3 : ℚ) * ((1 : ℚ) ^ (3 - e - i + 3 + 1))⁻¹)
    else 0 := by
  rw [res0, mul_assoc, coeff_X_pow_mul', inv_X_sub_one_pow]
  split_ifs with he
  · rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : ((m : ℚ) / 3) ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      positivity
    rw [coeff_mul_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_invSub_pow hm0, show (4 : ℕ) = 3 + 1 from rfl,
      coeff_invSub_pow one_ne_zero]
  · rfl

/-- The `w = 1` residue in explicit Laurent coefficients. -/
theorem res1_eq (j e : ℕ) : res1 j e =
    ∑ m ∈ (Icc 1 2).filter (fun m => j < m), ∑ t ∈ range 4, (e.choose t : ℚ) *
      ∑ i ∈ range (3 - t + 1),
        ((i + 2).choose 2 : ℚ) * (((m : ℚ) / 3 - 1) ^ (i + 2 + 1))⁻¹ *
          (((3 - t - i + 3).choose 3 : ℚ) * ((-1 : ℚ) ^ (3 - t - i + 3 + 1))⁻¹) := by
  rw [res1, mul_assoc, Finset.sum_mul, Finset.mul_sum, map_sum, inv_one_add_X_pow]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : ((m : ℚ) / 3 - 1) ≠ 0 := by
    have := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    intro h
    have : (m : ℚ) = 3 := by linarith
    have : m = 3 := by exact_mod_cast this
    omega
  rw [coeff_mul_range]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [coeff_one_add_X_pow, coeff_mul_range]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_invSub_pow hm0, show (4 : ℕ) = 3 + 1 from rfl,
    coeff_invSub_pow (by norm_num)]

theorem filter_le (j : ℕ) (hj : j ≤ 2) :
    (Icc 1 2).filter (fun m => m ≤ j) = if j = 0 then ∅ else if j = 1 then {1} else {1, 2} := by
  interval_cases j <;> decide

theorem filter_lt (j : ℕ) (hj : j ≤ 2) :
    (Icc 1 2).filter (fun m => j < m) = if j = 0 then {1, 2} else if j = 1 then {2} else ∅ := by
  interval_cases j <;> decide

/-! ### The three blocks -/

theorem Lam_0_0 : Lam 0 0 = (-531441/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_1 : Lam 0 1 = (-440559/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_2 : Lam 0 2 = (-361827/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_3 : Lam 0 3 = (-294273/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_4 : Lam 0 4 = (-236925/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_5 : Lam 0 5 = (-188811/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_0_6 : Lam 0 6 = (-148959/32) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 0 (by norm_num), filter_le 0 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_0 : Lam 1 0 = 0 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_1 : Lam 1 1 = (-10692) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_2 : Lam 1 2 = (-10692) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_3 : Lam 1 3 = (-8991) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_4 : Lam 1 4 = (-7290) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_5 : Lam 1 5 = (-5832) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_1_6 : Lam 1 6 = (-4617) := by
  rw [Lam, res0_eq, res1_eq, filter_lt 1 (by norm_num), filter_le 1 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_0 : Lam 2 0 = 531441/32 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_1 : Lam 2 1 = 45441/16 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_2 : Lam 2 2 = 6075/16 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_3 : Lam 2 3 = 243/8 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_4 : Lam 2 4 = 0 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_5 : Lam 2 5 = 0 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem Lam_2_6 : Lam 2 6 = 0 := by
  rw [Lam, res0_eq, res1_eq, filter_lt 2 (by norm_num), filter_le 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, Nat.choose]

theorem G0_eq : G 0 = !![(-531441/32), (-440559/32), (-361827/32), (-294273/32);
    (-440559/32), (-361827/32), (-294273/32), (-236925/32);
    (-361827/32), (-294273/32), (-236925/32), (-188811/32);
    (-294273/32), (-236925/32), (-188811/32), (-148959/32)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [G, Lam_0_0, Lam_0_1, Lam_0_2, Lam_0_3, Lam_0_4, Lam_0_5, Lam_0_6]

theorem G1_eq : G 1 = !![0, (-10692), (-10692), (-8991);
    (-10692), (-10692), (-8991), (-7290);
    (-10692), (-8991), (-7290), (-5832);
    (-8991), (-7290), (-5832), (-4617)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [G, Lam_1_0, Lam_1_1, Lam_1_2, Lam_1_3, Lam_1_4, Lam_1_5, Lam_1_6]

theorem G2_eq : G 2 = !![531441/32, 45441/16, 6075/16, 243/8;
    45441/16, 6075/16, 243/8, 0;
    6075/16, 243/8, 0, 0;
    243/8, 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [G, Lam_2_0, Lam_2_1, Lam_2_2, Lam_2_3, Lam_2_4, Lam_2_5, Lam_2_6]

/-- **N, Lemma 6.1**: `det G_0 = 3^20/2^12`. -/
theorem det_G0 : (G 0).det = 3 ^ 20 / 2 ^ 12 := by
  rw [G0_eq, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, Matrix.submatrix]
  norm_num

/-- **N, Lemma 6.1**: `det G_1 = 3^20·5²`. -/
theorem det_G1 : (G 1).det = 3 ^ 20 * 5 ^ 2 := by
  rw [G1_eq, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, Matrix.submatrix]
  norm_num

/-- **N, Lemma 6.1**: `det G_2 = 3^20/2^12`. -/
theorem det_G2 : (G 2).det = 3 ^ 20 / 2 ^ 12 := by
  rw [G2_eq, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, Matrix.submatrix]
  norm_num

theorem padicValRat_small (ℓ : ℕ) [Fact ℓ.Prime] (h7 : 7 ≤ ℓ) (q : ℕ) (hq0 : 0 < q) (hq : q < 7) :
    padicValRat ℓ (q : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h; have := Nat.le_of_dvd hq0 h; omega

/-- **N, Lemma 6.1 (consequence)**: every `det G_j` (`j ≤ 2`) is an `ℓ`-adic unit for every
prime `ℓ ≥ 7`. -/
theorem det_G_padicValRat (j : ℕ) (hj : j ≤ 2) (ℓ : ℕ) [Fact ℓ.Prime] (h7 : 7 ≤ ℓ) :
    padicValRat ℓ (G j).det = 0 := by
  have h2 := padicValRat_small ℓ h7 2 (by norm_num) (by norm_num)
  have h3 := padicValRat_small ℓ h7 3 (by norm_num) (by norm_num)
  have h5 := padicValRat_small ℓ h7 5 (by norm_num) (by norm_num)
  push_cast at h2 h3 h5
  interval_cases j
  · rw [det_G0, padicValRat.div (by norm_num) (by norm_num), padicValRat.pow (by norm_num),
      padicValRat.pow (by norm_num), h2, h3]; simp
  · rw [det_G1, padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow (by norm_num),
      padicValRat.pow (by norm_num), h3, h5]; simp
  · rw [det_G2, padicValRat.div (by norm_num) (by norm_num), padicValRat.pow (by norm_num),
      padicValRat.pow (by norm_num), h2, h3]; simp

end Zeta35.Blocks
