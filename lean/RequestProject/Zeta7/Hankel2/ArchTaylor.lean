import RequestProject.Zeta7.Hankel2.ArchL1
import RequestProject.Zeta7.Hankel2.Taylor72

/-!
# Archimedean Taylor-coefficient and local-factor bounds (paper Lemma 6.2, steps (3) and (4))

* `SerBound F A Λ`: `|[u^b] F| ≤ A Λ^b` for all `b`; closed under products (`SerBound.mul`).
* `abs_Hk_le`: for odd `n`, `|H_k[b]| ≤ |h_k| Λ_n^b`, `Λ_n = LamA n = 6 + 24n`, where `h_k = H_k[0]`.  This ties the
  Taylor coefficients to the roots and poles `ρ` of `W̃_k` (the factors `2u + n − 2k`,
  `(u + j + ½ − k)^6`, `(u + k' − k)^{−4}`), each contributing `|e_ρ|/|ρ| ≤ 2|e_ρ|` to `Λ`.
* `abs_HS_le`: `|HS(k, M)| ≤ |k| 2^M`.
* `l1_cPoly_le`: `‖c_{k,a}‖₁ = ‖β_{k,a} + X α_{k,a}‖₁ ≤ Q_n |h_k|` with
  `Q_n = 10^7 (2n+1) Λ_n^3`, for odd `n` and every node `k`.
-/

open Finset

namespace Hankel2.ArchB

/-- `|[u^b] F| ≤ A Λ^b` for every `b`. -/
def SerBound (F : PowerSeries ℚ) (A Λ : ℝ) : Prop :=
  ∀ b : ℕ, |((PowerSeries.coeff b F : ℚ) : ℝ)| ≤ A * Λ ^ b

theorem sum_antidiag_pow_le {Λ M : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (b : ℕ) :
    ∑ x ∈ antidiagonal b, Λ ^ x.1 * M ^ x.2 ≤ (Λ + M) ^ b := by
  rw [(Commute.all Λ M).add_pow']
  refine sum_le_sum fun x _ => ?_
  rw [nsmul_eq_mul]
  have h1 : (1 : ℝ) ≤ (b.choose x.1 : ℝ) := by
    have := Nat.choose_pos (n := b) (k := x.1) (by
      have := Finset.mem_antidiagonal.1 ‹x ∈ antidiagonal b›; omega)
    exact_mod_cast this
  have h2 : 0 ≤ Λ ^ x.1 * M ^ x.2 := by positivity
  nlinarith

theorem SerBound.mul {F G : PowerSeries ℚ} {A B Λ M : ℝ} (hF : SerBound F A Λ)
    (hG : SerBound G B M) (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) :
    SerBound (F * G) (A * B) (Λ + M) := by
  intro b
  rw [PowerSeries.coeff_mul]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ antidiagonal b, |((PowerSeries.coeff x.1 F : ℚ) : ℝ) * (PowerSeries.coeff x.2 G : ℚ)|
      ≤ ∑ x ∈ antidiagonal b, (A * Λ ^ x.1) * (B * M ^ x.2) := by
        refine sum_le_sum fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hF _) (hG _) (abs_nonneg _) (by positivity)
    _ = A * B * ∑ x ∈ antidiagonal b, Λ ^ x.1 * M ^ x.2 := by
        rw [mul_sum]; refine sum_congr rfl fun x _ => by ring
    _ ≤ A * B * (Λ + M) ^ b := mul_le_mul_of_nonneg_left (sum_antidiag_pow_le hΛ hM b) (by positivity)

theorem SerBound.one {Λ : ℝ} (hΛ : 0 ≤ Λ) : SerBound 1 1 Λ := by
  intro b
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [Rat.cast_zero, abs_zero, one_mul]
    positivity

theorem SerBound.mono {F : PowerSeries ℚ} {A Λ Λ' : ℝ} (h : SerBound F A Λ) (hA : 0 ≤ A)
    (hΛ : 0 ≤ Λ) (hΛ' : Λ ≤ Λ') : SerBound F A Λ' := fun b =>
  (h b).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛ hΛ' b) hA)

theorem SerBound.prod {ι : Type*} (s : Finset ι) {F : ι → PowerSeries ℚ} {A Λ : ι → ℝ}
    (h : ∀ i ∈ s, SerBound (F i) (A i) (Λ i)) (hA : ∀ i ∈ s, 0 ≤ A i) (hΛ : ∀ i ∈ s, 0 ≤ Λ i) :
    SerBound (∏ i ∈ s, F i) (∏ i ∈ s, A i) (∑ i ∈ s, Λ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SerBound.one (le_refl (0 : ℝ))
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    refine (h a (mem_insert_self _ _)).mul (ih (fun i hi => h i (mem_insert_of_mem hi))
      (fun i hi => hA i (mem_insert_of_mem hi)) (fun i hi => hΛ i (mem_insert_of_mem hi)))
      (hA a (mem_insert_self _ _)) (prod_nonneg fun i hi => hA i (mem_insert_of_mem hi))
      (hΛ a (mem_insert_self _ _)) (sum_nonneg fun i hi => hΛ i (mem_insert_of_mem hi))

theorem SerBound.pow {F : PowerSeries ℚ} {A Λ : ℝ} (h : SerBound F A Λ) (hA : 0 ≤ A)
    (hΛ : 0 ≤ Λ) (m : ℕ) : SerBound (F ^ m) (A ^ m) (m * Λ) := by
  have := SerBound.prod (range m) (F := fun _ => F) (A := fun _ => A) (Λ := fun _ => Λ)
    (fun _ _ => h) (fun _ _ => hA) (fun _ _ => hΛ)
  simpa using this

/-- A linear factor `d + e u` (`d ≠ 0`). -/
theorem SerBound.lin {d e : ℚ} (hd : d ≠ 0) :
    SerBound (PowerSeries.C d + PowerSeries.C e * PowerSeries.X) |(d : ℝ)| (|(e : ℝ)| / |(d : ℝ)|) := by
  have hd' : (0 : ℝ) < |(d : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  intro b
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases b with _ | _ | b
  · simp
  · simp only [one_ne_zero, if_false, if_true, zero_add, mul_one, pow_one]
    rw [mul_div_cancel₀ _ hd'.ne']
  · simp only [Nat.add_one_ne_zero, if_false, add_zero, mul_zero, Rat.cast_zero, abs_zero,
      show b + 1 + 1 ≠ 1 by omega]
    positivity

/-- The inverse `(d + u)^{−1}` (`d ≠ 0`). -/
theorem SerBound.inv_lin {d : ℚ} (hd : d ≠ 0) :
    SerBound (PowerSeries.C d + PowerSeries.X)⁻¹ |(d : ℝ)|⁻¹ |(d : ℝ)|⁻¹ := by
  have hinv : (PowerSeries.C d + PowerSeries.X)⁻¹ =
      PowerSeries.mk fun b => (-1) ^ b * d⁻¹ ^ (b + 1) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hd])]
    ext b
    rw [mul_comm, add_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    rcases b with _ | b
    · simp [hd]
    · rw [PowerSeries.coeff_succ_X_mul]
      simp only [PowerSeries.coeff_mk]
      simp [pow_succ]; field_simp; ring
  intro b
  rw [hinv, PowerSeries.coeff_mk]
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_inv, pow_succ]
  ring_nf; exact le_rfl

/-! ### The Taylor coefficients `H_k[b]` -/

/-- `Λ_n = 6 + 24 n`. -/
def LamA (n : ℕ) : ℝ := 6 + 24 * n

theorem one_le_LamA (n : ℕ) : 1 ≤ LamA n := by
  unfold LamA
  have : (0 : ℝ) ≤ n := by positivity
  linarith

theorem half_int_ne_zero (j : ℕ) (k : ℤ) : ((j : ℚ) + 1 / 2 - k) ≠ 0 := by
  intro h
  have : ((2 * (j : ℤ) + 1 - 2 * k : ℤ) : ℚ) = 0 := by push_cast; linarith
  have : (2 * (j : ℤ) + 1 - 2 * k : ℤ) = 0 := by exact_mod_cast this
  omega

theorem abs_half_int_ge (j : ℕ) (k : ℤ) : (1 / 2 : ℝ) ≤ |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)| := by
  have e : (Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ) = ((2 * (j : ℤ) + 1 - 2 * k : ℤ) : ℝ) / 2 := by
    push_cast; ring
  rw [e, abs_div, abs_two]
  have h : (1 : ℝ) ≤ |((2 * (j : ℤ) + 1 - 2 * k : ℤ) : ℝ)| := by
    have hne : (2 * (j : ℤ) + 1 - 2 * k : ℤ) ≠ 0 := by omega
    have := Int.one_le_abs hne
    exact_mod_cast this
  linarith

theorem lin_ne_zero {n : ℕ} (hn : n % 2 = 1) (k : ℤ) : ((n : ℚ) - 2 * k) ≠ 0 := by
  have : ((n : ℤ) - 2 * k : ℤ) ≠ 0 := by omega
  exact_mod_cast this

theorem abs_lin_ge {n : ℕ} (hn : n % 2 = 1) (k : ℤ) : (1 : ℝ) ≤ |(Rat.cast ((n : ℚ) - 2 * k) : ℝ)| := by
  have : ((n : ℤ) - 2 * k : ℤ) ≠ 0 := by omega
  have h := Int.one_le_abs this
  have e : (Rat.cast ((n : ℚ) - 2 * k) : ℝ) = (((n : ℤ) - 2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [e]; exact_mod_cast h

/-- `|H_k[b]| ≤ |h_k| Λ_n^b` for odd `n`. -/
theorem abs_Hk_le {n : ℕ} (hn : n % 2 = 1) (k : ℤ) (b : ℕ) :
    |((Fam3.Hk n k b : ℚ) : ℝ)| ≤ |((Fam3.Hk n k 0 : ℚ) : ℝ)| * LamA n ^ b := by
  -- the three kinds of factors
  have hlin := SerBound.lin (d := (n : ℚ) - 2 * k) (e := 2) (lin_ne_zero hn k)
  have hnum : ∀ j ∈ range n, SerBound (W2.numF k j) (|(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)| ^ 6)
      (6 * (1 / |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)|)) := by
    intro j _
    have h := SerBound.lin (d := (j : ℚ) + 1 / 2 - k) (e := 1) (half_int_ne_zero j k)
    rw [map_one, one_mul] at h
    have := h.pow (abs_nonneg _) (by positivity) 6
    simpa [W2.numF] using this
  have hden : ∀ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, SerBound (W2.denF k k')
      ((|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ 4) (4 * (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹) := by
    intro k' hk'
    have hne : (((k' - k : ℤ) : ℚ)) ≠ 0 := by
      have := Finset.ne_of_mem_erase hk'
      exact_mod_cast sub_ne_zero.2 this
    have := (SerBound.inv_lin hne).pow (by positivity) (by positivity) 4
    simpa [W2.denF] using this
  have hN := SerBound.prod (range n) hnum (fun _ _ => by positivity) (fun _ _ => by positivity)
  have hD := SerBound.prod _ hden (fun _ _ => by positivity) (fun _ _ => by positivity)
  have hall := (hlin.mul hN (abs_nonneg _) (prod_nonneg fun _ _ => by positivity)
    (by positivity) (sum_nonneg fun _ _ => by positivity)).mul hD
    (by positivity) (prod_nonneg fun _ _ => by positivity)
    (by positivity) (sum_nonneg fun _ _ => by positivity)
  -- the constant
  have hA : |(Rat.cast ((n : ℚ) - 2 * k) : ℝ)| * (∏ j ∈ range n, |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)| ^ 6) *
      ∏ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ^ 4 =
      |((Fam3.Hk n k 0 : ℚ) : ℝ)| := by
    rw [Fam3.Hk_zero_eq]
    push_cast
    rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod]
    congr 1
    · congr 1; refine prod_congr rfl fun j _ => by rw [abs_pow]
    · refine prod_congr rfl fun j _ => by rw [abs_pow, abs_inv]
  -- the growth rate
  have hΛ : |(Rat.cast (2 : ℚ) : ℝ)| / |(Rat.cast ((n : ℚ) - 2 * k) : ℝ)| +
      ∑ j ∈ range n, 6 * (1 / |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)|) +
      ∑ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, 4 * (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ≤
      LamA n := by
    have h1 : |(Rat.cast (2 : ℚ) : ℝ)| / |(Rat.cast ((n : ℚ) - 2 * k) : ℝ)| ≤ 2 := by
      have hL := abs_lin_ge hn k
      have h2' : |(Rat.cast (2 : ℚ) : ℝ)| = 2 := by norm_num
      rw [h2', div_le_iff₀ (by linarith)]; linarith
    have h2 : ∑ j ∈ range n, 6 * (1 / |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)|) ≤ 12 * n := by
      calc _ ≤ ∑ _j ∈ range n, (12 : ℝ) := by
            refine sum_le_sum fun j _ => ?_
            have := abs_half_int_ge j k
            have : 1 / |(Rat.cast ((j : ℚ) + 1 / 2 - k) : ℝ)| ≤ 2 := by
              rw [div_le_iff₀ (by linarith)]; linarith
            linarith
        _ = 12 * n := by simp; ring
    have h3 : ∑ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, 4 * (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹
        ≤ 12 * n + 4 := by
      calc _ ≤ ∑ _k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, (4 : ℝ) := by
            refine sum_le_sum fun k' hk' => ?_
            have hne : k' - k ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hk')
            have h1 : (1 : ℝ) ≤ |(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)| := by
              have := Int.one_le_abs hne
              push_cast; exact_mod_cast this
            have : (|(Rat.cast ((k' - k : ℤ) : ℚ) : ℝ)|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
            linarith
        _ ≤ ∑ _k' ∈ Finset.Icc (-(n : ℤ)) (2 * n), (4 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by norm_num)
        _ = 12 * n + 4 := by
            rw [sum_const, Int.card_Icc, nsmul_eq_mul]
            have : (2 * (n : ℤ) + 1 - -(n : ℤ)).toNat = 3 * n + 1 := by omega
            rw [this]; push_cast; ring
    unfold LamA; linarith
  have := (hall.mono (by positivity) (by positivity) hΛ) b
  rw [hA] at this
  exact this

/-! ### The harmonic sums and the local factors -/

theorem abs_HS_le (k : ℤ) (M : ℕ) : |((HS k M : ℚ) : ℝ)| ≤ |(k : ℝ)| * 2 ^ M := by
  have hterm : ∀ l : ℤ, |(((2 / (2 * (l : ℚ) - 1)) ^ M : ℚ) : ℝ)| ≤ 2 ^ M := by
    intro l
    have h1 : (1 : ℝ) ≤ |((2 * l - 1 : ℤ) : ℝ)| := by
      have : (2 * l - 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast Int.one_le_abs this
    push_cast
    rw [abs_pow, abs_div, abs_two]
    refine pow_le_pow_left₀ (by positivity) ?_ M
    rw [div_le_iff₀ (by push_cast at h1; linarith)]
    push_cast at h1; nlinarith
  simp only [HS, W3.Fam3.hsSum, Finset.filter_true]
  split_ifs with hk
  · push_cast
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _l ∈ Finset.Icc 1 k, (2 : ℝ) ^ M := sum_le_sum fun l _ => by
            have := hterm l; push_cast at this; exact this
      _ = |(k : ℝ)| * 2 ^ M := by
            rw [sum_const, Int.card_Icc, nsmul_eq_mul, abs_of_pos (by exact_mod_cast hk)]
            congr 1
            have : (k + 1 - 1).toNat = k.toNat := by congr 1; ring
            rw [this]
            exact_mod_cast Int.toNat_of_nonneg hk.le
  · push_cast
    rw [abs_neg]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _l ∈ Finset.Icc (k + 1) 0, (2 : ℝ) ^ M := sum_le_sum fun l _ => by
            have := hterm l; push_cast at this; exact this
      _ = |(k : ℝ)| * 2 ^ M := by
            rw [sum_const, Int.card_Icc, nsmul_eq_mul, abs_of_nonpos (by exact_mod_cast not_lt.1 hk)]
            congr 1
            have : (0 + 1 - (k + 1)).toNat = (-k).toNat := by congr 1; ring
            rw [this]
            have h := Int.toNat_of_nonneg (show 0 ≤ -k by omega)
            have : ((-k).toNat : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast h
            rw [this]; push_cast; ring

/-- `Q_n = 10^7 (2n+1) Λ_n^3`. -/
def Qn (n : ℕ) : ℝ := 10 ^ 7 * (2 * n + 1) * LamA n ^ 3

theorem abs_Hk_le3 {n : ℕ} (hn : n % 2 = 1) (k : ℤ) {b : ℕ} (hb : b ≤ 3) :
    |((Fam3.Hk n k b : ℚ) : ℝ)| ≤ |((Fam3.Hk n k 0 : ℚ) : ℝ)| * LamA n ^ 3 :=
  (abs_Hk_le hn k b).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_LamA n) hb) (abs_nonneg _))

theorem abs_alphaC_le {n : ℕ} (hn : n % 2 = 1) (k : ℤ) (a : ℕ) :
    |((Fam3.alphaC n k a : ℚ) : ℝ)| ≤ 46080 * (|((Fam3.Hk n k 0 : ℚ) : ℝ)| * LamA n ^ 3) := by
  unfold Fam3.alphaC
  split_ifs with ha
  · have h := abs_Hk_le3 hn k (b := 1 - a) (by omega)
    have e : (((-(Fam3.phi 3) * 6 * 2 ^ 7 * Fam3.Hk n k (1 - a) : ℚ)) : ℝ) =
        -46080 * ((Fam3.Hk n k (1 - a) : ℚ) : ℝ) := by
      simp only [Fam3.phi]; push_cast; ring
    rw [e, abs_mul]; norm_num; linarith
  · simp only [Rat.cast_zero, abs_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _)
      (pow_nonneg (by linarith [one_le_LamA n]) _))

theorem abs_betaC_le {n : ℕ} (hn : n % 2 = 1) {k : ℤ} (hk : |(k : ℝ)| ≤ 2 * n) (a : ℕ) :
    |((Fam3.betaC n k a : ℚ) : ℝ)| ≤
      4 * (840 * (2 * n * 256) * (|((Fam3.Hk n k 0 : ℚ) : ℝ)| * LamA n ^ 3)) := by
  unfold Fam3.betaC
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans ?_
  set H := |((Fam3.Hk n k 0 : ℚ) : ℝ)| * LamA n ^ 3
  have hH : 0 ≤ H := mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [one_le_LamA n]) _)
  have hterm : ∀ i ∈ Finset.Icc 1 (4 - a), |((Fam3.phi i : ℚ) : ℝ) * ((i : ℝ) + 3) *
      ((HS k (i + 4) : ℚ) : ℝ) * ((Fam3.Hk n k (4 - i - a) : ℚ) : ℝ)| ≤ 840 * (2 * n * 256) * H := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi4 : i ≤ 4 := by omega
    have hphi : |((Fam3.phi i : ℚ) : ℝ) * ((i : ℝ) + 3)| ≤ 840 := by
      have : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
      simp only [Fam3.phi]; push_cast
      rw [abs_of_nonneg (by positivity)]
      have h0 : (0 : ℝ) ≤ i := by positivity
      have : (i : ℝ) * (i + 1) * (i + 2) * (i + 3) ≤ 4 * 5 * 6 * 7 := by
        have h1 : (i : ℝ) * (i + 1) ≤ 4 * 5 := by nlinarith
        have h2 : (i : ℝ) * (i + 1) * (i + 2) ≤ 4 * 5 * 6 := by nlinarith
        nlinarith
      linarith
    have hHS : |((HS k (i + 4) : ℚ) : ℝ)| ≤ 2 * n * 256 := by
      refine (abs_HS_le k (i + 4)).trans ?_
      have : (2 : ℝ) ^ (i + 4) ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h0 : (0 : ℝ) ≤ 2 * n := by positivity
      calc |(k : ℝ)| * 2 ^ (i + 4) ≤ (2 * n) * 2 ^ 8 :=
            mul_le_mul hk this (by positivity) h0
        _ = 2 * n * 256 := by norm_num
    have hHk := abs_Hk_le3 hn k (b := 4 - i - a) (by omega)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hphi hHS (abs_nonneg _) (by norm_num)) hHk (abs_nonneg _)
      (by positivity)
  calc _ ≤ ∑ _i ∈ Finset.Icc 1 (4 - a), 840 * (2 * n * 256) * H := sum_le_sum hterm
    _ ≤ 4 * (840 * (2 * n * 256) * H) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : 4 - a + 1 - 1 ≤ 4 := by omega
        exact_mod_cast this

/-- **Local factor bound**: `‖c_{k,m}‖₁ ≤ Q_n |h_k|` (odd `n`, `|k| ≤ 2n`). -/
theorem l1_cPoly_le {n : ℕ} (hn : n % 2 = 1) {k : ℤ} (hk : |(k : ℝ)| ≤ 2 * n) (m : ℕ) :
    l1 (Fam3.cPoly n k m) ≤ Qn n * |((Fam3.Hk n k 0 : ℚ) : ℝ)| := by
  have hQ : 0 ≤ Qn n * |((Fam3.Hk n k 0 : ℚ) : ℝ)| := by
    unfold Qn
    have := one_le_LamA n
    have : (0 : ℝ) ≤ LamA n := by linarith
    positivity
  unfold Fam3.cPoly
  split_ifs with hm
  · refine (l1_add_le _ _).trans ?_
    rw [l1_C, l1_C_mul_X]
    have h1 := abs_alphaC_le hn k m
    have h2 := abs_betaC_le hn hk m
    set H := |((Fam3.Hk n k 0 : ℚ) : ℝ)|
    have hH : 0 ≤ H := abs_nonneg _
    have hL := one_le_LamA n
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have e : Qn n * H = 10 ^ 7 * (2 * n + 1) * (H * LamA n ^ 3) := by unfold Qn; ring
    rw [e]
    have hHL : 0 ≤ H * LamA n ^ 3 := mul_nonneg hH (pow_nonneg (by linarith) _)
    nlinarith
  · rw [l1_zero]; exact hQ

end Hankel2.ArchB
