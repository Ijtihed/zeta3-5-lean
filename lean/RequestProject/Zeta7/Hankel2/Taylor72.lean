import RequestProject.Zeta7.Hankel2.LemmaT

/-!
# Paper Lemma 7.2: Taylor valuations

Fix an odd prime `p`.  With `W̃_k(u) = u^4 W(−k+u)` (`W2.fam3H n k`), `H_k[b] = [u^b] W̃_k`
(`Hk n k b`) and

  `D_k = −v_p(h_k) = 4 ∑_{m≠k} v_p(k−m) − 6 ∑_{j<n} v_p(2k−2j−1) − v_p(n−2k)`   (eq. (Dk), `Dk`),

  `μ_k = max v_p(d)` over the nonzero roots and poles `d` of `W̃_k` (`muK`),

we prove (`norm_Hk_le`) `v_p(H_k[b]) ≥ −D_k − b μ_k`, stated as `|H_k[b]|_p ≤ p^{D_k + b μ_k}` (which
also covers `H_k[b] = 0`), and (`norm_HS_le`) `v_p(HS(k,M)) ≥ −M max_l v_p(2l−1)`.

With `L_p = ⌈log_p 4n⌉` (`Lp`): `μ_k ≤ L_p`, `λ_p(k) ≤ L_p` and `max_l v_p(2l−1) ≤ L_p` for every
node `k ∈ [−n, 2n]`, hence `v_p(HS(k,M)) ≥ −M L_p` (`norm_HS_le_Lp`).  If `p² > 6n` all these
valuations are `≤ 1` (`muK_le_one`, `lambdaP_le_one`, `hsMax_le_one`).

All the "valuation ≤ L" facts are proved uniformly under the hypothesis `4n < p^{L+1}`
(satisfied by `L = L_p`, and by `L = 1` when `p² > 6n`).
-/

open Finset

namespace Hankel2.Fam3

/-! ### Definitions -/

/-- `L_p = ⌈log_p 4n⌉`, the least `L` with `4n ≤ p^L`. -/
def Lp (p n : ℕ) : ℕ := Nat.clog p (4 * n)

/-- `D_k = −v_p(h_k) = 4 ∑_{m≠k} v_p(k−m) − 6 ∑_{j<n} v_p(2k−2j−1) − v_p(n−2k)` (paper eq. (Dk)). -/
def Dk (p n : ℕ) (k : ℤ) : ℤ :=
  4 * ∑ m ∈ (Fam3PF.nodes n).erase k, (padicValInt p (k - m) : ℤ)
    - 6 * ∑ j ∈ range n, (padicValInt p (2 * k - 2 * j - 1) : ℤ)
    - (padicValInt p ((n : ℤ) - 2 * k) : ℤ)

/-- `μ_k = max v_p(d)` over the nonzero roots and poles `d` of `W̃_k`: the poles `k − m`
(`m ≠ k`), the roots `(2k−2j−1)/2` (`j < n`) and the root `(2k − n)/2` (`v_p(2d)` for odd `p`). -/
noncomputable def muK (p n : ℕ) (k : ℤ) : ℕ :=
  max (max (lambdaP p n k) ((range n).sup fun j => padicValInt p (2 * k - 2 * j - 1)))
    (padicValInt p ((n : ℤ) - 2 * k))

/-- The range of summation `l` in `HS(k, M)`. -/
def hsRange (k : ℤ) : Finset ℤ := if 0 < k then Icc 1 k else Icc (k + 1) 0

/-- `max_l v_p(2l − 1)` over the range of `l` in `HS(k, M)`. -/
def hsMax (p : ℕ) (k : ℤ) : ℕ := (hsRange k).sup fun l => padicValInt p (2 * l - 1)

/-! ### Coefficient profiles of power series -/

section Prof

variable {p : ℕ} [hp : Fact p.Prime]

/-- `F` has profile `(D, μ)`: `|[u^b] F|_p ≤ p^{D + b μ}` for every `b`. -/
def SerProf (p : ℕ) (F : PowerSeries ℚ) (D : ℤ) (μ : ℕ) : Prop :=
  ∀ b : ℕ, padicNorm p (PowerSeries.coeff b F) ≤ (p : ℚ) ^ (D + (b : ℤ) * μ)

theorem p_pos_q : (0 : ℚ) < p := by exact_mod_cast hp.out.pos

theorem one_le_p_q : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le

theorem SerProf.mono {F : PowerSeries ℚ} {D D' : ℤ} {μ : ℕ} (h : SerProf p F D μ) (hD : D ≤ D') :
    SerProf p F D' μ := fun b =>
  (h b).trans (zpow_le_zpow_right₀ one_le_p_q (by linarith))

theorem SerProf.mul {F G : PowerSeries ℚ} {D₁ D₂ : ℤ} {μ : ℕ} (hF : SerProf p F D₁ μ)
    (hG : SerProf p G D₂ μ) : SerProf p (F * G) (D₁ + D₂) μ := by
  intro b
  rw [PowerSeries.coeff_mul]
  refine padicNorm.sum_le' (fun x hx => ?_) (by have := p_pos_q (p := p); positivity)
  rw [padicNorm.mul]
  have hx' := Finset.mem_antidiagonal.1 hx
  calc padicNorm p (PowerSeries.coeff x.1 F) * padicNorm p (PowerSeries.coeff x.2 G)
      ≤ (p : ℚ) ^ (D₁ + (x.1 : ℤ) * μ) * (p : ℚ) ^ (D₂ + (x.2 : ℤ) * μ) :=
        mul_le_mul (hF _) (hG _) (padicNorm.nonneg _) (by have := p_pos_q (p := p); positivity)
    _ = (p : ℚ) ^ (D₁ + D₂ + (b : ℤ) * μ) := by
        rw [← zpow_add₀ p_pos_q.ne']
        congr 1
        rw [← hx']; push_cast; ring

theorem SerProf.one (μ : ℕ) : SerProf p (1 : PowerSeries ℚ) 0 μ := by
  intro b
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp; have := p_pos_q (p := p); positivity

theorem SerProf.prod {ι : Type*} (s : Finset ι) {F : ι → PowerSeries ℚ} {D : ι → ℤ} {μ : ℕ}
    (h : ∀ i ∈ s, SerProf p (F i) (D i) μ) : SerProf p (∏ i ∈ s, F i) (∑ i ∈ s, D i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SerProf.one μ
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem SerProf.pow {F : PowerSeries ℚ} {D : ℤ} {μ : ℕ} (h : SerProf p F D μ) (m : ℕ) :
    SerProf p (F ^ m) (m * D) μ := by
  have := SerProf.prod (range m) (F := fun _ => F) (D := fun _ => D) (μ := μ) (fun _ _ => h)
  simpa [mul_comm] using this

/-- A linear factor `d + e u` with `|d|_p ≤ p^{−v}`, `|e|_p ≤ 1`, `v ≤ μ` has profile `(−v, μ)`. -/
theorem SerProf.lin {d e : ℚ} {v μ : ℕ} (hd : padicNorm p d ≤ (p : ℚ) ^ (-(v : ℤ)))
    (he : padicNorm p e ≤ 1) (hv : v ≤ μ) :
    SerProf p (PowerSeries.C d + PowerSeries.C e * PowerSeries.X) (-(v : ℤ)) μ := by
  intro b
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases b with _ | _ | b
  · simpa using hd
  · simp only [one_ne_zero, if_false, if_true, zero_add, mul_one]
    refine he.trans (one_le_zpow₀ one_le_p_q ?_)
    push_cast; omega
  · simp; have := p_pos_q (p := p); positivity

omit hp in
theorem padicNorm_eq_zpow_int {x : ℤ} (hx : x ≠ 0) :
    padicNorm p (x : ℚ) = (p : ℚ) ^ (-(padicValInt p x : ℤ)) := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hx), padicValRat.of_int]

omit hp in
theorem padicNorm_le_zpow_int (x : ℤ) :
    padicNorm p (x : ℚ) ≤ (p : ℚ) ^ (-(padicValInt p x : ℤ)) := by
  by_cases hx : x = 0
  · subst hx; simp
  · exact (padicNorm_eq_zpow_int hx).le

/-- The inverse `(d + u)^{−1}` of a factor with `|d|_p = p^{−v}`, `v ≤ μ`, has profile `(v, μ)`. -/
theorem SerProf.inv_lin {d : ℚ} (hd0 : d ≠ 0) {v μ : ℕ}
    (hd : padicNorm p d = (p : ℚ) ^ (-(v : ℤ))) (hv : v ≤ μ) :
    SerProf p (PowerSeries.C d + PowerSeries.X)⁻¹ v μ := by
  have hinv : (PowerSeries.C d + PowerSeries.X)⁻¹ =
      PowerSeries.mk fun b => (-1) ^ b * d⁻¹ ^ (b + 1) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hd0])]
    ext b
    rw [mul_comm, add_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    rcases b with _ | b
    · simp [hd0]
    · rw [PowerSeries.coeff_succ_X_mul]
      simp only [PowerSeries.coeff_mk]
      simp [pow_succ]; field_simp; ring
  intro b
  rw [hinv, PowerSeries.coeff_mk, padicNorm.mul, W2.padicNorm_pow', W2.padicNorm_pow',
    padicNorm.neg, padicNorm.one, one_pow, one_mul, W2.padicNorm_inv, hd, ← zpow_neg, neg_neg,
    ← zpow_natCast, ← zpow_mul]
  refine zpow_le_zpow_right₀ one_le_p_q ?_
  push_cast
  nlinarith

end Prof

/-! ### Lemma 7.2, first part: `v_p(H_k[b]) ≥ −D_k − b μ_k` -/

section Hk

variable {p : ℕ} [hp : Fact p.Prime]

theorem prof_linF (hp2 : p ≠ 2) (n : ℕ) (k : ℤ) {μ : ℕ}
    (hμ : padicValInt p ((n : ℤ) - 2 * k) ≤ μ) :
    SerProf p (W2.linF n k) (-(padicValInt p ((n : ℤ) - 2 * k) : ℤ)) μ := by
  unfold W2.linF
  refine SerProf.lin ?_ (by rw [W2.padicNorm_two_eq_one hp2]) hμ
  have := padicNorm_le_zpow_int (p := p) ((n : ℤ) - 2 * k)
  push_cast at this; exact this

theorem prof_numF (hp2 : p ≠ 2) (k : ℤ) (j : ℕ) {μ : ℕ}
    (hμ : padicValInt p (2 * k - 2 * j - 1) ≤ μ) :
    SerProf p (W2.numF k j) (6 * -(padicValInt p (2 * k - 2 * j - 1) : ℤ)) μ := by
  unfold W2.numF
  have e : ((j : ℚ) + 1 / 2 - k) = -(((2 * k - 2 * j - 1 : ℤ) : ℚ) / 2) := by push_cast; ring
  have h := SerProf.lin (p := p) (d := (j : ℚ) + 1 / 2 - k) (e := 1)
    (v := padicValInt p (2 * k - 2 * j - 1)) ?_ (by simp) hμ
  · rw [map_one, one_mul] at h
    have := h.pow 6
    exact_mod_cast this
  · rw [e, padicNorm.neg, padicNorm.div, W2.padicNorm_two_eq_one hp2, div_one]
    exact padicNorm_le_zpow_int _

theorem prof_denF {k k' : ℤ} (hne : k' ≠ k) {μ : ℕ} (hμ : padicValInt p (k - k') ≤ μ) :
    SerProf p (W2.denF k k') (4 * (padicValInt p (k - k') : ℤ)) μ := by
  unfold W2.denF
  have h0 : (((k' - k : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h := SerProf.inv_lin (p := p) h0 (v := padicValInt p (k - k')) ?_ hμ
  · have := h.pow 4
    exact_mod_cast this
  · rw [padicNorm_eq_zpow_int (sub_ne_zero.2 hne), padicValInt_sub_comm p]

omit hp in
theorem le_muK_lambda {n : ℕ} {k m : ℤ} (hm : m ∈ (Fam3PF.nodes n).erase k) :
    padicValInt p (k - m) ≤ muK p n k :=
  le_trans (Finset.le_sup (f := fun m => padicValInt p (k - m)) hm)
    (le_trans (le_max_left _ _) (le_max_left _ _))

omit hp in
theorem le_muK_root {n : ℕ} {k : ℤ} {j : ℕ} (hj : j ∈ range n) :
    padicValInt p (2 * k - 2 * j - 1) ≤ muK p n k :=
  le_trans (Finset.le_sup (f := fun j : ℕ => padicValInt p (2 * k - 2 * j - 1)) hj)
    (le_trans (le_max_right _ _) (le_max_left _ _))

omit hp in
theorem le_muK_lin (n : ℕ) (k : ℤ) : padicValInt p ((n : ℤ) - 2 * k) ≤ muK p n k :=
  le_max_right _ _

/-- The profile of `W̃_k`: `|[u^b] W̃_k|_p ≤ p^{D_k + b μ_k}`. -/
theorem serProf_fam3H (hp2 : p ≠ 2) (n : ℕ) (k : ℤ) :
    SerProf p (W2.fam3H n k) (Dk p n k) (muK p n k) := by
  have hlin := prof_linF hp2 n k (le_muK_lin (p := p) n k)
  have hnum := SerProf.prod (p := p) (range n) (F := fun j => W2.numF k j)
    (fun j hj => prof_numF hp2 k j (le_muK_root (n := n) hj))
  have hden := SerProf.prod (p := p) ((Finset.Icc (-(n : ℤ)) (2 * n)).erase k)
    (F := fun k' => W2.denF k k')
    (fun k' hk' => prof_denF (Finset.ne_of_mem_erase hk') (le_muK_lambda (n := n) hk'))
  have := (hlin.mul hnum).mul hden
  rw [W2.fam3H_eq]
  refine this.mono (le_of_eq ?_)
  simp only [Dk, Fam3PF.nodes, Finset.mul_sum]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- **Lemma 7.2 (first part).** `v_p(H_k[b]) ≥ −D_k − b μ_k`, in the form
`|H_k[b]|_p ≤ p^{D_k + b μ_k}` (odd `p`). -/
theorem norm_Hk_le (hp2 : p ≠ 2) (n : ℕ) (k : ℤ) (b : ℕ) :
    padicNorm p (Hk n k b) ≤ (p : ℚ) ^ (Dk p n k + (b : ℤ) * muK p n k) :=
  serProf_fam3H hp2 n k b

end Hk

/-! ### Lemma 7.2, second part: the harmonic sums -/

section HSsec

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicNorm_HS_term (hp2 : p ≠ 2) (l : ℤ) (M : ℕ) :
    padicNorm p ((2 / (2 * (l : ℚ) - 1)) ^ M) = (p : ℚ) ^ ((M : ℤ) * padicValInt p (2 * l - 1)) := by
  have h0 : (2 * l - 1 : ℤ) ≠ 0 := by omega
  rw [W2.padicNorm_pow', padicNorm.div, W2.padicNorm_two_eq_one hp2]
  have : (2 * (l : ℚ) - 1) = ((2 * l - 1 : ℤ) : ℚ) := by push_cast; ring
  rw [this, padicNorm_eq_zpow_int h0, one_div, ← zpow_neg, neg_neg, ← zpow_natCast, ← zpow_mul,
    mul_comm]

/-- **Lemma 7.2 (second part).** `v_p(HS(k,M)) ≥ −M · max_l v_p(2l−1)`, the maximum over the range
of `l` in the sum (odd `p`). -/
theorem norm_HS_le (hp2 : p ≠ 2) (k : ℤ) (M : ℕ) :
    padicNorm p (HS k M) ≤ (p : ℚ) ^ ((M : ℤ) * hsMax p k) := by
  have key : ∀ l ∈ hsRange k,
      padicNorm p ((2 / (2 * (l : ℚ) - 1)) ^ M) ≤ (p : ℚ) ^ ((M : ℤ) * hsMax p k) := by
    intro l hl
    rw [padicNorm_HS_term hp2]
    refine zpow_le_zpow_right₀ one_le_p_q ?_
    have h1 : padicValInt p (2 * l - 1) ≤ hsMax p k :=
      Finset.le_sup (f := fun l => padicValInt p (2 * l - 1)) hl
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (by positivity)
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ ((M : ℤ) * hsMax p k) := by
    have := p_pos_q (p := p); positivity
  simp only [HS, W3.Fam3.hsSum, Finset.filter_true]
  unfold hsRange at key
  split_ifs with hk
  · rw [if_pos hk] at key; exact padicNorm.sum_le' key hpos
  · rw [if_neg hk] at key; rw [padicNorm.neg]; exact padicNorm.sum_le' key hpos

end HSsec

/-! ### All the relevant valuations are `≤ L` when `4n < p^{L+1}` -/

section Bounds

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_le_of_natAbs_lt {x : ℤ} (hx : x ≠ 0) {L : ℕ} (h : x.natAbs < p ^ (L + 1)) :
    padicValInt p x ≤ L := by
  have hd : p ^ padicValInt p x ∣ x.natAbs := pow_padicValNat_dvd
  have h1 : p ^ padicValInt p x ≤ x.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hx) hd
  have h2 : p ^ padicValInt p x < p ^ (L + 1) := lt_of_le_of_lt h1 h
  have := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 h2
  omega

/-- A nonzero integer with `|x| ≤ 4n` has `v_p(x) ≤ L` when `4n < p^{L+1}`. -/
theorem padicValInt_le_of_abs_le {n L : ℕ} (hL : 4 * n < p ^ (L + 1)) {x : ℤ}
    (h1 : -(4 * n : ℤ) ≤ x) (h2 : x ≤ 4 * n) : padicValInt p x ≤ L := by
  by_cases hx : x = 0
  · subst hx; simp
  refine padicValInt_le_of_natAbs_lt hx (lt_of_le_of_lt ?_ hL)
  rcases Int.natAbs_eq x with h | h <;> omega

theorem mem_nodes_iff {n : ℕ} {k : ℤ} : k ∈ Fam3PF.nodes n ↔ -(n : ℤ) ≤ k ∧ k ≤ 2 * n := by
  simp [Fam3PF.nodes]

theorem lambdaP_le {n L : ℕ} (hL : 4 * n < p ^ (L + 1)) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    lambdaP p n k ≤ L := by
  refine Finset.sup_le fun m hm => ?_
  have hm' := mem_nodes_iff.1 (Finset.mem_of_mem_erase hm)
  have hk' := mem_nodes_iff.1 hk
  exact padicValInt_le_of_abs_le hL (by omega) (by omega)

theorem muK_le {n L : ℕ} (hL : 4 * n < p ^ (L + 1)) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    muK p n k ≤ L := by
  have hk' := mem_nodes_iff.1 hk
  refine max_le (max_le (lambdaP_le hL hk) (Finset.sup_le fun j hj => ?_)) ?_
  · have := Finset.mem_range.1 hj
    exact padicValInt_le_of_abs_le hL (by omega) (by omega)
  · exact padicValInt_le_of_abs_le hL (by omega) (by omega)

theorem hsMax_le {n L : ℕ} (hL : 4 * n < p ^ (L + 1)) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    hsMax p k ≤ L := by
  have hk' := mem_nodes_iff.1 hk
  refine Finset.sup_le fun l hl => ?_
  unfold hsRange at hl
  split_ifs at hl with h
  · have := Finset.mem_Icc.1 hl
    exact padicValInt_le_of_abs_le hL (by omega) (by omega)
  · have := Finset.mem_Icc.1 hl
    exact padicValInt_le_of_abs_le hL (by omega) (by omega)

/-- `L = L_p = ⌈log_p 4n⌉` satisfies `4n < p^{L+1}`. -/
theorem four_n_lt_pow_Lp (n : ℕ) : 4 * n < p ^ (Lp p n + 1) :=
  lt_of_le_of_lt (Nat.le_pow_clog hp.out.one_lt _)
    (Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self _))

omit hp in
/-- `L = 1` satisfies `4n < p^{L+1}` when `p² > 6n`. -/
theorem four_n_lt_pow_one {n : ℕ} (h : 6 * n < p ^ 2) : 4 * n < p ^ (1 + 1) := by
  norm_num; omega

/-- `μ_k ≤ L_p` (paper Lemma 7.2). -/
theorem muK_le_Lp {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) : muK p n k ≤ Lp p n :=
  muK_le (four_n_lt_pow_Lp n) hk

/-- `λ_p(k) ≤ L_p`. -/
theorem lambdaP_le_Lp {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) : lambdaP p n k ≤ Lp p n :=
  lambdaP_le (four_n_lt_pow_Lp n) hk

/-- `max_l v_p(2l−1) ≤ L_p` over the range of `HS(k, ·)`. -/
theorem hsMax_le_Lp {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) : hsMax p k ≤ Lp p n :=
  hsMax_le (four_n_lt_pow_Lp n) hk

/-- **Lemma 7.2** with `μ_k ≤ L_p`: `v_p(H_k[b]) ≥ −D_k − b L_p`. -/
theorem norm_Hk_le_Lp (hp2 : p ≠ 2) {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) (b : ℕ) :
    padicNorm p (Hk n k b) ≤ (p : ℚ) ^ (Dk p n k + (b : ℤ) * Lp p n) :=
  (norm_Hk_le hp2 n k b).trans (zpow_le_zpow_right₀ one_le_p_q (by
    have := muK_le_Lp (p := p) hk
    have : (b : ℤ) * muK p n k ≤ b * Lp p n :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
    linarith))

/-- **Lemma 7.2** (second part with `L_p`): `v_p(HS(k,M)) ≥ −M L_p` for every node `k`. -/
theorem norm_HS_le_Lp (hp2 : p ≠ 2) {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) (M : ℕ) :
    padicNorm p (HS k M) ≤ (p : ℚ) ^ ((M : ℤ) * Lp p n) :=
  (norm_HS_le hp2 k M).trans (zpow_le_zpow_right₀ one_le_p_q
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hsMax_le_Lp (p := p) hk) (by positivity)))

/-- For `p² > 6n` all the valuations of Lemma 7.2 are `≤ 1`. -/
theorem muK_le_one {n : ℕ} (h : 6 * n < p ^ 2) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    muK p n k ≤ 1 := muK_le (four_n_lt_pow_one h) hk

theorem lambdaP_le_one {n : ℕ} (h : 6 * n < p ^ 2) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    lambdaP p n k ≤ 1 := lambdaP_le (four_n_lt_pow_one h) hk

theorem hsMax_le_one {n : ℕ} (h : 6 * n < p ^ 2) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    hsMax p k ≤ 1 := hsMax_le (four_n_lt_pow_one h) hk

end Bounds

/-! ### `D_k = −v_p(h_k)` (paper eq. (Dk)) -/

section DkEq

variable {p : ℕ} [hp : Fact p.Prime]

theorem Hk_zero_eq (n : ℕ) (k : ℤ) : Hk n k 0 = ((n : ℚ) - 2 * k) *
    (∏ j ∈ range n, ((j : ℚ) + 1 / 2 - k) ^ 6) *
      ∏ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, ((((k' - k : ℤ) : ℚ))⁻¹) ^ 4 := by
  simp [Hk, W2.fam3H, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod,
    PowerSeries.constantCoeff_inv]

theorem padicValRat_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (h a (mem_insert_self _ _))
      (prod_ne_zero_iff.2 fun i hi => h i (mem_insert_of_mem hi)),
      ih fun i hi => h i (mem_insert_of_mem hi)]

/-- **`D_k = −v_p(h_k)`** with `h_k = H_k[0]` (paper eq. (Dk)), for odd `n` and odd `p`. -/
theorem padicValRat_Hk_zero (hp2 : p ≠ 2) {n : ℕ} (hn : n % 2 = 1) (k : ℤ) :
    padicValRat p (Hk n k 0) = -Dk p n k := by
  have h1 : ((n : ℚ) - 2 * k) ≠ 0 := by
    have : ((n : ℤ) - 2 * k : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hj : ∀ j ∈ range n, ((j : ℚ) + 1 / 2 - k) ^ 6 ≠ 0 := by
    intro j _
    have : (2 * (j : ℤ) + 1 - 2 * k : ℤ) ≠ 0 := by omega
    have : ((j : ℚ) + 1 / 2 - k) = ((2 * (j : ℤ) + 1 - 2 * k : ℤ) : ℚ) / 2 := by push_cast; ring
    rw [this]; exact pow_ne_zero _ (div_ne_zero (by exact_mod_cast ‹(2 * (j : ℤ) + 1 - 2 * k : ℤ) ≠ 0›)
      two_ne_zero)
  have hk' : ∀ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k, ((((k' - k : ℤ) : ℚ))⁻¹) ^ 4 ≠ 0 := by
    intro k' hk'
    have : (k' - k : ℤ) ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hk')
    exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast this))
  rw [Hk_zero_eq, padicValRat.mul (mul_ne_zero h1 (prod_ne_zero_iff.2 hj)) (prod_ne_zero_iff.2 hk'),
    padicValRat.mul h1 (prod_ne_zero_iff.2 hj), padicValRat_prod _ _ hj, padicValRat_prod _ _ hk']
  have e1 : padicValRat p ((n : ℚ) - 2 * k) = padicValInt p ((n : ℤ) - 2 * k) := by
    rw [← padicValRat.of_int]; push_cast; rfl
  have e2 : ∀ j ∈ range n, padicValRat p (((j : ℚ) + 1 / 2 - k) ^ 6) =
      6 * (padicValInt p (2 * k - 2 * j - 1) : ℤ) := by
    intro j _
    have h0 : (2 * k - 2 * (j : ℤ) - 1 : ℤ) ≠ 0 := by omega
    have : ((j : ℚ) + 1 / 2 - k) = -(((2 * k - 2 * (j : ℤ) - 1 : ℤ) : ℚ) / 2) := by push_cast; ring
    rw [padicValRat.pow (by rw [this]; exact neg_ne_zero.2 (div_ne_zero (by exact_mod_cast h0)
      two_ne_zero)), this, padicValRat.neg, padicValRat.div (by exact_mod_cast h0) two_ne_zero,
      padicValRat.of_int]
    have : padicValRat p 2 = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
      simp [padicValNat.eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out
        Nat.prime_two).1 h))]
    rw [this]; push_cast; ring
  have e3 : ∀ k' ∈ (Finset.Icc (-(n : ℤ)) (2 * n)).erase k,
      padicValRat p (((((k' - k : ℤ) : ℚ))⁻¹) ^ 4) = -(4 * (padicValInt p (k - k') : ℤ)) := by
    intro k' hk'
    have h0 : (k' - k : ℤ) ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hk')
    rw [padicValRat.pow (inv_ne_zero (by exact_mod_cast h0)), padicValRat.inv, padicValRat.of_int,
      padicValInt_sub_comm p]
    ring
  rw [e1, sum_congr rfl e2, sum_congr rfl e3]
  simp only [Dk, Fam3PF.nodes, sum_neg_distrib, ← mul_sum]
  ring

end DkEq

end Hankel2.Fam3
