import RequestProject.Zeta7.Hankel2.Leaf82

/-!
# Paper Lemma 8.3 (A1): the small-prime bound

For every odd prime `p`, every `n` and every `K ≤ 6n+4`,

  `T_p ≤ K(6n+4−K)/(p−1) + 12 K L_p + 113 n`                        (`lemmaA1`).

(The paper works with `K = κ n`, `κ ∈ [2.8, 3]`, so `K ≤ 6n+4` holds throughout; the hypothesis
is only used to know that `K(6n+4−K) ≥ 0`, so that the partial geometric sum over the levels
`p^j ≤ 3n` can be bounded by the full one.)

Proof (paper §8.2).  By the leaf lemma, `T_p ≤ 12 K L_p + max_s [∑_k s_k D_k − penalty(s)]`.
Both `D_k` (after dropping `−v_p(n−2k) ≤ 0`) and the penalty decompose over the levels
`q = p^j` (`D_le_sum_levels`, `penalty_eq_sum_levels`).  For a fixed profile `s`, level `q`
contributes (`levelTerm`)

  `∑_c [S_c (4(N_c − 1) − 6 z_c) − S_c² + ∑_{k∈c} s_k²]`,

where `c` runs over the residue classes mod `q`, `N_c` is the number of nodes in `c` and
`z_c = #{j < n : q ∣ 2c − 2j − 1}`.

* `q > 3n` (`levelTerm_le_zero_of_gt`): every class has at most one node, and the term is `≤ 0`.
* any odd `q` (`levelTerm_le`): with `B_c = 4 N_c − 6 z_c` and `∑ s_k² ≤ 4 S_c`, the term is
  `≤ ∑_c (S_c B_c − S_c²)`; since `∑_c N_c = 3n+1` and `∑_c z_c = n`, the mean of `B_c` over the
  `q` classes is exactly `(6n+4)/q`, and `|B_c − (6n+4)/q| ≤ 10` because
  `|N_c − (3n+1)/q| < 1` and `|z_c − n/q| < 1`.  Weak duality at `λ = mean − 2K/q`
  (`weak_duality_bound`) gives `≤ K(6n+4−K)/q + 25 q`.

Summing, `∑_{j ≥ 1} K(6n+4−K)/p^j ≤ K(6n+4−K)/(p−1)` and
`∑_{p^j ≤ 3n} 25 p^j ≤ 25 · 3n · p/(p−1) ≤ 113 n`.
-/

open Finset

namespace Hankel2.Fam3

/-! ### Weak duality -/

/-- **Per-level weak duality.**  If `∑ S_c = K`, `∑ B_c = q B̄` over `q` classes and
`|B_c − B̄| ≤ 10`, then `∑_c (S_c B_c − S_c²) ≤ K B̄ − K²/q + 25 q`. -/
theorem weak_duality_bound {ι : Type*} (T : Finset ι) (S B : ι → ℝ) (K Bbar : ℝ)
    (hq : (0 : ℝ) < T.card) (hS : ∑ c ∈ T, S c = K) (hB : ∑ c ∈ T, B c = T.card * Bbar)
    (hdev : ∀ c ∈ T, |B c - Bbar| ≤ 10) :
    ∑ c ∈ T, (S c * B c - S c ^ 2) ≤ K * Bbar - K ^ 2 / T.card + 25 * T.card := by
  set q : ℝ := (T.card : ℝ)
  set lam : ℝ := Bbar - 2 * K / q
  have h1 : ∀ c ∈ T, S c * B c - S c ^ 2 ≤ lam * S c + (B c - lam) ^ 2 / 4 := by
    intro c _; nlinarith [sq_nonneg (S c - (B c - lam) / 2)]
  have h2 := Finset.sum_le_sum h1
  have h3 : ∑ c ∈ T, (B c - lam) ^ 2 =
      ∑ c ∈ T, (B c - Bbar) ^ 2 + 4 * K / q * ∑ c ∈ T, (B c - Bbar) + q * (2 * K / q) ^ 2 := by
    rw [mul_sum]
    have : ∀ c ∈ T, (B c - lam) ^ 2 = (B c - Bbar) ^ 2 + 4 * K / q * (B c - Bbar) + (2 * K / q) ^ 2 := by
      intro c _; simp only [lam]; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
  have h4 : ∑ c ∈ T, (B c - Bbar) = 0 := by
    rw [sum_sub_distrib, hB, sum_const, nsmul_eq_mul]; ring
  have h5 : ∑ c ∈ T, (B c - Bbar) ^ 2 ≤ 100 * q := by
    calc ∑ c ∈ T, (B c - Bbar) ^ 2 ≤ ∑ c ∈ T, (100 : ℝ) := by
          refine sum_le_sum fun c hc => ?_
          have := hdev c hc
          have := abs_le.1 this
          nlinarith
      _ = 100 * q := by rw [sum_const, nsmul_eq_mul]; ring
  rw [sum_add_distrib, ← mul_sum, hS, ← sum_div] at h2
  rw [h3, h4] at h2
  have hq0 : q ≠ 0 := hq.ne'
  have e : lam * K + (∑ c ∈ T, (B c - Bbar) ^ 2 + 4 * K / q * 0 + q * (2 * K / q) ^ 2) / 4 =
      K * Bbar - K ^ 2 / q + (∑ c ∈ T, (B c - Bbar) ^ 2) / 4 := by
    simp only [lam]; field_simp; ring
  rw [e] at h2
  linarith

/-! ### Counting residues in an interval -/

/-- The number of `x ∈ [a, b)` with `x ≡ v (mod q)` is within `1` of `(b − a)/q`. -/
theorem count_modEq_bounds (a b v q : ℤ) (hq : 0 < q) (hab : a ≤ b) :
    ((b - a : ℝ) / q - 1 < (#{x ∈ Ico a b | x ≡ v [ZMOD q]} : ℝ)) ∧
      ((#{x ∈ Ico a b | x ≡ v [ZMOD q]} : ℝ) < (b - a : ℝ) / q + 1) := by
  have hc := Int.Ico_filter_modEq_card a b hq v
  set X : ℚ := (b - v) / (q : ℚ)
  set Y : ℚ := (a - v) / (q : ℚ)
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hXY : Y ≤ X := by
    simp only [X, Y]; gcongr
  have hmono : ⌈Y⌉ ≤ ⌈X⌉ := Int.ceil_le_ceil hXY
  rw [max_eq_left (by omega)] at hc
  have e1 : ((#{x ∈ Ico a b | x ≡ v [ZMOD q]} : ℤ) : ℝ) = ((⌈X⌉ - ⌈Y⌉ : ℤ) : ℝ) := by rw [hc]
  push_cast at e1
  rw [e1]
  have hX1 := Int.le_ceil X
  have hX2 := Int.ceil_lt_add_one X
  have hY1 := Int.le_ceil Y
  have hY2 := Int.ceil_lt_add_one Y
  have hXYd : X - Y = ((b - a : ℤ) : ℚ) / q := by simp only [X, Y]; push_cast; field_simp; ring
  have r1 : ((X : ℚ) : ℝ) - ((Y : ℚ) : ℝ) = (b - a : ℝ) / q := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hXYd
    push_cast at this; linarith
  have c1 : ((X : ℚ) : ℝ) ≤ ((⌈X⌉ : ℤ) : ℝ) := by exact_mod_cast hX1
  have c2 : ((⌈X⌉ : ℤ) : ℝ) < ((X : ℚ) : ℝ) + 1 := by exact_mod_cast hX2
  have c3 : ((Y : ℚ) : ℝ) ≤ ((⌈Y⌉ : ℤ) : ℝ) := by exact_mod_cast hY1
  have c4 : ((⌈Y⌉ : ℤ) : ℝ) < ((Y : ℚ) : ℝ) + 1 := by exact_mod_cast hY2
  constructor <;> linarith

/-! ### Level data -/

section LevelDefs

variable (n q : ℕ)

/-- `N_c`: the number of nodes `m ∈ [−n, 2n]` in the residue class `c` mod `q`. -/
def clsN (c : ℕ) : ℕ := #{m ∈ Fam3PF.nodes n | m % (q : ℤ) = c}

/-- The number of other nodes `m ≠ k` with `q ∣ k − m`. -/
def cntL (k : ℤ) : ℕ := #{m ∈ (Fam3PF.nodes n).erase k | (q : ℤ) ∣ k - m}

/-- `z(x) = #{j < n : q ∣ 2x − 2j − 1}` (the zeros of level `q` in the class of `x`). -/
def zL (x : ℤ) : ℕ := ((range n).filter (fun j : ℕ => (q : ℤ) ∣ 2 * x - 2 * (j : ℤ) - 1)).card

/-- `S_c = ∑_{k ≡ c (q)} s_k`. -/
def Scls (s : Fin (3 * n + 1) → ℕ) (c : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => nodeOf n i % (q : ℤ) = c), s i

/-- `∑_{k ≡ c (q)} s_k²`. -/
def sqCls (s : Fin (3 * n + 1) → ℕ) (c : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => nodeOf n i % (q : ℤ) = c), s i ^ 2

/-- The level-`q` part of the penalty, `∑_{c mod q} (S_c² − ∑_{k∈c} s_k²)`. -/
def penL (s : Fin (3 * n + 1) → ℕ) : ℤ :=
  ∑ c ∈ range q, ((Scls n q s c : ℤ) ^ 2 - (sqCls n q s c : ℤ))

/-- The level-`q` term `∑_k s_k (4 #{m ≠ k : q ∣ k−m} − 6 z(k)) − penalty_q(s)`. -/
def levelTerm (s : Fin (3 * n + 1) → ℕ) : ℤ :=
  ∑ i, (s i : ℤ) * (4 * (cntL n q (nodeOf n i) : ℤ) - 6 * (zL n q (nodeOf n i) : ℤ)) - penL n q s

end LevelDefs

theorem penalty_eq_sum_penL (p n : ℕ) (s : Fin (3 * n + 1) → ℕ) :
    penalty p n s = ∑ j ∈ Icc 1 (3 * n + 1), penL n (p ^ j) s := rfl

theorem nodeOf_mem (n : ℕ) (i : Fin (3 * n + 1)) : nodeOf n i ∈ Fam3PF.nodes n := by
  rw [mem_nodes_iff]; unfold nodeOf; have := i.isLt; omega

theorem toNat_emod_eq_iff {q : ℤ} (hq : 0 < q) (x : ℤ) (c : ℕ) :
    (x % q).toNat = c ↔ x % q = c := by
  have := Int.emod_nonneg x hq.ne'
  omega

theorem toNat_emod_mem_range {q : ℕ} (hq : 0 < q) (x : ℤ) : (x % (q : ℤ)).toNat ∈ range q := by
  rw [mem_range]
  have h1 := Int.emod_nonneg x (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by exact_mod_cast hq : (0 : ℤ) < q)
  omega

section LevelLemmas

variable {n q : ℕ}

/-- Regrouping a sum over nodes by residue classes. -/
theorem sum_regroup (hq : 0 < q) (s : Fin (3 * n + 1) → ℕ) (F : ℕ → ℝ) :
    ∑ i, (s i : ℝ) * F ((nodeOf n i % (q : ℤ)).toNat) = ∑ c ∈ range q, (Scls n q s c : ℝ) * F c := by
  rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (q : ℤ)).toNat) (t := range q)
    (fun i _ => toNat_emod_mem_range hq _)]
  refine sum_congr rfl fun c _ => ?_
  rw [Scls, Nat.cast_sum, sum_mul]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  refine sum_congr (filter_congr fun i _ => toNat_emod_eq_iff hq' _ _) fun i hi => ?_
  rw [(mem_filter.1 hi).2, Int.toNat_natCast]

theorem sum_Scls (hq : 0 < q) (s : Fin (3 * n + 1) → ℕ) :
    ∑ c ∈ range q, (Scls n q s c : ℝ) = ∑ i, (s i : ℝ) := by
  have := sum_regroup hq s (fun _ => 1)
  simpa using this.symm

theorem sum_clsN (hq : 0 < q) : ∑ c ∈ range q, clsN n q c = 3 * n + 1 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [← Fam3PF.card_nodes n, card_eq_sum_card_fiberwise (f := fun m => (m % (q : ℤ)).toNat)
    (t := range q) (fun m _ => toNat_emod_mem_range hq m)]
  refine sum_congr rfl fun c _ => ?_
  unfold clsN
  congr 1
  exact filter_congr fun m _ => (toNat_emod_eq_iff hq' _ _).symm

theorem cntL_add_one (hq : 0 < q) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    cntL n q k + 1 = clsN n q (k % (q : ℤ)).toNat := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hk' : (((k % (q : ℤ)).toNat : ℕ) : ℤ) = k % q := Int.toNat_of_nonneg (Int.emod_nonneg k hq'.ne')
  unfold cntL clsN
  rw [hk']
  have e : ((Fam3PF.nodes n).erase k).filter (fun m => (q : ℤ) ∣ k - m) =
      ((Fam3PF.nodes n).filter (fun m => m % (q : ℤ) = k % q)).erase k := by
    ext m
    simp only [mem_filter, mem_erase]
    have : (q : ℤ) ∣ k - m ↔ m % (q : ℤ) = k % q := by
      rw [← Int.ModEq, Int.modEq_iff_dvd]
    rw [this]; tauto
  have hmem : k ∈ (Fam3PF.nodes n).filter (fun m => m % (q : ℤ) = k % q) := mem_filter.2 ⟨hk, rfl⟩
  rw [e, card_erase_of_mem hmem]
  have : 0 < ((Fam3PF.nodes n).filter (fun m => m % (q : ℤ) = k % q)).card := card_pos.2 ⟨k, hmem⟩
  omega

theorem zL_emod (k : ℤ) : zL n q k = zL n q (k % (q : ℤ)) := by
  unfold zL
  congr 1
  refine filter_congr fun j _ => ?_
  have : 2 * k - 2 * j - 1 = (2 * (k % (q : ℤ)) - 2 * j - 1) + (q : ℤ) * (2 * (k / q)) := by
    have := Int.emod_add_mul_ediv k q
    linarith
  rw [this, dvd_add_left (dvd_mul_right _ _)]

theorem sqCls_le (s : Fin (3 * n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) (c : ℕ) :
    sqCls n q s c ≤ 4 * Scls n q s c := by
  unfold sqCls Scls
  rw [mul_sum]
  exact sum_le_sum fun i _ => by have := hs i; nlinarith

theorem sqCls_ge (s : Fin (3 * n + 1) → ℕ) (c : ℕ) :
    sqCls n q s c ≤ Scls n q s c ^ 2 := by
  unfold sqCls Scls
  rw [sq, sum_mul]
  exact sum_le_sum fun i hi => by
    rw [sq]; exact Nat.mul_le_mul_left _ (single_le_sum (fun _ _ => Nat.zero_le _) hi)

/-! #### Odd moduli: the zeros are equidistributed -/

theorem dvd_odd_iff {q : ℤ} (hq : Odd q) (x y : ℤ) :
    q ∣ 2 * x - 2 * y - 1 ↔ q ∣ (x - (q + 1) / 2) - y := by
  obtain ⟨t, rfl⟩ := hq
  have e : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  rw [e]
  have hcop : IsCoprime (2 * t + 1) 2 := ⟨1, -t, by ring⟩
  constructor
  · intro h
    refine hcop.dvd_of_dvd_mul_right ?_
    have : (x - (t + 1) - y) * 2 = (2 * x - 2 * y - 1) - (2 * t + 1) := by ring
    rw [this]; exact dvd_sub h dvd_rfl
  · intro h
    have : 2 * x - 2 * y - 1 = (x - (t + 1) - y) * 2 + (2 * t + 1) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left h _) dvd_rfl

theorem card_residue_eq_one {q : ℕ} (hq : Odd q) (j : ℕ) :
    ((range q).filter (fun c : ℕ => (q : ℤ) ∣ 2 * (c : ℤ) - 2 * (j : ℤ) - 1)).card = 1 := by
  have hq0 : 0 < q := hq.pos
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq0
  have hqo : Odd (q : ℤ) := by exact_mod_cast hq
  rw [card_eq_one]
  refine ⟨(((j : ℤ) + ((q : ℤ) + 1) / 2) % (q : ℤ)).toNat, ?_⟩
  ext c
  simp only [mem_filter, mem_range, mem_singleton]
  rw [dvd_odd_iff hqo, eq_comm, toNat_emod_eq_iff hq']
  constructor
  · rintro ⟨hc, hd⟩
    have h1 : ((c : ℤ)) % q = c := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hc)
    have h2 : (j + ((q : ℤ) + 1) / 2) ≡ c [ZMOD q] := by
      rw [Int.modEq_iff_dvd]; convert hd using 1; ring
    rw [Int.ModEq, h1] at h2
    exact h2
  · intro h
    have h3 : (0 : ℤ) ≤ c ∧ (c : ℤ) < q := by
      rw [← h]; exact ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
    refine ⟨by exact_mod_cast h3.2, ?_⟩
    have h2 : (j + ((q : ℤ) + 1) / 2) ≡ c [ZMOD q] := by
      rw [Int.ModEq, ← h, Int.emod_emod_of_dvd _ dvd_rfl]
    rw [Int.modEq_iff_dvd] at h2
    convert h2 using 1; ring

theorem sum_zL {q : ℕ} (hq : Odd q) : ∑ c ∈ range q, zL n q (c : ℤ) = n := by
  unfold zL
  simp only [card_filter]
  rw [sum_comm]
  simp only [← card_filter]
  rw [sum_congr rfl fun j _ => card_residue_eq_one hq j]
  simp

theorem clsN_eq_count {c : ℕ} (hc : c < q) :
    clsN n q c = #{x ∈ Ico (-(n : ℤ)) (2 * n + 1) | x ≡ c [ZMOD q]} := by
  unfold clsN
  have e : Fam3PF.nodes n = Ico (-(n : ℤ)) (2 * n + 1) := by
    ext x; simp only [Fam3PF.nodes, mem_Icc, mem_Ico]; omega
  rw [e]
  congr 1
  refine filter_congr fun x _ => ?_
  rw [Int.ModEq, Int.emod_eq_of_lt (a := (c : ℤ)) (by omega) (by exact_mod_cast hc)]

theorem zL_eq_count {q : ℕ} (hq : Odd q) (c : ℤ) :
    zL n q c = #{x ∈ Ico (0 : ℤ) n | x ≡ c - ((q : ℤ) + 1) / 2 [ZMOD q]} := by
  have hqo : Odd (q : ℤ) := by exact_mod_cast hq
  unfold zL
  refine card_nbij' (fun j : ℕ => (j : ℤ)) (fun x => x.toNat) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [coe_filter, Set.mem_setOf_eq, mem_range] at hj ⊢
    refine ⟨mem_Ico.2 ⟨by omega, by exact_mod_cast hj.1⟩, ?_⟩
    rw [Int.modEq_iff_dvd]
    have := (dvd_odd_iff hqo c j).1 hj.2
    convert this using 1
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_range, mem_Ico] at hx ⊢
    refine ⟨by omega, ?_⟩
    rw [dvd_odd_iff hqo, Int.toNat_of_nonneg hx.1.1]
    rw [Int.modEq_iff_dvd] at hx
    exact hx.2
  · intro j _; simp
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ico] at hx
    exact Int.toNat_of_nonneg hx.1.1

theorem clsN_bounds (hq : 0 < q) {c : ℕ} (hc : c < q) :
    |(clsN n q c : ℝ) - (3 * n + 1) / q| < 1 := by
  rw [clsN_eq_count hc]
  have := count_modEq_bounds (-(n : ℤ)) (2 * n + 1) c q (by exact_mod_cast hq) (by omega)
  push_cast at this
  rw [show (2 * (n : ℝ) + 1 - -n) = 3 * n + 1 by ring] at this
  rw [abs_lt]; constructor <;> linarith

theorem zL_bounds {q : ℕ} (hq : Odd q) (c : ℤ) : |(zL n q c : ℝ) - n / q| < 1 := by
  rw [zL_eq_count hq c]
  have := count_modEq_bounds 0 n (c - ((q : ℤ) + 1) / 2) q (by exact_mod_cast hq.pos) (by omega)
  push_cast at this
  rw [sub_zero] at this
  rw [abs_lt]; constructor <;> linarith

/-! #### The level bounds -/

/-- **Class-level weak duality** (paper Lemma 8.3 / Proposition 8.5): for odd `q`, every
profile `s` with `∑ s = K` and every real `a`,
`∑_c [S_c (4 N_c − 6 z_c + a) − S_c²] ≤ K(6n+4−K)/q + a K + 25 q`. -/
theorem classSum_le {q : ℕ} (hq : Odd q) (s : Fin (3 * n + 1) → ℕ) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) (a : ℝ) :
    ∑ c ∈ range q, ((Scls n q s c : ℝ) * (4 * clsN n q c - 6 * zL n q c + a) - (Scls n q s c : ℝ) ^ 2)
      ≤ K * (6 * n + 4 - K) / q + a * K + 25 * q := by
  have hq0 : 0 < q := hq.pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcard : ((range q).card : ℝ) = q := by simp
  have h := weak_duality_bound (range q) (fun c => (Scls n q s c : ℝ))
    (fun c => 4 * (clsN n q c : ℝ) - 6 * zL n q c + a) K ((6 * n + 4) / q + a)
    (by rw [hcard]; exact hqr) (by rw [sum_Scls hq0, hK]) ?_ ?_
  · rw [hcard] at h
    have e : K * ((6 * n + 4) / q + a) - K ^ 2 / q + 25 * q =
        K * (6 * n + 4 - K) / q + a * K + 25 * q := by field_simp; ring
    linarith
  · rw [hcard, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul]
    have h1 : ∑ c ∈ range q, (clsN n q c : ℝ) = 3 * n + 1 := by exact_mod_cast sum_clsN hq0
    have h2 : ∑ c ∈ range q, (zL n q c : ℝ) = n := by exact_mod_cast sum_zL hq
    rw [h1, h2]; field_simp; ring
  · intro c hc
    have hc' := mem_range.1 hc
    have h1 := clsN_bounds (n := n) hq0 hc'
    have h2 := zL_bounds (n := n) hq (c : ℤ)
    dsimp only
    rw [abs_lt] at h1 h2
    rw [abs_le]
    have e : (6 * n + 4 : ℝ) / q = 4 * ((3 * n + 1) / q) - 6 * (n / q) := by field_simp; ring
    constructor <;> nlinarith

/-- The level term for a class-constant weight: `∑_k s_k (4 #{m≠k : q ∣ k−m} − 6 z(k))`
equals `∑_c S_c (4 (N_c − 1) − 6 z_c)`. -/
theorem sum_node_weights (hq : 0 < q) (s : Fin (3 * n + 1) → ℕ) :
    ∑ i, (s i : ℝ) * (4 * (cntL n q (nodeOf n i) : ℝ) - 6 * (zL n q (nodeOf n i) : ℝ)) =
      ∑ c ∈ range q, (Scls n q s c : ℝ) * (4 * ((clsN n q c : ℝ) - 1) - 6 * zL n q c) := by
  rw [← sum_regroup hq s (fun c => 4 * ((clsN n q c : ℝ) - 1) - 6 * zL n q c)]
  refine sum_congr rfl fun i _ => ?_
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have h1 := cntL_add_one (n := n) hq (nodeOf_mem n i)
  have h2 := zL_emod (n := n) (q := q) (nodeOf n i)
  have h3 : (((nodeOf n i % (q : ℤ)).toNat : ℕ) : ℤ) = nodeOf n i % q :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
  have h2' : zL n q (nodeOf n i) = zL n q (((nodeOf n i % (q : ℤ)).toNat : ℕ) : ℤ) := by
    rw [h3]; exact h2
  rw [h2', ← h1]
  push_cast; ring

/-- **Level bound, `q` odd** (paper Lemma 8.3): for a profile `s` (`s_k ≤ 4`, `∑ s_k = K`) the
level-`q` term is `≤ K(6n+4−K)/q + 25 q`. -/
theorem levelTerm_le {q : ℕ} (hq : Odd q) (s : Fin (3 * n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) :
    (levelTerm n q s : ℝ) ≤ K * (6 * n + 4 - K) / q + 25 * q := by
  have hq0 := hq.pos
  have h := classSum_le (n := n) hq s K hK 0
  rw [levelTerm, penL]
  push_cast
  rw [sum_node_weights hq0 s, ← sum_sub_distrib]
  simp only [add_zero, zero_mul] at h
  refine le_trans (sum_le_sum fun c _ => ?_) h
  have := sqCls_le (n := n) (q := q) s hs c
  have h4 : (sqCls n q s c : ℝ) ≤ 4 * Scls n q s c := by exact_mod_cast this
  nlinarith [(Nat.cast_nonneg (Scls n q s c) : (0 : ℝ) ≤ _)]

/-- **Singleton levels** (paper Lemma 8.3): if `q > 3n` every class contains at most one node and
the level-`q` term is `≤ 0`. -/
theorem levelTerm_le_zero_of_gt (hq : 3 * n < q) (s : Fin (3 * n + 1) → ℕ) :
    levelTerm n q s ≤ 0 := by
  have hcnt : ∀ i, cntL n q (nodeOf n i) = 0 := by
    intro i
    unfold cntL
    rw [card_eq_zero, filter_eq_empty_iff]
    intro m hm hdvd
    have hk := mem_nodes_iff.1 (nodeOf_mem n i)
    have hm' := mem_nodes_iff.1 (mem_of_mem_erase hm)
    have hne := ne_of_mem_erase hm
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    exact hne (by omega)
  have hpen : 0 ≤ penL n q s := by
    unfold penL
    refine sum_nonneg fun c _ => ?_
    have := sqCls_ge (n := n) (q := q) s c
    have : (sqCls n q s c : ℤ) ≤ (Scls n q s c : ℤ) ^ 2 := by exact_mod_cast this
    linarith
  unfold levelTerm
  have : ∑ i, (s i : ℤ) * (4 * (cntL n q (nodeOf n i) : ℤ) - 6 * (zL n q (nodeOf n i) : ℤ)) ≤ 0 := by
    refine sum_nonpos fun i _ => ?_
    rw [hcnt i]
    have : (0 : ℤ) ≤ s i := by positivity
    have : (0 : ℤ) ≤ zL n q (nodeOf n i) := by positivity
    push_cast; nlinarith
  linarith

end LevelLemmas

/-! ### Level decomposition of `D_k` -/

section Decomp

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(x) = #{1 ≤ j ≤ N : p^j ∣ x}` for `x ≠ 0` with `v_p(x) ≤ N`. -/
theorem padicValInt_eq_sum_levels {x : ℤ} (hx : x ≠ 0) {N : ℕ} (hN : padicValInt p x ≤ N) :
    (padicValInt p x : ℤ) = ∑ j ∈ Icc 1 N, if ((p ^ j : ℕ) : ℤ) ∣ x then (1 : ℤ) else 0 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have e : (Icc 1 N).filter (fun j => ((p ^ j : ℕ) : ℤ) ∣ x) = Icc 1 (padicValInt p x) := by
    ext j
    simp only [mem_filter, mem_Icc, Nat.cast_pow]
    rw [padicValInt_dvd_iff]
    constructor
    · rintro ⟨_, h⟩; rcases h with h | h
      · exact absurd h hx
      · omega
    · intro h; exact ⟨by omega, Or.inr h.2⟩
  rw [e, Nat.card_Icc]; simp

omit hp in
theorem four_n_lt_pow_big (hp3 : 3 ≤ p) (n : ℕ) : 4 * n < p ^ (3 * n + 1 + 1) := by
  have h1 : n < 8 ^ n := Nat.lt_pow_self (by norm_num)
  have h2 : 4 * 8 ^ n = 2 ^ (3 * n + 2) := by
    rw [show 3 * n + 2 = 2 + 3 * n by ring, pow_add, pow_mul]; norm_num
  have h3 : 2 ^ (3 * n + 2) ≤ p ^ (3 * n + 2) := Nat.pow_le_pow_left (by omega) _
  calc 4 * n < 4 * 8 ^ n := by omega
    _ = 2 ^ (3 * n + 2) := h2
    _ ≤ p ^ (3 * n + 1 + 1) := h3

/-- **Level decomposition of `D_k`** (paper Lemma 8.3): dropping `−v_p(n−2k) ≤ 0`,
`D_k ≤ ∑_{1 ≤ j ≤ 3n+1} (4 #{m ≠ k : p^j ∣ k−m} − 6 #{j' < n : p^j ∣ 2k−2j'−1})`. -/
theorem Dk_le_sum_levels (hp3 : 3 ≤ p) {n : ℕ} {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    Dk p n k ≤ ∑ j ∈ Icc 1 (3 * n + 1),
      (4 * (cntL n (p ^ j) k : ℤ) - 6 * (zL n (p ^ j) k : ℤ)) := by
  have hL := four_n_lt_pow_big hp3 n
  have hk' := mem_nodes_iff.1 hk
  have hA : ∑ m ∈ (Fam3PF.nodes n).erase k, (padicValInt p (k - m) : ℤ) =
      ∑ j ∈ Icc 1 (3 * n + 1), (cntL n (p ^ j) k : ℤ) := by
    rw [sum_congr rfl fun m hm => padicValInt_eq_sum_levels (p := p)
      (sub_ne_zero.2 (ne_of_mem_erase hm).symm)
      (by
        have hm' := mem_nodes_iff.1 (mem_of_mem_erase hm)
        exact padicValInt_le_of_abs_le hL (by omega) (by omega)), sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [cntL, card_filter]; push_cast; rfl
  have hB : ∑ j' ∈ range n, (padicValInt p (2 * k - 2 * j' - 1) : ℤ) =
      ∑ j ∈ Icc 1 (3 * n + 1), (zL n (p ^ j) k : ℤ) := by
    rw [sum_congr rfl fun (j' : ℕ) (hj' : j' ∈ range n) => padicValInt_eq_sum_levels (p := p)
      (by omega : 2 * k - 2 * (j' : ℤ) - 1 ≠ 0)
      (by
        have := mem_range.1 hj'
        exact padicValInt_le_of_abs_le hL (by omega) (by omega)), sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [zL, card_filter]; push_cast; rfl
  unfold Dk
  rw [hA, hB, sum_sub_distrib, ← mul_sum, ← mul_sum]
  have : (0 : ℤ) ≤ padicValInt p ((n : ℤ) - 2 * k) := by positivity
  linarith

end Decomp

/-! ### Geometric sums over the levels -/

theorem sum_Icc_geom (r : ℝ) (hr : r ≠ 1) (N : ℕ) :
    ∑ j ∈ Icc 1 N, r ^ j = r * (1 - r ^ N) / (1 - r) := by
  have h1r : 1 - r ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    field_simp; ring

theorem sum_Icc_inv_pow_le {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    ∑ j ∈ Icc 1 N, (1 / (p : ℝ)) ^ j ≤ 1 / ((p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr : (1 / (p : ℝ)) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq (by linarith)]; linarith
  rw [sum_Icc_geom _ hr]
  have hpos : 0 ≤ (1 / (p : ℝ)) ^ N := by positivity
  have e : 1 / ((p : ℝ) - 1) = (1 / p) / (1 - 1 / p) := by field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)
  have : (0 : ℝ) < 1 / p := by positivity
  nlinarith

theorem sum_small_levels_le {p : ℕ} (hp : 3 ≤ p) (n N : ℕ) :
    ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ 3 * n), (p : ℝ) ^ j ≤ 9 * n / 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [filter_false_of_mem]
    · simp
    · intro j hj
      have := Nat.one_le_pow j p (by omega)
      omega
  set J := Nat.log p (3 * n)
  have hJ : p ^ J ≤ 3 * n := Nat.pow_log_le_self p (by omega)
  have hsub : (Icc 1 N).filter (fun j => p ^ j ≤ 3 * n) ⊆ range (J + 1) := by
    intro j hj
    rw [mem_filter] at hj
    rw [mem_range]
    have := Nat.le_log_of_pow_le (by omega : 1 < p) hj.2
    omega
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  calc ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ 3 * n), (p : ℝ) ^ j
      ≤ ∑ j ∈ range (J + 1), (p : ℝ) ^ j :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ((p : ℝ) ^ (J + 1) - 1) / ((p : ℝ) - 1) := geom_sum_eq (by linarith) _
    _ ≤ 9 * n / 2 := by
        have hJr : (p : ℝ) ^ J ≤ 3 * n := by exact_mod_cast hJ
        rw [div_le_iff₀ (by linarith), pow_succ]
        have : (0 : ℝ) ≤ (p : ℝ) ^ J := by positivity
        nlinarith

/-! ### Lemma A1 -/

section A1

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_profiles_iff {n K : ℕ} {s : Fin (3 * n + 1) → ℕ} :
    s ∈ profiles n K ↔ (∀ i, s i ≤ 4) ∧ ∑ i, s i = K := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i; omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i; omega, h2⟩

/-- The value of a profile is at most `∑_k s_k D_k + 12 K L_p − penalty(s)` (leaf lemma). -/
theorem profile_value_le (hp2 : p ≠ 2) {n K : ℕ} {s : Fin (3 * n + 1) → ℕ} (hs : s ∈ profiles n K) :
    (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ) ≤
      (((∑ i, (s i : ℤ) * Dk p n (nodeOf n i)) + 12 * K * Lp p n - penalty p n s : ℤ) : WithBot ℤ) := by
  have hK := (mem_profiles_iff.1 hs).2
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk p n (nodeOf n i) + 12 * s i * Lp p n : ℤ)) : WithBot ℤ)) +
          (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ => leaf_lemma hp2 (nodeOf_mem n i) (s i)) _
    _ = _ := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]
        congr 1
        rw [sum_add_distrib]
        have : ∑ i, (12 * (s i : ℤ) * Lp p n) = 12 * K * Lp p n := by
          rw [← sum_mul, ← mul_sum]; congr 2; exact_mod_cast hK
        rw [this]; ring

/-- `∑_k s_k D_k − penalty(s) ≤ ∑_{j=1}^{3n+1} (level-`p^j` term)`. -/
theorem sum_D_sub_penalty_le (hp3 : 3 ≤ p) {n : ℕ} (s : Fin (3 * n + 1) → ℕ) :
    (∑ i, (s i : ℤ) * Dk p n (nodeOf n i)) - penalty p n s ≤
      ∑ j ∈ Icc 1 (3 * n + 1), levelTerm n (p ^ j) s := by
  unfold levelTerm
  rw [sum_sub_distrib, ← penalty_eq_sum_penL, sum_comm]
  have : ∑ i, (s i : ℤ) * Dk p n (nodeOf n i) ≤
      ∑ i, ∑ j ∈ Icc 1 (3 * n + 1), (s i : ℤ) *
        (4 * (cntL n (p ^ j) (nodeOf n i) : ℤ) - 6 * (zL n (p ^ j) (nodeOf n i) : ℤ)) := by
    refine sum_le_sum fun i _ => ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (Dk_le_sum_levels hp3 (nodeOf_mem n i)) (by positivity)
  linarith

/-- The sum of the level terms, `≤ K(6n+4−K)/(p−1) + 113 n` (for `K ≤ 6n+4`). -/
theorem sum_levelTerm_le (hp3 : 3 ≤ p) {n K : ℕ} (hK6 : K ≤ 6 * n + 4) {s : Fin (3 * n + 1) → ℕ}
    (hs : s ∈ profiles n K) :
    (∑ j ∈ Icc 1 (3 * n + 1), (levelTerm n (p ^ j) s : ℝ)) ≤
      (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 113 * n := by
  obtain ⟨hs4, hK⟩ := mem_profiles_iff.1 hs
  have hKr : ∑ i, (s i : ℝ) = K := by exact_mod_cast hK
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  set A : ℝ := (K : ℝ) * (6 * n + 4 - K)
  have hA : 0 ≤ A := by
    have : (K : ℝ) ≤ 6 * n + 4 := by exact_mod_cast hK6
    have : (0 : ℝ) ≤ K := by positivity
    simp only [A]; nlinarith
  have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hterm : ∀ j ∈ Icc 1 (3 * n + 1), (levelTerm n (p ^ j) s : ℝ) ≤
      A * (1 / (p : ℝ)) ^ j + (if p ^ j ≤ 3 * n then 25 * (p : ℝ) ^ j else 0) := by
    intro j _
    have hApos : 0 ≤ A * (1 / (p : ℝ)) ^ j := by positivity
    split_ifs with h
    · have := levelTerm_le (n := n) (hodd.pow (n := j)) s hs4 K hKr
      have e : A * (1 / (p : ℝ)) ^ j = (K : ℝ) * (6 * n + 4 - K) / ((p ^ j : ℕ) : ℝ) := by
        simp only [A]; push_cast; rw [one_div_pow, mul_one_div]
      rw [e]; push_cast at this ⊢; linarith
    · have := levelTerm_le_zero_of_gt (n := n) (q := p ^ j) (by omega) s
      have : (levelTerm n (p ^ j) s : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← sum_filter, ← mul_sum]
  have h1 := sum_Icc_inv_pow_le (p := p) (by omega) (3 * n + 1)
  have h2 := sum_small_levels_le (p := p) hp3 n (3 * n + 1)
  have : A * ∑ j ∈ Icc 1 (3 * n + 1), (1 / (p : ℝ)) ^ j ≤ A * (1 / ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left h1 hA
  have e : A * (1 / ((p : ℝ) - 1)) = (K : ℝ) * (6 * n + 4 - K) / (p - 1) := by
    simp only [A]; ring
  have hn : (0 : ℝ) ≤ n := by positivity
  linarith

/-- **Lemma 8.3 (A1).**  For every odd prime `p` and every `K ≤ 6n + 4`,
`T_p ≤ K(6n+4−K)/(p−1) + 12 K L_p + 113 n`  (`T_p = −∞` is allowed). -/
theorem lemmaA1 (hp2 : p ≠ 2) (n K : ℕ) (hK6 : K ≤ 6 * n + 4) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set bound : ℝ := (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n
  have key : TP p n K ≤ ((⌊bound⌋ : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun s hs => (profile_value_le hp2 hs).trans (WithBot.coe_le_coe.2 ?_)
    refine Int.le_floor.2 ?_
    have h1 := sum_D_sub_penalty_le hp3 s (p := p)
    have h1' : (((∑ i, (s i : ℤ) * Dk p n (nodeOf n i)) - penalty p n s : ℤ) : ℝ) ≤
        ∑ j ∈ Icc 1 (3 * n + 1), (levelTerm n (p ^ j) s : ℝ) := by exact_mod_cast h1
    have h2 := sum_levelTerm_le (p := p) hp3 hK6 hs
    push_cast at h1' ⊢
    simp only [bound]
    linarith
  intro t ht
  rw [ht, WithBot.coe_le_coe] at key
  exact (Int.cast_le.2 key).trans (Int.floor_le _)

/-- **Lemma 8.3 (A1)** for `max(T_p, 0)`. -/
theorem lemmaA1_plus (hp2 : p ≠ 2) (n K : ℕ) (hK6 : K ≤ 6 * n + 4) :
    (TPplus p n K : ℝ) ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hb : 0 ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) + 12 * K * Lp p n + 113 * n := by
    have : (K : ℝ) ≤ 6 * n + 4 := by exact_mod_cast hK6
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have : 0 ≤ (K : ℝ) * (6 * n + 4 - K) / (p - 1) := by
      apply div_nonneg _ (by linarith); nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    positivity
  unfold TPplus
  induction h : TP p n K with
  | bot => simpa using hb
  | coe t =>
    have := lemmaA1 hp2 n K hK6 t h
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simpa using hb
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]; simpa using this

end A1

end Hankel2.Fam3
