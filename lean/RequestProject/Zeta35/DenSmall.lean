import RequestProject.Zeta35.DenLeaf
import RequestProject.Zeta7.Hankel2.SingleLevel

/-!
# Denominators (N, Theorem 5.1), step 2: small, middle and large primes

Port of `Hankel2.Fam3.lemmaA1` and `Hankel2.Fam3.prop85` (P, Lemma 8.3 and Proposition 8.5;
W, Lemmas 3.5–3.7) to the nodes `|k| ≤ R` of paper N (no zeros, `2R + 1` nodes), for **every**
prime `ℓ` (including `ℓ = 2`).  Write `N₀ = 4(2R + 1)` (`= 12n + 4` for even `n`).

* `D_k = ∑_{j ≥ 1} 4 #{m ≠ k : ℓ^j ∣ k − m}` (`Dk3_eq_sum_levels`), and the penalty decomposes over
  the same levels, so `∑_k s_k D_k − penalty(s) = ∑_j (level-ℓ^j term)`;
* each level `q` contributes at most `K(N₀ − K)/q + 4q` (`levelTerm_le3`, weak duality with
  deviation `4`), and nothing if `q > 2R` (`levelTerm_le_zero_of_gt3`);
* **`lemmaA1_plus3`** (small primes): `max(T_ℓ, 0) ≤ K(N₀ − K)/(ℓ − 1) + 6 K L_ℓ + 16 R`;
* **`prop85_plus3`** (single level, `9n < 2ℓ²`): `max(T_ℓ, 0) ≤ K(N₀ − K)/ℓ + 3K + 4ℓ`;
* **`TPplus_eq_zero_of_large3`** (`9n < 2ℓ`): `max(T_ℓ, 0) = 0`.
-/

open Finset Hankel2

namespace Zeta35.Den

/-! ### Weak duality with a general deviation -/

/-- **Per-level weak duality.**  If `∑ S_c = K`, `∑ B_c = q B̄` over `q` classes and
`|B_c − B̄| ≤ δ`, then `∑_c (S_c B_c − S_c²) ≤ K B̄ − K²/q + q δ²/4`. -/
theorem weak_duality_bound' {ι : Type*} (T : Finset ι) (S B : ι → ℝ) (K Bbar δ : ℝ)
    (hq : (0 : ℝ) < T.card) (hS : ∑ c ∈ T, S c = K) (hB : ∑ c ∈ T, B c = T.card * Bbar)
    (hdev : ∀ c ∈ T, |B c - Bbar| ≤ δ) :
    ∑ c ∈ T, (S c * B c - S c ^ 2) ≤ K * Bbar - K ^ 2 / T.card + T.card * δ ^ 2 / 4 := by
  set q : ℝ := (T.card : ℝ)
  set lam : ℝ := Bbar - 2 * K / q
  have h1 : ∀ c ∈ T, S c * B c - S c ^ 2 ≤ lam * S c + (B c - lam) ^ 2 / 4 := by
    intro c _; nlinarith [sq_nonneg (S c - (B c - lam) / 2)]
  have h2 := Finset.sum_le_sum h1
  have h3 : ∑ c ∈ T, (B c - lam) ^ 2 =
      ∑ c ∈ T, (B c - Bbar) ^ 2 + 4 * K / q * ∑ c ∈ T, (B c - Bbar) + q * (2 * K / q) ^ 2 := by
    rw [mul_sum]
    have : ∀ c ∈ T, (B c - lam) ^ 2 =
        (B c - Bbar) ^ 2 + 4 * K / q * (B c - Bbar) + (2 * K / q) ^ 2 := by
      intro c _; simp only [lam]; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
  have h4 : ∑ c ∈ T, (B c - Bbar) = 0 := by
    rw [sum_sub_distrib, hB, sum_const, nsmul_eq_mul]; ring
  have h5 : ∑ c ∈ T, (B c - Bbar) ^ 2 ≤ q * δ ^ 2 := by
    calc ∑ c ∈ T, (B c - Bbar) ^ 2 ≤ ∑ c ∈ T, δ ^ 2 := by
          refine sum_le_sum fun c hc => ?_
          have := hdev c hc
          have h0 : 0 ≤ δ := (abs_nonneg _).trans this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = q * δ ^ 2 := by rw [sum_const, nsmul_eq_mul]
  rw [sum_add_distrib, ← mul_sum, hS, ← sum_div] at h2
  rw [h3, h4] at h2
  have hq0 : q ≠ 0 := hq.ne'
  have e : lam * K + (∑ c ∈ T, (B c - Bbar) ^ 2 + 4 * K / q * 0 + q * (2 * K / q) ^ 2) / 4 =
      K * Bbar - K ^ 2 / q + (∑ c ∈ T, (B c - Bbar) ^ 2) / 4 := by
    simp only [lam]; field_simp; ring
  rw [e] at h2
  linarith

/-! ### Level data -/

section LevelDefs

variable (n q : ℕ)

/-- `N_c`: the number of nodes `|m| ≤ R` in the residue class `c` mod `q`. -/
def clsN3 (c : ℕ) : ℕ := #{m ∈ nodes n | m % (q : ℤ) = c}

/-- The number of other nodes `m ≠ k` with `q ∣ k − m`. -/
def cntL3 (k : ℤ) : ℕ := #{m ∈ (nodes n).erase k | (q : ℤ) ∣ k - m}

/-- `S_c = ∑_{k ≡ c (q)} s_k`. -/
def Scls3 (s : Fin (2 * R n + 1) → ℕ) (c : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => nodeOf n i % (q : ℤ) = c), s i

/-- `∑_{k ≡ c (q)} s_k²`. -/
def sqCls3 (s : Fin (2 * R n + 1) → ℕ) (c : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => nodeOf n i % (q : ℤ) = c), s i ^ 2

/-- The level-`q` part of the penalty. -/
def penL3 (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ c ∈ range q, ((Scls3 n q s c : ℤ) ^ 2 - (sqCls3 n q s c : ℤ))

/-- The level-`q` term `∑_k 4 s_k #{m ≠ k : q ∣ k − m} − penalty_q(s)`. -/
def levelTerm3 (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ i, (s i : ℤ) * (4 * (cntL3 n q (nodeOf n i) : ℤ)) - penL3 n q s

end LevelDefs

theorem penalty_eq_sum_penL3 (p n : ℕ) (s : Fin (2 * R n + 1) → ℕ) :
    penalty p n s = ∑ j ∈ Icc 1 (2 * R n + 1), penL3 n (p ^ j) s := rfl

theorem mem_profiles_iff3 {n K : ℕ} {s : Fin (2 * R n + 1) → ℕ} :
    s ∈ profiles n K ↔ (∀ i, s i ≤ 4) ∧ ∑ i, s i = K := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i; omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i; omega, h2⟩

section LevelLemmas

variable {n q : ℕ}

theorem sum_regroup3 (hq : 0 < q) (s : Fin (2 * R n + 1) → ℕ) (F : ℕ → ℝ) :
    ∑ i, (s i : ℝ) * F ((nodeOf n i % (q : ℤ)).toNat) =
      ∑ c ∈ range q, (Scls3 n q s c : ℝ) * F c := by
  rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (q : ℤ)).toNat) (t := range q)
    (fun i _ => Fam3.toNat_emod_mem_range hq _)]
  refine sum_congr rfl fun c _ => ?_
  rw [Scls3, Nat.cast_sum, sum_mul]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  refine sum_congr (filter_congr fun i _ => Fam3.toNat_emod_eq_iff hq' _ _) fun i hi => ?_
  rw [(mem_filter.1 hi).2, Int.toNat_natCast]

theorem sum_Scls3 (hq : 0 < q) (s : Fin (2 * R n + 1) → ℕ) :
    ∑ c ∈ range q, (Scls3 n q s c : ℝ) = ∑ i, (s i : ℝ) := by
  have := sum_regroup3 hq s (fun _ => 1)
  simpa using this.symm

theorem sum_sq_regroup3 (hq : 0 < q) (s : Fin (2 * R n + 1) → ℕ) :
    ∑ i, (s i : ℝ) ^ 2 = ∑ c ∈ range q, (sqCls3 n q s c : ℝ) := by
  rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (q : ℤ)).toNat) (t := range q)
    (fun i _ => Fam3.toNat_emod_mem_range hq _)]
  refine sum_congr rfl fun c _ => ?_
  rw [sqCls3, Nat.cast_sum]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  refine sum_congr (filter_congr fun i _ => Fam3.toNat_emod_eq_iff hq' _ _) fun i _ => ?_
  push_cast; ring

theorem sum_clsN3 (hq : 0 < q) : ∑ c ∈ range q, clsN3 n q c = 2 * R n + 1 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [← card_nodes n, card_eq_sum_card_fiberwise (f := fun m => (m % (q : ℤ)).toNat)
    (t := range q) (fun m _ => Fam3.toNat_emod_mem_range hq m)]
  refine sum_congr rfl fun c _ => ?_
  unfold clsN3
  congr 1
  exact filter_congr fun m _ => (Fam3.toNat_emod_eq_iff hq' _ _).symm

theorem cntL_add_one3 (hq : 0 < q) {k : ℤ} (hk : k ∈ nodes n) :
    cntL3 n q k + 1 = clsN3 n q (k % (q : ℤ)).toNat := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hk' : (((k % (q : ℤ)).toNat : ℕ) : ℤ) = k % q :=
    Int.toNat_of_nonneg (Int.emod_nonneg k hq'.ne')
  unfold cntL3 clsN3
  rw [hk']
  have e : ((nodes n).erase k).filter (fun m => (q : ℤ) ∣ k - m) =
      ((nodes n).filter (fun m => m % (q : ℤ) = k % q)).erase k := by
    ext m
    simp only [mem_filter, mem_erase]
    have : (q : ℤ) ∣ k - m ↔ m % (q : ℤ) = k % q := by
      rw [← Int.ModEq, Int.modEq_iff_dvd]
    rw [this]; tauto
  have hmem : k ∈ (nodes n).filter (fun m => m % (q : ℤ) = k % q) := mem_filter.2 ⟨hk, rfl⟩
  rw [e, card_erase_of_mem hmem]
  have : 0 < ((nodes n).filter (fun m => m % (q : ℤ) = k % q)).card := card_pos.2 ⟨k, hmem⟩
  omega

theorem sqCls_le3 (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) (c : ℕ) :
    sqCls3 n q s c ≤ 4 * Scls3 n q s c := by
  unfold sqCls3 Scls3
  rw [mul_sum]
  exact sum_le_sum fun i _ => by have := hs i; nlinarith

theorem sqCls_ge3 (s : Fin (2 * R n + 1) → ℕ) (c : ℕ) :
    sqCls3 n q s c ≤ Scls3 n q s c ^ 2 := by
  unfold sqCls3 Scls3
  rw [sq, sum_mul]
  exact sum_le_sum fun i hi => by
    rw [sq]; exact Nat.mul_le_mul_left _ (single_le_sum (fun _ _ => Nat.zero_le _) hi)

theorem clsN_eq_count3 {c : ℕ} (hc : c < q) :
    clsN3 n q c = #{x ∈ Ico (-(R n : ℤ)) (R n + 1) | x ≡ c [ZMOD q]} := by
  unfold clsN3
  have e : nodes n = Ico (-(R n : ℤ)) (R n + 1) := by
    ext x; simp only [nodes, mem_Icc, mem_Ico]; omega
  rw [e]
  congr 1
  refine filter_congr fun x _ => ?_
  rw [Int.ModEq, Int.emod_eq_of_lt (a := (c : ℤ)) (by omega) (by exact_mod_cast hc)]

theorem clsN_bounds3 (hq : 0 < q) {c : ℕ} (hc : c < q) :
    |(clsN3 n q c : ℝ) - (2 * R n + 1) / q| < 1 := by
  rw [clsN_eq_count3 hc]
  have := Fam3.count_modEq_bounds (-(R n : ℤ)) (R n + 1) c q (by exact_mod_cast hq) (by omega)
  push_cast at this
  rw [show ((R n : ℝ) + 1 - -(R n : ℝ)) = 2 * R n + 1 by ring] at this
  rw [abs_lt]; constructor <;> linarith

/-- **Class-level weak duality**: for `q ≥ 1`, every profile `s` with `∑ s = K` and every real
`a`, `∑_c [S_c (4 N_c + a) − S_c²] ≤ K(N₀ − K)/q + a K + 4 q`, `N₀ = 4(2R+1)`. -/
theorem classSum_le3 (hq0 : 0 < q) (s : Fin (2 * R n + 1) → ℕ) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) (a : ℝ) :
    ∑ c ∈ range q, ((Scls3 n q s c : ℝ) * (4 * clsN3 n q c + a) - (Scls3 n q s c : ℝ) ^ 2)
      ≤ K * (4 * (2 * R n + 1) - K) / q + a * K + 4 * q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcard : ((range q).card : ℝ) = q := by simp
  have h := weak_duality_bound' (range q) (fun c => (Scls3 n q s c : ℝ))
    (fun c => 4 * (clsN3 n q c : ℝ) + a) K (4 * (2 * R n + 1) / q + a) 4
    (by rw [hcard]; exact hqr) (by rw [sum_Scls3 hq0, hK]) ?_ ?_
  · rw [hcard] at h
    have e : K * (4 * (2 * R n + 1) / q + a) - K ^ 2 / q + q * 4 ^ 2 / 4 =
        K * (4 * (2 * R n + 1) - K) / q + a * K + 4 * q := by field_simp; ring
    linarith
  · rw [hcard, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    have h1 : ∑ c ∈ range q, (clsN3 n q c : ℝ) = 2 * R n + 1 := by
      exact_mod_cast sum_clsN3 hq0
    rw [h1]; field_simp
  · intro c hc
    have hc' := mem_range.1 hc
    have h1 := clsN_bounds3 (n := n) hq0 hc'
    dsimp only
    rw [abs_lt] at h1
    rw [abs_le]
    have e : (4 * (2 * R n + 1) : ℝ) / q = 4 * ((2 * R n + 1) / q) := by ring
    constructor <;> nlinarith

theorem sum_node_weights3 (hq : 0 < q) (s : Fin (2 * R n + 1) → ℕ) :
    ∑ i, (s i : ℝ) * (4 * (cntL3 n q (nodeOf n i) : ℝ)) =
      ∑ c ∈ range q, (Scls3 n q s c : ℝ) * (4 * ((clsN3 n q c : ℝ) - 1)) := by
  rw [← sum_regroup3 hq s (fun c => 4 * ((clsN3 n q c : ℝ) - 1))]
  refine sum_congr rfl fun i _ => ?_
  have h1 := cntL_add_one3 (n := n) hq (nodeOf_mem_nodes n i)
  rw [← h1]
  push_cast; ring

/-- **Level bound**: for a profile `s` (`s_k ≤ 4`, `∑ s_k = K`) the level-`q` term is
`≤ K(N₀ − K)/q + 4q`. -/
theorem levelTerm_le3 (hq0 : 0 < q) (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) :
    (levelTerm3 n q s : ℝ) ≤ K * (4 * (2 * R n + 1) - K) / q + 4 * q := by
  have h := classSum_le3 (n := n) hq0 s K hK 0
  rw [levelTerm3, penL3]
  push_cast
  rw [sum_node_weights3 hq0 s, ← sum_sub_distrib]
  simp only [add_zero, zero_mul] at h
  refine le_trans (sum_le_sum fun c _ => ?_) h
  have := sqCls_le3 (n := n) (q := q) s hs c
  have h4 : (sqCls3 n q s c : ℝ) ≤ 4 * Scls3 n q s c := by exact_mod_cast this
  nlinarith [(Nat.cast_nonneg (Scls3 n q s c) : (0 : ℝ) ≤ _)]

theorem cntL_eq_zero_of_gt3 (hq : 2 * R n < q) {k : ℤ} (hk : k ∈ nodes n) : cntL3 n q k = 0 := by
  unfold cntL3
  rw [card_eq_zero, filter_eq_empty_iff]
  intro m hm hdvd
  have hk' := Finset.mem_Icc.1 hk
  have hm' := Finset.mem_Icc.1 (mem_of_mem_erase hm)
  have hne := ne_of_mem_erase hm
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
  exact hne (by omega)

theorem penL_nonneg3 (s : Fin (2 * R n + 1) → ℕ) : 0 ≤ penL3 n q s := by
  unfold penL3
  refine sum_nonneg fun c _ => ?_
  have := sqCls_ge3 (n := n) (q := q) s c
  have : (sqCls3 n q s c : ℤ) ≤ (Scls3 n q s c : ℤ) ^ 2 := by exact_mod_cast this
  linarith

/-- **Singleton levels**: if `q > 2R` every class has at most one node, and the term is `≤ 0`. -/
theorem levelTerm_le_zero_of_gt3 (hq : 2 * R n < q) (s : Fin (2 * R n + 1) → ℕ) :
    levelTerm3 n q s ≤ 0 := by
  have hpen := penL_nonneg3 (n := n) (q := q) s
  unfold levelTerm3
  have : ∑ i, (s i : ℤ) * (4 * (cntL3 n q (nodeOf n i) : ℤ)) = 0 := by
    refine sum_eq_zero fun i _ => ?_
    rw [cntL_eq_zero_of_gt3 hq (nodeOf_mem_nodes n i)]; simp
  linarith

end LevelLemmas

/-! ### Level decomposition of `D_k` -/

section Decomp

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_R_lt_pow (n : ℕ) : 2 * R n < p ^ (2 * R n + 1) := by
  have h1 : 2 * R n < 2 ^ (2 * R n) := Nat.lt_two_pow_self
  have h3 : 2 ^ (2 * R n) ≤ p ^ (2 * R n + 1) :=
    (Nat.pow_le_pow_left hp.out.two_le _).trans (Nat.pow_le_pow_right hp.out.pos (by omega))
  omega

/-- **Level decomposition of `D_k`**: `D_k = ∑_{1 ≤ j ≤ 2R+1} 4 #{m ≠ k : p^j ∣ k − m}`. -/
theorem Dk3_eq_sum_levels {n : ℕ} {k : ℤ} (hk : k ∈ nodes n) :
    Dk3 p n k = ∑ j ∈ Icc 1 (2 * R n + 1), 4 * (cntL3 n (p ^ j) k : ℤ) := by
  have hk' := Finset.mem_Icc.1 hk
  have hA : ∑ m ∈ (nodes n).erase k, (padicValInt p (k - m) : ℤ) =
      ∑ j ∈ Icc 1 (2 * R n + 1), (cntL3 n (p ^ j) k : ℤ) := by
    rw [sum_congr rfl fun m hm => Fam3.padicValInt_eq_sum_levels (p := p)
      (sub_ne_zero.2 (ne_of_mem_erase hm).symm)
      (by
        have hm' := Finset.mem_Icc.1 (mem_of_mem_erase hm)
        have hne : k - m ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hm).symm
        refine Fam3.padicValInt_le_of_natAbs_lt hne ?_
        have := two_R_lt_pow (p := p) n
        have : (k - m).natAbs ≤ 2 * R n := by omega
        calc (k - m).natAbs < p ^ (2 * R n + 1) := by omega
          _ ≤ p ^ (2 * R n + 1 + 1) := Nat.pow_le_pow_right hp.out.pos (by omega)), sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [cntL3, card_filter]; push_cast; rfl
  unfold Dk3
  rw [hA, mul_sum]

theorem sum_D_sub_penalty_eq3 {n : ℕ} (s : Fin (2 * R n + 1) → ℕ) :
    (∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i)) - penalty p n s =
      ∑ j ∈ Icc 1 (2 * R n + 1), levelTerm3 n (p ^ j) s := by
  unfold levelTerm3
  rw [sum_sub_distrib, ← penalty_eq_sum_penL3, sum_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Dk3_eq_sum_levels (nodeOf_mem_nodes n i), mul_sum]

end Decomp

/-! ### Geometric sums over the levels -/

theorem sum_small_levels_le3 {p : ℕ} (hp : 2 ≤ p) (M N : ℕ) :
    ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ M), (p : ℝ) ^ j ≤ 2 * M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [filter_false_of_mem]
    · simp
    · intro j hj
      have := Nat.one_le_pow j p (by omega)
      omega
  set J := Nat.log p M
  have hJ : p ^ J ≤ M := Nat.pow_log_le_self p (by omega)
  have hsub : (Icc 1 N).filter (fun j => p ^ j ≤ M) ⊆ range (J + 1) := by
    intro j hj
    rw [mem_filter] at hj
    rw [mem_range]
    have := Nat.le_log_of_pow_le (by omega : 1 < p) hj.2
    omega
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ M), (p : ℝ) ^ j
      ≤ ∑ j ∈ range (J + 1), (p : ℝ) ^ j :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ((p : ℝ) ^ (J + 1) - 1) / ((p : ℝ) - 1) := geom_sum_eq (by linarith) _
    _ ≤ 2 * M := by
        have hJr : (p : ℝ) ^ J ≤ M := by exact_mod_cast hJ
        rw [div_le_iff₀ (by linarith), pow_succ]
        have : (0 : ℝ) ≤ (p : ℝ) ^ J := by positivity
        nlinarith

/-! ### Small primes (P, Lemma 8.3; W, Lemma 3.5) -/

section A1

variable {p : ℕ} [hp : Fact p.Prime]

theorem profile_value_le3 {n K : ℕ} {s : Fin (2 * R n + 1) → ℕ} (hs : s ∈ profiles n K) :
    (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ) ≤
      (((∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i)) + 6 * K * Lp3 p n - penalty p n s : ℤ) :
        WithBot ℤ) := by
  have hK := (mem_profiles_iff3.1 hs).2
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk3 p n (nodeOf n i) + 6 * s i * Lp3 p n : ℤ)) : WithBot ℤ)) +
          (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ =>
          leaf_lemma3 (nodeOf_mem_nodes n i) (s i)) _
    _ = _ := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]
        congr 1
        rw [sum_add_distrib]
        have : ∑ i, (6 * (s i : ℤ) * Lp3 p n) = 6 * K * Lp3 p n := by
          rw [← sum_mul, ← mul_sum]; congr 2; exact_mod_cast hK
        rw [this]; ring

theorem sum_levelTerm_le3 {n K : ℕ} (hK6 : K ≤ 4 * (2 * R n + 1)) {s : Fin (2 * R n + 1) → ℕ}
    (hs : s ∈ profiles n K) :
    (∑ j ∈ Icc 1 (2 * R n + 1), (levelTerm3 n (p ^ j) s : ℝ)) ≤
      (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) + 16 * R n := by
  obtain ⟨hs4, hK⟩ := mem_profiles_iff3.1 hs
  have hKr : ∑ i, (s i : ℝ) = K := by exact_mod_cast hK
  have hp2 : 2 ≤ p := hp.out.two_le
  set A : ℝ := (K : ℝ) * (4 * (2 * R n + 1) - K)
  have hA : 0 ≤ A := by
    have : (K : ℝ) ≤ 4 * (2 * R n + 1) := by exact_mod_cast hK6
    have : (0 : ℝ) ≤ K := by positivity
    simp only [A]; nlinarith
  have hterm : ∀ j ∈ Icc 1 (2 * R n + 1), (levelTerm3 n (p ^ j) s : ℝ) ≤
      A * (1 / (p : ℝ)) ^ j + (if p ^ j ≤ 2 * R n then 4 * (p : ℝ) ^ j else 0) := by
    intro j _
    have hApos : 0 ≤ A * (1 / (p : ℝ)) ^ j := by positivity
    split_ifs with h
    · have := levelTerm_le3 (n := n) (q := p ^ j) (pow_pos hp.out.pos j) s hs4 K hKr
      have e : A * (1 / (p : ℝ)) ^ j = (K : ℝ) * (4 * (2 * R n + 1) - K) / ((p ^ j : ℕ) : ℝ) := by
        simp only [A]; push_cast; rw [one_div_pow, mul_one_div]
      rw [e]; push_cast at this ⊢; linarith
    · have := levelTerm_le_zero_of_gt3 (n := n) (q := p ^ j) (by omega) s
      have : (levelTerm3 n (p ^ j) s : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← sum_filter, ← mul_sum]
  have h1 := Fam3.sum_Icc_inv_pow_le (p := p) hp2 (2 * R n + 1)
  have h2 := sum_small_levels_le3 (p := p) hp2 (2 * R n) (2 * R n + 1)
  have : A * ∑ j ∈ Icc 1 (2 * R n + 1), (1 / (p : ℝ)) ^ j ≤ A * (1 / ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left h1 hA
  have e : A * (1 / ((p : ℝ) - 1)) = (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) := by
    simp only [A]; ring
  push_cast at h2
  linarith

/-- **Small primes** (P, Lemma 8.3; W, Lemma 3.5): for every prime `p` and `K ≤ 4(2R+1)`,
`T_p ≤ K(4(2R+1) − K)/(p − 1) + 6 K L_p + 16 R`. -/
theorem lemmaA1_3 (n K : ℕ) (hK6 : K ≤ 4 * (2 * R n + 1)) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) + 6 * K * Lp3 p n + 16 * R n := by
  set bound : ℝ := (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) + 6 * K * Lp3 p n + 16 * R n
  have key : TP p n K ≤ ((⌊bound⌋ : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun s hs => (profile_value_le3 hs).trans (WithBot.coe_le_coe.2 ?_)
    refine Int.le_floor.2 ?_
    have h1 := sum_D_sub_penalty_eq3 s (p := p)
    have h1' : (((∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i)) - penalty p n s : ℤ) : ℝ) =
        ∑ j ∈ Icc 1 (2 * R n + 1), (levelTerm3 n (p ^ j) s : ℝ) := by exact_mod_cast h1
    have h2 := sum_levelTerm_le3 (p := p) hK6 hs
    push_cast at h1' ⊢
    simp only [bound]
    linarith
  intro t ht
  rw [ht, WithBot.coe_le_coe] at key
  exact (Int.cast_le.2 key).trans (Int.floor_le _)

theorem TPplus_le_of {p n K : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : ℤ, TP p n K = (t : WithBot ℤ) → (t : ℝ) ≤ B) : (TPplus p n K : ℝ) ≤ B := by
  unfold TPplus
  induction hT : TP p n K with
  | bot => simpa using hB
  | coe t =>
    have := h t hT
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right (by exact_mod_cast ht : (t : WithBot ℤ) ≤ 0)]; simpa using hB
    · rw [max_eq_left (by exact_mod_cast ht : (0 : WithBot ℤ) ≤ t)]; simpa using this

/-- **Small primes** for `max(T_p, 0)`. -/
theorem lemmaA1_plus3 (n K : ℕ) (hK6 : K ≤ 4 * (2 * R n + 1)) :
    (TPplus p n K : ℝ) ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) + 6 * K * Lp3 p n +
      16 * R n := by
  refine TPplus_le_of ?_ (lemmaA1_3 n K hK6)
  have : (K : ℝ) ≤ 4 * (2 * R n + 1) := by exact_mod_cast hK6
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have : 0 ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / (p - 1) := by
    apply div_nonneg _ (by linarith); nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  positivity

end A1

/-! ### Single-level primes (P, Proposition 8.5; W, Lemma 3.7) -/

section Single

variable {p : ℕ} [hp : Fact p.Prime]

theorem profile_value_le_single3 {n : ℕ} (h9 : 9 * n < 2 * p ^ 2) (s : Fin (2 * R n + 1) → ℕ) :
    (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ) ≤
      (((∑ i, ((s i : ℤ) * Dk3 p n (nodeOf n i) + 6 * s i - s i * (s i - 1))) -
        penalty p n s : ℤ) : WithBot ℤ) := by
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk3 p n (nodeOf n i) + 6 * s i - s i * (s i - 1) : ℤ)) :
          WithBot ℤ)) + (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ =>
          fP_le_single3 h9 (nodeOf_mem_nodes n i) (s i)) _
    _ = _ := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]
        congr 1

omit hp in
theorem levelOne_single_le3 {n : ℕ} (hq0 : 0 < p) (s : Fin (2 * R n + 1) → ℕ) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) :
    (levelTerm3 n p s : ℝ) + ∑ i, (7 * (s i : ℝ) - (s i : ℝ) ^ 2) ≤
      K * (4 * (2 * R n + 1) - K) / p + 3 * K + 4 * p := by
  have h := classSum_le3 (n := n) hq0 s K hK 3
  rw [levelTerm3, penL3]
  push_cast
  have h7 : ∑ i, (7 * (s i : ℝ) - (s i : ℝ) ^ 2) =
      7 * K - ∑ c ∈ range p, (sqCls3 n p s c : ℝ) := by
    rw [sum_sub_distrib, ← mul_sum, hK, sum_sq_regroup3 hq0 s]
  have hS := sum_Scls3 (n := n) hq0 s
  rw [sum_node_weights3 hq0 s, h7]
  have e : ∀ c ∈ range p, (Scls3 n p s c : ℝ) * (4 * clsN3 n p c + 3) -
      (Scls3 n p s c : ℝ) ^ 2 = (Scls3 n p s c : ℝ) * (4 * ((clsN3 n p c : ℝ) - 1)) -
        ((Scls3 n p s c : ℝ) ^ 2 - sqCls3 n p s c) + 7 * Scls3 n p s c - sqCls3 n p s c := by
    intro c _; ring
  rw [sum_congr rfl e] at h
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  rw [sum_sub_distrib]
  linarith

/-- **Single-level primes** (P, Proposition 8.5; W, Lemma 3.7): if `9n < 2p²` then
`T_p ≤ K(4(2R+1) − K)/p + 3K + 4p`. -/
theorem prop85_3 {n : ℕ} (h9 : 9 * n < 2 * p ^ 2) (K : ℕ) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / p + 3 * K + 4 * p := by
  have hp2 : 2 ≤ p := hp.out.two_le
  set bound : ℝ := (K : ℝ) * (4 * (2 * R n + 1) - K) / p + 3 * K + 4 * p
  have key : TP p n K ≤ ((⌊bound⌋ : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun s hs => (profile_value_le_single3 h9 s).trans
      (WithBot.coe_le_coe.2 ?_)
    refine Int.le_floor.2 ?_
    obtain ⟨hs4, hK⟩ := mem_profiles_iff3.1 hs
    have hKr : ∑ i, (s i : ℝ) = K := by exact_mod_cast hK
    have h1 := sum_D_sub_penalty_eq3 s (p := p)
    have h1' : (((∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i)) - penalty p n s : ℤ) : ℝ) =
        ∑ j ∈ Icc 1 (2 * R n + 1), (levelTerm3 n (p ^ j) s : ℝ) := by exact_mod_cast h1
    have hR : 2 * R n < p ^ 2 := by unfold R; omega
    have h2 : ∑ j ∈ Icc 1 (2 * R n + 1), (levelTerm3 n (p ^ j) s : ℝ) ≤
        (levelTerm3 n p s : ℝ) := by
      rw [← add_sum_erase _ _ (mem_Icc.2 ⟨le_rfl, by omega⟩), pow_one]
      have : ∑ j ∈ (Icc 1 (2 * R n + 1)).erase 1, (levelTerm3 n (p ^ j) s : ℝ) ≤ 0 := by
        refine sum_nonpos fun j hj => ?_
        have hj' := mem_erase.1 hj
        have hj2 : 2 ≤ j := by have := (mem_Icc.1 hj'.2).1; omega
        have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj2
        exact_mod_cast levelTerm_le_zero_of_gt3 (n := n) (by omega) s
      linarith
    have h3 := levelOne_single_le3 (n := n) hp.out.pos s K hKr
    push_cast at h1' ⊢
    have e : ∑ i, ((s i : ℝ) * (Dk3 p n (nodeOf n i) : ℝ) + 6 * s i - s i * (s i - 1)) =
        ∑ i, (s i : ℝ) * (Dk3 p n (nodeOf n i) : ℝ) + ∑ i, (7 * (s i : ℝ) - (s i : ℝ) ^ 2) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; ring
    rw [e]
    simp only [bound]
    linarith
  intro t ht
  rw [ht, WithBot.coe_le_coe] at key
  exact (Int.cast_le.2 key).trans (Int.floor_le _)

/-- **Single-level primes** for `max(T_p, 0)` (for `K ≤ 4(2R+1)`). -/
theorem prop85_plus3 {n : ℕ} (h9 : 9 * n < 2 * p ^ 2) {K : ℕ} (hK6 : K ≤ 4 * (2 * R n + 1)) :
    (TPplus p n K : ℝ) ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / p + 3 * K + 4 * p := by
  refine TPplus_le_of ?_ (prop85_3 h9 K)
  have : (K : ℝ) ≤ 4 * (2 * R n + 1) := by exact_mod_cast hK6
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have : 0 ≤ (K : ℝ) * (4 * (2 * R n + 1) - K) / p := by
    apply div_nonneg _ (by linarith); nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  positivity

/-- **Large primes**: if `9n < 2p` then `T_p ≤ 0`. -/
theorem TP_le_zero_of_large3 {n : ℕ} (h9 : 9 * n < 2 * p) (K : ℕ) : TP p n K ≤ (0 : WithBot ℤ) := by
  have hL : 9 * n < 2 * p ^ (0 + 1) := by simpa using h9
  have hR : 2 * R n < p := by unfold R; omega
  refine Finset.sup_le fun s _ => ?_
  have hD : ∀ i, Dk3 p n (nodeOf n i) = 0 := by
    intro i
    rw [Dk3_eq_sum_levels (nodeOf_mem_nodes n i)]
    refine sum_eq_zero fun j hj => ?_
    have hj1 := (mem_Icc.1 hj).1
    have : p ≤ p ^ j := Nat.le_self_pow (by omega) p
    rw [cntL_eq_zero_of_gt3 (by omega) (nodeOf_mem_nodes n i)]; simp
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk3 p n (nodeOf n i) : ℤ)) : WithBot ℤ)) +
          (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ => by
          simpa using fP_le_sharp3 hL (nodeOf_mem_nodes n i) (s i)) _
    _ = (((∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i)) - penalty p n s : ℤ) : WithBot ℤ) := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]; congr 1
    _ ≤ (0 : WithBot ℤ) := by
        rw [← WithBot.coe_zero, WithBot.coe_le_coe]
        have h1 : ∑ i, (s i : ℤ) * Dk3 p n (nodeOf n i) = 0 :=
          sum_eq_zero fun i _ => by rw [hD i, mul_zero]
        have h2 : 0 ≤ penalty p n s := by
          rw [penalty_eq_sum_penL3]; exact sum_nonneg fun j _ => penL_nonneg3 s
        linarith

/-- **Large primes**: if `9n < 2p` then `max(T_p, 0) = 0`. -/
theorem TPplus_eq_zero_of_large3 {n : ℕ} (h9 : 9 * n < 2 * p) (K : ℕ) : TPplus p n K = 0 := by
  unfold TPplus
  rw [max_eq_right (TP_le_zero_of_large3 h9 K)]
  rfl

end Single

end Zeta35.Den
