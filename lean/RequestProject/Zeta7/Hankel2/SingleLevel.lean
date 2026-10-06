import RequestProject.Zeta7.Hankel2.LemmaA1

/-!
# Single-level primes `p² > 6n` (paper §8.3): Proposition 8.5

For `p² > 6n` all the valuations of Lemma 7.2 are `≤ 1`, and the sharp leaf bound gives
`f_p(k, s) ≤ s D_k + 8 s − s (s−1)`, i.e. `f_p(k,s) + s² ≤ s (D_k + 9)` (`fP_le_single`).
Only the level `j = 1` has non-singleton classes, and the class-level weak duality
(`classSum_le`, with the shift `a = 5`) gives

  **Proposition 8.5** (`prop85`): `T_p ≤ K(6n+4−K)/p + 5K + 25p`.

In the paper this is stated for `p² > 6n` **and** `p ≤ 0.4n`; the second hypothesis is used there only
to guarantee `D_c ≥ 0`, which is needed to evaluate the clipped leaf bound `f⁺` exactly (Lemma 8.4).
Working directly with the unclipped `e_p` (sharp leaf bound) avoids this, so `prop85` needs only
`p² > 6n`; `prop85_paper` is the statement with the paper's hypotheses.
-/

open Finset

namespace Hankel2.Fam3

variable {p : ℕ} [hp : Fact p.Prime]

/-- The value of a profile is at most `∑_k (s_k D_k + 8 s_k − s_k(s_k−1)) − penalty(s)` when
`p² > 6n`. -/
theorem profile_value_le_single (hp2 : p ≠ 2) {n : ℕ} (h6 : 6 * n < p ^ 2)
    (s : Fin (3 * n + 1) → ℕ) :
    (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ) ≤
      (((∑ i, ((s i : ℤ) * Dk p n (nodeOf n i) + 8 * s i - s i * (s i - 1))) - penalty p n s : ℤ) :
        WithBot ℤ) := by
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk p n (nodeOf n i) + 8 * s i - s i * (s i - 1) : ℤ)) : WithBot ℤ)) +
          (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ => fP_le_single hp2 h6 (nodeOf_mem n i) (s i)) _
    _ = _ := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]
        congr 1

/-- Regrouping `∑_k s_k²` by residue classes. -/
theorem sum_sq_regroup {n q : ℕ} (hq : 0 < q) (s : Fin (3 * n + 1) → ℕ) :
    ∑ i, (s i : ℝ) ^ 2 = ∑ c ∈ range q, (sqCls n q s c : ℝ) := by
  rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (q : ℤ)).toNat) (t := range q)
    (fun i _ => toNat_emod_mem_range hq _)]
  refine sum_congr rfl fun c _ => ?_
  rw [sqCls, Nat.cast_sum]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  refine sum_congr (filter_congr fun i _ => toNat_emod_eq_iff hq' _ _) fun i _ => ?_
  push_cast; ring

omit hp in
/-- The level-one bound with the single-level leaf: `levelTerm_p + ∑_k (9 s_k − s_k²)
≤ K(6n+4−K)/p + 5K + 25p`. -/
theorem levelOne_single_le {n : ℕ} (hodd : Odd p) (s : Fin (3 * n + 1) → ℕ) (K : ℝ)
    (hK : ∑ i, (s i : ℝ) = K) :
    (levelTerm n p s : ℝ) + ∑ i, (9 * (s i : ℝ) - (s i : ℝ) ^ 2) ≤
      K * (6 * n + 4 - K) / p + 5 * K + 25 * p := by
  have hq0 := hodd.pos
  have h := classSum_le (n := n) hodd s K hK 5
  rw [levelTerm, penL]
  push_cast
  have h9 : ∑ i, (9 * (s i : ℝ) - (s i : ℝ) ^ 2) = 9 * K - ∑ c ∈ range p, (sqCls n p s c : ℝ) := by
    rw [sum_sub_distrib, ← mul_sum, hK, sum_sq_regroup hq0 s]
  have hS := sum_Scls (n := n) hq0 s
  rw [sum_node_weights hq0 s, h9]
  have e : ∀ c ∈ range p, (Scls n p s c : ℝ) * (4 * clsN n p c - 6 * zL n p c + 5) -
      (Scls n p s c : ℝ) ^ 2 = (Scls n p s c : ℝ) * (4 * ((clsN n p c : ℝ) - 1) - 6 * zL n p c) -
        ((Scls n p s c : ℝ) ^ 2 - sqCls n p s c) + 9 * Scls n p s c - sqCls n p s c := by
    intro c _; ring
  rw [sum_congr rfl e] at h
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at h
  rw [sum_sub_distrib]
  linarith

/-- **Proposition 8.5 (small `u`), unclipped form.** If `p² > 6n` then
`T_p ≤ K(6n+4−K)/p + 5K + 25p`. -/
theorem prop85 (hp2 : p ≠ 2) {n : ℕ} (h6 : 6 * n < p ^ 2) (K : ℕ) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ (K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set bound : ℝ := (K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p
  have key : TP p n K ≤ ((⌊bound⌋ : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun s hs => (profile_value_le_single hp2 h6 s).trans
      (WithBot.coe_le_coe.2 ?_)
    refine Int.le_floor.2 ?_
    obtain ⟨hs4, hK⟩ := mem_profiles_iff.1 hs
    have hKr : ∑ i, (s i : ℝ) = K := by exact_mod_cast hK
    -- the level decomposition
    have h1 := sum_D_sub_penalty_le hp3 s (p := p)
    have h1' : (((∑ i, (s i : ℤ) * Dk p n (nodeOf n i)) - penalty p n s : ℤ) : ℝ) ≤
        ∑ j ∈ Icc 1 (3 * n + 1), (levelTerm n (p ^ j) s : ℝ) := by exact_mod_cast h1
    -- only level one survives
    have h2 : ∑ j ∈ Icc 1 (3 * n + 1), (levelTerm n (p ^ j) s : ℝ) ≤ (levelTerm n p s : ℝ) := by
      rw [← add_sum_erase _ _ (mem_Icc.2 ⟨le_rfl, by omega⟩), pow_one]
      have : ∑ j ∈ (Icc 1 (3 * n + 1)).erase 1, (levelTerm n (p ^ j) s : ℝ) ≤ 0 := by
        refine sum_nonpos fun j hj => ?_
        have hj' := mem_erase.1 hj
        have hj2 : 2 ≤ j := by have := (mem_Icc.1 hj'.2).1; omega
        have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj2
        exact_mod_cast levelTerm_le_zero_of_gt (n := n) (by omega) s
      linarith
    have h3 := levelOne_single_le (n := n) hodd s K hKr
    push_cast at h1' ⊢
    have e : ∑ i, ((s i : ℝ) * (Dk p n (nodeOf n i) : ℝ) + 8 * s i - s i * (s i - 1)) =
        ∑ i, (s i : ℝ) * (Dk p n (nodeOf n i) : ℝ) + ∑ i, (9 * (s i : ℝ) - (s i : ℝ) ^ 2) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; ring
    rw [e]
    simp only [bound]
    linarith
  intro t ht
  rw [ht, WithBot.coe_le_coe] at key
  exact (Int.cast_le.2 key).trans (Int.floor_le _)

/-- **Proposition 8.5** with the paper's hypotheses `p² > 6n` and `p ≤ 0.4 n`
(the second one is not needed, see `prop85`). -/
theorem prop85_paper (hp2 : p ≠ 2) {n : ℕ} (h6 : 6 * n < p ^ 2) (_h04 : (p : ℝ) ≤ 0.4 * n)
    (K : ℕ) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ (K : ℝ) * (6 * n + 4 - K) / p + 5 * K + 25 * p :=
  prop85 hp2 h6 K

/-! ### Large primes `p > 4n` (paper §8.3, end of the circle model) -/

omit hp in
theorem cntL_eq_zero_of_gt {n q : ℕ} (hq : 3 * n < q) {k : ℤ} (hk : k ∈ Fam3PF.nodes n) :
    cntL n q k = 0 := by
  unfold cntL
  rw [card_eq_zero, filter_eq_empty_iff]
  intro m hm hdvd
  have hk' := mem_nodes_iff.1 hk
  have hm' := mem_nodes_iff.1 (mem_of_mem_erase hm)
  have hne := ne_of_mem_erase hm
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
  exact hne (by omega)

/-- For `p > 4n`, `D_k ≤ 0` for every node. -/
theorem Dk_nonpos_of_large (hp2 : p ≠ 2) {n : ℕ} (h4 : 4 * n < p) {k : ℤ}
    (hk : k ∈ Fam3PF.nodes n) : Dk p n k ≤ 0 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  refine (Dk_le_sum_levels hp3 hk).trans (sum_nonpos fun j hj => ?_)
  have hj1 := (mem_Icc.1 hj).1
  have : p ≤ p ^ j := Nat.le_self_pow (by omega) p
  rw [cntL_eq_zero_of_gt (by omega) hk]
  have : (0 : ℤ) ≤ zL n (p ^ j) k := by positivity
  push_cast; linarith

theorem penalty_nonneg (p n : ℕ) (s : Fin (3 * n + 1) → ℕ) : 0 ≤ penalty p n s := by
  rw [penalty_eq_sum_penL]
  refine sum_nonneg fun j _ => ?_
  unfold penL
  refine sum_nonneg fun c _ => ?_
  have := sqCls_ge (n := n) (q := p ^ j) s c
  have : (sqCls n (p ^ j) s c : ℤ) ≤ (Scls n (p ^ j) s c : ℤ) ^ 2 := by exact_mod_cast this
  linarith

/-- **Large primes.** If `p > 4n` (odd), then `T_p ≤ 0` (all classes are singletons without
`hs` nodes and all valuations vanish). -/
theorem TP_le_zero_of_large (hp2 : p ≠ 2) {n : ℕ} (h4 : 4 * n < p) (K : ℕ) :
    TP p n K ≤ (0 : WithBot ℤ) := by
  have hL : 4 * n < p ^ (0 + 1) := by simpa using h4
  refine Finset.sup_le fun s _ => ?_
  calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
      ≤ (∑ i, ((((s i : ℤ) * Dk p n (nodeOf n i) : ℤ)) : WithBot ℤ)) +
          (((-penalty p n s : ℤ)) : WithBot ℤ) :=
        add_le_add_left (sum_le_sum fun i _ => by
          simpa using fP_le_sharp hp2 hL (nodeOf_mem n i) (s i)) _
    _ = (((∑ i, (s i : ℤ) * Dk p n (nodeOf n i)) - penalty p n s : ℤ) : WithBot ℤ) := by
        rw [← WithBot.coe_sum, ← WithBot.coe_add]; congr 1
    _ ≤ (0 : WithBot ℤ) := by
        rw [← WithBot.coe_zero, WithBot.coe_le_coe]
        have h1 : ∑ i, (s i : ℤ) * Dk p n (nodeOf n i) ≤ 0 :=
          sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (by positivity)
            (Dk_nonpos_of_large hp2 h4 (nodeOf_mem n i))
        have h2 := penalty_nonneg p n s
        linarith

/-- **Large primes.** If `p > 4n` (odd), then `max(T_p, 0) = 0`. -/
theorem TPplus_eq_zero_of_large (hp2 : p ≠ 2) {n : ℕ} (h4 : 4 * n < p) (K : ℕ) :
    TPplus p n K = 0 := by
  unfold TPplus
  rw [max_eq_right (TP_le_zero_of_large hp2 h4 K)]
  rfl

end Hankel2.Fam3
