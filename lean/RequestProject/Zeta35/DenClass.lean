import RequestProject.Zeta35.DenNode

/-!
# Denominators (N, Theorem 5.1), step 4: class values and weak duality for single-level primes

For a single-level prime `ℓ` (`9n < 2ℓ²`) the penalty is the level-one penalty
`∑_c (S_c² − ∑_{k ∈ c} s_k²)` plus non-negative terms, and the node bound `fP_add_sq_le_wnode` gives
for a residue class `c` with `N` nodes, `b ∈ {0, 1}` of them `hs`-free (`3|k| ≤ ℓ`):

  `∑_{k ∈ c} (f_ℓ(k, s_k) + s_k²) − S_c² ≤ V(N, b, S_c)`  (`class_bound`),

`V(N, b, S) = 0` for an `hs`-free singleton (`N = b = 1`), and otherwise
`V(N, b, S) = 4NS + 3 min(S, 4(N − b)) − S²` (`Vt`).  With `ψ(N, b, λ) = max_{0 ≤ S ≤ 4N} (V − λS)`
(`psiT`), weak duality gives

  **`TP_le_psi`**: `T_ℓ ≤ λK + ∑_{c mod ℓ} ψ(N_c, b_c, λ)` for every real `λ`.
-/

open Finset Hankel2

namespace Zeta35.Den

variable {p : ℕ} [hp : Fact p.Prime]

/-- The residue class `c` mod `p`, as a set of node indices. -/
def clsF (p n c : ℕ) : Finset (Fin (2 * R n + 1)) := univ.filter fun i => nodeOf n i % (p : ℤ) = c

/-- `b_c`: the number of `hs`-free nodes (`3|k| ≤ p`) in the class `c` (it is `0` or `1`). -/
def bC (p n c : ℕ) : ℕ := ((clsF p n c).filter fun i => 3 * |nodeOf n i| ≤ (p : ℤ)).card

/-- The class value `V(N, b, S)`. -/
def Vt (N b S : ℕ) : ℤ :=
  if N = 1 ∧ b = 1 then 0 else 4 * N * S + 3 * (min S (4 * (N - b)) : ℕ) - (S : ℤ) ^ 2

/-- `ψ(N, b, λ) = max_{0 ≤ S ≤ 4N} (V(N, b, S) − λ S)`. -/
noncomputable def psiT (N b : ℕ) (lam : ℝ) : ℝ :=
  (range (4 * N + 1)).sup' nonempty_range_add_one fun S => (Vt N b S : ℝ) - lam * S

theorem le_psiT {N b S : ℕ} (hS : S ≤ 4 * N) (lam : ℝ) :
    (Vt N b S : ℝ) - lam * S ≤ psiT N b lam :=
  le_sup' (f := fun S => (Vt N b S : ℝ) - lam * S) (mem_range.2 (by omega))

theorem psiT_nonneg (N b : ℕ) (lam : ℝ) : 0 ≤ psiT N b lam := by
  have := le_psiT (N := N) (b := b) (S := 0) (by omega) lam
  simpa [Vt] using this

omit hp in
theorem card_clsF (n c : ℕ) : (clsF p n c).card = clsN3 n p c := by
  unfold clsF clsN3
  rw [card_filter, card_filter, sum_nodes_eq n (fun m => if m % (p : ℤ) = c then 1 else 0)]

theorem oK3_add_one (n : ℕ) (i : Fin (2 * R n + 1)) :
    oK3 p n (nodeOf n i) + 1 = (clsF p n ((nodeOf n i % (p : ℤ)).toNat)).card := by
  rw [card_clsF]
  exact cntL_add_one3 hp.out.pos (nodeOf_mem_nodes n i)

omit hp in
theorem mem_clsF {n c : ℕ} {i : Fin (2 * R n + 1)} (h : i ∈ clsF p n c) :
    (nodeOf n i % (p : ℤ)).toNat = c := by
  unfold clsF at h
  rw [(mem_filter.1 h).2]; simp

omit hp in
theorem hsI_eq (k : ℤ) : hsI p k = if 3 * |k| ≤ (p : ℤ) then 0 else 1 := by
  unfold hsI; split_ifs <;> omega

theorem bC_le_one (n c : ℕ) : bC p n c ≤ 1 := by
  unfold bC
  rw [card_le_one]
  intro i hi j hj
  simp only [clsF, mem_filter, mem_univ, true_and] at hi hj
  have hdvd : (p : ℤ) ∣ nodeOf n i - nodeOf n j := by
    exact Int.ModEq.dvd (show Int.ModEq p (nodeOf n j) (nodeOf n i) from hj.1.trans hi.1.symm)
  have h2 : |nodeOf n i - nodeOf n j| < p := by
    have := abs_sub (nodeOf n i) (nodeOf n j)
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd h2
  exact nodeOf_injective n (by omega)

omit hp in
theorem Scls_le (n c : ℕ) (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) :
    Scls3 n p s c ≤ 4 * (clsF p n c).card := by
  unfold Scls3
  rw [card_eq_sum_ones, mul_sum]
  exact sum_le_sum fun i _ => by simpa using hs i

/-- **The class bound.** -/
theorem class_bound (n c : ℕ) (s : Fin (2 * R n + 1) → ℕ) (hs : ∀ i, s i ≤ 4) :
    (∑ i ∈ clsF p n c, wnode (oK3 p n (nodeOf n i)) (hsI p (nodeOf n i)) (s i)) -
      (Scls3 n p s c : ℤ) ^ 2 ≤ Vt (clsF p n c).card (bC p n c) (Scls3 n p s c) := by
  set N := (clsF p n c).card with hN
  set b := bC p n c with hb
  have hSdef : Scls3 n p s c = ∑ i ∈ clsF p n c, s i := rfl
  have ho : ∀ i ∈ clsF p n c, oK3 p n (nodeOf n i) + 1 = N := by
    intro i hi; rw [oK3_add_one, mem_clsF hi]
  by_cases h11 : N = 1 ∧ b = 1
  · -- an `hs`-free singleton
    obtain ⟨i0, hi0⟩ := card_eq_one.1 h11.1
    have hfree : (clsF p n c).filter (fun i => 3 * |nodeOf n i| ≤ (p : ℤ)) = clsF p n c := by
      have h1 : ((clsF p n c).filter (fun i => 3 * |nodeOf n i| ≤ (p : ℤ))).card = 1 := h11.2
      exact eq_of_subset_of_card_le (filter_subset _ _) (by rw [h1, ← hN, h11.1])
    have hi0m : i0 ∈ clsF p n c := by rw [hi0]; exact mem_singleton_self _
    have h3 : 3 * |nodeOf n i0| ≤ (p : ℤ) := by
      rw [← hfree] at hi0m; exact (mem_filter.1 hi0m).2
    have ho0 : oK3 p n (nodeOf n i0) = 0 := by have := ho i0 hi0m; omega
    have hs0 : hsI p (nodeOf n i0) = 0 := by rw [hsI_eq, if_pos h3]
    rw [hSdef, hi0, sum_singleton, sum_singleton, ho0, hs0]
    unfold Vt wnode
    rw [if_pos ⟨rfl, rfl⟩, if_pos h11]
    simp
  · -- every node has `w = s (4N + 3 hs)`
    have hw : ∀ i ∈ clsF p n c, wnode (oK3 p n (nodeOf n i)) (hsI p (nodeOf n i)) (s i) =
        (s i : ℤ) * (4 * N + 3 * hsI p (nodeOf n i)) := by
      intro i hi
      have hoi := ho i hi
      unfold wnode
      split_ifs with h
      · -- `o = 0`, `hs = 0`: then `N = 1` and `b = 1`, a contradiction
        exfalso
        apply h11
        refine ⟨by omega, ?_⟩
        have hN1 : N = 1 := by omega
        have h3 : 3 * |nodeOf n i| ≤ (p : ℤ) := by
          have := h.2; rw [hsI_eq] at this; split_ifs at this with h'
          exact h'
        have : 1 ≤ b := by
          rw [hb, bC]; exact card_pos.2 ⟨i, mem_filter.2 ⟨hi, h3⟩⟩
        have := bC_le_one (p := p) n c
        omega
      · rw [show ((oK3 p n (nodeOf n i) : ℕ) : ℤ) = (N : ℤ) - 1 by omega]
        ring
    rw [sum_congr rfl hw]
    have hsplit : ∑ i ∈ clsF p n c, (s i : ℤ) * (4 * N + 3 * hsI p (nodeOf n i)) =
        4 * N * Scls3 n p s c + 3 * ∑ i ∈ clsF p n c, (s i : ℤ) * hsI p (nodeOf n i) := by
      rw [hSdef]; push_cast
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => by ring
    rw [hsplit]
    -- the `hs` part
    have hhs1 : ∑ i ∈ clsF p n c, (s i : ℤ) * hsI p (nodeOf n i) ≤ Scls3 n p s c := by
      rw [hSdef]; push_cast
      refine sum_le_sum fun i _ => ?_
      have := hsI_le_one (p := p) (k := nodeOf n i)
      have : (0 : ℤ) ≤ s i := by positivity
      have h' : ((hsI p (nodeOf n i) : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hsI_le_one
      nlinarith
    have hhs2 : ∑ i ∈ clsF p n c, (s i : ℤ) * hsI p (nodeOf n i) ≤ 4 * ((N - b : ℕ) : ℤ) := by
      have hcount : ((clsF p n c).filter (fun i => ¬ 3 * |nodeOf n i| ≤ (p : ℤ))).card = N - b := by
        have := card_filter_add_card_filter_not (s := clsF p n c)
          (fun i => 3 * |nodeOf n i| ≤ (p : ℤ))
        rw [← hN] at this
        rw [hb, bC]; omega
      calc ∑ i ∈ clsF p n c, (s i : ℤ) * hsI p (nodeOf n i)
          = ∑ i ∈ (clsF p n c).filter (fun i => ¬ 3 * |nodeOf n i| ≤ (p : ℤ)), (s i : ℤ) := by
            rw [sum_filter]
            refine sum_congr rfl fun i _ => ?_
            rw [hsI_eq]; split_ifs <;> simp
        _ ≤ ∑ i ∈ (clsF p n c).filter (fun i => ¬ 3 * |nodeOf n i| ≤ (p : ℤ)), (4 : ℤ) :=
            sum_le_sum fun i _ => by exact_mod_cast hs i
        _ = 4 * ((N - b : ℕ) : ℤ) := by rw [sum_const, hcount, nsmul_eq_mul]; ring
    unfold Vt
    rw [if_neg h11]
    have hmin : ∑ i ∈ clsF p n c, (s i : ℤ) * hsI p (nodeOf n i) ≤
        ((min (Scls3 n p s c) (4 * (N - b)) : ℕ) : ℤ) := by
      rcases le_total (Scls3 n p s c) (4 * (N - b)) with h | h
      · rw [min_eq_left h]; exact hhs1
      · rw [min_eq_right h]; push_cast at hhs2 ⊢; exact hhs2
    linarith

omit hp in
/-- The level-one penalty is the sum over the classes of `S_c² − ∑_{k ∈ c} s_k²`. -/
theorem penalty_ge_penL (n : ℕ) (s : Fin (2 * R n + 1) → ℕ) : penL3 n p s ≤ penalty p n s := by
  rw [penalty_eq_sum_penL3, ← add_sum_erase _ _ (mem_Icc.2 ⟨le_rfl, by omega⟩), pow_one]
  have := sum_nonneg fun j (_ : j ∈ (Icc 1 (2 * R n + 1)).erase 1) =>
    penL_nonneg3 (n := n) (q := p ^ j) s
  linarith

/-- **Weak duality for a single-level prime**: `T_p ≤ λK + ∑_{c mod p} ψ(N_c, b_c, λ)`. -/
theorem TP_le_psi {n : ℕ} (h9 : 9 * n < 2 * p ^ 2) (K : ℕ) (lam : ℝ) :
    ∀ t : ℤ, TP p n K = (t : WithBot ℤ) →
      (t : ℝ) ≤ lam * K + ∑ c ∈ range p, psiT (clsF p n c).card (bC p n c) lam := by
  have hp0 := hp.out.pos
  set B : ℝ := lam * K + ∑ c ∈ range p, psiT (clsF p n c).card (bC p n c) lam
  have key : TP p n K ≤ ((⌊B⌋ : ℤ) : WithBot ℤ) := by
    refine Finset.sup_le fun s hs => ?_
    obtain ⟨hs4, hK⟩ := mem_profiles_iff3.1 hs
    set w : Fin (2 * R n + 1) → ℤ := fun i => wnode (oK3 p n (nodeOf n i)) (hsI p (nodeOf n i)) (s i)
    have h1 : (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ) ≤
        (((∑ i, (w i - (s i : ℤ) ^ 2)) - penalty p n s : ℤ) : WithBot ℤ) := by
      have : ∀ i, fP p n (nodeOf n i) (s i) ≤ (((w i - (s i : ℤ) ^ 2) : ℤ) : WithBot ℤ) := by
        intro i
        have h := fP_add_sq_le_wnode h9 (nodeOf_mem_nodes n i) (s i)
        induction hf : fP p n (nodeOf n i) (s i) with
        | bot => exact bot_le
        | coe a =>
          rw [hf] at h
          rw [← WithBot.coe_add, WithBot.coe_le_coe] at h
          exact WithBot.coe_le_coe.2 (by simp only [w]; linarith)
      calc (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)
          ≤ (∑ i, ((((w i - (s i : ℤ) ^ 2) : ℤ)) : WithBot ℤ)) +
              (((-penalty p n s : ℤ)) : WithBot ℤ) := add_le_add_left (sum_le_sum fun i _ => this i) _
        _ = _ := by rw [← WithBot.coe_sum, ← WithBot.coe_add]; congr 1
    refine h1.trans (WithBot.coe_le_coe.2 (Int.le_floor.2 ?_))
    -- regroup by classes
    have hfib : ∀ g : Fin (2 * R n + 1) → ℤ, ∑ i, g i = ∑ c ∈ range p, ∑ i ∈ clsF p n c, g i := by
      intro g
      rw [← sum_fiberwise_of_maps_to (g := fun i => (nodeOf n i % (p : ℤ)).toNat) (t := range p)
        (fun i _ => Fam3.toNat_emod_mem_range hp0 _)]
      refine sum_congr rfl fun c _ => ?_
      refine sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [clsF, mem_filter, mem_univ, true_and]
      exact Fam3.toNat_emod_eq_iff (by exact_mod_cast hp0) _ _
    have hpen := penalty_ge_penL (p := p) n s
    have hsq : ∑ i, (s i : ℤ) ^ 2 = ∑ c ∈ range p, (sqCls3 n p s c : ℤ) := by
      rw [hfib]; refine sum_congr rfl fun c _ => ?_; unfold sqCls3 clsF; push_cast; rfl
    have hval : (∑ i, (w i - (s i : ℤ) ^ 2)) - penL3 n p s =
        ∑ c ∈ range p, ((∑ i ∈ clsF p n c, w i) - (Scls3 n p s c : ℤ) ^ 2) := by
      rw [sum_sub_distrib, hsq, penL3, hfib w, ← sum_sub_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun c _ => by ring
    have hcls : ∀ c ∈ range p, (((∑ i ∈ clsF p n c, w i) - (Scls3 n p s c : ℤ) ^ 2 : ℤ) : ℝ) ≤
        psiT (clsF p n c).card (bC p n c) lam + lam * Scls3 n p s c := by
      intro c _
      have h := class_bound (p := p) n c s hs4
      have h2 := le_psiT (N := (clsF p n c).card) (b := bC p n c) (Scls_le n c s hs4) lam
      have h' : (((∑ i ∈ clsF p n c, w i) - (Scls3 n p s c : ℤ) ^ 2 : ℤ) : ℝ) ≤
          (Vt (clsF p n c).card (bC p n c) (Scls3 n p s c) : ℝ) := by exact_mod_cast h
      linarith
    have hSK : ∑ c ∈ range p, (Scls3 n p s c : ℝ) = K := by
      rw [sum_Scls3 hp0 s]; exact_mod_cast hK
    have hsum := sum_le_sum hcls
    rw [sum_add_distrib, ← mul_sum, hSK] at hsum
    have hpen' : (∑ i, (w i - (s i : ℤ) ^ 2)) - penalty p n s ≤
        (∑ i, (w i - (s i : ℤ) ^ 2)) - penL3 n p s := by linarith
    calc ((((∑ i, (w i - (s i : ℤ) ^ 2)) - penalty p n s : ℤ)) : ℝ)
        ≤ (((∑ i, (w i - (s i : ℤ) ^ 2)) - penL3 n p s : ℤ) : ℝ) := by exact_mod_cast hpen'
      _ = ∑ c ∈ range p, (((∑ i ∈ clsF p n c, w i) - (Scls3 n p s c : ℤ) ^ 2 : ℤ) : ℝ) := by
        rw [hval, Int.cast_sum]
      _ ≤ B := by simp only [B]; linarith [hsum]
  intro t ht
  rw [ht, WithBot.coe_le_coe] at key
  exact (Int.cast_le.2 key).trans (Int.floor_le _)

end Zeta35.Den
