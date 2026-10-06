import Mathlib
import RequestProject.Zeta7.Hankel2.W3Family3
import RequestProject.Zeta7.Hankel2.W4Jets
import RequestProject.Zeta7.Hankel2.W4Local

/-!
# W4 for family 3: the non-harmonic-sum Gram matrices

`ZETA7_STATUS.md`, round (e) §2 (Lemma W4).  The full node functional of family 3 is
`L(F) = Σ_{k ∈ [-n, 2n]} Σ_{i=1}^{4} w_i(k) r_{k,i}(F)`, where
`r_{k,i}(F) = [u^{-i}] (F W)(-k + u) = Σ_{j ≤ 4-i} F_j(-k) [u^{4-i-j}] H_k(u)` (`resCoef`).
`G_rest` and `G_α` are the matrices `nodeGram ω E` of this shape with `p`-integral weights `ω`
(the `p`-free harmonic sums, resp. the constants `α_i`).

`w4_family3`: for **any** `p`-integral weights `ω`, and the dual Hermite basis `E` of the family-3
conditions (any `E` with the prescribed jets and `p`-integral coefficients), every weighted entry
`p^{r_x + s_y} (nodeGram ω E)[x,y]` has `p`-adic norm `< 1`.

The proof is local: at lone and generic-pair nodes `|[u^m] H_k|_p ≤ p^{1+m}` (`W4Local`); at a
special pair `{s, s ∓ p}` the product `E_x E_y` vanishes at `-s` to order `N = ord_s(x) + ord_s(y)`,
so its jets at both members have `|F_j| ≤ p^{j-N}` (`padicNorm_jet_shift_le`), while
`|[u^m] H_k|_p ≤ p^{4+m}` and `N + r_x + s_y ≥ 12`.
-/

open Polynomial

namespace Hankel2.W3.Fam3

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `r_{k,i}(F) = Σ_{j ≤ 4-i} F_j(-k) [u^{4-i-j}] H_k(u)`, the coefficient of `u^{-i}` in the Laurent
expansion of `F W` at `t = -k`. -/
noncomputable def resCoef (n : ℕ) (F : ℚ[X]) (k : ℤ) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (5 - i), (hasseDeriv j F).eval (-(k : ℚ)) *
    PowerSeries.coeff (4 - i - j) (W2.fam3H n k)

/-- The Gram matrix `Σ_k Σ_{i=1}^4 ω_{k,i} r_{k,i}(E_x E_y)` of the node functional with weights `ω`. -/
noncomputable def nodeGram (n : ℕ) {ι : Type*} (ω : ℤ → ℕ → ℚ) (E : ι → ℚ[X]) :
    Matrix ι ι ℚ := fun x y =>
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (2 * n), ∑ i ∈ Finset.Icc 1 4, ω k i * resCoef n (E x * E y) k i

theorem padicNorm_coeff_mul_le_one (F G : ℚ[X]) (hF : ∀ d, padicNorm p (F.coeff d) ≤ 1)
    (hG : ∀ d, padicNorm p (G.coeff d) ≤ 1) (d : ℕ) : padicNorm p ((F * G).coeff d) ≤ 1 := by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun x _ => ?_) zero_le_one
  rw [padicNorm.mul]
  exact mul_le_one₀ (hF _) (padicNorm.nonneg _) (hG _)

theorem padicNorm_jet_le_one (F : ℚ[X]) (hF : ∀ d, padicNorm p (F.coeff d) ≤ 1) (c : ℤ) (j : ℕ) :
    padicNorm p ((hasseDeriv j F).eval (c : ℚ)) ≤ 1 := by
  conv_lhs => rw [F.as_sum_range' _ (Nat.lt_succ_self _)]
  simp only [map_sum, hasseDeriv_monomial, eval_finset_sum, eval_monomial]
  refine padicNorm.sum_le' (fun d _ => ?_) zero_le_one
  rw [padicNorm.mul, padicNorm.mul, ← Int.cast_pow]
  exact mul_le_one₀ (mul_le_one₀ (padicNorm.of_nat _) (padicNorm.nonneg _) (hF d))
    (padicNorm.nonneg _) (padicNorm.of_int _)

theorem HB_mono {H : PowerSeries ℚ} {e e' : ℤ} (h : W2.HB p H e) (hee : e ≤ e') :
    W2.HB p H e' := fun m =>
  (h m).trans (zpow_le_zpow_right₀ W2.one_lt_p_rat.le (by omega))

/-- Node classes: a node `k ∈ [-n, 2n]` is lone or in a generic pair (`|[u^m] H_k| ≤ p^{1+m}`), or it
is a member of a special pair `{s, s ∓ p}` with `s` a special harmonic-sum node. -/
theorem node_class (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) {k : ℤ}
    (hk : k ∈ Finset.Icc (-(n : ℤ)) (2 * n)) :
    W2.HB p (W2.fam3H n k) 1 ∨
      ∃ s : ℤ, s ∈ hsNodes n p ∧ nodeType n p s = .special ∧
        (s - k = 0 ∨ s - k = p ∨ s - k = -(p : ℤ)) ∧ W2.HB p (W2.fam3H n k) 4 := by
  have h13 := W2.p_ge_13 hn hlow hup
  have hodd := W2.p_odd (p := p) h13
  simp only [Finset.mem_Icc] at hk
  have hspec : ∀ s : ℤ, (s ≤ -(((p : ℤ) + 1) / 2) ∨ (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ s) →
      -(n : ℤ) ≤ s → s ≤ 2 * n → s ∈ hsNodes n p ∧ nodeType n p s = .special := by
    intro s hs1 hs2 hs3
    refine ⟨?_, ?_⟩
    · simp only [hsNodes, Finset.mem_union, Finset.mem_Icc]; omega
    · simp only [nodeType]; rw [if_pos (by omega)]
  by_cases c1 : k ≤ -(((p : ℤ) + 1) / 2)
  · exact Or.inr ⟨k, (hspec k (Or.inl c1) hk.1 (by omega)).1,
      (hspec k (Or.inl c1) hk.1 (by omega)).2, Or.inl (by ring),
      W2.HB_special_left hn hlow hup hk.1 c1⟩
  by_cases c2 : k ≤ n - ((p : ℤ) + 1) / 2
  · left
    by_cases hg : 2 * k = n - p
    · exact HB_mono (W2.HB_gstar_partner hn hlow hup hg) (by norm_num)
    · exact HB_mono (W2.HB_generic_partner hn hlow hup (by omega) c2 hg) (by norm_num)
  by_cases c3 : k ≤ 2 * n - p
  · have hs := hspec (k + p) (Or.inr (by omega)) (by omega) (by omega)
    exact Or.inr ⟨k + p, hs.1, hs.2, Or.inr (Or.inl (by ring)),
      W2.HB_special_right_partner hn hlow hup (by omega) c3⟩
  by_cases c4 : k ≤ (p : ℤ) - n - 1
  · exact Or.inl (HB_mono (W2.HB_lone hn hlow hup (by omega) c4) (by norm_num))
  by_cases c5 : k ≤ (p : ℤ) - ((p : ℤ) + 1) / 2
  · have hs := hspec (k - p) (Or.inl (by omega)) (by omega) (by omega)
    exact Or.inr ⟨k - p, hs.1, hs.2, Or.inr (Or.inr (by ring)),
      W2.HB_special_left_partner hn hlow hup (by omega) c5⟩
  by_cases c6 : k ≤ n + ((p : ℤ) - 1) / 2
  · left
    by_cases hg : 2 * k = n + p
    · exact HB_mono (W2.HB_gstar hn hlow hup hg) (by norm_num)
    · exact HB_mono (W2.HB_generic hn hlow hup (by omega) c6 hg) (by norm_num)
  · have hs := hspec k (Or.inr (by omega)) hk.1 hk.2
    exact Or.inr ⟨k, hs.1, hs.2, Or.inl (by ring),
      W2.HB_special_right hn hlow hup (by omega) hk.2⟩

omit hp in
theorem rowE_ge_two (t : NodeType) {a : ℕ} (ha : a < t.mult) : 2 ≤ t.rowE a := by
  cases t <;> simp only [NodeType.mult, NodeType.rowE] at * <;> omega

omit hp in
theorem colE_ge_three (t : NodeType) {a : ℕ} (ha : a < t.mult) : 3 ≤ t.colE a := by
  cases t <;> simp only [NodeType.mult, NodeType.colE] at * <;> omega

/-- Vanishing order of `E_x` at the special harmonic-sum node `s`. -/
def ord (s : ℤ) (x : Cond (fun k : hsNodes n p => nodeType n p k)) : ℕ :=
  if (x.1 : ℤ) = s then (x.2 : ℕ) else 4

omit hp in
theorem aux_special_bounds (t : NodeType) (ht : t = .special) {a : ℕ} (ha : a < t.mult) :
    6 ≤ (a : ℤ) + t.rowE a ∧ 6 ≤ (a : ℤ) + t.colE a ∧ a < 4 := by
  subst ht; simp only [NodeType.mult, NodeType.rowE, NodeType.colE] at *; omega

omit hp in
theorem ord_add_rowExp {s : ℤ} (hs : nodeType n p s = .special)
    (x : Cond (fun k : hsNodes n p => nodeType n p k)) :
    6 ≤ (ord s x : ℤ) + rowExp (fun k : hsNodes n p => nodeType n p k) x := by
  unfold ord rowExp
  beta_reduce
  have hx2 := x.2.2
  beta_reduce at hx2
  split_ifs with h
  · have ht : nodeType n p (x.1 : ℤ) = .special := by rw [h]; exact hs
    exact (aux_special_bounds _ ht hx2).1
  · have := rowE_ge_two _ hx2; push_cast; omega

omit hp in
theorem ord_add_colExp {s : ℤ} (hs : nodeType n p s = .special)
    (x : Cond (fun k : hsNodes n p => nodeType n p k)) :
    6 ≤ (ord s x : ℤ) + colExp (fun k : hsNodes n p => nodeType n p k) x := by
  unfold ord colExp
  beta_reduce
  have hx2 := x.2.2
  beta_reduce at hx2
  split_ifs with h
  · have ht : nodeType n p (x.1 : ℤ) = .special := by rw [h]; exact hs
    exact (aux_special_bounds _ ht hx2).2.1
  · have := colE_ge_three _ hx2; push_cast; omega

omit hp in
theorem ord_vanish (E : Cond (fun k : hsNodes n p => nodeType n p k) → ℚ[X])
    (hδ : ∀ x (k : hsNodes n p) j (hj : j < (nodeType n p k).mult),
      (hasseDeriv j (E x)).eval (-(k : ℤ) : ℚ) = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    {s : ℤ} (hsm : s ∈ hsNodes n p) (hs : nodeType n p s = .special)
    (x : Cond (fun k : hsNodes n p => nodeType n p k)) :
    ∀ m < ord s x, (hasseDeriv m (E x)).eval (-(s : ℚ)) = 0 := by
  intro m hm
  have hm4 : m < (nodeType n p (⟨s, hsm⟩ : hsNodes n p)).mult := by
    have : ord s x ≤ 4 := by
      unfold ord; split_ifs with h
      · have hx2 := x.2.2
        beta_reduce at hx2
        have ht : nodeType n p (x.1 : ℤ) = .special := by rw [h]; exact hs
        exact (aux_special_bounds _ ht hx2).2.2.le
      · exact le_rfl
    change m < (nodeType n p s).mult
    rw [hs]; simp only [NodeType.mult]; omega
  have := hδ x ⟨s, hsm⟩ m hm4
  rw [if_neg] at this
  · simpa using this
  · intro heq
    unfold ord at hm
    have h1 : (x.1 : ℤ) = s := by rw [heq]
    rw [if_pos h1] at hm
    have h2 : (x.2 : ℕ) = m := by
      have := congrArg (fun z : Cond (fun k : hsNodes n p => nodeType n p k) => (z.2 : ℕ)) heq
      simpa using this
    omega

/-- **Lemma W4 for family 3.**  For the dual Hermite basis `E` of the family-3 conditions (any `E` with
the prescribed jets and `p`-integral coefficients) and **any** `p`-integral weights `ω`, every weighted
entry `p^{r_x + s_y} (nodeGram ω E)[x,y]` of the node Gram matrix has `p`-adic norm `< 1`.  This applies
to `G_rest` (weights: the `p`-free parts of the harmonic sums) and to `G_α` (weights: the constants
`α_i`). -/
theorem w4_family3 (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    (E : Cond (fun k : hsNodes n p => nodeType n p k) → ℚ[X])
    (hδ : ∀ x (k : hsNodes n p) j (hj : j < (nodeType n p k).mult),
      (hasseDeriv j (E x)).eval (-(k : ℤ) : ℚ) = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hcoef : ∀ x d, padicNorm p ((E x).coeff d) ≤ 1)
    (ω : ℤ → ℕ → ℚ) (hω : ∀ k i, padicNorm p (ω k i) ≤ 1)
    (x y : Cond (fun k : hsNodes n p => nodeType n p k)) :
    padicNorm p (weightScale p (rowExp _) (colExp _) (nodeGram n ω E) x y) < 1 := by
  have h1 : (1 : ℚ) < p := W2.one_lt_p_rat
  have hp0 : (0 : ℚ) < p := by linarith
  set z : ℤ := rowExp (fun k : hsNodes n p => nodeType n p k) x +
    colExp (fun k : hsNodes n p => nodeType n p k) y with hz
  have hz5 : 5 ≤ z := NodeType.five_le_rowE_add_colE _ _ x.2.2 y.2.2
  set F := E x * E y with hF
  have hFc : ∀ d, padicNorm p (F.coeff d) ≤ 1 :=
    padicNorm_coeff_mul_le_one _ _ (hcoef x) (hcoef y)
  simp only [weightScale, nodeGram, resCoef, Finset.mul_sum]
  refine padicNorm_sum_lt_one p _ _ fun k hk => padicNorm_sum_lt_one p _ _ fun i hi =>
    padicNorm_sum_lt_one p _ _ fun j hj => ?_
  rw [← hz, ← hF]
  simp only [Finset.mem_Icc] at hi
  simp only [Finset.mem_range] at hj
  rw [padicNorm_zpow_mul, padicNorm.mul, padicNorm.mul]
  have hw0 : (0 : ℚ) < (p : ℚ) ^ (-z) := zpow_pos hp0 _
  have hFj0 := padicNorm.nonneg (p := p) ((hasseDeriv j F).eval (-(k : ℚ)))
  have hH0 := padicNorm.nonneg (p := p) (PowerSeries.coeff (4 - i - j) (W2.fam3H n k))
  -- generic bound: `|ω| ≤ 1`, `|F_j| ≤ p^A`, `|H| ≤ p^B` with `A + B < z`
  have key : ∀ A B : ℤ, A + B < z → padicNorm p ((hasseDeriv j F).eval (-(k : ℚ))) ≤ (p : ℚ) ^ A →
      padicNorm p (PowerSeries.coeff (4 - i - j) (W2.fam3H n k)) ≤ (p : ℚ) ^ B →
      (p : ℚ) ^ (-z) * (padicNorm p (ω k i) * (padicNorm p ((hasseDeriv j F).eval (-(k : ℚ))) *
        padicNorm p (PowerSeries.coeff (4 - i - j) (W2.fam3H n k)))) < 1 := by
    intro A B hAB hA hB
    calc (p : ℚ) ^ (-z) * (padicNorm p (ω k i) * (padicNorm p ((hasseDeriv j F).eval (-(k : ℚ))) *
          padicNorm p (PowerSeries.coeff (4 - i - j) (W2.fam3H n k))))
        ≤ (p : ℚ) ^ (-z) * (1 * ((p : ℚ) ^ A * (p : ℚ) ^ B)) := by
          refine mul_le_mul_of_nonneg_left ?_ hw0.le
          exact mul_le_mul (hω k i) (mul_le_mul hA hB hH0 (zpow_pos hp0 _).le)
            (mul_nonneg hFj0 hH0) zero_le_one
      _ = (p : ℚ) ^ (-z + A + B) := by
          rw [one_mul, ← mul_assoc, ← zpow_add₀ hp0.ne', ← zpow_add₀ hp0.ne']
      _ < 1 := zpow_lt_one_of_neg₀ h1 (by omega)
  have hmle : ((4 - i - j : ℕ) : ℤ) = 4 - i - j := by omega
  rcases node_class hn hlow hup hk with hH | ⟨s, hsm, hs, hsk, hH⟩
  · -- lone node or generic pair
    refine key 0 (1 + ((4 - i - j : ℕ) : ℤ)) (by omega) ?_ (hH _)
    rw [zpow_zero]
    have := padicNorm_jet_le_one F hFc (-k) j
    push_cast at this
    exact this
  · -- special pair `{s, s ∓ p}`
    set N := ord s x + ord s y with hN
    have hNz : 12 ≤ (N : ℤ) + z := by
      have := ord_add_rowExp hs x; have := ord_add_colExp hs y; push_cast [hN]; omega
    have hjet : padicNorm p ((hasseDeriv j F).eval (-(k : ℚ))) ≤ (p : ℚ) ^ ((j : ℤ) - N) := by
      have hpt : -(k : ℚ) = -(s : ℚ) + ((s - k : ℤ) : ℚ) := by push_cast; ring
      rw [hpt]
      refine W3.padicNorm_jet_shift_le F (-(s : ℚ)) ((s - k : ℤ) : ℚ) N j ?_ ?_ ?_
      · intro m
        have := padicNorm_jet_le_one F hFc (-s) m
        push_cast at this
        exact this
      · intro m hm
        exact W3.jet_mul_eq_zero _ _ _ (ord s x) (ord s y) m
          (ord_vanish E hδ hsm hs x) (ord_vanish E hδ hsm hs y) hm
      · rcases hsk with h | h | h
        · rw [h]; simp
        · rw [h]; push_cast; rw [padicNorm.padicNorm_p_of_prime]
        · rw [h]; push_cast; rw [padicNorm.neg, padicNorm.padicNorm_p_of_prime]
    exact key ((j : ℤ) - N) (4 + ((4 - i - j : ℕ) : ℤ)) (by omega) hjet (hH _)

end Hankel2.W3.Fam3
