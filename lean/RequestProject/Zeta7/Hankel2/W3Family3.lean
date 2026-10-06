import Mathlib
import RequestProject.Zeta7.Hankel2.W3Gram
import RequestProject.Zeta7.Hankel2.W2Local
import RequestProject.Zeta7.Hankel2.HermiteBasis

/-!
# W1 + W2 + W3 for family 3: the harmonic-sum Gram matrix at a prime `p ∈ [(7n+2)/4, 2n-1]`

`ZETA7_STATUS.md`, rounds (e), (g), (h) and (i).

* `exists_dual_hermite_basis` (W1, rational form): for integer nodes pairwise distinct mod `p` and any
  multiplicities, the dual Hermite basis `E` exists over `ℚ`, its coefficients and all its jets at the
  nodes are `p`-integral, and its prescribed jets are `δ`.
* `Fam3.hsNodes`, `Fam3.nodeType`, `Fam3.hsC`: the harmonic-sum nodes of family 3 at `p`, their types
  (special / generic / `g*`), and the `p`-parts of their constants (`W2.hsConst`).
* `Fam3.nodeHyp` (W2 ⟹ the hypotheses of W3), `Fam3.hsNodes_injective_mod` (node combinatorics).
* `Fam3.w3_family3` (**W1 + W2 + W3**): for odd `n` and a prime `p` with `7n + 2 ≤ 4p`, `p + 1 ≤ 2n`,
  the dual Hermite basis `E` of the family-3 conditions (jets `0..3` at special nodes, `0,1` at generic
  nodes, `0` at `g*`, nodes `t = -k`) exists, and the harmonic-sum Gram matrix
  `G_HS[x,y] = L_HS(E_x E_y)` has `p`-integral weighted entries `p^{r_x+s_y} G_HS[x,y]` and weighted
  determinant of `p`-adic norm `1`.
-/

open Polynomial Matrix

namespace Hankel2.W3

section DualBasis

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **W1, rational form.**  Integer nodes `ν i`, pairwise distinct mod `p`, multiplicities `m i`: the dual
Hermite basis `E` exists over `ℚ`; its prescribed jets are `δ`, and its coefficients and all its jets at
the nodes are `p`-integral. -/
theorem exists_dual_hermite_basis (ν : ι → ℤ) (hν : Function.Injective (fun i => (ν i : ZMod p)))
    (m : ι → ℕ) :
    ∃ E : (Σ i, Fin (m i)) → ℚ[X],
      (∀ x i j (hj : j < m i),
        (hasseDeriv j (E x)).eval (ν i : ℚ) = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0) ∧
      (∀ x d, padicNorm p ((E x).coeff d) ≤ 1) ∧
      (∀ x d, Fintype.card (Σ i, Fin (m i)) ≤ d → (E x).coeff d = 0) ∧
      (∀ x i j, padicNorm p ((hasseDeriv j (E x)).eval (ν i : ℚ)) ≤ 1) := by
  classical
  set e := Fintype.equivFin (Σ i, Fin (m i))
  set VZ := confluentVandermonde m ν e
  set V : Matrix _ _ ℚ := confluentVandermonde m (fun i => (ν i : ℚ)) e with hV
  have hVmap : V = (Int.castRingHom ℚ).mapMatrix VZ := by
    rw [RingHom.mapMatrix_apply, map_confluentVandermonde]; rfl
  have hdetZ : ¬ (p : ℤ) ∣ VZ.det := not_dvd_det_confluentVandermonde_int m ν hν e
  have hdet : V.det = (VZ.det : ℚ) := by
    rw [hVmap, ← RingHom.map_det]; rfl
  have hdetnorm : padicNorm p V.det = 1 := by
    rw [hdet]; exact (padicNorm.int_eq_one_iff _).2 hdetZ
  have hdet0 : V.det ≠ 0 := fun h => by simp [h] at hdetnorm
  set W := V⁻¹ with hWdef
  have hW : ∀ c x, padicNorm p (W c x) ≤ 1 := by
    intro c x
    have hadj : V.adjugate = (Int.castRingHom ℚ).mapMatrix VZ.adjugate := by
      rw [hVmap, RingHom.map_adjugate]
    rw [hWdef, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, padicNorm.mul, Ring.inverse_eq_inv',
      W2.padicNorm_inv (p := p), hdetnorm, inv_one, one_mul, hadj]
    exact padicNorm.of_int _
  have hVW : V * W = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.mpr hdet0)
  refine ⟨fun x => ∑ c, monomial (e c : ℕ) (W c x), ?_, ?_, ?_, ?_⟩
  · intro x i j hj
    have h1 := confluentVandermonde_mulVec m (fun i => (ν i : ℚ)) e (fun c => W c x) ⟨i, ⟨j, hj⟩⟩
    rw [← hV] at h1
    simp only at h1
    rw [← h1]
    have h2 : (V *ᵥ fun c => W c x) ⟨i, ⟨j, hj⟩⟩ = (V * W) ⟨i, ⟨j, hj⟩⟩ x := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h2, hVW, Matrix.one_apply]
    simp only [eq_comm]
  · intro x d
    rw [finset_sum_coeff]
    refine padicNorm.sum_le' (fun c _ => ?_) zero_le_one
    rw [coeff_monomial]
    split_ifs
    · exact hW c x
    · simp
  · intro x d hd
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [coeff_monomial, if_neg]
    have := (e c).2
    omega
  · intro x i j
    simp only [map_sum, hasseDeriv_monomial, eval_finset_sum, eval_monomial]
    refine padicNorm.sum_le' (fun c _ => ?_) zero_le_one
    rw [padicNorm.mul, padicNorm.mul]
    have h1 : padicNorm p (((e c : ℕ).choose j : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
    have h2 : padicNorm p ((ν i : ℚ) ^ ((e c : ℕ) - j)) ≤ 1 := by
      rw [← Int.cast_pow]; exact padicNorm.of_int _
    exact mul_le_one₀ (mul_le_one₀ h1 (padicNorm.nonneg _) (hW c x)) (padicNorm.nonneg _) h2

end DualBasis

namespace Fam3

variable (n p : ℕ)

/-- The harmonic-sum nodes of family 3 at the prime `p`: right `k ∈ [(p+1)/2, 2n]` and left
`k ∈ [-n, -(p+1)/2]` (the node itself is `t = -k`). -/
def hsNodes : Finset ℤ :=
  Finset.Icc (((p : ℤ) + 1) / 2) (2 * n) ∪ Finset.Icc (-(n : ℤ)) (-(((p : ℤ) + 1) / 2))

/-- The type of the harmonic-sum node `k`: special (left nodes and right `k ≥ n + (p+1)/2`), `g*`
(`2k = n + p`), generic (the other right nodes). -/
def nodeType (k : ℤ) : NodeType :=
  if k < 0 ∨ (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ k then .special
  else if 2 * k = n + p then .gstar else .generic

/-- The `p`-part of the constants of the functional at the harmonic-sum node `k` (`W2.hsConst`, with
pole parameter `q = p` at right nodes and `q = -p`, with an overall sign, at left nodes). -/
noncomputable def hsC (k : ℤ) (j : ℕ) : ℚ :=
  if 0 < k then W2.hsConst p (W2.fam3H n k) j else -W2.hsConst (-(p : ℚ)) (W2.fam3H n k) j

variable {n p} [hp : Fact p.Prime]

omit hp in
theorem pow_eq_zpow (m : ℕ) : (p : ℚ) ^ m = (p : ℚ) ^ (m : ℤ) := (zpow_natCast _ _).symm

omit hp in
theorem specialHyp (c : ℕ → ℚ) (h : ∀ a ≤ 3, padicNorm p (c a) = (p : ℚ) ^ (12 - a)) :
    NodeHyp p .special c where
  small j hj hj3 := by simp only [NodeType.mult] at hj; omega
  lead a b ha hb hab := by
    rw [h _ hab, pow_eq_zpow]
    apply le_of_eq
    congr 1
    simp only [NodeType.rowE, NodeType.colE]
    omega
  unit := by
    change padicNorm p (c 3) = (p : ℚ) ^ (9 : ℤ)
    rw [h 3 le_rfl, pow_eq_zpow]; rfl

theorem genericHyp (c : ℕ → ℚ) (h0 : padicNorm p (c 0) ≤ (p : ℚ) ^ 5)
    (h1 : padicNorm p (c 1) = (p : ℚ) ^ 5) (h2 : padicNorm p (c 2) = (p : ℚ) ^ 4)
    (h3 : padicNorm p (c 3) = (p : ℚ) ^ 3) : NodeHyp p .generic c where
  small j hj hj3 := by
    have h1p : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    simp only [NodeType.mult] at hj
    interval_cases j
    · rw [h2, pow_eq_zpow]; rfl
    · rw [h3, pow_eq_zpow]; exact zpow_le_zpow_right₀ h1p (by norm_num)
  lead a b ha hb hab := by
    have h1p : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    simp only [NodeType.mult, NodeType.rowE, NodeType.colE] at ha hb ⊢
    have h5 : (p : ℚ) ^ 5 = (p : ℚ) ^ ((2 : ℤ) + 3) := by rw [pow_eq_zpow]; rfl
    interval_cases a <;> interval_cases b
    · rw [← h5]; exact h0
    · rw [← h5]; exact h1.le
    · rw [← h5]; exact h1.le
    · rw [← h5]; simp only [Nat.reduceAdd]; rw [h2]; exact pow_le_pow_right₀ h1p (by norm_num)
  unit := by
    change padicNorm p (c 1) = (p : ℚ) ^ (5 : ℤ)
    rw [h1, pow_eq_zpow]; rfl

theorem gstarHyp (c : ℕ → ℚ) (h0 : padicNorm p (c 0) = (p : ℚ) ^ 5)
    (h1 : padicNorm p (c 1) = (p : ℚ) ^ 4) (h2 : padicNorm p (c 2) ≤ (p : ℚ) ^ 2)
    (h3 : padicNorm p (c 3) = (p : ℚ) ^ 2) : NodeHyp p .gstar c where
  small j hj hj3 := by
    have h1p : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    simp only [NodeType.mult] at hj
    have h4 : (p : ℚ) ^ (4 : ℤ) = (p : ℚ) ^ 4 := by rw [pow_eq_zpow]; rfl
    rw [h4]
    interval_cases j
    · rw [h1]
    · exact h2.trans (pow_le_pow_right₀ h1p (by norm_num))
    · rw [h3]; exact pow_le_pow_right₀ h1p (by norm_num)
  lead a b ha hb hab := by
    simp only [NodeType.mult, NodeType.rowE, NodeType.colE] at ha hb ⊢
    interval_cases a; interval_cases b
    rw [h0, pow_eq_zpow]; rfl
  unit := by
    change padicNorm p (c 0) = (p : ℚ) ^ (5 : ℤ)
    rw [h0, pow_eq_zpow]; rfl

/-- **W2 ⟹ the local hypotheses of W3**, at every harmonic-sum node. -/
theorem nodeHyp (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) {k : ℤ}
    (hk : k ∈ hsNodes n p) : NodeHyp p (nodeType n p k) (hsC n p k) := by
  have h13 := W2.p_ge_13 hn hlow hup
  have hodd := W2.p_odd (p := p) h13
  simp only [hsNodes, Finset.mem_union, Finset.mem_Icc] at hk
  rcases hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
  · have hpos : 0 < k := by omega
    have hc : hsC n p k = fun j => W2.hsConst p (W2.fam3H n k) j := by
      funext j; simp [hsC, hpos]
    rw [hc]
    by_cases hsp : (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ k
    · have ht : nodeType n p k = .special := by simp [nodeType, hsp]
      rw [ht]
      exact specialHyp _ fun a ha => W2.w2_special_right hn hlow hup hsp hk2 ha
    · by_cases hg : 2 * k = n + p
      · have ht : nodeType n p k = .gstar := by
          simp [nodeType, hsp, hg, show ¬ k < 0 by omega]
        rw [ht]
        obtain ⟨h0, h1, h2, h3⟩ := W2.w2_gstar hn hlow hup hg
        exact gstarHyp _ h0 h1 h2 h3
      · have ht : nodeType n p k = .generic := by
          simp [nodeType, hsp, hg, show ¬ k < 0 by omega]
        rw [ht]
        obtain ⟨h0, h1, h2, h3⟩ := W2.w2_generic hn hlow hup hk1 (by omega) hg
        exact genericHyp _ h0 h1 h2 h3
  · have hneg : k < 0 := by omega
    have hc : hsC n p k = fun j => -W2.hsConst (-(p : ℚ)) (W2.fam3H n k) j := by
      funext j; simp [hsC, show ¬ 0 < k by omega]
    have ht : nodeType n p k = .special := by simp [nodeType, hneg]
    rw [hc, ht]
    exact specialHyp _ fun a ha => by
      rw [padicNorm.neg]; exact W2.w2_special_left hn hlow hup hk1 hk2 ha

/-- The harmonic-sum nodes are pairwise incongruent mod `p`. -/
theorem hsNodes_injective_mod (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    Function.Injective (fun k : hsNodes n p => ((-(k : ℤ) : ℤ) : ZMod p)) := by
  rintro ⟨k1, hk1⟩ ⟨k2, hk2⟩ h
  simp only at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  simp only [hsNodes, Finset.mem_union, Finset.mem_Icc] at hk1 hk2
  have hP : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
  have hb1 : -(2 * (p : ℤ)) < (p : ℤ) * m := by rw [← hm]; omega
  have hb2 : (p : ℤ) * m < 2 * p := by rw [← hm]; omega
  have hm1 : -2 < m := by nlinarith
  have hm2 : m < 2 := by nlinarith
  apply Subtype.ext
  simp only
  interval_cases m <;> omega

/-- **W1 + W2 + W3 for family 3.**  Let `n` be odd and `p` a prime with `7n + 2 ≤ 4p` and
`p + 1 ≤ 2n`.  Impose jets `0..3` at the special harmonic-sum nodes, jets `0, 1` at the generic ones
and jet `0` at `g*` (nodes `t = -k`).  Then the dual Hermite basis `E` exists, with `p`-integral
coefficients, and the harmonic-sum Gram matrix `G_HS[x,y] = L_HS(E_x E_y)`,
`L_HS(F) = Σ_k Σ_{j ≤ 3} c_{k,j} F_j(-k)` with `c_{k,j}` the `p`-parts of W2, has `p`-integral weighted
entries `p^{r_x+s_y} G_HS[x,y]` and weighted determinant of `p`-adic norm `1`, i.e.
`v_p det G_HS = -Σ_x (r_x + s_x)`. -/
theorem w3_family3 (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    ∃ E : Cond (fun k : hsNodes n p => nodeType n p k) → ℚ[X],
      (∀ x (k : hsNodes n p) j (hj : j < (nodeType n p k).mult),
        (hasseDeriv j (E x)).eval (-(k : ℤ) : ℚ) = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0) ∧
      (∀ x d, padicNorm p ((E x).coeff d) ≤ 1) ∧
      (∀ x d, Fintype.card (Cond (fun k : hsNodes n p => nodeType n p k)) ≤ d → (E x).coeff d = 0) ∧
      let G : Matrix _ _ ℚ := fun x y =>
        functionalHS (fun k : hsNodes n p => hsC n p k) (fun k => (-(k : ℤ) : ℚ)) (E x * E y)
      (∀ x y, padicNorm p (weightScale p (rowExp _) (colExp _) G x y) ≤ 1) ∧
      padicNorm p (weightScale p (rowExp _) (colExp _) G).det = 1 := by
  obtain ⟨E, hδ, hcoef, hdeg, hint⟩ := exists_dual_hermite_basis (p := p) (ι := hsNodes n p)
    (fun k => -(k : ℤ)) (hsNodes_injective_mod hlow hup) (fun k => (nodeType n p k).mult)
  refine ⟨E, fun x k j hj => by exact_mod_cast hδ x k j hj, hcoef, hdeg, ?_⟩
  intro G
  have hG : G = gram (fun k : hsNodes n p => hsC n p k)
      (fun x k j => (hasseDeriv j (E x)).eval (((-(k : ℤ)) : ℤ) : ℚ)) := by
    ext x y
    rw [gram_eq_functional]
    simp only [G, functionalHS]
    push_cast
    rfl
  rw [hG]
  exact w3_gram (fun k : hsNodes n p => hsC n p k) (fun k => nodeHyp hn hlow hup k.2) _
    (fun x k j hj => hδ x k j hj) (fun x k j => hint x k j)

/-! ### Counting: `K = 10n + 3 - 4p` conditions and `v_p det G_HS = -(82n - 36p + 31)` -/

/-- `Σ_{a < mult} (r_a + s_a)` for a node of the given type (`= 2 Σ ℓ` over its conditions). -/
def typeWeight : NodeType → ℤ
  | .special => 36
  | .generic => 10
  | .gstar => 5

omit hp in
theorem sum_weights (t : NodeType) :
    ∑ a : Fin t.mult, (t.rowE a + t.colE a) = typeWeight t := by
  cases t
  · show ∑ a : Fin 4, (NodeType.special.rowE a + NodeType.special.colE a) = 36
    simp [Fin.sum_univ_succ, NodeType.rowE, NodeType.colE]
  · show ∑ a : Fin 2, (NodeType.generic.rowE a + NodeType.generic.colE a) = 10
    simp [NodeType.rowE, NodeType.colE]
  · show ∑ a : Fin 1, (NodeType.gstar.rowE a + NodeType.gstar.colE a) = 5
    simp [NodeType.rowE, NodeType.colE]

omit hp in
/-- The harmonic-sum node set, split into the left nodes, the right special nodes and the right
generic nodes (including `g*`). -/
theorem hsNodes_eq (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    hsNodes n p = Finset.Icc (-(n : ℤ)) (-(((p : ℤ) + 1) / 2)) ∪
      (Finset.Icc ((n : ℤ) + ((p : ℤ) + 1) / 2) (2 * n) ∪
        Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1)) := by
  ext k; simp only [hsNodes, Finset.mem_union, Finset.mem_Icc]; omega

omit hp in
/-- Sum of a function of the node type over the harmonic-sum nodes, for odd `n` and odd `p` in the
window: `(2n - p + 1)` special nodes, `n - 1` generic nodes and one `g*`. -/
theorem sum_nodeType (hn : n % 2 = 1) (hodd : p % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p)
    (hup : p + 1 ≤ 2 * n) (f : NodeType → ℤ) :
    ∑ k ∈ hsNodes n p, f (nodeType n p k) =
      (2 * n - p + 1) * f .special + (n - 1) * f .generic + f .gstar := by
  have hd2 : Disjoint (Finset.Icc ((n : ℤ) + ((p : ℤ) + 1) / 2) (2 * n))
      (Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1)) := by
    rw [Finset.disjoint_left]; intro k; simp only [Finset.mem_Icc]; omega
  have hd1 : Disjoint (Finset.Icc (-(n : ℤ)) (-(((p : ℤ) + 1) / 2)))
      (Finset.Icc ((n : ℤ) + ((p : ℤ) + 1) / 2) (2 * n) ∪
        Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1)) := by
    rw [Finset.disjoint_left]; intro k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [hsNodes_eq hlow hup, Finset.sum_union hd1, Finset.sum_union hd2]
  have h1 : ∑ k ∈ Finset.Icc (-(n : ℤ)) (-(((p : ℤ) + 1) / 2)), f (nodeType n p k) =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) (-(((p : ℤ) + 1) / 2)), f .special := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    simp only [nodeType, show k < 0 by omega, true_or, if_true]
  have h2 : ∑ k ∈ Finset.Icc ((n : ℤ) + ((p : ℤ) + 1) / 2) (2 * n), f (nodeType n p k) =
      ∑ k ∈ Finset.Icc ((n : ℤ) + ((p : ℤ) + 1) / 2) (2 * n), f .special := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    simp only [nodeType, hk.1, or_true, if_true]
  have h3 : ∑ k ∈ Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1),
      f (nodeType n p k) =
      ∑ k ∈ Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1),
        (if 2 * k = n + p then f .gstar else f .generic) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    simp only [nodeType, show ¬ (k < 0 ∨ (n : ℤ) + ((p : ℤ) + 1) / 2 ≤ k) by omega, if_false]
    split_ifs <;> rfl
  rw [h1, h2, h3, Finset.sum_const, Finset.sum_const, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const]
  have hfilt : (Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1)).filter
      (fun k : ℤ => 2 * k = (n : ℤ) + p) = ({((n : ℤ) + p) / 2} : Finset ℤ) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1))
    (fun k => 2 * k = (n : ℤ) + p)
  rw [hfilt, Finset.card_singleton, Int.card_Icc] at hcard
  rw [hfilt, Finset.card_singleton, Int.card_Icc, Int.card_Icc]
  have hc : ((Finset.filter (fun k : ℤ => ¬2 * k = (n : ℤ) + p)
      (Finset.Icc (((p : ℤ) + 1) / 2) ((n : ℤ) + ((p : ℤ) + 1) / 2 - 1))).card : ℤ) = n - 1 := by
    omega
  simp only [nsmul_eq_mul, hc]
  push_cast
  have e1 : (((-(((p : ℤ) + 1) / 2) + 1 - -(n : ℤ)).toNat : ℕ) : ℤ) = n - (p - 1) / 2 := by omega
  have e2 : (((2 * (n : ℤ) + 1 - ((n : ℤ) + ((p : ℤ) + 1) / 2)).toNat : ℕ) : ℤ) = n - (p - 1) / 2 := by
    omega
  rw [e1, e2]
  have e3 : ((p : ℤ) - 1) / 2 * 2 = p - 1 := by omega
  linear_combination (-(f NodeType.special)) * e3

omit hp in
/-- The number of Hermite conditions is `K = 10n + 3 - 4p`. -/
theorem card_cond (hn : n % 2 = 1) (hodd : p % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p)
    (hup : p + 1 ≤ 2 * n) :
    (Fintype.card (Cond (fun k : hsNodes n p => nodeType n p k)) : ℤ) = 10 * n + 3 - 4 * p := by
  rw [Fintype.card_sigma]
  push_cast
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort (hsNodes n p) (fun k => ((nodeType n p k).mult : ℤ))]
  rw [sum_nodeType hn hodd hlow hup (fun t => (t.mult : ℤ))]
  simp only [NodeType.mult]
  push_cast
  ring

omit hp in
/-- `Σ_x (r_x + s_x) = 2 Σ ℓ = 82n - 36p + 31`. -/
theorem sum_exps (hn : n % 2 = 1) (hodd : p % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p)
    (hup : p + 1 ≤ 2 * n) :
    ∑ x : Cond (fun k : hsNodes n p => nodeType n p k),
      (rowExp (fun k : hsNodes n p => nodeType n p k) x +
        colExp (fun k : hsNodes n p => nodeType n p k) x) = 82 * n - 36 * p + 31 := by
  rw [Fintype.sum_sigma]
  simp only [rowExp, colExp, sum_weights]
  rw [Finset.sum_coe_sort (hsNodes n p) (fun k => typeWeight (nodeType n p k))]
  rw [sum_nodeType hn hodd hlow hup typeWeight]
  simp only [typeWeight]
  ring

omit hp in
theorem prod_zpow_eq {α : Type*} (s : Finset α) (q : ℚ) (hq : q ≠ 0) (f : α → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

/-- **`v_p(det G_HS) = -(82n - 36p + 31)` for family 3.**  With the dual Hermite basis `E` of the
family-3 conditions and the harmonic-sum Gram matrix `G_HS[x,y] = L_HS(E_x E_y)`,
`|det G_HS|_p = p^{82n - 36p + 31}` exactly (for odd `n`, prime `p`, `7n + 2 ≤ 4p`, `p + 1 ≤ 2n`). -/
theorem padicNorm_det_gramHS (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    ∃ E : Cond (fun k : hsNodes n p => nodeType n p k) → ℚ[X],
      (∀ x (k : hsNodes n p) j (hj : j < (nodeType n p k).mult),
        (hasseDeriv j (E x)).eval (-(k : ℤ) : ℚ) = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0) ∧
      (∀ x d, padicNorm p ((E x).coeff d) ≤ 1) ∧
      (∀ x d, Fintype.card (Cond (fun k : hsNodes n p => nodeType n p k)) ≤ d → (E x).coeff d = 0) ∧
      padicNorm p (Matrix.det (fun x y =>
        functionalHS (fun k : hsNodes n p => hsC n p k) (fun k => (-(k : ℤ) : ℚ)) (E x * E y))) =
        (p : ℚ) ^ ((82 * n - 36 * p + 31 : ℤ)) := by
  have hodd := W2.p_odd (p := p) (W2.p_ge_13 hn hlow hup)
  obtain ⟨E, hδ, hcoef, hdeg, -, hdet⟩ := w3_family3 hn hlow hup
  refine ⟨E, hδ, hcoef, hdeg, ?_⟩
  set G : Matrix (Cond (fun k : hsNodes n p => nodeType n p k))
    (Cond (fun k : hsNodes n p => nodeType n p k)) ℚ := fun x y =>
      functionalHS (fun k : hsNodes n p => hsC n p k) (fun k => (-(k : ℤ) : ℚ)) (E x * E y)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  change padicNorm p (weightScale p (rowExp _) (colExp _) G).det = 1 at hdet
  rw [det_weightScale, prod_zpow_eq _ _ hp0, prod_zpow_eq _ _ hp0] at hdet
  have hS := sum_exps hn hodd hlow hup
  have e : (p : ℚ) ^ (∑ i, rowExp (fun k : hsNodes n p => nodeType n p k) i) * G.det *
      (p : ℚ) ^ (∑ i, colExp (fun k : hsNodes n p => nodeType n p k) i) =
      (p : ℚ) ^ ((82 * n - 36 * p + 31 : ℤ)) * G.det := by
    rw [← hS, Finset.sum_add_distrib, zpow_add₀ hp0]; ring
  rw [e, padicNorm_zpow_mul] at hdet
  have h2 : (p : ℚ) ^ ((82 * n - 36 * p + 31 : ℤ)) * ((p : ℚ) ^ (-(82 * n - 36 * p + 31 : ℤ)) *
      padicNorm p G.det) = padicNorm p G.det := by
    rw [← mul_assoc, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, one_mul]
  rw [← h2, hdet, mul_one]

end Fam3

end Hankel2.W3
