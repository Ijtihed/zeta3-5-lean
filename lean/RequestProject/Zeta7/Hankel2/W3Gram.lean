import Mathlib
import RequestProject.Zeta7.Hankel2.WeightCert
import RequestProject.Zeta7.Hankel2.W3Blocks

/-!
# W3: the harmonic-sum Gram matrix in the dual Hermite basis

`ZETA7_STATUS.md`, round (e) §2 (Lemma W3), family 3, `K = 10n + 3 - 4p`.

The harmonic-sum part of the node functional is
`L_HS(F) = Σ_k Σ_{j ≤ 3} c_{k,j} · F_j(x_k)`, where `F_j(x_k)` is the `j`-th Hasse derivative
(Taylor coefficient) of `F` at the node `x_k`, and `k` runs over the harmonic-sum nodes.  The nodes
are of three types (`NodeType`): *special* (all four jets prescribed), *generic* (jets `0, 1`
prescribed) and `g*` (jet `0` prescribed).  The Hermite conditions are indexed by `Cond τ`, and the
dual Hermite basis `E_x` has jets `J x k j = (E_x)_j(x_k)` equal to `δ` on the prescribed jets and
`p`-integral otherwise (W1, `HermiteBasis.lean`).

Here `G_HS[x,y] = L_HS(E_x E_y)`; by the Leibniz rule for Hasse derivatives this is
`gram c J x y` (`gram_eq_functional`).  With the weights `ℓ = (6,5,4,3)` at special nodes and `5/2`
at generic nodes and `g*` (realised as row exponent `2` and column exponent `3`), the main theorem
`w3_gram` shows, under the local valuations of W2 (`NodeHyp`, proved in `W2Local.lean` for the
actual constants), that the weighted matrix `p^{r_x + s_y} G_HS[x,y]` is `p`-integral and has
`p`-adic unit determinant, i.e. `v_p det G_HS = -2 Σ ℓ`.
-/

open Matrix Polynomial

namespace Hankel2.W3

/-- The three types of harmonic-sum nodes at the prime `p`. -/
inductive NodeType
  | special
  | generic
  | gstar
  deriving DecidableEq

namespace NodeType

/-- Number of prescribed jets at a node of the given type. -/
def mult : NodeType → ℕ
  | special => 4
  | generic => 2
  | gstar => 1

/-- Row exponent of the condition "jet `a`" at a node of the given type. -/
def rowE : NodeType → ℕ → ℤ
  | special, a => 6 - a
  | generic, _ => 2
  | gstar, _ => 2

/-- Column exponent of the condition "jet `b`" at a node of the given type. -/
def colE : NodeType → ℕ → ℤ
  | special, b => 6 - b
  | generic, _ => 3
  | gstar, _ => 3

theorem mult_le_four (t : NodeType) : t.mult ≤ 4 := by cases t <;> decide

theorem five_le_rowE_add_colE (t t' : NodeType) {a b : ℕ} (ha : a < t.mult) (hb : b < t'.mult) :
    5 ≤ t.rowE a + t'.colE b := by
  cases t <;> cases t' <;> simp only [mult, rowE, colE] at * <;> omega

end NodeType

variable (p : ℕ) [hp : Fact p.Prime]

/-- The local valuation hypotheses at a node of type `t` with constants `c j` (`j ≤ 3`); these are
the conclusions of Lemma W2 (`W2Local.lean`).
* `small`: an unprescribed jet order `j ≤ 3` carries a constant with `v_p ≥ -4`;
* `lead`: the prescribed pair `(a, b)` carries a constant with `v_p ≥ -(r_a + s_b)`;
* `unit`: the entry that makes the local block unimodular has exact valuation. -/
structure NodeHyp (t : NodeType) (c : ℕ → ℚ) : Prop where
  small : ∀ j, t.mult ≤ j → j ≤ 3 → padicNorm p (c j) ≤ (p : ℚ) ^ (4 : ℤ)
  lead : ∀ a b, a < t.mult → b < t.mult → a + b ≤ 3 →
    padicNorm p (c (a + b)) ≤ (p : ℚ) ^ (t.rowE a + t.colE b)
  unit : match t with
    | .special => padicNorm p (c 3) = (p : ℚ) ^ (9 : ℤ)
    | .generic => padicNorm p (c 1) = (p : ℚ) ^ (5 : ℤ)
    | .gstar => padicNorm p (c 0) = (p : ℚ) ^ (5 : ℤ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → NodeType)

/-- Hermite conditions: jet `a < mult (τ k)` at node `k`. -/
abbrev Cond := Σ k : ι, Fin (τ k).mult

/-- Row exponents of the weight certificate. -/
def rowExp (x : Cond τ) : ℤ := (τ x.1).rowE x.2

/-- Column exponents of the weight certificate. -/
def colExp (x : Cond τ) : ℤ := (τ x.1).colE x.2

variable {τ}

/-- The local contribution of node `k` to `L_HS(E_x E_y)`, written through the jets
`J x k j = (E_x)_j(x_k)`. -/
def localTerm (c : ι → ℕ → ℚ) (J : Cond τ → ι → ℕ → ℚ) (k : ι) (x y : Cond τ) : ℚ :=
  ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
    if a + b ≤ 3 then c k (a + b) * J x k a * J y k b else 0

/-- The harmonic-sum Gram matrix `G_HS[x,y] = L_HS(E_x E_y)`. -/
def gram (c : ι → ℕ → ℚ) (J : Cond τ → ι → ℕ → ℚ) : Matrix (Cond τ) (Cond τ) ℚ :=
  fun x y => ∑ k, localTerm c J k x y

/-- The functional `L_HS(F) = Σ_k Σ_{j ≤ 3} c_{k,j} F_j(x_k)` on polynomials. -/
noncomputable def functionalHS (c : ι → ℕ → ℚ) (node : ι → ℚ) (F : ℚ[X]) : ℚ :=
  ∑ k, ∑ j ∈ Finset.range 4, c k j * (hasseDeriv j F).eval (node k)

omit [DecidableEq ι] in
/-- **Leibniz bridge.**  If `J` is the jet array of polynomials `E`, then `gram c J x y` is the
harmonic-sum functional applied to `E_x E_y`. -/
theorem gram_eq_functional (c : ι → ℕ → ℚ) (node : ι → ℚ) (E : Cond τ → ℚ[X]) (x y : Cond τ) :
    gram c (fun x k j => (hasseDeriv j (E x)).eval (node k)) x y =
      functionalHS c node (E x * E y) := by
  unfold gram functionalHS localTerm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hasseDeriv_mul, Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, Finset.range_zero,
    Finset.sum_empty]
  simp
  ring

/-! ### Ultrametric bookkeeping -/

theorem padicNorm_sum_le_one {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ i ∈ s, padicNorm p (f i) ≤ 1) : padicNorm p (∑ i ∈ s, f i) ≤ 1 :=
  padicNorm.sum_le' h zero_le_one

theorem padicNorm_sum_lt_one {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ i ∈ s, padicNorm p (f i) < 1) : padicNorm p (∑ i ∈ s, f i) < 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · exact padicNorm.sum_lt hs h

theorem padicNorm_zpow_mul (z : ℤ) (q : ℚ) :
    padicNorm p ((p : ℚ) ^ z * q) = (p : ℚ) ^ (-z) * padicNorm p q := by
  rw [padicNorm.mul]
  congr 1
  let f : ℚ →*₀ ℚ :=
    { toFun := padicNorm p, map_zero' := padicNorm.zero, map_one' := padicNorm.one,
      map_mul' := padicNorm.mul }
  have := map_zpow₀ f (p : ℚ) z
  change padicNorm p _ = padicNorm p _ ^ z at this
  rw [this, padicNorm.padicNorm_p_of_prime, _root_.inv_zpow']

variable {p}

omit [Fintype ι] in
/-- **The term bound.**  Every term of the weighted local contribution has norm `≤ 1`, and norm
`< 1` unless it is the *leading* term `x = (k, a)`, `y = (k, b)`. -/
theorem term_bound (c : ι → ℕ → ℚ) (hc : ∀ k, NodeHyp p (τ k) (c k))
    (J : Cond τ → ι → ℕ → ℚ)
    (hJδ : ∀ x k j (hj : j < (τ k).mult), J x k j = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hJint : ∀ x k j, padicNorm p (J x k j) ≤ 1) (k : ι) (x y : Cond τ) (a b : ℕ)
    (hab : a + b ≤ 3) :
    padicNorm p ((p : ℚ) ^ (rowExp τ x + colExp τ y) * (c k (a + b) * J x k a * J y k b)) ≤ 1 ∧
    (¬ (x.1 = k ∧ y.1 = k ∧ (x.2 : ℕ) = a ∧ (y.2 : ℕ) = b) →
      padicNorm p ((p : ℚ) ^ (rowExp τ x + colExp τ y) * (c k (a + b) * J x k a * J y k b)) < 1) := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  have h5 : 5 ≤ rowExp τ x + colExp τ y :=
    NodeType.five_le_rowE_add_colE _ _ x.2.2 y.2.2
  rw [padicNorm_zpow_mul, padicNorm.mul, padicNorm.mul]
  by_cases hx0 : J x k a = 0
  · simp [hx0]
  by_cases hy0 : J y k b = 0
  · simp [hy0]
  have hxJ := hJint x k a
  have hyJ := hJint y k b
  have hc0 := padicNorm.nonneg (p := p) (c k (a + b))
  have hxJ0 := padicNorm.nonneg (p := p) (J x k a)
  have hyJ0 := padicNorm.nonneg (p := p) (J y k b)
  have hw0 : (0 : ℚ) < (p : ℚ) ^ (-(rowExp τ x + colExp τ y)) := zpow_pos hp0 _
  by_cases hsmall : (τ k).mult ≤ a + b
  · have hcs := (hc k).small (a + b) hsmall hab
    have hlt : (p : ℚ) ^ (-(rowExp τ x + colExp τ y)) * (p : ℚ) ^ (4 : ℤ) < 1 := by
      rw [← zpow_add₀ hp0.ne']
      exact zpow_lt_one_of_neg₀ h1 (by omega)
    have hle : (p : ℚ) ^ (-(rowExp τ x + colExp τ y)) *
        (padicNorm p (c k (a + b)) * padicNorm p (J x k a) * padicNorm p (J y k b)) ≤
        (p : ℚ) ^ (-(rowExp τ x + colExp τ y)) * (p : ℚ) ^ (4 : ℤ) := by
      refine mul_le_mul_of_nonneg_left ?_ hw0.le
      calc padicNorm p (c k (a + b)) * padicNorm p (J x k a) * padicNorm p (J y k b)
          ≤ (p : ℚ) ^ (4 : ℤ) * 1 * 1 := by gcongr
        _ = _ := by ring
    exact ⟨(hle.trans_lt hlt).le, fun _ => hle.trans_lt hlt⟩
  · push_neg at hsmall
    have ha : a < (τ k).mult := by omega
    have hb : b < (τ k).mult := by omega
    have hx : x = ⟨k, ⟨a, ha⟩⟩ := by
      by_contra hne; exact hx0 (by rw [hJδ x k a ha, if_neg hne])
    have hy : y = ⟨k, ⟨b, hb⟩⟩ := by
      by_contra hne; exact hy0 (by rw [hJδ y k b hb, if_neg hne])
    subst hx hy
    refine ⟨?_, fun h => absurd ⟨rfl, rfl, rfl, rfl⟩ h⟩
    have hJa : J ⟨k, ⟨a, ha⟩⟩ k a = 1 := by rw [hJδ _ k a ha, if_pos rfl]
    have hJb : J ⟨k, ⟨b, hb⟩⟩ k b = 1 := by rw [hJδ _ k b hb, if_pos rfl]
    rw [hJa, hJb, padicNorm.one, mul_one, mul_one]
    have hl := (hc k).lead a b ha hb hab
    change padicNorm p (c k (a + b)) ≤ (p : ℚ) ^ (rowExp τ ⟨k, ⟨a, ha⟩⟩ + colExp τ ⟨k, ⟨b, hb⟩⟩)
      at hl
    calc (p : ℚ) ^ (-(rowExp τ ⟨k, ⟨a, ha⟩⟩ + colExp τ ⟨k, ⟨b, hb⟩⟩)) * padicNorm p (c k (a + b))
        ≤ (p : ℚ) ^ (-(rowExp τ ⟨k, ⟨a, ha⟩⟩ + colExp τ ⟨k, ⟨b, hb⟩⟩)) *
          (p : ℚ) ^ (rowExp τ ⟨k, ⟨a, ha⟩⟩ + colExp τ ⟨k, ⟨b, hb⟩⟩) :=
          mul_le_mul_of_nonneg_left hl hw0.le
      _ = 1 := by rw [← zpow_add₀ hp0.ne', neg_add_cancel, zpow_zero]

/-- The weighted Gram entries are `p`-integral. -/
theorem gram_entry_le_one (c : ι → ℕ → ℚ) (hc : ∀ k, NodeHyp p (τ k) (c k))
    (J : Cond τ → ι → ℕ → ℚ)
    (hJδ : ∀ x k j (hj : j < (τ k).mult), J x k j = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hJint : ∀ x k j, padicNorm p (J x k j) ≤ 1) (x y : Cond τ) :
    padicNorm p (weightScale p (rowExp τ) (colExp τ) (gram c J) x y) ≤ 1 := by
  simp only [weightScale, gram, localTerm, Finset.mul_sum, mul_ite, mul_zero]
  refine padicNorm_sum_le_one p _ _ fun k _ => padicNorm_sum_le_one p _ _ fun a _ =>
    padicNorm_sum_le_one p _ _ fun b _ => ?_
  split_ifs with hab
  · exact (term_bound c hc J hJδ hJint k x y a b hab).1
  · simp

/-- Off the node blocks, the weighted Gram entries are divisible by `p`. -/
theorem gram_entry_lt_one_of_ne (c : ι → ℕ → ℚ) (hc : ∀ k, NodeHyp p (τ k) (c k))
    (J : Cond τ → ι → ℕ → ℚ)
    (hJδ : ∀ x k j (hj : j < (τ k).mult), J x k j = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hJint : ∀ x k j, padicNorm p (J x k j) ≤ 1) (x y : Cond τ) (hxy : x.1 ≠ y.1) :
    padicNorm p (weightScale p (rowExp τ) (colExp τ) (gram c J) x y) < 1 := by
  simp only [weightScale, gram, localTerm, Finset.mul_sum, mul_ite, mul_zero]
  refine padicNorm_sum_lt_one p _ _ fun k _ => padicNorm_sum_lt_one p _ _ fun a _ =>
    padicNorm_sum_lt_one p _ _ fun b _ => ?_
  split_ifs with hab
  · exact (term_bound c hc J hJδ hJint k x y a b hab).2 fun h => hxy (h.1.trans h.2.1.symm)
  · simp

/-- The leading value of the local block. -/
def leadVal (c : ℕ → ℚ) (a b : ℕ) : ℚ := if a + b ≤ 3 then c (a + b) else 0

/-- Inside a node block, the weighted Gram entry is congruent mod `p` to the weighted leading
value `p^{r_a + s_b} c_{k, a+b}`. -/
theorem gram_entry_sub_lead (c : ι → ℕ → ℚ) (hc : ∀ k, NodeHyp p (τ k) (c k))
    (J : Cond τ → ι → ℕ → ℚ)
    (hJδ : ∀ x k j (hj : j < (τ k).mult), J x k j = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hJint : ∀ x k j, padicNorm p (J x k j) ≤ 1) (k : ι) (a b : Fin (τ k).mult) :
    padicNorm p (weightScale p (rowExp τ) (colExp τ) (gram c J) ⟨k, a⟩ ⟨k, b⟩ -
      (p : ℚ) ^ ((τ k).rowE a + (τ k).colE b) * leadVal (c k) a b) < 1 := by
  have ha4 : (a : ℕ) < 4 := lt_of_lt_of_le a.2 (NodeType.mult_le_four _)
  have hb4 : (b : ℕ) < 4 := lt_of_lt_of_le b.2 (NodeType.mult_le_four _)
  set x : Cond τ := ⟨k, a⟩
  set y : Cond τ := ⟨k, b⟩
  set w : ℚ := (p : ℚ) ^ (rowExp τ x + colExp τ y) with hw
  have hwe : (p : ℚ) ^ ((τ k).rowE a + (τ k).colE b) = w := rfl
  rw [hwe]
  set g : ℕ → ℕ → ℚ := fun a' b' =>
    if a' + b' ≤ 3 then c k (a' + b') * J x k a' * J y k b' else 0 with hg
  have hT : localTerm c J k x y = ∑ a' ∈ Finset.range 4, ∑ b' ∈ Finset.range 4, g a' b' := rfl
  have hsplit : weightScale p (rowExp τ) (colExp τ) (gram c J) x y - w * leadVal (c k) a b =
      ∑ k' ∈ Finset.univ.erase k, w * localTerm c J k' x y +
      ∑ a' ∈ Finset.range 4, ∑ b' ∈ Finset.range 4,
        (w * g a' b' - if a' = (a : ℕ) ∧ b' = (b : ℕ) then w * leadVal (c k) a b else 0) := by
    have hsum : ∑ a' ∈ Finset.range 4, ∑ b' ∈ Finset.range 4,
        (if a' = (a : ℕ) ∧ b' = (b : ℕ) then w * leadVal (c k) a b else 0) =
        w * leadVal (c k) a b := by
      simp only [ite_and]
      simp [ha4, hb4]
    simp only [Finset.sum_sub_distrib, hsum]
    simp only [weightScale, gram]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), mul_add, Finset.mul_sum, hT, Finset.mul_sum]
    simp only [Finset.mul_sum, ← hw]
    ring
  rw [hsplit]
  refine lt_of_le_of_lt padicNorm.nonarchimedean (max_lt ?_ ?_)
  · refine padicNorm_sum_lt_one p _ _ fun k' hk' => ?_
    have hk'k : k' ≠ k := Finset.ne_of_mem_erase hk'
    simp only [localTerm, Finset.mul_sum, mul_ite, mul_zero]
    refine padicNorm_sum_lt_one p _ _ fun a' _ => padicNorm_sum_lt_one p _ _ fun b' _ => ?_
    split_ifs with hab
    · exact (term_bound c hc J hJδ hJint k' x y a' b' hab).2 fun h => hk'k h.1.symm
    · simp
  · refine padicNorm_sum_lt_one p _ _ fun a' _ => padicNorm_sum_lt_one p _ _ fun b' _ => ?_
    by_cases hlead : a' = (a : ℕ) ∧ b' = (b : ℕ)
    · obtain ⟨rfl, rfl⟩ := hlead
      rw [if_pos ⟨rfl, rfl⟩]
      have hJa : J x k a = 1 := by rw [hJδ x k a a.2, if_pos rfl]
      have hJb : J y k b = 1 := by rw [hJδ y k b b.2, if_pos rfl]
      simp only [hg, leadVal, hJa, hJb, mul_one]
      split_ifs <;> simp
    · rw [if_neg hlead, sub_zero]
      simp only [hg, mul_ite, mul_zero]
      split_ifs with hab
      · exact (term_bound c hc J hJδ hJint k x y a' b' hab).2 fun h => hlead ⟨h.2.2.1.symm, h.2.2.2.symm⟩
      · simp

theorem norm_ratCast_padic (q : ℚ) : ‖(q : ℚ_[p])‖ = (padicNorm p q : ℝ) := by
  rw [Padic.eq_padicNorm]

theorem mem_maximalIdeal_of_close (z : ℤ_[p]) (q : ℚ) (h : ‖(z : ℚ_[p]) - (q : ℚ_[p])‖ < 1)
    (hq : padicNorm p q < 1) : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hq' : ‖(q : ℚ_[p])‖ < 1 := by rw [norm_ratCast_padic]; exact_mod_cast hq
  have : (z : ℚ_[p]) = ((z : ℚ_[p]) - q) + q := by ring
  change ‖(z : ℚ_[p])‖ < 1
  rw [this]
  exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt h hq')

theorem isUnit_of_close (z : ℤ_[p]) (q : ℚ) (h : ‖(z : ℚ_[p]) - (q : ℚ_[p])‖ < 1)
    (hq : padicNorm p q = 1) : IsUnit z := by
  rw [PadicInt.isUnit_iff]
  have hq' : ‖(q : ℚ_[p])‖ = 1 := by rw [norm_ratCast_padic]; exact_mod_cast hq
  have : (z : ℚ_[p]) = ((z : ℚ_[p]) - q) + q := by ring
  change ‖(z : ℚ_[p])‖ = 1
  rw [this, Padic.add_eq_max_of_ne (by rw [hq']; exact h.ne), hq']
  exact max_eq_right h.le

/-- The local block lemma: a `p`-adic integer matrix congruent mod `p` to the weighted leading block
of a node satisfying `NodeHyp` has unit determinant. -/
theorem isUnit_det_block (t : NodeType) (c : ℕ → ℚ) (hc : NodeHyp p t c)
    (B : Matrix (Fin t.mult) (Fin t.mult) ℤ_[p])
    (hB : ∀ a b, ‖(B a b : ℚ_[p]) - (((p : ℚ) ^ (t.rowE a + t.colE b) * leadVal c a b : ℚ) : ℚ_[p])‖
      < 1) : IsUnit B.det := by
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  cases t with
  | special =>
    have hu : padicNorm p (c 3) = (p : ℚ) ^ (9 : ℤ) := hc.unit
    refine isUnit_det_of_antitriangular_mod (n := 4) B (fun i j hij => ?_) (fun i => ?_)
    · refine mem_maximalIdeal_of_close _ _ (hB i j) ?_
      simp [leadVal, show ¬ ((i : ℕ) + j ≤ 3) by omega]
    · refine isUnit_of_close _ _ (hB i (Fin.rev i)) ?_
      have hi : (i : ℕ) + (Fin.rev i : ℕ) = 3 := by rw [Fin.val_rev]; have := i.2; omega
      have he : NodeType.special.rowE i + NodeType.special.colE (Fin.rev i) = 9 := by
        simp only [NodeType.rowE, NodeType.colE]; omega
      rw [he, leadVal, if_pos hi.le, hi, padicNorm_zpow_mul, hu, ← zpow_add₀ hp0.ne']
      simp
  | generic =>
    have hu : padicNorm p (c 1) = (p : ℚ) ^ (5 : ℤ) := hc.unit
    have hs : padicNorm p (c 2) ≤ (p : ℚ) ^ (4 : ℤ) := hc.small 2 le_rfl (by norm_num)
    refine isUnit_det_fin_two_of_mod (R := ℤ_[p]) (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) ?_ ?_ ?_
    · refine mem_maximalIdeal_of_close _ _ (hB (1 : Fin 2) (1 : Fin 2)) ?_
      change padicNorm p ((p : ℚ) ^ ((2 : ℤ) + 3) * leadVal c 1 1) < 1
      rw [leadVal, if_pos (by norm_num), padicNorm_zpow_mul]
      calc (p : ℚ) ^ (-((2 : ℤ) + 3)) * padicNorm p (c (1 + 1))
          ≤ (p : ℚ) ^ (-((2 : ℤ) + 3)) * (p : ℚ) ^ (4 : ℤ) :=
            mul_le_mul_of_nonneg_left hs (zpow_pos hp0 _).le
        _ < 1 := by rw [← zpow_add₀ hp0.ne']; exact zpow_lt_one_of_neg₀ h1 (by norm_num)
    · refine isUnit_of_close _ _ (hB (0 : Fin 2) (1 : Fin 2)) ?_
      change padicNorm p ((p : ℚ) ^ ((2 : ℤ) + 3) * leadVal c 0 1) = 1
      rw [leadVal, if_pos (by norm_num), padicNorm_zpow_mul, zero_add, hu, ← zpow_add₀ hp0.ne']
      simp
    · refine isUnit_of_close _ _ (hB (1 : Fin 2) (0 : Fin 2)) ?_
      change padicNorm p ((p : ℚ) ^ ((2 : ℤ) + 3) * leadVal c 1 0) = 1
      rw [leadVal, if_pos (by norm_num), padicNorm_zpow_mul, add_zero, hu, ← zpow_add₀ hp0.ne']
      simp
  | gstar =>
    have hu : padicNorm p (c 0) = (p : ℚ) ^ (5 : ℤ) := hc.unit
    change IsUnit (Matrix.det (n := Fin 1) B)
    rw [Matrix.det_unique]
    refine isUnit_of_close _ _ (hB (0 : Fin 1) (0 : Fin 1)) ?_
    change padicNorm p ((p : ℚ) ^ ((2 : ℤ) + 3) * leadVal c 0 0) = 1
    rw [leadVal, if_pos (by norm_num), padicNorm_zpow_mul, add_zero, hu, ← zpow_add₀ hp0.ne']
    simp

/-- **Lemma W3.**  Under the W1 properties of the dual Hermite basis (`hJδ`, `hJint`) and the W2
local valuations (`hc`), the weighted harmonic-sum Gram matrix `p^{r_x + s_y} G_HS[x,y]` is
`p`-integral and has `p`-adic unit determinant; equivalently `v_p det G_HS = -Σ_x (r_x + s_x)`. -/
theorem w3_gram (c : ι → ℕ → ℚ) (hc : ∀ k, NodeHyp p (τ k) (c k))
    (J : Cond τ → ι → ℕ → ℚ)
    (hJδ : ∀ x k j (hj : j < (τ k).mult), J x k j = if x = ⟨k, ⟨j, hj⟩⟩ then 1 else 0)
    (hJint : ∀ x k j, padicNorm p (J x k j) ≤ 1) :
    (∀ x y, padicNorm p (weightScale p (rowExp τ) (colExp τ) (gram c J) x y)
      ≤ 1) ∧
    padicNorm p (weightScale p (rowExp τ) (colExp τ) (gram c J)).det = 1 := by
  set M := weightScale p (rowExp τ) (colExp τ) (gram c J) with hM
  have hle : ∀ x y, padicNorm p (M x y) ≤ 1 := gram_entry_le_one c hc J hJδ hJint
  refine ⟨hle, ?_⟩
  let M' : Matrix (Cond τ) (Cond τ) ℤ_[p] := fun i j => ratToPadicInt (M i j) (hle i j)
  have hM' : ∀ i j, ((M' i j : ℤ_[p]) : ℚ_[p]) = ((M i j : ℚ) : ℚ_[p]) := fun _ _ => rfl
  let blk : Cond τ → Fin (Fintype.card ι) := fun x => Fintype.equivFin ι x.1
  have hunit : IsUnit M'.det := by
    refine isUnit_det_of_blockTriangular_mod M' blk (fun i j hij => ?_) (fun b => ?_)
    · have hne : i.1 ≠ j.1 := by
        intro h; apply (ne_of_gt hij); simp [blk, h]
      refine mem_maximalIdeal_of_close _ (M i j) (by rw [hM', sub_self, norm_zero]; norm_num) ?_
      exact gram_entry_lt_one_of_ne c hc J hJδ hJint i j hne
    · set k := (Fintype.equivFin ι).symm b with hk
      have hblk : ∀ x : Cond τ, blk x = b ↔ x.1 = k := by
        intro x; simp [blk, hk, Equiv.eq_symm_apply]
      let e : Fin (τ k).mult ≃ {x : Cond τ // blk x = b} :=
        Equiv.ofBijective (fun a => ⟨⟨k, a⟩, (hblk _).2 rfl⟩) (by
          constructor
          · intro a a' h
            have h' := congrArg Subtype.val h
            simpa using h'
          · rintro ⟨⟨k', a⟩, hx⟩
            have : k' = k := (hblk _).1 hx
            subst this
            exact ⟨a, rfl⟩)
      rw [← Matrix.det_submatrix_equiv_self e]
      refine isUnit_det_block (τ k) (c k) (hc k) _ fun a a' => ?_
      change ‖((M ⟨k, a⟩ ⟨k, a'⟩ : ℚ) : ℚ_[p]) - (((p : ℚ) ^ ((τ k).rowE a + (τ k).colE a') *
        leadVal (c k) a a' : ℚ) : ℚ_[p])‖ < 1
      rw [← Rat.cast_sub, norm_ratCast_padic]
      exact_mod_cast gram_entry_sub_lead c hc J hJδ hJint k a a'
  have hcast : ((M'.det : ℤ_[p]) : ℚ_[p]) = ((M.det : ℚ) : ℚ_[p]) := by
    have h1 : ((M'.det : ℤ_[p]) : ℚ_[p]) =
        ((PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).mapMatrix M').det := by
      rw [← RingHom.map_det]; rfl
    have h2 : ((M.det : ℚ) : ℚ_[p]) = ((Rat.castHom ℚ_[p]).mapMatrix M).det := by
      rw [← RingHom.map_det]; rfl
    rw [h1, h2]
    rfl
  rw [PadicInt.isUnit_iff] at hunit
  have : ‖((M.det : ℚ) : ℚ_[p])‖ = 1 := by rw [← hcast]; exact hunit
  rw [norm_ratCast_padic] at this
  exact_mod_cast this

end Hankel2.W3
