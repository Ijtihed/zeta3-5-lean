import RequestProject.Zeta35.NVGram
import RequestProject.Zeta7.Hankel2.W4Family3

/-!
# Non-vanishing (N, §6): the Hermite basis and the weighted valuations

The Hermite basis `E_{(h,j₀)}` (`h` an anchor, `j₀ < 4`) is dual to the jets of order `< 4` at the
anchors `t = −h` (`exists_basis`, from the confluent Vandermonde being an `ℓ`-unit).  Its jets
satisfy (`jet_lb`) `v(E_{x,a}(k)) ≥ lb x k a`, where

* at the own anchor: `δ_{a,j₀}`; at the own partner: `≥ j₀ − a`;
* at other anchors: `0`; at other partners: `≥ 4 − a`; at singletons: `≥ 0`.

With the valuations of the local constants (`VB_betaL`, `VB_betaR`, `VB_alpha`) and the weights
`ϖ = 5 − j₀`, the weighted valuation `ω` of every term is `≥ 1` for `b^{rest}` and `a`, `≥ 1` for
`b^ℓ` off the diagonal pair blocks, and `≥ 0` for `b^ℓ` (N, proof of Theorem 6.2).
-/

open Polynomial Finset

namespace Zeta35.NV

variable {n ℓ : ℕ}

/-- The index set of the Hermite basis: an anchor `h` and a jet order `j₀ < 4`. -/
abbrev HIdx (n ℓ : ℕ) := Σ _ : ↥(anch n ℓ), Fin 4

theorem anch_inj_mod (h : Adm n ℓ) :
    Function.Injective (fun i : ↥(anch n ℓ) => (((-(i : ℤ)) : ℤ) : ZMod ℓ)) := by
  intro i i' heq
  simp only at heq
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 heq
  have hi := mem_anch.mp i.2
  have hi' := mem_anch.mp i'.2
  obtain ⟨c, hc⟩ := hd
  have hl := h.lo
  have hl0 : (0 : ℤ) < ℓ := by exact_mod_cast h.prime.pos
  have h1 : c < 1 := by
    by_contra hcon; push_neg at hcon
    have : (ℓ : ℤ) * 1 ≤ ℓ * c := mul_le_mul_of_nonneg_left hcon hl0.le
    omega
  have h2 : -1 < c := by
    by_contra hcon; push_neg at hcon
    have : (ℓ : ℤ) * c ≤ ℓ * (-1) := mul_le_mul_of_nonneg_left hcon hl0.le
    omega
  have : c = 0 := by omega
  subst this
  exact Subtype.ext (by omega)

/-- **The Hermite basis** dual to the jets of order `< 4` at the anchors. -/
theorem exists_basis (h : Adm n ℓ) :
    haveI := Fact.mk h.prime
    ∃ E : HIdx n ℓ → ℚ[X],
      (∀ x (i : ↥(anch n ℓ)) j (hj : j < 4),
        Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0) ∧
      (∀ x d, padicNorm ℓ ((E x).coeff d) ≤ 1) ∧
      (∀ x d, Fintype.card (HIdx n ℓ) ≤ d → (E x).coeff d = 0) := by
  haveI := Fact.mk h.prime
  obtain ⟨E, h1, h2, h3, _⟩ := Hankel2.W3.exists_dual_hermite_basis (p := ℓ)
    (fun i : ↥(anch n ℓ) => -(i : ℤ)) (anch_inj_mod h) (fun _ => 4)
  refine ⟨E, fun x i j hj => ?_, h2, h3⟩
  have := h1 x i j hj
  unfold Pjet PF.Pjet
  rw [show (-((i : ℤ) : ℚ)) = (((-(i : ℤ)) : ℤ) : ℚ) by push_cast; ring]
  exact this

/-- "`k` is a paired node". -/
def Paired (n ℓ : ℕ) (k : ℤ) : Prop := k ∈ anch n ℓ ∨ k + ℓ ∈ anch n ℓ

instance (n ℓ : ℕ) (k : ℤ) : Decidable (Paired n ℓ k) := by unfold Paired; infer_instance

/-- "`k` belongs to the pair of `x`". -/
def InPair (n ℓ : ℕ) (x : HIdx n ℓ) (k : ℤ) : Prop := k = x.1.1 ∨ k = x.1.1 - ℓ

instance (n ℓ : ℕ) (x : HIdx n ℓ) (k : ℤ) : Decidable (InPair n ℓ x k) := by
  unfold InPair; infer_instance

/-- The lower bound for the valuation of the jets of `E_x` at `k`. -/
def lb (n ℓ : ℕ) (x : HIdx n ℓ) (k : ℤ) (a : ℕ) : ℤ :=
  if InPair n ℓ x k then (x.2 : ℤ) - a else if Paired n ℓ k then 4 - a else 0

theorem InPair.paired {x : HIdx n ℓ} {k : ℤ} (hk : InPair n ℓ x k) : Paired n ℓ k := by
  rcases hk with rfl | rfl
  · exact Or.inl x.1.2
  · right; rw [sub_add_cancel]; exact x.1.2

theorem lb_paired (x : HIdx n ℓ) {k : ℤ} (hp : Paired n ℓ k) (a : ℕ) :
    (x.2 : ℤ) - a + (if InPair n ℓ x k then 0 else 4 - (x.2 : ℤ)) ≤ lb n ℓ x k a := by
  unfold lb; split_ifs <;> omega

theorem lb_single (x : HIdx n ℓ) {k : ℤ} (hp : ¬ Paired n ℓ k) (a : ℕ) : lb n ℓ x k a = 0 := by
  unfold lb
  rw [if_neg (fun h => hp h.paired), if_neg hp]

theorem inPair_unique (h : Adm n ℓ) {x y : HIdx n ℓ} {k : ℤ} (hx : InPair n ℓ x k)
    (hy : InPair n ℓ y k) : x.1 = y.1 := by
  have h1 := anch_pos h x.1.2
  have h2 := anch_pos h y.1.2
  apply Subtype.ext
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega

/-- **The jets of the Hermite basis.** -/
theorem jet_lb (h : Adm n ℓ) (E : HIdx n ℓ → ℚ[X])
    (hE1 : ∀ x (i : ↥(anch n ℓ)) j (hj : j < 4),
      Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
    (hE2 : haveI := Fact.mk h.prime; ∀ x d, padicNorm ℓ ((E x).coeff d) ≤ 1)
    (x : HIdx n ℓ) (k : ℤ) (a : ℕ) (ha : a < 4) :
    haveI := Fact.mk h.prime; VB ℓ (Pjet (E x) k a) (lb n ℓ x k a) := by
  haveI := Fact.mk h.prime
  have hint : ∀ (c : ℤ) m, padicNorm ℓ ((hasseDeriv m (E x)).eval (c : ℚ)) ≤ 1 :=
    fun c m => Hankel2.W3.Fam3.padicNorm_jet_le_one (p := ℓ) (E x) (hE2 x) c m
  have hdl : padicNorm ℓ (ℓ : ℚ) ≤ (ℓ : ℚ)⁻¹ := by rw [padicNorm.padicNorm_p_of_prime]
  -- vanishing of the jets at an anchor `i ≠ x.1` and below `x.2` at `x.1`
  have hvan : ∀ (i : ↥(anch n ℓ)) (m : ℕ), m < 4 → (i ≠ x.1 ∨ m ≠ (x.2 : ℕ)) →
      (hasseDeriv m (E x)).eval (((-(i : ℤ)) : ℤ) : ℚ) = 0 := by
    intro i m hm hne
    have := hE1 x i m hm
    unfold Pjet PF.Pjet at this
    rw [show (((-(i : ℤ)) : ℤ) : ℚ) = -((i : ℤ) : ℚ) by push_cast; ring, this, if_neg]
    rintro rfl
    rcases hne with h1 | h1 <;> exact h1 rfl
  unfold lb
  split_ifs with hin hp
  · rcases hin with hk | hk
    · -- own anchor
      have := hE1 x x.1 a ha
      rw [hk, this]
      split_ifs with hxa
      · have : (x.2 : ℕ) = a := by rw [hxa]
        rw [this, sub_self]; exact VB_one
      · exact VB_zero _
    · -- own partner
      have hs := Hankel2.W3.padicNorm_jet_shift_le (p := ℓ) (E x) (((-(x.1 : ℤ)) : ℤ) : ℚ) ℓ x.2 a
        (fun m => hint _ m) (fun m hm => hvan x.1 m (by omega) (Or.inr (by omega))) hdl
      unfold VB Pjet PF.Pjet
      rw [hk, show (-((x.1 - ℓ : ℤ) : ℚ)) = (((-(x.1 : ℤ)) : ℤ) : ℚ) + ℓ by push_cast; ring]
      convert hs using 2; ring
  · rcases hp with hp | hp
    · -- another anchor
      have hne : (⟨k, hp⟩ : ↥(anch n ℓ)) ≠ x.1 := fun he => hin (Or.inl (by rw [← he]))
      have := hvan ⟨k, hp⟩ a ha (Or.inl hne)
      unfold Pjet PF.Pjet
      rw [show (-((k : ℤ) : ℚ)) = (((-(k : ℤ)) : ℤ) : ℚ) by push_cast; ring]
      simp only at this
      rw [this]; exact VB_zero _
    · -- another partner
      have hne : (⟨k + ℓ, hp⟩ : ↥(anch n ℓ)) ≠ x.1 := fun he =>
        hin (Or.inr (by rw [← he]; ring))
      have hs := Hankel2.W3.padicNorm_jet_shift_le (p := ℓ) (E x) (((-(k + ℓ : ℤ)) : ℤ) : ℚ) ℓ 4 a
        (fun m => hint _ m) (fun m hm => hvan ⟨k + ℓ, hp⟩ m hm (Or.inl hne)) hdl
      unfold VB Pjet PF.Pjet
      rw [show (-((k : ℤ) : ℚ)) = (((-(k + ℓ : ℤ)) : ℤ) : ℚ) + ℓ by push_cast; ring]
      convert hs using 2; push_cast; ring
  · -- singleton
    unfold Pjet PF.Pjet
    rw [show (-((k : ℤ) : ℚ)) = (((-k : ℤ)) : ℚ) by push_cast; ring]
    exact (VB_zero_iff _).2 (hint _ a)

theorem jet_int (h : Adm n ℓ) (E : HIdx n ℓ → ℚ[X])
    (hE2 : haveI := Fact.mk h.prime; ∀ x d, padicNorm ℓ ((E x).coeff d) ≤ 1)
    (x : HIdx n ℓ) (k : ℤ) (a : ℕ) : haveI := Fact.mk h.prime; VB ℓ (Pjet (E x) k a) 0 := by
  haveI := Fact.mk h.prime
  unfold Pjet PF.Pjet
  rw [show (-((k : ℤ) : ℚ)) = (((-k : ℤ)) : ℚ) by push_cast; ring]
  exact (VB_zero_iff _).2 (Hankel2.W3.Fam3.padicNorm_jet_le_one (p := ℓ) (E x) (hE2 x) _ a)

/-! ### Valuations of the local constants, uniformly over the nodes -/

theorem VB_betaL (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (a : ℕ) (ha : a < 4) :
    haveI := Fact.mk h.prime
    VB ℓ (betaL n ℓ k a) (if Paired n ℓ k then (a : ℤ) - 10 else 100) := by
  haveI := Fact.mk h.prime
  split_ifs with hp
  · rcases hp with hp | hp
    · have := VB_of_scaled (betaL_anchor h hp a ha).2
      convert this using 1; push_cast [show a ≤ 10 by omega]; ring
    · have := VB_of_scaled (betaL_partner h hp a ha).2
      rw [show k + ℓ - ℓ = k by ring] at this
      convert this using 1; push_cast [show a ≤ 10 by omega]; ring
  · rw [betaL_single h hk (fun h1 => hp (Or.inl h1)) (fun h2 => hp (Or.inr h2))]
    exact VB_zero _

theorem VB_betaR (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (a : ℕ) (ha : a < 4) :
    haveI := Fact.mk h.prime
    VB ℓ (betaR n ℓ k a) (if Paired n ℓ k then (a : ℤ) - 7 else 0) := by
  haveI := Fact.mk h.prime
  split_ifs with hp
  · rcases hp with hp | hp
    · exact betaR_paired (fun b => (Hk_anchor h hp b).2) a ha
    · have := betaR_paired (n := n) (fun b => (Hk_partner h hp b).2) a ha
      rwa [show k + ℓ - ℓ = k by ring] at this
  · exact betaR_single h hk (fun h1 => hp (Or.inl h1)) (fun h2 => hp (Or.inr h2)) a

theorem VB_alpha (h : Adm n ℓ) {k : ℤ} (hk : k ∈ nodes n) (a : ℕ) :
    haveI := Fact.mk h.prime
    VB ℓ (alphaC n k a) (if Paired n ℓ k then (a : ℤ) - 5 else 0) := by
  haveI := Fact.mk h.prime
  split_ifs with hp
  · rcases hp with hp | hp
    · exact alpha_paired (fun b => (Hk_anchor h hp b).2) a
    · have := alpha_paired (n := n) (fun b => (Hk_partner h hp b).2) a
      rwa [show k + ℓ - ℓ = k by ring] at this
  · exact alpha_single h hk (fun h1 => hp (Or.inl h1)) (fun h2 => hp (Or.inr h2)) a

/-- The weights `ϖ_{(h,j₀)} = 5 − j₀`. -/
def wt (x : HIdx n ℓ) : ℤ := 5 - (x.2 : ℤ)

end Zeta35.NV
