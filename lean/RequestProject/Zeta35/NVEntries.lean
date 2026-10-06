import RequestProject.Zeta35.NVBasis

/-!
# Non-vanishing (N, §6): the weighted Gram entries in the Hermite basis

For the Hermite basis `E` and the weights `ϖ = 5 − j₀`:

* `Gr_bound`, `Ga_bound`: `ℓ^{ϖ_x+ϖ_y} b^{rest}(E_x E_y)` and `ℓ^{ϖ_x+ϖ_y} a(E_x E_y)` are `≡ 0 (mod ℓ)`
  (rational part `ω ≥ 3`, `ζ₃(5)` part `ω ≥ 5`, singletons `ω ≥ 4`);
* `Gh_int`: `ℓ^{ϖ_x+ϖ_y} b^ℓ(E_x E_y)` is `ℓ`-integral;
* `Gh_off`: it is `≡ 0` for `x`, `y` in different pairs (`ω ≥ 1`);
* `Gh_diag`: for `x = (h, a)`, `y = (h, b)` it is `≡ 2 y₀(h) Λ_{j(h)}(w^{a+b}) (mod ℓ)`.
-/

open Polynomial Finset

namespace Zeta35.NV

variable {n ℓ : ℕ}

section

variable [hℓ : Fact ℓ.Prime] (h : Adm n ℓ) (E : HIdx n ℓ → ℚ[X])
    (hE1 : ∀ x (i : ↥(anch n ℓ)) j (hj : j < 4),
      Pjet (E x) i j = if x = ⟨i, ⟨j, hj⟩⟩ then 1 else 0)
    (hE2 : ∀ x d, padicNorm ℓ ((E x).coeff d) ≤ 1)
include h hE1 hE2

theorem Gr_bound (x y : HIdx n ℓ) :
    VB ℓ ((ℓ : ℚ) ^ (wt x + wt y) * Phi (nodes n) (betaR n ℓ) (E x * E y)) 1 := by
  refine functional_bound _ _ _ _ _ _ fun k hk a1 a2 ha => ?_
  refine term_VB (VB_betaR h hk _ ha) (jet_lb h E hE1 hE2 x k a1 (by omega))
    (jet_lb h E hE1 hE2 y k a2 (by omega)) ?_
  have hx := x.2.isLt
  have hy := y.2.isLt
  unfold wt
  by_cases hp : Paired n ℓ k
  · have h1 := lb_paired x hp a1
    have h2 := lb_paired y hp a2
    rw [if_pos hp]
    split_ifs at h1 h2 <;> push_cast <;> omega
  · rw [if_neg hp, lb_single x hp, lb_single y hp]; omega

theorem Ga_bound (x y : HIdx n ℓ) :
    VB ℓ ((ℓ : ℚ) ^ (wt x + wt y) * Phi (nodes n) (alphaC n) (E x * E y)) 1 := by
  refine functional_bound _ _ _ _ _ _ fun k hk a1 a2 ha => ?_
  refine term_VB (VB_alpha h hk _) (jet_lb h E hE1 hE2 x k a1 (by omega))
    (jet_lb h E hE1 hE2 y k a2 (by omega)) ?_
  have hx := x.2.isLt
  have hy := y.2.isLt
  unfold wt
  by_cases hp : Paired n ℓ k
  · have h1 := lb_paired x hp a1
    have h2 := lb_paired y hp a2
    rw [if_pos hp]
    split_ifs at h1 h2 <;> push_cast <;> omega
  · rw [if_neg hp, lb_single x hp, lb_single y hp]; omega

/-- The `b^ℓ` terms over a set of nodes `s` avoiding the pairs of `x` or of `y` in the stated
way have `ω ≥ e`. -/
theorem Gh_bound_on (x y : HIdx n ℓ) (s : Finset ℤ) (hs : s ⊆ nodes n) (e : ℤ) (he : e ≤ 1)
    (hpair : ∀ k ∈ s, InPair n ℓ x k → InPair n ℓ y k → e ≤ 0) :
    VB ℓ ((ℓ : ℚ) ^ (wt x + wt y) * Phi s (betaL n ℓ) (E x * E y)) e := by
  refine functional_bound _ _ _ _ _ _ fun k hk a1 a2 ha => ?_
  refine term_VB (VB_betaL h (hs hk) _ ha) (jet_lb h E hE1 hE2 x k a1 (by omega))
    (jet_lb h E hE1 hE2 y k a2 (by omega)) ?_
  have hx := x.2.isLt
  have hy := y.2.isLt
  have hp' := hpair k hk
  unfold wt
  by_cases hp : Paired n ℓ k
  · have h1 := lb_paired x hp a1
    have h2 := lb_paired y hp a2
    rw [if_pos hp]
    split_ifs at h1 h2 with hx' hy'
    · have := hp' hx' hy'; push_cast; omega
    all_goals push_cast; omega
  · rw [if_neg hp, lb_single x hp, lb_single y hp]; omega

theorem Gh_int (x y : HIdx n ℓ) :
    VB ℓ ((ℓ : ℚ) ^ (wt x + wt y) * Phi (nodes n) (betaL n ℓ) (E x * E y)) 0 :=
  Gh_bound_on h E hE1 hE2 x y _ subset_rfl 0 (by norm_num) fun _ _ _ _ => le_rfl

theorem Gh_off (x y : HIdx n ℓ) (hxy : x.1 ≠ y.1) :
    VB ℓ ((ℓ : ℚ) ^ (wt x + wt y) * Phi (nodes n) (betaL n ℓ) (E x * E y)) 1 :=
  Gh_bound_on h E hE1 hE2 x y _ subset_rfl 1 le_rfl fun _ _ hx hy =>
    absurd (inPair_unique h hx hy) hxy

omit hℓ h hE2 in
/-- The jets of `E_{(i,a)}` at its own anchor. -/
theorem jet_own (i : ↥(anch n ℓ)) (a : Fin 4) (m : ℕ) (hm : m < 4) :
    Pjet (E ⟨i, a⟩) i m = if m = (a : ℕ) then 1 else 0 := by
  rw [hE1 _ i m hm]
  congr 1
  apply propext
  constructor
  · intro he
    have := congrArg (fun z : HIdx n ℓ => (z.2 : ℕ)) he
    simp only at this; omega
  · intro he
    subst he
    rfl

theorem Gh_diag (i : ↥(anch n ℓ)) (a b : Fin 4) :
    VB ℓ ((ℓ : ℚ) ^ (wt (⟨i, a⟩ : HIdx n ℓ) + wt (⟨i, b⟩ : HIdx n ℓ)) *
        Phi (nodes n) (betaL n ℓ) (E ⟨i, a⟩ * E ⟨i, b⟩) -
      2 * yA n ℓ i * Blocks.Lam (jType ℓ i) ((a : ℕ) + b)) 1 := by
  have ha4 := a.isLt
  have hb4 := b.isLt
  set P := E ⟨i, a⟩ * E ⟨i, b⟩ with hP
  have hJa := jet_own E hE1 i a
  have hJb := jet_own E hE1 i b
  -- the jets of `P` at the anchor
  have hint : ∀ m, VB ℓ (Pjet P i m) 0 := by
    intro m
    rw [hP, Pjet_mul]
    exact VB.sum _ _ fun ab _ => by
      simpa using (jet_int h E hE2 _ i ab.1).mul (jet_int h E hE2 _ i ab.2)
  have hlow : ∀ m < (a : ℕ) + b, Pjet P i m = 0 := by
    intro m hm
    exact Hankel2.W3.jet_mul_eq_zero _ _ _ a b m
      (fun m' hm' => by
        have := hJa m' (by omega); unfold Pjet PF.Pjet at this; rw [this, if_neg (by omega)])
      (fun m' hm' => by
        have := hJb m' (by omega); unfold Pjet PF.Pjet at this; rw [this, if_neg (by omega)]) hm
  have hs : Pjet P i ((a : ℕ) + b) = 1 := by
    rw [hP, Pjet_mul, Finset.sum_eq_single ((a : ℕ), (b : ℕ))]
    · simp only; rw [hJa a ha4, hJb b hb4, if_pos rfl, if_pos rfl, mul_one]
    · intro ab hab hne
      rw [Finset.mem_antidiagonal] at hab
      by_cases h1 : ab.1 < a
      · rw [hJa ab.1 (by omega), if_neg (by omega), zero_mul]
      · have h2 : ab.2 < b := by
          by_contra h2
          apply hne; ext <;> simp <;> omega
        rw [hJb ab.2 (by omega), if_neg (by omega), mul_zero]
    · intro hn; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hn
  have hmid : ∀ m, (a : ℕ) + b < m → m < 4 → Pjet P i m = 0 := by
    intro m hm1 hm2
    rw [hP, Pjet_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    rw [hJa ab.1 (by omega), hJb ab.2 (by omega)]
    split_ifs <;> first | omega | simp
  have hlead := pair_lead h i.2 P ((a : ℕ) + b) (by omega) hint hlow hs hmid
  -- split off the pair from the other nodes
  have hi : (i : ℤ) ∈ nodes n := anch_mem_nodes h i.2
  have hi' : (i : ℤ) - ℓ ∈ (nodes n).erase i := by
    refine Finset.mem_erase.mpr ⟨?_, anch_sub_mem_nodes h i.2⟩
    have := (Fact.out : ℓ.Prime).pos; omega
  have hsplit : Phi (nodes n) (betaL n ℓ) P =
      (∑ a ∈ range 4, betaL n ℓ i a * Pjet P i a +
        ∑ a ∈ range 4, betaL n ℓ (i - ℓ) a * Pjet P (i - ℓ) a) +
      Phi (((nodes n).erase i).erase (i - ℓ)) (betaL n ℓ) P := by
    unfold Phi
    rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi']
    ring
  have hrest := Gh_bound_on h E hE1 hE2 ⟨i, a⟩ ⟨i, b⟩ (((nodes n).erase i).erase (i - ℓ))
    (fun k hk => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)) 1 le_rfl
    (fun k hk hx _ => by
      exfalso
      obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hk
      obtain ⟨h3, _⟩ := Finset.mem_erase.mp h2
      rcases hx with hx | hx
      · exact h3 hx
      · exact h1 hx)
  have hw : wt (⟨i, a⟩ : HIdx n ℓ) + wt (⟨i, b⟩ : HIdx n ℓ) = (10 : ℤ) - ((a : ℕ) + b : ℕ) := by
    unfold wt; push_cast; ring
  rw [hsplit, mul_add, hw]
  rw [hw] at hrest
  have e : (ℓ : ℚ) ^ ((10 : ℤ) - ((a : ℕ) + b : ℕ)) *
        (∑ a ∈ range 4, betaL n ℓ i a * Pjet P i a +
          ∑ a ∈ range 4, betaL n ℓ (i - ℓ) a * Pjet P (i - ℓ) a) +
      (ℓ : ℚ) ^ ((10 : ℤ) - ((a : ℕ) + b : ℕ)) *
        Phi (((nodes n).erase i).erase (i - ℓ)) (betaL n ℓ) P -
      2 * yA n ℓ i * Blocks.Lam (jType ℓ i) ((a : ℕ) + b) =
      ((ℓ : ℚ) ^ ((10 : ℤ) - ((a : ℕ) + b : ℕ)) *
        (∑ a ∈ range 4, betaL n ℓ i a * Pjet P i a +
          ∑ a ∈ range 4, betaL n ℓ (i - ℓ) a * Pjet P (i - ℓ) a) -
        2 * yA n ℓ i * Blocks.Lam (jType ℓ i) ((a : ℕ) + b)) +
      (ℓ : ℚ) ^ ((10 : ℤ) - ((a : ℕ) + b : ℕ)) *
        Phi (((nodes n).erase i).erase (i - ℓ)) (betaL n ℓ) P := by ring
  rw [e]
  exact hlead.add hrest

end

end Zeta35.NV
