import RequestProject.Zeta35.TreeBlock
import RequestProject.Zeta35.TreePenalty
import RequestProject.Zeta7.Hankel2.ConfluentVdm

/-!
# Tree bound, step 4: the confluent Vandermonde minors `det E[:, f]` (paper N, §5; P, §7)

Port of `RequestProject/Zeta7/Hankel2/LemmaTVdm.lean` to the nodes `|k| ≤ R`: the unit assignment
`|det E[:, f]|_ℓ ≤ ℓ^{Z_f}` (`norm_det_Emat_le`) and the exponent identity (`two_Zf`).
-/

open Polynomial Finset Matrix

namespace Zeta35

open Hankel2

variable {n K : ℕ}

/-- `λ_p` at the node `u`. -/
noncomputable def lam (p n : ℕ) (u : Fin (2 * R n + 1)) : ℕ := lambdaP p n (nodeOf n u)

/-- The pair exponents of the unit assignment. -/
noncomputable def eF (p : ℕ) (f : Fin K → Idx n) (c c' : Fin K) : ℕ :=
  if nodeF f c = nodeF f c' then lam p n (nodeF f c)
  else padicValInt p (nodeOf n (nodeF f c) - nodeOf n (nodeF f c'))

/-- `Z_f = ∑_c b_c λ_p(k_c) − ∑_{c<c'} e_{cc'}`. -/
noncomputable def Zf (p : ℕ) (f : Fin K → Idx n) : ℤ :=
  ((∑ c, (ordF f c : ℕ) * lam p n (nodeF f c) : ℕ) : ℤ) -
    ((∑ c, ∑ c' ∈ Ioi c, eF p f c c' : ℕ) : ℤ)

theorem nodeOf_mem_nodes (n : ℕ) (u : Fin (2 * R n + 1)) : nodeOf n u ∈ nodes n := by
  simp only [nodes, mem_Icc, nodeOf]
  have := u.isLt
  omega

theorem nodeOf_injective (n : ℕ) : Function.Injective (nodeOf n) := by
  intro u v h
  simp only [nodeOf] at h
  exact Fin.ext (by omega)

theorem padicValInt_sub_comm (p : ℕ) (a b : ℤ) : padicValInt p (a - b) = padicValInt p (b - a) := by
  rw [← neg_sub, padicValInt, padicValInt, Int.natAbs_neg]

theorem padicVal_le_lam (p n : ℕ) {u v : Fin (2 * R n + 1)} (h : u ≠ v) :
    padicValInt p (nodeOf n u - nodeOf n v) ≤ lam p n u := by
  unfold lam lambdaP
  exact le_sup (f := fun m => padicValInt p (nodeOf n u - m))
    (mem_erase.2 ⟨fun h' => h (nodeOf_injective n h').symm, nodeOf_mem_nodes n v⟩)

theorem inv_pow_eq_zpow (p : ℕ) (e : ℕ) : ((p : ℝ)⁻¹) ^ e = (p : ℝ) ^ (-(e : ℤ)) := by
  rw [inv_pow, _root_.zpow_neg, zpow_natCast]

/-- **The Vandermonde bound** `|det E[:, f]|_p ≤ p^{Z_f}`. -/
theorem norm_det_Emat_le (p : ℕ) [hp : Fact p.Prime] (f : Fin K → Idx n) :
    ‖((((Emat n K).submatrix id f).det : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ Zf p f := by
  set x : Fin K → ℚ_[p] := fun c => (((-((nodeOf n (nodeF f c) : ℤ) : ℚ)) : ℚ) : ℚ_[p]) with hx
  have hdet : ((((Emat n K).submatrix id f).det : ℚ) : ℚ_[p]) =
      (Matrix.of fun (i c : Fin K) => (((i : ℕ).choose (ordF f c : ℕ) : ℕ) : ℚ_[p]) *
        x c ^ ((i : ℕ) - (ordF f c : ℕ))).det := by
    have := RingHom.map_det (Rat.castHom ℚ_[p]) ((Emat n K).submatrix id f)
    simp only [Rat.coe_castHom] at this
    rw [this]
    congr 1
  have key := norm_det_confluent_le x (fun c => (ordF f c : ℕ)) (fun c => lam p n (nodeF f c))
    (eF p f) (fun c c' _ => ?_) (fun c c' _ => ?_)
  rotate_left
  · -- the node differences
    have hdiff : x c' - x c = (((nodeOf n (nodeF f c) - nodeOf n (nodeF f c') : ℤ) : ℚ) : ℚ_[p]) := by
      simp only [hx]; push_cast; ring
    rw [hdiff]
    unfold eF
    split_ifs with h
    · rw [h, sub_self]; simp
    · rw [inv_pow_eq_zpow]
      have := (Padic.norm_int_le_pow_iff_dvd (p := p)
        (nodeOf n (nodeF f c) - nodeOf n (nodeF f c'))
        (padicValInt p (nodeOf n (nodeF f c) - nodeOf n (nodeF f c')))).2
        (padicValInt_dvd _)
      simpa using this
  · unfold eF
    split_ifs with h
    · exact ⟨le_rfl, by rw [h]⟩
    · refine ⟨padicVal_le_lam p n h, ?_⟩
      rw [padicValInt_sub_comm]
      exact padicVal_le_lam p n (Ne.symm h)
  rw [← hdet] at key
  rw [inv_pow_eq_zpow, inv_pow_eq_zpow] at key
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [Zf, sub_eq_add_neg, zpow_add₀ hp0.ne']
  set B := ((∑ c, (ordF f c : ℕ) * lam p n (nodeF f c) : ℕ) : ℤ)
  set E := ((∑ c, ∑ c' ∈ Ioi c, eF p f c c' : ℕ) : ℤ)
  set D := ‖((((Emat n K).submatrix id f).det : ℚ) : ℚ_[p])‖
  calc D = D * (p : ℝ) ^ (-B) * (p : ℝ) ^ B := by
        rw [mul_assoc, ← zpow_add₀ hp0.ne', neg_add_cancel, zpow_zero, mul_one]
    _ ≤ (p : ℝ) ^ (-E) * (p : ℝ) ^ B := mul_le_mul_of_nonneg_right key (zpow_pos hp0 _).le
    _ = (p : ℝ) ^ B * (p : ℝ) ^ (-E) := mul_comm _ _

/-! ### The exponent identity -/

theorem sym_sum_Ioi {K : ℕ} (h : Fin K → Fin K → ℤ) (hs : ∀ c c', h c c' = h c' c) :
    2 * ∑ c, ∑ c' ∈ Ioi c, h c c' = ∑ c, ∑ c', h c c' - ∑ c, h c c := by
  have e1 : ∀ c, ∑ c', h c c' = ∑ c' ∈ Iio c, h c c' + h c c + ∑ c' ∈ Ioi c, h c c' := by
    intro c
    have hpt : ∀ c', h c c' = (if c' < c then h c c' else 0) + (if c = c' then h c c' else 0) +
        (if c < c' then h c c' else 0) := by
      intro c'
      rcases lt_trichotomy c' c with hlt | heq | hgt
      · simp [hlt, hlt.ne', not_lt.2 hlt.le]
      · subst heq; simp
      · simp [hgt, hgt.ne, not_lt.2 hgt.le]
    rw [sum_congr rfl fun c' _ => hpt c', sum_add_distrib, sum_add_distrib, sum_ite_eq,
      if_pos (mem_univ c), ← sum_filter, ← sum_filter,
      show univ.filter (fun c' => c' < c) = Iio c by ext; simp,
      show univ.filter (fun c' => c < c') = Ioi c by ext; simp]
  have e2 : ∑ c, ∑ c' ∈ Iio c, h c c' = ∑ c, ∑ c' ∈ Ioi c, h c c' := by
    rw [sum_comm' (s' := fun c' => Ioi c') (t' := univ)]
    · refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => hs _ _
    · intro c c'; simp
  rw [sum_congr rfl fun c _ => e1 c, sum_add_distrib, sum_add_distrib, e2]
  ring

theorem sum_nodeF (f : Fin K → Idx n) (G : Fin (2 * R n + 1) → ℤ) :
    ∑ c, G (nodeF f c) = ∑ u, (prof f u : ℤ) * G u := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := nodeF f) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const, nsmul_eq_mul, prof]

theorem two_mul_choose_two (s : ℕ) : 2 * ((s.choose 2 : ℕ) : ℤ) = s * s - s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · have h1 : 2 * s.choose 2 = s * (s - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd
    have h2 : ((2 * s.choose 2 : ℕ) : ℤ) = ((s * (s - 1) : ℕ) : ℤ) := by rw [h1]
    push_cast [Nat.cast_sub hs] at h2
    linarith

theorem eF_eq (p : ℕ) (f : Fin K → Idx n) (c c' : Fin K) :
    (eF p f c c' : ℤ) = (if nodeF f c = nodeF f c' then (lam p n (nodeF f c) : ℤ) else 0) +
      (padicValInt p (nodeOf n (nodeF f c) - nodeOf n (nodeF f c')) : ℤ) := by
  unfold eF
  split_ifs with h
  · rw [h, sub_self]; simp
  · simp

/-- **The exponent identity** `2 Z_f = 2 ∑_u λ_p(u) ℓ_u(f) − ∑_{k,m} s_k s_m v_p(k − m)`. -/
theorem two_Zf (p : ℕ) {f : Fin K → Idx n} (hf : StrictMono f) :
    2 * Zf p f = 2 * ∑ u, (lam p n u : ℤ) * (ellCol f u : ℤ) - pairSum p n (prof f) := by
  set s := prof f
  -- the first sum
  have hA : ((∑ c, (ordF f c : ℕ) * lam p n (nodeF f c) : ℕ) : ℤ) =
      ∑ u, (lam p n u : ℤ) * ((ellCol f u : ℤ) + ((s u).choose 2 : ℕ)) := by
    push_cast
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := nodeF f) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], ← sum_mul]
    have := sum_ordF_eq hf u
    have h' : ((∑ c ∈ univ.filter (fun c => nodeF f c = u), (ordF f c : ℕ) : ℕ) : ℤ) =
        ((ellCol f u + (prof f u).choose 2 : ℕ) : ℤ) := by rw [this]
    push_cast at h'
    rw [h']; ring
  -- the pair sum
  have hE : 2 * ((∑ c, ∑ c' ∈ Ioi c, eF p f c c' : ℕ) : ℤ) =
      ∑ u, ((s u : ℤ) * ((s u : ℤ) * (lam p n u : ℤ)) - (s u : ℤ) * (lam p n u : ℤ)) +
        pairSum p n s := by
    push_cast
    have hdiag : ∑ c, (eF p f c c : ℤ) = ∑ u, (s u : ℤ) * (lam p n u : ℤ) := by
      simp only [eF, if_true]
      exact sum_nodeF f (fun u => (lam p n u : ℤ))
    rw [sym_sum_Ioi (fun c c' => (eF p f c c' : ℤ)) (fun c c' => by
      show (eF p f c c' : ℤ) = eF p f c' c
      rw [eF_eq, eF_eq, padicValInt_sub_comm]
      by_cases h : nodeF f c = nodeF f c'
      · rw [if_pos h, if_pos h.symm, h]
      · rw [if_neg h, if_neg (Ne.symm h)]), hdiag]
    simp_rw [eF_eq, sum_add_distrib]
    have h1 : ∀ c, ∑ c', (if nodeF f c = nodeF f c' then (lam p n (nodeF f c) : ℤ) else 0) =
        (s (nodeF f c) : ℤ) * (lam p n (nodeF f c) : ℤ) := by
      intro c
      rw [sum_nodeF f (fun u' => if nodeF f c = u' then (lam p n (nodeF f c) : ℤ) else 0)]
      simp [s]
    have h2 : ∀ c, ∑ c', (padicValInt p (nodeOf n (nodeF f c) - nodeOf n (nodeF f c')) : ℤ) =
        ∑ u', (s u' : ℤ) * (padicValInt p (nodeOf n (nodeF f c) - nodeOf n u') : ℤ) := by
      intro c
      exact sum_nodeF f (fun u' => (padicValInt p (nodeOf n (nodeF f c) - nodeOf n u') : ℤ))
    simp_rw [h1, h2]
    rw [sum_nodeF f (fun u => (s u : ℤ) * (lam p n u : ℤ)),
      sum_nodeF f (fun u => ∑ u', (s u' : ℤ) * (padicValInt p (nodeOf n u - nodeOf n u') : ℤ)),
      pairSum, sum_sub_distrib]
    simp only [mul_sum]
    push_cast
    have h3 : ∑ i, ∑ i', (s i : ℤ) * ((s i' : ℤ) * (padicValInt p (nodeOf n i - nodeOf n i') : ℤ)) =
        ∑ i, ∑ i', (s i : ℤ) * (s i' : ℤ) * (padicValInt p (nodeOf n i - nodeOf n i') : ℤ) :=
      sum_congr rfl fun i _ => sum_congr rfl fun i' _ => by ring
    rw [h3]
    ring
  calc 2 * Zf p f = 2 * ((∑ c, (ordF f c : ℕ) * lam p n (nodeF f c) : ℕ) : ℤ) -
        2 * ((∑ c, ∑ c' ∈ Ioi c, eF p f c c' : ℕ) : ℤ) := by rw [Zf]; ring
    _ = ∑ u, 2 * ((lam p n u : ℤ) * ((ellCol f u : ℤ) + ((s u).choose 2 : ℕ))) -
        (∑ u, ((s u : ℤ) * ((s u : ℤ) * (lam p n u : ℤ)) - (s u : ℤ) * (lam p n u : ℤ)) +
          pairSum p n s) := by rw [hA, hE, mul_sum]
    _ = ∑ u, (2 * ((lam p n u : ℤ) * (ellCol f u : ℤ)) +
          ((s u : ℤ) * ((s u : ℤ) * (lam p n u : ℤ)) - (s u : ℤ) * (lam p n u : ℤ))) -
        (∑ u, ((s u : ℤ) * ((s u : ℤ) * (lam p n u : ℤ)) - (s u : ℤ) * (lam p n u : ℤ)) +
          pairSum p n s) := by
        congr 1
        refine sum_congr rfl fun u _ => ?_
        have := two_mul_choose_two (s u)
        linear_combination (lam p n u : ℤ) * this
    _ = 2 * ∑ u, (lam p n u : ℤ) * (ellCol f u : ℤ) - pairSum p n s := by
        rw [sum_add_distrib, mul_sum]; ring

end Zeta35
