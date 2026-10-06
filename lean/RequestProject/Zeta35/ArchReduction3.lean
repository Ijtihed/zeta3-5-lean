import RequestProject.Zeta35.ArchTaylor3
import RequestProject.Zeta35.TreeBound
import RequestProject.Zeta7.Hankel2.ArchReduction

/-!
# The discrete reduction for `ζ₃(5)` (N, Theorem 4.1; W, Lemma 4.1; port of P, Lemma 6.2)

Port of `Hankel2.ArchB.lemma62` to the nodes `|k| ≤ R` of paper N.  We run the archimedean bound
over the double Cauchy–Binet expansion `Δ_K = ∑_{f,g} det E[:,f] · det C[f,g] · det E[:,g]`
(`Zeta35.hankelPoly_eq_sum`):

* `abs_det_Emat_le3`: `|det E[:,f]| ≤ exp(½ ∑_{u,v} s_u s_v ln(|u − v| + 2))`, `s = prof f`;
* `l1_det_Cbl_le3`: `‖det C[f,g]‖₁ ≤ 24^{2R+1} ∏_u (Q |h_u|)^{s_u}`, `Q = 2·10⁵ Λ³`;
* the kernel replacement `ln(|d| + 2) ≤ B(d) + 2/|d|` (`d ≠ 0`) with the harmonic estimate
  `sum_inv_node_le3`.

**`lemma62_3`**: if `E_B(s) ≤ M` for every profile `0 ≤ s_u ≤ 4`, `∑ s_u = K`, then
`‖Δ_K‖₁ ≤ exp(M + 𝓔(n, K))` with `𝓔(n,K) = K (ln Q + 16(1 + ln 2R) + 4 ln 2) + (2R+1)(ln 24 + 8 ln 2)`.
-/

open Polynomial Finset Matrix Hankel2

namespace Zeta35.Arch

variable {n K : ℕ}

/-- `h_u = H_u[0]` at the node `nodeOf n u`, as a real number. -/
noncomputable def hR3 (n : ℕ) (u : Fin (2 * R n + 1)) : ℝ := ((Hk n (nodeOf n u) 0 : ℚ) : ℝ)

/-- The discrete energy `E_B(s) = ∑_u s_u ln|h_u| + ∑_{u,v} s_u s_v B(u − v)`. -/
noncomputable def EB3 (n : ℕ) (s : Fin (2 * R n + 1) → ℝ) : ℝ :=
  ∑ u, s u * Real.log |hR3 n u| +
    ∑ u, ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v)

/-- `Q = 2·10⁵ Λ³`. -/
noncomputable def Qn3 (n : ℕ) : ℝ := 200000 * LamZ n ^ 3

/-- The error term `𝓔(n, K)`. -/
noncomputable def errR3 (n K : ℕ) : ℝ :=
  K * (Real.log (Qn3 n) + 16 * (1 + Real.log (2 * R n)) + 4 * Real.log 2) +
    (2 * R n + 1) * (Real.log 24 + 8 * Real.log 2)

theorem Qn3_pos (n : ℕ) : 0 < Qn3 n := by
  unfold Qn3; have := one_le_LamZ n; positivity

theorem sum_nodeF_real3 (f : Fin K → Idx n) (G : Fin (2 * R n + 1) → ℝ) :
    ∑ c, G (nodeF f c) = ∑ u, (prof f u : ℝ) * G u := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := nodeF f) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const, nsmul_eq_mul, prof]

/-- `G(u, v) = ln(|u − v| + 2)`. -/
noncomputable def Gk3 (n : ℕ) (u v : Fin (2 * R n + 1)) : ℝ :=
  Real.log (|((nodeOf n u : ℝ) - nodeOf n v)| + 2)

theorem abs_det_Emat_le3 (f : Fin K → Idx n) :
    |((((Emat n K).submatrix id f).det : ℚ) : ℝ)| ≤
      Real.exp ((∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk3 n u v) / 2) := by
  set x : Fin K → ℝ := fun c => -((nodeOf n (nodeF f c) : ℤ) : ℝ) with hx
  have hdet : ((((Emat n K).submatrix id f).det : ℚ) : ℝ) =
      (Matrix.of fun (i c : Fin K) => (((i : ℕ).choose (ordF f c : ℕ) : ℕ) : ℝ) *
        x c ^ ((i : ℕ) - (ordF f c : ℕ))).det := by
    have := RingHom.map_det (Rat.castHom ℝ) ((Emat n K).submatrix id f)
    simp only [Rat.coe_castHom] at this
    rw [this]
    congr 1
    ext i c
    simp [Emat, hx, nodeF, ordF]
  rw [hdet]
  refine (ArchB.abs_det_confluent_le x (fun c => (ordF f c : ℕ))).trans ?_
  have hpos : ∀ c c', 0 < |x c' - x c| + 2 := fun _ _ => by positivity
  have hprod : ∏ c, ∏ c' ∈ Ioi c, (|x c' - x c| + 2) =
      Real.exp (∑ c, ∑ c' ∈ Ioi c, Real.log (|x c' - x c| + 2)) := by
    rw [Real.exp_sum]
    refine prod_congr rfl fun c _ => ?_
    rw [Real.exp_sum]
    refine prod_congr rfl fun c' _ => ?_
    rw [Real.exp_log (hpos c c')]
  rw [hprod, Real.exp_le_exp]
  have hx' : ∀ c c', |x c' - x c| = |((nodeOf n (nodeF f c) : ℝ)) - nodeOf n (nodeF f c')| := by
    intro c c'
    simp only [hx]
    congr 1; ring
  have hsym := ArchB.sym_sum_Ioi_le (fun c c' => Real.log (|x c' - x c| + 2))
    (fun c c' => by simp only; rw [abs_sub_comm])
    (fun c => Real.log_nonneg (by simp))
  have hfull : ∑ c, ∑ c', Real.log (|x c' - x c| + 2) =
      ∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk3 n u v := by
    simp_rw [hx']
    rw [sum_nodeF_real3 f (fun u => ∑ c', Real.log (|((nodeOf n u : ℝ)) - nodeOf n (nodeF f c')| + 2))]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_nodeF_real3 f (fun v => Real.log (|((nodeOf n u : ℝ)) - nodeOf n v| + 2)), mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [Gk3]; ring
  linarith

theorem l1_det_Cbl_le3 {f g : Fin K → Idx n} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : prof f = prof g) :
    l1 ((Cbl n).submatrix f g).det ≤
      24 ^ (2 * R n + 1) * ∏ u, (Qn3 n * |hR3 n u|) ^ prof f u := by
  have hnode := nodeF_eq_of_prof_eq hf hg hfg
  have hbt : ((Cbl n).submatrix f g).BlockTriangular (nodeF f) := by
    intro c d hcd
    simp only [submatrix_apply, Cbl]
    rw [if_neg]
    intro h
    have h' : nodeF f c = nodeF g d := h
    rw [← hnode] at h'
    exact absurd h' (ne_of_gt hcd)
  rw [hbt.det]
  have hA : ∀ u, 0 ≤ Qn3 n * |hR3 n u| := fun u => mul_nonneg (Qn3_pos n).le (abs_nonneg _)
  have hblock : ∀ u, l1 (((Cbl n).submatrix f g).toSquareBlock (nodeF f) u).det ≤
      24 * (Qn3 n * |hR3 n u|) ^ prof f u := by
    intro u
    have hcard : Fintype.card {c // nodeF f c = u} = prof f u := by
      rw [Fintype.card_subtype]; rfl
    refine (ArchB.l1_det_le _ (Qn3 n * |hR3 n u|) fun c d => ?_).trans ?_
    · show l1 (Cbl n (f c) (g d)) ≤ _
      simp only [Cbl]
      split_ifs with h
      · have hc : (ofLex (f c)).1 = u := c.2
        rw [hc]
        exact l1_cPoly_le n _ _
      · rw [ArchB.l1_zero]; exact hA u
    · rw [hcard]
      have h4 := prof_le_four hf u
      have : ((prof f u).factorial : ℝ) ≤ 24 := by
        have : (prof f u).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le h4
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right this (pow_nonneg (hA u) _)
  refine (ArchB.l1_prod_le _ _).trans ?_
  calc ∏ u ∈ univ.image (nodeF f), l1 (((Cbl n).submatrix f g).toSquareBlock (nodeF f) u).det
      ≤ ∏ u ∈ univ.image (nodeF f), 24 * (Qn3 n * |hR3 n u|) ^ prof f u :=
        prod_le_prod (fun _ _ => ArchB.l1_nonneg _) (fun u _ => hblock u)
    _ = 24 ^ (univ.image (nodeF f)).card *
          ∏ u ∈ univ.image (nodeF f), (Qn3 n * |hR3 n u|) ^ prof f u := by
        rw [prod_mul_distrib, prod_const]
    _ ≤ 24 ^ (2 * R n + 1) * ∏ u, (Qn3 n * |hR3 n u|) ^ prof f u := by
        refine mul_le_mul ?_ (le_of_eq ?_) (prod_nonneg fun u _ => pow_nonneg (hA u) _)
          (by positivity)
        · refine pow_le_pow_right₀ (by norm_num) ?_
          exact (card_le_univ _).trans (by simp)
        · refine prod_subset (subset_univ _) fun u _ hu => ?_
          have : prof f u = 0 := by
            rw [prof, card_eq_zero, filter_eq_empty_iff]
            intro c _ hc
            exact hu (mem_image.2 ⟨c, mem_univ _, hc⟩)
          rw [this, pow_zero]

theorem Hk_zero_ne_zero3 (n : ℕ) (k : ℤ) : Hk n k 0 ≠ 0 := by
  unfold Hk
  rw [Hk_zero_eq]
  refine prod_ne_zero_iff.2 fun k' hk' => pow_ne_zero _ (inv_ne_zero ?_)
  exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk')

theorem hR3_ne_zero (n : ℕ) (u : Fin (2 * R n + 1)) : hR3 n u ≠ 0 := by
  unfold hR3; exact_mod_cast Hk_zero_ne_zero3 n _

/-! ### The harmonic estimate over the nodes `|k| ≤ R` -/

theorem sum_inv_dist_left_le3 (n : ℕ) (k : ℤ) (hk : k ∈ nodes n) :
    ∑ m ∈ (nodes n).filter (· < k), 1 / (((k - m : ℤ)) : ℝ) ≤ 1 + Real.log (2 * R n) := by
  simp only [nodes, mem_Icc] at hk
  set A := (nodes n).filter (· < k)
  have hinj : Set.InjOn (fun m : ℤ => (k - m - 1).toNat) A := by
    intro x hx y hy hxy
    simp only [A, nodes, coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    omega
  have e : ∑ m ∈ A, 1 / (((k - m : ℤ)) : ℝ) =
      ∑ m ∈ A, 1 / ((((k - m - 1).toNat : ℕ) : ℝ) + 1) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [A, nodes, mem_filter, mem_Icc] at hm
    congr 1
    have : ((k - m - 1).toNat : ℤ) = k - m - 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((k - m - 1).toNat : ℕ) : ℝ) = ((k - m - 1 : ℤ) : ℝ) := by exact_mod_cast this
    rw [h']; push_cast; ring
  rw [e, ← sum_image (g := fun m : ℤ => (k - m - 1).toNat) (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) hinj]
  have hsub : A.image (fun m : ℤ => (k - m - 1).toNat) ⊆ range (2 * R n) := by
    intro i hi
    simp only [A, nodes, mem_image, mem_filter, mem_Icc, mem_range] at hi ⊢
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
  rw [← LemmaB.harmonic_real_eq]
  exact harmonic_le_one_add_log _ |>.trans (by push_cast; exact le_refl _)

theorem sum_inv_dist_right_le3 (n : ℕ) (k : ℤ) (hk : k ∈ nodes n) :
    ∑ m ∈ (nodes n).filter (k < ·), 1 / (((m - k : ℤ)) : ℝ) ≤ 1 + Real.log (2 * R n) := by
  simp only [nodes, mem_Icc] at hk
  set A := (nodes n).filter (k < ·)
  have hinj : Set.InjOn (fun m : ℤ => (m - k - 1).toNat) A := by
    intro x hx y hy hxy
    simp only [A, nodes, coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at hxy
    omega
  have e : ∑ m ∈ A, 1 / (((m - k : ℤ)) : ℝ) =
      ∑ m ∈ A, 1 / ((((m - k - 1).toNat : ℕ) : ℝ) + 1) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [A, nodes, mem_filter, mem_Icc] at hm
    congr 1
    have : ((m - k - 1).toNat : ℤ) = m - k - 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((m - k - 1).toNat : ℕ) : ℝ) = ((m - k - 1 : ℤ) : ℝ) := by exact_mod_cast this
    rw [h']; push_cast; ring
  rw [e, ← sum_image (g := fun m : ℤ => (m - k - 1).toNat) (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) hinj]
  have hsub : A.image (fun m : ℤ => (m - k - 1).toNat) ⊆ range (2 * R n) := by
    intro i hi
    simp only [A, nodes, mem_image, mem_filter, mem_Icc, mem_range] at hi ⊢
    obtain ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hi
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
  rw [← LemmaB.harmonic_real_eq]
  exact harmonic_le_one_add_log _ |>.trans (by push_cast; exact le_refl _)

/-- **Harmonic estimate**: `∑_{m ≠ k} 1/|k − m| ≤ 2(1 + ln 2R)` over the nodes `|m| ≤ R`. -/
theorem sum_inv_dist_le3 (n : ℕ) (k : ℤ) (hk : k ∈ nodes n) :
    ∑ m ∈ (nodes n).erase k, 1 / |(((k - m : ℤ)) : ℝ)| ≤ 2 * (1 + Real.log (2 * R n)) := by
  have hsplit : ∑ m ∈ (nodes n).erase k, 1 / |(((k - m : ℤ)) : ℝ)| =
      ∑ m ∈ (nodes n).filter (· < k), 1 / |(((k - m : ℤ)) : ℝ)| +
        ∑ m ∈ (nodes n).filter (k < ·), 1 / |(((k - m : ℤ)) : ℝ)| := by
    rw [← sum_filter_add_sum_filter_not ((nodes n).erase k) (· < k)]
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext m; simp only [mem_filter, mem_erase]; constructor
      · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'⟩
    · refine sum_congr ?_ fun _ _ => rfl
      ext m; simp only [mem_filter, mem_erase, not_lt]; constructor
      · rintro ⟨⟨h0, h⟩, h'⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'.le⟩
  rw [hsplit]
  have h1 : ∑ m ∈ (nodes n).filter (· < k), 1 / |(((k - m : ℤ)) : ℝ)| =
      ∑ m ∈ (nodes n).filter (· < k), 1 / (((k - m : ℤ)) : ℝ) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter] at hm
    rw [abs_of_pos (by exact_mod_cast (show (0 : ℤ) < k - m by omega))]
  have h2 : ∑ m ∈ (nodes n).filter (k < ·), 1 / |(((k - m : ℤ)) : ℝ)| =
      ∑ m ∈ (nodes n).filter (k < ·), 1 / (((m - k : ℤ)) : ℝ) := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_filter] at hm
    rw [abs_of_neg (by exact_mod_cast (show k - m < 0 by omega))]
    push_cast; ring_nf
  rw [h1, h2]
  linarith [sum_inv_dist_left_le3 n k hk, sum_inv_dist_right_le3 n k hk]

/-- `∑_v 1/|u − v| ≤ 2(1 + ln 2R)` over the nodes. -/
theorem sum_inv_node_le3 (n : ℕ) (u : Fin (2 * R n + 1)) :
    ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| ≤ 2 * (1 + Real.log (2 * R n)) := by
  have h := sum_inv_dist_le3 n (nodeOf n u) (nodeOf_mem_nodes n u)
  rw [← sum_nodes_eq n (fun m => 1 / |((nodeOf n u : ℝ) - m)|)]
  rw [← add_sum_erase _ _ (nodeOf_mem_nodes n u)]
  simp only [sub_self, abs_zero, div_zero, zero_add]
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun m _ => ?_
  push_cast; rfl

/-- The Vandermonde exponent against the energy. -/
theorem sum_Gk_le3 (s : Fin (2 * R n + 1) → ℝ) (hs0 : ∀ u, 0 ≤ s u) (hs4 : ∀ u, s u ≤ 4) :
    ∑ u, ∑ v, s u * s v * Gk3 n u v ≤
      ∑ u, ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        (∑ u, s u) * (16 * (1 + Real.log (2 * R n)) + 4 * Real.log 2) := by
  rw [sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun u _ => ?_
  have hterm : ∀ v, s u * s v * Gk3 n u v ≤
      s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
      s u * (8 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then 4 * Real.log 2 else 0)) := by
    intro v
    have h := ArchB.log_add_two_le ((nodeOf n u : ℝ) - nodeOf n v)
    have hsuv : 0 ≤ s u * s v := mul_nonneg (hs0 u) (hs0 v)
    have e : (((nodeOf n u : ℝ) - nodeOf n v) = 0) ↔ u = v := by
      constructor
      · intro h0
        exact nodeOf_injective n (by exact_mod_cast sub_eq_zero.1 h0)
      · rintro rfl; simp
    have hG : s u * s v * Gk3 n u v ≤ s u * s v * (ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then Real.log 2 else 0)) := by
      unfold Gk3
      refine mul_le_mul_of_nonneg_left ?_ hsuv
      have := h
      simp only [e] at this
      exact this
    have hinv : 0 ≤ 1 / |((nodeOf n u : ℝ) - nodeOf n v)| := by positivity
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : s u * s v * (2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) ≤
        s u * (8 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) := by
      have : s v * 2 ≤ 8 := by linarith [hs4 v]
      have hx : 0 ≤ s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) := mul_nonneg (hs0 u) hinv
      calc s u * s v * (2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) =
          (s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) * (s v * 2) := by ring
        _ ≤ (s u * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|)) * 8 :=
          mul_le_mul_of_nonneg_left this hx
        _ = _ := by ring
    have h2 : s u * s v * (if u = v then Real.log 2 else 0) ≤
        s u * (if u = v then 4 * Real.log 2 else 0) := by
      split_ifs
      · have hx : 0 ≤ s u * Real.log 2 := mul_nonneg (hs0 u) hl2
        calc s u * s v * Real.log 2 = (s u * Real.log 2) * s v := by ring
          _ ≤ (s u * Real.log 2) * 4 := mul_le_mul_of_nonneg_left (hs4 v) hx
          _ = _ := by ring
      · simp
    nlinarith
  calc ∑ v, s u * s v * Gk3 n u v ≤ ∑ v, (s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (8 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
          (if u = v then 4 * Real.log 2 else 0))) := sum_le_sum fun v _ => hterm v
    _ = ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (8 * ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| + 4 * Real.log 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _)]
    _ ≤ ∑ v, s u * s v * ArchB.Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (16 * (1 + Real.log (2 * R n)) + 4 * Real.log 2) := by
        have := sum_inv_node_le3 n u
        have := hs0 u
        nlinarith

/-! ### The discrete reduction -/

/-- **Discrete reduction (port of P, Lemma 6.2).**  If `E_B(s) ≤ M` for every profile
`0 ≤ s_u ≤ 4`, `∑ s_u = K`, then `‖Δ_K‖₁ ≤ exp(M + 𝓔(n, K))`. -/
theorem lemma62_3 (M : ℝ)
    (hM : ∀ s ∈ profiles n K, EB3 n (fun u => (s u : ℝ)) ≤ M) :
    l1 (hankelPoly n K) ≤ Real.exp (M + errR3 n K) := by
  set T := Real.exp (M + K * (Real.log (Qn3 n) + 16 * (1 + Real.log (2 * R n)) + 4 * Real.log 2) +
    (2 * R n + 1) * Real.log 24) with hT
  have hQ : 0 < Qn3 n := Qn3_pos n
  have hterm : ∀ f ∈ smSet K (Idx n), ∀ g ∈ smSet K (Idx n),
      l1 (C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
        C ((Emat n K).submatrix id g).det) ≤ T := by
    intro f hf g hg
    rw [mem_smSet] at hf hg
    refine (ArchB.l1_C_mul_mul_C_le _ _ _).trans ?_
    by_cases hfg : prof f = prof g
    · set s : Fin (2 * R n + 1) → ℝ := fun u => (prof f u : ℝ) with hs
      have hs0 : ∀ u, 0 ≤ s u := fun u => by positivity
      have hs4 : ∀ u, s u ≤ 4 := fun u => by
        simp only [hs]; exact_mod_cast prof_le_four hf u
      have hsK : ∑ u, s u = K := by simp only [hs]; exact_mod_cast sum_prof f
      have hE1 := abs_det_Emat_le3 f
      have hE2 := abs_det_Emat_le3 g
      rw [← hfg] at hE2
      have hC := l1_det_Cbl_le3 hf hg hfg
      have hprod : ∏ u, (Qn3 n * |hR3 n u|) ^ prof f u =
          Real.exp (∑ u, s u * (Real.log (Qn3 n) + Real.log |hR3 n u|)) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun u _ => ?_
        have hpos : 0 < Qn3 n * |hR3 n u| := mul_pos hQ (abs_pos.2 (hR3_ne_zero n u))
        rw [← Real.log_mul hQ.ne' (abs_pos.2 (hR3_ne_zero n u)).ne', mul_comm (s u), Real.exp_mul,
          Real.exp_log hpos, hs, Real.rpow_natCast]
      rw [hprod] at hC
      have h24 : (24 : ℝ) ^ (2 * R n + 1) = Real.exp ((2 * R n + 1) * Real.log 24) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        push_cast; ring_nf
      rw [h24] at hC
      have hEB := hM (prof f) (prof_mem_profiles hf)
      have hG := sum_Gk_le3 s hs0 hs4
      rw [hsK] at hG
      unfold EB3 at hEB
      set S2 := ∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk3 n u v
      calc |(((Emat n K).submatrix id f).det : ℝ)| * l1 ((Cbl n).submatrix f g).det *
            |(((Emat n K).submatrix id g).det : ℝ)|
          ≤ Real.exp (S2 / 2) *
            (Real.exp ((2 * R n + 1) * Real.log 24) *
              Real.exp (∑ u, s u * (Real.log (Qn3 n) + Real.log |hR3 n u|))) *
            Real.exp (S2 / 2) := by
            refine mul_le_mul (mul_le_mul hE1 hC (ArchB.l1_nonneg _) (Real.exp_pos _).le) hE2
              (abs_nonneg _) (by positivity)
        _ = Real.exp (S2 + (2 * R n + 1) * Real.log 24 + K * Real.log (Qn3 n) +
              ∑ u, s u * Real.log |hR3 n u|) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [mul_add, sum_add_distrib, ← sum_mul, hsK]
            ring
        _ ≤ T := by
            rw [hT, Real.exp_le_exp]
            simp only [hs] at hG
            linarith
    · rw [det_cbl_eq_zero_of_prof_ne hfg, ArchB.l1_zero, mul_zero, zero_mul]
      exact (Real.exp_pos _).le
  rw [hankelPoly_eq_sum]
  refine (ArchB.l1_sum_le _ _).trans ?_
  have hcard := ArchB.card_smSet_le K (Idx n)
  have hcardI : Fintype.card (Idx n) = 4 * (2 * R n + 1) := by
    simp [Idx, Fintype.card_prod, mul_comm]
  rw [hcardI] at hcard
  calc ∑ f ∈ smSet K (Idx n), l1 (∑ g ∈ smSet K (Idx n),
        C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
          C ((Emat n K).submatrix id g).det)
      ≤ ∑ _f ∈ smSet K (Idx n), ∑ _g ∈ smSet K (Idx n), T :=
        sum_le_sum fun f hf => (ArchB.l1_sum_le _ _).trans (sum_le_sum fun g hg => hterm f hf g hg)
    _ = ((smSet K (Idx n)).card : ℝ) ^ 2 * T := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ ((2 : ℝ) ^ (4 * (2 * R n + 1))) ^ 2 * T := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) (Real.exp_pos _).le
        exact_mod_cast hcard
    _ = Real.exp (M + errR3 n K) := by
        rw [hT, errR3, ← pow_mul]
        have : (2 : ℝ) ^ (4 * (2 * R n + 1) * 2) =
            Real.exp ((2 * R n + 1) * (8 * Real.log 2)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
          push_cast; ring_nf
        rw [this, ← Real.exp_add]
        congr 1; ring

end Zeta35.Arch
