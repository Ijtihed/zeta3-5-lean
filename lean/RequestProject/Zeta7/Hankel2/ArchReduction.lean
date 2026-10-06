import RequestProject.Zeta7.Hankel2.ArchVdm
import RequestProject.Zeta7.Hankel2.ArchTaylor
import RequestProject.Zeta7.Hankel2.LemmaT
import RequestProject.Zeta7.Hankel2.LemmaB62

/-!
# Paper Lemma 6.2 (discrete reduction): `ln ‖Δ_K‖₁ ≤ max_s E_B(s) + 𝓔_n`

We run the archimedean bound over the double Cauchy–Binet expansion
`Δ_K = ∑_{f,g} det E[:,f] · det C[f,g] · det E[:,g]` (`Fam3.hankelPoly_eq_sum`):

* `abs_det_Emat_le`: `|det E[:,f]| ≤ exp(½ ∑_{u,v} s_u s_v ln(|u − v| + 2))`, `s = prof f`
  (archimedean confluent Vandermonde bound, `abs_det_confluent_le`);
* `l1_det_Cbl_le`: `‖det C[f,g]‖₁ ≤ 24^{3n+1} ∏_u (Q_n |h_u|)^{s_u}` (block factorisation and
  the local factor bound `l1_cPoly_le`);
* `card_smSet_le`: at most `2^{4(3n+1)}` column sets;
* the kernel replacement `ln(|d| + 2) ≤ B(d) + 2/|d|` (`d ≠ 0`), summed with the harmonic
  estimate `sum_inv_dist_le`.

**`lemma62`**: for odd `n` and every `M`, if `E_B(s) ≤ M` for every profile `0 ≤ s_u ≤ 4`,
`∑ s_u = K`, then `‖Δ_K‖₁ ≤ exp(M + 𝓔(n, K))` with the explicit
`𝓔(n,K) = K (ln Q_n + 16(1 + ln 3n) + 4 ln 2) + (3n+1)(ln 24 + 8 ln 2) = O(n log n)`
(for `K ≤ 3n+1`); there is no `n²` contribution.
-/

open Polynomial Finset Matrix

namespace Hankel2.ArchB

open Fam3

variable {n K : ℕ}

/-- The CND kernel `B(d) = ½ ln(1 + d²)`. -/
noncomputable def Bk (d : ℝ) : ℝ := Real.log (1 + d ^ 2) / 2

/-- `h_u = H_u[0]` at the node `nodeOf n u`, as a real number. -/
noncomputable def hR (n : ℕ) (u : Fin (3 * n + 1)) : ℝ := ((Hk n (nodeOf n u) 0 : ℚ) : ℝ)

/-- The discrete energy `E_B(s) = ∑_u s_u ln|h_u| + ∑_{u,v} s_u s_v B(u − v)` (note `B(0) = 0`). -/
noncomputable def EB (n : ℕ) (s : Fin (3 * n + 1) → ℝ) : ℝ :=
  ∑ u, s u * Real.log |hR n u| +
    ∑ u, ∑ v, s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v)

/-- The error term `𝓔(n, K)` of Lemma 6.2. -/
noncomputable def errR (n K : ℕ) : ℝ :=
  K * (Real.log (Qn n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) +
    (3 * n + 1) * (Real.log 24 + 8 * Real.log 2)

/-! ### Generalities -/

theorem card_smSet_le (K : ℕ) (ι : Type*) [Fintype ι] [LinearOrder ι] :
    (smSet K ι).card ≤ 2 ^ Fintype.card ι := by
  classical
  have h := card_le_card_of_injOn (s := smSet K ι) (t := (univ : Finset ι).powerset)
    (fun f => univ.image f) (fun f _ => by simp) (by
      intro f hf g hg hfg
      simp only [mem_coe, mem_smSet] at hf hg
      have hfg' : univ.image f = univ.image g := hfg
      have hcf : (univ.image f).card = K := by
        rw [card_image_of_injective _ hf.injective, card_univ, Fintype.card_fin]
      have e1 : f = fun i => (univ.image f).orderEmbOfFin hcf i :=
        orderEmbOfFin_unique hcf (fun i => mem_image_of_mem _ (mem_univ i)) hf
      have hcg : (univ.image g).card = K := by
        rw [card_image_of_injective _ hg.injective, card_univ, Fintype.card_fin]
      have e2 : g = fun i => (univ.image g).orderEmbOfFin hcg i :=
        orderEmbOfFin_unique hcg (fun i => mem_image_of_mem _ (mem_univ i)) hg
      rw [e1, e2]
      funext i
      congr 2)
  simpa [card_powerset] using h

theorem sym_sum_Ioi_le {K : ℕ} (h : Fin K → Fin K → ℝ) (hs : ∀ c c', h c c' = h c' c)
    (hd : ∀ c, 0 ≤ h c c) :
    2 * ∑ c, ∑ c' ∈ Ioi c, h c c' ≤ ∑ c, ∑ c', h c c' := by
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
  have := sum_nonneg fun c (_ : c ∈ univ) => hd c
  linarith

theorem sum_nodeF_real (f : Fin K → Idx n) (G : Fin (3 * n + 1) → ℝ) :
    ∑ c, G (nodeF f c) = ∑ u, (prof f u : ℝ) * G u := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := nodeF f) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.1 hc).2], sum_const, nsmul_eq_mul, prof]

theorem abs_nodeOf_le (n : ℕ) (u : Fin (3 * n + 1)) : |((nodeOf n u : ℤ) : ℝ)| ≤ 2 * n := by
  have := u.isLt
  have h1 : -(n : ℤ) ≤ nodeOf n u := by simp only [nodeOf]; omega
  have h2 : nodeOf n u ≤ 2 * n := by simp only [nodeOf]; omega
  rw [abs_le]
  constructor
  · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((nodeOf n u : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  · exact_mod_cast h2

/-! ### The Vandermonde factor -/

/-- `G(u, v) = ln(|u − v| + 2)`. -/
noncomputable def Gk (n : ℕ) (u v : Fin (3 * n + 1)) : ℝ :=
  Real.log (|((nodeOf n u : ℝ) - nodeOf n v)| + 2)

theorem abs_det_Emat_le (f : Fin K → Idx n) :
    |((((Emat n K).submatrix id f).det : ℚ) : ℝ)| ≤
      Real.exp ((∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk n u v) / 2) := by
  set x : Fin K → ℝ := fun c => ((xnode n (nodeOf n (nodeF f c)) : ℚ) : ℝ) with hx
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
  refine (abs_det_confluent_le x (fun c => (ordF f c : ℕ))).trans ?_
  -- the product as an exponential
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
    simp only [hx, xnode]; push_cast
    congr 1; ring
  have hsym := sym_sum_Ioi_le (fun c c' => Real.log (|x c' - x c| + 2))
    (fun c c' => by simp only; rw [abs_sub_comm])
    (fun c => Real.log_nonneg (by simp))
  have hfull : ∑ c, ∑ c', Real.log (|x c' - x c| + 2) =
      ∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk n u v := by
    simp_rw [hx']
    rw [sum_nodeF_real f (fun u => ∑ c', Real.log (|((nodeOf n u : ℝ)) - nodeOf n (nodeF f c')| + 2))]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_nodeF_real f (fun v => Real.log (|((nodeOf n u : ℝ)) - nodeOf n v| + 2)), mul_sum]
    refine sum_congr rfl fun v _ => ?_
    simp only [Gk]; ring
  linarith

/-! ### The block factor -/

theorem l1_det_Cbl_le (hn : n % 2 = 1) {f g : Fin K → Idx n} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : prof f = prof g) :
    l1 ((Cbl n).submatrix f g).det ≤
      24 ^ (3 * n + 1) * ∏ u, (Qn n * |hR n u|) ^ prof f u := by
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
  have hA : ∀ u, 0 ≤ Qn n * |hR n u| := fun u => by
    unfold Qn
    have := one_le_LamA n
    have : (0 : ℝ) ≤ LamA n := by linarith
    positivity
  -- each block
  have hblock : ∀ u, l1 (((Cbl n).submatrix f g).toSquareBlock (nodeF f) u).det ≤
      24 * (Qn n * |hR n u|) ^ prof f u := by
    intro u
    have hcard : Fintype.card {c // nodeF f c = u} = prof f u := by
      rw [Fintype.card_subtype]; rfl
    refine (l1_det_le _ (Qn n * |hR n u|) fun c d => ?_).trans ?_
    · show l1 (Cbl n (f c) (g d)) ≤ _
      simp only [Cbl]
      split_ifs with h
      · have hc : (ofLex (f c)).1 = u := c.2
        rw [hc]
        exact l1_cPoly_le hn (abs_nodeOf_le n u) _
      · rw [l1_zero]; exact hA u
    · rw [hcard]
      have h4 := prof_le_four hf u
      have : ((prof f u).factorial : ℝ) ≤ 24 := by
        have : (prof f u).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le h4
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right this (pow_nonneg (hA u) _)
  refine (l1_prod_le _ _).trans ?_
  calc ∏ u ∈ univ.image (nodeF f), l1 (((Cbl n).submatrix f g).toSquareBlock (nodeF f) u).det
      ≤ ∏ u ∈ univ.image (nodeF f), 24 * (Qn n * |hR n u|) ^ prof f u :=
        prod_le_prod (fun _ _ => l1_nonneg _) (fun u _ => hblock u)
    _ = 24 ^ (univ.image (nodeF f)).card * ∏ u ∈ univ.image (nodeF f), (Qn n * |hR n u|) ^ prof f u := by
        rw [prod_mul_distrib, prod_const]
    _ ≤ 24 ^ (3 * n + 1) * ∏ u, (Qn n * |hR n u|) ^ prof f u := by
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

/-! ### Kernel replacement -/

theorem Hk_zero_ne_zero (hn : n % 2 = 1) (k : ℤ) : Hk n k 0 ≠ 0 := by
  rw [Fam3.Hk_zero_eq]
  refine mul_ne_zero (mul_ne_zero (lin_ne_zero hn k)
    (prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (half_int_ne_zero j k)))
    (prod_ne_zero_iff.2 fun k' hk' => pow_ne_zero _ (inv_ne_zero ?_))
  exact_mod_cast sub_ne_zero.2 (ne_of_mem_erase hk')

theorem hR_ne_zero (hn : n % 2 = 1) (u : Fin (3 * n + 1)) : hR n u ≠ 0 := by
  unfold hR; exact_mod_cast Hk_zero_ne_zero hn _

theorem Bk_zero : Bk 0 = 0 := by simp [Bk]

theorem log_abs_le_Bk (d : ℝ) : Real.log |d| ≤ Bk d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Bk]
  · unfold Bk
    have h1 : Real.log (d ^ 2) ≤ Real.log (1 + d ^ 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, ← Real.log_abs] at h1
    push_cast at h1; linarith

theorem log_add_two_le (d : ℝ) :
    Real.log (|d| + 2) ≤ Bk d + 2 * (1 / |d|) + (if d = 0 then Real.log 2 else 0) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Bk_zero]
  · rw [if_neg hd, add_zero]
    have hd' : 0 < |d| := abs_pos.2 hd
    have h1 : Real.log (|d| + 2) = Real.log |d| + Real.log (1 + 2 / |d|) := by
      rw [← Real.log_mul hd'.ne' (by positivity)]
      congr 1; field_simp
    have h2 : Real.log (1 + 2 / |d|) ≤ 2 / |d| := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / |d| by positivity)
      linarith
    have h3 := log_abs_le_Bk d
    rw [h1]
    have e : 2 * (1 / |d|) = 2 / |d| := by ring
    linarith

/-- `∑_v 1/|u − v| ≤ 2(1 + ln 3n)` over the nodes. -/
theorem sum_inv_node_le (n : ℕ) (u : Fin (3 * n + 1)) :
    ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| ≤ 2 * (1 + Real.log (3 * n)) := by
  have h := LemmaB.sum_inv_dist_le n (nodeOf n u) (nodeOf_mem_nodes n u)
  rw [← sum_nodes_eq n (fun m => 1 / |((nodeOf n u : ℝ) - m)|)]
  rw [← add_sum_erase _ _ (nodeOf_mem_nodes n u)]
  simp only [sub_self, abs_zero, div_zero, zero_add]
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun m _ => ?_
  push_cast; rfl

/-- The Vandermonde exponent against the energy: `∑ s_u s_v ln(|u−v|+2) ≤ ∑ s_u s_v B(u−v) + K(16(1+ln 3n) + 4 ln 2)`. -/
theorem sum_Gk_le (s : Fin (3 * n + 1) → ℝ) (hs0 : ∀ u, 0 ≤ s u) (hs4 : ∀ u, s u ≤ 4) :
    ∑ u, ∑ v, s u * s v * Gk n u v ≤
      ∑ u, ∑ v, s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        (∑ u, s u) * (16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) := by
  rw [sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun u _ => ?_
  have hterm : ∀ v, s u * s v * Gk n u v ≤ s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v) +
      s u * (8 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then 4 * Real.log 2 else 0)) := by
    intro v
    have h := log_add_two_le ((nodeOf n u : ℝ) - nodeOf n v)
    have hsuv : 0 ≤ s u * s v := mul_nonneg (hs0 u) (hs0 v)
    have e : (((nodeOf n u : ℝ) - nodeOf n v) = 0) ↔ u = v := by
      constructor
      · intro h0
        exact nodeOf_injective n (by exact_mod_cast sub_eq_zero.1 h0)
      · rintro rfl; simp
    have hG : s u * s v * Gk n u v ≤ s u * s v * (Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        2 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
        (if u = v then Real.log 2 else 0)) := by
      unfold Gk
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
  calc ∑ v, s u * s v * Gk n u v ≤ ∑ v, (s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (8 * (1 / |((nodeOf n u : ℝ) - nodeOf n v)|) +
          (if u = v then 4 * Real.log 2 else 0))) := sum_le_sum fun v _ => hterm v
    _ = ∑ v, s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (8 * ∑ v, 1 / |((nodeOf n u : ℝ) - nodeOf n v)| + 4 * Real.log 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_ite_eq, if_pos (mem_univ _)]
    _ ≤ ∑ v, s u * s v * Bk ((nodeOf n u : ℝ) - nodeOf n v) +
        s u * (16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) := by
        have := sum_inv_node_le n u
        have := hs0 u
        nlinarith

/-! ### Lemma 6.2 -/

theorem l1_C_mul_mul_C_le (a b : ℚ) (P : ℚ[X]) :
    l1 (C a * P * C b) ≤ |(a : ℝ)| * l1 P * |(b : ℝ)| := by
  refine (l1_mul_le _ _).trans ?_
  rw [l1_C]
  exact mul_le_mul_of_nonneg_right ((l1_mul_le _ _).trans (by rw [l1_C])) (abs_nonneg _)

/-- **Paper Lemma 6.2 (discrete reduction).**  For odd `n`: if `E_B(s) ≤ M` for every profile
`0 ≤ s_u ≤ 4`, `∑ s_u = K`, then `‖Δ_K‖₁ ≤ exp(M + 𝓔(n, K))`. -/
theorem lemma62 (hn : n % 2 = 1) (M : ℝ)
    (hM : ∀ s ∈ profiles n K, EB n (fun u => (s u : ℝ)) ≤ M) :
    l1 (hankelPoly n K) ≤ Real.exp (M + errR n K) := by
  set T := Real.exp (M + K * (Real.log (Qn n) + 16 * (1 + Real.log (3 * n)) + 4 * Real.log 2) +
    (3 * n + 1) * Real.log 24) with hT
  have hQ : 0 < Qn n := by
    unfold Qn
    have := one_le_LamA n
    have : (0 : ℝ) < LamA n := by linarith
    positivity
  have hterm : ∀ f ∈ smSet K (Idx n), ∀ g ∈ smSet K (Idx n),
      l1 (C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
        C ((Emat n K).submatrix id g).det) ≤ T := by
    intro f hf g hg
    rw [mem_smSet] at hf hg
    refine (l1_C_mul_mul_C_le _ _ _).trans ?_
    by_cases hfg : prof f = prof g
    · set s : Fin (3 * n + 1) → ℝ := fun u => (prof f u : ℝ) with hs
      have hs0 : ∀ u, 0 ≤ s u := fun u => by positivity
      have hs4 : ∀ u, s u ≤ 4 := fun u => by
        simp only [hs]; exact_mod_cast prof_le_four hf u
      have hsK : ∑ u, s u = K := by simp only [hs]; exact_mod_cast sum_prof f
      have hE1 := abs_det_Emat_le f
      have hE2 := abs_det_Emat_le g
      rw [← hfg] at hE2
      have hC := l1_det_Cbl_le hn hf hg hfg
      have hprod : ∏ u, (Qn n * |hR n u|) ^ prof f u =
          Real.exp (∑ u, s u * (Real.log (Qn n) + Real.log |hR n u|)) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun u _ => ?_
        have hpos : 0 < Qn n * |hR n u| := mul_pos hQ (abs_pos.2 (hR_ne_zero hn u))
        rw [← Real.log_mul hQ.ne' (abs_pos.2 (hR_ne_zero hn u)).ne', mul_comm (s u), Real.exp_mul,
          Real.exp_log hpos, hs, Real.rpow_natCast]
      rw [hprod] at hC
      have h24 : (24 : ℝ) ^ (3 * n + 1) = Real.exp ((3 * n + 1) * Real.log 24) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        push_cast; ring_nf
      rw [h24] at hC
      have hEB := hM (prof f) (prof_mem_profiles hf)
      have hG := sum_Gk_le s hs0 hs4
      rw [hsK] at hG
      unfold EB at hEB
      set S2 := ∑ u, ∑ v, (prof f u : ℝ) * prof f v * Gk n u v
      calc |(((Emat n K).submatrix id f).det : ℝ)| * l1 ((Cbl n).submatrix f g).det *
            |(((Emat n K).submatrix id g).det : ℝ)|
          ≤ Real.exp (S2 / 2) *
            (Real.exp ((3 * n + 1) * Real.log 24) *
              Real.exp (∑ u, s u * (Real.log (Qn n) + Real.log |hR n u|))) *
            Real.exp (S2 / 2) := by
            refine mul_le_mul (mul_le_mul hE1 hC (l1_nonneg _) (Real.exp_pos _).le) hE2
              (abs_nonneg _) (by positivity)
        _ = Real.exp (S2 + (3 * n + 1) * Real.log 24 + K * Real.log (Qn n) +
              ∑ u, s u * Real.log |hR n u|) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [mul_add, sum_add_distrib, ← sum_mul, hsK]
            ring
        _ ≤ T := by
            rw [hT, Real.exp_le_exp]
            simp only [hs] at hG
            linarith
    · rw [det_cbl_eq_zero_of_prof_ne hfg, l1_zero, mul_zero, zero_mul]
      exact (Real.exp_pos _).le
  rw [hankelPoly_eq_sum]
  refine (l1_sum_le _ _).trans ?_
  have hcard := card_smSet_le K (Idx n)
  have hcardI : Fintype.card (Idx n) = 4 * (3 * n + 1) := by
    simp [Idx, Fintype.card_prod, mul_comm]
  rw [hcardI] at hcard
  calc ∑ f ∈ smSet K (Idx n), l1 (∑ g ∈ smSet K (Idx n),
        C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
          C ((Emat n K).submatrix id g).det)
      ≤ ∑ _f ∈ smSet K (Idx n), ∑ _g ∈ smSet K (Idx n), T :=
        sum_le_sum fun f hf => (l1_sum_le _ _).trans (sum_le_sum fun g hg => hterm f hf g hg)
    _ = ((smSet K (Idx n)).card : ℝ) ^ 2 * T := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ ((2 : ℝ) ^ (4 * (3 * n + 1))) ^ 2 * T := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) (Real.exp_pos _).le
        exact_mod_cast hcard
    _ = Real.exp (M + errR n K) := by
        rw [hT, errR, ← pow_mul]
        have : (2 : ℝ) ^ (4 * (3 * n + 1) * 2) = Real.exp ((3 * n + 1) * (8 * Real.log 2)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
          push_cast; ring_nf
        rw [this, ← Real.exp_add]
        congr 1; ring

end Hankel2.ArchB
