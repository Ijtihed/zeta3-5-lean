module

public import Mathlib

/-!
# Newman's analytic (Tauberian) theorem

Let `f : ℝ → ℂ` be measurable and bounded by `M` on `[0, ∞)`, and let
`g(z) = ∫₀^∞ f(t) e^{-zt} dt` (`Re z > 0`) extend to a function `G` holomorphic on an open set
`U ⊇ {Re z ≥ 0}`.  Then `∫₀^T f(t) dt → G(0)` as `T → ∞` (**`newman_tauberian`**).

Proof (Newman, Zagier): contour integration of `(G(z) - g_T(z)) e^{zT} (1 + z²/R²) / z` over the
right semicircle `|z| = R`, `Re z ≥ 0`, closed on the left by the half-ellipse
`δ cos θ + i R sin θ` (for `G`) resp. the left semicircle (for the entire `g_T`).  The Cauchy
formula is obtained from primitives on discs (`DifferentiableOn.isExactOn_ball`) and the
fundamental theorem of calculus along each path.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric intervalIntegral

namespace PNT

/-! ### Paths and the fundamental theorem of calculus along a path -/

/-- FTC along a `C¹` path: if `F' = φ` on `S` and `γ` stays in `S`, then
`∫ φ(γ) γ' = F(γ b) - F(γ a)`. -/
theorem path_ftc {F φ : ℂ → ℂ} {S : Set ℂ} (hF : ∀ z ∈ S, HasDerivAt F (φ z) z)
    {γ γ' : ℝ → ℂ} {a b : ℝ} (hγ : ∀ s ∈ uIcc a b, HasDerivAt γ (γ' s) s)
    (hS : ∀ s ∈ uIcc a b, γ s ∈ S)
    (hcont : ContinuousOn (fun s => φ (γ s) * γ' s) (uIcc a b)) :
    ∫ s in a..b, φ (γ s) * γ' s = F (γ b) - F (γ a) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro s hs
    exact (hF _ (hS s hs)).comp s (hγ s hs)
  · exact hcont.intervalIntegrable

/-- The circle `θ ↦ R e^{iθ}`. -/
noncomputable def circ (R θ : ℝ) : ℂ := R * cexp (θ * I)

/-- Derivative of `circ`. -/
noncomputable def circ' (R θ : ℝ) : ℂ := R * cexp (θ * I) * I

/-- The half-ellipse `θ ↦ δ cos θ + i R sin θ`. -/
noncomputable def ell (δ R θ : ℝ) : ℂ := (δ * Real.cos θ : ℝ) + (R * Real.sin θ : ℝ) * I

/-- Derivative of `ell`. -/
noncomputable def ell' (δ R θ : ℝ) : ℂ := (-(δ * Real.sin θ) : ℝ) + (R * Real.cos θ : ℝ) * I

theorem hasDerivAt_circ (R θ : ℝ) : HasDerivAt (circ R) (circ' R θ) θ := by
  have := (((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp.const_mul (R : ℂ)
  convert this using 1
  simp [circ']; ring

theorem hasDerivAt_ell (δ R θ : ℝ) : HasDerivAt (ell δ R) (ell' δ R θ) θ := by
  have h1 := ((Real.hasDerivAt_cos θ).const_mul δ).ofReal_comp
  have h2 := (((Real.hasDerivAt_sin θ).const_mul R).ofReal_comp).mul_const I
  convert h1.add h2 using 1
  simp [ell']

theorem continuous_circ (R : ℝ) : Continuous (circ R) := by
  unfold circ; fun_prop

theorem continuous_circ' (R : ℝ) : Continuous (circ' R) := by
  unfold circ'; fun_prop

theorem continuous_ell (δ R : ℝ) : Continuous (ell δ R) := by
  unfold ell; fun_prop

theorem continuous_ell' (δ R : ℝ) : Continuous (ell' δ R) := by
  unfold ell'; fun_prop

theorem circ_re (R θ : ℝ) : (circ R θ).re = R * Real.cos θ := by
  simp [circ, Complex.exp_re]

theorem norm_circ {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ‖circ R θ‖ = R := by
  simp [circ, norm_exp_ofReal_mul_I, abs_of_nonneg hR]

theorem circ'_eq (R θ : ℝ) : circ' R θ = circ R θ * I := by
  simp [circ, circ']

theorem ell_re (δ R θ : ℝ) : (ell δ R θ).re = δ * Real.cos θ := by
  simp only [ell, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; ring

theorem ell_im (δ R θ : ℝ) : (ell δ R θ).im = R * Real.sin θ := by
  simp only [ell, add_im, ofReal_re, mul_im, I_re, I_im, ofReal_im]; ring

theorem circ_pi_div_two (R : ℝ) : circ R (Real.pi / 2) = R * I := by
  simp [circ]

theorem circ_neg_pi_div_two (R : ℝ) : circ R (-(Real.pi / 2)) = -(R * I) := by
  simp [circ, Complex.exp_neg]

theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi]; simp

theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi]; simp

theorem circ_three_pi_div_two (R : ℝ) : circ R (3 * Real.pi / 2) = -(R * I) := by
  rw [circ, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, cos_three_pi_div_two,
    sin_three_pi_div_two]; push_cast; ring

theorem ell_pi_div_two (δ R : ℝ) : ell δ R (Real.pi / 2) = R * I := by
  simp [ell]

theorem ell_three_pi_div_two (δ R : ℝ) : ell δ R (3 * Real.pi / 2) = -(R * I) := by
  rw [ell, cos_three_pi_div_two, sin_three_pi_div_two]; push_cast; ring

/-! ### Cauchy's formula for a closed curve made of two paths, via primitives -/

/-- For `H` holomorphic on a disc containing `0` and two paths in the disc avoiding `0` that
form a closed curve, `∮ H(z)/z dz = H(0) ∮ dz/z`. -/
theorem cauchy_pair {c : ℂ} {ρ : ℝ} {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball c ρ))
    (h0 : (0 : ℂ) ∈ ball c ρ)
    {γ₁ γ₁' γ₂ γ₂' : ℝ → ℂ} {a₁ b₁ a₂ b₂ : ℝ}
    (hγ₁ : ∀ s ∈ uIcc a₁ b₁, HasDerivAt γ₁ (γ₁' s) s)
    (hγ₂ : ∀ s ∈ uIcc a₂ b₂, HasDerivAt γ₂ (γ₂' s) s)
    (hc₁ : ContinuousOn γ₁' (uIcc a₁ b₁)) (hc₂ : ContinuousOn γ₂' (uIcc a₂ b₂))
    (hB₁ : ∀ s ∈ uIcc a₁ b₁, γ₁ s ∈ ball c ρ) (hB₂ : ∀ s ∈ uIcc a₂ b₂, γ₂ s ∈ ball c ρ)
    (hne₁ : ∀ s ∈ uIcc a₁ b₁, γ₁ s ≠ 0) (hne₂ : ∀ s ∈ uIcc a₂ b₂, γ₂ s ≠ 0)
    (he₁ : γ₁ b₁ = γ₂ a₂) (he₂ : γ₂ b₂ = γ₁ a₁) :
    (∫ s in a₁..b₁, H (γ₁ s) / γ₁ s * γ₁' s) + (∫ s in a₂..b₂, H (γ₂ s) / γ₂ s * γ₂' s)
      = H 0 * ((∫ s in a₁..b₁, γ₁' s / γ₁ s) + (∫ s in a₂..b₂, γ₂' s / γ₂ s)) := by
  set D := dslope H 0 with hD
  have hDd : DifferentiableOn ℂ D (ball c ρ) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h0)).mpr hH
  obtain ⟨Fp, hFp⟩ := hDd.isExactOn_ball
  have key : ∀ {γ γ' : ℝ → ℂ} {a b : ℝ}, (∀ s ∈ uIcc a b, HasDerivAt γ (γ' s) s) →
      ContinuousOn γ' (uIcc a b) → (∀ s ∈ uIcc a b, γ s ∈ ball c ρ) →
      (∀ s ∈ uIcc a b, γ s ≠ 0) →
      (∫ s in a..b, H (γ s) / γ s * γ' s) =
        (Fp (γ b) - Fp (γ a)) + H 0 * ∫ s in a..b, γ' s / γ s := by
    intro γ γ' a b hγ hc hB hne
    have hγc : ContinuousOn γ (uIcc a b) := fun s hs => (hγ s hs).continuousAt.continuousWithinAt
    have hDc : ContinuousOn (fun s => D (γ s) * γ' s) (uIcc a b) :=
      (hDd.continuousOn.comp hγc fun s hs => hB s hs).mul hc
    have hIc : ContinuousOn (fun s => γ' s / γ s) (uIcc a b) := hc.div hγc hne
    rw [← path_ftc hFp hγ hB hDc, ← intervalIntegral.integral_const_mul,
      ← integral_add hDc.intervalIntegrable (hIc.intervalIntegrable.const_mul (H 0))]
    refine integral_congr fun s hs => ?_
    simp only [hD, dslope_of_ne _ (hne s hs), slope_def_field, sub_zero]
    field_simp [hne s hs]
    ring
  rw [key hγ₁ hc₁ hB₁ hne₁, key hγ₂ hc₂ hB₂ hne₂, he₁, he₂]
  ring

/-- `∫ dz/z` along a path in the slit plane. -/
theorem integral_inv_slit {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ s ∈ uIcc a b, HasDerivAt γ (γ' s) s) (hc : ContinuousOn γ' (uIcc a b))
    (hS : ∀ s ∈ uIcc a b, γ s ∈ slitPlane) :
    ∫ s in a..b, γ' s / γ s = log (γ b) - log (γ a) := by
  have hγc : ContinuousOn γ (uIcc a b) := fun s hs => (hγ s hs).continuousAt.continuousWithinAt
  rw [← path_ftc (F := log) (φ := fun z => z⁻¹) (S := slitPlane) (fun z hz => hasDerivAt_log hz)
    hγ hS]
  · exact integral_congr fun s _ => by simp [div_eq_inv_mul]
  · exact (hγc.inv₀ fun s hs => slitPlane_ne_zero (hS s hs)).mul hc

/-- `∫ dz/z` along a path in the negative of the slit plane. -/
theorem integral_inv_negslit {γ γ' : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ s ∈ uIcc a b, HasDerivAt γ (γ' s) s) (hc : ContinuousOn γ' (uIcc a b))
    (hS : ∀ s ∈ uIcc a b, -γ s ∈ slitPlane) :
    ∫ s in a..b, γ' s / γ s = log (-γ b) - log (-γ a) := by
  have hγc : ContinuousOn γ (uIcc a b) := fun s hs => (hγ s hs).continuousAt.continuousWithinAt
  have hF : ∀ z ∈ {z : ℂ | -z ∈ slitPlane}, HasDerivAt (fun z => log (-z)) z⁻¹ z := by
    intro z hz
    have := (hasDerivAt_log hz).comp z (hasDerivAt_neg z)
    convert this using 1
    simp [inv_neg]
  rw [← path_ftc (F := fun z => log (-z)) (φ := fun z => z⁻¹) hF hγ hS]
  · exact integral_congr fun s _ => by simp [div_eq_inv_mul]
  · refine (hγc.inv₀ fun s hs => ?_).mul hc
    intro h; have := slitPlane_ne_zero (hS s hs); simp [h] at this

theorem log_RI_sub {R : ℝ} (hR : 0 < R) : log (R * I) - log (-(R * I)) = Real.pi * I := by
  rw [log_ofReal_mul hR I_ne_zero, ← mul_neg, log_ofReal_mul hR (neg_ne_zero.mpr I_ne_zero),
    log_I, log_neg_I]; ring

theorem circ_im (R θ : ℝ) : (circ R θ).im = R * Real.sin θ := by
  simp [circ, Complex.exp_im]

theorem mem_slitPlane_of {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.re = 0 → z.im ≠ 0) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases h1.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr (h2 h.symm)

theorem sin_ne_zero_of_cos_eq_zero {θ : ℝ} (h : Real.cos θ = 0) : Real.sin θ ≠ 0 := by
  intro hs; have := Real.sin_sq_add_cos_sq θ; rw [h, hs] at this; norm_num at this

/-- `∫ dz/z` over the right semicircle is `πi`. -/
theorem integral_inv_circ_right {R : ℝ} (hR : 0 < R) :
    ∫ θ in -(Real.pi / 2)..Real.pi / 2, circ' R θ / circ R θ = Real.pi * I := by
  have hle : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [integral_inv_slit (fun s _ => hasDerivAt_circ R s) (continuous_circ' R).continuousOn,
    circ_pi_div_two, circ_neg_pi_div_two, log_RI_sub hR]
  intro s hs
  rw [uIcc_of_le hle] at hs
  have hc : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc hs
  refine mem_slitPlane_of (by rw [circ_re]; positivity) fun h => ?_
  rw [circ_re] at h; rw [circ_im]
  have : Real.cos s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hR.ne'
    · exact h
  exact mul_ne_zero hR.ne' (sin_ne_zero_of_cos_eq_zero this)

/-- `∫ dz/z` over the left semicircle is `πi`. -/
theorem integral_inv_circ_left {R : ℝ} (hR : 0 < R) :
    ∫ θ in Real.pi / 2..3 * Real.pi / 2, circ' R θ / circ R θ = Real.pi * I := by
  have hle : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  rw [integral_inv_negslit (fun s _ => hasDerivAt_circ R s) (continuous_circ' R).continuousOn,
    circ_pi_div_two, circ_three_pi_div_two, neg_neg, log_RI_sub hR]
  intro s hs
  rw [uIcc_of_le hle] at hs
  have hc : Real.cos s ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2])
  refine mem_slitPlane_of (by rw [neg_re, circ_re]; nlinarith) fun h => ?_
  rw [neg_re, circ_re] at h; rw [neg_im, circ_im]
  have : Real.cos s = 0 := by
    rcases mul_eq_zero.mp (neg_eq_zero.mp h) with h | h
    · exact absurd h hR.ne'
    · exact h
  exact neg_ne_zero.mpr (mul_ne_zero hR.ne' (sin_ne_zero_of_cos_eq_zero this))

/-- `∫ dz/z` over the left half-ellipse is `πi`. -/
theorem integral_inv_ell {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∫ θ in Real.pi / 2..3 * Real.pi / 2, ell' δ R θ / ell δ R θ = Real.pi * I := by
  have hle : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  rw [integral_inv_negslit (fun s _ => hasDerivAt_ell δ R s) (continuous_ell' δ R).continuousOn,
    ell_pi_div_two, ell_three_pi_div_two, neg_neg, log_RI_sub hR]
  intro s hs
  rw [uIcc_of_le hle] at hs
  have hc : Real.cos s ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2])
  refine mem_slitPlane_of (by rw [neg_re, ell_re]; nlinarith) fun h => ?_
  rw [neg_re, ell_re] at h; rw [neg_im, ell_im]
  have : Real.cos s = 0 := by
    rcases mul_eq_zero.mp (neg_eq_zero.mp h) with h | h
    · exact absurd h hδ.ne'
    · exact h
  exact neg_ne_zero.mpr (mul_ne_zero hR.ne' (sin_ne_zero_of_cos_eq_zero this))

/-! ### Geometry: a disc inside `U` containing the contour -/

theorem exists_ball_contour {U : Set ℂ} (hU : IsOpen U) (hHalf : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℂ, ∃ ρ : ℝ, ball c ρ ⊆ U ∧
      (∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.re → z ∈ ball c ρ) ∧
      (∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → z ∈ ball c ρ) := by
  set K : Set ℂ := (fun y : ℝ => (y : ℂ) * I) '' Icc (-(R + 1)) (R + 1) with hK
  have hKc : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨y, _, rfl⟩; exact hHalf _ (by simp)
  obtain ⟨δ₀, hδ₀, hth⟩ := hKc.exists_thickening_subset_open hU hKU
  set d := min δ₀ 1 with hd
  have hd0 : 0 < d := lt_min hδ₀ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hthd : Metric.thickening d K ⊆ U :=
    (Metric.thickening_mono (min_le_left _ _) K).trans hth
  set c : ℝ := (R + 1) ^ 2 / d with hc
  have hc0 : 0 < c := by positivity
  have hcd : c * d = (R + 1) ^ 2 := by rw [hc]; field_simp
  set δ := min (d / 2) (R / (2 * c + 1)) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ d / 2 := min_le_left _ _
  have hδ2 : δ ≤ R / (2 * c + 1) := min_le_right _ _
  have hδR : 2 * c * δ + δ ^ 2 ≤ R := by
    have h1 : δ * (2 * c + 1) ≤ R := by
      rwa [le_div_iff₀ (by positivity)] at hδ2
    nlinarith
  set ρ := Real.sqrt ((c + δ) ^ 2 + R ^ 2 + 1) with hρ
  have hρ2 : ρ ^ 2 = (c + δ) ^ 2 + R ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hnormsq : ∀ z : ℂ, ‖z - (c : ℂ)‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hmem : ∀ z : ℂ, (z.re - c) ^ 2 + z.im ^ 2 < ρ ^ 2 → z ∈ ball (c : ℂ) ρ := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    rw [← hnormsq] at hz
    exact lt_of_pow_lt_pow_left₀ 2 hρ0 hz
  refine ⟨δ, hδ0, c, ρ, ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hz2 : (z.re - c) ^ 2 + z.im ^ 2 < ρ ^ 2 := by
      rw [← hnormsq]; exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
    rcases le_or_gt 0 z.re with h | h
    · exact hHalf z h
    · apply hthd
      rw [Metric.mem_thickening_iff]
      refine ⟨(z.im : ℂ) * I, ⟨z.im, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · have : z.im ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
        nlinarith [abs_le_of_sq_le_sq' this (by linarith)]
      · have : z.im ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
        exact (abs_le_of_sq_le_sq' this (by linarith)).2
      · rw [dist_eq_norm]
        have : z - (z.im : ℂ) * I = (z.re : ℂ) := by
          apply Complex.ext <;> simp
        rw [this, norm_real, Real.norm_eq_abs, abs_of_neg h]
        have : 2 * c * (-z.re) < c * d := by nlinarith
        nlinarith
  · intro z hz hre
    apply hmem
    have : z.re ^ 2 + z.im ^ 2 ≤ R ^ 2 := by
      have := Complex.sq_norm z
      rw [Complex.normSq_apply] at this
      nlinarith [norm_nonneg z]
    nlinarith
  · intro z h1 h2 h3
    apply hmem
    have : z.im ^ 2 ≤ R ^ 2 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    nlinarith

/-! ### The two contour identities -/

/-- Contour identity for `G`: right semicircle plus left half-ellipse. -/
theorem contour_G {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {c : ℂ} {ρ : ℝ} {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball c ρ))
    (hB1 : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ z.re → z ∈ ball c ρ)
    (hB2 : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → z ∈ ball c ρ) :
    (∫ θ in -(Real.pi / 2)..Real.pi / 2, H (circ R θ) / circ R θ * circ' R θ) +
      (∫ θ in Real.pi / 2..3 * Real.pi / 2, H (ell δ R θ) / ell δ R θ * ell' δ R θ)
      = 2 * Real.pi * I * H 0 := by
  have hle1 : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hle2 : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  rw [cauchy_pair hH (hB1 0 (by simp; linarith) le_rfl) (fun s _ => hasDerivAt_circ R s)
    (fun s _ => hasDerivAt_ell δ R s) (continuous_circ' R).continuousOn
    (continuous_ell' δ R).continuousOn, integral_inv_circ_right hR, integral_inv_ell hδ hR]
  · ring
  · intro s hs
    rw [uIcc_of_le hle1] at hs
    refine hB1 _ (norm_circ hR.le s).le ?_
    rw [circ_re]; exact mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc hs)
  · intro s hs
    rw [uIcc_of_le hle2] at hs
    have hc : Real.cos s ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hs.1 (by linarith [hs.2])
    refine hB2 _ ?_ ?_ ?_
    · rw [ell_re]; nlinarith [Real.neg_one_le_cos s]
    · rw [ell_re]; nlinarith
    · rw [ell_im, abs_mul, abs_of_pos hR]
      nlinarith [Real.abs_sin_le_one s]
  · intro s _ h
    have := norm_circ hR.le s
    rw [h, norm_zero] at this; linarith
  · intro s _ h
    have h1 := ell_re δ R s
    have h2 := ell_im δ R s
    rw [h, zero_re] at h1; rw [h, zero_im] at h2
    have hc : Real.cos s = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd h hδ.ne'
      · exact h
    exact mul_ne_zero hR.ne' (sin_ne_zero_of_cos_eq_zero hc) h2.symm
  · rw [circ_pi_div_two, ell_pi_div_two]
  · rw [ell_three_pi_div_two, circ_neg_pi_div_two]

/-- Contour identity for an entire `H`: the full circle. -/
theorem contour_T {R : ℝ} (hR : 0 < R) {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    (∫ θ in -(Real.pi / 2)..Real.pi / 2, H (circ R θ) / circ R θ * circ' R θ) +
      (∫ θ in Real.pi / 2..3 * Real.pi / 2, H (circ R θ) / circ R θ * circ' R θ)
      = 2 * Real.pi * I * H 0 := by
  have hB : ∀ s : ℝ, circ R s ∈ ball (0 : ℂ) (R + 1) := fun s => by
    rw [mem_ball_zero_iff, norm_circ hR.le]; linarith
  have hne : ∀ s : ℝ, circ R s ≠ 0 := fun s h => by
    have := norm_circ hR.le s
    rw [h, norm_zero] at this; linarith
  rw [cauchy_pair hH.differentiableOn (mem_ball_self (by linarith))
    (fun s _ => hasDerivAt_circ R s) (fun s _ => hasDerivAt_circ R s)
    (continuous_circ' R).continuousOn (continuous_circ' R).continuousOn
    (fun s _ => hB s) (fun s _ => hB s) (fun s _ => hne s) (fun s _ => hne s) rfl
    (by rw [circ_three_pi_div_two, circ_neg_pi_div_two]),
    integral_inv_circ_right hR, integral_inv_circ_left hR]
  ring

/-! ### The truncated Laplace transform -/

/-- `g_T(z) = ∫₀^T f(t) e^{-zt} dt`. -/
noncomputable def lapT (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)

theorem norm_integrand_le {f : ℝ → ℂ} {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M) {t : ℝ} (ht : 0 ≤ t)
    (z : ℂ) : ‖f t * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * t) := by
  rw [norm_mul, norm_exp]
  have : (-z * (t : ℂ)).re = -z.re * t := by simp
  rw [this]
  gcongr
  exact hM t ht

theorem measurable_integrand {f : ℝ → ℂ} (hf : Measurable f) (z : ℂ) :
    Measurable fun t : ℝ => f t * cexp (-z * t) :=
  hf.mul (by fun_prop)

theorem norm_lapT_le {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z.re < 0) :
    ‖lapT f T z‖ ≤ M * Real.exp (-z.re * T) / (-z.re) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  set a := -z.re with ha
  have ha0 : 0 < a := by linarith
  have hc : Continuous fun t => M * Real.exp (a * t) := by fun_prop
  have hint : ∫ t in (0 : ℝ)..T, M * Real.exp (a * t) = M * (Real.exp (a * T) - 1) / a := by
    have := integral_eq_sub_of_hasDerivAt (a := 0) (b := T)
      (f := fun t => M * Real.exp (a * t) / a) (f' := fun t => M * Real.exp (a * t))
      (fun t _ => by
        have := (((hasDerivAt_id t).const_mul a).exp.const_mul M).div_const a
        convert this using 1; simp only [id]; field_simp)
      (hc.intervalIntegrable _ _)
    rw [this]; simp; ring
  calc ‖lapT f T z‖ ≤ ∫ t in (0 : ℝ)..T, M * Real.exp (a * t) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hT
          (Eventually.of_forall fun t ht => ?_) (hc.intervalIntegrable _ _)
        exact norm_integrand_le hM ht.1.le z
    _ = M * (Real.exp (a * T) - 1) / a := hint
    _ ≤ M * Real.exp (a * T) / a := by
        gcongr; linarith
    _ = M * Real.exp (-z.re * T) / (-z.re) := by rw [ha]

theorem integrableOn_integrand {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun t : ℝ => f t * cexp (-z * t)) (Ioi c) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) c).const_mul M)
    (measurable_integrand hf z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun t ht => norm_integrand_le hM (hc.trans (le_of_lt ht)) z

theorem norm_lap_sub_lapT_le {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 0 < z.re) :
    ‖(∫ t in Ioi 0, f t * cexp (-z * t)) - lapT f T z‖ ≤ M * Real.exp (-z.re * T) / z.re := by
  rw [← integral_interval_add_Ioi (integrableOn_integrand hf hM hz le_rfl)
    (integrableOn_integrand hf hM hz hT), lapT, add_sub_cancel_left]
  calc ‖∫ t in Ioi T, f t * cexp (-z * t)‖ ≤ ∫ t in Ioi T, M * Real.exp (-z.re * t) := by
        refine norm_integral_le_of_norm_le
          ((integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) T).const_mul M) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun t ht => norm_integrand_le hM (hT.trans (le_of_lt ht)) z
    _ = M * Real.exp (-z.re * T) / z.re := by
        rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith)]
        field_simp

theorem differentiable_lapT {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℂ (lapT f T) := by
  intro z₀
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  set K := ‖z₀‖ + 1
  have hexp : ∀ z : ℂ, ‖z‖ ≤ K → ∀ t ∈ uIoc 0 T, Real.exp (-z.re * t) ≤ Real.exp (K * T) := by
    intro z hz t ht
    rw [uIoc_of_le hT] at ht
    apply Real.exp_le_exp.mpr
    have h1 : -z.re ≤ K := (neg_le_abs _).trans ((abs_re_le_norm z).trans hz)
    have hK : 0 ≤ K := by positivity
    nlinarith [ht.1, ht.2]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume) (a := 0) (b := T)
    (F := fun z t => f t * cexp (-z * t)) (F' := fun z t => f t * (-(t : ℂ) * cexp (-z * t)))
    (x₀ := z₀) (s := ball z₀ 1) (bound := fun _ => M * T * Real.exp (K * T))
    (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (measurable_integrand hf z).aestronglyMeasurable)
    (by
      refine IntervalIntegrable.mono_fun' (g := fun _ => M * Real.exp (K * T))
        _root_.intervalIntegrable_const (measurable_integrand hf z₀).aestronglyMeasurable ?_
      rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 ≤ t := by rw [uIoc_of_le hT] at ht; exact ht.1.le
      exact (norm_integrand_le hM ht0 z₀).trans
        (mul_le_mul_of_nonneg_left (hexp z₀ (by simp [K]) t ht) hM0))
    ((hf.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t ht z hz => by
      have ht' := ht
      rw [uIoc_of_le hT] at ht'
      have hzK : ‖z‖ ≤ K := by
        have := norm_le_norm_add_norm_sub' z z₀
        rw [mem_ball, dist_eq_norm] at hz
        simp only [K]; linarith
      rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos ht'.1, norm_exp]
      have : (-z * (t : ℂ)).re = -z.re * t := by simp
      rw [this]
      calc ‖f t‖ * (t * Real.exp (-z.re * t)) ≤ M * (T * Real.exp (K * T)) := by
            exact mul_le_mul (hM t ht'.1.le)
              (mul_le_mul ht'.2 (hexp z hzK t ht) (Real.exp_pos _).le hT)
              (mul_nonneg ht'.1.le (Real.exp_pos _).le) hM0
        _ = M * T * Real.exp (K * T) := by ring)
    _root_.intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ => by
      have := ((hasDerivAt_neg z).mul_const (t : ℂ)).cexp.const_mul (f t)
      convert this using 1
      ring)
  exact key.2.differentiableAt

/-! ### The kernel `e^{zT}(1 + z²/R²)` -/

theorem norm_one_add_sq_div {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ = 2 * |z.re| / R := by
  have hR2 : (R : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [mul_conj, normSq_eq_norm_sq, hz]; push_cast; ring
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have h1 : 1 + z ^ 2 / (R : ℂ) ^ 2 = z * (2 * (z.re : ℂ)) / (R : ℂ) ^ 2 := by
    have := add_conj z
    push_cast at this
    rw [← this]
    field_simp
    rw [hR2]; ring
  rw [h1, norm_div, norm_mul, norm_mul, hz]
  simp [abs_of_pos hR]
  field_simp

/-- The kernel. -/
noncomputable def kern (R T : ℝ) (z : ℂ) : ℂ := cexp (z * T) * (1 + z ^ 2 / (R : ℂ) ^ 2)

theorem differentiable_kern (R T : ℝ) : Differentiable ℂ (kern R T) := by
  unfold kern; fun_prop

theorem kern_bound {R : ℝ} (hR : 0 < R) {M T : ℝ} (hM : 0 ≤ M) {F : ℂ → ℂ} {z : ℂ}
    (hz : ‖z‖ = R) (hF : z.re ≠ 0 → ‖F z‖ ≤ M * Real.exp (-z.re * T) / |z.re|) :
    ‖F z * kern R T z‖ ≤ 2 * M / R := by
  rw [kern, norm_mul, norm_mul, norm_exp, norm_one_add_sq_div hR hz]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  rcases eq_or_ne z.re 0 with h | h
  · rw [h]; simp; positivity
  · have hpos : 0 < |z.re| := abs_pos.mpr h
    calc ‖F z‖ * (Real.exp (z.re * T) * (2 * |z.re| / R))
        ≤ M * Real.exp (-z.re * T) / |z.re| * (Real.exp (z.re * T) * (2 * |z.re| / R)) := by
          gcongr; exact hF h
      _ = 2 * M / R * (Real.exp (-z.re * T) * Real.exp (z.re * T)) := by
          field_simp
      _ = 2 * M / R := by rw [← Real.exp_add]; simp

/-- Pointwise bound on the right semicircle. -/
theorem bound_right {R : ℝ} (hR : 0 < R) {M T : ℝ} (hM : 0 ≤ M) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → ‖F z‖ ≤ M * Real.exp (-z.re * T) / z.re) (θ : ℝ)
    (hθ : 0 ≤ Real.cos θ) :
    ‖F (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ‖ ≤ 2 * M / R := by
  have hne : circ R θ ≠ 0 := fun h => by
    have := norm_circ hR.le θ; rw [h, norm_zero] at this; linarith
  have hre : 0 ≤ (circ R θ).re := by rw [circ_re]; positivity
  rw [circ'_eq, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hne, norm_mul, norm_I,
    mul_one]
  refine kern_bound hR hM (norm_circ hR.le θ) fun h => ?_
  rw [abs_of_nonneg hre]; exact hF _ (lt_of_le_of_ne hre (Ne.symm h))

/-- Pointwise bound on the left semicircle. -/
theorem bound_left {R : ℝ} (hR : 0 < R) {M T : ℝ} (hM : 0 ≤ M) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, z.re < 0 → ‖F z‖ ≤ M * Real.exp (-z.re * T) / (-z.re)) (θ : ℝ)
    (hθ : Real.cos θ ≤ 0) :
    ‖F (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ‖ ≤ 2 * M / R := by
  have hne : circ R θ ≠ 0 := fun h => by
    have := norm_circ hR.le θ; rw [h, norm_zero] at this; linarith
  have hre : (circ R θ).re ≤ 0 := by
    rw [circ_re]; exact mul_nonpos_of_nonneg_of_nonpos hR.le hθ
  rw [circ'_eq, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hne, norm_mul, norm_I,
    mul_one]
  refine kern_bound hR hM (norm_circ hR.le θ) fun h => ?_
  rw [abs_of_nonpos hre]; exact hF _ (lt_of_le_of_ne hre h)

/-- The half-ellipse contribution of `G` tends to `0`. -/
theorem tendsto_ell_part {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {G : ℂ → ℂ}
    (hG : ContinuousOn G {z | -δ ≤ z.re ∧ z.re ≤ 0 ∧ |z.im| ≤ R}) :
    Tendsto (fun T : ℝ => ∫ θ in Real.pi / 2..3 * Real.pi / 2,
      G (ell δ R θ) * kern R T (ell δ R θ) / ell δ R θ * ell' δ R θ) atTop (𝓝 0) := by
  have hle2 : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem : ∀ θ ∈ uIcc (Real.pi / 2) (3 * Real.pi / 2),
      ell δ R θ ∈ {z : ℂ | -δ ≤ z.re ∧ z.re ≤ 0 ∧ |z.im| ≤ R} := by
    intro θ hθ
    rw [uIcc_of_le hle2] at hθ
    have hc : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
    refine ⟨?_, ?_, ?_⟩
    · rw [ell_re]; nlinarith [Real.neg_one_le_cos θ]
    · rw [ell_re]; nlinarith
    · rw [ell_im, abs_mul, abs_of_pos hR]; nlinarith [Real.abs_sin_le_one θ]
  have hne : ∀ θ, ell δ R θ ≠ 0 := by
    intro θ h
    have h1 := ell_re δ R θ
    have h2 := ell_im δ R θ
    rw [h, zero_re] at h1; rw [h, zero_im] at h2
    have hc : Real.cos θ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd h hδ.ne'
      · exact h
    exact mul_ne_zero hR.ne' (sin_ne_zero_of_cos_eq_zero hc) h2.symm
  set q : ℝ → ℂ := fun θ => G (ell δ R θ) * (1 + ell δ R θ ^ 2 / (R : ℂ) ^ 2) / ell δ R θ *
    ell' δ R θ with hqdef
  have hq : ContinuousOn q (uIcc (Real.pi / 2) (3 * Real.pi / 2)) := by
    refine (((hG.comp (continuous_ell δ R).continuousOn hmem).mul ?_).div
      (continuous_ell δ R).continuousOn fun θ _ => hne θ).mul (continuous_ell' δ R).continuousOn
    exact (continuous_const.add (((continuous_ell δ R).pow 2).div_const _)).continuousOn
  have hF : ∀ T θ, G (ell δ R θ) * kern R T (ell δ R θ) / ell δ R θ * ell' δ R θ =
      cexp (ell δ R θ * T) * q θ := by
    intro T θ; simp only [kern, hqdef]; ring
  simp_rw [hF]
  have h0 : (0 : ℂ) = ∫ θ in Real.pi / 2..3 * Real.pi / 2, (0 : ℂ) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun θ => ‖q θ‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun T => ?_
    have : ContinuousOn (fun θ => cexp (ell δ R θ * T) * q θ)
        (uIcc (Real.pi / 2) (3 * Real.pi / 2)) :=
      (Complex.continuous_exp.comp ((continuous_ell δ R).mul continuous_const)).continuousOn.mul hq
    exact (this.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [eventually_ge_atTop 0] with T hT
    refine Eventually.of_forall fun θ hθ => ?_
    have hθ' := uIoc_subset_uIcc hθ
    have hre := (hmem θ hθ').2.1
    rw [norm_mul, norm_exp]
    have : (ell δ R θ * T).re ≤ 0 := by
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hre hT
    calc Real.exp (ell δ R θ * T).re * ‖q θ‖ ≤ 1 * ‖q θ‖ := by
          gcongr; exact Real.exp_le_one_iff.mpr this
      _ = ‖q θ‖ := one_mul _
  · exact hq.norm.intervalIntegrable
  · filter_upwards [Measure.ae_ne volume (3 * Real.pi / 2)] with θ hθne hθ
    rw [uIoc_of_le hle2] at hθ
    have hc : Real.cos θ < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by
        rcases hθ.2.lt_or_eq with h | h
        · linarith
        · exact absurd h hθne)
    have hlim : Tendsto (fun T : ℝ => cexp (ell δ R θ * T)) atTop (𝓝 0) := by
      rw [Complex.tendsto_exp_nhds_zero_iff]
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, ell_re]
      exact tendsto_id.const_mul_atTop_of_neg (by nlinarith)
    simpa using hlim.mul_const (q θ)

/-! ### Newman's theorem -/

/-- **Newman's analytic theorem.** -/
theorem newman_tauberian (f : ℝ → ℂ) (hf : Measurable f) (M : ℝ)
    (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M)
    (U : Set ℂ) (hU : IsOpen U) (hHalf : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G U)
    (hLap : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ioi 0, f t * cexp (-z * t)) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (G 0)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := 4 * (M + 1) / ε with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨δ, hδ, c, ρ, hsub, hB1, hB2⟩ := exists_ball_contour hU hHalf hR
  have hGc : ContinuousOn G {z | -δ ≤ z.re ∧ z.re ≤ 0 ∧ |z.im| ≤ R} :=
    hG.continuousOn.mono fun z hz => hsub (hB2 z hz.1 hz.2.1 hz.2.2)
  have hE := tendsto_ell_part hR hδ hGc
  rw [Metric.tendsto_atTop] at hE
  obtain ⟨N, hN⟩ := hE (Real.pi * ε) (by positivity)
  refine ⟨max N 0, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := le_of_max_le_right hT
  have hTN : N ≤ T := le_of_max_le_left hT
  have hGH : DifferentiableOn ℂ (fun z => G z * kern R T z) (ball c ρ) :=
    (hG.mono hsub).mul (differentiable_kern R T).differentiableOn
  have hdT := differentiable_lapT hf hM hT0
  have I1 := contour_G hR hδ hGH hB1 hB2
  have I2 := contour_T (H := fun z => lapT f T z * kern R T z) hR
    (hdT.mul (differentiable_kern R T))
  have hk0 : kern R T 0 = 1 := by simp [kern]
  have hlap0 : lapT f T 0 = ∫ t in (0 : ℝ)..T, f t := by simp [lapT]
  simp only [hk0, mul_one] at I1 I2
  have hle1 : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hle2 : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have hne : ∀ s : ℝ, circ R s ≠ 0 := fun s h => by
    have := norm_circ hR.le s
    rw [h, norm_zero] at this; linarith
  -- continuity of the integrands on the right semicircle
  have hcircU : ∀ s ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2), circ R s ∈ U := by
    intro s hs
    rw [uIcc_of_le hle1] at hs
    refine hsub (hB1 _ (norm_circ hR.le s).le ?_)
    rw [circ_re]; exact mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc hs)
  have hcG : ContinuousOn (fun θ => G (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ)
      (uIcc (-(Real.pi / 2)) (Real.pi / 2)) := by
    refine (((hG.continuousOn.comp (continuous_circ R).continuousOn hcircU).mul
      ((differentiable_kern R T).continuous.comp (continuous_circ R)).continuousOn).div
      (continuous_circ R).continuousOn fun s _ => hne s).mul (continuous_circ' R).continuousOn
  have hcT : ContinuousOn (fun θ => lapT f T (circ R θ) * kern R T (circ R θ) / circ R θ *
      circ' R θ) (uIcc (-(Real.pi / 2)) (Real.pi / 2)) := by
    refine (((hdT.continuous.comp (continuous_circ R)).continuousOn.mul
      ((differentiable_kern R T).continuous.comp (continuous_circ R)).continuousOn).div
      (continuous_circ R).continuousOn fun s _ => hne s).mul (continuous_circ' R).continuousOn
  have hsplit : (∫ θ in -(Real.pi / 2)..Real.pi / 2,
      (G (circ R θ) - lapT f T (circ R θ)) * kern R T (circ R θ) / circ R θ * circ' R θ) =
      (∫ θ in -(Real.pi / 2)..Real.pi / 2,
        G (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ) -
      (∫ θ in -(Real.pi / 2)..Real.pi / 2,
        lapT f T (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ) := by
    rw [← integral_sub hcG.intervalIntegrable hcT.intervalIntegrable]
    exact integral_congr fun θ _ => by ring
  set A := ∫ θ in -(Real.pi / 2)..Real.pi / 2,
      (G (circ R θ) - lapT f T (circ R θ)) * kern R T (circ R θ) / circ R θ * circ' R θ
  set B := ∫ θ in Real.pi / 2..3 * Real.pi / 2,
      lapT f T (circ R θ) * kern R T (circ R θ) / circ R θ * circ' R θ
  set E := ∫ θ in Real.pi / 2..3 * Real.pi / 2,
      G (ell δ R θ) * kern R T (ell δ R θ) / ell δ R θ * ell' δ R θ
  have hkey : 2 * Real.pi * I * (G 0 - ∫ t in (0 : ℝ)..T, f t) = A + E - B := by
    rw [← hlap0, mul_sub, ← I1, ← I2, hsplit]; ring
  have hA : ‖A‖ ≤ 2 * M / R * Real.pi := by
    have := norm_integral_le_of_norm_le_const (a := -(Real.pi / 2)) (b := Real.pi / 2)
      (C := 2 * M / R) (f := fun θ => (G (circ R θ) - lapT f T (circ R θ)) *
        kern R T (circ R θ) / circ R θ * circ' R θ) (fun θ hθ => by
        rw [uIoc_of_le hle1] at hθ
        refine bound_right hR hM0 (F := fun z => G z - lapT f T z) (fun z hz => ?_) θ
          (Real.cos_nonneg_of_mem_Icc ⟨hθ.1.le, hθ.2⟩)
        show ‖G z - lapT f T z‖ ≤ _
        rw [hLap z hz]; exact norm_lap_sub_lapT_le hf hM hT0 hz)
    rwa [show |Real.pi / 2 - -(Real.pi / 2)| = Real.pi by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring] at this
  have hB : ‖B‖ ≤ 2 * M / R * Real.pi := by
    have := norm_integral_le_of_norm_le_const (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (C := 2 * M / R) (f := fun θ => lapT f T (circ R θ) *
        kern R T (circ R θ) / circ R θ * circ' R θ) (fun θ hθ => by
        rw [uIoc_of_le hle2] at hθ
        exact bound_left hR hM0 (F := lapT f T) (fun z hz => norm_lapT_le hM hT0 hz) θ
          (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2])))
    rwa [show |3 * Real.pi / 2 - Real.pi / 2| = Real.pi by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring] at this
  have hEb : ‖E‖ < Real.pi * ε := by
    have := hN T hTN
    rwa [dist_zero_right] at this
  have hnorm : ‖2 * Real.pi * I * (G 0 - ∫ t in (0 : ℝ)..T, f t)‖ =
      2 * Real.pi * ‖G 0 - ∫ t in (0 : ℝ)..T, f t‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_I]
    simp [abs_of_pos Real.pi_pos]
  have htri : ‖A + E - B‖ ≤ ‖A‖ + ‖E‖ + ‖B‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  rw [hkey] at hnorm
  have hMR : 2 * M / R * Real.pi * 2 < Real.pi * ε := by
    rw [hRdef]
    have : 2 * M / (4 * (M + 1) / ε) * Real.pi * 2 = Real.pi * ε * (M / (M + 1)) := by
      field_simp; ring
    rw [this]
    have : M / (M + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    exact mul_lt_of_lt_one_right (by positivity) this
  rw [dist_comm, dist_eq_norm]
  have : 2 * Real.pi * ‖G 0 - ∫ t in (0 : ℝ)..T, f t‖ < 2 * Real.pi * ε := by
    rw [← hnorm]; linarith
  exact lt_of_mul_lt_mul_left this (by positivity)

end PNT
