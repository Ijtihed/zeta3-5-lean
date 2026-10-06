import RequestProject.Zeta35.InputDefs
import RequestProject.Zeta7.Hankel2.ContAssembly

/-!
# Translating the continuum problem of N, §4 to the interval of P (for N, Theorem 4.1)

The node interval of paper N is `[−3/2, 3/2]`; the continuum machinery of the `ζ₂(7)` library
(`Hankel2.ArchB`, P §6) lives on `[−1, 2]`.  The translation `x ↦ x − 1/2` identifies them:

* `shf f = f(· − 1/2)`;
* `logPot_shf`: `𝓛(shf f)(x) = 𝓛₃ f(x − 1/2)`; `pairing_shf`: `⟨shf f, shf g⟩ = ⟨f, g⟩₃`;
* `feasible_shf`, `feasible3_unshf`: feasibility is preserved;
* `Ph σ = shf (P_σ) = −4 𝓛1 + 2 𝓛(shf σ)` (`Ph_eq`), `|Ph σ| ≤ 216` on `[−1, 2]` (`abs_Ph_le`);
* `pairing_Ph_le_gap3`: `⟨Ph σ, σ' − shf σ⟩ ≤ gap₃(σ)` for every `σ'` feasible on `[−1, 2]`;
* `P_bound_gen`: the `ζ₂(7)` bound `P_bound` for an arbitrary bounded gradient `P` and an arbitrary
  upper bound `G` of the gap, for `κ ≤ 6`.
-/

open MeasureTheory Finset Hankel2 Hankel2.ArchB

namespace Zeta35.Arch

/-- The translate `f(· − 1/2)`. -/
noncomputable def shf (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (x - 1 / 2)

theorem integral_shf (g : ℝ → ℝ) :
    ∫ x in (-1 : ℝ)..2, g (x - 1 / 2) = ∫ x in (-3 / 2 : ℝ)..(3 / 2), g x := by
  rw [intervalIntegral.integral_comp_sub_right g (1 / 2 : ℝ)]
  norm_num

theorem logPot_shf (f : ℝ → ℝ) (x : ℝ) : logPot (shf f) x = logPot3 f (x - 1 / 2) := by
  unfold logPot logPot3 shf
  have := integral_shf (fun y => Real.log |x - 1 / 2 - y| * f y)
  rw [← this]
  refine intervalIntegral.integral_congr fun y _ => ?_
  congr 3; ring

theorem pairing_shf (f g : ℝ → ℝ) : pairing (shf f) (shf g) = pairing3 f g := by
  unfold pairing pairing3 shf
  exact integral_shf (fun x => f x * g x)

theorem feasible_shf {κ : ℝ} {σ : ℝ → ℝ} (h : Feasible3 κ σ) : Feasible κ (shf σ) := by
  obtain ⟨hm, hb, hi⟩ := h
  refine ⟨hm.comp (measurable_id.sub measurable_const), fun x => hb _, ?_⟩
  unfold shf; rw [integral_shf]; exact hi

theorem feasible3_unshf {κ : ℝ} {σ : ℝ → ℝ} (h : Feasible κ σ) :
    Feasible3 κ (fun x => σ (x + 1 / 2)) := by
  obtain ⟨hm, hb, hi⟩ := h
  refine ⟨hm.comp (measurable_id.add measurable_const), fun x => hb _, ?_⟩
  rw [← integral_shf]; simp only [sub_add_cancel]; exact hi

theorem shf_unshf (σ : ℝ → ℝ) : shf (fun x => σ (x + 1 / 2)) = σ := by
  funext x; simp [shf]

/-- The translated gradient `Ph σ = P_σ(· − 1/2)`. -/
noncomputable def Ph (σ : ℝ → ℝ) : ℝ → ℝ := shf (Pgrad3 σ)

theorem shf_one : shf (fun _ : ℝ => (1 : ℝ)) = fun _ => 1 := rfl

theorem logPot_one_shf (x : ℝ) :
    logPot (fun _ => (1 : ℝ)) x = logPot3 (fun _ => 1) (x - 1 / 2) :=
  logPot_shf (fun _ => 1) x

theorem Ph_eq (σ : ℝ → ℝ) (x : ℝ) :
    Ph σ x = -4 * logPot (fun _ => 1) x + 2 * logPot (shf σ) x := by
  unfold Ph
  simp only [shf, Pgrad3, Upot3]
  rw [logPot_one_shf, logPot_shf]

theorem measurable_Ph {σ : ℝ → ℝ} (hσm : Measurable σ) : Measurable (Ph σ) := by
  have : Ph σ = fun x => -4 * logPot (fun _ => 1) x + 2 * logPot (shf σ) x := funext (Ph_eq σ)
  rw [this]
  exact ((measurable_logPot measurable_const).const_mul _).add
    ((measurable_logPot (hσm.comp (measurable_id.sub measurable_const))).const_mul _)

theorem abs_Ph_le {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |Ph σ x| ≤ 216 := by
  rw [Ph_eq]
  have h1 := abs_logPot_le (f := fun _ => (1 : ℝ)) (M := 1) measurable_const (fun _ => zero_le_one)
    (fun _ => le_rfl) hx
  have h2 := abs_logPot_le (f := shf σ) (M := 4) (hσm.comp (measurable_id.sub measurable_const))
    (fun y => (hσ _).1) (fun y => (hσ _).2) hx
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem pairing_Ph_eq (σ σ₁ : ℝ → ℝ) :
    pairing3 (Pgrad3 σ) (fun x => σ₁ x - σ x) = pairing (Ph σ) (fun x => shf σ₁ x - shf σ x) := by
  rw [← pairing_shf]; rfl

theorem bddAbove_gap3 {κ : ℝ} {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) :
    BddAbove {g | ∃ σ', Feasible3 κ σ' ∧ g = pairing3 (Pgrad3 σ) (fun x => σ' x - σ x)} := by
  refine ⟨3 * (216 * 8), ?_⟩
  rintro g ⟨σ₁, ⟨_, h1, _⟩, rfl⟩
  rw [pairing_Ph_eq]
  refine le_trans (le_abs_self _) (abs_integral_le_of_bdd fun x hx => ?_)
  rw [abs_mul]
  refine mul_le_mul (abs_Ph_le hσm hσ hx) ?_ (abs_nonneg _) (by norm_num)
  simp only [shf]
  rw [abs_le]; constructor <;> linarith [(h1 (x - 1 / 2)).1, (h1 (x - 1 / 2)).2,
    (hσ (x - 1 / 2)).1, (hσ (x - 1 / 2)).2]

theorem pairing_Ph_le_gap3 {κ : ℝ} {σ : ℝ → ℝ} (hσm : Measurable σ)
    (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) {σ' : ℝ → ℝ} (h' : Feasible κ σ') :
    pairing (Ph σ) (fun x => σ' x - shf σ x) ≤ gap3 κ σ := by
  have h := le_csSup (bddAbove_gap3 (κ := κ) hσm hσ)
    ⟨fun x => σ' (x + 1 / 2), feasible3_unshf h', rfl⟩
  rw [pairing_Ph_eq, shf_unshf] at h
  exact h

/-- `F₃[σ] = ⟨shf σ, Ph σ⟩ − ⟨shf σ, 𝓛(shf σ)⟩`. -/
theorem Fenergy3_eq {σ : ℝ → ℝ} (hσm : Measurable σ) (hσ : ∀ x, 0 ≤ σ x ∧ σ x ≤ 4) :
    Fenergy3 σ = (∫ x in (-1 : ℝ)..2, shf σ x * Ph σ x) - pairing (shf σ) (logPot (shf σ)) := by
  have hsm : Measurable (shf σ) := hσm.comp (measurable_id.sub measurable_const)
  have hsb : ∀ y, |shf σ y| ≤ 4 := fun y => by
    show |σ (y - 1 / 2)| ≤ 4
    rw [abs_of_nonneg (hσ _).1]; exact (hσ _).2
  have hs : ∀ x, 0 ≤ shf σ x ∧ shf σ x ≤ 4 := fun x => hσ _
  have e1 : pairing3 σ Upot3 = pairing (shf σ) (fun x => -4 * logPot (fun _ => 1) x) := by
    rw [← pairing_shf]; congr 1; funext x; simp only [shf, Upot3]
    rw [logPot_one_shf]
  have e2 : pairing3 σ (logPot3 σ) = pairing (shf σ) (logPot (shf σ)) := by
    rw [← pairing_shf]; congr 1; funext x; simp only [shf]; rw [logPot_shf]
  have i1 := ii_mul_on hsm ((measurable_logPot measurable_const).const_mul (-4)) hsb
    (B := 72) (g := fun x => -4 * logPot (fun _ => (1 : ℝ)) x) (fun x hx => by
      have := abs_logPot_le (f := fun _ => (1 : ℝ)) (M := 1) measurable_const
        (fun _ => zero_le_one) (fun _ => le_rfl) hx
      rw [abs_mul]; norm_num; linarith) (le_refl (-1 : ℝ)) (by norm_num) (le_refl 2)
  have i2 := ii_mul_on hsm (measurable_logPot hsm) hsb (fun x hx => abs_logPot_σ_le hsm hs hx)
    (le_refl (-1 : ℝ)) (by norm_num) (le_refl 2)
  unfold Fenergy3
  rw [e1, e2]
  unfold pairing
  have e3 : (fun x => shf σ x * Ph σ x) =
      fun x => shf σ x * (-4 * logPot (fun _ => 1) x) + 2 * (shf σ x * logPot (shf σ) x) := by
    funext x; rw [Ph_eq]; ring
  rw [e3, intervalIntegral.integral_add i1 (i2.const_mul 2), intervalIntegral.integral_const_mul]
  ring

/-! ### The linear term against an integer profile, for a general gradient -/

theorem P_bound_gen {σ P : ℝ → ℝ} {n K : ℕ} {C G : ℝ} (hn : 0 < n) (hF : Feasible ((K : ℝ) / n) σ)
    (hK : (K : ℝ) / n ≤ 6) (hPm : Measurable P) (hPb : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |P x| ≤ C)
    (hG : ∀ σ', Feasible ((K : ℝ) / n) σ' → pairing P (fun x => σ' x - σ x) ≤ G)
    (s : ℤ → ℝ) (hs : ∀ k, 0 ≤ s k ∧ s k ≤ 4)
    (hsum1 : (K : ℝ) - 4 ≤ ∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k)
    (hsum2 : ∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k ≤ K) :
    ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
        s k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), P x) ≤
      (n : ℝ) ^ 2 * ((∫ x in (-1 : ℝ)..2, σ x * P x) + G) + 12 * C * n := by
  obtain ⟨hσm, hσ, hmass⟩ := hF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 ≤ C := (abs_nonneg _).trans (hPb 0 ⟨by norm_num, by norm_num⟩)
  set κ := (K : ℝ) / n with hκ
  have hσb : ∀ y, |σ y| ≤ 4 := fun y => by rw [abs_of_nonneg (hσ y).1]; exact (hσ y).2
  set σ' := stepFn n s with hσ'
  have hσ'b : ∀ x, 0 ≤ σ' x ∧ σ' x ≤ 4 := fun x => by
    simp only [hσ', stepFn]; split_ifs
    · exact hs _
    · exact ⟨le_rfl, by norm_num⟩
  have hσ'a : ∀ x, |σ' x| ≤ 4 := fun y => by rw [abs_of_nonneg (hσ'b y).1]; exact (hσ'b y).2
  have hσ'm : Measurable σ' := by
    have : Measurable (fun x : ℝ => s (⌈(n : ℝ) * x⌉ - 1)) := by fun_prop
    exact Measurable.ite measurableSet_Ioc this measurable_const
  have hPσ' : ∫ x in (-1 : ℝ)..2, σ' x * P x = ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
      s k * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), P x := by
    rw [integral_split_cells' hn fun a b ha hab hb => ii_mul_on hσ'm hPm hσ'a hPb ha hab hb]
    refine sum_congr rfl fun k hk => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (cell_le hn k)] at hx
    simp only [hσ', stepFn_cell hn s hk hx]
  have hm1 : ∫ x in (-1 : ℝ)..2, σ' x = (∑ k ∈ Ico (-(n : ℤ)) (2 * n), s k) / n := by
    rw [integral_split_cells' hn fun a b _ _ _ => ii_of_bdd hσ'm hσ'a a b, sum_div]
    refine sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_congr_ae (g := fun _ => s k)
      (Filter.Eventually.of_forall fun x hx => by
        rw [Set.uIoc_of_le (cell_le hn k)] at hx
        exact stepFn_cell hn s hk hx)]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp; ring
  set m1 := ∫ x in (-1 : ℝ)..2, σ' x with hm1def
  have hm1a : κ - 4 / n ≤ m1 := by
    rw [hm1, hκ, div_sub_div_same]; exact div_le_div_of_nonneg_right hsum1 hn'.le
  have hm1b : m1 ≤ κ := by rw [hm1, hκ]; exact div_le_div_of_nonneg_right hsum2 hn'.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : 4 / (n : ℝ) ≤ 4 := by rw [div_le_iff₀ hn']; linarith
  set lam := (12 - κ) / (12 - m1) with hlam
  have hden : 0 < 12 - m1 := by linarith
  have hlam1 : 1 - lam = (κ - m1) / (12 - m1) := by rw [hlam]; field_simp; ring
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hden.le
  have hlamle : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
  have hlamn : 1 - lam ≤ 1 / n := by
    rw [hlam1, div_le_div_iff₀ hden hn']
    have : (κ - m1) * n ≤ 4 := by
      have := mul_le_mul_of_nonneg_right (show κ - m1 ≤ 4 / n by linarith) hn'.le
      rwa [div_mul_cancel₀ _ hn'.ne'] at this
    nlinarith
  set σ'' : ℝ → ℝ := fun x => lam * σ' x + (1 - lam) * 4 with hσ''
  have hfeas : Feasible κ σ'' := by
    refine ⟨(hσ'm.const_mul lam).add measurable_const, fun x => ?_, ?_⟩
    · obtain ⟨h0, h4⟩ := hσ'b x
      constructor
      · simp only [hσ'']; nlinarith
      · simp only [hσ'']; nlinarith
    · simp only [hσ'']
      rw [intervalIntegral.integral_add ((ii_of_bdd hσ'm hσ'a _ _).const_mul lam)
        intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul, ← hm1def, hlam]
      field_simp; ring
  have hgap : pairing P (fun x => σ'' x - σ x) ≤ G := hG σ'' hfeas
  have iP : IntervalIntegrable P volume (-1) 2 :=
    ii_of_bdd_on hPm hPb (le_refl _) (by norm_num) (le_refl _)
  have iPσ' : IntervalIntegrable (fun x => σ' x * P x) volume (-1) 2 :=
    ii_mul_on hσ'm hPm hσ'a hPb (le_refl _) (by norm_num) (le_refl _)
  have iσP : IntervalIntegrable (fun x => σ x * P x) volume (-1) 2 :=
    ii_mul_on hσm hPm hσb hPb (le_refl _) (by norm_num) (le_refl _)
  set X := ∫ x in (-1 : ℝ)..2, σ' x * P x with hX
  set Y := ∫ x in (-1 : ℝ)..2, σ x * P x with hY
  have hpair : pairing P (fun x => σ'' x - σ x) =
      lam * X + (1 - lam) * 4 * (∫ x in (-1 : ℝ)..2, P x) - Y := by
    unfold pairing
    have e : (fun x => P x * (σ'' x - σ x)) =
        fun x => (lam * (σ' x * P x) + (1 - lam) * 4 * P x) - σ x * P x := by
      funext x; simp only [hσ'']; ring
    rw [e, intervalIntegral.integral_sub ((iPσ'.const_mul lam).add (iP.const_mul _)) iσP,
      intervalIntegral.integral_add (iPσ'.const_mul lam) (iP.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcorr : |X - 4 * ∫ x in (-1 : ℝ)..2, P x| ≤ 12 * C := by
    rw [hX, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iPσ'
      (iP.const_mul _)]
    have := abs_integral_le_of_bdd (C := 4 * C) (f := fun x => σ' x * P x - 4 * P x) fun x hx => by
      have e : σ' x * P x - 4 * P x = (σ' x - 4) * P x := by ring
      show |σ' x * P x - 4 * P x| ≤ 4 * C
      rw [e, abs_mul]
      have : |σ' x - 4| ≤ 4 := by
        rw [abs_le]; constructor <;> linarith [(hσ'b x).1, (hσ'b x).2]
      exact mul_le_mul this (hPb x hx) (abs_nonneg _) (by norm_num)
    linarith
  have hXle : X ≤ G + Y + 12 * C / n := by
    have hdecomp : X = pairing P (fun x => σ'' x - σ x) + Y +
        (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x) := by rw [hpair]; ring
    have h1 : (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x) ≤ 12 * C / n := by
      have hl0 : 0 ≤ 1 - lam := by linarith
      calc (1 - lam) * (X - 4 * ∫ x in (-1 : ℝ)..2, P x)
          ≤ (1 - lam) * (12 * C) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcorr) hl0
        _ ≤ 1 / n * (12 * C) := mul_le_mul_of_nonneg_right hlamn (by positivity)
        _ = 12 * C / n := by ring
    linarith
  have hLHS : ∑ k ∈ Ico (-(n : ℤ)) (2 * n),
      s k * ((n : ℝ) ^ 2 * ∫ x in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), P x) = (n : ℝ) ^ 2 * X := by
    rw [show X = _ from hPσ', mul_sum]; refine sum_congr rfl fun k _ => by ring
  rw [hLHS]
  have : (n : ℝ) ^ 2 * (12 * C / n) = 12 * C * n := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hXle (sq_nonneg (n : ℝ))]

end Zeta35.Arch
