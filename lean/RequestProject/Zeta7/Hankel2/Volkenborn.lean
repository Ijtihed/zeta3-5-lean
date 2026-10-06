import Mathlib

/-!
# The Volkenborn integral and the structural lemma for inverse powers

The 2-adic Hankel construction of `HANKEL2_ZETA7.md` is built on the Volkenborn integral

`∫_{ℤ_p} f(t) dt = lim_{N → ∞} p^{-N} ∑_{t < p^N} f(t)`.

This file sets up that limit (`Hankel2.volkSum`, `Hankel2.HasVolkenborn`, `Hankel2.volkInt`)
and proves the *structural lemma* that drives the whole method: for `‖c‖ > 1`,

`∫_{ℤ_p} (t + c + k)^{-m} dt = ∫_{ℤ_p} (t + c)^{-m} dt − m ∑_{l < k} (c + l)^{-(m+1)}`,

together with the fact that existence of the integral for one shift *implies* existence for
every further integer shift (`Hankel2.hasVolkenborn_shift`,
`Hankel2.hasVolkenborn_shift_nat`).  With `p = 2` and `c = 1/2` this is exactly the
displayed identity of the task,

`∫_{ℤ₂} (t + 1/2 + k)^{-m} dt = m·2^{m+1}·ζ₂(m+1) − m ∑_{l=1}^{k} (l − 1/2)^{-(m+1)}`,

once `ζ₂(m+1)` is normalised by `m·2^{m+1}·ζ₂(m+1) = ∫_{ℤ₂}(t+1/2)^{-m} dt`
(`Hankel2.zeta2`, `Hankel2.volkInt_half_shift`).  The Kubota–Leopoldt interpretation of that
normalisation is classical and is *not* formalised here.

Everything in this file is proved.  The only classical input that is **not** formalised is
the *existence* of the Volkenborn integral of `(t+c)^{-m}` (Volkenborn's theorem: the
integral exists for every strictly differentiable function).  Existence therefore appears
as an explicit hypothesis `HasVolkenborn` wherever it is needed; by
`Hankel2.hasVolkenborn_shift_nat` one such hypothesis per exponent `m` suffices for the
whole family of shifts.
-/

namespace Hankel2

open Filter Finset Topology

variable {p : ℕ} [Fact p.Prime]

/-- The `N`-th Volkenborn Riemann sum `p^{-N} ∑_{t < p^N} f(t)`. -/
noncomputable def volkSum (p : ℕ) [Fact p.Prime] (f : ℚ_[p] → ℚ_[p]) (N : ℕ) : ℚ_[p] :=
  ((p : ℚ_[p]) ^ N)⁻¹ * ∑ t ∈ range (p ^ N), f ((t : ℕ) : ℚ_[p])

/-- `f` has Volkenborn integral `I` over `ℤ_p`. -/
def HasVolkenborn (p : ℕ) [Fact p.Prime] (f : ℚ_[p] → ℚ_[p]) (I : ℚ_[p]) : Prop :=
  Tendsto (volkSum p f) atTop (𝓝 I)

/-- The Volkenborn integral (the limit of the Riemann sums; junk value if it diverges). -/
noncomputable def volkInt (p : ℕ) [Fact p.Prime] (f : ℚ_[p] → ℚ_[p]) : ℚ_[p] :=
  limUnder atTop (volkSum p f)

theorem HasVolkenborn.unique {f : ℚ_[p] → ℚ_[p]} {I J : ℚ_[p]}
    (hI : HasVolkenborn p f I) (hJ : HasVolkenborn p f J) : I = J :=
  tendsto_nhds_unique hI hJ

theorem HasVolkenborn.volkInt_eq {f : ℚ_[p] → ℚ_[p]} {I : ℚ_[p]} (hI : HasVolkenborn p f I) :
    volkInt p f = I := hI.limUnder_eq

/-! ## Linearity -/

theorem HasVolkenborn.add {f g : ℚ_[p] → ℚ_[p]} {I J : ℚ_[p]}
    (hf : HasVolkenborn p f I) (hg : HasVolkenborn p g J) :
    HasVolkenborn p (fun t => f t + g t) (I + J) := by
  have h : volkSum p (fun t => f t + g t) = fun N => volkSum p f N + volkSum p g N := by
    funext N
    simp only [volkSum, Finset.sum_add_distrib, mul_add]
  rw [HasVolkenborn, h]
  exact Filter.Tendsto.add hf hg

theorem HasVolkenborn.const_mul {f : ℚ_[p] → ℚ_[p]} {I : ℚ_[p]} (c : ℚ_[p])
    (hf : HasVolkenborn p f I) : HasVolkenborn p (fun t => c * f t) (c * I) := by
  have h : volkSum p (fun t => c * f t) = fun N => c * volkSum p f N := by
    funext N
    simp only [volkSum, ← Finset.mul_sum, mul_left_comm]
  rw [HasVolkenborn, h]
  exact Filter.Tendsto.const_mul c hf

theorem HasVolkenborn.neg {f : ℚ_[p] → ℚ_[p]} {I : ℚ_[p]} (hf : HasVolkenborn p f I) :
    HasVolkenborn p (fun t => -f t) (-I) := by
  simpa using hf.const_mul (-1)

theorem HasVolkenborn.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p] → ℚ_[p]) (I : ι → ℚ_[p])
    (h : ∀ i ∈ s, HasVolkenborn p (f i) (I i)) :
    HasVolkenborn p (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, I i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hz : volkSum p (fun _ : ℚ_[p] => (0 : ℚ_[p])) = fun _ => 0 := by
        funext N; simp [volkSum]
      simp only [Finset.sum_empty, HasVolkenborn, hz]
      exact tendsto_const_nhds
  | insert a s ha ih =>
      have h1 : HasVolkenborn p (f a) (I a) := h a (Finset.mem_insert_self a s)
      have h2 : HasVolkenborn p (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, I i) :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have h3 := h1.add h2
      simp only [Finset.sum_insert ha]
      convert h3 using 2

/-! ## The telescoping (shift) identity -/

/-- The exact difference of the Riemann sums of `f(·+1)` and of `f`:
`volkSum f(·+1) N − volkSum f N = p^{-N}(f(p^N) − f(0))`. -/
theorem volkSum_shift (f : ℚ_[p] → ℚ_[p]) (N : ℕ) :
    volkSum p (fun t => f (t + 1)) N
      = volkSum p f N + ((p : ℚ_[p]) ^ N)⁻¹ * (f ((p ^ N : ℕ) : ℚ_[p]) - f 0) := by
  set F : ℕ → ℚ_[p] := fun t => f ((t : ℕ) : ℚ_[p]) with hF
  have hsum : ∑ t ∈ range (p ^ N), f (((t : ℕ) : ℚ_[p]) + 1)
      = ∑ t ∈ range (p ^ N), F t + (F (p ^ N) - F 0) := by
    have h2 : ∑ t ∈ range (p ^ N), (F (t + 1) - F t) = F (p ^ N) - F 0 :=
      Finset.sum_range_sub F (p ^ N)
    have h3 : ∑ t ∈ range (p ^ N), F (t + 1)
        = ∑ t ∈ range (p ^ N), F t + (F (p ^ N) - F 0) := by
      rw [← h2, Finset.sum_sub_distrib]
      ring
    rw [← h3]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [hF]
  simp only [volkSum, hsum, hF]
  push_cast
  ring

/-! ## The derivative limit for inverse powers -/

/-- `p ^ N → 0` in `ℚ_[p]`. -/
theorem tendsto_p_pow_zero (p : ℕ) [Fact p.Prime] :
    Tendsto (fun N : ℕ => ((p ^ N : ℕ) : ℚ_[p])) atTop (𝓝 0) := by
  have hnorm : ∀ N : ℕ, ‖((p ^ N : ℕ) : ℚ_[p])‖ = (p : ℝ)⁻¹ ^ N := by
    intro N
    push_cast
    rw [norm_pow, Padic.norm_p]
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simp only [hnorm]
  have hlt : |(p : ℝ)⁻¹| < 1 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [abs_of_nonneg (by positivity), inv_lt_one_iff₀]
    right; exact hp1
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlt

variable {c : ℚ_[p]}

/-- If `‖x‖ ≤ 1 < ‖c‖` then `x + c ≠ 0`. -/
theorem add_ne_zero_of_norm_lt {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hc : 1 < ‖c‖) : x + c ≠ 0 := by
  intro h
  have hcx : c = -x := by linear_combination (norm := ring_nf) h
  rw [hcx, norm_neg] at hc
  linarith

/-- The difference quotient of `x ↦ (x+c)^{-m}` at `0`, in closed form. -/
theorem inv_pow_diff_quot {x : ℚ_[p]} (hx : x ≠ 0) (hxc : x + c ≠ 0) (hc0 : c ≠ 0) (m : ℕ) :
    x⁻¹ * (((x + c) ^ m)⁻¹ - (c ^ m)⁻¹)
      = -(∑ j ∈ range m, (x + c) ^ j * c ^ (m - 1 - j)) * (((x + c) ^ m * c ^ m)⁻¹) := by
  have hxcm : (x + c) ^ m ≠ 0 := pow_ne_zero _ hxc
  have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc0
  have hgeom : c ^ m - (x + c) ^ m = -x * ∑ j ∈ range m, (x + c) ^ j * c ^ (m - 1 - j) := by
    have h2 : (∑ i ∈ range m, (x + c) ^ i * c ^ (m - 1 - i)) * ((x + c) - c)
        = (x + c) ^ m - c ^ m := geom_sum₂_mul (x + c) c m
    have h3 : (x + c) - c = x := by ring
    rw [h3] at h2
    linear_combination h2
  have key : ((x + c) ^ m)⁻¹ - (c ^ m)⁻¹ = (c ^ m - (x + c) ^ m) * ((x + c) ^ m * c ^ m)⁻¹ := by
    field_simp
  rw [key, hgeom]
  field_simp

/-- **The derivative limit, sequence form.**  For any sequence `x N → 0` of nonzero elements
of `ℤ_p`, the difference quotients of `x ↦ (x+c)^{-m}` at `0` converge to `−m·c^{-(m+1)}`. -/
theorem tendsto_diff_quot_seq (hc : 1 < ‖c‖) (m : ℕ) (x : ℕ → ℚ_[p]) (hx0 : ∀ N, x N ≠ 0)
    (hx1 : ∀ N, ‖x N‖ ≤ 1) (hxlim : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (x N)⁻¹ * ((((x N + c) ^ m)⁻¹) - ((c ^ m)⁻¹)))
      atTop (𝓝 (-(m : ℚ_[p]) * (c ^ (m + 1))⁻¹)) := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  set G : ℚ_[p] → ℚ_[p] := fun y =>
    -(∑ j ∈ range m, (y + c) ^ j * c ^ (m - 1 - j)) * (((y + c) ^ m * c ^ m)⁻¹) with hG
  have hGcont : ContinuousAt G 0 := by
    have hden : ((0 : ℚ_[p]) + c) ^ m * c ^ m ≠ 0 := by
      simp only [zero_add]
      exact mul_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hc0)
    refine ContinuousAt.mul ?_ (ContinuousAt.inv₀ ?_ hden)
    · exact (continuous_finset_sum _ fun j _ =>
        ((continuous_id.add continuous_const).pow j).mul continuous_const).neg.continuousAt
    · exact (((continuous_id.add continuous_const).pow m).mul continuous_const).continuousAt
  have hG0 : G 0 = -(m : ℚ_[p]) * (c ^ (m + 1))⁻¹ := by
    simp only [hG, zero_add]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hs : ∑ y ∈ range (k + 1), c ^ y * c ^ (k + 1 - 1 - y)
          = ((k + 1 : ℕ) : ℚ_[p]) * c ^ k := by
        rw [Finset.sum_congr rfl (fun j hj => ?_)]
        · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · simp only [mem_range] at hj
          rw [← pow_add]
          congr 1
          omega
      rw [hs]
      have h2 : c ^ k * (c ^ (k + 1) * c ^ (k + 1))⁻¹ = (c ^ (k + 1 + 1))⁻¹ := by
        field_simp
        ring
      rw [neg_mul, mul_assoc, h2, neg_mul]
  have heq : ∀ N : ℕ, (x N)⁻¹ * ((((x N + c) ^ m)⁻¹) - ((c ^ m)⁻¹)) = G (x N) := by
    intro N
    have hxc : x N + c ≠ 0 := add_ne_zero_of_norm_lt (hx1 N) hc
    rw [hG]
    exact inv_pow_diff_quot (hx0 N) hxc hc0 m
  simp only [heq]
  rw [← hG0]
  exact hGcont.tendsto.comp hxlim

/-- `p ^ N` is a nonzero element of `ℤ_p`. -/
theorem p_pow_ne_zero (p : ℕ) [Fact p.Prime] (N : ℕ) : (((p ^ N : ℕ) : ℚ_[p])) ≠ 0 := by
  have hnorm : ‖(((p ^ N : ℕ) : ℚ_[p]))‖ = (p : ℝ)⁻¹ ^ N := by
    push_cast; rw [norm_pow, Padic.norm_p]
  have hppos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  intro h
  rw [h, norm_zero] at hnorm
  nlinarith [pow_pos hppos N]

theorem norm_p_pow_le_one (p : ℕ) [Fact p.Prime] (N : ℕ) : ‖(((p ^ N : ℕ) : ℚ_[p]))‖ ≤ 1 := by
  simpa using (Padic.norm_int_le_one (p := p) ((p ^ N : ℕ) : ℤ))

/-- **The derivative limit.**  `p^{-N}((p^N + c)^{-m} − c^{-m}) → −m·c^{-(m+1)}`. -/
theorem tendsto_diff_quot (hc : 1 < ‖c‖) (m : ℕ) :
    Tendsto (fun N : ℕ => (((p : ℚ_[p]) ^ N))⁻¹ *
        ((((((p ^ N : ℕ) : ℚ_[p]) + c) ^ m)⁻¹) - ((c ^ m)⁻¹)))
      atTop (𝓝 (-(m : ℚ_[p]) * (c ^ (m + 1))⁻¹)) := by
  have hpow : ∀ N : ℕ, ((p : ℚ_[p]) ^ N) = (((p ^ N : ℕ) : ℚ_[p])) := by
    intro N; push_cast; ring
  simp only [hpow]
  exact tendsto_diff_quot_seq hc m _ (p_pow_ne_zero p) (norm_p_pow_le_one p)
    (tendsto_p_pow_zero p)

/-! ## The structural lemma -/

/-- **Shift by one.**  If `(t+c)^{-m}` has a Volkenborn integral, so does `(t+c+1)^{-m}`,
and the two differ by `−m·c^{-(m+1)}`. -/
theorem hasVolkenborn_shift (hc : 1 < ‖c‖) (m : ℕ) {I : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I) :
    HasVolkenborn p (fun t => ((t + (c + 1)) ^ m)⁻¹) (I + -(m : ℚ_[p]) * (c ^ (m + 1))⁻¹) := by
  set f : ℚ_[p] → ℚ_[p] := fun t => ((t + c) ^ m)⁻¹ with hf
  have hshift : (fun t : ℚ_[p] => ((t + (c + 1)) ^ m)⁻¹) = fun t => f (t + 1) := by
    funext t
    simp only [hf]
    ring_nf
  rw [hshift, HasVolkenborn]
  have hsum : ∀ N : ℕ, volkSum p (fun t => f (t + 1)) N
      = volkSum p f N + ((p : ℚ_[p]) ^ N)⁻¹ * (f ((p ^ N : ℕ) : ℚ_[p]) - f 0) :=
    volkSum_shift f
  rw [funext hsum]
  refine Filter.Tendsto.add hI ?_
  have hf0 : f 0 = (c ^ m)⁻¹ := by simp [hf]
  have hfx : ∀ N : ℕ, f ((p ^ N : ℕ) : ℚ_[p]) = (((((p ^ N : ℕ) : ℚ_[p]) + c) ^ m)⁻¹) := by
    intro N; simp [hf]
  simp only [hfx, hf0, mul_sub]
  have := tendsto_diff_quot (c := c) hc m
  simpa [mul_sub] using this

/-- **The structural lemma.**  Iterating the shift: for every `k`,

`∫ (t + c + k)^{-m} dt = ∫ (t + c)^{-m} dt − m ∑_{l < k} (c + l)^{-(m+1)}`,

and the left-hand integral exists as soon as the right-hand one does. -/
theorem hasVolkenborn_shift_nat (hc : 1 < ‖c‖) (m : ℕ) {I : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I) (k : ℕ) :
    HasVolkenborn p (fun t => ((t + (c + (k : ℚ_[p]))) ^ m)⁻¹)
      (I - (m : ℚ_[p]) * ∑ l ∈ range k, ((c + (l : ℚ_[p])) ^ (m + 1))⁻¹) := by
  induction k with
  | zero => simpa using hI
  | succ k ih =>
      have hck : 1 < ‖c + (k : ℚ_[p])‖ := by
        have hk : ‖(k : ℚ_[p])‖ ≤ 1 := by
          simpa using (Padic.norm_int_le_one (p := p) (k : ℤ))
        have hne : ‖c‖ ≠ ‖(k : ℚ_[p])‖ := by
          intro h; rw [h] at hc; linarith
        rw [Padic.add_eq_max_of_ne hne]
        exact lt_of_lt_of_le hc (le_max_left _ _)
      have h2 := hasVolkenborn_shift (c := c + (k : ℚ_[p])) hck m ih
      have hfun : (fun t : ℚ_[p] => ((t + (c + (k : ℚ_[p]) + 1)) ^ m)⁻¹)
          = fun t : ℚ_[p] => ((t + (c + ((k + 1 : ℕ) : ℚ_[p]))) ^ m)⁻¹ := by
        funext t
        push_cast
        ring_nf
      rw [hfun] at h2
      have hval : I - (m : ℚ_[p]) * ∑ l ∈ range k, ((c + (l : ℚ_[p])) ^ (m + 1))⁻¹
            + -(m : ℚ_[p]) * ((c + (k : ℚ_[p])) ^ (m + 1))⁻¹
          = I - (m : ℚ_[p]) * ∑ l ∈ range (k + 1), ((c + (l : ℚ_[p])) ^ (m + 1))⁻¹ := by
        rw [Finset.sum_range_succ]
        ring
      rwa [hval] at h2

/-! ## The 2-adic zeta values -/

/-- The normalisation `m·2^{m+1}·ζ₂(m+1) = ∫_{ℤ₂}(t+1/2)^{-m} dt` of the Kubota–Leopoldt
2-adic zeta value.  (That this agrees with the Kubota–Leopoldt function is classical and is
not formalised here; only the normalisation is used below.) -/
noncomputable def zeta2 (s : ℕ) : ℚ_[2] :=
  (volkInt 2 (fun t => ((t + 1 / 2) ^ (s - 1))⁻¹)) / (((s - 1 : ℕ) : ℚ_[2]) * 2 ^ s)

/-- `‖1/2‖₂ = 2 > 1`, the hypothesis needed for the structural lemma at `c = 1/2`. -/
theorem norm_half_2 : (1 : ℝ) < ‖(1 / 2 : ℚ_[2])‖ := by
  have h : ‖(1 / 2 : ℚ_[2])‖ = ‖(2 : ℚ_[2])‖⁻¹ := by
    rw [one_div, norm_inv]
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2)
    norm_num at this ⊢
    exact this
  rw [h, h2]
  norm_num

/-- **The structural lemma at `p = 2`, `c = 1/2`**, in the form used in the task:

`∫_{ℤ₂}(t + 1/2 + k)^{-m} dt = m·2^{m+1}·ζ₂(m+1) − m·∑_{l=1}^{k}(l − 1/2)^{-(m+1)}`.

The hypothesis is the (classical, unformalised) existence of the basic integral. -/
theorem volkInt_half_shift (m : ℕ) (hm : (m : ℚ_[2]) ≠ 0) (k : ℕ)
    (hI : ∃ I, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) I) :
    volkInt 2 (fun t => ((t + (1 / 2 + (k : ℚ_[2]))) ^ m)⁻¹)
      = (m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1)
        - (m : ℚ_[2]) * ∑ l ∈ range k, ((1 / 2 + (l : ℚ_[2])) ^ (m + 1))⁻¹ := by
  obtain ⟨I, hI⟩ := hI
  have hbase : volkInt 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) = I := hI.volkInt_eq
  have hz : (m : ℚ_[2]) * 2 ^ (m + 1) * zeta2 (m + 1) = I := by
    rw [zeta2]
    simp only [Nat.add_sub_cancel, hbase]
    field_simp
  rw [hz, ← (hasVolkenborn_shift_nat norm_half_2 m hI k).volkInt_eq]

end Hankel2
