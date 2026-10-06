import RequestProject.Zeta7.Hankel2.Volkenborn

/-!
# The reflection rule and the vanishing of `ζ₂` at even arguments

This file removes one of the two classical inputs that `Purity.lean` had to assume: it
*proves* `ζ₂(even) = 0` for the normalisation `Hankel2.zeta2`, i.e.

`∫_{ℤ₂} (t + 1/2)^{-m} dt = 0`  for odd `m`,

from the existence of the Volkenborn integrals alone.

The argument is the Volkenborn **reflection rule**

`∫ f(-t) dt = ∫ f(t) dt + f'(0)`,

proved here for `f(t) = (t+c)^{-m}` by comparing the Riemann sum of `f(-·)` with the Riemann
sum of `f(· − p^N)`: the reindexing `t ↦ p^N − t` is exact, and the resulting difference of
sums is `p^N · Ψ_N` where `Ψ_N` is a Volkenborn-type sum of the uniformly convergent family
of difference quotients, hence bounded — so the difference tends to `0`.

Combining the reflection rule with the shift rule of `Volkenborn.lean` at `p = 2`, `c = 1/2`
gives `I = −I` for odd `m`, because `−c + 1 = c`: the function is (anti)symmetric under
`t ↦ −1 − t`.
-/

namespace Hankel2

open Filter Finset Topology

variable {p : ℕ} [Fact p.Prime]

/-! ## Ultrametric preliminaries -/

theorem norm_sub_le_max' (u d : ℚ_[p]) : ‖u - d‖ ≤ max ‖u‖ ‖d‖ := by
  have h := IsUltrametricDist.norm_add_le_max u (-d)
  rwa [norm_neg, ← sub_eq_add_neg] at h

theorem norm_sub_eq_of_lt {u d : ℚ_[p]} (h : ‖d‖ < ‖u‖) : ‖u - d‖ = ‖u‖ := by
  have hne : ‖u‖ ≠ ‖-d‖ := by rw [norm_neg]; exact ne_of_gt h
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg]
  exact max_eq_left (le_of_lt h)

theorem norm_add_eq_of_lt {y c : ℚ_[p]} (h : ‖y‖ < ‖c‖) : ‖y + c‖ = ‖c‖ := by
  have hne : ‖y‖ ≠ ‖c‖ := ne_of_lt h
  rw [Padic.add_eq_max_of_ne hne]
  exact max_eq_right (le_of_lt h)

/-- `‖(u−d)^j − u^j‖ ≤ ‖d‖·‖u‖^{j−1}`. -/
theorem pow_sub_pow_norm_le (u d : ℚ_[p]) (h : ‖d‖ ≤ ‖u‖) (j : ℕ) :
    ‖(u - d) ^ j - u ^ j‖ ≤ ‖d‖ * ‖u‖ ^ (j - 1) := by
  have hud : ‖u - d‖ ≤ ‖u‖ := le_trans (norm_sub_le_max' u d) (max_le le_rfl h)
  have key : (∑ i ∈ range j, (u - d) ^ i * u ^ (j - 1 - i)) * ((u - d) - u) = (u - d) ^ j - u ^ j :=
    geom_sum₂_mul (u - d) u j
  have hsub : (u - d) - u = -d := by ring
  rw [hsub] at key
  rw [← key, norm_mul, norm_neg, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg d)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_pow]
  simp only [mem_range] at hi
  calc ‖u - d‖ ^ i * ‖u‖ ^ (j - 1 - i) ≤ ‖u‖ ^ i * ‖u‖ ^ (j - 1 - i) := by gcongr
    _ = ‖u‖ ^ (j - 1) := by rw [← pow_add]; congr 1; omega

/-! ## The uniform first-order estimate -/

/-- The difference quotient `Φ(u,d)` of `x ↦ x^{-m}` between `u−d` and `u` differs from its
value `m·u^{-(m+1)}` at `d = 0` by at most `‖d‖`, uniformly in `u` with `‖u‖ ≥ 1`. -/
theorem phi_sub_g_norm_le (u d : ℚ_[p]) (hu : 1 ≤ ‖u‖) (hd : ‖d‖ < ‖u‖) (m : ℕ) :
    ‖(∑ j ∈ range m, (u - d) ^ j * u ^ (m - 1 - j)) * (((u - d) ^ m * u ^ m)⁻¹)
        - (m : ℚ_[p]) * (u ^ (m + 1))⁻¹‖ ≤ ‖d‖ := by
  have hupos : (0 : ℝ) < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; linarith
  have hudn : ‖u - d‖ = ‖u‖ := norm_sub_eq_of_lt hd
  have hud0 : u - d ≠ 0 := by
    intro h; rw [h, norm_zero] at hudn; linarith
  set A : ℚ_[p] := ∑ j ∈ range m, (u - d) ^ j * u ^ (m - 1 - j) with hA
  set A0 : ℚ_[p] := (m : ℚ_[p]) * u ^ (m - 1) with hA0def
  set B : ℚ_[p] := ((u - d) ^ m * u ^ m)⁻¹ with hB
  set B0 : ℚ_[p] := (u ^ (2 * m))⁻¹ with hB0
  have hg : (m : ℚ_[p]) * (u ^ (m + 1))⁻¹ = A0 * B0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [hA0def]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hpow : u ^ k * (u ^ (2 * (k + 1)))⁻¹ = (u ^ (k + 1 + 1))⁻¹ := by
        field_simp
        rw [← pow_add]
        congr 1
        omega
      rw [hA0def, hB0, Nat.add_sub_cancel, mul_assoc, hpow]
  have hsplit : A * B - (m : ℚ_[p]) * (u ^ (m + 1))⁻¹ = (A - A0) * B + A0 * (B - B0) := by
    rw [hg]; ring
  -- the norm of `B`
  have hnB : ‖B‖ = (‖u‖ ^ (2 * m))⁻¹ := by
    rw [hB, norm_inv, norm_mul, norm_pow, norm_pow, hudn, ← pow_add]
    congr 2
    omega
  -- `‖A₀‖ ≤ ‖u‖^m`
  have hA0n : ‖A0‖ ≤ ‖u‖ ^ m := by
    rw [hA0def, norm_mul, norm_pow]
    have h1 : ‖(m : ℚ_[p])‖ ≤ 1 := by
      simpa using (Padic.norm_int_le_one (p := p) (m : ℤ))
    calc ‖(m : ℚ_[p])‖ * ‖u‖ ^ (m - 1) ≤ 1 * ‖u‖ ^ (m - 1) := by gcongr
      _ = ‖u‖ ^ (m - 1) := one_mul _
      _ ≤ ‖u‖ ^ m := pow_le_pow_right₀ hu (by omega)
  -- `‖A − A₀‖ ≤ ‖d‖·‖u‖^m`
  have hAn : ‖A - A0‖ ≤ ‖d‖ * ‖u‖ ^ m := by
    have hA0sum : A0 = ∑ j ∈ range m, u ^ j * u ^ (m - 1 - j) := by
      rw [hA0def, Finset.sum_congr rfl (fun j hj => ?_)]
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      · simp only [mem_range] at hj
        rw [← pow_add]
        congr 1
        omega
    rw [hA, hA0sum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj => ?_
    simp only [mem_range] at hj
    have hterm : (u - d) ^ j * u ^ (m - 1 - j) - u ^ j * u ^ (m - 1 - j)
        = ((u - d) ^ j - u ^ j) * u ^ (m - 1 - j) := by ring
    rw [hterm, norm_mul, norm_pow]
    have hstep : ‖(u - d) ^ j - u ^ j‖ * ‖u‖ ^ (m - 1 - j)
        ≤ (‖d‖ * ‖u‖ ^ (j - 1)) * ‖u‖ ^ (m - 1 - j) := by
      gcongr
      exact pow_sub_pow_norm_le u d (le_of_lt hd) j
    have heq : (‖d‖ * ‖u‖ ^ (j - 1)) * ‖u‖ ^ (m - 1 - j)
        = ‖d‖ * ‖u‖ ^ ((j - 1) + (m - 1 - j)) := by rw [pow_add]; ring
    have hlast : ‖d‖ * ‖u‖ ^ ((j - 1) + (m - 1 - j)) ≤ ‖d‖ * ‖u‖ ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (by omega)) (norm_nonneg _)
    linarith [hstep, heq.le, hlast]
  -- `‖B − B₀‖ ≤ ‖d‖·‖u‖^{−2m}`
  have hBn : ‖B - B0‖ ≤ ‖d‖ * (‖u‖ ^ (2 * m))⁻¹ := by
    have hpp : ‖(u - d) ^ m - u ^ m‖ ≤ ‖d‖ * ‖u‖ ^ (m - 1) :=
      pow_sub_pow_norm_le u d (le_of_lt hd) m
    have hfac : B - B0
        = (u ^ m * (u ^ m - (u - d) ^ m)) * (((u - d) ^ m * u ^ m)⁻¹ * (u ^ (2 * m))⁻¹) := by
      have h2 : u ^ (2 * m) = u ^ m * u ^ m := by rw [← pow_add]; congr 1; omega
      rw [hB, hB0, h2]
      field_simp
    rw [hfac, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_mul, norm_pow, norm_pow,
      norm_pow, hudn, ← pow_add]
    have hmm : m + m = 2 * m := by omega
    rw [hmm]
    have hsub : ‖u ^ m - (u - d) ^ m‖ ≤ ‖d‖ * ‖u‖ ^ (m - 1) := by
      rw [← norm_neg]
      simpa using hpp
    calc ‖u‖ ^ m * ‖u ^ m - (u - d) ^ m‖ * ((‖u‖ ^ (2 * m))⁻¹ * (‖u‖ ^ (2 * m))⁻¹)
        ≤ ‖u‖ ^ m * (‖d‖ * ‖u‖ ^ (m - 1)) * ((‖u‖ ^ (2 * m))⁻¹ * (‖u‖ ^ (2 * m))⁻¹) := by
          gcongr
      _ = ‖d‖ * ((‖u‖ ^ m * ‖u‖ ^ (m - 1)) * (‖u‖ ^ (2 * m))⁻¹) * (‖u‖ ^ (2 * m))⁻¹ := by ring
      _ ≤ ‖d‖ * 1 * (‖u‖ ^ (2 * m))⁻¹ := by
          gcongr
          rw [← pow_add, inv_eq_one_div, mul_one_div, div_le_one (by positivity)]
          exact pow_le_pow_right₀ hu (by omega)
      _ = ‖d‖ * (‖u‖ ^ (2 * m))⁻¹ := by ring
  -- put the two pieces together
  have hsmall : ‖u‖ ^ m * (‖u‖ ^ (2 * m))⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, mul_one_div, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hu (by omega)
  have h1 : ‖(A - A0) * B‖ ≤ ‖d‖ := by
    rw [norm_mul, hnB]
    calc ‖A - A0‖ * (‖u‖ ^ (2 * m))⁻¹ ≤ (‖d‖ * ‖u‖ ^ m) * (‖u‖ ^ (2 * m))⁻¹ := by
          gcongr
      _ = ‖d‖ * (‖u‖ ^ m * (‖u‖ ^ (2 * m))⁻¹) := by ring
      _ ≤ ‖d‖ * 1 := by gcongr
      _ = ‖d‖ := mul_one _
  have h2 : ‖A0 * (B - B0)‖ ≤ ‖d‖ := by
    rw [norm_mul]
    calc ‖A0‖ * ‖B - B0‖ ≤ ‖u‖ ^ m * (‖d‖ * (‖u‖ ^ (2 * m))⁻¹) := by
          gcongr
      _ = ‖d‖ * (‖u‖ ^ m * (‖u‖ ^ (2 * m))⁻¹) := by ring
      _ ≤ ‖d‖ * 1 := by gcongr
      _ = ‖d‖ := mul_one _
  rw [hsplit]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 h2)

/-! ## Riemann-sum preliminaries -/

/-- The ultrametric bound on a Volkenborn Riemann sum. -/
theorem norm_volkSum_le (f : ℚ_[p] → ℚ_[p]) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ t : ℕ, ‖f ((t : ℕ) : ℚ_[p])‖ ≤ C) : ‖volkSum p f N‖ ≤ (p : ℝ) ^ N * C := by
  rw [volkSum, norm_mul]
  have hnorm : ‖(((p : ℚ_[p]) ^ N))⁻¹‖ = (p : ℝ) ^ N := by
    rw [norm_inv, norm_pow, Padic.norm_p]
    simp
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun t _ => h t

/-- Reindexing `t ↦ M − t` in a Riemann sum of `f(−t)`. -/
theorem sum_neg_reindex (f : ℚ_[p] → ℚ_[p]) (M : ℕ) (hM : 0 < M) :
    ∑ t ∈ range M, f (-(t : ℚ_[p]))
      = ∑ s ∈ range M, f ((s : ℚ_[p]) - (M : ℚ_[p])) + f 0 - f (-(M : ℚ_[p])) := by
  have h1 : ∑ t ∈ range M, f (-(t : ℚ_[p]))
      = f 0 + ∑ t ∈ Ico 1 M, f (-(t : ℚ_[p])) := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM]
    simp
  have h2 : ∑ s ∈ range M, f ((s : ℚ_[p]) - (M : ℚ_[p]))
      = f (-(M : ℚ_[p])) + ∑ s ∈ Ico 1 M, f ((s : ℚ_[p]) - (M : ℚ_[p])) := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hM]
    simp
  have h3 : ∑ t ∈ Ico 1 M, f (-(t : ℚ_[p])) = ∑ s ∈ Ico 1 M, f ((s : ℚ_[p]) - (M : ℚ_[p])) := by
    refine Finset.sum_nbij' (i := fun t => M - t) (j := fun s => M - s) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      simp only []
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      simp only []
      omega
    · intro a ha
      simp only [mem_Ico] at ha
      have hcast : ((M - a : ℕ) : ℚ_[p]) = (M : ℚ_[p]) - (a : ℚ_[p]) := by
        have hle : a ≤ M := by omega
        push_cast [hle]
        ring
      rw [hcast]
      congr 1
      ring
  rw [h1, h2, h3]
  ring

theorem volkSum_add (f g : ℚ_[p] → ℚ_[p]) (N : ℕ) :
    volkSum p (fun t => f t + g t) N = volkSum p f N + volkSum p g N := by
  simp only [volkSum, Finset.sum_add_distrib, mul_add]

theorem volkSum_const_mul (a : ℚ_[p]) (f : ℚ_[p] → ℚ_[p]) (N : ℕ) :
    volkSum p (fun t => a * f t) N = a * volkSum p f N := by
  simp only [volkSum, ← Finset.mul_sum, mul_left_comm]

/-! ## The reflection rule -/

variable {c : ℚ_[p]}

/-- The exact difference of two inverse powers as a multiple of `d`. -/
theorem inv_pow_shift_diff {u d : ℚ_[p]} (hd0 : d ≠ 0) (hu0 : u ≠ 0) (hud0 : u - d ≠ 0) (m : ℕ) :
    ((u - d) ^ m)⁻¹ - (u ^ m)⁻¹
      = d * ((∑ j ∈ range m, (u - d) ^ j * u ^ (m - 1 - j)) * (((u - d) ^ m * u ^ m)⁻¹)) := by
  have hru : -d + u = u - d := by ring
  have h := inv_pow_diff_quot (c := u) (x := -d) (neg_ne_zero.mpr hd0)
    (by rw [hru]; exact hud0) hu0 m
  rw [hru] at h
  have h2 := congrArg (fun z : ℚ_[p] => (-d) * z) h
  simp only at h2
  rw [← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hd0), one_mul] at h2
  rw [h2]
  ring

set_option maxHeartbeats 1000000 in
/-- **The reflection rule** for `f(t) = (t+c)^{-m}`: `∫ f(−t) dt = ∫ f dt + f'(0)`. -/
theorem hasVolkenborn_reflect (hc : 1 < ‖c‖) (m : ℕ) {I J : ℚ_[p]}
    (hI : HasVolkenborn p (fun t => ((t + c) ^ m)⁻¹) I)
    (hJ : HasVolkenborn p (fun t => ((t + c) ^ (m + 1))⁻¹) J) :
    HasVolkenborn p (fun t => ((-t + c) ^ m)⁻¹) (I - (m : ℚ_[p]) * (c ^ (m + 1))⁻¹) := by
  classical
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  have hc1 : (1 : ℝ) ≤ ‖c‖ := le_of_lt hc
  set f : ℚ_[p] → ℚ_[p] := fun t => ((t + c) ^ m)⁻¹ with hf
  set d : ℕ → ℚ_[p] := fun N => ((p ^ N : ℕ) : ℚ_[p]) with hd
  have hd0 : ∀ N, d N ≠ 0 := fun N => p_pow_ne_zero p N
  have hdle : ∀ N, ‖d N‖ ≤ 1 := fun N => norm_p_pow_le_one p N
  have hdnorm : ∀ N, ‖d N‖ = ((p : ℝ) ^ N)⁻¹ := by
    intro N
    rw [hd]
    push_cast
    rw [norm_pow, Padic.norm_p, ← inv_pow]
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_p_pow_zero p
  have hppow : ∀ N : ℕ, ((p : ℚ_[p]) ^ N) = d N := by
    intro N; rw [hd]; push_cast; ring
  -- norms of the shifted points
  have hunorm : ∀ y : ℚ_[p], ‖y‖ ≤ 1 → ‖y + c‖ = ‖c‖ := by
    intro y hy
    exact norm_add_eq_of_lt (lt_of_le_of_lt hy hc)
  have hnatnorm : ∀ t : ℕ, ‖((t : ℕ) : ℚ_[p])‖ ≤ 1 := by
    intro t
    simpa using (Padic.norm_int_le_one (p := p) (t : ℤ))
  -- the pointwise difference identity
  have hpoint : ∀ (N : ℕ) (t : ℕ),
      f (((t : ℕ) : ℚ_[p]) - d N) - f ((t : ℕ) : ℚ_[p])
        = d N * ((∑ j ∈ range m, (((t : ℕ) : ℚ_[p]) + c - d N) ^ j
              * (((t : ℕ) : ℚ_[p]) + c) ^ (m - 1 - j))
            * ((((t : ℕ) : ℚ_[p]) + c - d N) ^ m * (((t : ℕ) : ℚ_[p]) + c) ^ m)⁻¹) := by
    intro N t
    have hu : ‖((t : ℕ) : ℚ_[p]) + c‖ = ‖c‖ := hunorm _ (hnatnorm t)
    have hu0 : ((t : ℕ) : ℚ_[p]) + c ≠ 0 := by
      intro h; rw [h, norm_zero] at hu; linarith
    have hud : ‖(((t : ℕ) : ℚ_[p]) + c) - d N‖ = ‖((t : ℕ) : ℚ_[p]) + c‖ := by
      refine norm_sub_eq_of_lt ?_
      rw [hu]
      exact lt_of_le_of_lt (hdle N) hc
    have hud0 : (((t : ℕ) : ℚ_[p]) + c) - d N ≠ 0 := by
      intro h; rw [h, norm_zero] at hud; rw [hu] at hud; linarith
    have hfeq : f (((t : ℕ) : ℚ_[p]) - d N) = (((((t : ℕ) : ℚ_[p]) + c) - d N) ^ m)⁻¹ := by
      rw [hf]
      ring_nf
    rw [hfeq, hf]
    exact inv_pow_shift_diff (hd0 N) hu0 hud0 m
  -- the difference-quotient family and its limit function
  set Φ : ℕ → ℚ_[p] → ℚ_[p] := fun N y =>
    (∑ j ∈ range m, (y + c - d N) ^ j * (y + c) ^ (m - 1 - j))
      * (((y + c - d N) ^ m * (y + c) ^ m)⁻¹) with hΦ
  set g : ℚ_[p] → ℚ_[p] := fun y => (m : ℚ_[p]) * (((y + c) ^ (m + 1))⁻¹) with hgdef
  -- the Riemann sums of the shifted function
  have hdiffsum : ∀ N, volkSum p (fun y => f (y - d N)) N
      = volkSum p f N + d N * volkSum p (Φ N) N := by
    intro N
    have hsum : ∑ t ∈ range (p ^ N), f (((t : ℕ) : ℚ_[p]) - d N)
        = ∑ t ∈ range (p ^ N), f ((t : ℕ) : ℚ_[p])
          + d N * ∑ t ∈ range (p ^ N), Φ N ((t : ℕ) : ℚ_[p]) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have h := hpoint N t
      rw [hΦ]
      linear_combination h
    simp only [volkSum, hsum]
    ring
  -- the sums of `Φ` are bounded
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ N, ‖volkSum p (fun y => ((y + c) ^ (m + 1))⁻¹) N‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hJ.norm).bddAbove_range
    exact ⟨M, fun N => hM ⟨N, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hPsi : ∀ N, ‖volkSum p (Φ N) N‖ ≤ max M 1 := by
    intro N
    have hsplit : Φ N = fun y => g y + (Φ N y - g y) := by
      funext y; ring
    rw [hsplit, volkSum_add]
    have h1 : ‖volkSum p g N‖ ≤ M := by
      rw [hgdef, volkSum_const_mul, norm_mul]
      have hm1 : ‖(m : ℚ_[p])‖ ≤ 1 := by
        simpa using (Padic.norm_int_le_one (p := p) (m : ℤ))
      calc ‖(m : ℚ_[p])‖ * ‖volkSum p (fun y => ((y + c) ^ (m + 1))⁻¹) N‖
          ≤ 1 * ‖volkSum p (fun y => ((y + c) ^ (m + 1))⁻¹) N‖ := by gcongr
        _ = ‖volkSum p (fun y => ((y + c) ^ (m + 1))⁻¹) N‖ := one_mul _
        _ ≤ M := hM N
    have h2 : ‖volkSum p (fun y => Φ N y - g y) N‖ ≤ 1 := by
      have hb : ∀ t : ℕ, ‖Φ N ((t : ℕ) : ℚ_[p]) - g ((t : ℕ) : ℚ_[p])‖ ≤ ‖d N‖ := by
        intro t
        have hu : ‖((t : ℕ) : ℚ_[p]) + c‖ = ‖c‖ := hunorm _ (hnatnorm t)
        have h := phi_sub_g_norm_le (((t : ℕ) : ℚ_[p]) + c) (d N) (by rw [hu]; exact hc1)
          (by rw [hu]; exact lt_of_le_of_lt (hdle N) hc) m
        rw [hΦ, hgdef]
        exact h
      have h3 := norm_volkSum_le (fun y => Φ N y - g y) N ‖d N‖ (norm_nonneg _) hb
      rw [hdnorm N] at h3
      have hppos : (0 : ℝ) < (p : ℝ) ^ N := by
        have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
        positivity
      rwa [mul_inv_cancel₀ (ne_of_gt hppos)] at h3
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _)))
  -- hence the correction term tends to zero
  have hbound : ∀ N, ‖d N * volkSum p (Φ N) N‖ ≤ ((p : ℝ) ^ N)⁻¹ * max M 1 := by
    intro N
    rw [norm_mul, hdnorm N]
    exact mul_le_mul_of_nonneg_left (hPsi N) (by positivity)
  have htend : Tendsto (fun N : ℕ => ((p : ℝ) ^ N)⁻¹ * max M 1) atTop (𝓝 0) := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hz : Tendsto (fun N : ℕ => ((p : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp1)
    simpa using hz.mul_const (max M 1)
  have hzero : Tendsto (fun N => d N * volkSum p (Φ N) N) atTop (𝓝 0) :=
    squeeze_zero_norm hbound htend
  -- the reflection identity for the Riemann sums
  have hrefl : ∀ N, volkSum p (fun y => f (-y)) N
      = volkSum p (fun y => f (y - d N)) N + (((p : ℚ_[p]) ^ N))⁻¹ * (f 0 - f (-(d N))) := by
    intro N
    have hMpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
    have hre := sum_neg_reindex f (p ^ N) hMpos
    have hcast : ((p ^ N : ℕ) : ℚ_[p]) = d N := rfl
    rw [hcast] at hre
    simp only [volkSum, hre, hppow N]
    ring
  -- the boundary term
  have hD : Tendsto (fun N => (((p : ℚ_[p]) ^ N))⁻¹ * (f 0 - f (-(d N)))) atTop
      (𝓝 (-(m : ℚ_[p]) * (c ^ (m + 1))⁻¹)) := by
    have hx0 : ∀ N, -(d N) ≠ 0 := fun N => neg_ne_zero.mpr (hd0 N)
    have hx1 : ∀ N, ‖-(d N)‖ ≤ 1 := by
      intro N; rw [norm_neg]; exact hdle N
    have hxlim : Tendsto (fun N => -(d N)) atTop (𝓝 0) := by
      simpa using hdlim.neg
    have hq := tendsto_diff_quot_seq hc m (fun N => -(d N)) hx0 hx1 hxlim
    have heq : ∀ N : ℕ, (-(d N))⁻¹ * (((((-(d N)) + c) ^ m)⁻¹) - ((c ^ m)⁻¹))
        = (((p : ℚ_[p]) ^ N))⁻¹ * (f 0 - f (-(d N))) := by
      intro N
      have hf0 : f 0 = (c ^ m)⁻¹ := by rw [hf]; simp
      have hfd : f (-(d N)) = ((((-(d N)) + c) ^ m)⁻¹) := by rw [hf]
      rw [hf0, hfd, hppow N, inv_neg]
      ring
    simpa only [heq] using hq
  -- assemble
  have hcomb : ∀ N, volkSum p (fun y => f (-y)) N
      = (volkSum p f N + d N * volkSum p (Φ N) N)
        + (((p : ℚ_[p]) ^ N))⁻¹ * (f 0 - f (-(d N))) := by
    intro N
    rw [hrefl N, hdiffsum N]
  have hfinal : Tendsto (volkSum p (fun y => f (-y))) atTop
      (𝓝 (I + 0 + -(m : ℚ_[p]) * (c ^ (m + 1))⁻¹)) :=
    Filter.Tendsto.congr (fun N => (hcomb N).symm)
      (Filter.Tendsto.add (Filter.Tendsto.add hI hzero) hD)
  have hval : I + 0 + -(m : ℚ_[p]) * (c ^ (m + 1))⁻¹ = I - (m : ℚ_[p]) * (c ^ (m + 1))⁻¹ := by
    ring
  rw [hval] at hfinal
  exact hfinal

/-! ## `ζ₂` vanishes at even arguments -/

/-- For odd `m` the basic integral `∫_{ℤ₂}(t+1/2)^{-m} dt` vanishes.  This is the 2-adic
statement `ζ₂(even) = 0` in the normalisation of `Hankel2.zeta2`.

The proof combines the reflection rule with the shift rule: the substitution `t ↦ −1 − t`
fixes the family (because `−1/2 + 1 = 1/2`) and negates the integrand when `m` is odd. -/
theorem volkInt_inv_pow_half_odd (m : ℕ) (hm : Odd m) {I J : ℚ_[2]}
    (hI : HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ m)⁻¹) I)
    (hJ : HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ (m + 1))⁻¹) J) :
    I = 0 := by
  have hc : (1 : ℝ) < ‖(1 / 2 : ℚ_[2])‖ := norm_half_2
  have hcneg : (1 : ℝ) < ‖(-(1 / 2) : ℚ_[2])‖ := by rwa [norm_neg]
  -- reflection
  have h1 := hasVolkenborn_reflect hc m hI hJ
  -- the reflected function is `−(t − 1/2)^{-m}`
  have hfun : (fun t : ℚ_[2] => ((-t + 1 / 2) ^ m)⁻¹)
      = fun t : ℚ_[2] => -(((t + -(1 / 2)) ^ m)⁻¹) := by
    funext t
    have hneg : (-t + 1 / 2 : ℚ_[2]) = -(t + -(1 / 2)) := by ring
    rw [hneg, hm.neg_pow, inv_neg]
  rw [hfun] at h1
  have h2 : HasVolkenborn 2 (fun t : ℚ_[2] => ((t + -(1 / 2)) ^ m)⁻¹)
      (-(I - (m : ℚ_[2]) * (((1 : ℚ_[2]) / 2) ^ (m + 1))⁻¹)) := by
    have := h1.neg
    simpa using this
  -- shift back by one
  have h3 := hasVolkenborn_shift (c := (-(1 / 2) : ℚ_[2])) hcneg m h2
  have hshift : (-(1 / 2) + 1 : ℚ_[2]) = 1 / 2 := by ring
  rw [hshift] at h3
  -- the two descriptions of the same integral must agree
  have hsame := hI.unique h3
  have hpow : ((-(1 / 2) : ℚ_[2]) ^ (m + 1)) = ((1 / 2 : ℚ_[2]) ^ (m + 1)) := by
    obtain ⟨k, rfl⟩ := hm
    have hev : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
    exact hev.neg_pow _
  rw [hpow] at hsame
  linear_combination hsame / 2

/-- **`ζ₂` vanishes at even arguments** (in the normalisation `Hankel2.zeta2`), given the
existence of the two Volkenborn integrals involved. -/
theorem zeta2_even_eq_zero (s : ℕ) (hs : Even s) (hs2 : 2 ≤ s)
    (hI : ∃ I, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ (s - 1))⁻¹) I)
    (hJ : ∃ J, HasVolkenborn 2 (fun t => ((t + 1 / 2) ^ (s - 1 + 1))⁻¹) J) :
    zeta2 s = 0 := by
  obtain ⟨I, hI⟩ := hI
  obtain ⟨J, hJ⟩ := hJ
  have hodd : Odd (s - 1) := by
    obtain ⟨k, rfl⟩ := hs
    refine ⟨k - 1, by omega⟩
  have hzero : I = 0 := volkInt_inv_pow_half_odd (s - 1) hodd hI hJ
  rw [zeta2, hI.volkInt_eq, hzero, zero_div]

end Hankel2
