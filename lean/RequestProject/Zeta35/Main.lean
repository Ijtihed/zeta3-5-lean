import RequestProject.Zeta35.Criterion
import RequestProject.Zeta35.PrimeInputs
import RequestProject.Zeta35.ArchProfile
import RequestProject.Zeta35.DecayBound
import RequestProject.Zeta35.TreeBound

/-!
# The irrationality of `ζ₃(5)`: the logical assembly (paper N, §7)

`Zeta35.Zeta35Inputs` collects, as explicit fields, exactly the inputs of N that are not yet
formalised, each stated as in N in terms of the true Hankel polynomial `Δ_K = Zeta35.hankelPoly n K`
of the functional `L(P) = ∑_{a=1,2} ∫_{ℤ₃} (P W)'(t + a/3) dt` (`Defs.lean`, `Purity.lean`):

* (i)   `decay` — N, Theorem 3.1 (3-adic decay);
* (ii)  `arch` — N, Theorem 4.1 (archimedean size) for `κ = K/n ∈ [5.9, 6]` and the profile
        `σ_κ ≡ κ/3`;
* (iii) ~~`tree`~~ — the tree bound `−v_ℓ(Δ_K) ≤ T_ℓ` for all primes `ℓ ≠ 3` (N, §5; P, Thm 7.1;
        W, Thm 3.2): **proved** (`Zeta35.tree_bound`, `TreeBound.lean`, for every prime, including
        `ℓ = 2`), so it is no longer a field (see `tree_field_holds`);
        `cRest`, `thm_5_1` — N, Theorem 5.1 (the prime sum with constant `c(κ)`,
        stated for any limit `M₀` of the Mertens sum with `ℓ = 3` removed); `table_c` — the
        certificate bound `c(κ) ≤ 71.2` on `[5.9, 6]` (N, Appendix A; relaxed from
        `c(6) ≤ 71.075041`, CLAIMS T5);
* (iv)  `nonvanishing` — N, Theorem 6.2 (strict dominance at an admissible prime).

`Zeta35.zeta3_five_irrational` derives `ζ₃(5) ∉ ℚ` from these fields together with the proved
ingredients: purity (`Purity.lean`), the tree bound (`Zeta35.tree_bound`), the criterion (`Zeta35.pden_criterion`, N Lemma 2.3), the
auxiliary prime from the prime number theorem (`Zeta35.aux_prime3`), Mertens' theorem with `ℓ = 3`
removed (`Zeta35.tendsto_mertens3`), the closed form of `F[σ_κ]` and the bound on `gap(σ_κ)`
(`Zeta35.Fdag_sigmaK_le`), the asymptotics of the decay exponent (`Zeta35.decayExp_ge`), and the
budget arithmetic of N, §7 (margin `> 4` bits on `[5.9, 6]`).
-/

open Polynomial Finset Filter Topology

namespace Zeta35

open Hankel2

/-- **The inputs of N still missing**, each stated as in N. -/
structure Zeta35Inputs where
  /-- (i) **N, Theorem 3.1 (3-adic decay)**: for even `n` and `2 ≤ K ≤ 6n + 2`,
  `v₃(Δ_K(ζ₃(5))) ≥ 2 ∑_{i<K} v₃(i!_S) + K(4(3n+1) − log₃ D − log₃(D+1))`, `D = 2K − 2`,
  stated as `‖Δ_K(ζ₃(5))‖₃ ≤ 3^{−(…)}`. -/
  decay : ∀ n K : ℕ, Even n → 2 ≤ K → K ≤ 6 * n + 2 →
    ‖aeval (zeta3 5) (hankelPoly n K)‖ ≤ (3 : ℝ) ^ (-decayExp n K)
  /-- (ii) **N, Theorem 4.1 (archimedean size)** for `κ = K/n ∈ [5.9, 6]` and the feasible
  profile `σ_κ ≡ κ/3`: `ln ‖Δ_K‖₁ ≤ (κ² − 12κ) n² ln n + n² (F[σ_κ] + gap(σ_κ)) + o(n²)`. -/
  arch : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
    (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 →
      Real.log (l1 (hankelPoly n K)) ≤
        (((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy3 (sigmaK ((K : ℝ) / n)) +
              gap3 ((K : ℝ) / n) (sigmaK ((K : ℝ) / n)))
          + ε * (n : ℝ) ^ 2
  -- (iii-a) **The tree bound** (N, §5; P, Thm 7.1; W, Thm 3.2) is proved (`tree_bound`), see
  -- `tree_field_holds` below for the field in its original form.
  /-- The `κ`-dependent part `rest(κ) = I(κ) + 3κ/20 + 2/400` of `c(κ)` (in nats; `I(κ)` is the
  circle-model integral of N, Theorem 5.1). -/
  cRest : ℝ → ℝ
  /-- (iii-b) **N, Theorem 5.1**: if `∑_{ℓ ≤ Y, ℓ ≠ 3} ln ℓ/(ℓ−1) = ln Y + M₀ + o(1)`, then,
  uniformly for `κ = K/n ∈ [5.9, 6]`,
  `∑_{ℓ ≠ 3} max(T_ℓ, 0) log₂ ℓ ≤ κ(12 − κ) n² log₂ n + c(κ) n² + o(n²)` with
  `c(κ) = [κ(12−κ)(M₀ − ln 20) + rest(κ)]/ln 2` (stated for every finite set of primes `≠ 3`). -/
  thm_5_1 : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertens3Sum Y - Real.log Y) atTop (𝓝 M₀) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
      (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 3) →
        ∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.logb 2 ℓ ≤
          ((K : ℝ) / n) * (12 - (K : ℝ) / n) * (n : ℝ) ^ 2 * Real.logb 2 n
            + cConst M₀ cRest ((K : ℝ) / n) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2
  /-- (iii-c) **The certificate bound** (N, Appendix A; CLAIMS T5, relaxed):
  `c(κ) ≤ 71.2` for `κ ∈ [5.9, 6]`, with the true Mertens constant `−γ − ½ ln 3`. -/
  table_c : ∀ κ : ℝ, 5.9 ≤ κ → κ ≤ 6 → cConst mertens3Const cRest κ ≤ 71.2
  /-- (iv) **N, Theorem 6.2 (non-vanishing)**: for even `n` and an admissible prime `ℓ`
  (`ℓ > R`, `ℓ ≥ 7`, `ℓ − R ≤ ℓ/3`, `ℓ ∤ b`), `Δ_K(a/b) ≠ 0` for `K = 4(3n + 1 − ℓ)`. -/
  nonvanishing : ∀ n ℓ : ℕ, Even n → ℓ.Prime → R n < ℓ → 7 ≤ ℓ → 3 * (ℓ - R n) ≤ ℓ →
    ∀ r : ℚ, ¬ ℓ ∣ r.den → (hankelPoly n (4 * (3 * n + 1 - ℓ))).eval r ≠ 0

/-- The former field (iii-a) `tree` of `Zeta35Inputs`, in exactly its original form: **the tree
bound** `−v_ℓ(Δ_K) ≤ T_ℓ` for every prime `ℓ ≠ 3` (N, §5; P, Thm 7.1; W, Thm 3.2).  It holds
unconditionally (`tree_bound`, which needs neither `ℓ ≠ 3` nor any condition on `n`, `K`). -/
theorem tree_field_holds :
    ∀ n K ℓ : ℕ, ℓ.Prime → ℓ ≠ 3 → negTop (gaussVal ℓ (hankelPoly n K)) ≤ TP ℓ n K :=
  fun n K ℓ hℓ _ => tree_bound n K ℓ hℓ

/-! ### Auxiliary facts for the assembly -/

/-- `deg Δ_K ≤ K`. -/
theorem natDegree_hankelPoly_le (n K : ℕ) : (hankelPoly n K).natDegree ≤ K := by
  have h := Polynomial.natDegree_det_X_add_C_le
    (Matrix.of fun i j : Fin K => aL n (X ^ ((i : ℕ) + j)))
    (Matrix.of fun i j : Fin K => bL n (X ^ ((i : ℕ) + j)))
  rw [Fintype.card_fin] at h
  refine le_of_eq_of_le ?_ h
  unfold hankelPoly
  congr 1
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-- The lower-order terms are eventually dominated by `n²`. -/
theorem eventually_lower_order3 (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) * (1 + Real.logb 2 n) + D * n < (n : ℝ) ^ 2 := by
  refine ⟨⌈(4 * C + D + 2) ^ 2⌉₊, fun n hn => ?_⟩
  have hn' : (4 * C + D + 2) ^ 2 ≤ (n : ℝ) := (Nat.ceil_le).1 hn
  set s := Real.sqrt n
  have hs : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsbig : 4 * C + D + 2 ≤ s := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 4 * C + D + 2)]
    exact Real.sqrt_le_sqrt hn'
  have hspos : 0 < s := by linarith
  have hlog : Real.log n ≤ 2 * s := by
    rw [← hs, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hspos
    push_cast; linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : Real.logb 2 n ≤ 3 * s := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  rw [← hs]
  have h1 : C * s ^ 2 * (1 + Real.logb 2 (s ^ 2)) ≤ C * s ^ 2 * (1 + 3 * s) := by
    rw [hs]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hs1 : 1 ≤ s := by linarith
  nlinarith [mul_pos hspos hspos, mul_pos (mul_pos hspos hspos) hspos,
    mul_nonneg hC (mul_nonneg hs0 hs0), mul_nonneg hD hs0,
    mul_nonneg (mul_nonneg hC hs0) (sub_nonneg.2 hs1)]

/-- A nonzero polynomial has a finite Gauss valuation. -/
theorem gaussVal_eq_coe' {F : ℚ[X]} (hF : F ≠ 0) (p : ℕ) : ∃ g : ℤ, gaussVal p F = g := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf F.support (nonempty_support_iff.mpr hF)
    (fun i => ((padicValRat p (F.coeff i) : ℤ) : WithTop ℤ))
  exact ⟨_, hi⟩

/-- From `−g ≤ T_ℓ` to `max(−g, 0) ≤ max(T_ℓ, 0)`. -/
theorem max_neg_le_TPplus {ℓ n K : ℕ} {g : ℤ} (h : negTop (g : WithTop ℤ) ≤ TP ℓ n K) :
    max (-g) 0 ≤ TPplus ℓ n K := by
  have h' : (((-g : ℤ)) : WithBot ℤ) ≤ TP ℓ n K := h
  unfold TPplus
  generalize TP ℓ n K = T at h' ⊢
  induction T using WithBot.recBotCoe with
  | bot => exact absurd h' (by simp)
  | coe t =>
      have ht : -g ≤ t := by exact_mod_cast h'
      rw [show max ((t : WithBot ℤ)) 0 = ((max t 0 : ℤ) : WithBot ℤ) by
        rw [← WithBot.coe_zero, ← WithBot.coe_max]]
      simp only [WithBot.unbotD_coe]
      exact max_le_max ht le_rfl

/-- `‖Δ‖₁ > 0` for `Δ ≠ 0`. -/
theorem l1_pos' {F : ℚ[X]} (hF : F ≠ 0) : 0 < l1 F := by
  unfold l1
  refine Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨F.natDegree, by simp, ?_⟩
  simpa [abs_pos] using hF

/-- `log₂ 3 · log₃ y = log₂ y`. -/
theorem logb_two_three_mul (y : ℝ) : Real.logb 2 3 * Real.logb 3 y = Real.logb 2 y := by
  have h3 : Real.log 3 ≠ 0 := by positivity
  simp only [Real.logb]
  field_simp

/-- **The budget (N, §7; CLAIMS T9)**: on `κ ∈ [5.9, 6]`, with `c(κ) ≤ 71.2` and
`F†(κ) ≤ (54 − 36 ln 3)/ln 2 + 3κ(4 − 2κ/3)`, the margin is at least `4` bits:
`c + F† + 4 ≤ log₂ 3 · (12κ − κ²/4)`. -/
theorem budget {κ c : ℝ} (h1 : 5.9 ≤ κ) (h2 : κ ≤ 6) (hc : c ≤ 71.2) :
    c + ((54 - 36 * Real.log 3) / Real.log 2 + 3 * κ * (4 - 2 * κ / 3)) + 4 ≤
      Real.logb 2 3 * (12 * κ - κ ^ 2 / 4) := by
  obtain ⟨l3a, l3b⟩ := log_three_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hl2 : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_mul_eq_mul_div, le_div_iff₀ hl2]
  have hAl : (54 - 36 * Real.log 3) / Real.log 2 * Real.log 2 = 54 - 36 * Real.log 3 :=
    div_mul_cancel₀ _ hl2.ne'
  have e : (c + ((54 - 36 * Real.log 3) / Real.log 2 + 3 * κ * (4 - 2 * κ / 3)) + 4) * Real.log 2 =
      (c + 3 * κ * (4 - 2 * κ / 3) + 4) * Real.log 2 + (54 - 36 * Real.log 3) := by
    simp only [add_mul, hAl]; ring
  rw [e]
  have hc' : c * Real.log 2 ≤ 71.2 * Real.log 2 := mul_le_mul_of_nonneg_right hc hl2.le
  have hA : 0 ≤ 75.2 + 3 * κ * (4 - 2 * κ / 3) := by nlinarith
  have hB : 0 ≤ 36 + 12 * κ - κ ^ 2 / 4 := by nlinarith
  have hq : 0.6932 * (75.2 + 3 * κ * (4 - 2 * κ / 3)) + 54 ≤ 1.0986 * (36 + 12 * κ - κ ^ 2 / 4) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)]
  nlinarith [mul_le_mul_of_nonneg_left l2b.le hA, mul_le_mul_of_nonneg_left l3a.le hB]

/-- The archimedean bound converted to bits. -/
theorem bits_B3 {l n κ G F : ℝ} (hG : G / Real.log 2 ≤ F)
    (h : Real.log l ≤ (κ ^ 2 - 12 * κ) * n ^ 2 * Real.log n + n ^ 2 * G + 1 / 10 * n ^ 2) :
    Real.logb 2 l ≤ (κ ^ 2 - 12 * κ) * n ^ 2 * Real.logb 2 n + F * n ^ 2 + 3 / 20 * n ^ 2 := by
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h2 : 0 < Real.log 2 := by linarith
  have hG' : G ≤ F * Real.log 2 := by rwa [div_le_iff₀ h2] at hG
  have hN : 0 ≤ n ^ 2 := by positivity
  simp only [Real.logb]
  rw [div_le_iff₀ h2]
  have e : ((κ ^ 2 - 12 * κ) * n ^ 2 * (Real.log n / Real.log 2) + F * n ^ 2 + 3 / 20 * n ^ 2) *
      Real.log 2 = (κ ^ 2 - 12 * κ) * n ^ 2 * Real.log n + F * Real.log 2 * n ^ 2
        + 3 / 20 * n ^ 2 * Real.log 2 := by field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hG' hN]

/-- The decay bound (N, Theorem 3.1) converted to bits:
`log₂ ‖Δ_K(ζ)‖₃ ≤ −log₂ 3 · (12κ − κ²/4) n² + 100 n (1 + log₂ n)`. -/
theorem decay_bits {x : ℝ} (hx : 0 < x) {n K : ℕ} (hK2 : 2 ≤ K) (hK6 : K ≤ 6 * n)
    (h : x ≤ (3 : ℝ) ^ (-decayExp n K)) :
    Real.logb 2 x ≤ -(Real.logb 2 3 * (12 * ((K : ℝ) / n) - ((K : ℝ) / n) ^ 2 / 4) * (n : ℝ) ^ 2) +
      100 * (n : ℝ) * (1 + Real.logb 2 n) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hx h
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num)] at h1
  have hl23 : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left (decayExp_ge n K hK2) hl23.le
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hKn : (K : ℝ) ≤ 6 * n := by
    have : ((K : ℕ) : ℝ) ≤ ((6 * n : ℕ) : ℝ) := by exact_mod_cast hK6
    push_cast at this; linarith
  have hlogK : Real.logb 2 (2 * K - 1) ≤ 4 + Real.logb 2 n := by
    have h3 : Real.logb 2 (2 * K - 1) ≤ Real.logb 2 (16 * n) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    rw [Real.logb_mul (by norm_num) hnR.ne'] at h3
    have : Real.logb 2 16 = 4 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow]; simp
    linarith
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn1)
  have e1 : Real.logb 2 3 * (12 * (n : ℝ) * K - (K : ℝ) ^ 2 / 4 - 4 * K * Real.logb 3 (2 * K - 1)) =
      Real.logb 2 3 * (12 * ((K : ℝ) / n) - ((K : ℝ) / n) ^ 2 / 4) * (n : ℝ) ^ 2 -
        4 * K * Real.logb 2 (2 * K - 1) := by
    rw [← logb_two_three_mul (2 * K - 1)]; field_simp
  rw [e1] at h2
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have h4 : 4 * (K : ℝ) * Real.logb 2 (2 * K - 1) ≤ 100 * (n : ℝ) * (1 + Real.logb 2 n) := by
    have h5 := mul_le_mul_of_nonneg_left hlogK hK0
    have h6 : (K : ℝ) * Real.logb 2 n ≤ 6 * n * Real.logb 2 n :=
      mul_le_mul_of_nonneg_right hKn hlogn
    nlinarith
  linarith

/-- The final bit count of N, §7. -/
theorem assembly_arith3 {a b e f κ N2 L Fd g Q Er X : ℝ} (hN2 : 0 < N2)
    (hT2 : a ≤ κ * (12 - κ) * N2 * L + 71.2 * N2 + 1 / 10 * N2)
    (hB2 : b ≤ (κ ^ 2 - 12 * κ) * N2 * L + Fd * N2 + 3 / 20 * N2)
    (hBK : e ≤ X) (hA2 : f ≤ -(g * Q * N2) + Er)
    (hmargin : 71.2 + Fd + 4 ≤ g * Q) (hNL : Er + X < N2) :
    a + b + e + f < 0 := by
  have h1 := mul_le_mul_of_nonneg_right hmargin hN2.le
  have e1 : κ * (12 - κ) * N2 * L + (κ ^ 2 - 12 * κ) * N2 * L = 0 := by ring
  nlinarith

/-! ### The main theorem -/

/-- **`ζ₃(5)` is irrational**, from the inputs `Zeta35Inputs` (paper N, §7). -/
theorem zeta3_five_irrational (I : Zeta35Inputs) : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) := by
  intro r hr
  obtain ⟨NB, hNB⟩ := I.arch (1 / 10) (by norm_num)
  obtain ⟨NT, hNT⟩ := I.thm_5_1 mertens3Const tendsto_mertens3 (1 / 10) (by norm_num)
  obtain ⟨N0, hN0⟩ := aux_prime3 r.den r.den_pos
  have hB1 : (1 : ℝ) ≤ (denNumMax r : ℝ) := by
    have : (1 : ℤ) ≤ denNumMax r := le_max_of_le_right (by exact_mod_cast r.den_pos)
    exact_mod_cast this
  have hlB : 0 ≤ Real.logb 2 (denNumMax r) := Real.logb_nonneg (by norm_num) hB1
  obtain ⟨NL, hNL⟩ := eventually_lower_order3 100 (6 * Real.logb 2 (denNumMax r)) (by norm_num)
    (by positivity)
  set m : ℕ := NB + NT + N0 + NL + 1000 with hm_def
  set n : ℕ := 2 * m with hn_def
  have hn : Even n := ⟨m, by omega⟩
  have hn1000 : (1000 : ℝ) ≤ n := by
    have : 1000 ≤ n := by omega
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by linarith
  have hnNB : NB ≤ n := by omega
  have hnNT : NT ≤ n := by omega
  have hnN0 : N0 ≤ n := by omega
  have hnNL : NL ≤ n := by omega
  have hRn : R n = 3 * m := by rw [R, hn_def]; omega
  clear_value n m
  obtain ⟨ℓ, hℓ, hℓlo, hℓhi, hℓ11, hℓb⟩ := hN0 n hnN0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- the admissibility conditions, in `ℕ`
  have hlo : 3 * m + 1 ≤ ℓ := by
    have : ((3 * m : ℕ) : ℝ) < (ℓ : ℝ) := by push_cast; rw [hn_def] at hℓlo; push_cast at hℓlo; linarith
    exact_mod_cast this
  have hhi : 25 * ℓ ≤ 76 * m := by
    have : ((25 * ℓ : ℕ) : ℝ) ≤ ((76 * m : ℕ) : ℝ) := by
      push_cast; rw [hn_def] at hℓhi; push_cast at hℓhi; linarith
    exact_mod_cast this
  set K : ℕ := 4 * (3 * n + 1 - ℓ) with hK_def
  have hK6 : K ≤ 6 * n := by omega
  have hKlo : 59 * n ≤ 10 * K := by omega
  have hK2 : 2 ≤ K := by omega
  have hKK : K = 4 * (3 * n + 1 - ℓ) := hK_def
  clear_value K
  set κ : ℝ := (K : ℝ) / n with hκ_def
  have hKκ : (K : ℝ) = κ * n := by rw [hκ_def]; field_simp
  have hκ1 : (5.9 : ℝ) ≤ κ := by
    rw [hκ_def, le_div_iff₀ hnR]
    have : ((59 * n : ℕ) : ℝ) ≤ ((10 * K : ℕ) : ℝ) := by exact_mod_cast hKlo
    push_cast at this; linarith
  have hκ2 : κ ≤ 6 := by
    rw [hκ_def, div_le_iff₀ hnR]
    have : ((K : ℕ) : ℝ) ≤ ((6 * n : ℕ) : ℝ) := by exact_mod_cast hK6
    push_cast at this; linarith
  -- non-vanishing (N, Theorem 6.2)
  have hΔr : (hankelPoly n K).eval r ≠ 0 := by
    rw [hKK]
    exact I.nonvanishing n ℓ hn hℓ (by omega) (by omega) (by omega) r hℓb
  have hdeg := natDegree_hankelPoly_le n K
  have hLB := hNB n K hnNB hn hκ1 hκ2
  have hTsum := hNT n K hnNT hn hκ1 hκ2
  have hLT : ∀ q : ℕ, q.Prime → q ≠ 3 → negTop (gaussVal q (hankelPoly n K)) ≤ TP q n K :=
    fun q hq hq3 => tree_field_holds n K q hq hq3
  have hA0 := I.decay n K hn hK2 (by omega)
  rw [hr] at hA0
  have hdecay := decayExp_ge n K hK2
  generalize hankelPoly n K = Δ at hΔr hdeg hLB hLT hA0
  rw [← hκ_def] at hLB hTsum
  have hΔ0 : Δ ≠ 0 := fun h => hΔr (by rw [h, eval_zero])
  have hΔζ : aeval (r : ℚ_[3]) Δ = ((Δ.eval r : ℚ) : ℚ_[3]) := by
    rw [show (r : ℚ_[3]) = algebraMap ℚ ℚ_[3] r from rfl, aeval_algebraMap_apply,
      coe_aeval_eq_eval]
    rfl
  have hne : aeval (r : ℚ_[3]) Δ ≠ 0 := by rw [hΔζ]; exact_mod_cast hΔr
  -- the criterion (N, Lemma 2.3)
  obtain ⟨S, E, hSE, hcrit⟩ := pden_criterion 3 Δ hdeg r hne
  have hS : ∀ q ∈ S, q.Prime ∧ q ≠ 3 := fun q hq => ⟨(hSE q hq).1, (hSE q hq).2.1⟩
  have hTS := hTsum S hS
  have hEle : ∀ q ∈ S, (E q : ℝ) ≤ TPplus q n K := by
    intro q hq
    obtain ⟨hqp, hq3, hEq⟩ := hSE q hq
    obtain ⟨g, hg⟩ := gaussVal_eq_coe' hΔ0 q
    have hT := hLT q hqp hq3
    rw [hg] at hT
    have h1 := hEq g hg
    have h2 := max_neg_le_TPplus hT
    exact_mod_cast h1.trans h2
  -- (iii) the denominators, in bits
  have hdpos : 0 < ∏ q ∈ S, (q : ℝ) ^ E q :=
    Finset.prod_pos fun q hq => pow_pos (by exact_mod_cast (hS q hq).1.pos) _
  have hdlog : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) ≤
      ∑ q ∈ S, (TPplus q n K : ℝ) * Real.logb 2 q := by
    rw [Real.logb_prod S _
      (fun q hq => pow_ne_zero _ (by exact_mod_cast (hS q hq).1.ne_zero))]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Real.logb_pow]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hS q hq).1.one_lt.le
    exact mul_le_mul_of_nonneg_right (hEle q hq) (Real.logb_nonneg (by norm_num) hq1)
  have hc := I.table_c κ hκ1 hκ2
  have hT2 : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) ≤
      κ * (12 - κ) * (n : ℝ) ^ 2 * Real.logb 2 n + 71.2 * (n : ℝ) ^ 2 + 1 / 10 * (n : ℝ) ^ 2 := by
    have h2 : cConst mertens3Const I.cRest κ * (n : ℝ) ^ 2 ≤ 71.2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith [hdlog.trans hTS]
  -- (ii) the archimedean size, in bits
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  have hl1pos : 0 < l1 Δ := l1_pos' hΔ0
  have hl3 : Real.log 3 ≤ 1.5 := by have := log_three_bounds.2; linarith
  have hFd := Fdag_sigmaK_le (κ := κ) (by linarith) hκ2 hl3
  set Fd : ℝ := (54 - 36 * Real.log 3) / Real.log 2 + 3 * κ * (4 - 2 * κ / 3) with hFd_def
  have hB2 : Real.logb 2 (l1 Δ) ≤
      (κ ^ 2 - 12 * κ) * (n : ℝ) ^ 2 * Real.logb 2 n + Fd * (n : ℝ) ^ 2 +
        3 / 20 * (n : ℝ) ^ 2 := bits_B3 hFd hLB
  -- (i) the decay, in bits
  have hnormpos : 0 < ‖aeval (r : ℚ_[3]) Δ‖ := norm_pos_iff.mpr hne
  have hA2 : Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ ≤
      -(Real.logb 2 3 * (12 * κ - κ ^ 2 / 4) * (n : ℝ) ^ 2) +
        100 * (n : ℝ) * (1 + Real.logb 2 n) := decay_bits hnormpos hK2 hK6 hA0
  -- the height of `r`
  have hBK : Real.logb 2 ((denNumMax r : ℝ) ^ K) ≤ 6 * Real.logb 2 (denNumMax r) * n := by
    rw [Real.logb_pow]
    have : (K : ℝ) ≤ 6 * n := by
      have : ((K : ℕ) : ℝ) ≤ ((6 * n : ℕ) : ℝ) := by exact_mod_cast hK6
      push_cast at this; linarith
    calc (K : ℝ) * Real.logb 2 (denNumMax r) ≤ (6 * n) * Real.logb 2 (denNumMax r) :=
          mul_le_mul_of_nonneg_right this hlB
      _ = 6 * Real.logb 2 (denNumMax r) * n := by ring
  -- the margin
  have hmargin := budget (c := 71.2) hκ1 hκ2 le_rfl
  have hNLn := hNL n hnNL
  have hN2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsum : Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) + Real.logb 2 (l1 Δ) +
      Real.logb 2 ((denNumMax r : ℝ) ^ K) + Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ < 0 :=
    assembly_arith3 hN2 hT2 hB2 hBK hA2 (by linarith [hmargin]) (by linarith [hNLn])
  -- assemble: the product in the criterion is `< 1`
  have hBKpos : 0 < (denNumMax r : ℝ) ^ K := pow_pos (by linarith) _
  have hYpos : 0 < (∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K *
      ‖aeval (r : ℚ_[3]) Δ‖ := by positivity
  have hlogY : Real.logb 2 ((∏ q ∈ S, (q : ℝ) ^ E q) * l1 Δ * (denNumMax r : ℝ) ^ K *
      ‖aeval (r : ℚ_[3]) Δ‖) = Real.logb 2 (∏ q ∈ S, (q : ℝ) ^ E q) + Real.logb 2 (l1 Δ) +
      Real.logb 2 ((denNumMax r : ℝ) ^ K) + Real.logb 2 ‖aeval (r : ℚ_[3]) Δ‖ := by
    rw [Real.logb_mul (by positivity) hnormpos.ne', Real.logb_mul (by positivity)
      hBKpos.ne', Real.logb_mul hdpos.ne' hl1pos.ne']
  rw [← hlogY, Real.logb_neg_iff (by norm_num) hYpos] at hsum
  exact absurd hcrit (not_le.mpr hsum)

end Zeta35
