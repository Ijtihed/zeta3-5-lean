import Mathlib
import RequestProject.Zeta7.Hankel2.W4Family3
import RequestProject.Zeta7.Hankel2.WeightCert

/-!
# Theorem NV for family 3 (the node functional): `Δ_K(r) ≠ 0` for `p ∤ den r`

`ZETA7_STATUS.md`, round (e) §1–§2.  The node functional of family 3 (round (e) §1) is

  `L_X(F) = Σ_{k=-n}^{2n} Σ_{i=1}^{4} w_i(k) r_{k,i}(F)`,   `w_i(k) = α_i X + β_i(k)`,

with `r_{k,i}(F) = [u^{-i}] (F W)(-k + u)` (`resCoef`), `α_i = i(i+1)(i+2)(i+3) 2^{i+4} [i odd]`
(`alphaW`), `β_i(k) = -i(i+1)(i+2)(i+3) HS(k, i+4)` (`betaW`), and the harmonic sums
`HS(k, M) = Σ_{l=1}^{k} (2/(2l-1))^M` for `k > 0`, `HS(k, M) = -Σ_{l=k+1}^{0} (2/(2l-1))^M` for `k ≤ 0`
(`hsSum`).  At a prime `p` the harmonic sums split into the terms with `p ∣ 2l - 1` and the rest.

**Theorem NV** (`nv_family3`, fully in Lean): for odd `n`, a prime `p` with `7n + 2 ≤ 4p`, `p + 1 ≤ 2n`,
`K = 10n + 3 - 4p`, and every rational `r` with `p ∤ den r`, the Hankel determinant
`det [L_r(t^{a+b})]_{a,b < K}` is nonzero.

The proof assembles W1 (dual Hermite basis), W2 + W3 (`w3_family3`, the harmonic-sum Gram matrix
has unit weighted determinant), W4 (`w4_family3`, the other two Gram matrices are weighted-small), the
weight certificate (`det_ne_zero_of_weight_certificate`) and the change of basis from monomials to `E`.

What is **not** in Lean: the identification of this node functional with the 2-adic (Volkenborn)
integral `L(P) = ∫_{ℤ_2} (P W)'''(t + 1/2) dt = a(P) ζ₂(7) + b(P)` of the request (round (e) §1), and
the analytic inputs (decay, archimedean bound, Lemma T).
-/

open Polynomial

namespace Hankel2.W3.Fam3

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `i(i+1)(i+2)(i+3)`. -/
def cI (i : ℕ) : ℚ := (i : ℚ) * (i + 1) * (i + 2) * (i + 3)

/-- `α_i = i(i+1)(i+2)(i+3) 2^{i+4}` for odd `i`, `0` for even `i`. -/
def alphaW (i : ℕ) : ℚ := if i % 2 = 1 then cI i * 2 ^ (i + 4) else 0

/-- The harmonic sum `HS(k, M)`, restricted to the indices `l` satisfying `P`. -/
noncomputable def hsSum (k : ℤ) (M : ℕ) (P : ℤ → Prop) [DecidablePred P] : ℚ :=
  if 0 < k then ∑ l ∈ (Finset.Icc 1 k).filter P, (2 / (2 * (l : ℚ) - 1)) ^ M
  else -∑ l ∈ (Finset.Icc (k + 1) 0).filter P, (2 / (2 * (l : ℚ) - 1)) ^ M

/-- `β_i(k) = -i(i+1)(i+2)(i+3) HS(k, i+4)`. -/
noncomputable def betaW (k : ℤ) (i : ℕ) : ℚ := -cI i * hsSum k (i + 4) (fun _ => True)

/-- The harmonic-sum part of `β_i(k)` at `p` (terms with `p ∣ 2l - 1`). -/
noncomputable def betaHS (p : ℕ) (k : ℤ) (i : ℕ) : ℚ :=
  -cI i * hsSum k (i + 4) (fun l => (p : ℤ) ∣ 2 * l - 1)

/-- The rest of `β_i(k)` at `p` (terms with `p ∤ 2l - 1`). -/
noncomputable def betaRest (p : ℕ) (k : ℤ) (i : ℕ) : ℚ :=
  -cI i * hsSum k (i + 4) (fun l => ¬ (p : ℤ) ∣ 2 * l - 1)

/-- The node functional `L_r(F) = Σ_{k=-n}^{2n} Σ_{i=1}^{4} (r α_i + β_i(k)) r_{k,i}(F)`. -/
noncomputable def nodeFunctional (n : ℕ) (r : ℚ) (F : ℚ[X]) : ℚ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) (2 * n), ∑ i ∈ Finset.Icc 1 4,
    (r * alphaW i + betaW k i) * resCoef n F k i

/-- The `K × K` Hankel matrix of moments `L_r(t^{a+b})`. -/
noncomputable def hankelNode (n K : ℕ) (r : ℚ) : Matrix (Fin K) (Fin K) ℚ :=
  fun a b => nodeFunctional n r (X ^ ((a : ℕ) + b))

omit hp in
theorem betaW_eq (k : ℤ) (i : ℕ) : betaW k i = betaHS p k i + betaRest p k i := by
  have key : ∀ (s : Finset ℤ) (M : ℕ),
      ∑ l ∈ s.filter (fun _ => True), (2 / (2 * (l : ℚ) - 1)) ^ M =
        ∑ l ∈ s.filter (fun l => (p : ℤ) ∣ 2 * l - 1), (2 / (2 * (l : ℚ) - 1)) ^ M +
        ∑ l ∈ s.filter (fun l => ¬ (p : ℤ) ∣ 2 * l - 1), (2 / (2 * (l : ℚ) - 1)) ^ M := by
    intro s M
    rw [Finset.filter_true, Finset.sum_filter_add_sum_filter_not]
  simp only [betaW, betaHS, betaRest, hsSum]
  split_ifs
  · rw [key]; ring
  · rw [key]; ring

theorem padicNorm_cI_le (i : ℕ) : padicNorm p (cI i) ≤ 1 := by
  have : cI i = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by simp [cI]
  rw [this]; exact padicNorm.of_nat _

theorem padicNorm_hsTerm_le {l : ℤ} (hl : ¬ (p : ℤ) ∣ 2 * l - 1) (M : ℕ) :
    padicNorm p ((2 / (2 * (l : ℚ) - 1)) ^ M) ≤ 1 := by
  rw [W2.padicNorm_pow' (p := p)]
  refine pow_le_one₀ (padicNorm.nonneg _) ?_
  have e : (2 * (l : ℚ) - 1) = ((2 * l - 1 : ℤ) : ℚ) := by push_cast; ring
  rw [e, padicNorm.div, W2.padicNorm_int_eq_one hl, div_one]
  exact_mod_cast padicNorm.of_nat (p := p) 2

theorem padicNorm_betaRest_le (k : ℤ) (i : ℕ) : padicNorm p (betaRest p k i) ≤ 1 := by
  rw [betaRest, padicNorm.mul, padicNorm.neg]
  refine mul_le_one₀ (padicNorm_cI_le i) (padicNorm.nonneg _) ?_
  simp only [hsSum]
  split_ifs
  · exact padicNorm.sum_le' (fun l hl => padicNorm_hsTerm_le (Finset.mem_filter.1 hl).2 _)
      zero_le_one
  · rw [padicNorm.neg]
    exact padicNorm.sum_le' (fun l hl => padicNorm_hsTerm_le (Finset.mem_filter.1 hl).2 _)
      zero_le_one

theorem padicNorm_alphaW_le (i : ℕ) : padicNorm p (alphaW i) ≤ 1 := by
  rw [alphaW]
  split_ifs
  · rw [padicNorm.mul]
    refine mul_le_one₀ (padicNorm_cI_le i) (padicNorm.nonneg _) ?_
    exact_mod_cast padicNorm.of_nat (p := p) (2 ^ (i + 4))
  · simp

omit hp in
/-- The Gram matrix of `L_r` in any basis splits as `G_HS + G_rest + r G_α`. -/
theorem gram_nodeFunctional {ι : Type*} (E : ι → ℚ[X]) (r : ℚ) :
    (fun x y => nodeFunctional n r (E x * E y)) =
      nodeGram n (betaHS p) E + nodeGram n (betaRest p) E + r • nodeGram n (fun _ i => alphaW i) E := by
  ext x y
  simp only [nodeFunctional, nodeGram, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [betaW_eq (p := p)]; ring


omit hp in
/-- The algebra behind `hsConst`: exchanging the order of summation in `Σ_i β_i r_{k,i}`. -/
theorem sum_beta_resCoef_eq (q : ℚ) (Fj : ℕ → ℚ) (H : PowerSeries ℚ) :
    ∑ i ∈ Finset.Icc 1 4, (-cI i * (2 / q) ^ (i + 4)) *
      ∑ j ∈ Finset.range (5 - i), Fj j * PowerSeries.coeff (4 - i - j) H =
    ∑ j ∈ Finset.range 4, W2.hsConst q H j * Fj j := by
  have hI : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [hI]
  simp [W2.hsConst, Finset.sum_range_succ, cI]
  ring

/-- The `p`-part of the harmonic sums at the nodes. -/
theorem hsSum_dvd (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) {k : ℤ}
    (hk : k ∈ Finset.Icc (-(n : ℤ)) (2 * n)) (M : ℕ) :
    hsSum k M (fun l => (p : ℤ) ∣ 2 * l - 1) =
      if k ∈ hsNodes n p then (if 0 < k then (2 / (p : ℚ)) ^ M else -(2 / (-(p : ℚ))) ^ M)
      else 0 := by
  have h13 := W2.p_ge_13 hn hlow hup
  have hodd := W2.p_odd (p := p) h13
  have hP : (0 : ℤ) < p := by omega
  simp only [Finset.mem_Icc] at hk
  -- the only odd multiples of `p` in `[-(2n-1), 4n-1]` are `±p`
  have hmult : ∀ l : ℤ, -n ≤ l → l ≤ 2 * n → (p : ℤ) ∣ 2 * l - 1 →
      l = ((p : ℤ) + 1) / 2 ∨ l = 1 - ((p : ℤ) + 1) / 2 := by
    intro l hl1 hl2 hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hm1 : -2 < m := by nlinarith
    have hm2 : m < 3 := by nlinarith
    interval_cases m <;> omega
  have hh : (2 * (((((p : ℤ) + 1) / 2 : ℤ)) : ℚ) - 1) = (p : ℚ) := by
    have : 2 * (((p : ℤ) + 1) / 2) - 1 = (p : ℤ) := by omega
    exact_mod_cast this
  have hh' : (2 * (((1 - ((p : ℤ) + 1) / 2 : ℤ)) : ℚ) - 1) = -(p : ℚ) := by
    have : 2 * (1 - ((p : ℤ) + 1) / 2) - 1 = -(p : ℤ) := by omega
    exact_mod_cast this
  have hdvd1 : (p : ℤ) ∣ 2 * (((p : ℤ) + 1) / 2) - 1 := ⟨1, by omega⟩
  have hdvd2 : (p : ℤ) ∣ 2 * (1 - ((p : ℤ) + 1) / 2) - 1 := ⟨-1, by omega⟩
  simp only [hsSum, hsNodes, Finset.mem_union, Finset.mem_Icc]
  by_cases hpos : 0 < k
  · rw [if_pos hpos]
    by_cases hin : ((p : ℤ) + 1) / 2 ≤ k
    · have hf : (Finset.Icc 1 k).filter (fun l => (p : ℤ) ∣ 2 * l - 1) = {((p : ℤ) + 1) / 2} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases hmult l (by omega) (by omega) h3 with h | h
          · exact h
          · omega
        · rintro rfl; exact ⟨⟨by omega, hin⟩, hdvd1⟩
      rw [hf, Finset.sum_singleton, hh, if_pos (Or.inl ⟨hin, hk.2⟩), if_pos hpos]
    · have hf : (Finset.Icc 1 k).filter (fun l => (p : ℤ) ∣ 2 * l - 1) = ∅ := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
        intro h1 h3
        rcases hmult l (by omega) (by omega) h3 with h | h <;> omega
      rw [hf, Finset.sum_empty, if_neg (by omega)]
  · rw [if_neg hpos]
    by_cases hin : k ≤ -(((p : ℤ) + 1) / 2)
    · have hf : (Finset.Icc (k + 1) 0).filter (fun l => (p : ℤ) ∣ 2 * l - 1) =
          {1 - ((p : ℤ) + 1) / 2} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases hmult l (by omega) (by omega) h3 with h | h
          · omega
          · exact h
        · rintro rfl; exact ⟨⟨by omega, by omega⟩, hdvd2⟩
      rw [hf, Finset.sum_singleton, hh', if_pos (Or.inr ⟨hk.1, hin⟩), if_neg hpos]
    · have hf : (Finset.Icc (k + 1) 0).filter (fun l => (p : ℤ) ∣ 2 * l - 1) = ∅ := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
        intro h1 h3
        rcases hmult l (by omega) (by omega) h3 with h | h <;> omega
      rw [hf, Finset.sum_empty, neg_zero, if_neg (by omega)]

/-- The harmonic-sum part of the node functional is the functional `L_HS` of W3 with the constants
`hsC` of W2. -/
theorem nodeGram_betaHS (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n)
    {ι : Type*} (E : ι → ℚ[X]) :
    nodeGram n (betaHS p) E = fun x y =>
      functionalHS (fun k : hsNodes n p => hsC n p k) (fun k => (-(k : ℤ) : ℚ)) (E x * E y) := by
  ext x y
  set F := E x * E y
  simp only [nodeGram, functionalHS]
  have hsub : hsNodes n p ⊆ Finset.Icc (-(n : ℤ)) (2 * n) := by
    intro k hk
    simp only [hsNodes, Finset.mem_union, Finset.mem_Icc] at hk ⊢
    omega
  rw [← Finset.sum_subset hsub, ← Finset.sum_coe_sort (hsNodes n p)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hkI := hsub k.2
    have hb : ∀ i, betaHS p k i = -cI i * (if 0 < (k : ℤ) then (2 / (p : ℚ)) ^ (i + 4)
        else -(2 / (-(p : ℚ))) ^ (i + 4)) := by
      intro i
      rw [betaHS, hsSum_dvd hn hlow hup hkI, if_pos k.2]
    simp only [hb, resCoef, hsC]
    split_ifs with hpos
    · exact sum_beta_resCoef_eq (p : ℚ) (fun j => (hasseDeriv j F).eval (-((k : ℤ) : ℚ))) _
    · have := sum_beta_resCoef_eq (-(p : ℚ)) (fun j => (hasseDeriv j F).eval (-((k : ℤ) : ℚ)))
        (W2.fam3H n k)
      simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg, F] at this ⊢
      rw [← this, neg_neg]
  · intro k hk hkn
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [betaHS, hsSum_dvd hn hlow hup hk, if_neg hkn]
    ring

/-- **Theorem NV, Gram form.**  In the dual Hermite basis `E`, the Gram matrix of `L_r` is nonsingular
for every rational `r` with `p ∤ den r`. -/
theorem nv_gram (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) :
    ∃ E : Cond (fun k : hsNodes n p => nodeType n p k) → ℚ[X],
      (∀ x d, Fintype.card (Cond (fun k : hsNodes n p => nodeType n p k)) ≤ d → (E x).coeff d = 0) ∧
      ∀ r : ℚ, ¬ p ∣ r.den → (Matrix.det fun x y => nodeFunctional n r (E x * E y)) ≠ 0 := by
  obtain ⟨E, hδ, hcoef, hdeg, hG⟩ := w3_family3 hn hlow hup
  dsimp only at hG
  obtain ⟨hGle, hdet⟩ := hG
  refine ⟨E, hdeg, fun r hr => ?_⟩
  rw [gram_nodeFunctional (p := p) E r]
  refine det_ne_zero_of_weight_certificate (p := p) _ _ _ (rowExp _) (colExp _) ?_ ?_ ?_ ?_ hr
  · rw [nodeGram_betaHS hn hlow hup E]; exact hGle
  · rw [nodeGram_betaHS hn hlow hup E]; exact hdet
  · exact fun x y => w4_family3 hn hlow hup E hδ hcoef _ (padicNorm_betaRest_le) x y
  · exact fun x y => w4_family3 hn hlow hup E hδ hcoef _ (fun _ i => padicNorm_alphaW_le i) x y

omit hp in
theorem nodeFunctional_add (r : ℚ) (F G : ℚ[X]) :
    nodeFunctional n r (F + G) = nodeFunctional n r F + nodeFunctional n r G := by
  simp only [nodeFunctional, resCoef, map_add, eval_add, add_mul, mul_add, Finset.sum_add_distrib]

omit hp in
theorem nodeFunctional_smul (r a : ℚ) (F : ℚ[X]) :
    nodeFunctional n r (a • F) = a * nodeFunctional n r F := by
  simp only [nodeFunctional, resCoef, map_smul, eval_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

omit hp in
theorem nodeFunctional_sum {α : Type*} (r : ℚ) (s : Finset α) (F : α → ℚ[X]) :
    nodeFunctional n r (∑ a ∈ s, F a) = ∑ a ∈ s, nodeFunctional n r (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nodeFunctional, resCoef]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, nodeFunctional_add, ih]

omit hp in
theorem poly_eq_sum_fin {K : ℕ} (P : ℚ[X]) (hP : ∀ d, K ≤ d → P.coeff d = 0) :
    P = ∑ d : Fin K, Polynomial.C (P.coeff d) * X ^ (d : ℕ) := by
  ext m
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < K
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega)]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [if_neg]; intro h; have := b.2; omega

/-- **Theorem NV (family 3, node functional).**  For odd `n`, a prime `p` with `7n + 2 ≤ 4p` and
`p + 1 ≤ 2n`, `K = 10n + 3 - 4p`, and every rational `r` whose denominator is prime to `p`, the Hankel
determinant `Δ_K(r) = det [L_r(t^{a+b})]_{a,b<K}` of the node functional is nonzero. -/
theorem nv_family3 (hn : n % 2 = 1) (hlow : 7 * n + 2 ≤ 4 * p) (hup : p + 1 ≤ 2 * n) (r : ℚ)
    (hr : ¬ p ∣ r.den) : (hankelNode n (10 * n + 3 - 4 * p) r).det ≠ 0 := by
  have hodd := W2.p_odd (p := p) (W2.p_ge_13 hn hlow hup)
  obtain ⟨E, hdeg, hne⟩ := nv_gram hn hlow hup
  set K := 10 * n + 3 - 4 * p with hK
  have hcard : Fintype.card (Cond (fun k : hsNodes n p => nodeType n p k)) = K := by
    have := card_cond hn hodd hlow hup
    omega
  set e := Fintype.equivFinOfCardEq hcard
  set Cm : Matrix (Fin K) (Fin K) ℚ := fun d c => (E (e.symm c)).coeff d
  have hdegK : ∀ x d, K ≤ d → (E x).coeff d = 0 := fun x d hd => hdeg x d (by omega)
  have hsum : ∀ c, E (e.symm c) = ∑ d : Fin K, Polynomial.C (Cm d c) * X ^ (d : ℕ) :=
    fun c => poly_eq_sum_fin _ (hdegK _)
  have hmul : Cm.transpose * hankelNode n K r * Cm =
      (Matrix.of fun x y => nodeFunctional n r (E x * E y)).submatrix e.symm e.symm := by
    ext c c'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      hankelNode]
    rw [hsum c, hsum c', Finset.sum_mul_sum]
    have e2 : ∀ (a b : ℚ) (i j : ℕ),
        Polynomial.C a * X ^ i * (Polynomial.C b * X ^ j) = (a * b) • X ^ (i + j) := by
      intro a b i j; rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul, pow_add]; ring
    simp only [e2, nodeFunctional_sum, nodeFunctional_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  intro h0
  apply hne r hr
  have h1 := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul,
    Matrix.det_submatrix_equiv_self] at h1
  exact h1.symm

/-- **Theorem NV for all large `n`.**  If every large odd `n` admits a prime `p` with `7n + 2 ≤ 4p`
and `p + 1 ≤ 2n` (true for all large `n` by the prime number theorem; not proved here), then for every
rational `r` and every odd `n ≥ max N₀ (den r)` there is such a prime with
`Δ_{10n+3-4p}(r) ≠ 0` (because `p > n ≥ den r`, so `p ∤ den r`). -/
theorem nv_family3_eventually (r : ℚ) (N₀ : ℕ)
    (hprime : ∀ n, N₀ ≤ n → n % 2 = 1 → ∃ p, p.Prime ∧ 7 * n + 2 ≤ 4 * p ∧ p + 1 ≤ 2 * n) :
    ∀ n, max N₀ r.den ≤ n → n % 2 = 1 → ∃ p, p.Prime ∧ 7 * n + 2 ≤ 4 * p ∧ p + 1 ≤ 2 * n ∧
      (hankelNode n (10 * n + 3 - 4 * p) r).det ≠ 0 := by
  intro n hn hodd
  obtain ⟨p, hpp, hlow, hup⟩ := hprime n (le_trans (le_max_left _ _) hn) hodd
  haveI : Fact p.Prime := ⟨hpp⟩
  refine ⟨p, hpp, hlow, hup, nv_family3 hodd hlow hup r ?_⟩
  intro hd
  have h1 := Nat.le_of_dvd r.den_pos hd
  have h2 : r.den ≤ n := le_trans (le_max_right _ _) hn
  omega

end Hankel2.W3.Fam3
