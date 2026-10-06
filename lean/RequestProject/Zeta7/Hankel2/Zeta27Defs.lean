import RequestProject.Zeta7.Hankel2.Family3Lemma21
import RequestProject.Zeta7.Hankel2.Bhargava
import RequestProject.Zeta7.Hankel2.Criterion

/-!
# Definitions for the analytic inputs of the ζ₂(7) proof (paper §§4, 6, 7, 8, 10)

This file only contains *definitions*: the objects in terms of which the still-missing
analytic inputs (the fields of `Hankel2.Zeta27Inputs`, see `Main2adic.lean`) are stated.

* §4 (Theorem A): `A3 n = 4(3n+1) + 1 + 6 v₂(n!)`, `Dth n K = 2K + 6n − 1`, integer-valued
  polynomials (`IntValued`).
* §3 (criterion): the `ℓ¹` norm `‖F‖₁` (`l1`) and the Gauss valuation `v_p(F) = min_j v_p(f_j)`
  (`gaussVal`, `⊤` for `F = 0`).
* §7 (Theorem 7.1, the tree bound "Lemma T"): the local matrices `C_k = [c_{k,a+b}]_{a,b≤3}` with `c_{k,m} = β_{k,m} + X α_{k,m}`
  (`Cmat`), the minors `det C_k[R, {0,…,s−1}]` (`minorR`), the **unclipped**
  `e_p(k,s,ℓ) = max_R −v(det C_k[R,{0..s−1}])` (`eP`, `−∞` if all minors vanish),
  `λ_p(k) = max_{m≠k} v_p(k−m)` (`lambdaP`), `f_p(k,s) = max_{0≤ℓ≤s(4−s)} [e_p(k,s,ℓ) + ℓ λ_p(k)]`,
  `f_p(k,0) = 0` (`fP`), the level penalty `∑_{j≥1} ∑_{c mod p^j} (S_c² − ∑_{k∈c} s_k²)`
  (`penalty`) and `T_p` (`TP`), with `max(T_p, 0)` (`TPplus`).
* §6 (Theorem 6.1, archimedean size "Lemma B"): the logarithmic potential `𝓛f(x) = ∫_{-1}^{2} ln|x−y| f(y) dy` (`logPot`),
  `F[σ]` (`Fenergy`), `P_σ` (`Pgrad`), feasibility (`Feasible`), `gap(σ)` (`gapF`) and
  piecewise-constant profiles (`PiecewiseConst`).
* Table 1 (§10): the five `κ`-intervals and the certified constants (`kappaLo`, `cTab`, `FdagTab`).
* §8.4: the Mertens-type prime sum (`mertensSum`); `θ` is Mathlib's `Chebyshev.theta`.
-/

open Polynomial Finset

namespace Hankel2

/-! ### Theorem A (§4) -/

/-- `A₃ = 4(3n+1) + 1 + 6 v₂(n!)`. -/
noncomputable def A3 (n : ℕ) : ℝ := 4 * (3 * n + 1) + 1 + 6 * (padicValNat 2 n.factorial : ℝ)

/-- `D = 2K + 6n − 1`. -/
def Dth (n K : ℕ) : ℕ := 2 * K + 6 * n - 1

/-- The entry bound of paper Lemma 4.3, `A₃ − 3 log₂ D − log₂(D+1)`. -/
noncomputable def entryBound (n K : ℕ) : ℝ :=
  A3 n - 3 * Real.logb 2 (Dth n K) - Real.logb 2 ((Dth n K : ℝ) + 1)

/-- An integer-valued polynomial: `B(z) ∈ ℤ` for all `z ∈ ℤ`. -/
def IntValued (B : ℚ[X]) : Prop := ∀ z : ℤ, ∃ m : ℤ, B.eval (z : ℚ) = m

/-! ### The criterion (§3) -/

/-- `‖F‖₁ = ∑_j |f_j|`. -/
noncomputable def l1 (F : ℚ[X]) : ℝ := ∑ i ∈ range (F.natDegree + 1), |((F.coeff i : ℚ) : ℝ)|

/-- The Gauss valuation `v_p(F) = min_j v_p(f_j)` (`⊤` for `F = 0`). -/
noncomputable def gaussVal (p : ℕ) (F : ℚ[X]) : WithTop ℤ :=
  F.support.inf fun i => ((padicValRat p (F.coeff i) : ℤ) : WithTop ℤ)

/-- `v ↦ −v` from `WithTop ℤ` to `WithBot ℤ` (`−(+∞) = −∞`). -/
def negTop : WithTop ℤ → WithBot ℤ
  | none => ⊥
  | some a => some (-a)

/-! ### Lemma T = Theorem 7.1 (§7) -/

namespace Fam3

/-- `c_{k,m} = β_{k,m} + X α_{k,m}` for `m ≤ 3`, and `c_{k,m} = 0` for `m > 3`. -/
noncomputable def cPoly (n : ℕ) (k : ℤ) (m : ℕ) : ℚ[X] :=
  if m ≤ 3 then C (betaC n k m) + C (alphaC n k m) * X else 0

/-- The local Hankel matrix `C_k = [c_{k,a+b}]_{a,b ≤ 3}`. -/
noncomputable def Cmat (n : ℕ) (k : ℤ) : Matrix (Fin 4) (Fin 4) ℚ[X] :=
  fun a b => cPoly n k ((a : ℕ) + b)

/-- The minor `det C_k[R, {0, …, |R|−1}]` (rows `R` in increasing order). -/
noncomputable def minorR (n : ℕ) (k : ℤ) (R : Finset (Fin 4)) : ℚ[X] :=
  (Matrix.of fun i j : Fin R.card =>
    Cmat n k (R.orderEmbOfFin rfl i) (Fin.castLE (by simpa using R.card_le_univ) j)).det

/-- `ℓ(R) = ∑ R − C(|R|, 2)`. -/
def ellR (R : Finset (Fin 4)) : ℕ := (∑ r ∈ R, (r : ℕ)) - R.card.choose 2

/-- The **unclipped** `e_p(k,s,ℓ) = max −v_p(det C_k[R,{0..s−1}])` over `|R| = s`, `ℓ(R) = ℓ`
(`−∞` if there is no such nonzero minor). -/
noncomputable def eP (p n : ℕ) (k : ℤ) (s ℓ : ℕ) : WithBot ℤ :=
  (univ.filter fun R : Finset (Fin 4) => R.card = s ∧ ellR R = ℓ).sup
    fun R => negTop (gaussVal p (minorR n k R))

/-- `λ_p(k) = max_{m ≠ k} v_p(k − m)` over the nodes `m ∈ [−n, 2n]`. -/
noncomputable def lambdaP (p n : ℕ) (k : ℤ) : ℕ :=
  ((Fam3PF.nodes n).erase k).sup fun m => padicValInt p (k - m)

/-- `f_p(k,s) = max_{0 ≤ ℓ ≤ s(4−s)} [e_p(k,s,ℓ) + ℓ λ_p(k)]`, `f_p(k,0) = 0`. -/
noncomputable def fP (p n : ℕ) (k : ℤ) (s : ℕ) : WithBot ℤ :=
  if s = 0 then 0 else
    (range (s * (4 - s) + 1)).sup fun ℓ => eP p n k s ℓ + (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ)

/-- The node `k = i − n` indexed by `i : Fin (3n+1)`. -/
def nodeOf (n : ℕ) (i : Fin (3 * n + 1)) : ℤ := (i : ℤ) - n

/-- The level penalty `∑_{j ≥ 1} ∑_{c mod p^j} (S_c² − ∑_{k ∈ c} s_k²)`, `S_c = ∑_{k ≡ c} s_k`.
Levels with `p^j > 3n` contribute `0` (every class contains at most one node), so the sum over
`1 ≤ j ≤ 3n+1` is the full sum. -/
def penalty (p n : ℕ) (s : Fin (3 * n + 1) → ℕ) : ℤ :=
  ∑ j ∈ Icc 1 (3 * n + 1), ∑ c ∈ range (p ^ j),
    (((∑ i ∈ univ.filter (fun i => nodeOf n i % ((p ^ j : ℕ) : ℤ) = c), s i : ℕ) : ℤ) ^ 2
      - ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((p ^ j : ℕ) : ℤ) = c), s i ^ 2 : ℕ) : ℤ))

/-- The profiles `0 ≤ s_k ≤ 4` with `∑ s_k = K`. -/
def profiles (n K : ℕ) : Finset (Fin (3 * n + 1) → ℕ) :=
  (Fintype.piFinset fun _ => range 5).filter fun s => ∑ i, s i = K

/-- `T_p = max_s [∑_k f_p(k, s_k) − penalty(s)]` (paper Theorem 7.1). -/
noncomputable def TP (p n K : ℕ) : WithBot ℤ :=
  (profiles n K).sup fun s =>
    (∑ i, fP p n (nodeOf n i) (s i)) + (((-penalty p n s : ℤ)) : WithBot ℤ)

/-- `max(T_p, 0)` as an integer. -/
noncomputable def TPplus (p n K : ℕ) : ℤ := WithBot.unbotD 0 (max (TP p n K) 0)

end Fam3

/-! ### Lemma B = Theorem 6.1 (§6) -/

/-- The logarithmic potential `𝓛f(x) = ∫_{-1}^{2} ln|x − y| f(y) dy`. -/
noncomputable def logPot (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (-1 : ℝ)..2, Real.log |x - y| * f y

/-- `⟨f, g⟩ = ∫_{-1}^{2} f g`. -/
noncomputable def pairing (f g : ℝ → ℝ) : ℝ := ∫ x in (-1 : ℝ)..2, f x * g x

/-- `𝟙_I`, `I = (0,1)`. -/
noncomputable def indI : ℝ → ℝ := Set.indicator (Set.Ioo 0 1) 1

/-- `𝟙_O`, `O = [−1,0] ∪ [1,2]`. -/
noncomputable def indO : ℝ → ℝ := Set.indicator (Set.Icc (-1) 0 ∪ Set.Icc 1 2) 1

/-- `F[σ] = ⟨σ, 2𝓛𝟙_I − 4𝓛𝟙_O⟩ + ⟨σ, 𝓛σ⟩`. -/
noncomputable def Fenergy (σ : ℝ → ℝ) : ℝ :=
  pairing σ (fun x => 2 * logPot indI x - 4 * logPot indO x) + pairing σ (logPot σ)

/-- `P_σ = 2𝓛𝟙_I − 4𝓛𝟙_O + 2𝓛σ`. -/
noncomputable def Pgrad (σ : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * logPot indI x - 4 * logPot indO x + 2 * logPot σ x

/-- `σ` is feasible for `κ`: measurable, `0 ≤ σ ≤ 4`, `∫_{-1}^{2} σ = κ`. -/
def Feasible (κ : ℝ) (σ : ℝ → ℝ) : Prop :=
  Measurable σ ∧ (∀ x, 0 ≤ σ x ∧ σ x ≤ 4) ∧ ∫ x in (-1 : ℝ)..2, σ x = κ

/-- `gap(σ) = sup_{σ' feasible} ⟨P_σ, σ' − σ⟩`. -/
noncomputable def gapF (κ : ℝ) (σ : ℝ → ℝ) : ℝ :=
  sSup {g | ∃ σ', Feasible κ σ' ∧ g = pairing (Pgrad σ) (fun x => σ' x - σ x)}

/-- `σ` is piecewise constant on `[−1, 2]` with at most `m` pieces. -/
def PiecewiseConst (m : ℕ) (σ : ℝ → ℝ) : Prop :=
  ∃ (a : Fin (m + 1) → ℝ) (v : Fin m → ℝ), a 0 = -1 ∧ a (Fin.last m) = 2 ∧ Monotone a ∧
    ∀ i : Fin m, ∀ x ∈ Set.Ioo (a i.castSucc) (a i.succ), σ x = v i

/-! ### Table 1 (§10) -/

/-- The left endpoints `2.80, 2.84, 2.88, 2.92, 2.96` of the five `κ`-intervals. -/
noncomputable def kappaLo (j : Fin 5) : ℝ := 2.8 + 0.04 * (j : ℝ)

/-- The certified upper bounds for `c(κ)` (bits per `n²`), paper Table 1 / Appendix B
(`c ≤ 47.92972, 48.47596, 49.05433, 49.62853, 50.20161`, rounded upward). -/
noncomputable def cTab : Fin 5 → ℝ := ![47.9298, 48.4760, 49.0544, 49.6286, 50.2017]

/-- The certified upper bounds for `F†(κ) = (F[σ_κ] + gap(σ_κ))/ln 2` (bits per `n²`), paper
Table 1 / Appendix A, Proposition A.2 (rounded upward). -/
noncomputable def FdagTab : Fin 5 → ℝ := ![8.4252, 8.4584, 8.5109, 8.5768, 8.6479]

/-! ### Prime sums (§8.4) -/

/-- `∑_{3 ≤ p ≤ x} ln p / (p − 1)`. -/
noncomputable def mertensSum (x : ℝ) : ℝ :=
  ∑ p ∈ Icc 3 ⌊x⌋₊ with p.Prime, Real.log p / ((p : ℝ) - 1)

end Hankel2
