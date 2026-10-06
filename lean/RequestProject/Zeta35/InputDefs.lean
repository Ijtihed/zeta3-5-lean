import RequestProject.Zeta35.Purity
import RequestProject.Zeta7.Hankel2.Zeta27Defs

/-!
# Definitions for the analytic inputs of the `ζ₃(5)` proof (paper N, §§3–5)

Only *definitions*: the objects in terms of which the still-open inputs (the fields of
`Zeta35.Zeta35Inputs`, `Main.lean`) are stated.

* §3 (decay, N Theorem 3.1): `v₃(i!_S) = −i + ∑_{j ≥ 0} ⌊i/(2·3^j)⌋` (`vS`), and the decay
  exponent `2 ∑_{i<K} v₃(i!_S) + K(4(3n+1) − log₃ D − log₃(D+1))`, `D = 2K − 2` (`decayExp`).
* §4 (archimedean size, N Theorem 4.1): the logarithmic potential on `[−3/2, 3/2]`
  (`logPot3`), `U = −4 𝓛1` (`Upot3`), `F[σ] = ⟨σ, U⟩ + ⟨σ, 𝓛σ⟩` (`Fenergy3`),
  `P_σ = U + 2𝓛σ` (`Pgrad3`), feasibility `0 ≤ σ ≤ 4`, `∫σ = κ` (`Feasible3`), `gap(σ)` (`gap3`),
  and the profile `σ_κ ≡ κ/3` (`sigmaK`).
* §5 (denominators, N Theorem 5.1; P, Thm 7.1; W, Thm 3.2): the tree bound `T_ℓ` for the local
  matrices `C_k = [c_{k,a+b}]_{a,b ≤ 3}`, `c_{k,m} = β_{k,m} + X α_{k,m}` (`Cmat`, `eP`, `lambdaP`,
  `fP`, `penalty`, `TP`, `TPplus`), exactly as in `Hankel2.Fam3` but for the nodes `|k| ≤ R`;
  the Mertens sum with `ℓ = 3` removed (`mertens3Sum`), and the constant
  `c(κ) = [κ(12−κ)(M₀ − ln 20) + rest(κ)]/ln 2` (`cConst`).
-/

open Polynomial Finset

namespace Zeta35

open Hankel2

/-! ### §3: decay -/

/-- `v₃(i!_S) = −i + ∑_{j ≥ 0} ⌊i/(2·3^j)⌋` for `S = 3⁻¹ℤ₃^×` (the terms with `j > i` vanish). -/
def vS (i : ℕ) : ℤ := -(i : ℤ) + ∑ j ∈ range (i + 1), ((i / (2 * 3 ^ j) : ℕ) : ℤ)

/-- The exponent of N, Theorem 3.1:
`2 ∑_{i<K} v₃(i!_S) + K (4(3n+1) − log₃ D − log₃(D+1))`, `D = 2K − 2`. -/
noncomputable def decayExp (n K : ℕ) : ℝ :=
  2 * ∑ i ∈ range K, (vS i : ℝ) +
    K * (4 * (3 * n + 1) - Real.logb 3 ((2 * K - 2 : ℕ) : ℝ) - Real.logb 3 ((2 * K - 2 : ℕ) + 1 : ℝ))

/-! ### §4: archimedean size -/

/-- `𝓛f(x) = ∫_{−3/2}^{3/2} ln|x − y| f(y) dy`. -/
noncomputable def logPot3 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-3 / 2 : ℝ)..(3 / 2), Real.log |x - y| * f y

/-- `⟨f, g⟩ = ∫_{−3/2}^{3/2} f g`. -/
noncomputable def pairing3 (f g : ℝ → ℝ) : ℝ := ∫ x in (-3 / 2 : ℝ)..(3 / 2), f x * g x

/-- The potential `U = −4 𝓛 1_{[−3/2,3/2]}` of the weight (no zeros). -/
noncomputable def Upot3 (x : ℝ) : ℝ := -4 * logPot3 (fun _ => 1) x

/-- `F[σ] = ⟨σ, U⟩ + ⟨σ, 𝓛σ⟩`. -/
noncomputable def Fenergy3 (σ : ℝ → ℝ) : ℝ := pairing3 σ Upot3 + pairing3 σ (logPot3 σ)

/-- `P_σ = U + 2 𝓛σ`. -/
noncomputable def Pgrad3 (σ : ℝ → ℝ) (x : ℝ) : ℝ := Upot3 x + 2 * logPot3 σ x

/-- `σ` is feasible for `κ`: measurable, `0 ≤ σ ≤ 4`, `∫_{−3/2}^{3/2} σ = κ`. -/
def Feasible3 (κ : ℝ) (σ : ℝ → ℝ) : Prop :=
  Measurable σ ∧ (∀ x, 0 ≤ σ x ∧ σ x ≤ 4) ∧ ∫ x in (-3 / 2 : ℝ)..(3 / 2), σ x = κ

/-- `gap(σ) = sup_{σ' feasible} ⟨P_σ, σ' − σ⟩`. -/
noncomputable def gap3 (κ : ℝ) (σ : ℝ → ℝ) : ℝ :=
  sSup {g | ∃ σ', Feasible3 κ σ' ∧ g = pairing3 (Pgrad3 σ) (fun x => σ' x - σ x)}

/-- The profile `σ_κ ≡ κ/3`. -/
noncomputable def sigmaK (κ : ℝ) : ℝ → ℝ := fun _ => κ / 3

/-! ### §5: the tree bound -/

/-- `c_{k,m} = β_{k,m} + X α_{k,m}` for `m ≤ 3`, and `0` for `m > 3`. -/
noncomputable def cPoly (n : ℕ) (k : ℤ) (m : ℕ) : ℚ[X] :=
  if m ≤ 3 then C (betaC n k m) + C (alphaC n k m) * X else 0

/-- The local Hankel matrix `C_k = [c_{k,a+b}]_{a,b ≤ 3}`. -/
noncomputable def Cmat (n : ℕ) (k : ℤ) : Matrix (Fin 4) (Fin 4) ℚ[X] :=
  fun a b => cPoly n k ((a : ℕ) + b)

/-- The minor `det C_k[R, {0, …, |R|−1}]`. -/
noncomputable def minorR (n : ℕ) (k : ℤ) (Rs : Finset (Fin 4)) : ℚ[X] :=
  (Matrix.of fun i j : Fin Rs.card =>
    Cmat n k (Rs.orderEmbOfFin rfl i) (Fin.castLE (by simpa using Rs.card_le_univ) j)).det

/-- The unclipped `e_ℓ(k,s,j) = max −v_ℓ(det C_k[R,{0..s−1}])` over `|R| = s`, `ℓ(R) = j`. -/
noncomputable def eP (ℓ n : ℕ) (k : ℤ) (s j : ℕ) : WithBot ℤ :=
  (univ.filter fun Rs : Finset (Fin 4) => Rs.card = s ∧ Fam3.ellR Rs = j).sup
    fun Rs => negTop (gaussVal ℓ (minorR n k Rs))

/-- `λ_ℓ(k) = max_{m ≠ k} v_ℓ(k − m)` over the nodes `|m| ≤ R`. -/
noncomputable def lambdaP (ℓ n : ℕ) (k : ℤ) : ℕ :=
  ((nodes n).erase k).sup fun m => padicValInt ℓ (k - m)

/-- `f_ℓ(k,s) = max_{0 ≤ j ≤ s(4−s)} [e_ℓ(k,s,j) + j λ_ℓ(k)]`, `f_ℓ(k,0) = 0`. -/
noncomputable def fP (ℓ n : ℕ) (k : ℤ) (s : ℕ) : WithBot ℤ :=
  if s = 0 then 0 else
    (range (s * (4 - s) + 1)).sup fun j => eP ℓ n k s j + (((j * lambdaP ℓ n k : ℕ) : ℤ) : WithBot ℤ)

/-- The node `k = i − R` indexed by `i : Fin (2R+1)`. -/
def nodeOf (n : ℕ) (i : Fin (2 * R n + 1)) : ℤ := (i : ℤ) - R n

/-- The level penalty `∑_{j ≥ 1} ∑_{c mod ℓ^j} (S_c² − ∑_{k ∈ c} s_k²)`. -/
def penalty (ℓ n : ℕ) (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ j ∈ Icc 1 (2 * R n + 1), ∑ c ∈ range (ℓ ^ j),
    (((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i : ℕ) : ℤ) ^ 2
      - ((∑ i ∈ univ.filter (fun i => nodeOf n i % ((ℓ ^ j : ℕ) : ℤ) = c), s i ^ 2 : ℕ) : ℤ))

/-- The profiles `0 ≤ s_k ≤ 4` with `∑ s_k = K`. -/
def profiles (n K : ℕ) : Finset (Fin (2 * R n + 1) → ℕ) :=
  (Fintype.piFinset fun _ => range 5).filter fun s => ∑ i, s i = K

/-- **The tree bound** `T_ℓ = max_s [∑_k f_ℓ(k, s_k) − penalty(s)]` (P, Thm 7.1; W, Thm 3.2). -/
noncomputable def TP (ℓ n K : ℕ) : WithBot ℤ :=
  (profiles n K).sup fun s =>
    (∑ i, fP ℓ n (nodeOf n i) (s i)) + (((-penalty ℓ n s : ℤ)) : WithBot ℤ)

/-- `max(T_ℓ, 0)` as an integer. -/
noncomputable def TPplus (ℓ n K : ℕ) : ℤ := WithBot.unbotD 0 (max (TP ℓ n K) 0)

/-- `∑_{ℓ ≤ Y, ℓ prime, ℓ ≠ 3} ln ℓ / (ℓ − 1)` (Mertens' sum with `ℓ = 3` removed). -/
noncomputable def mertens3Sum (Y : ℝ) : ℝ :=
  ∑ ℓ ∈ Icc 2 ⌊Y⌋₊ with (ℓ.Prime ∧ ℓ ≠ 3), Real.log ℓ / ((ℓ : ℝ) - 1)

/-- The constant of N, Theorem 5.1, for a Mertens constant `M₀` and the remaining
`κ`-dependent part `rest(κ) = I(κ) + 3κ/20 + 2/400` (in nats):
`c(κ) = [κ(12 − κ)(M₀ − ln 20) + rest(κ)] / ln 2`.  The true value has `M₀ = −γ − ½ ln 3`. -/
noncomputable def cConst (M₀ : ℝ) (rest : ℝ → ℝ) (κ : ℝ) : ℝ :=
  (κ * (12 - κ) * (M₀ - Real.log 20) + rest κ) / Real.log 2

/-- The Mertens constant with `ℓ = 3` removed: `−γ − ½ ln 3`. -/
noncomputable def mertens3Const : ℝ := -Real.eulerMascheroniConstant - Real.log 3 / 2

end Zeta35
