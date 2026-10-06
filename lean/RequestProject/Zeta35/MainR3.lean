import RequestProject.Zeta35.MainR2
import RequestProject.Zeta35.NVMain

/-!
# Round 2 assembly with non-vanishing discharged

`Zeta35InputsR3` is `Zeta35InputsR2` without the field `nonvanishing`, which is now the theorem
`Zeta35.NV.nonvanishing_holds` (N, Theorem 6.2).
-/

open Polynomial Finset Filter Topology

namespace Zeta35

open Hankel2

/-- **The inputs of N still missing** after N, Theorem 6.2 is proved. -/
structure Zeta35InputsR3 where
  /-- (i) **N, Theorem 3.1 (3-adic decay)**. -/
  decay : ∀ n K : ℕ, Even n → 2 ≤ K → K ≤ 6 * n + 2 →
    ‖aeval (zeta3 5) (hankelPoly n K)‖ ≤ (3 : ℝ) ^ (-decayExp n K)
  /-- (ii) **N, Theorem 4.1 (archimedean size)** for `κ = K/n ∈ [5.9, 6]`, profile `σ_κ ≡ κ/3`,
  for `Δ_K ≠ 0`. -/
  arch : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
    (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → hankelPoly n K ≠ 0 →
      Real.log (l1 (hankelPoly n K)) ≤
        (((K : ℝ) / n) ^ 2 - 12 * ((K : ℝ) / n)) * (n : ℝ) ^ 2 * Real.log n
          + (n : ℝ) ^ 2 * (Fenergy3 (sigmaK ((K : ℝ) / n)) +
              gap3 ((K : ℝ) / n) (sigmaK ((K : ℝ) / n)))
          + ε * (n : ℝ) ^ 2
  /-- The `κ`-dependent part `rest(κ)` of `c(κ)`. -/
  cRest : ℝ → ℝ
  /-- (iii-b) **N, Theorem 5.1**. -/
  thm_5_1 : ∀ M₀ : ℝ, Tendsto (fun Y : ℝ => mertens3Sum Y - Real.log Y) atTop (𝓝 M₀) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n K : ℕ, N ≤ n → Even n →
      (5.9 : ℝ) ≤ (K : ℝ) / n → (K : ℝ) / n ≤ 6 → ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 3) →
        ∑ ℓ ∈ S, (TPplus ℓ n K : ℝ) * Real.logb 2 ℓ ≤
          ((K : ℝ) / n) * (12 - (K : ℝ) / n) * (n : ℝ) ^ 2 * Real.logb 2 n
            + cConst M₀ cRest ((K : ℝ) / n) * (n : ℝ) ^ 2 + ε * (n : ℝ) ^ 2
  /-- (iii-c) **The certificate bound** `c(κ) ≤ 71.2` on `[5.9, 6]`. -/
  table_c : ∀ κ : ℝ, 5.9 ≤ κ → κ ≤ 6 → cConst mertens3Const cRest κ ≤ 71.2

/-- The `Zeta35InputsR2` obtained by adding the proved field `nonvanishing`. -/
def Zeta35InputsR3.toR2 (I : Zeta35InputsR3) : Zeta35InputsR2 where
  decay := I.decay
  arch := I.arch
  cRest := I.cRest
  thm_5_1 := I.thm_5_1
  table_c := I.table_c
  nonvanishing := NV.nonvanishing_holds

/-- **`ζ₃(5)` is irrational**, from the inputs `Zeta35InputsR3` (N, Theorem 6.2 is proved). -/
theorem zeta3_five_irrational_R3 (I : Zeta35InputsR3) : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) :=
  zeta3_five_irrational_R2 I.toR2

end Zeta35
