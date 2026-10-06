import RequestProject.Zeta35.MainR3
import RequestProject.Zeta35.DecayMain

/-!
# Round 2 assembly with non-vanishing and decay discharged

`Zeta35InputsR4` is `Zeta35InputsR3` without the field `decay`, which is now the theorem
`Zeta35.Dec.decay_holds` (N, Theorem 3.1).  The remaining fields are N, Theorem 4.1 (`arch`,
for `Δ_K ≠ 0`) and N, Theorem 5.1 with the certificate bound (`cRest`, `thm_5_1`, `table_c`).
-/

open Polynomial Finset Filter Topology

namespace Zeta35

open Hankel2

/-- **The inputs of N still missing** after N, Theorems 3.1 and 6.2 are proved. -/
structure Zeta35InputsR4 where
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

/-- The `Zeta35InputsR3` obtained by adding the proved field `decay`. -/
def Zeta35InputsR4.toR3 (I : Zeta35InputsR4) : Zeta35InputsR3 where
  decay := Dec.decay_holds
  arch := I.arch
  cRest := I.cRest
  thm_5_1 := I.thm_5_1
  table_c := I.table_c

/-- **`ζ₃(5)` is irrational**, from the inputs `Zeta35InputsR4` (N, Theorems 3.1 and 6.2 are
proved). -/
theorem zeta3_five_irrational_R4 (I : Zeta35InputsR4) : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) :=
  zeta3_five_irrational_R3 I.toR3

end Zeta35
