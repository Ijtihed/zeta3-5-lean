import RequestProject.Zeta35.MainR4
import RequestProject.Zeta35.ArchMain3

/-!
# Round 3 assembly with the archimedean bound discharged

`Zeta35InputsR5` is `Zeta35InputsR4` without the field `arch`, which is now the theorem
`Zeta35.Arch.arch_holds` (N, Theorem 4.1).  The remaining fields are N, Theorem 5.1 with the
certificate bound (`cRest`, `thm_5_1`, `table_c`).
-/

open Polynomial Finset Filter Topology

namespace Zeta35

open Hankel2

/-- **The inputs of N still missing** after N, Theorems 3.1, 4.1 and 6.2 are proved. -/
structure Zeta35InputsR5 where
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

/-- The `Zeta35InputsR4` obtained by adding the proved field `arch`. -/
def Zeta35InputsR5.toR4 (I : Zeta35InputsR5) : Zeta35InputsR4 where
  arch := Arch.arch_holds
  cRest := I.cRest
  thm_5_1 := I.thm_5_1
  table_c := I.table_c

/-- **`ζ₃(5)` is irrational**, from the inputs `Zeta35InputsR5` (N, Theorems 3.1, 4.1 and 6.2
are proved). -/
theorem zeta3_five_irrational_R5 (I : Zeta35InputsR5) : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) :=
  zeta3_five_irrational_R4 I.toR4

end Zeta35
