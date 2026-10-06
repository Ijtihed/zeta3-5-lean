import RequestProject.Zeta7.Hankel2.Volkenborn

/-!
# The fixed target for `ζ₃(5)` (paper N = `paper/N_zeta3_5.pdf`)

`IM M = ∑_{a=1,2} ∫_{ℤ₃} (t + a/3)^{-M} dt` is the Volkenborn integral of N, Lemma 2.1, and
`zeta3 s` is its normalisation `I_{s-1} = 3^s (s-1) ζ₃(s)` (N, Lemma 2.1, even `s - 1`).
The identification of `zeta3 5` with the Kubota–Leopoldt value `L₃(5, ω⁻⁴)` is the classical
fact cited in N, Lemma 2.1 ([Coh, §§11.2–11.3], [LLS, Lemma 2.5]); it is not formalised here.

The final theorem of the project is

`theorem Zeta35.zeta3_five_irrational_final : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3])`

with no hypotheses. These definitions must not be changed.
-/

namespace Zeta35

open Hankel2

/-- `I_M = ∑_{a=1,2} ∫_{ℤ₃} (t + a/3)^{-M} dt` (N, Lemma 2.1). -/
noncomputable def IM (M : ℕ) : ℚ_[3] :=
  ∑ a ∈ Finset.Icc (1 : ℕ) 2, volkInt 3 (fun t => ((t + (a : ℚ_[3]) / 3) ^ M)⁻¹)

/-- The normalisation of N, Lemma 2.1: `I_{s-1} = 3^s (s-1) ζ₃(s)`. -/
noncomputable def zeta3 (s : ℕ) : ℚ_[3] :=
  IM (s - 1) / (((s - 1 : ℕ) : ℚ_[3]) * 3 ^ s)

end Zeta35
