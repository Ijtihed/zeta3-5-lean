import RequestProject.Zeta35.MainR5
import RequestProject.Zeta35.DenTable

/-!
# **`ζ₃(5)` is irrational** (final theorem, no hypotheses)

All inputs of N are now theorems:

* N, Theorem 3.1 (decay): `Zeta35.Dec.decay_holds`;
* N, Theorem 4.1 (archimedean bound): `Zeta35.Arch.arch_holds`;
* N, Theorem 5.1 (denominators): `Zeta35.Den.thm_5_1_holds`, with
  `rest(κ) = Zeta35.Den.cRest35 κ = stepBound + 3κ/20 + 2/400`;
* the certificate bound `c(κ) ≤ 71.2` on `[5.9, 6]`: `Zeta35.Den.table_c_holds`
  (the certificate `certificates/cert_c_p3_q4_d1_a1.5_k6.0.json`, kernel-checked in
  `Zeta35/CertData/B*.lean`);
* N, Theorem 6.2 (non-vanishing): `Zeta35.NV.nonvanishing_holds`.
-/

namespace Zeta35

/-- The inputs `Zeta35InputsR5`, all discharged. -/
noncomputable def inputsR5 : Zeta35InputsR5 where
  cRest := Den.cRest35
  thm_5_1 := Den.thm_5_1_holds
  table_c := Den.table_c_holds

/-- **`ζ₃(5)` is irrational.** -/
theorem zeta3_five_irrational_final : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3]) :=
  zeta3_five_irrational_R5 inputsR5

end Zeta35
