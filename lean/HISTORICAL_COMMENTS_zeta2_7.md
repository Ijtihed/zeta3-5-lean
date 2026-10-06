# Historical comments in the Lean sources

The Lean sources were developed over eight rounds. Some doc-comments were written in early rounds
and describe gaps that later modules closed. They were left unchanged, so that the sources stay
byte-identical to the verified build (SHA-256 in `../verification/original_aristotle_output/`).
None of these comments affects any statement or proof.

| Location | Historical comment | Current status |
|---|---|---|
| `Zeta7/Hankel2/Target.lean`, header (lines 4–17) | The asymptotic rates are "not discharged here". | This round-1 conditional target is not imported by the final theorem. The unconditional result is `Hankel2.zeta2_seven_irrational_final` in `Main2adicFinal.lean`. |
| `Zeta7/Hankel2/Volkenborn.lean`, lines 26–31 | Existence of the integral "appears as an explicit hypothesis `HasVolkenborn`". | Existence is proved in `VolkenbornExist.lean` (`exists_hasVolkenborn_half`) and used on the main path (`PurityInt.lean`). |
| `Zeta7/Hankel2/Criterion.lean`, line 25 | "What remains open for ζ₂(7) is the analytic …" | Supplied by later modules: Theorem A (`ThmA2adic.lean`, `Lemma43.lean`), Lemma B (`LemmaB61.lean`), the denominator bound (`LemmaT.lean`, `Thm81Reduction.lean`, `CertC.lean`) and the constants (`PropA2.lean`). |
| `Zeta7/Hankel2/NVFamily3.lean`, line 322 | "true for all large n by the prime number theorem; not proved here" | The prime number theorem is proved in `Zeta7/PNT/` (`PNT.tendsto_theta_div`) and used by `aux_prime` on the main path. |

To see what the final theorem depends on, run `#print axioms Hankel2.zeta2_seven_irrational_final`.
It reports only `[propext, Classical.choice, Quot.sound]`.
