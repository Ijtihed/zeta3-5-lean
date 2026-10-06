# ζ₃(5) is irrational: Lean 4 formalization

Ijtihed Kilani (Aalto University), 2026. Formalization of the paper *On the irrationality of ζ₃(5)*.

## Main theorem
```lean
-- lean/RequestProject/Zeta35/MainFinal.lean
theorem Zeta35.zeta3_five_irrational_final : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3])
```
It has no hypotheses and depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

`zeta3 5` is defined in `lean/RequestProject/Zeta35/Target.lean` as (1/(4·3⁵)) Σ_{a=1,2} ∫_{ℤ₃} (t + a/3)⁻⁴ dt, with
the Volkenborn integral defined as the limit of 3⁻ᴺ Σ_{t<3ᴺ} f(t). The existence of this limit is proved.

## What is not formalized
- The identification of `zeta3 5` with the Kubota–Leopoldt value L₃(5, ω⁻⁴) is the classical normalisation (paper,
  Lemma 2.1). It only involves a non-zero rational factor.
- The formal proof uses slightly relaxed constants (K/n ∈ [5.9, 6], denominator constant c ≤ 71.2). It still has a
  margin of at least 4 bits per n²; the paper's margin is 7.93.

## Build
Requires Lean 4.28.0 (pinned in `lean/lean-toolchain`) and Mathlib v4.28.0 (pinned in `lean/lake-manifest.json`).
```
cd lean
lake exe cache get
lake build RequestProject.Zeta35.MainFinal
lake env lean scripts/print_axioms_Z35_R3.lean
```
The certificate modules (`Zeta35/CertData/`) are checked by kernel evaluation and take some time and memory. The full
verification log, including a clean build and `leanchecker --fresh` replays, is in `verification/VERIFY.md`.

## Contents
- `lean/`: the Lean project, exactly the 175 modules imported by the main theorem. `RequestProject/Zeta35/` is this
  formalization; `RequestProject/Zeta7/` is reused from the author's ζ₂(7) formalization (namespace `Hankel2`, with the
  prime number theorem and Mertens' theorem).
- `lean/certificates/`: the denominator certificate (JSON) and an independent Python checker (`check_cp_indep.py`,
  needs mpmath).
- `lean/scripts/`: the generator of the certificate data modules, and the axiom printout.
- `checks/`: small exact checks of the paper's local blocks and non-vanishing (not inputs to the Lean proof).
- `verification/VERIFY.md`: the verification log.

Some docstrings refer to intermediate assembly stages (`MainR2` … `MainR5`) and an internal roadmap ("CLAIMS"); every
input they call open is proved by a later module, ending in `MainFinal.lean`.

## How it was made
The formalization was produced with Harmonic's Aristotle prover from the paper and a roadmap prepared with the large
language model Claude Opus 5.5 (Anthropic). The author directed the work and checked the results.

## License
MIT; see `LICENSE`.
