# ζ₃(5) is irrational: Lean 4 formalization

Lean 4 proof of the main theorem of *On the irrationality of ζ₃(5)* by Ijtihed Kilani.

```lean
-- lean/RequestProject/Zeta35/MainFinal.lean
theorem Zeta35.zeta3_five_irrational_final : ∀ r : ℚ, zeta3 5 ≠ (r : ℚ_[3])
```

The theorem has no hypotheses. It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
`zeta3 5` is defined in `Zeta35/Target.lean` as I₄/972, where I₄ is a sum of two 3-adic Volkenborn integrals. The
identity `zeta3 5` = L₃(5, ω⁻⁴) with the Kubota–Leopoldt value is classical and is not formalized (paper, Lemma 2.1).

## Build

Requires Lean 4.28.0 and Mathlib v4.28.0, both pinned in `lean/`.

```
cd lean
lake exe cache get
lake build RequestProject.Zeta35.MainFinal
```

The certificate modules are checked by kernel evaluation and need time and memory.

## Contents

- `lean/`: the Lean project. `Zeta35/` is this formalization. `Zeta7/` is reused from the author's ζ₂(7) formalization.
- `lean/certificates/`: the denominator certificate, an independent Python checker, and `enclose_constants.py`, which
  proves the final numerical bounds in exact rational arithmetic.
- `checks/`: small exact checks of the local blocks and non-vanishing.
- `verification/VERIFY.md`: build and `leanchecker` logs.

The formalization was produced with Harmonic's Aristotle prover.

## License

MIT
