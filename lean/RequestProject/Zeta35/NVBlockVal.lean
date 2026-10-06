import RequestProject.Zeta35.LocalBlocks

/-!
# Non-vanishing (N, §6): the leading pair values are `2 Λ_j`

`limL σ ε C a` is the mod-`ℓ` leading value of `ℓ^{10−a} β^ℓ_{k,a} / y₀` at a node with harmonic
poles `{cℓ : c ∈ C}`, sign pattern `σ` of `S_k`, and mate at `k + εℓ` (see `NV.local_const`):
`limL σ ε C a = −∑_{i=1}^{4−a} ∑_{c ∈ C} i σ_{i+1} (i+1) 3^{i+2} c^{-(i+2)} (−ε)^{4−i−a} C(7−i−a, 3)`.

For the anchor `k` (`S_k = −…`, mate `k − ℓ`) we get `limA`, for the partner `k − ℓ`
(`S = (−1)^{M+1} …`, mate `k`) we get `limP`.  The pair value on `w^s` is
`Mval C₀ C₁ s = [s < 4] limA C₀ s + ∑_{t<4} limP C₁ t · C(s, t)` (the partner jets of `w^s` at `w = 1`
are the binomial coefficients).  We check (`Mval_eq`) that `Mval = 2 Λ_j` on `w^s`, `s ≤ 6`, for
the three pair types `(C₀, C₁) = (∅, {1,2})`, `({1},{1})`, `({1,2}, ∅)` (`j = 0, 1, 2`).
-/

open Finset

namespace Zeta35.NV

/-- The leading value of the pole part of a local constant (see the module docstring). -/
def limL (σ : ℕ → ℚ) (ε : ℚ) (Cs : Finset ℕ) (a : ℕ) : ℚ :=
  -∑ i ∈ Icc 1 (4 - a), ∑ c ∈ Cs, (i : ℚ) * σ (i + 1) * ((i + 1 : ℕ) : ℚ) * 3 ^ (i + 1 + 1) *
    ((c : ℚ) ^ (i + 1 + 1))⁻¹ * ((-ε) ^ (4 - i - a) * ((4 - i - a + 3).choose 3 : ℚ))

/-- Anchor (`k > 0`, mate `k − ℓ`). -/
def limA (Cs : Finset ℕ) (a : ℕ) : ℚ := limL (fun _ => -1) (-1) Cs a

/-- Partner (`k − ℓ < 0`, mate `k`). -/
def limP (Cs : Finset ℕ) (a : ℕ) : ℚ := limL (fun M => (-1) ^ (M + 1)) 1 Cs a

/-- The leading pair value on `w^s`. -/
def Mval (C0 C1 : Finset ℕ) (s : ℕ) : ℚ :=
  (if s < 4 then limA C0 s else 0) + ∑ t ∈ range 4, limP C1 t * (s.choose t : ℚ)

/-- The harmonic pole sets of the pair of type `j`. -/
def C0j (j : ℕ) : Finset ℕ := if j = 0 then ∅ else if j = 1 then {1} else {1, 2}

def C1j (j : ℕ) : Finset ℕ := if j = 0 then {1, 2} else if j = 1 then {1} else ∅

theorem Mval_eq (j s : ℕ) (hj : j ≤ 2) (hs : s ≤ 6) :
    Mval (C0j j) (C1j j) s = 2 * Blocks.Lam j s := by
  interval_cases j <;> interval_cases s <;>
  simp only [C0j, C1j, Blocks.Lam_0_0, Blocks.Lam_0_1, Blocks.Lam_0_2, Blocks.Lam_0_3,
    Blocks.Lam_0_4, Blocks.Lam_0_5, Blocks.Lam_0_6, Blocks.Lam_1_0, Blocks.Lam_1_1,
    Blocks.Lam_1_2, Blocks.Lam_1_3, Blocks.Lam_1_4, Blocks.Lam_1_5, Blocks.Lam_1_6,
    Blocks.Lam_2_0, Blocks.Lam_2_1, Blocks.Lam_2_2, Blocks.Lam_2_3, Blocks.Lam_2_4,
    Blocks.Lam_2_5, Blocks.Lam_2_6] <;> decide +kernel

end Zeta35.NV
