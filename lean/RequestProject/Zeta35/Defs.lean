import RequestProject.Zeta35.Target
import RequestProject.Zeta35.PartialFrac

/-!
# The construction of paper N, §2: weight, functional, local constants, Hankel polynomial

Notation of N, §1: `n` is even, `R = 3n/2`, and the nodes are the integers `k` with `|k| ≤ R`
(`3n + 1` of them).  The definitions below make sense for every `n` (with `R = ⌊3n/2⌋`).

* `W n t = ∏_{|k| ≤ R} (t + k)^{-4}` on `ℚ₃` (`Zeta35.W`);
* `L n P = ∑_{a=1,2} ∫_{ℤ₃} (P W)'(t + a/3) dt` (`Zeta35.L`), the Volkenborn functional of N, §2;
* `H_k[b] = [u^b] u⁴ W(−k + u)` (`Zeta35.Hk`) and `P_a(k) = [u^a] P(−k + u)` (`Zeta35.Pjet`);
* the harmonic sums `S_k(M)` of N, Lemma 2.2, for every `k ∈ ℤ` (`Zeta35.Sk`):
  `S_k(M) = −M 3^{M+1} ∑_{m ≤ 3k−1, 3 ∤ m} m^{−M−1}` for `k > 0`,
  `S_k(M) = M (−1)^{M+1} 3^{M+1} ∑_{m ≤ 3|k|−1, 3 ∤ m} m^{−M−1}` for `k < 0`, `S_0(M) = 0`;
* the local constants `c_{k,a} = β_{k,a} + α_{k,a} ζ₃(5)` of N, Lemma 2.2, i.e.
  `c_{k,a} = −∑_{i=1}^{4−a} i H_k[4−i−a] (I_{i+1} + S_k(i+1))` with `I_3 = I_5 = 0`, the `I_2` terms
  cancelling, and `I_4 = 4·3⁵ ζ₃(5)`:
  `α_{k,a} = −3·4·3⁵ H_k[1−a]` for `a ≤ 1`, `α_{k,a} = 0` for `a ≥ 2` (`alphaC`),
  `β_{k,a} = −∑_{i=1}^{4−a} i H_k[4−i−a] S_k(i+1)` (`betaC`);
* `a(P) = ∑_k ∑_{a ≤ 3} α_{k,a} P_a(k)` (`aL`), `b(P) = ∑_k ∑_{a ≤ 3} β_{k,a} P_a(k)` (`bL`);
* the Hankel polynomial `Δ_K(X) = det[b(x^{i+j}) + X a(x^{i+j})]_{i,j<K}` (`hankelPoly`).
-/

open Polynomial Finset

namespace Zeta35

open Hankel2

/-- `R = 3n/2` (exact for even `n`). -/
def R (n : ℕ) : ℕ := 3 * n / 2

/-- The nodes `k ∈ ℤ` with `|k| ≤ R`. -/
def nodes (n : ℕ) : Finset ℤ := Finset.Icc (-(R n : ℤ)) (R n)

theorem card_nodes (n : ℕ) : (nodes n).card = 2 * R n + 1 := by
  rw [nodes, Int.card_Icc]; omega

theorem R_of_even {n : ℕ} (hn : Even n) : 2 * R n = 3 * n := by
  obtain ⟨m, rfl⟩ := hn; unfold R; omega

theorem card_nodes_of_even {n : ℕ} (hn : Even n) : (nodes n).card = 3 * n + 1 := by
  rw [card_nodes, R_of_even hn]

/-- The weight `W(t) = ∏_{|k| ≤ R} (t + k)^{-4}` on `ℚ₃`. -/
noncomputable def W (n : ℕ) (t : ℚ_[3]) : ℚ_[3] := (∏ k ∈ nodes n, (t + (k : ℚ_[3])) ^ 4)⁻¹

/-- **The functional of N, §2**: `L(P) = ∑_{a=1,2} ∫_{ℤ₃} (P W)'(t + a/3) dt`. -/
noncomputable def L (n : ℕ) (P : ℚ[X]) : ℚ_[3] :=
  ∑ a ∈ Finset.Icc (1 : ℕ) 2,
    volkInt 3 (fun t => deriv (fun s => aeval s P * W n s) (t + (a : ℚ_[3]) / 3))

/-- `H_k[b] = [u^b] u⁴ W(−k + u)`. -/
noncomputable def Hk (n : ℕ) (k : ℤ) (b : ℕ) : ℚ := PF.Hk (nodes n) k b

/-- `P_a(k) = [u^a] P(−k + u)`. -/
noncomputable def Pjet (P : ℚ[X]) (k : ℤ) (a : ℕ) : ℚ := PF.Pjet P k a

/-- The partial sum `∑_{1 ≤ m < 3N, 3 ∤ m} m^{−M−1}`. -/
noncomputable def hsum3 (N M : ℕ) : ℚ :=
  ∑ m ∈ (Finset.range (3 * N)).filter (fun m => ¬ 3 ∣ m), ((m : ℚ) ^ (M + 1))⁻¹

/-- **The harmonic sums `S_k(M)` of N, Lemma 2.2**, for every `k ∈ ℤ`. -/
noncomputable def Sk (k : ℤ) (M : ℕ) : ℚ :=
  if 0 < k then -(M : ℚ) * 3 ^ (M + 1) * hsum3 k.natAbs M
  else if k < 0 then (M : ℚ) * (-1) ^ (M + 1) * 3 ^ (M + 1) * hsum3 k.natAbs M
  else 0

/-- `α_{k,a}` (the coefficient of `ζ₃(5)` in `c_{k,a}`). -/
noncomputable def alphaC (n : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  if a ≤ 1 then -(3 * (4 * 3 ^ 5)) * Hk n k (1 - a) else 0

/-- `β_{k,a}` (the rational part of `c_{k,a}`). -/
noncomputable def betaC (n : ℕ) (k : ℤ) (a : ℕ) : ℚ :=
  -∑ i ∈ Finset.Icc 1 (4 - a), (i : ℚ) * Hk n k (4 - i - a) * Sk k (i + 1)

/-- `a(P) = ∑_k ∑_{a ≤ 3} α_{k,a} P_a(k)`. -/
noncomputable def aL (n : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range 4, alphaC n k a * Pjet P k a

/-- `b(P) = ∑_k ∑_{a ≤ 3} β_{k,a} P_a(k)`. -/
noncomputable def bL (n : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ nodes n, ∑ a ∈ range 4, betaC n k a * Pjet P k a

/-- **The Hankel polynomial** `Δ_K(X) = det[b(x^{i+j}) + X a(x^{i+j})]_{i,j<K}`. -/
noncomputable def hankelPoly (n K : ℕ) : ℚ[X] :=
  (Matrix.of fun i j : Fin K =>
    C (bL n (X ^ ((i : ℕ) + j))) + C (aL n (X ^ ((i : ℕ) + j))) * X).det

end Zeta35
