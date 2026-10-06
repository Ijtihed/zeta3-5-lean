import Mathlib

/-!
# W3: from the local block structure to a unit determinant

`ZETA7_STATUS.md`, rounds (e) and (g).  In Lemma W3 the weighted matrix `Ĝ_HS` (entries
`p^{ℓ_x+ℓ_y} G_HS[x,y]`) is shown to be `p`-integral and congruent mod `p` to a block-diagonal matrix whose
blocks are

* at a special node: a `4 × 4` block that is *anti-triangular* (entries with `a + b > 3` vanish) with unit
  anti-diagonal `p⁹ c₃`;
* at a generic node: a `2 × 2` block `[[p⁵c₀, p⁵c₁], [p⁵c₁, ≡ 0]]` with `p⁵c₁` a unit;
* at `g*`: a `1 × 1` unit.

This file proves, over an arbitrary local ring, the algebraic steps that turn this structure into
"`det Ĝ_HS` is a unit":

* `isUnit_det_of_blockTriangular_mod`: if the entries below the blocks (for any linear order on the block
  labels) lie in the maximal ideal and every diagonal block has unit determinant, the determinant is a unit.
  Congruence to a block-*diagonal* matrix is a special case.
* `isUnit_det_of_antitriangular_mod`: anti-triangular mod the maximal ideal with unit anti-diagonal.
* `isUnit_det_fin_two_of_mod`: the generic-node `2 × 2` block.
-/

open Matrix

namespace Hankel2

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A matrix whose reduction modulo the maximal ideal is block (lower-)triangular, with every diagonal block
of unit determinant, has unit determinant. -/
theorem isUnit_det_of_blockTriangular_mod {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (M : Matrix ι ι R) (blk : ι → β)
    (hoff : ∀ i j, blk j < blk i → M i j ∈ IsLocalRing.maximalIdeal R)
    (hblk : ∀ b, IsUnit (M.toSquareBlock blk b).det) : IsUnit M.det := by
  classical
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have htri : ((IsLocalRing.residue R).mapMatrix M).BlockTriangular blk := by
    intro i j hij
    simpa [IsLocalRing.residue_eq_zero_iff] using hoff i j hij
  rw [htri.det, Finset.prod_ne_zero_iff]
  intro b _
  have h : ((IsLocalRing.residue R).mapMatrix M).toSquareBlock blk b =
      (IsLocalRing.residue R).mapMatrix (M.toSquareBlock blk b) := rfl
  rw [h, ← RingHom.map_det, IsLocalRing.residue_ne_zero_iff_isUnit]
  exact hblk b

/-- The special-node block: if the entries with `i + j ≥ n` lie in the maximal ideal and the anti-diagonal
entries (`i + j = n - 1`) are units, the determinant is a unit. -/
theorem isUnit_det_of_antitriangular_mod {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hbelow : ∀ i j : Fin n, n ≤ (i : ℕ) + j → M i j ∈ IsLocalRing.maximalIdeal R)
    (hanti : ∀ i : Fin n, IsUnit (M i (Fin.rev i))) : IsUnit M.det := by
  have hperm : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))).det =
      Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) * M.det := Matrix.det_permute' _ _
  have hunit : IsUnit (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have htri : ((IsLocalRing.residue R).mapMatrix
        (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)))).BlockTriangular id := by
      intro i j hij
      have hle : n ≤ (i : ℕ) + (Fin.rev j : ℕ) := by
        rw [Fin.val_rev]; have := j.2; have : (j : ℕ) < i := hij; omega
      simpa [IsLocalRing.residue_eq_zero_iff] using hbelow i (Fin.rev j) hle
    rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
    intro i _
    simpa [IsLocalRing.residue_ne_zero_iff_isUnit] using hanti i
  rw [hperm] at hunit
  exact isUnit_of_mul_isUnit_right hunit

/-- The generic-node block `[[a, b], [b', c]]` with `c` in the maximal ideal and `b, b'` units. -/
theorem isUnit_det_fin_two_of_mod (M : Matrix (Fin 2) (Fin 2) R)
    (h11 : M 1 1 ∈ IsLocalRing.maximalIdeal R) (h01 : IsUnit (M 0 1)) (h10 : IsUnit (M 1 0)) :
    IsUnit M.det := by
  rw [Matrix.det_fin_two]
  have hu : IsUnit (-(M 0 1 * M 1 0)) := (h01.mul h10).neg
  have hm : M 0 0 * M 1 1 ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_left _ _ h11
  have : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -(M 0 1 * M 1 0) + M 0 0 * M 1 1 := by ring
  rw [this]
  by_contra hnu
  have h2 : -(M 0 1 * M 1 0) + M 0 0 * M 1 1 ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h3 : -(M 0 1 * M 1 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h2 hm
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

end Hankel2
