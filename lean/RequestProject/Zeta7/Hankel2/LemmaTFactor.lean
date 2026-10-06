import RequestProject.Zeta7.Hankel2.Zeta27Defs
import RequestProject.Zeta7.Hankel2.CauchyBinet

/-!
# The factorisation `Δ_K = det(E · C · Eᵀ)` (for paper Theorem 7.1)

Index the columns by `ι = Fin (3n+1) ×ₗ Fin 4` (node `u`, Taylor order `b`, lexicographic).  Then
`H_{ij} = ∑_u ∑_{b,b'} E_{i,(u,b)} c_{u,b+b'} E_{j,(u,b')}` with the confluent Vandermonde matrix
`E_{i,(u,b)} = C(i,b) x_u^{i−b}` (`Emat`) and the block-diagonal matrix
`C_{(u,b),(u',b')} = [u = u'] c_{u,b+b'}` (`Cbl`).  This is the Leibniz rule
`(x^{i+j})_a = ∑_{b+b'=a} (x^i)_b (x^j)_{b'}` for the Taylor coefficients at the nodes.
-/

open Polynomial Finset Matrix

namespace Hankel2.Fam3

/-- The column index set `ι = Fin (3n+1) ×ₗ Fin 4`. -/
abbrev Idx (n : ℕ) := Lex (Fin (3 * n + 1) × Fin 4)

/-- `E_{i,(u,b)} = C(i,b) x_u^{i−b}`. -/
noncomputable def Emat (n K : ℕ) : Matrix (Fin K) (Idx n) ℚ := fun i c =>
  ((i : ℕ).choose (ofLex c).2 : ℚ) * xnode n (nodeOf n (ofLex c).1) ^ ((i : ℕ) - (ofLex c).2)

/-- The block-diagonal matrix `[u = u'] c_{u,b+b'}`. -/
noncomputable def Cbl (n : ℕ) : Matrix (Idx n) (Idx n) ℚ[X] := fun c d =>
  if (ofLex c).1 = (ofLex d).1 then cPoly n (nodeOf n (ofLex c).1) ((ofLex c).2 + (ofLex d).2)
  else 0

theorem cPoly_eq_zero {n : ℕ} {k : ℤ} {m : ℕ} (hm : 4 ≤ m) : cPoly n k m = 0 := by
  simp [cPoly, show ¬ m ≤ 3 by omega]

theorem sum_range4_antidiag {R : Type*} [CommRing R] (g : ℕ → R) (hg : ∀ m, 4 ≤ m → g m = 0)
    (h : ℕ → ℕ → R) :
    ∑ a ∈ range 4, g a * ∑ x ∈ antidiagonal a, h x.1 x.2 =
      ∑ b : Fin 4, ∑ b' : Fin 4, g (b + b') * h b b' := by
  have g4 := hg 4 le_rfl; have g5 := hg 5 (by norm_num); have g6 := hg 6 (by norm_num)
  simp [sum_range_succ, Fin.sum_univ_four, Finset.Nat.antidiagonal_succ, g4, g5, g6]
  ring

theorem hasseDeriv_X_pow_eval (m a : ℕ) (x : ℚ) :
    (hasseDeriv a ((X : ℚ[X]) ^ m)).eval x = (m.choose a : ℚ) * x ^ (m - a) := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, eval_monomial, mul_one]

theorem pjet_X_pow (n : ℕ) (k : ℤ) (i j a : ℕ) :
    Pjet n (X ^ (i + j)) k a = ∑ x ∈ antidiagonal a,
      ((i.choose x.1 : ℚ) * xnode n k ^ (i - x.1)) * ((j.choose x.2 : ℚ) * xnode n k ^ (j - x.2)) := by
  rw [Pjet, pow_add, hasseDeriv_mul, eval_finset_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_mul, hasseDeriv_X_pow_eval, hasseDeriv_X_pow_eval]

theorem sum_nodes_eq (n : ℕ) {M : Type*} [AddCommMonoid M] (F : ℤ → M) :
    ∑ k ∈ Fam3PF.nodes n, F k = ∑ u : Fin (3 * n + 1), F (nodeOf n u) := by
  symm
  refine sum_bij (fun u _ => nodeOf n u) ?_ ?_ ?_ ?_
  · intro u _
    simp only [Fam3PF.nodes, mem_Icc, nodeOf]
    have := u.isLt
    omega
  · intro u _ v _ h
    simp only [nodeOf] at h
    exact Fin.ext (by omega)
  · intro k hk
    simp only [Fam3PF.nodes, mem_Icc] at hk
    refine ⟨⟨(k + n).toNat, by omega⟩, mem_univ _, ?_⟩
    simp only [nodeOf]
    omega
  · intro u _; rfl

theorem sum_idx {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Idx n → M) :
    ∑ c : Idx n, F c = ∑ u : Fin (3 * n + 1), ∑ b : Fin 4, F (toLex (u, b)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv toLex _ _ fun _ => rfl).symm

/-- **The factorisation** `Δ_K = det(E C Eᵀ)`. -/
theorem hankelPoly_eq_det (n K : ℕ) :
    hankelPoly n K =
      ((Emat n K).map (C : ℚ →+* ℚ[X]) * Cbl n * ((Emat n K).map (C : ℚ →+* ℚ[X]))ᵀ).det := by
  unfold hankelPoly
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [of_apply, mul_apply, map_apply, transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, sum_idx]
  -- left side as a sum over nodes
  have hL : C (bL n (X ^ ((i : ℕ) + j))) + C (aL n (X ^ ((i : ℕ) + j))) * X =
      ∑ u : Fin (3 * n + 1), ∑ a ∈ range 4,
        cPoly n (nodeOf n u) a * C (Pjet n (X ^ ((i : ℕ) + j)) (nodeOf n u) a) := by
    rw [bL, aL, sum_nodes_eq, sum_nodes_eq]
    simp only [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun u _ => sum_congr rfl fun a ha => ?_
    rw [cPoly, if_pos (by simp at ha; omega)]
    simp only [map_mul]; ring
  rw [hL]
  refine sum_congr rfl fun u _ => ?_
  simp_rw [pjet_X_pow, map_sum]
  rw [sum_range4_antidiag (fun a => cPoly n (nodeOf n u) a) (fun m hm => cPoly_eq_zero hm)
    (fun b b' => C (((i : ℕ).choose b : ℚ) * xnode n (nodeOf n u) ^ ((i : ℕ) - b) *
      (((j : ℕ).choose b' : ℚ) * xnode n (nodeOf n u) ^ ((j : ℕ) - b'))))]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_idx, Finset.sum_eq_single u]
  · refine sum_congr rfl fun b' _ => ?_
    simp only [Emat, Cbl, ofLex_toLex, if_true, map_mul, map_pow, map_natCast]
    ring
  · intro v _ hv
    refine sum_eq_zero fun b' _ => ?_
    simp [Cbl, Ne.symm hv]
  · simp

/-- **Double Cauchy–Binet expansion**:
`Δ_K = ∑_{f, g} det E[:, f] · det C[f, g] · det E[:, g]` over strictly monotone `f, g`. -/
theorem hankelPoly_eq_sum (n K : ℕ) :
    hankelPoly n K = ∑ f ∈ smSet K (Idx n), ∑ g ∈ smSet K (Idx n),
      C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
        C ((Emat n K).submatrix id g).det := by
  rw [hankelPoly_eq_det, Matrix.mul_assoc, det_mul_eq_sum_strictMono]
  refine sum_congr rfl fun f _ => ?_
  have h1 : (Cbl n * ((Emat n K).map (C : ℚ →+* ℚ[X]))ᵀ).submatrix f id =
      (Cbl n).submatrix f id * ((Emat n K).map (C : ℚ →+* ℚ[X]))ᵀ := by
    ext i j; simp [mul_apply]
  rw [h1, det_mul_eq_sum_strictMono, Finset.mul_sum]
  refine sum_congr rfl fun g _ => ?_
  have h2 : ((Emat n K).map (C : ℚ →+* ℚ[X])).submatrix id f =
      ((Emat n K).submatrix id f).map (C : ℚ →+* ℚ[X]) := rfl
  have h3 : ((Emat n K).map (C : ℚ →+* ℚ[X]))ᵀ.submatrix g id =
      (((Emat n K).submatrix id g).map (C : ℚ →+* ℚ[X]))ᵀ := rfl
  have h4 : ((Cbl n).submatrix f id).submatrix id g = (Cbl n).submatrix f g := rfl
  have h5 : ∀ M : Matrix (Fin K) (Fin K) ℚ, (M.map (C : ℚ →+* ℚ[X])).det = C M.det :=
    fun M => (RingHom.map_det C M).symm
  rw [h2, h3, det_transpose, h4, h5, h5]
  ring

end Hankel2.Fam3
