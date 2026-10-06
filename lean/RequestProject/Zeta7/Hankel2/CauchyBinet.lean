import Mathlib

/-!
# The Cauchy–Binet formula

For `A : Matrix (Fin K) ι R` and `B : Matrix ι (Fin K) R` over a commutative ring, with `ι` a
finite linear order,

  `det (A * B) = ∑_{f : Fin K → ι strictly monotone} det A[:, f] · det B[f, :]`

(`Hankel2.det_mul_eq_sum_strictMono`).  Used for the tree bound (paper Theorem 7.1).
-/

open Matrix Finset Equiv

namespace Hankel2

variable {R : Type*} [CommRing R] {K : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The set of strictly monotone maps `Fin K → ι`. -/
noncomputable def smSet (K : ℕ) (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (Fin K → ι) :=
  by classical exact univ.filter fun f => StrictMono f

theorem mem_smSet {f : Fin K → ι} : f ∈ smSet K ι ↔ StrictMono f := by
  classical
  unfold smSet; simp

omit [LinearOrder ι] in
/-- `det (A B) = ∑_h (∏_i B[h i, i]) det A[:, h]`, over all maps `h`. -/
theorem det_mul_eq_sum_fun (A : Matrix (Fin K) ι R) (B : Matrix ι (Fin K) R) :
    (A * B).det = ∑ h : Fin K → ι, (∏ i, B (h i) i) * (A.submatrix id h).det := by
  classical
  rw [det_apply]
  simp only [mul_apply]
  have : ∀ σ : Perm (Fin K), (∏ i, ∑ j, A (σ i) j * B j i) =
      ∑ h : Fin K → ι, ∏ i, (A (σ i) (h i) * B (h i) i) := by
    intro σ
    rw [Finset.prod_univ_sum]
    simp
  simp_rw [this, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [submatrix_apply, id]
  rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul]
  ring

/-- **Cauchy–Binet.** -/
theorem det_mul_eq_sum_strictMono (A : Matrix (Fin K) ι R) (B : Matrix ι (Fin K) R) :
    (A * B).det = ∑ f ∈ smSet K ι, (A.submatrix id f).det * (B.submatrix f id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  -- drop the non-injective maps
  have hni : ∀ h : Fin K → ι, ¬ Function.Injective h → (A.submatrix id h).det = 0 := by
    intro h hh
    simp only [Function.Injective, not_forall] at hh
    obtain ⟨a, b, hab, hne⟩ := hh
    exact det_zero_of_column_eq hne fun k => by simp [hab]
  rw [← Finset.sum_filter_of_ne (p := fun h => Function.Injective h) (fun h _ hh => by
    by_contra hc; exact hh (by rw [hni h hc, mul_zero]))]
  -- expand the right side over pairs `(f, τ)`
  have hR : ∀ f ∈ smSet K ι, (A.submatrix id f).det * (B.submatrix f id).det =
      ∑ τ : Perm (Fin K), (∏ i, B (f (τ i)) i) * (A.submatrix id (f ∘ τ)).det := by
    intro f _
    rw [det_apply (B.submatrix f id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : A.submatrix id (f ∘ τ) = (A.submatrix id f).submatrix id τ := rfl
    rw [this, det_permute']
    simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hR, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun fτ _ => fτ.1 ∘ fτ.2) ?_ ?_ ?_ ?_
  · intro fτ hfτ
    simp only [mem_product, mem_smSet] at hfτ
    simp only [mem_filter, mem_univ, true_and]
    exact hfτ.1.injective.comp fτ.2.injective
  · intro ⟨f, τ⟩ h1 ⟨f', τ'⟩ h2 heq
    simp only [mem_product, mem_smSet, mem_univ, and_true] at h1 h2
    simp only at heq
    have himg : univ.image f = univ.image f' := by
      have e1 : univ.image (f ∘ τ) = univ.image f := by
        ext x; simp only [mem_image, mem_univ, true_and, Function.comp]
        exact ⟨fun ⟨a, ha⟩ => ⟨τ a, ha⟩, fun ⟨a, ha⟩ => ⟨τ.symm a, by simpa using ha⟩⟩
      have e2 : univ.image (f' ∘ τ') = univ.image f' := by
        ext x; simp only [mem_image, mem_univ, true_and, Function.comp]
        exact ⟨fun ⟨a, ha⟩ => ⟨τ' a, ha⟩, fun ⟨a, ha⟩ => ⟨τ'.symm a, by simpa using ha⟩⟩
      rw [← e1, ← e2, heq]
    have hc : (univ.image f).card = K := by
      rw [card_image_of_injective _ h1.injective, card_univ, Fintype.card_fin]
    have hf : f = (univ.image f).orderEmbOfFin hc :=
      orderEmbOfFin_unique hc (fun x => mem_image_of_mem f (mem_univ x)) h1
    have hf' : f' = (univ.image f).orderEmbOfFin hc :=
      orderEmbOfFin_unique hc (fun x => by rw [himg]; exact mem_image_of_mem f' (mem_univ x)) h2
    have hff : f = f' := hf.trans hf'.symm
    subst hff
    have hττ : τ = τ' := by
      ext i
      have := congrFun heq i
      simp only [Function.comp] at this
      rw [h1.injective this]
    rw [hττ]
  · intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    set S := univ.image h with hS
    have hc : S.card = K := by
      rw [hS, card_image_of_injective _ hh, card_univ, Fintype.card_fin]
    set f := S.orderEmbOfFin hc with hf
    have hmem : ∀ i, h i ∈ S := fun i => mem_image_of_mem h (mem_univ i)
    set τf : Fin K → Fin K := fun i => (S.orderIsoOfFin hc).symm ⟨h i, hmem i⟩ with hτf
    have hτinj : Function.Injective τf := by
      intro a b hab
      simp only [hτf] at hab
      have := (S.orderIsoOfFin hc).symm.injective hab
      exact hh (congrArg Subtype.val this)
    have hτbij : Function.Bijective τf := Finite.injective_iff_bijective.1 hτinj
    refine ⟨(f, Equiv.ofBijective τf hτbij), ?_, ?_⟩
    · simp only [mem_product, mem_smSet, mem_univ, and_true]
      exact (S.orderEmbOfFin hc).strictMono
    · funext i
      simp only [Function.comp, Equiv.ofBijective_apply, hτf, hf]
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · intro fτ _
    rfl

end Hankel2
