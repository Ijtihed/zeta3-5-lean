import RequestProject.Zeta7.Hankel2.LemmaTFactor
import RequestProject.Zeta7.Hankel2.LemmaTNv
import RequestProject.Zeta7.Hankel2.HankelMinors

/-!
# Minors of the block-diagonal matrix `C` (for paper Theorem 7.1)

For strictly monotone `f, g : Fin K → ι` (`ι = Fin (3n+1) ×ₗ Fin 4`), with node profiles
`s_u(f) = #{c : node(f c) = u}` (`prof`):

* `det C[f, g] = 0` unless `s(f) = s(g)` (`det_cbl_eq_zero_of_prof_ne`);
* if `s(f) = s(g)` the node maps agree (`nodeF_eq_of_prof_eq`), the minor factors over the nodes
  (block-triangular determinant), and each factor is a local minor `det C_u[F_u, G_u]`, whence
  `−v_p(det C[f, g]) ≤ ∑_u e_p(u, s_u, ℓ_u(f) + ℓ_u(g))` (`nv_det_cbl_le`), with
  `ℓ_u(f) = ∑_{node(f c) = u} b_c − C(s_u, 2)` (`ellCol`).
-/

open Polynomial Finset Matrix

namespace Hankel2.Fam3

variable {n K : ℕ}

/-- The node of the column `f c`. -/
def nodeF (f : Fin K → Idx n) (c : Fin K) : Fin (3 * n + 1) := (ofLex (f c)).1

/-- The Taylor order of the column `f c`. -/
def ordF (f : Fin K → Idx n) (c : Fin K) : Fin 4 := (ofLex (f c)).2

/-- The node profile `s_u(f) = #{c : node(f c) = u}`. -/
def prof (f : Fin K → Idx n) (u : Fin (3 * n + 1)) : ℕ := (univ.filter fun c => nodeF f c = u).card

/-- `ℓ_u(f) = ∑_{node(f c) = u} b_c − C(s_u, 2)`. -/
def ellCol (f : Fin K → Idx n) (u : Fin (3 * n + 1)) : ℕ :=
  (∑ c ∈ univ.filter (fun c => nodeF f c = u), (ordF f c : ℕ)) - (prof f u).choose 2

theorem nodeF_mono {f : Fin K → Idx n} (hf : StrictMono f) : Monotone (nodeF f) :=
  fun _ _ h => Prod.Lex.monotone_fst _ _ (hf.monotone h)

theorem sum_prof (f : Fin K → Idx n) : ∑ u, prof f u = K := by
  have := card_eq_sum_card_fiberwise (f := nodeF f) (s := univ) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))
  simpa [prof] using this.symm

theorem det_cbl_eq_zero_of_prof_ne {f g : Fin K → Idx n} (h : prof f ≠ prof g) :
    ((Cbl n).submatrix f g).det = 0 := by
  rw [det_apply]
  refine sum_eq_zero fun σ _ => ?_
  by_contra hne
  have hall : ∀ i, nodeF f (σ i) = nodeF g i := by
    intro i
    by_contra hi
    apply hne
    rw [Finset.prod_eq_zero (mem_univ i) (by simp [Cbl, nodeF] at hi ⊢; simp [hi])]
    simp
  apply h
  have hle : ∀ u, prof g u ≤ prof f u := by
    intro u
    refine card_le_card_of_injOn σ (fun i hi => ?_) (σ.injective.injOn)
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    rw [hall]; exact hi
  funext u
  have := (Finset.sum_eq_sum_iff_of_le (s := univ) (fun u _ => hle u)).1
    (by rw [sum_prof, sum_prof])
  exact (this u (mem_univ _)).symm

theorem mono_le_iff {α : Type*} [LinearOrder α] {h : Fin K → α} (hm : Monotone h) (c : Fin K)
    (u : α) : h c ≤ u ↔ (c : ℕ) < (univ.filter fun c' => h c' ≤ u).card := by
  constructor
  · intro hc
    have hs : Iic c ⊆ univ.filter fun c' => h c' ≤ u := fun c' hc' => by
      simp only [mem_Iic] at hc'
      simp only [mem_filter, mem_univ, true_and]
      exact (hm hc').trans hc
    have := card_le_card hs
    rw [Fin.card_Iic] at this
    omega
  · intro hc
    by_contra hcu
    push_neg at hcu
    have hs : (univ.filter fun c' => h c' ≤ u) ⊆ Iio c := fun c' hc' => by
      simp only [mem_filter, mem_univ, true_and] at hc'
      simp only [mem_Iio]
      by_contra hh
      push_neg at hh
      exact absurd (hc'.trans_lt hcu) (not_lt.2 (hm hh))
    have := card_le_card hs
    rw [Fin.card_Iio] at this
    omega

theorem card_le_eq_sum_prof (f : Fin K → Idx n) (u : Fin (3 * n + 1)) :
    (univ.filter fun c => nodeF f c ≤ u).card = ∑ u' ∈ Iic u, prof f u' := by
  rw [card_eq_sum_card_fiberwise (f := nodeF f) (t := Iic u)
    (fun c hc => by simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc; simpa using hc)]
  refine sum_congr rfl fun u' hu' => ?_
  rw [prof, filter_filter]
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ mem_Iic.1 hu', h⟩

theorem nodeF_eq_of_prof_eq {f g : Fin K → Idx n} (hf : StrictMono f) (hg : StrictMono g)
    (h : prof f = prof g) : nodeF f = nodeF g := by
  have key : ∀ u, (univ.filter fun c => nodeF f c ≤ u).card =
      (univ.filter fun c => nodeF g c ≤ u).card := by
    intro u; rw [card_le_eq_sum_prof, card_le_eq_sum_prof, h]
  funext c
  apply le_antisymm
  · rw [mono_le_iff (nodeF_mono hf), key, ← mono_le_iff (nodeF_mono hg)]
  · rw [mono_le_iff (nodeF_mono hg), ← key, ← mono_le_iff (nodeF_mono hf)]

theorem toLex_nodeF_ordF (f : Fin K → Idx n) (c : Fin K) : toLex (nodeF f c, ordF f c) = f c := rfl

theorem prof_le_four {f : Fin K → Idx n} (hf : StrictMono f) (u : Fin (3 * n + 1)) :
    prof f u ≤ 4 := by
  have := card_le_card_of_injOn (s := univ.filter fun c => nodeF f c = u)
    (t := (univ : Finset (Fin 4))) (ordF f)
    (fun _ _ => mem_coe.2 (mem_univ _)) (by
      intro c hc c' hc' hcc
      simp at hc hc'
      apply hf.injective
      rw [← toLex_nodeF_ordF f c, ← toLex_nodeF_ordF f c', hc, hc', hcc])
  simpa [prof] using this

theorem prof_mem_profiles {f : Fin K → Idx n} (hf : StrictMono f) : prof f ∈ profiles n K := by
  simp only [profiles, mem_filter, Fintype.mem_piFinset, mem_range]
  exact ⟨fun u => Nat.lt_succ_of_le (prof_le_four hf u), sum_prof f⟩

/-! ### The block factorisation -/

theorem strictMono_le_apply {s : ℕ} {F : Fin s → ℕ} (hF : StrictMono F) (i : Fin s) :
    (i : ℕ) ≤ F i := by
  have hsub : (Iic i).image F ⊆ range (F i + 1) := fun x hx => by
    simp only [mem_image, mem_Iic] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact mem_range.2 (Nat.lt_succ_of_le (hF.monotone hj))
  have := card_le_card hsub
  rw [card_image_of_injective _ hF.injective, Fin.card_Iic, card_range] at this
  omega

theorem choose_two_le_sum {s : ℕ} {F : Fin s → Fin 4} (hF : StrictMono F) :
    s.choose 2 ≤ ∑ i, (F i : ℕ) := by
  have h1 : ∑ i : Fin s, (i : ℕ) = s.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) s, Finset.sum_range_id, Nat.choose_two_right]
  rw [← h1]
  exact sum_le_sum fun i _ => strictMono_le_apply (F := fun i => (F i : ℕ))
    (fun a b hab => by simpa using hF hab) i

/-- The rows of the block of node `u`, in increasing order. -/
noncomputable def blockEquiv (f : Fin K → Idx n) (u : Fin (3 * n + 1)) :
    Fin (prof f u) ≃o {c // nodeF f c = u} :=
  Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_subtype]; rfl)

theorem ordF_block_strictMono {f : Fin K → Idx n} (hf : StrictMono f) (u : Fin (3 * n + 1)) :
    StrictMono fun r => ordF f (blockEquiv f u r) := by
  intro r r' hr
  have h1 : (blockEquiv f u r : Fin K) < blockEquiv f u r' := (blockEquiv f u).strictMono hr
  have h2 := hf h1
  rw [Prod.Lex.lt_iff] at h2
  have e1 := (blockEquiv f u r).2
  have e2 := (blockEquiv f u r').2
  simp only [nodeF] at e1 e2
  rcases h2 with h2 | h2
  · exact absurd (lt_of_lt_of_eq (lt_of_eq_of_lt e1.symm h2) e2) (lt_irrefl u)
  · exact h2.2

theorem sum_ordF_block (f : Fin K → Idx n) (u : Fin (3 * n + 1)) :
    ∑ r, (ordF f (blockEquiv f u r) : ℕ) =
      ∑ c ∈ univ.filter (fun c => nodeF f c = u), (ordF f c : ℕ) := by
  rw [Fintype.sum_equiv (blockEquiv f u).toEquiv (fun r => (ordF f (blockEquiv f u r) : ℕ))
    (fun c => (ordF f c : ℕ)) (fun r => rfl)]
  exact (Finset.sum_subtype (univ.filter fun c => nodeF f c = u) (fun x => by simp)
    (fun c => (ordF f c : ℕ))).symm

theorem ellF_block (f : Fin K → Idx n) (u : Fin (3 * n + 1)) :
    ellF (fun r => ordF f (blockEquiv f u r)) = ellCol f u := by
  rw [ellF, ellCol, sum_ordF_block]

theorem sum_ordF_eq {f : Fin K → Idx n} (hf : StrictMono f) (u : Fin (3 * n + 1)) :
    ∑ c ∈ univ.filter (fun c => nodeF f c = u), (ordF f c : ℕ) =
      ellCol f u + (prof f u).choose 2 := by
  have := choose_two_le_sum (ordF_block_strictMono hf u)
  rw [sum_ordF_block] at this
  rw [ellCol]; omega

/-- The block of node `u` is a local minor `det C_u[F_u, G_u]`. -/
theorem det_block_eq {f g : Fin K → Idx n} (hfg : nodeF f = nodeF g) (u : Fin (3 * n + 1)) :
    (((Cbl n).submatrix f g).toSquareBlock (nodeF f) u).det =
      hminor (cPoly n (nodeOf n u)) (fun r => ordF f (blockEquiv f u r))
        (fun r => ordF g (blockEquiv f u r)) := by
  rw [← det_submatrix_equiv_self (blockEquiv f u).toEquiv, hminor]
  congr 1
  refine Matrix.ext fun r r' => ?_
  have e1 := (blockEquiv f u r).2
  have e2 := (blockEquiv f u r').2
  have e2' : nodeF g (blockEquiv f u r') = u := by rw [← hfg]; exact e2
  change Cbl n (f (blockEquiv f u r)) (g (blockEquiv f u r')) = _
  simp only [Cbl]
  simp only [nodeF] at e1 e2'
  split_ifs with h
  · simp only [of_apply, ordF]
    exact congrArg (fun k => cPoly n (nodeOf n k) _) e1
  · exact absurd (e1.trans e2'.symm) h

/-- `det C_u[R, {0..s−1}]` as a `minorR`. -/
theorem hminor_std_eq_minorR (k : ℤ) {s : ℕ} (Rw : Fin s → Fin 4) (hR : StrictMono Rw)
    (hs : s ≤ 4) :
    hminor (cPoly n k) Rw (stdCols hs) = minorR n k (univ.image Rw) := by
  have hc : (univ.image Rw).card = s := by
    rw [card_image_of_injective _ hR.injective, card_univ, Fintype.card_fin]
  have hRw : Rw = fun i => (univ.image Rw).orderEmbOfFin hc i :=
    orderEmbOfFin_unique hc (fun i => mem_image_of_mem _ (mem_univ i)) hR
  generalize univ.image Rw = R at hc hRw
  subst hc
  rw [hRw]
  rfl

theorem ellR_image {s : ℕ} (Rw : Fin s → Fin 4) (hR : StrictMono Rw) :
    ellR (univ.image Rw) = ellF Rw := by
  rw [ellR, ellF, sum_image (fun a _ b _ h => hR.injective h),
    card_image_of_injective _ hR.injective, card_univ, Fintype.card_fin]

theorem nv_list_sum_le {p : ℕ} [Fact p.Prime] {α : Type*} (L : List α) (φ : α → ℚ[X]) (B : WithBot ℤ)
    (h : ∀ x ∈ L, nv p (φ x) ≤ B) : nv p (L.map φ).sum ≤ B := by
  induction L with
  | nil => simp [nv_zero]
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons]
    exact (nv_add_le _ _).trans (max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx])))

theorem nv_hminor_le (p : ℕ) [Fact p.Prime] (k : ℤ) {s : ℕ} {F G : Fin s → Fin 4} (hF : StrictMono F)
    (hG : StrictMono G) :
    nv p (hminor (cPoly n k) F G) ≤ eP p n k s (ellF F + ellF G) := by
  obtain ⟨L, hL, heq⟩ := hminor_reduce (cPoly n k) (fun m hm => cPoly_eq_zero hm) F G hF hG
  rw [heq]
  refine nv_list_sum_le L _ _ fun Rw hRw => ?_
  obtain ⟨hR, hell⟩ := hL Rw hRw
  rw [hminor_std_eq_minorR k Rw hR]
  refine le_sup (f := fun R => negTop (gaussVal p (minorR n k R))) ?_
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨?_, by rw [ellR_image Rw hR, hell]⟩
  rw [card_image_of_injective _ hR.injective, card_univ, Fintype.card_fin]

/-- **The block bound**: `−v_p(det C[f,g]) ≤ ∑_u e_p(u, s_u, ℓ_u(f) + ℓ_u(g))`. -/
theorem nv_det_cbl_le (p : ℕ) [Fact p.Prime] {f g : Fin K → Idx n} (hf : StrictMono f) (hg : StrictMono g)
    (hfg : nodeF f = nodeF g) :
    nv p ((Cbl n).submatrix f g).det ≤ ∑ u ∈ univ.image (nodeF f),
      eP p n (nodeOf n u) (prof f u) (ellCol f u + ellCol g u) := by
  have hbt : ((Cbl n).submatrix f g).BlockTriangular (nodeF f) := by
    intro c d hcd
    simp only [submatrix_apply, Cbl]
    rw [if_neg]
    intro h
    have h' : nodeF f c = nodeF g d := h
    rw [← hfg] at h'
    exact absurd h' (ne_of_gt hcd)
  rw [hbt.det]
  refine (nv_prod_le _ _).trans (sum_le_sum fun u _ => ?_)
  rw [det_block_eq hfg u]
  have hG : StrictMono fun r => ordF g (blockEquiv f u r) := by
    intro r r' hr
    have h1 : (blockEquiv f u r : Fin K) < blockEquiv f u r' := (blockEquiv f u).strictMono hr
    have h2 := hg h1
    rw [Prod.Lex.lt_iff] at h2
    have e1 : nodeF g (blockEquiv f u r) = u := by rw [← hfg]; exact (blockEquiv f u r).2
    have e2 : nodeF g (blockEquiv f u r') = u := by rw [← hfg]; exact (blockEquiv f u r').2
    simp only [nodeF] at e1 e2
    rcases h2 with h2 | h2
    · exact absurd (lt_of_lt_of_eq (lt_of_eq_of_lt e1.symm h2) e2) (lt_irrefl u)
    · exact h2.2
  refine (nv_hminor_le p (nodeOf n u) (ordF_block_strictMono hf u) hG).trans (le_of_eq ?_)
  congr 2
  rw [ellF_block]
  congr 1
  -- the `g`-side: the block of `g` is the same set of rows
  have hsum : ∑ r, (ordF g (blockEquiv f u r) : ℕ) =
      ∑ c ∈ univ.filter (fun c => nodeF g c = u), (ordF g c : ℕ) := by
    rw [Fintype.sum_equiv (blockEquiv f u).toEquiv (fun r => (ordF g (blockEquiv f u r) : ℕ))
      (fun c => (ordF g c : ℕ)) (fun r => rfl)]
    exact (Finset.sum_subtype (univ.filter fun c => nodeF g c = u) (fun x => by simp [hfg])
      (fun c => (ordF g c : ℕ))).symm
  have hprof : prof f u = prof g u := by
    simp only [prof, hfg]
  rw [ellF, ellCol, hsum, hprof]

end Hankel2.Fam3
