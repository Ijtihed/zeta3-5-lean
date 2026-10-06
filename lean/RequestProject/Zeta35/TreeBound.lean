import RequestProject.Zeta35.TreeVdm

/-!
# The tree bound `−v_ℓ(Δ_K) ≤ T_ℓ` (paper N, §5; P, Thm 7.1; W, Thm 3.2; CLAIMS T5)

`tree_bound`: for every prime `ℓ` (in particular every `ℓ ≠ 3`, **including `ℓ = 2`**) and all
`n, K`, `−v_ℓ(Δ_K) ≤ T_ℓ = max_s [∑_k f_ℓ(k, s_k) − penalty(s)]`, for the true Hankel polynomial
`Δ_K = Zeta35.hankelPoly n K` of paper N.  As N remarks, the proof uses only multiplicativity and
ultrametricity of `v_ℓ`.  This is the port of `Hankel2.Fam3.lemmaT`
(`RequestProject/Zeta7/Hankel2/LemmaT.lean`) to the local constants and nodes of N.

Proof: by the double Cauchy–Binet expansion (`hankelPoly_eq_sum`),
`Δ_K = ∑_{f,g} det E[:, f] · det C[f, g] · det E[:, g]`; for a term with `det C[f,g] ≠ 0` the node
profiles agree, and the bounds of `TreeBlock`, `TreeVdm`, `TreePenalty` combine with
`e_ℓ(u, s_u, ℓ_u) + ℓ_u λ_ℓ(u) ≤ f_ℓ(u, s_u)` (`eP_add_le_fP`).
-/

open Polynomial Finset Matrix

namespace Zeta35

open Hankel2

variable {n K : ℕ}

theorem ellR_le (R : Finset (Fin 4)) : Fam3.ellR R ≤ R.card * (4 - R.card) := by
  revert R; decide

theorem eP_add_le_fP (p n : ℕ) (k : ℤ) {s : ℕ} (hs : s ≠ 0) (ℓ : ℕ) :
    eP p n k s ℓ + (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ) ≤ fP p n k s := by
  rw [fP, if_neg hs]
  by_cases hℓ : ℓ ≤ s * (4 - s)
  · exact le_sup (f := fun ℓ => eP p n k s ℓ + (((ℓ * lambdaP p n k : ℕ) : ℤ) : WithBot ℤ))
      (mem_range.2 (Nat.lt_succ_of_le hℓ))
  · have : eP p n k s ℓ = ⊥ := by
      rw [eP, Finset.sup_eq_bot_iff]
      intro R hR
      simp only [mem_filter, mem_univ, true_and] at hR
      have := ellR_le R
      rw [hR.1, hR.2] at this
      exact absurd this hℓ
    rw [this, WithBot.bot_add]; exact bot_le

theorem ellCol_eq_zero_of_not_mem {f : Fin K → Idx n} {u : Fin (2 * R n + 1)}
    (hu : u ∉ univ.image (nodeF f)) : ellCol f u = 0 := by
  have : univ.filter (fun c => nodeF f c = u) = ∅ := by
    ext c; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h; exact hu (mem_image.2 ⟨c, mem_univ _, h⟩)
  simp [ellCol, this]

theorem prof_ne_zero_of_mem {f : Fin K → Idx n} {u : Fin (2 * R n + 1)}
    (hu : u ∈ univ.image (nodeF f)) : prof f u ≠ 0 := by
  obtain ⟨c, _, hc⟩ := mem_image.1 hu
  rw [prof, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨c, by simp [hc]⟩

theorem prof_eq_zero_of_not_mem {f : Fin K → Idx n} {u : Fin (2 * R n + 1)}
    (hu : u ∉ univ.image (nodeF f)) : prof f u = 0 := by
  rw [prof, card_eq_zero]
  ext c; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h; exact hu (mem_image.2 ⟨c, mem_univ _, h⟩)

/-- One term of the double Cauchy–Binet expansion. -/
theorem nv_term_le (p : ℕ) [Fact p.Prime] {f g : Fin K → Idx n} (hf : StrictMono f)
    (hg : StrictMono g) :
    nv p (C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
      C ((Emat n K).submatrix id g).det) ≤ TP p n K := by
  by_cases hpr : prof f = prof g
  swap
  · rw [det_cbl_eq_zero_of_prof_ne hpr, mul_zero, zero_mul, nv_zero]; exact bot_le
  have hfg := nodeF_eq_of_prof_eq hf hg hpr
  set s := prof f with hs
  -- the three factors
  have h1 : nv p (C ((Emat n K).submatrix id f).det) ≤ Zf p f := nv_C_le (norm_det_Emat_le p f)
  have h3 : nv p (C ((Emat n K).submatrix id g).det) ≤ Zf p g := nv_C_le (norm_det_Emat_le p g)
  have h2 := nv_det_cbl_le p hf hg hfg
  set S := ∑ u ∈ univ.image (nodeF f), eP p n (nodeOf n u) (prof f u) (ellCol f u + ellCol g u)
  -- the exponent identity
  have hZ : Zf p f + Zf p g =
      ∑ u, (lam p n u : ℤ) * ((ellCol f u : ℤ) + (ellCol g u : ℤ)) - penalty p n s := by
    have e1 := two_Zf p hf
    have e2 := two_Zf p hg
    rw [← hs] at e1
    rw [← hpr] at e2
    rw [penalty_eq_pairSum]
    have : ∑ u, (lam p n u : ℤ) * ((ellCol f u : ℤ) + (ellCol g u : ℤ)) =
        ∑ u, (lam p n u : ℤ) * (ellCol f u : ℤ) + ∑ u, (lam p n u : ℤ) * (ellCol g u : ℤ) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun u _ => by ring
    rw [this]
    linarith
  -- restrict the `λ ℓ` sum to the occupied nodes
  have hsum : ∑ u, (lam p n u : ℤ) * ((ellCol f u : ℤ) + (ellCol g u : ℤ)) =
      ∑ u ∈ univ.image (nodeF f), (lam p n u : ℤ) * ((ellCol f u : ℤ) + (ellCol g u : ℤ)) := by
    symm
    refine sum_subset (subset_univ _) fun u _ hu => ?_
    have hu' : u ∉ univ.image (nodeF g) := by rwa [← hfg]
    rw [ellCol_eq_zero_of_not_mem hu, ellCol_eq_zero_of_not_mem hu']; simp
  -- the `f_p` sum
  have hfP : ∑ u ∈ univ.image (nodeF f),
      (eP p n (nodeOf n u) (prof f u) (ellCol f u + ellCol g u) +
        ((((ellCol f u + ellCol g u) * lambdaP p n (nodeOf n u) : ℕ) : ℤ) : WithBot ℤ)) ≤
      ∑ u, fP p n (nodeOf n u) (s u) := by
    rw [← sum_subset (subset_univ (univ.image (nodeF f))) (fun u _ hu => by
      rw [hs, prof_eq_zero_of_not_mem hu, fP, if_pos rfl])]
    exact sum_le_sum fun u hu => eP_add_le_fP p n _ (prof_ne_zero_of_mem hu) _
  rw [sum_add_distrib] at hfP
  have hTP : (∑ u, fP p n (nodeOf n u) (s u)) + ((-penalty p n s : ℤ) : WithBot ℤ) ≤ TP p n K :=
    le_sup (f := fun s => (∑ i, fP p n (nodeOf n i) (s i)) + ((-penalty p n s : ℤ) : WithBot ℤ))
      (prof_mem_profiles hf)
  have hcast : (∑ u ∈ univ.image (nodeF f),
      ((((ellCol f u + ellCol g u) * lambdaP p n (nodeOf n u) : ℕ) : ℤ) : WithBot ℤ)) =
      (((Zf p f + Zf p g + penalty p n s : ℤ)) : WithBot ℤ) := by
    rw [← WithBot.coe_sum, hZ, hsum, sub_add_cancel]
    congr 1
    push_cast
    refine sum_congr rfl fun u _ => ?_
    rw [lam]; ring
  rw [hcast] at hfP
  calc nv p (C ((Emat n K).submatrix id f).det * ((Cbl n).submatrix f g).det *
        C ((Emat n K).submatrix id g).det)
      ≤ (Zf p f : WithBot ℤ) + S + (Zf p g : WithBot ℤ) :=
        (nv_mul_le _ _).trans (add_le_add ((nv_mul_le _ _).trans (add_le_add h1 h2)) h3)
    _ = S + (((Zf p f + Zf p g + penalty p n s : ℤ)) : WithBot ℤ) +
          ((-penalty p n s : ℤ) : WithBot ℤ) := by
        rw [add_assoc S, ← WithBot.coe_add, show Zf p f + Zf p g + penalty p n s + -penalty p n s =
          Zf p f + Zf p g by ring, WithBot.coe_add]
        abel
    _ ≤ (∑ u, fP p n (nodeOf n u) (s u)) + ((-penalty p n s : ℤ) : WithBot ℤ) :=
        add_le_add hfP le_rfl
    _ ≤ TP p n K := hTP

/-- **The tree bound** (N, §5; P, Thm 7.1; W, Thm 3.2), for every prime `ℓ`. -/
theorem tree_bound (n K p : ℕ) (hp : p.Prime) :
    negTop (gaussVal p (hankelPoly n K)) ≤ TP p n K := by
  haveI := Fact.mk hp
  change nv p (hankelPoly n K) ≤ TP p n K
  rw [hankelPoly_eq_sum]
  refine (nv_sum_le _ _).trans (Finset.sup_le fun f hf => ?_)
  refine (nv_sum_le _ _).trans (Finset.sup_le fun g hg => ?_)
  exact nv_term_le p (mem_smSet.1 hf) (mem_smSet.1 hg)

end Zeta35
