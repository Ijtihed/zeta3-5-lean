import RequestProject.Zeta35.InputDefs

/-!
# Tree bound, step 3: the level penalty as a pair sum (paper N, §5; P, §7)

Port of `RequestProject/Zeta7/Hankel2/LemmaTPenalty.lean` to the nodes `|k| ≤ R`:
`penalty(s) = ∑_{k, m} s_k s_m v_ℓ(k − m)` (`penalty_eq_pairSum`).
-/

open Finset

namespace Zeta35

open Hankel2

/-- `∑_{k, m} s_k s_m v_p(k − m)` over the nodes. -/
noncomputable def pairSum (p n : ℕ) (s : Fin (2 * R n + 1) → ℕ) : ℤ :=
  ∑ i, ∑ i', ((s i * s i' : ℕ) : ℤ) * (padicValInt p (nodeOf n i - nodeOf n i') : ℤ)

theorem sq_sub_sum_sq {ι : Type*} [DecidableEq ι] (A : Finset ι) (s : ι → ℕ) :
    (((∑ i ∈ A, s i : ℕ) : ℤ) ^ 2 - ((∑ i ∈ A, s i ^ 2 : ℕ) : ℤ)) =
      ∑ i ∈ A, ∑ i' ∈ A, if i = i' then 0 else ((s i * s i' : ℕ) : ℤ) := by
  have h : ∀ i ∈ A, (∑ i' ∈ A, if i = i' then 0 else ((s i * s i' : ℕ) : ℤ)) =
      (∑ i' ∈ A, ((s i * s i' : ℕ) : ℤ)) - ((s i ^ 2 : ℕ) : ℤ) := by
    intro i hi
    have : ∀ i' ∈ A, (if i = i' then 0 else ((s i * s i' : ℕ) : ℤ)) =
        ((s i * s i' : ℕ) : ℤ) - if i = i' then ((s i * s i' : ℕ) : ℤ) else 0 := by
      intro i' _; split_ifs <;> simp
    rw [sum_congr rfl this, sum_sub_distrib, sum_ite_eq A i, if_pos hi]
    push_cast; ring
  rw [sum_congr rfl h, sum_sub_distrib]
  push_cast
  rw [sq, sum_mul_sum]

theorem sum_classes {ι : Type*} [Fintype ι] [DecidableEq ι] (cls : ι → ℤ) (N : ℕ)
    (hcls : ∀ i, cls i ∈ (range N).image (fun c : ℕ => (c : ℤ))) (F : ι → ι → ℤ) :
    ∑ c ∈ range N, ∑ i ∈ univ.filter (fun i => cls i = c),
        ∑ i' ∈ univ.filter (fun i => cls i = c), F i i' =
      ∑ i, ∑ i', if cls i = cls i' then F i i' else 0 := by
  have h1 : ∀ c ∈ range N, (∑ i ∈ univ.filter (fun i => cls i = c),
      ∑ i' ∈ univ.filter (fun i => cls i = c), F i i') =
      ∑ i ∈ univ.filter (fun i => cls i = c), ∑ i', if cls i = cls i' then F i i' else 0 := by
    intro c _
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_filter, mem_univ, true_and] at hi
    rw [sum_filter]
    refine sum_congr rfl fun i' _ => ?_
    rw [hi]
    by_cases h : cls i' = c
    · simp [h]
    · simp [h, Ne.symm h]
  rw [sum_congr rfl h1]
  -- regroup the classes
  have h2 := sum_fiberwise_of_maps_to (s := univ) (t := (range N).image (fun c : ℕ => (c : ℤ)))
    (g := cls) (fun i _ => hcls i) (fun i => ∑ i', if cls i = cls i' then F i i' else 0)
  rw [← h2, sum_image (fun a _ b _ h => by exact_mod_cast h)]

theorem count_levels (p : ℕ) [hp : Fact p.Prime] (N : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hdN : d.natAbs ≤ N) :
    ∑ j ∈ Icc 1 (N + 1), (if ((p ^ j : ℕ) : ℤ) ∣ d then (1 : ℤ) else 0) = padicValInt p d := by
  have hv : padicValInt p d ≤ N + 1 := by
    have h1 : ((p ^ padicValInt p d : ℕ) : ℤ) ∣ d := by exact_mod_cast padicValInt_dvd d
    have h2 : p ^ padicValInt p d ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hd)
      (Int.natCast_dvd.1 h1)
    have h3 : N + 1 < p ^ (N + 1) := Nat.lt_pow_self hp.out.one_lt
    by_contra h
    push_neg at h
    have : p ^ (N + 1) ≤ p ^ padicValInt p d := Nat.pow_le_pow_right hp.out.pos h.le
    omega
  rw [sum_boole]
  have : (Icc 1 (N + 1)).filter (fun j => ((p ^ j : ℕ) : ℤ) ∣ d) = Icc 1 (padicValInt p d) := by
    ext j
    simp only [mem_filter, mem_Icc]
    rw [show ((p ^ j : ℕ) : ℤ) = (p : ℤ) ^ j by push_cast; rfl, padicValInt_dvd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3.resolve_left hd⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans hv⟩, Or.inr h2⟩
  rw [this, Nat.card_Icc]
  simp

theorem nodeOf_natAbs_sub_le (n : ℕ) (i i' : Fin (2 * R n + 1)) :
    (nodeOf n i - nodeOf n i').natAbs ≤ 2 * R n := by
  have h1 := i.isLt
  have h2 := i'.isLt
  simp only [nodeOf]
  omega

/-- **The penalty is the pair sum.** -/
theorem penalty_eq_pairSum (p n : ℕ) [hp : Fact p.Prime] (s : Fin (2 * R n + 1) → ℕ) :
    penalty p n s = pairSum p n s := by
  unfold penalty
  simp_rw [sq_sub_sum_sq]
  have hcls : ∀ j, ∀ i : Fin (2 * R n + 1),
      nodeOf n i % ((p ^ j : ℕ) : ℤ) ∈ (range (p ^ j)).image (fun c : ℕ => (c : ℤ)) := by
    intro j i
    have hpos : (0 : ℤ) < ((p ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos j
    simp only [mem_image, mem_range]
    refine ⟨(nodeOf n i % ((p ^ j : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos (nodeOf n i) hpos
      have := Int.emod_nonneg (nodeOf n i) hpos.ne'
      omega
    · exact Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
  rw [sum_congr rfl fun j _ => sum_classes _ _ (hcls j) _]
  rw [sum_comm]
  unfold pairSum
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i' _ => ?_
  by_cases hii : i = i'
  · subst hii; simp
  · have hd : nodeOf n i - nodeOf n i' ≠ 0 := by
      simp only [nodeOf]; intro h; exact hii (Fin.ext (by omega))
    rw [← count_levels p (2 * R n) _ hd (nodeOf_natAbs_sub_le n i i'), mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [if_neg hii]
    have : nodeOf n i % ((p ^ j : ℕ) : ℤ) = nodeOf n i' % ((p ^ j : ℕ) : ℤ) ↔
        ((p ^ j : ℕ) : ℤ) ∣ nodeOf n i - nodeOf n i' := by
      rw [← Int.ModEq, Int.modEq_iff_dvd, ← dvd_neg, neg_sub]
    by_cases h : ((p ^ j : ℕ) : ℤ) ∣ nodeOf n i - nodeOf n i'
    · rw [if_pos (this.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; ring

end Zeta35
