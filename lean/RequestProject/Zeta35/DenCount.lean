import RequestProject.Zeta35.DenPsi

/-!
# Denominators (N, Theorem 5.1), step 6: counting the class types of a prime `ℓ ∈ (n/20, 9n/2]`

For an odd prime `ℓ = 2H + 1`, `n` even (`2R = 3n`) and `q` with `qℓ ≤ 3n ≤ (q + 1)ℓ`, the residue
classes mod `ℓ` are indexed by `t ∈ [−H, H]`.  With `e = ⌊q/2⌋` and `w = R − eℓ`:

* the class of `t` has at most `q + [cN(t)]` nodes (one more for `t = 0` in the boundary case
  `q` odd, `w = ℓ`), where `cN(t) = (|t| ≤ w)` for `q` even and `cN(t) = (ℓ − w ≤ |t|)` for `q` odd;
* it contains an `hs`-free node (`3|k| ≤ ℓ`) whenever `cB(t) = (3|t| ≤ ℓ)`.

The four counts `#{t : cN(t) = x, cB(t) = y}` are within `2` of `n · meas_i(u)`, `u = ℓ/n`, where
`meas_i` are the class-type measures of the circle model (`measF`).  Hence (**`sum_psi_le`**)

  `∑_{c mod ℓ} ψ(N_c, b_c, λ) ≤ ∑_{i < 4} (n · meas_i(u) + 2) ψ(N_i, b_i, λ) + ψ(q + 2, 0, λ)`

for `λ ≥ 0`, with the types `(N_i, b_i) = (q+1, 1), (q+1, 0), (q, 1), (q, 0)`.
-/

open Finset

namespace Zeta35.Den

/-! ### The circle-model measures -/

/-- The measures of the four class types `(q+1, 1), (q+1, 0), (q, 1), (q, 0)` at `u`, on the
branch `br` (`r = 3 − qu`; `br` says `r ≥ 2u/3` for `q` even and `r ≥ u/3` for `q` odd). -/
def measF {α : Type*} [Field α] (q : ℕ) (br : Bool) (u : α) : Fin 4 → α :=
  if q % 2 = 0 then
    (if br then ![2 / 3 * u, 3 - q * u - 2 / 3 * u, 0, u - (3 - q * u)]
      else ![3 - q * u, 0, 2 / 3 * u - (3 - q * u), u / 3])
  else
    (if br then ![3 - q * u - u / 3, u / 3, u - (3 - q * u), 0]
      else ![0, 3 - q * u, 2 / 3 * u, u / 3 - (3 - q * u)])

/-- The branch function: `r − 2u/3` (`q` even) or `r − u/3` (`q` odd). -/
def sgnF {α : Type*} [Field α] (q : ℕ) (u : α) : α :=
  if q % 2 = 0 then 3 - (q + 2 / 3) * u else 3 - (q + 1 / 3) * u

/-- The class sizes of the four types. -/
def typN (q : ℕ) (i : Fin 4) : ℕ := if i.val < 2 then q + 1 else q

/-- The `hs`-free counts of the four types. -/
def typB (i : Fin 4) : ℕ := if i.val % 2 = 0 then 1 else 0

/-- `3n · meas_i(ℓ/n)` as an integer. -/
def Mint (q : ℕ) (br : Bool) (n ℓ : ℤ) : Fin 4 → ℤ :=
  if q % 2 = 0 then
    (if br then ![2 * ℓ, 9 * n - 3 * (q * ℓ) - 2 * ℓ, 0, 3 * ℓ - 9 * n + 3 * (q * ℓ)]
      else ![9 * n - 3 * (q * ℓ), 0, 2 * ℓ - 9 * n + 3 * (q * ℓ), ℓ])
  else
    (if br then ![9 * n - 3 * (q * ℓ) - ℓ, ℓ, 3 * ℓ - 9 * n + 3 * (q * ℓ), 0]
      else ![0, 9 * n - 3 * (q * ℓ), 2 * ℓ, ℓ - 9 * n + 3 * (q * ℓ)])

theorem measF_eq_Mint (q : ℕ) (br : Bool) {n ℓ : ℕ} (hn : 0 < n) (i : Fin 4) :
    (n : ℝ) * measF q br ((ℓ : ℝ) / n) i = (Mint q br n ℓ i : ℝ) / 3 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold measF Mint
  split_ifs <;> fin_cases i <;> simp <;> field_simp <;> ring

theorem sgnF_mul (q : ℕ) {n ℓ : ℕ} (hn : 0 < n) :
    3 * (n : ℝ) * sgnF q ((ℓ : ℝ) / n) =
      if q % 2 = 0 then 9 * (n : ℝ) - 3 * (q * ℓ) - 2 * ℓ else 9 * (n : ℝ) - 3 * (q * ℓ) - ℓ := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold sgnF
  split_ifs <;> field_simp <;> ring

/-! ### Residues in a symmetric window -/

theorem emod_window {ℓ t : ℤ} (h1 : -ℓ ≤ t) (h2 : t < ℓ) :
    t % ℓ = if 0 ≤ t then t else t + ℓ := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h h2
  · rw [Int.emod_eq_add_self_emod]; exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Reindexing the residues mod `ℓ = 2H + 1` by the window `[−H, H]`. -/
theorem sum_range_eq_window {M : Type*} [AddCommMonoid M] {ℓ H : ℕ} (hℓ : ℓ = 2 * H + 1)
    (F : ℕ → M) :
    ∑ t ∈ Icc (-(H : ℤ)) H, F ((t % (ℓ : ℤ)).toNat) = ∑ c ∈ range ℓ, F c := by
  refine sum_nbij' (fun t => (t % (ℓ : ℤ)).toNat) (fun c => if c ≤ H then (c : ℤ) else c - ℓ)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_Icc] at ht
    simp only [mem_range]
    rw [emod_window (ℓ := ℓ) (t := t) (by omega) (by omega)]
    split_ifs <;> omega
  · intro c hc
    simp only [mem_range] at hc
    simp only [mem_Icc]
    split_ifs <;> omega
  · intro t ht
    simp only [mem_Icc] at ht
    simp only
    rw [emod_window (ℓ := ℓ) (t := t) (by omega) (by omega)]
    split_ifs <;> omega
  · intro c hc
    simp only [mem_range] at hc
    simp only
    split_ifs with h
    · rw [emod_window (ℓ := ℓ) (t := c) (by omega) (by omega)]; split_ifs <;> omega
    · rw [emod_window (ℓ := ℓ) (t := c - ℓ) (by omega) (by omega)]; split_ifs <;> omega
  · intro t _; rfl

/-! ### Class sizes -/

/-- The class of `t` in `[−R, R]` has at most `2e + 1 − [w < t] − [t < −w] + [t ≤ w − ℓ] +
[ℓ − w ≤ t]` elements, when `R = eℓ + w`, `0 ≤ w ≤ ℓ`, `|t| ≤ H`, `ℓ = 2H + 1`. -/
theorem card_class_le {ℓ H R e w t : ℤ} (hℓ : ℓ = 2 * H + 1) (hH : 0 ≤ H) (he : 0 ≤ e) (hR : R = e * ℓ + w)
    (hw0 : 0 ≤ w) (hwl : w ≤ ℓ) (ht1 : -H ≤ t) (ht2 : t ≤ H) :
    ((#{m ∈ Icc (-R) R | m % ℓ = t % ℓ} : ℕ) : ℤ) ≤
      2 * e + 1 - (if w < t then 1 else 0) - (if t < -w then 1 else 0) +
        (if t ≤ w - ℓ then 1 else 0) + (if ℓ - w ≤ t then 1 else 0) := by
  set jhi : ℤ := e + (if t ≤ w - ℓ then 1 else 0) - (if w < t then 1 else 0)
  set jlo : ℤ := -e - (if ℓ - w ≤ t then 1 else 0) + (if t < -w then 1 else 0)
  have hsub : {m ∈ Icc (-R) R | m % ℓ = t % ℓ} ⊆ (Icc jlo jhi).image (fun j => t + ℓ * j) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmod⟩ := hm
    obtain ⟨j, hj⟩ : ℓ ∣ m - t := Int.ModEq.dvd (show Int.ModEq ℓ t m from hmod.symm)
    refine mem_image.2 ⟨j, mem_Icc.2 ⟨?_, ?_⟩, by linarith⟩
    · -- lower bound on `j`: `−R ≤ t + ℓ j`
      have key : ℓ * (j + e) ≥ -w - t := by nlinarith
      have h2 : ∀ d : ℤ, d ≤ -2 → ℓ * d ≤ -2 * ℓ := fun d hd => by nlinarith
      have h1 : ∀ d : ℤ, d = -1 → ℓ * d = -ℓ := fun d hd => by subst hd; ring
      have h0 : ∀ d : ℤ, d = 0 → ℓ * d = 0 := fun d hd => by subst hd; ring
      have := h2 (j + e); have := h1 (j + e); have := h0 (j + e)
      simp only [jlo]
      split_ifs <;> omega
    · have key : ℓ * (j - e) ≤ w - t := by nlinarith
      have h2 : ∀ d : ℤ, 2 ≤ d → 2 * ℓ ≤ ℓ * d := fun d hd => by nlinarith
      have h1 : ∀ d : ℤ, d = 1 → ℓ * d = ℓ := fun d hd => by subst hd; ring
      have h0 : ∀ d : ℤ, d = 0 → ℓ * d = 0 := fun d hd => by subst hd; ring
      have := h2 (j - e); have := h1 (j - e); have := h0 (j - e)
      simp only [jhi]
      split_ifs <;> omega
  have hc := (card_le_card hsub).trans card_image_le
  rw [Int.card_Icc] at hc
  have : ((#{m ∈ Icc (-R) R | m % ℓ = t % ℓ} : ℕ) : ℤ) ≤ ((jhi + 1 - jlo).toNat : ℤ) := by
    exact_mod_cast hc
  simp only [jhi, jlo] at this
  split_ifs at this ⊢ <;> omega

/-! ### Counting symmetric interval conditions -/

theorem card_filter_abs (H : ℤ) (hH : 0 ≤ H) (P : ℤ → Prop) [DecidablePred P] :
    ((#{t ∈ Icc (-H) H | P |t|} : ℕ) : ℤ) = (if P 0 then 1 else 0) + 2 * #{a ∈ Icc 1 H | P a} := by
  have hsplit : Icc (-H) H = Icc (-H) (-1) ∪ insert 0 (Icc 1 H) := by
    ext x; simp only [mem_Icc, mem_union, mem_insert]; omega
  have hdisj : Disjoint (Icc (-H) (-1)) (insert 0 (Icc 1 H)) := by
    rw [disjoint_left]; intro x hx hx'
    simp only [mem_Icc, mem_insert] at hx hx'; omega
  have hneg : #{t ∈ Icc (-H) (-1) | P |t|} = #{a ∈ Icc 1 H | P a} := by
    refine card_nbij' (fun t => -t) (fun a => -a) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ht ⊢
      rw [abs_of_neg (by omega)] at ht
      exact ⟨⟨by omega, by omega⟩, ht.2⟩
    · intro a ha
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha ⊢
      rw [abs_neg, abs_of_pos (by omega)]
      exact ⟨⟨by omega, by omega⟩, ha.2⟩
    · intro t _; simp
    · intro a _; simp
  have hpos : {t ∈ Icc 1 H | P |t|} = {a ∈ Icc 1 H | P a} :=
    filter_congr fun x hx => by rw [abs_of_pos (by simp only [mem_Icc] at hx; omega)]
  rw [hsplit, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj), filter_insert,
    hneg, hpos]
  simp only [abs_zero]
  split_ifs with hP
  · rw [card_insert_of_notMem (by simp)]; push_cast; ring
  · push_cast; ring

theorem card_filter_interval (H L U : ℤ) (P : ℤ → Prop) [DecidablePred P]
    (hP : ∀ a, 1 ≤ a → a ≤ H → (P a ↔ L ≤ a ∧ a ≤ U)) :
    ((#{a ∈ Icc 1 H | P a} : ℕ) : ℤ) = max 0 (min H U - max 1 L + 1) := by
  have e : {a ∈ Icc 1 H | P a} = Icc (max 1 L) (min H U) := by
    ext a
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := (hP a h1 h2).1 h3
      omega
    · intro h
      have h1 : 1 ≤ a := by omega
      have h2 : a ≤ H := by omega
      exact ⟨⟨h1, h2⟩, (hP a h1 h2).2 ⟨by omega, by omega⟩⟩
  rw [e, Int.card_Icc]
  omega

/-! ### The four type counts -/

/-- `cN(a)` for `a = |t|`: the class of `t` has `q + 1` (rather than `q`) nodes. -/
def cNP (q : ℕ) (ℓ w a : ℤ) : Prop := (q % 2 = 0 ∧ a ≤ w) ∨ (q % 2 = 1 ∧ ℓ - w ≤ a)

instance (q : ℕ) (ℓ w a : ℤ) : Decidable (cNP q ℓ w a) := by unfold cNP; infer_instance

/-- The condition for the type `i` at `a = |t|`. -/
def typP (q : ℕ) (ℓ w : ℤ) (i : Fin 4) (a : ℤ) : Prop :=
  (cNP q ℓ w a ↔ i.val < 2) ∧ (3 * a ≤ ℓ ↔ i.val % 2 = 0)

instance (q : ℕ) (ℓ w : ℤ) (i : Fin 4) (a : ℤ) : Decidable (typP q ℓ w i a) := by
  unfold typP; infer_instance

/-- **The type counts**: `3 #{t : type i} ≤ 3n · meas_i + 6`. -/
theorem count_bound {n ℓ H q e : ℕ} {w : ℤ} (br : Bool) (hℓ : ℓ = 2 * H + 1) (hn : Even n)
    (he : e = q / 2) (hw : w = (R n : ℤ) - e * ℓ) (hq1 : q * ℓ ≤ 3 * n) (hq2 : 3 * n ≤ (q + 1) * ℓ)
    (hbr1 : br = true → 0 ≤ (if q % 2 = 0 then 9 * (n : ℤ) - 3 * (q * ℓ) - 2 * ℓ
      else 9 * (n : ℤ) - 3 * (q * ℓ) - ℓ))
    (hbr2 : br = false → (if q % 2 = 0 then 9 * (n : ℤ) - 3 * (q * ℓ) - 2 * ℓ
      else 9 * (n : ℤ) - 3 * (q * ℓ) - ℓ) ≤ 0) (i : Fin 4) :
    3 * ((#{t ∈ Icc (-(H : ℤ)) H | typP q ℓ w i |t|} : ℕ) : ℤ) ≤ Mint q br n ℓ i + 6 := by
  have hR : 2 * R n = 3 * n := R_of_even hn
  have hq1' : (q : ℤ) * ℓ ≤ 3 * n := by exact_mod_cast hq1
  have hq2' : 3 * (n : ℤ) ≤ q * ℓ + ℓ := by
    have : ((3 * n : ℕ) : ℤ) ≤ (((q + 1) * ℓ : ℕ) : ℤ) := by exact_mod_cast hq2
    push_cast at this; linarith
  have hR' : 2 * (R n : ℤ) = 3 * n := by exact_mod_cast hR
  have hℓ' : (ℓ : ℤ) = 2 * H + 1 := by exact_mod_cast hℓ
  rw [card_filter_abs _ (by positivity)]
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · -- `q` even
    have hQ : (q : ℤ) * ℓ = 2 * ((e : ℤ) * ℓ) := by
      have : (q : ℤ) = 2 * e := by omega
      rw [this]; ring
    simp only [hq, if_true] at hbr1 hbr2
    have hP : ∀ (L U : ℤ), (∀ a : ℤ, 1 ≤ a → a ≤ H → (typP q ℓ w i a ↔ L ≤ a ∧ a ≤ U)) →
        ((#{a ∈ Icc 1 (H : ℤ) | typP q ℓ w i a} : ℕ) : ℤ) = max 0 (min (H : ℤ) U - max 1 L + 1) :=
      fun L U h => card_filter_interval _ L U _ h
    fin_cases i
    · rw [hP 1 (min w (ℓ / 3)) (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, if_true]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> (try split_ifs) <;> omega
    · rw [hP (ℓ / 3 + 1) w (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, if_true]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> omega
    · rw [hP (w + 1) (ℓ / 3) (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, if_true]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> (try split_ifs) <;> omega
    · rw [hP (max (w + 1) (ℓ / 3 + 1)) H (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, if_true]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> omega
  · -- `q` odd
    have hQ : (q : ℤ) * ℓ = 2 * ((e : ℤ) * ℓ) + ℓ := by
      have : (q : ℤ) = 2 * e + 1 := by omega
      rw [this]; ring
    simp only [hq, one_ne_zero, if_false] at hbr1 hbr2
    have hP : ∀ (L U : ℤ), (∀ a : ℤ, 1 ≤ a → a ≤ H → (typP q ℓ w i a ↔ L ≤ a ∧ a ≤ U)) →
        ((#{a ∈ Icc 1 (H : ℤ) | typP q ℓ w i a} : ℕ) : ℤ) = max 0 (min (H : ℤ) U - max 1 L + 1) :=
      fun L U h => card_filter_interval _ L U _ h
    fin_cases i
    · rw [hP (ℓ - w) (ℓ / 3) (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, one_ne_zero, if_false]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> (try split_ifs) <;> omega
    · rw [hP (max (ℓ - w) (ℓ / 3 + 1)) H (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, one_ne_zero, if_false]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> omega
    · rw [hP 1 (min (ℓ - w - 1) (ℓ / 3)) (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, one_ne_zero, if_false]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> (try split_ifs) <;> omega
    · rw [hP (ℓ / 3 + 1) (ℓ - w - 1) (fun a h1 h2 => by simp [typP, cNP, hq]; omega)]
      simp only [Mint, hq, one_ne_zero, if_false]
      cases br <;> simp [typP, cNP, hq] at hbr1 hbr2 ⊢ <;> omega

end Zeta35.Den
