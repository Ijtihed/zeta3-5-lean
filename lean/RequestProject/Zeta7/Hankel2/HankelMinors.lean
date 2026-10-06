import Mathlib

/-!
# Minors of the local Hankel blocks (for paper Theorem 7.1)

For `c : ℕ → R` with `c m = 0` for `m ≥ 4`, the local block is `C = [c_{a+b}]_{a,b ≤ 3}`.
Every minor `det C[f, g]` (rows `f`, columns `g`, both strictly increasing) is a sum of minors
`det C[R, {0, …, s−1}]` with `ℓ(R) = ℓ(f) + ℓ(g)`, where `ℓ(f) = ∑ f − C(s, 2)`
(`hminor_reduce`).  This is the finite-dimensional case of the Littlewood–Richardson
expansion used implicitly in paper Proposition 5.1.  It is checked here case by case
(all 70 pairs).
-/

open Matrix Finset

namespace Hankel2

variable {R : Type*} [CommRing R]

/-- The minor `det [c_{f i + g j}]`. -/
def hminor (c : ℕ → R) {s : ℕ} (f g : Fin s → Fin 4) : R :=
  (Matrix.of fun i j => c ((f i : ℕ) + (g j : ℕ))).det

/-- `ℓ(f) = ∑ f − C(s, 2)`. -/
def ellF {s : ℕ} (f : Fin s → Fin 4) : ℕ := (∑ i, (f i : ℕ)) - s.choose 2

/-- The standard columns `{0, …, s−1}`. -/
def stdCols {s : ℕ} (hs : s ≤ 4) : Fin s → Fin 4 := Fin.castLE hs

theorem card_le_four_of_strictMono {s : ℕ} {f : Fin s → Fin 4} (hf : StrictMono f) : s ≤ 4 := by
  simpa using Fintype.card_le_of_injective f hf.injective

theorem sm_cases1 {f : Fin 1 → Fin 4} (hf : StrictMono f) :
    f = ![0] ∨ f = ![1] ∨ f = ![2] ∨ f = ![3] := by
  have e : f = ![f 0] := by funext i; fin_cases i <;> rfl
  rw [e]
  generalize f 0 = a0 at *
  fin_cases a0 <;> simp_all <;> decide

theorem sm_cases2 {f : Fin 2 → Fin 4} (hf : StrictMono f) :
    f = ![0, 1] ∨ f = ![0, 2] ∨ f = ![0, 3] ∨ f = ![1, 2] ∨ f = ![1, 3] ∨ f = ![2, 3] := by
  have e : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have h0 : f 0 < f 1 := hf (by decide)
  rw [e]
  generalize f 0 = a0 at *
  generalize f 1 = a1 at *
  fin_cases a0 <;> fin_cases a1 <;> simp_all <;> decide

theorem sm_cases3 {f : Fin 3 → Fin 4} (hf : StrictMono f) :
    f = ![0, 1, 2] ∨ f = ![0, 1, 3] ∨ f = ![0, 2, 3] ∨ f = ![1, 2, 3] := by
  have e : f = ![f 0, f 1, f 2] := by funext i; fin_cases i <;> rfl
  have h0 : f 0 < f 1 := hf (by decide)
  have h1 : f 1 < f 2 := hf (by decide)
  rw [e]
  generalize f 0 = a0 at *
  generalize f 1 = a1 at *
  generalize f 2 = a2 at *
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> simp_all <;> decide

theorem hminor_reduce (c : ℕ → R) (hc : ∀ m, 4 ≤ m → c m = 0) {s : ℕ} (f g : Fin s → Fin 4)
    (hf : StrictMono f) (hg : StrictMono g) :
    ∃ L : List (Fin s → Fin 4), (∀ Rw ∈ L, StrictMono Rw ∧ ellF Rw = ellF f + ellF g) ∧
      hminor c f g = (L.map fun Rw => hminor c Rw (stdCols (card_le_four_of_strictMono hf))).sum := by
  have hs := card_le_four_of_strictMono hf
  have c4 := hc 4 le_rfl
  have c5 := hc 5 (by norm_num)
  have c6 := hc 6 (by norm_num)
  interval_cases s
  · refine ⟨[f], ?_, ?_⟩
    · intro Rw hR; simp at hR; subst hR; exact ⟨hf, by simp [ellF]⟩
    · simp [hminor, Subsingleton.elim f (stdCols hs)]
  · rcases sm_cases1 hf with rfl | rfl | rfl | rfl <;>
    rcases sm_cases1 hg with rfl | rfl | rfl | rfl
    · refine ⟨[![0]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
  · rcases sm_cases2 hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases sm_cases2 hg with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨[![0, 1]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 3], ![1, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
  · rcases sm_cases3 hf with rfl | rfl | rfl | rfl <;>
    rcases sm_cases3 hg with rfl | rfl | rfl | rfl
    · refine ⟨[![0, 1, 2]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 1, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![0, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[![1, 2, 3]], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
    · refine ⟨[], by decide, ?_⟩
      simp [hminor, stdCols, Matrix.det_fin_two, Matrix.det_fin_three, c4, c5, c6]
      try ring
  · have key : ∀ f : Fin 4 → Fin 4, StrictMono f → f = stdCols hs := by
      intro f hf
      have h0 : (f 0 : ℕ) < f 1 := hf (by decide)
      have h1 : (f 1 : ℕ) < f 2 := hf (by decide)
      have h2 : (f 2 : ℕ) < f 3 := hf (by decide)
      have h3 := (f 3).isLt
      funext i; fin_cases i <;> (apply Fin.ext; simp [stdCols]; omega)
    obtain rfl := key g hg
    obtain rfl := key f hf
    refine ⟨[stdCols hs], ?_, by simp⟩
    intro Rw hR
    simp only [List.mem_singleton] at hR
    subst hR
    refine ⟨hf, ?_⟩
    simp [ellF, stdCols, Fin.sum_univ_four, Nat.choose]

end Hankel2
