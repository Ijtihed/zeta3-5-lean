module

public import Mathlib

/-!
# The logarithmic derivative of `ζ` near the line `Re s = 1`

* `zetaReg s = (s - 1) ζ(s)`, extended by `1` at `s = 1`, is entire (`differentiable_zetaReg`),
  nonvanishing on `Re s ≥ 1` (`zetaReg_ne_zero`), and `zetaReg'(1) = γ` (`deriv_zetaReg_one`).
* `newmanG z = -(zetaReg'(z+1)/zetaReg(z+1) + 1)/(z+1)` is holomorphic on the open set
  `newmanU ⊇ {Re z ≥ 0}`, equals `L(Λ, z+1)/(z+1) - 1/z` for `Re z > 0` (`newmanG_eq`), and
  `newmanG 0 = -(γ + 1)` (`newmanG_zero`).
-/

@[expose] public section

open Complex Filter Topology Set

namespace PNT

/-- `(s - 1) ζ(s)`, with its limit value `1` at `s = 1`. -/
noncomputable def zetaReg : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

theorem zetaReg_of_ne {s : ℂ} (hs : s ≠ 1) : zetaReg s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem zetaReg_one : zetaReg 1 = 1 := Function.update_self _ _ _

theorem zetaReg_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaReg =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_ne.mem_nhds hs] with w hw using zetaReg_of_ne hw

theorem differentiable_zetaReg : Differentiable ℂ zetaReg := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    refine (DifferentiableAt.differentiableWithinAt ?_)
    refine ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq
      (zetaReg_eventuallyEq hs1)
  · rw [zetaReg, continuousAt_update_same]
    exact riemannZeta_residue_one

theorem zetaReg_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaReg s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [zetaReg_one]; exact one_ne_zero
  · rw [zetaReg_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

theorem deriv_zetaReg_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv zetaReg s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  rw [(zetaReg_eventuallyEq hs).deriv_eq]
  have := ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  have h2 : HasDerivAt (fun w => (w - 1) * riemannZeta w)
      (riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
    convert this using 1; simp
  exact h2.deriv

theorem deriv_zetaReg_one : deriv zetaReg 1 = (Real.eulerMascheroniConstant : ℂ) := by
  have h := (differentiable_zetaReg 1).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine tendsto_nhds_unique h (tendsto_riemannZeta_sub_one_div.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [slope_def_field, zetaReg_of_ne hs1, zetaReg_one]
  field_simp

/-- The holomorphic extension of the Laplace transform in Newman's argument. -/
noncomputable def newmanG (z : ℂ) : ℂ := -(deriv zetaReg (z + 1) / zetaReg (z + 1) + 1) / (z + 1)

/-- Its domain of holomorphy. -/
def newmanU : Set ℂ := {z | z + 1 ≠ 0 ∧ zetaReg (z + 1) ≠ 0}

theorem isOpen_newmanU : IsOpen newmanU := by
  refine IsOpen.inter (isOpen_ne_fun (by fun_prop) continuous_const) ?_
  exact isOpen_ne_fun (differentiable_zetaReg.continuous.comp (by fun_prop)) continuous_const

theorem half_subset_newmanU {z : ℂ} (hz : 0 ≤ z.re) : z ∈ newmanU := by
  refine ⟨fun h => ?_, zetaReg_ne_zero (by simp; linarith)⟩
  have := congrArg re h; simp at this; linarith

theorem differentiableOn_newmanG : DifferentiableOn ℂ newmanG newmanU := by
  have hd : Differentiable ℂ (deriv zetaReg) := by
    have := (differentiable_zetaReg.differentiableOn (s := univ)).deriv isOpen_univ
    exact differentiableOn_univ.mp this
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold newmanG
  refine DifferentiableAt.div ?_ (by fun_prop) hz.1
  refine DifferentiableAt.neg (DifferentiableAt.add ?_ (differentiableAt_const _))
  exact ((hd.comp (by fun_prop : Differentiable ℂ fun z : ℂ => z + 1)) z).div
    ((differentiable_zetaReg.comp (by fun_prop : Differentiable ℂ fun z : ℂ => z + 1)) z) hz.2

theorem newmanG_zero : newmanG 0 = -((Real.eulerMascheroniConstant : ℂ) + 1) := by
  simp [newmanG, deriv_zetaReg_one, zetaReg_one]

theorem newmanG_eq {z : ℂ} (hz : 0 < z.re) :
    newmanG z = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1) / (z + 1) -
      1 / z := by
  have hs : 1 < (z + 1).re := by simp; linarith
  have hs1 : z + 1 ≠ 1 := fun h => by simp at h; rw [h] at hz; simp at hz
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hs0 : z + 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, newmanG, deriv_zetaReg_of_ne hs1,
    zetaReg_of_ne hs1]
  simp only [add_sub_cancel_right]
  field_simp
  ring

end PNT
