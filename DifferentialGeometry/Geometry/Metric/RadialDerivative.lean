import DifferentialGeometry.Geometry.Metric.RadialField
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section

open scoped InnerProductSpace ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasFDerivAt_norm_of_ne {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert h using 1
  · funext y
    simp only [Real.sqrt_sq (norm_nonneg y)]
  · ext u
    simp only [smul_apply, smul_eq_mul,
      Real.sqrt_sq (norm_nonneg x)]
    field_simp
    simp [mul_comm]

theorem differentiableAt_radialBilinearField {a : ℝ → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a ‖x‖) (hx : x ≠ 0) :
    DifferentiableAt ℝ (radialBilinearField a) x := by
  have hn := (hasFDerivAt_norm_of_ne hx).differentiableAt
  have he : DifferentiableAt ℝ (NormedSpace.normalize : E → E) x :=
    (hn.inv (norm_ne_zero_iff.mpr hx)).smul differentiableAt_id
  have hc : DifferentiableAt ℝ (fun y : E => (a ‖y‖ / ‖y‖) ^ 2) x := by
    convert ((ha.comp x hn).mul (hn.inv (norm_ne_zero_iff.mpr hx))).pow 2 using 1 <;> rfl
  exact (contDiff_radialBilinearForm (n := 1)).contDiffAt.differentiableAt one_ne_zero |>.comp x
    (he.prodMk hc)

theorem fderiv_radialBilinearField_apply {a : ℝ → ℝ} {a' : ℝ} {x : E}
    (ha : HasDerivAt a a' ‖x‖) (hx : x ≠ 0) (u v w : E) :
    let r := ‖x‖
    let c := (a r / r) ^ 2
    let dc := 2 * (a r / r) * ((a' * r - a r) / r ^ 2)
    let d := (1 - c) / r ^ 2
    let dd := -dc / r ^ 2 - 2 * (1 - c) / r ^ 3
    fderiv ℝ (radialBilinearField a) x u v w =
      dc / r * ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ +
        dd / r * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ +
        d * (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ) := by
  let c : ℝ → ℝ := fun r => (a r / r) ^ 2
  let d : ℝ → ℝ := fun r => (1 - c r) / r ^ 2
  let dc := 2 * (a ‖x‖ / ‖x‖) * ((a' * ‖x‖ - a ‖x‖) / ‖x‖ ^ 2)
  let dd := -dc / ‖x‖ ^ 2 - 2 * (1 - c ‖x‖) / ‖x‖ ^ 3
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc : HasDerivAt c dc ‖x‖ := by
    convert (ha.div (hasDerivAt_id ‖x‖) hn).pow 2 using 1 <;>
      first | rfl | simp [dc]
  have hd : HasDerivAt d dd ‖x‖ := by
    have hsub : HasDerivAt (fun r => 1 - c r) (-dc) ‖x‖ := hc.const_sub 1
    have h := hsub.div
      ((hasDerivAt_id ‖x‖).pow 2) (pow_ne_zero 2 hn)
    convert h using 1 <;> first | rfl | (dsimp [dd]; field_simp)
  have hnorm := hasFDerivAt_norm_of_ne hx
  have hcNorm := hc.comp_hasFDerivAt x hnorm
  have hdNorm := hd.comp_hasFDerivAt x hnorm
  have hv : HasFDerivAt (fun y : E => ⟪y, v⟫_ℝ) (innerSL ℝ v) x := by
    convert (innerSL ℝ v).hasFDerivAt (x := x) using 1
    funext y
    exact real_inner_comm v y
  have hw : HasFDerivAt (fun y : E => ⟪y, w⟫_ℝ) (innerSL ℝ w) x := by
    convert (innerSL ℝ w).hasFDerivAt (x := x) using 1
    funext y
    exact real_inner_comm w y
  have hEval := (hcNorm.mul_const ⟪v, w⟫_ℝ).add ((hdNorm.mul hv).mul hw)
  have heq : (fun y : E => radialBilinearField a y v w) =
      (fun y : E => c ‖y‖ * ⟪v, w⟫_ℝ + d ‖y‖ * ⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ) := by
    funext y
    rw [radialBilinearField_apply]
    dsimp [c, d]
    ring
  change HasFDerivAt
    (fun y : E => c ‖y‖ * ⟪v, w⟫_ℝ + d ‖y‖ * ⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ) _ x at hEval
  rw [← heq] at hEval
  have hB := (differentiableAt_radialBilinearField ha.differentiableAt hx).hasFDerivAt
  have hBv := hB.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v x)
  have hBvw := hBv.clm_apply (hasFDerivAt_const (𝕜 := ℝ) w x)
  have heval := congrArg (fun L : E →L[ℝ] ℝ => L u) hBvw.fderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, map_zero, zero_add] at heval
  dsimp only
  rw [← heval, hEval.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply, Function.comp_apply]
  dsimp [dc, dd, d, c]
  rw [real_inner_comm v u, real_inner_comm w u]
  ring

end DifferentialGeometry.Geometry.Riemannian
