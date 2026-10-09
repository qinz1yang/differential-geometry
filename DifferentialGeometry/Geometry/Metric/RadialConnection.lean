import DifferentialGeometry.Geometry.Metric.RadialDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Manifold InnerProductSpace Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem leviCivita_const_of_radialBilinearField
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {a' : ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : HasDerivAt a a' ‖x‖) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) (u v : E) :
    let r := ‖x‖
    let α := a' / (a r * r) - 1 / r ^ 2
    let β := (1 - a r * a' / r) / r ^ 2
    let γ := -(2 * α + β) / r ^ 2
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
      ((leviCivitaConnectionOfMetric (I := 𝓘(ℝ, E)) g
        (constantModelVectorField v) x)
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)) =
      α • (⟪x, u⟫_ℝ • v + ⟪x, v⟫_ℝ • u) +
        (β * ⟪u, v⟫_ℝ + γ * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) • x := by
  have hinj : Function.Injective (radialBilinearField a x) := by
    intro y z hyz
    by_contra hne
    have hpos := radialBilinearField_pos hx hane (sub_ne_zero.mpr hne)
    have hzero : radialBilinearField a x (y - z) (y - z) = 0 := by
      have hform : radialBilinearField a x (y - z) = 0 := by
        rw [map_sub, hyz, sub_self]
      rw [hform]
      rfl
    exact (ne_of_gt hpos) hzero
  dsimp only
  apply hinj
  rw [const_flat_eq_nhds g (radialBilinearField a) hg
    (differentiableAt_radialBilinearField ha.differentiableAt hx) u v]
  ext w
  rw [MetricKoszul.koszul_cov_apply]
  rw [fderiv_radialBilinearField_apply ha hx,
    fderiv_radialBilinearField_apply ha hx, fderiv_radialBilinearField_apply ha hx]
  rw [radialBilinearField_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  ring

end DifferentialGeometry.Geometry.Riemannian
