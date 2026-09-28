import DifferentialGeometry.Geometry.Metric.ConeChart.Connection
import DifferentialGeometry.Geometry.Curvature.Metric.ConcurrentField
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
open Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Multilinear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem metricRm04_coneEuler_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ h y.2) (hr : z.1 ≠ 0)
    (u v w : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    metricRm04At g z (vec4 u v (coneEulerField z) w) = 0 := by
  let R : ContMDiffSection 𝓘(ℝ, ℝ × V) (ℝ × V) ∞
      (TangentSpace 𝓘(ℝ, ℝ × V) : (ℝ × V) → Type _) :=
    ⟨coneEulerField, coneEulerField_contMDiff⟩
  apply metricRm04_concurrent_eq_zero g R _ u v w
  have hrnear : ∀ᶠ y : ℝ × V in 𝓝 z, y.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually_ne hr
  filter_upwards [eventually_eventually_nhds.mpr hmetric, hh, hrnear] with y hgy hhy hry
  intro a
  exact leviCivita_coneEuler_of_coneForm g hgy hhy hry a

theorem metricRm04_coneRadial_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ h y.2) (hr : z.1 ≠ 0)
    (u v w : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    metricRm04At g z (vec4 u v (constantModelVectorField (1, 0) z) w) = 0 := by
  have hz := metricRm04_coneEuler_eq_zero g hmetric hh hr u v w
  have hmul : metricRm04At g z (vec4 u v (coneEulerField z) w) =
      z.1 * metricRm04At g z (vec4 u v (constantModelVectorField (1, 0) z) w) := by
    have hupdate (a : TangentSpace 𝓘(ℝ, ℝ × V) z) :
        Function.update (vec4 u v (constantModelVectorField (1, 0) z) w) (2 : Fin 4) a =
          vec4 u v a w := by
      funext i
      fin_cases i <;> rfl
    have h := (metricRm04At g z).map_update_smul
      (vec4 u v (constantModelVectorField (1, 0) z) w) (2 : Fin 4) z.1
        (constantModelVectorField (1, 0) z)
    rw [hupdate, hupdate] at h
    exact h
  rw [hmul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hr

end DifferentialGeometry.Geometry.Riemannian
