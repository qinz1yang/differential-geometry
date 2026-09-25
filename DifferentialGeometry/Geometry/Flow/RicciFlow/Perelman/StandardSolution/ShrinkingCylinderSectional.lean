import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderSectional
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

theorem metricRm04_restricted_shrinkingCylinder_horizontal_lower_bound_of_small_metric_derivatives
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U) (x : U)
    {ε : ℝ} (hε : ε ≤ 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      ((shrinkingCylinderMetric (E := E) t).restrictOpen U)
      ((shrinkingCylinderMetric (E := E) t).restrictOpen U) x ≤ ε)
    (u v : TangentSpace (𝓡 2) x.val.1) :
    (1 / 16 : ℝ) * (g.inner x (u, 0) (u, 0) * g.inner x (v, 0) (v, 0) -
      (g.inner x (u, 0) (v, 0)) ^ 2) ≤
      metricRm04StandardAt g x (u, 0) (v, 0) (v, 0) (u, 0) := by
  have ha : 0 < 2 * (1 - t) := by linarith
  have hmetric : shrinkingCylinderMetric (E := E) t =
      cylinderMetric (DifferentialGeometry.scaleMetric (2 * (1 - t)) ha
        (Geometry.roundMetric (E := E) (n := 2))) := shrinkingCylinderMetric_eq_prod ht1
  exact metricRm04_restricted_scaled_roundCylinder_horizontal_lower_bound_of_small_metric_derivatives
    (2 * (1 - t)) ha (by linarith) U g x hε (by simpa only [hmetric] using hsmall) u v

theorem metricRm04_shrinkingCylinder_horizontal_lower_bound_of_small_metric_derivatives
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ))
    (x : Metric.sphere (0 : E) 1 × ℝ) {ε : ℝ} (hε : ε ≤ 1 / 1000)
    (hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m g
      (shrinkingCylinderMetric (E := E) t) (shrinkingCylinderMetric (E := E) t) x ≤ ε)
    (u v : TangentSpace (𝓡 2) x.1) :
    (1 / 16 : ℝ) * (g.inner x (u, 0) (u, 0) * g.inner x (v, 0) (v, 0) -
      (g.inner x (u, 0) (v, 0)) ^ 2) ≤
      metricRm04StandardAt g x (u, 0) (v, 0) (v, 0) (u, 0) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 2
  change EuclideanSpace ℝ (Fin 2) at u v
  let U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ) := ⊤
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) U.isOpen)
  let y : U := ⟨x, trivial⟩
  have hh := metricRm04_restricted_shrinkingCylinder_horizontal_lower_bound_of_small_metric_derivatives
    ht0 ht1 U (g.restrictOpen U) y hε (by
      intro m hm
      rw [metricDerivNorm_restrictOpen]
      exact hsmall m hm) u v
  have hRm := metricRm04StandardAt_restrictOpen g U y (u, 0) (v, 0) (v, 0) (u, 0)
  erw [DifferentialGeometry.mfderiv_subtype_val (I := (𝓡 2).prod 𝓘(ℝ))] at hRm
  rw [hRm] at hh
  exact hh

end DifferentialGeometry.PDE.RicciFlow
