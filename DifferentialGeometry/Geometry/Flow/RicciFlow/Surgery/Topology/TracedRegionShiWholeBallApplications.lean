import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility

/-!
# Consumers of A11b

* The WBD03 norm: A11b for the bundled norm `curvatureDerivativeNorm`, through
  `curvatureDerivativeNorm_eq_curvDerivNorm`.
* A parabolically `Rm`-controlled ball of radius `2s` (`isParabolicallyRmControlledBall`) is the
  traced region `isTracedRegion t p (2s) (4 s²) (s⁻²/4)`, so A11b applies with `τ = 4`, `C₀ = 1/4`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

/-- A11b for the bundled curvature derivative norm (the norm of the WBD03 statements). -/
theorem curvatureDerivativeNorm_le_whole_ball_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {τ s C₀ : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hC₀ : 0 < C₀)
    (htr : H.isTracedRegion t p (2 * s) (τ * s ^ 2) (C₀ / s ^ 2)) (m : ℕ) :
    ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p s,
      curvatureDerivativeNorm (H.stageMetric (H.activeStage t) t) m q ≤
        shiLocalUniformBound 3 m (C₀ * τ / 2)
            (Real.sqrt C₀ / (8 * Real.exp ((3 : ℝ) ^ 2 * (C₀ * τ / 2)))) *
          C₀ / Real.sqrt (τ / 2) ^ m / s ^ (m + 2) := by
  intro q hq
  rw [curvatureDerivativeNorm_eq_curvDerivNorm]
  exact A11b_shi_whole_ball_of_isTracedRegion H t p hτ hs hC₀ htr m q hq

/-- A parabolically `Rm`-controlled ball of radius `2s` gives the whole-ball Shi bound on
`B(p, s)`: A11b with `τ = 4` and `C₀ = 1/4`. -/
theorem shi_whole_ball_of_isParabolicallyRmControlledBall (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {s : ℝ} (hs : 0 < s)
    (hball : H.isParabolicallyRmControlledBall t p (2 * s)) (m : ℕ) :
    ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p s,
      curvDerivNorm m (H.stageMetric (H.activeStage t) t) q ≤
        shiLocalUniformBound 3 m (1 / 4 * 4 / 2)
            (Real.sqrt (1 / 4) / (8 * Real.exp ((3 : ℝ) ^ 2 * (1 / 4 * 4 / 2)))) *
          (1 / 4) / Real.sqrt (4 / 2) ^ m / s ^ (m + 2) := by
  have htr := (H.isParabolicallyRmControlledBall_iff_isTracedRegion t p (2 * s)).mp hball
  have e1 : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
  have e2 : ((2 * s) ^ 2)⁻¹ = 1 / 4 / s ^ 2 := by
    field_simp
    ring
  rw [e2, e1] at htr
  exact A11b_shi_whole_ball_of_isTracedRegion H t p (by norm_num) hs (by norm_num) htr m

end FILL910
