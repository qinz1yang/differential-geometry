import DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false

/-!
# Polarization for pointwise Riemannian metrics

This file records the small fiberwise polarization step used by local-isometry
arguments: a real-linear map that preserves the metric quadratic form
preserves the full metric inner product.
-/

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M']

/-- A continuous linear map between tangent fibers that preserves every
metric square preserves the full pointwise metric. -/
theorem inner_eq_of_diag
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric I' M')
    (x : M) (x' : M')
    (A : TangentSpace I x →L[ℝ] TangentSpace I' x')
    (hdiag : ∀ u, g'.inner x' (A u) (A u) = g.inner x u u)
    (u v : TangentSpace I x) :
    g'.inner x' (A u) (A v) = g.inner x u v := by
  have hleft :
      g'.inner x' (A (u + v)) (A (u + v)) =
        g'.inner x' (A u) (A u) +
          2 * g'.inner x' (A u) (A v) +
            g'.inner x' (A v) (A v) := by
    rw [map_add, map_add, map_add, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.add_apply, g'.symm x' (A v) (A u)]
    ring
  have hright :
      g.inner x (u + v) (u + v) =
        g.inner x u u + 2 * g.inner x u v + g.inner x v v := by
    rw [(g.inner x).map_add u v, ContinuousLinearMap.add_apply,
      (g.inner x u).map_add u v, (g.inner x v).map_add u v,
      g.symm x v u]
    ring
  have huv := hdiag (u + v)
  rw [hleft, hright, hdiag u, hdiag v] at huv
  linarith

end Riemannian
end Geometry
end DifferentialGeometry
