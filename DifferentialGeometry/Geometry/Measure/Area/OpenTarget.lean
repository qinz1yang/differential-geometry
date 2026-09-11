import DifferentialGeometry.Geometry.Measure.Area.Manifold
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype








open Bundle Manifold DifferentialGeometry
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem riemannianAreaDensity_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : ℂ → U) (z : ℂ) :
    riemannianAreaDensity (g.restrictOpen U) u z =
      riemannianAreaDensity g (Subtype.val ∘ u) z := by
  unfold riemannianAreaDensity
  rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp]
  rfl



theorem riemannianArea_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : ℂ → U) (s : Set ℂ) :
    riemannianArea (g.restrictOpen U) u s = riemannianArea g (Subtype.val ∘ u) s := by
  unfold riemannianArea
  congr 1
  funext z
  exact riemannianAreaDensity_restrictOpen g U u z



theorem riemannianDiskArea_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (u : DifferentialGeometry.Topology.closedDisk → U) :
    riemannianDiskArea (g.restrictOpen U) u = riemannianDiskArea g (Subtype.val ∘ u) :=
  riemannianArea_restrictOpen g U (diskExtension u) _

end DifferentialGeometry.Geometry
