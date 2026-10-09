import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetricSmooth
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone

/-!
# CM5.b at `n = ∞`: the smooth hinge comparison as a special case

Smooth regression of the finite-metric hinge comparison CM5.b
(`comparisonAngle_le_arccos_inner_finite`). A smooth metric is the case `r = ⊤` of a
`C^{r+1}` metric; the nonnegative sectional cone condition of the smooth API gives `sec ≥ 0` in the
finite-order sense (`sectionalCurvature_nonneg_of_mem_cone`, through B7's
`sectionalCurvature_eq_smooth`), and CM-H's bridge `expMap_smul_eq_intrinsicGeodesic` identifies the
ported rays with the smooth API's complete geodesics. Hence the statement of the tree's smooth
`complete_triangle_angle` (Toponogov/CompleteShortening.lean) follows from CM5.b
(`complete_triangle_angle_of_finite`), without the hypothesis `[ConnectedSpace M]` of the smooth
proof. Lane CM-A2, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.FiniteComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- The nonnegative sectional cone condition of the smooth API gives `sec ≥ 0` in the
finite-order sense. -/
theorem sectionalCurvature_nonneg_of_mem_cone
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hsec : ∀ y : M, DifferentialGeometry.Geometry.Curvature.metricRm04At g y ∈
      DifferentialGeometry.tensor04SectionalNonnegativeCone)
    (y : M) (w₁ w₂ : TangentSpace I y) :
    0 ≤ Bundle.ContMDiffRiemannianMetric.sectionalCurvature g y w₁ w₂ := by
  rw [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth,
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
  exact div_nonneg
    ((DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      g y).mp (hsec y) w₁ w₂)
    (DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_nonneg g y w₁ w₂)

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Smooth regression of CM5.b.** The conclusion of the smooth `complete_triangle_angle`, derived
from the finite-metric hinge comparison at `r = ⊤` (no `ConnectedSpace` needed). -/
theorem complete_triangle_angle_of_finite
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g)
    (hsec : ∀ y : M, DifferentialGeometry.Geometry.Curvature.metricRm04At g y ∈
      DifferentialGeometry.tensor04SectionalNonnegativeCone)
    (o : M) (u v : TangentSpace I o) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a)).toReal = a)
    (hminB : (riemannianEDist I o (intrinsicGeodesic g hEnorm o v b)).toReal = b) :
    comparisonAngle (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a)).toReal
      (riemannianEDist I o (intrinsicGeodesic g hEnorm o v b)).toReal
      (riemannianEDist I (intrinsicGeodesic g hEnorm o u a)
        (intrinsicGeodesic g hEnorm o v b)).toReal ≤ Real.arccos (g.inner o u v) := by
  have hd (x y : M) : (riemannianEDist I x y).toReal = dist x y := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hA := Bundle.ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic g hEnorm o u a
  have hB := Bundle.ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic g hEnorm o v b
  rw [hd, hd, hd] at *
  rw [hminA, hminB, ← hA, ← hB]
  rw [← hA] at hminA
  rw [← hB] at hminB
  exact comparisonAngle_le_arccos_inner_finite (r := ⊤) g le_top hEnorm o u v ha hb hu hv
    hminA hminB (sectionalCurvature_nonneg_of_mem_cone g hsec)

end DifferentialGeometry.Geometry.FiniteComparison
