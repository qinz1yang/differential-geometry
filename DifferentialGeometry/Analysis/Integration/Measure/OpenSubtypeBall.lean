import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Set Manifold
open scoped Manifold ContDiff ENNReal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (x : U) (r : ℝ) :
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    riemannianVolumeMeasure I U (g.restrictOpen U)
        (riemannianBallOf (g.restrictOpen U) x r) =
      riemannianVolumeMeasure I M g (riemannianBallOf g x.val r) := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hpre : riemannianBallOf (g.restrictOpen U) x r =
      Subtype.val ⁻¹' riemannianBallOf g x.val r := by
    ext y
    change riemannianEDistOf (g.restrictOpen U) x y < ENNReal.ofReal r ↔
      riemannianEDistOf g x.val y.val < ENNReal.ofReal r
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
  have hball : MeasurableSet (riemannianBallOf g x.val r) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g x.val)
      continuous_const).measurableSet
  have hsub : riemannianBallOf g x.val r ⊆ U := by
    rw [riemannianBallOf_eq_image_restrictOpen_of_isClosed g U hU x r]
    rintro y ⟨z,_,rfl⟩
    exact z.property
  rw [hpre]
  exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    g U hball hsub

end DifferentialGeometry.Integral.Measure
