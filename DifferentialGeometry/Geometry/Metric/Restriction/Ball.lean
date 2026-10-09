import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianBallOf_eq_image_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [T2Space U]
    (hU : IsClosed (U : Set M)) (x : U) (r : ℝ) :
    riemannianBallOf g x.val r =
      Subtype.val '' riemannianBallOf (g.restrictOpen U) x r := by
  ext y
  constructor
  · intro hy
    have hycomp : y ∈ connectedComponent x.val :=
      Geometry.Metric.edistOf_ball_subset_connCompOpen g x.val r hy
    have hyU : y ∈ U :=
      (show IsClopen (U : Set M) from ⟨hU, U.isOpen⟩).connectedComponent_subset x.property hycomp
    refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    change riemannianEDistOf (g.restrictOpen U) x ⟨y, hyU⟩ < ENNReal.ofReal r
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
    exact hy
  · rintro ⟨z, hz, rfl⟩
    change riemannianEDistOf g x.val z.val < ENNReal.ofReal r
    rw [← riemannianEDistOf_restrictOpen_of_isClosed g U hU x z]
    exact hz

end DifferentialGeometry
