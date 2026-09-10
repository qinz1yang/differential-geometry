import DifferentialGeometry.Geometry.Boundary.EmbeddingFrontier
import DifferentialGeometry.Topology.Manifold.ParametrizationDerivative

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [HasSmoothBoundary E H I] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M] [BoundarylessManifold J M]

theorem isPreconnected_interior_target_of_smooth_parametrization [PreconnectedSpace P]
    (e : PartialEquiv P M) (hes : e.source = univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsPreconnected (interior e.target) := by
  obtain ⟨hemb, hinj⟩ :=
    Poincare.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv e hes he hei
  have hrange : range e = e.target := by
    rw [← image_univ, ← hes, e.image_source_eq_target]
  rw [← hrange]
  exact isPreconnected_interior_range_of_fullRank_embedding e he hemb hinj hdim

theorem closure_interior_target_of_smooth_parametrization [CompactSpace P] [T2Space M]
    (e : PartialEquiv P M) (hes : e.source = univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    closure (interior e.target) = e.target := by
  obtain ⟨hemb, hinj⟩ :=
    Poincare.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv e hes he hei
  have hrange : range e = e.target := by
    rw [← image_univ, ← hes, e.image_source_eq_target]
  rw [← hrange]
  exact closure_interior_range_of_fullRank_closedEmbedding e he
    (he.continuous.isClosedEmbedding hemb.injective) hinj hdim

end Poincare.Geometry.Boundary
