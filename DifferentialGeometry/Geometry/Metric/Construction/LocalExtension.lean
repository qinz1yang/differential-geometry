import DifferentialGeometry.Geometry.Metric.Construction.OpenExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

set_option autoImplicit false
noncomputable section
open TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem model_metric_nonempty :
    Nonempty (SmoothRiemannianMetric 𝓘(ℝ, E) E) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  obtain ⟨g⟩ := DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric
    (I := 𝓘(ℝ, F)) (M := F)
  exact ⟨Diffeomorph.pullbackMetricCross g (toEuclidean (E := E)).toDiffeomorph⟩

theorem exists_model_metric_extension (U : Opens E)
    (gU : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∃ V : Opens E, ∃ hVU : V ≤ U,
        (x : E) ∈ V ∧ ∀ y : V, ∀ v w : E,
          g.inner (y : E) v w = gU.inner (Opens.inclusion hVU y) v w := by
  obtain ⟨R⟩ := model_metric_nonempty (E := E)
  obtain ⟨g, V, hxV, hVU, heq, _⟩ :=
    DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_closed
      R U gU (K := {(x : E)}) isClosed_singleton
      (Set.singleton_subset_iff.mpr x.2)
  refine ⟨g, V, hVU, hxV (Set.mem_singleton _), ?_⟩
  intro y v w
  exact heq y y.2 v w

end DifferentialGeometry.Geometry.Riemannian
