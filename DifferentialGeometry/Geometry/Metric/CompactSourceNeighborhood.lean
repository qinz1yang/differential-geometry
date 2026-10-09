import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Topology.MetricSpace.Thickening

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_uniform_local_source_metric_bound_near_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : F → M} {U K : Set F}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (η : ℝ) (C : ℝ≥0), 0 < η ∧ ∀ p ∈ K,
      closedBall p η ⊆ U ∧
      (∀ x ∈ closedBall p η, ∀ y ∈ closedBall p η,
        riemannianEDistOf g (r x) (r y) ≤ (C : ℝ≥0∞) * edist x y) ∧
      ∀ x ∈ closedBall p η, ∀ v : F,
        Real.sqrt (g.inner (r x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r x v)
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) r x v)) ≤ C * ‖v‖ := by
  obtain ⟨η, hη, hηU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hcompact : IsCompact (cthickening η K) := hK.cthickening
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hr hcompact hηU
  refine ⟨η, C, hη, ?_⟩
  intro p hp
  have hball : closedBall p η ⊆ cthickening η K :=
    fun x hx => mem_cthickening_of_dist_le x p η K hp hx
  have hballU := hball.trans hηU
  refine ⟨hballU, ?_, fun x hx => hC x (hball hx)⟩
  intro x hx y hy
  exact riemannian_edist_le_on_convex_source g hU hr hballU (convex_closedBall p η)
    (fun z hz => hC z (hball hz)) hx hy

end DifferentialGeometry.Geometry

end

end
