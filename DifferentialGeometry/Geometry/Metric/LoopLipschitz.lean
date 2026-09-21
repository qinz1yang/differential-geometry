import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Topology.LoopSpace.Lipschitz

section

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_riemannian_lipschitz_freeLoop_of_contMDiff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => γ (t : loopCircle))) :
    ∃ C : ℝ≥0, ∀ θ η, riemannianEDistOf g (γ θ) (γ η) ≤ (C : ℝ≥0∞) * edist θ η := by
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g isOpen_univ hγ.contMDiffOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)) (subset_univ _)
  refine ⟨C, ?_⟩
  intro θ η
  obtain ⟨a, d, ha0, ha1, hd0, hd1, haη, hadθ, hdist⟩ := exists_short_circle_lifts θ η
  have ha : a ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have had : a + d ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h := riemannian_edist_le_on_convex_source g isOpen_univ hγ.contMDiffOn
    (subset_univ _) (convex_Icc (-1 : ℝ) 2) hC had ha
  have hdist' : edist (a + d) a = edist θ η := by
    rw [edist_dist, edist_dist, hdist, Real.dist_eq, add_sub_cancel_left]
  simpa only [haη, hadθ, hdist'] using h

end DifferentialGeometry.Geometry

end

end
