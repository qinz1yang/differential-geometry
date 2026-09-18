import DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz
import DifferentialGeometry.Topology.LoopSpace.Lipschitz

noncomputable section

open Bundle Manifold Set DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

omit [FiniteDimensional ℝ E] in
theorem exists_riemannian_lipschitz_freeLoop_of_contMDiff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : loopCircle → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ∃ L : ℝ≥0, ∀ θ η : loopCircle,
      riemannianEDistOf g (γ θ) (γ η) ≤ (L : ℝ≥0∞) * edist θ η := by
  obtain ⟨C, hC⟩ := exists_compact_source_riemannian_lipschitz (f := fun t : ℝ => γ (t : loopCircle))
    g (U := Set.univ) isOpen_univ ((hγ.of_le (by simp)).contMDiffOn) isCompact_Icc
    (Set.subset_univ _)
  refine ⟨C, fun θ η => ?_⟩
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, had, hdist⟩ :=
    DifferentialGeometry.Topology.exists_short_circle_lifts η θ
  have ha : a ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hadm : a + d ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hda : dist θ η = |d| := by rw [dist_comm, hdist]
  have he : edist a (a + d) = edist θ η := by
    have h1 : dist a (a + d) = |d| := by
      have h : a - (a + d) = -d := by ring
      rw [Real.dist_eq, h, abs_neg]
    rw [edist_dist, edist_dist, h1, hda]
  calc riemannianEDistOf g (γ θ) (γ η)
      = riemannianEDistOf g (γ (a : loopCircle)) (γ ((a + d : ℝ) : loopCircle)) := by
        rw [hay, had]
    _ ≤ (C : ℝ≥0∞) * edist a (a + d) := hC a ha (a + d) hadm
    _ = (C : ℝ≥0∞) * edist θ η := by rw [he]

end DifferentialGeometry.Geometry
