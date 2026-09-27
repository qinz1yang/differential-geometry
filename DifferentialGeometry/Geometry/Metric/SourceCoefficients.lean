import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.CompactBounds








open Set Bundle Manifold DifferentialGeometry
open scoped ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem contDiffOn_sourceMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U) (v w : V) :
    ContDiffOn ℝ ∞ (fun x => g.inner (f x)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x v) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x w)) U :=
  contDiffOn_sourceSectionPairing g hf
    (contMDiffOn_source_partial hU hf (by simp) v)
    (contMDiffOn_source_partial hU hf (by simp) w)



theorem exists_bound_iteratedFDeriv_sourceMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v w : V) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun y => g.inner (f y)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y v) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y w)) x‖ ≤ C :=
  DifferentialGeometry.Analysis.exists_bound_iteratedFDeriv_on_compact hU
    (contDiffOn_sourceMetricPairing g hU hf v w) hK hKU k

end DifferentialGeometry.Geometry
