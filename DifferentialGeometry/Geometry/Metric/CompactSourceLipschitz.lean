import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import DifferentialGeometry.Topology.Connected.FiniteEDistance
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry Filter Metric
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem exists_local_source_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U) {x : V} (hx : x ∈ U) :
    ∃ (C : ℝ≥0) (S : Set V), S ∈ 𝓝 x ∧ ∀ y ∈ S, ∀ z ∈ S,
      riemannianEDistOf g (f y) (f z) ≤ (C : ℝ≥0∞) * edist y z := by
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hball : closedBall x (a / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith : a / 2 < a)).trans haU
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hf
    (isCompact_closedBall x (a / 2)) hball
  exact ⟨C, closedBall x (a / 2), closedBall_mem_nhds x (half_pos ha),
    fun y hy z hz => riemannian_edist_le_on_convex_source g hU hf hball
      (convex_closedBall x (a / 2)) hC hy hz⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_compact_source_riemannian_lipschitz [T3Space M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ y ∈ S, ∀ z ∈ S,
      riemannianEDistOf g (f y) (f z) ≤ (C : ℝ≥0∞) * edist y z := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hlocal : LocallyLipschitzOn S f := by
    intro x hx
    obtain ⟨C, A, hA, hC⟩ := exists_local_source_riemannian_lipschitz g hU hf (hSU hx)
    exact ⟨C, A, mem_nhdsWithin_of_mem_nhds hA, hC⟩
  exact hlocal.exists_lipschitzOnWith_of_compact hS

end DifferentialGeometry.Geometry
