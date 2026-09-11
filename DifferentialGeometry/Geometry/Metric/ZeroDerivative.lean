import DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz



noncomputable section

open Set Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem eq_of_mfderiv_eq_zero_on_convex
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hd : ∀ p ∈ S, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p = 0)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hdist := riemannian_edist_le_on_convex_source g hU hf hSU hS (C := 0)
    (fun p hp v => by simp [hd p hp]) hx hy
  have hzero : riemannianEDistOf g (f x) (f y) = 0 := by
    simpa only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] using hdist
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact edist_eq_zero.mp hzero

end DifferentialGeometry.Geometry
