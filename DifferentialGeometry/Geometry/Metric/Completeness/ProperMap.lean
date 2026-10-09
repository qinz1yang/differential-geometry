import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Topology.UniformSpace.ProperMap

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.RiemannianMetricComplete

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem of_isProperMap_of_mfderiv_bound
    (g : SmoothRiemannianMetric I M) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (hp : IsProperMap f)
    {C : NNReal} (hC : 0 < C)
    (hb : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v)) :
    RiemannianMetricComplete g := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hLip : LipschitzWith C f := fun x y =>
    Geometry.edist_map_le_of_metric_mfderiv_bound g hC hf hb x y
  exact hp.completeSpace hLip.uniformContinuous

end DifferentialGeometry.RiemannianMetricComplete
