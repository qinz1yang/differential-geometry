import DifferentialGeometry.Geometry.Metric.CompactInjectivity

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def intrinsicInjectivityRadiusOf
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M) : ENNReal := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let metricSpace : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := metricSpace.toPseudoEMetricSpace
  let : @CompleteSpace M metricSpace.toUniformSpace := hcomplete.complete
  have hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact intrinsicInjRadius (I := I) g hnorm p

@[simp] theorem intrinsicInjectivityRadiusOf_model_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hcomplete : RiemannianMetricComplete g) (p : E) :
    intrinsicInjectivityRadiusOf g hcomplete p = intrinsicInjectivityRadius g hcomplete p := by
  rfl

end DifferentialGeometry.Geometry.Riemannian

end
