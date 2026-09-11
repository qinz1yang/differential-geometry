import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetricComplete_pullbackMetricCross {g : SmoothRiemannianMetric J N}
    (hg : RiemannianMetricComplete g) (Φ : M ≃ₘ⟮I, J⟯ N) :
    RiemannianMetricComplete (Diffeomorph.pullbackMetricCross g Φ) := by
  let gM : SmoothRiemannianMetric I M := Diffeomorph.pullbackMetricCross g Φ
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : IsManifold J 1 N := IsManifold.of_le (I := J) (M := N) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let : T3Space M := inferInstance
  let : T3Space N := inferInstance
  change RiemannianMetricComplete gM
  refine ⟨?_⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨gM.inner, gM.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric J N
  let : CompleteSpace N := hg.complete
  let e : M ≃ᵢ N := {
    Φ.toEquiv with
    isometry_toFun := by
      intro x y
      change riemannianEDistOf g (Φ x) (Φ y) = riemannianEDistOf gM x y
      exact (DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross g Φ x y).symm }
  exact e.completeSpace

end DifferentialGeometry.Geometry.Metric

end
