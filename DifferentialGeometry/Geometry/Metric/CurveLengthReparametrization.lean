import DifferentialGeometry.Geometry.Metric.CurveVariation
import DifferentialGeometry.Analysis.Calculus.Variation.Periodic



noncomputable section

open Bundle Manifold Set DifferentialGeometry Function
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



theorem riemannianCurveLength_unit_period (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (hp : Periodic γ 1) (a : ℝ) :
    riemannianCurveLength g γ a (a + 1) = riemannianCurveLength g γ 0 1 := by
  rw [riemannianCurveLength_eq_variation g hγ, riemannianCurveLength_eq_variation g hγ]
  apply congrArg ENNReal.toReal
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.eVariationOn_unit_period hp a




theorem riemannianCurveLength_comp_monotone_lift (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C D : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (hp : Periodic γ 1) {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hm : Monotone ψ)
    (hdegree : ∀ t, ψ (t + 1) = ψ t + 1)
    (hcomp : ∀ x y, riemannianEDistOf g (γ (ψ x)) (γ (ψ y)) ≤ (D : ℝ≥0∞) * edist x y) :
    riemannianCurveLength g (γ ∘ ψ) 0 1 = riemannianCurveLength g γ 0 1 := by
  rw [riemannianCurveLength_eq_variation g (γ := γ ∘ ψ) hcomp, riemannianCurveLength_eq_variation g hγ]
  apply congrArg ENNReal.toReal
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.eVariationOn_comp_monotone_lift hp hψ hm hdegree

end DifferentialGeometry.Geometry
