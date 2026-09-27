import DifferentialGeometry.Geometry.Measure.Area.GeodesicAnnulus



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry


def cylinderLift {Q : Type*} (H : ℝ × loopCircle → Q) (z : ℂ) : Q :=
  H (z.re, (z.im : loopCircle))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]


def cylinderArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (H : ℝ × loopCircle → M) : ℝ :=
  riemannianArea g (cylinderLift H) unitSquare

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem cylinderLift_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {H : ℝ × loopCircle → M} {K : ℝ≥0}
    (hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (K : ℝ≥0∞) * edist p q) :
    ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (cylinderLift H z) (cylinderLift H w) ≤ (C : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hH' : LipschitzWith K H := hH
  exact ⟨_, hH'.comp (Complex.reCLM.lipschitz.prodMk
    (loopCircle_projection_lipschitz.comp Complex.imCLM.lipschitz))⟩


theorem geodesicAnnulusArea_eq_cylinderArea
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : loopCircle → M) :
    geodesicAnnulusArea g γ₀ γ₁ = cylinderArea g (geodesicAnnulus g γ₀ γ₁) := rfl

end DifferentialGeometry.Geometry
