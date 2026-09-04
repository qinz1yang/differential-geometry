import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.Tower

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.ReverseSecondDerivative

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def morreyTwoC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let L₁ := max (revJetOneC (E := E) Λ) Λ
  let L₂ := revJetTwoC (E := E) Λ
  morreyUnifConst Λ
    (baseMorreyConst (I := I) (M := M) gBase 0 2)
    (kjetConst (Module.finrank ℝ E) Λ L₁ L₂ 2)
    (Module.finrank ℝ E) 2

theorem morreyTwoC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdim : Module.finrank ℝ E / 2 + 2 = 3) :
    0 ≤ morreyTwoC (I := I) (M := M) gBase Λ ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (T : SmoothCcTensor g 0 2) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
            morreyTwoC (I := I) (M := M) gBase Λ ^ 2 *
              ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
  have hC : 0 ≤ morreyTwoC (I := I) (M := M) gBase Λ := by
    dsimp only [morreyTwoC]
    exact morreyUnifConst_nonneg hΛ
      (baseMorreyConst_nonneg (I := I) (M := M) gBase 0 2)
      (kjetConst_nonneg hΛ
        (hΛ.trans (le_max_right _ _))
        (by
          dsimp [revJetTwoC]
          exact le_max_left _ _)
        (Module.finrank ℝ E) 2)
      (Module.finrank ℝ E) 2
  refine ⟨hC, ?_⟩
  intro g hEq hjet1 hjet2 T x
  obtain ⟨hL₁, hL₂, hfwd1, hrev1, hrev2⟩ :=
    reverseJetPack (I := I) gBase g hEq hjet1 hjet2
  have hmorrey := fibreMorrey_uniform_class (I := I) gBase g hEq
    hfwd1 hrev1 hrev2 hL₁ hL₂ hdim 2 T x
  simpa only [morreyTwoC] using hmorrey

end RicciFlow
end PDE
end DifferentialGeometry
