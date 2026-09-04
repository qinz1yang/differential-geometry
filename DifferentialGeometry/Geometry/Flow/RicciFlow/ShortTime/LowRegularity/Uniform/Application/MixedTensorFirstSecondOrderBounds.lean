import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.H1L6
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.FiberLpThreeSixComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.Morrey
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem operatorFieldComposition_h1_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          ‖(⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
              SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ p r
  obtain ⟨CΦ, hCΦ, hΦ6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ r c
  obtain ⟨CG6, hCG6, hG6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ p (r + 1)
  obtain ⟨CV, hCV, h63⟩ :=
    DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six
      (I := I) (M := M) gBase Λ
  let CG3 : ℝ := CV * CG6
  let C : ℝ :=
    Cpt + (Cpt + Real.sqrt (Module.finrank ℝ E) * CΦ * CG3)
  have hCG3 : 0 ≤ CG3 := by
    dsimp [CG3]
    exact mul_nonneg hCV hCG6
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦjet hWjet
  have hΦ6' : ∀ S : SmoothCcTensorH1 g r c,
      lpNorm (fiberLpFun g r c S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * ‖S‖ := by
    intro S
    change lpNorm (fun x => Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r c x
          (S.toCcTensor.toSection x))) 6
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * ‖S‖
    exact hΦ6 g hEq hjet1 S
  have hG3 : ∀ S : SmoothCcTensorH1 g p (r + 1),
      lpNorm (fiberLpFun g p (r + 1) S.toCcTensor) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG3 * ‖S‖ := by
    intro S
    calc
      _ ≤ CV * lpNorm (fiberLpFun g p (r + 1) S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq p (r + 1) S.toCcTensor
      _ ≤ CV * (CG6 * ‖S‖) := by
        apply mul_le_mul_of_nonneg_left _ hCV
        change lpNorm (fun x => Real.sqrt
            (riemannianFiberNormSq (I := I) (M := M) g p (r + 1) x
              (S.toCcTensor.toSection x))) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG6 * ‖S‖
        exact hG6 g hEq hjet1 S
      _ = CG3 * ‖S‖ := by
        dsimp [CG3]
        ring
  have hlocal := operator_field_composition_h1_bound_of_embedding_bounds (I := I) (M := M) g p r c
    Cpt CΦ CG3 hCpt hCΦ hCG3 (hpt g hEq hjet1 hjet2) hΦ6' hG3
    Φ W A B hA hB hΦjet hWjet
  simpa only [C] using hlocal

theorem operatorFieldComposition_h2_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          ‖(⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
              SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.morreyRS_uniform
      (I := I) (M := M) hDim gBase hΛ r c
  obtain ⟨CG, hCG, hG6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ r (c + 1)
  obtain ⟨CW, hCW, hW6⟩ :=
    DifferentialGeometry.PDE.RicciFlow.h1Lp6RS_uniform
      (I := I) (M := M) hDim gBase hΛ p r
  obtain ⟨CV, hCV, h63⟩ :=
    DifferentialGeometry.PDE.RicciFlow.fiber_lp_three_le_uniform_constant_mul_lp_six
      (I := I) (M := M) gBase Λ
  let CW3 : ℝ := CV * CW
  let C : ℝ :=
    Cpt + (CG * CW3 + Real.sqrt (Module.finrank ℝ E) * Cpt)
  have hCW3 : 0 ≤ CW3 := by
    dsimp only [CW3]
    exact mul_nonneg hCV hCW
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦjet hWjet
  have hG6' : ∀ S : SmoothCcTensorH1 g r (c + 1),
      lpNorm (fiberLpFun g r (c + 1) S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * ‖S‖ := by
    intro S
    change lpNorm (fun x => Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r (c + 1) x
          (S.toCcTensor.toSection x))) 6
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * ‖S‖
    exact hG6 g hEq hjet1 S
  have hW3 : ∀ S : SmoothCcTensorH1 g p r,
      lpNorm (fiberLpFun g p r S.toCcTensor) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CW3 * ‖S‖ := by
    intro S
    calc
      _ ≤ CV * lpNorm (fiberLpFun g p r S.toCcTensor) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
        h63 g hEq p r S.toCcTensor
      _ ≤ CV * (CW * ‖S‖) := by
        apply mul_le_mul_of_nonneg_left _ hCV
        change lpNorm (fun x => Real.sqrt
            (riemannianFiberNormSq (I := I) (M := M) g p r x
              (S.toCcTensor.toSection x))) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CW * ‖S‖
        exact hW6 g hEq hjet1 S
      _ = CW3 * ‖S‖ := by
        dsimp only [CW3]
        ring
  have hlocal := operator_field_composition_h2_bound_of_embedding_bounds (I := I) (M := M) g p r c
    Cpt CG CW3 hCpt hCG hCW3 (hpt g hEq hjet1 hjet2) hG6' hW3
    Φ W A B hA hB hΦjet hWjet
  simpa only [C] using hlocal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
