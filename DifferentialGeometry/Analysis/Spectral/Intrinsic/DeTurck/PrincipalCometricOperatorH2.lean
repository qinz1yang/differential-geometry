import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricCoefficientBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SecondCovariantDerivativeApplication

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

noncomputable def principalCometricOperatorH2
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) :=
  secondCovariantDerivativeApplication (I := I) (M := M) g₀ 2 2
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)

theorem principalCometricOperatorH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        ‖principalCometricOperatorH2 (I := I) (M := M) g₀ g₁‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
  obtain ⟨ρ, Ccoeff, hρ, hCcoeff, hcoeff⟩ :=
    exists_deTurckPrincipalCometricCoefficient_secondOrder_bound (I := I) (M := M) hDim g₀
  obtain ⟨Capp, hCapp, happ⟩ :=
    secondCovariantDerivativeApplication_norm (I := I) (M := M) hDim g₀ 2 2
  refine ⟨ρ, Capp * Ccoeff, hρ, mul_nonneg hCapp hCcoeff, ?_⟩
  intro T g₁ hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  let A : ℝ := Ccoeff * N
  have hN : 0 ≤ N := norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg hCcoeff hN
  obtain ⟨_, hjet⟩ := hcoeff T g₁ (by simpa only [N] using hT) htie
  have hbound := happ
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    A hA (by simpa only [A, N] using hjet)
  simpa only [principalCometricOperatorH2, A, N, mul_assoc] using hbound

theorem principalCometricOperatorH2_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor g₀ 0 2) :
    principalCometricOperatorH2 (I := I) (M := M) g₀ g₁
        (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ U) := by
  simpa only [principalCometricOperatorH2, deTurckPrincipalCometricArm] using
    secondCovariantDerivativeApplication_ccTensorToHs (I := I) (M := M) hDim g₀ 2 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
