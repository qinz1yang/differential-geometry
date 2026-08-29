import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CurvatureCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopPathDeviationBounds
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapLinear

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem top_path_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ Ctop Clow : ℝ, 0 < ρ ∧ 0 ≤ Ctop ∧ 0 ≤ Clow ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          {δ : ℝ} (hδ_lt : δ < 1)
          (hδ : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T) δ)
          {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : gFibreOpBound g
            (ccTensorBilinSymm (I := I) g T') δ')
          {R : ℝ}, 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ∀ U : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 4 2
                  (rhsTopPathIntegral (I := I) (M := M) g T T'
                    hδ_lt hδ hδ'_lt hδ')
                  (iteratedCovGrad (I := I) g 0 2 2 U) -
                DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
                  (I := I) g 0 2 U)‖ ≤
              Ctop * R *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
                Clow *
                  ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    top_path_dev_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h23_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Clow, hClow, hlow⟩ :=
    fixed_curv_h1_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, Capp * Cdev, Clow, hρ, mul_nonneg hCapp hCdev, hClow, ?_⟩
  intro g hEq hjet T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  obtain ⟨_, hdevJet⟩ :=
    hdev g hEq hjet T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT'
  have hA : 0 ≤ Cdev * R := mul_nonneg hCdev hR
  have htop := happ g hEq hjet
    (rhsTopPathIntegral (I := I) (M := M) g T T'
        hδ_lt hδ hδ'_lt hδ' -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
    U (Cdev * R) hA hdevJet
  have hlow' := hlow g hEq hjet U
  rw [top_path_split (I := I) (M := M) g T T'
    hδ_lt hδ hδ'_lt hδ' U, ccTensorToHs_add]
  simpa only [mul_assoc, iteratedCovGrad_zero] using
    (norm_add_le _ _).trans (add_le_add htop hlow')

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
