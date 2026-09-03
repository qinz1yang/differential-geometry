import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricComparisonEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNormUniformBound
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.HigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRiemannianFiberNormSqBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnectionDifferencePalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower

theorem jetGNInterp (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Cgn : ℕ → ℝ}
    (hCgn_ch : ∀ (k : ℕ) (hk : 1 ≤ k),
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k hk).choose = Cgn k)
    {Lam : ℝ} (hLam_nn : 0 ≤ Lam)
    (hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2)
    (i₀ : ℕ) (hi₀ : 1 ≤ i₀) (j : ℕ) (hj0 : 0 < j) (hji : j < i₀) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
      Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)) := by
  have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
    (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose_spec.2
  have hb := hGNspec (iteratedCovGrad (I := I) g₀ 0 2 2 P) Lam hLam_nn hΛsup_v2 j hj0 hji
  rw [hCgn_ch i₀ hi₀] at hb
  have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 ((2 + 2) + i₀)
      (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toFun =
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀ (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ :=
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
      (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
  rw [hnorm] at hb
  exact hb

end CurvatureCoefficientDifferenceJetTower

end Spectral
end Analysis
end DifferentialGeometry

end
