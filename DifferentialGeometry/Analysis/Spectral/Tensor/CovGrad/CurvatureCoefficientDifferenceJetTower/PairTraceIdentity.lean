import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Grid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Palatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RecoveryEndomorphismJetBounds
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis

import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.FiberNorm.Basic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.HigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.JetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.JetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.ParallelRaiseJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantOrderFibreNormBounds
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_operatorFieldComposition_parallel (g₀ : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) (W : SmoothCcTensor g₀ a b) :
    ∀ j : ℕ, iteratedCovGrad (I := I) g₀ a c j
        (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W) :=
  CurvatureCoefficientDifferenceJetTower.iteratedCovGrad_operatorFieldComposition_parallel
    (I := I) (M := M) g₀ a b c Φ hΦ W

def pairTraceKernel (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  CurvatureCoefficientDifferenceJetTower.phiDtPair (I := I) (M := M) g₀

omit [SigmaCompactSpace M] in
lemma phiDtPair_covGrad_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 6 2 (pairTraceKernel (I := I) (M := M) g₀) = 0 := by
  unfold pairTraceKernel
  exact CurvatureCoefficientDifferenceJetTower.phiDtPair_covGrad_zero
    (I := I) (M := M) g₀

def pairTraceKernelSlotPerm : Equiv.Perm (Fin 6) :=
  CurvatureCoefficientDifferenceJetTower.sigmaE0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
lemma slotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x
          (fun k : Fin 4 => u (Fin.natAdd 2 k)) :=
  CurvatureCoefficientDifferenceJetTower.slotExtendIter_two_toModel
    (I := I) (M := M) g₀ X x D u

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem mixedCoeff_backgroundDifference_eq_pairTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceKernel (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  unfold pairTraceKernel pairTraceKernelSlotPerm
  exact CurvatureCoefficientDifferenceJetTower.mixedCoeff_backgroundDifference_eq_pairTrace
    (I := I) (M := M) g₀ g₁

end Spectral
end Analysis
end DifferentialGeometry
end
