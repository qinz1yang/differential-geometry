import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricComparisonEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem riemannianFiberNormSqIterCont (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (l : ℕ) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 0 2 l P)
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P) x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
theorem jetSupLow (g₀ : SmoothRiemannianMetric I M) {a : ℕ} {R Cemb Lam : ℝ}
    (hR : 0 ≤ R)
    (hCemb : ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
      (∑ m ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m W).toSection x)) ≤
        Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2)
    (hLam : Lam = Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R)
    (P : SmoothCcTensor g₀ 0 2)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R)
    (m : ℕ) (hm : m ≤ 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
  have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
        ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
      _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤
      ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) := by
    have hmmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    exact Finset.single_le_sum
      (f := fun m' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x))
      (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m') x _) hmmem
  have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hchain : ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) ≤ Lam ^ 2 := by
    refine le_trans (hCemb P x) ?_
    rw [hLam2]
    calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
        ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
  exact le_trans hsingle hchain

end CurvatureCoefficientDifferenceJetTower

end Spectral
end Analysis
end DifferentialGeometry

end
