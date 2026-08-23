import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.UnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
omit [NeZero (Module.finrank ℝ E)] in
theorem unitModel_basisChart_eq_tensorChartComponentRaw (g : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g s W x (fun k => chartModelBasis E (Jdx k)) =
      tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx x := by
  rw [tensorChartComponentRaw_def, tensorChartComponentProjection_apply]
  unfold tensorTrivProj
  rw [DifferentialGeometry.Tensor.tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
        (I := I) (M := M) 0 s x (b := x) rfl (mem_chart_source H x)
        (W.toSection x) (dualCoordinateProductMultilinearMap (E := E) 0 ![])]
  unfold unitModel
  congr 2

omit [NeZero (Module.finrank ℝ E)] in
theorem unitModel_basisChart_eq_tensorChartComponent (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (k i : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g 2 W x ![chartModelBasis E k, chartModelBasis E i] =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 W x ![] ![k, i] x := by
  have h := unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g 2 W x ![k, i]
  have hfun : (fun j : Fin 2 => chartModelBasis E (![k, i] j)) =
      ![chartModelBasis E k, chartModelBasis E i] := by
    funext j; fin_cases j <;> rfl
  rwa [hfun] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (g₁ : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((chartModelBasis E).cDualBasis k)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  apply DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective (I := I) g₁ x
  ext u
  change g₁.inner x (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((chartModelBasis E).cDualBasis k))) u =
    g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u
  rw [cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((chartModelBasis E).cDualBasis k) u]
  have hu : u = ∑ m : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m •
        chartBasisVecFiber (I := I) x m x :=
    chartBasisVecFiber_recompose (I := I) x hxbase u
  set c : Fin (Module.finrank ℝ E) → ℝ := fun m =>
    ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m with hc_def
  have hRHS_inner :
      g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u =
        ∑ m : Fin (Module.finrank ℝ E),
          c m * (if k = m then (1 : ℝ) else 0) := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (g₁.inner x (chartInvGramMatrix (I := I) g₁ x x k l •
                (chartModelBasis E l : TangentSpace I x))) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      refine congrArg (fun t : TangentSpace I x => chartInvGramMatrix (I := I) g₁ x x k l *
        g₁.inner x (chartModelBasis E l : TangentSpace I x) t) ?_
      exact hu
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) =
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    rw [show ∑ m : Fin (Module.finrank ℝ E),
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) =
          ∑ m : Fin (Module.finrank ℝ E), c m *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l *
                chartGramMatrix (I := I) g₁ x x l m) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show g₁.inner x (chartModelBasis E l : TangentSpace I x)
              (chartBasisVecFiber (I := I) x m x) =
            chartGramMatrix (I := I) g₁ x x l m from ?_]
      · ring
      · rw [show (chartModelBasis E l : TangentSpace I x) =
            chartBasisVecFiber (I := I) x l x from (hself l).symm]
        rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ x x l m]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    have hkron : (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            chartGramMatrix (I := I) g₁ x x l m) =
        (chartInvGramMatrix (I := I) g₁ x x * chartGramMatrix (I := I) g₁ x x) k m := by
      rw [Matrix.mul_apply]
    rw [hkron, chartInvGramMatrix_mul_chartGramMatrix (I := I) g₁ x hxbase, Matrix.one_apply]
  rw [hRHS_inner]
  rw [show (chartModelBasis E).cDualBasis k (u : E) =
        ∑ m : Fin (Module.finrank ℝ E), c m *
          (chartModelBasis E).cDualBasis k (chartBasisVecFiber (I := I) x m x : E) from ?_]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    rw [show (chartBasisVecFiber (I := I) x m x : E) = (chartModelBasis E m : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) (hself m)]
    rw [Module.Basis.cDualBasis_apply_self (chartModelBasis E) k m]
  · conv_lhs => rw [show (u : E) = ((∑ m : Fin (Module.finrank ℝ E),
          c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) hu]
    rw [show ((∑ m : Fin (Module.finrank ℝ E),
            c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) =
          ∑ m : Fin (Module.finrank ℝ E),
            c m • (chartBasisVecFiber (I := I) x m x : E) from ?_]
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    · rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
