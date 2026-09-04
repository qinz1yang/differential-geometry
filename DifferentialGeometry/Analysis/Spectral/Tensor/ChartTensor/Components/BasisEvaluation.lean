import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.UnitModel
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities

noncomputable section


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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
omit [NeZero (Module.finrank ℝ E)] in
theorem unitModel_basisChart_eq_tensorChartComponentRaw (g : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g s W x (fun k => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (Jdx k)) =
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
    unitModel (I := I) (M := M) g 2 W x ![DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i] =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 W x ![] ![k, i] x := by
  have h := unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g 2 W x ![k, i]
  have hfun : (fun j : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E (![k, i] j)) =
      ![DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i] := by
    funext j; fin_cases j <;> rfl
  rwa [hfun] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (g₁ : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).cDualBasis k)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l • DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x t x = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E t := fun t =>
    by
      rw [chartBasisVecFiber_self (I := I) x t, DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply,
        DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply]
  apply DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective (I := I) g₁ x
  ext u
  change g₁.inner x (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).cDualBasis k))) u =
    g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k l • DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) u
  rw [cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).cDualBasis k) u]
  have hu : u = ∑ m : Fin (Module.finrank ℝ E),
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m •
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x :=
    chartBasisVecFiber_recompose (I := I) x hxbase u
  set c : Fin (Module.finrank ℝ E) → ℝ := fun m =>
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m with hc_def
  have hRHS_inner :
      g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l • DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) u =
        ∑ m : Fin (Module.finrank ℝ E),
          c m * (if k = m then (1 : ℝ) else 0) := by
    rw [map_sum (g₁.inner x), sum_apply]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (g₁.inner x (chartInvGramMatrix (I := I) g₁ x x k l •
                DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) u from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_smul, smul_apply, smul_eq_mul]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)
                (∑ m : Fin (Module.finrank ℝ E), c m • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      refine congrArg (fun t : TangentSpace I x => chartInvGramMatrix (I := I) g₁ x x k l *
        g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l) t) ?_
      exact hu
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)
                (∑ m : Fin (Module.finrank ℝ E), c m • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x) =
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x))) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    rw [show ∑ m : Fin (Module.finrank ℝ E),
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x))) =
          ∑ m : Fin (Module.finrank ℝ E), c m *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ x x l m) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show g₁.inner x (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x m x) =
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ x x l m from ?_]
      · ring
      · rw [show DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x l =
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x l x from (chartBasisVecFiber_self (I := I) x l).symm]
        rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ x x l m]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    have hkron : (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ x x l m) =
        (chartInvGramMatrix (I := I) g₁ x x * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g₁ x x) k m := by
      rw [Matrix.mul_apply]
    rw [hkron, chartInvGramMatrix_mul_chartGramMatrix (I := I) g₁ x hxbase, Matrix.one_apply]
  rw [hRHS_inner]
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  rw [show (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).dualBasis k = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord k from
    congrFun (Module.Basis.coe_dualBasis (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) k]
  change ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (tangentSpaceModelContinuousLinearEquiv (I := I) x u)) k =
    ∑ m : Fin (Module.finrank ℝ E), c m * (if k = m then (1 : ℝ) else 0)
  have hc : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (tangentSpaceModelContinuousLinearEquiv (I := I) x u)) k = c k := by
    rw [hc_def, ← DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply (I := I) x u]
    rw [show DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x u =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u from
      congrFun ((trivializationAt E (TangentSpace I) x).coe_continuousLinearEquivAt_eq
        (R := ℝ) hxbase) u]
  rw [hc]
  rw [Finset.sum_eq_single k]
  · simp only [if_pos, mul_one]
  · intro m _ hmk
    rw [if_neg hmk.symm, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
