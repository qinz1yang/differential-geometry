import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LiePathDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LieTermChartValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.SymmetrizedReindexedCoefficient

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [SigmaCompactSpace M] in
theorem linearizedDeTurckLieAt_eq_threeArm_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w =
        smoothCcTensorBilinForm (I := I) g₀ (T - T') x w v)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → E) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorrectionZeroField (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  let vt : Fin 2 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
  have hSsymmS : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g₀ (T - T') hSsymm
  rw [linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) hs]
  rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (vt 0) (vt 1) hs).deriv]
  simp only [vt, DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j
            (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorrectionZeroField (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i,
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j] := by
    intro i j
    rw [deriv_metricPerturbationPath_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    have h := lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
    rw [hSsymmS] at h
    exact h
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorrectionZeroField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      + operatorFieldApply (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      + operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hWbase
  calc (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 0)) i *
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j
              (extChartAt I x x)) s)
      = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 0)) i *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 1)) j *
            deriv (fun s : ℝ =>
              DeTurckCoefficients.chartLieDeTurckComp (I := I)
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j
                  (extChartAt I x x)) s := Finset.sum_comm
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 0)) i *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (v 1)) j *
            unitModel (I := I) (M := M) g₀ 2 Wbase x
              ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i,
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j] := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [hcomp i j]
    _ = unitModel (I := I) (M := M) g₀ 2 Wbase x v :=
        unitModel_basis_expand_two (I := I) (M := M) g₀ Wbase x v

end DifferentialGeometry.Analysis.Spectral
