import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Manifold
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem unitModel_of_deTurckRHSSection_realize
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (W : SmoothCcTensor g₀ 0 2)
    (hW : W.toSection =
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 W x v =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  rw [unitModel]
  change Tensor0SSpace.toModel ((W.toSection x) _) v = _
  rw [hW, Tensor0SSpace.toModel_apply_model_vector]
  exact deTurckRHSSection_eval (I := I) g_bg
    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x _

end DifferentialGeometry.Analysis.Spectral
