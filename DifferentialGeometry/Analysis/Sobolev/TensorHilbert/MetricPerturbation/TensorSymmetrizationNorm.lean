import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ReindexingTermDecomposition
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmetricBilinearForm_of_tensorSymmetrization_eq_self (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [ccTensorBilinSymm_apply, smoothCcTensorBilinForm_ccTensor02Symm, smoothCcTensorBilinForm_ccTensor02Symm,
    ccTensorBilinSymm_symm (I := I) g₀ T x w v, ccTensorBilinSymm_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem fiberwiseOperatorNormBound_of_tensorSymmetrization (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T)) δ := by
  intro x v w
  rw [symmetricBilinearForm_of_tensorSymmetrization_eq_self (I := I) (M := M) g₀ T x v w]
  exact hδ x v w

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem bilinearForm_of_tensorSymmetrization_symm (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x v w =
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x w v := by
  rw [smoothCcTensorBilinForm_ccTensor02Symm, smoothCcTensorBilinForm_ccTensor02Symm, ccTensorBilinSymm_symm]

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  have hbridge : ∀ (W : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 k W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + k)
      (iteratedCovGrad (I := I) g₀ 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k
            (domDomCongrSection (I := I) g₀ σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) σ T k x
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g₀ σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hintegrand)
  have hnnA : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ :=
    norm_nonneg _
  have hnnB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  exact (sq_eq_sq₀ hnnA hnnB).mp hsq

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_tensorSymmetrization_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T with hTsw_def
  have hiter_eq : iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k Tsw := by
    rw [hTsw_def]; exact iteratedCovGrad_ccTensor02Symm_eq (I := I) g₀ T k
  rw [hiter_eq]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by rw [Real.norm_eq_abs]; norm_num
  rw [habs, hTsw_def,
    norm_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) T k]
  have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_ccTensor02Symm_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ :=
  norm_iteratedCovGrad_tensorSymmetrization_le (I := I) (M := M) g₀ T k

end DifferentialGeometry.Analysis.Spectral

end
