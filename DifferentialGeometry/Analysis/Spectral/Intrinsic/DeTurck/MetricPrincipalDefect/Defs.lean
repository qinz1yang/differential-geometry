import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def deTurckMetricPrincipalDefectTotal (g₀ g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieSecondOrderPrincipalCoeff (I := I) g₀ g
    + traceHessianCoeff (I := I) (M := M) g₀ g
    - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
        + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g)

private theorem trace_perm_comp (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieTrace_reindex (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoefficientInputSlots_toSection,
    traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoefficientInputSlotsFiber_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_eq_reindex (g₀ g : SmoothRiemannianMetric I M) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
        - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
            + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := by
  have hPhi : deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermA
        + deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermAT
        - traceHessianCoeff (I := I) (M := M) g₀ g)
      + traceHessianCoeff (I := I) (M := M) g₀ g
      - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
          + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := rfl
  rw [hPhi,
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermA
      (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA)
      (trace_perm_comp deTurckLieSecondOrderDivSlotPermA),
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieSecondOrderDivSlotPermAT
      (traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT)
      (trace_perm_comp deTurckLieSecondOrderDivSlotPermAT)]
  abel

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) =
      deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        - (linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckMetricPrincipalDefectTotal, linearizedRicciSecondOrderFieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgroup : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by
    abel
  rw [hgroup, hhalf]
  abel

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq_neg_two_smul
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) =
      (-2 : ℝ) • linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckMetricPrincipalDefectTotal_metricPerturbationPath_eq (I := I) (M := M)
    g₀ T T' hδ hδ' s]
  rw [show (-2 : ℝ) • linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
      -(linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciSecondOrderFieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) from by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul, two_smul]]
  abel

end DifferentialGeometry.Analysis.Spectral
