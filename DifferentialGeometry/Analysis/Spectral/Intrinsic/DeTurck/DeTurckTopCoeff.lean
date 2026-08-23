import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

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
  deTurckLieArm2PrincipalCoeff (I := I) g₀ g
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
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection,
    traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem metricPrincipalDefect_reindex (g₀ g : SmoothRiemannianMetric I M) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
        - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
            + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := by
  have hPhi : deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀ g =
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
        + deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
        - traceHessianCoeff (I := I) (M := M) g₀ g)
      + traceHessianCoeff (I := I) (M := M) g₀ g
      - (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g
          + ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g) := rfl
  rw [hPhi,
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
      (trace_perm_comp deTurckLieArm2DivSlotPermA),
    lieTrace_reindex (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
      (trace_perm_comp deTurckLieArm2DivSlotPermAT)]
  abel

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem phi_realized_eq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) =
      deTurckLieArm2PrincipalCoeff (I := I) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckMetricPrincipalDefectTotal, linearizedRicciArm2FieldLichnerowicz]
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

end DifferentialGeometry.Analysis.Spectral
