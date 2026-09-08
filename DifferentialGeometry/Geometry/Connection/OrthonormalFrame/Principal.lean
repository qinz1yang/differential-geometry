import DifferentialGeometry.Geometry.Connection.OrthonormalFrame
import DifferentialGeometry.Geometry.Connection.Principal
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Principal

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

def orthonormalFramePrincipalConnectionForm (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible) (hsmooth : ContMDiffCovariantDerivative cov ∞) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
    letI : ∀ x, Nonempty (V x ≃ₗᵢ[ℝ] F) := fun x => ⟨FiberBundle.linearIsometryEquivAt (F := F) V x⟩
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).toFiberBundle
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I ∞
    letI := FiberBundle.orthonormalFrame_isPrincipalBundle (F := F) V
    letI := FiberBundle.orthonormalFrame_isManifold (F := F) V I ∞
    PrincipalConnectionForm 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) (F ≃ₗᵢ[ℝ] F)
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (fun x => V x ≃ₗᵢ[ℝ] F) ∞ := by
  letI : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  letI : ∀ x, Nonempty (V x ≃ₗᵢ[ℝ] F) := fun x => ⟨FiberBundle.linearIsometryEquivAt (F := F) V x⟩
  letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).toFiberBundle
  letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I ∞
  letI := FiberBundle.orthonormalFrame_isPrincipalBundle (F := F) V
  letI := FiberBundle.orthonormalFrame_isManifold (F := F) V I ∞
  let O := 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))
  let P := TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)
  let φ := LinearIsometryEquiv.groupLieAlgebraEquiv (E := F)
  let omegaForm : ∀ p : P, TangentSpace (I.prod O) p →L[ℝ] GroupLieAlgebra O (F ≃ₗᵢ[ℝ] F) :=
    fun p => φ.symm.toContinuousLinearMap.comp
      ((cov.orthonormalFrameConnectionForm (by simp) p).codRestrict
        (skewAdjoint.submodule ℝ (F →L[ℝ] F))
        (fun U => hcov.orthonormalFrameConnectionForm_mem_skewAdjoint (by simp) p U))
  refine ⟨omegaForm, ?_, ?_, ?_⟩
  · let : ∀ p : P, TopologicalSpace (TangentSpace (I.prod O) p) := fun _ => inferInstance
    let pr : (F →L[ℝ] F) →L[ℝ] skewAdjoint.submodule ℝ (F →L[ℝ] F) := {
      __ := skewAdjointPart ℝ
      cont := by
        apply continuous_induced_rng.mpr
        exact (continuous_id.sub continuous_star).const_smul (⅟ (2 : ℝ)) }
    let L := (DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
      (I := O) (1 : F ≃ₗᵢ[ℝ] F)).toContinuousLinearMap.comp
      (φ.symm.toContinuousLinearMap.comp pr)
    have h := L.contMDiff.comp (cov.contMDiff_orthonormalFrameConnectionForm hsmooth)
    apply h.congr
    intro z
    symm
    change L (cov.orthonormalFrameConnectionForm (by simp) z.proj z.snd) =
      (omegaForm z.proj z.snd : skewAdjoint.submodule ℝ (F →L[ℝ] F))
    have hpr := LinearMap.congr_fun
      (skewAdjointPart_comp_subtype_skewAdjoint (R := ℝ) (A := F →L[ℝ] F))
      (⟨cov.orthonormalFrameConnectionForm (by simp) z.proj z.snd,
        hcov.orthonormalFrameConnectionForm_mem_skewAdjoint (by simp) z.proj z.snd⟩ :
        skewAdjoint.submodule ℝ (F →L[ℝ] F))
    exact congrArg (fun K : skewAdjoint.submodule ℝ (F →L[ℝ] F) =>
      (DifferentialGeometry.tangentSpaceModelContinuousLinearEquiv
        (I := O) (1 : F ≃ₗᵢ[ℝ] F)) (φ.symm K)) hpr
  · intro p U
    apply φ.injective
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    change (φ (φ.symm _)).val w = (φ U).val w
    rw [φ.apply_symm_apply]
    exact cov.orthonormalFrameConnectionForm_fundamental_apply (by simp) p U w
  · intro g p X
    apply φ.injective
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    change (φ (φ.symm _)).val w =
      (φ (mfderiv O O (fun h => g * h * g⁻¹) 1 (omegaForm p X))).val w
    rw [φ.apply_symm_apply, LinearIsometryEquiv.groupLieAlgebraEquiv_conj]
    change cov.orthonormalFrameConnectionForm (by simp) (g • p)
      (mfderiv (I.prod O) (I.prod O) (fun q : P => g • q) p X) w =
        g ((φ (φ.symm _)).val (g.symm w))
    rw [φ.apply_symm_apply]
    exact cov.orthonormalFrameConnectionForm_smul_apply (by simp) g p X w

theorem orthonormalFramePrincipalConnectionForm_apply (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible) (hsmooth : ContMDiffCovariantDerivative cov ∞) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
    letI : ∀ x, Nonempty (V x ≃ₗᵢ[ℝ] F) := fun x => ⟨FiberBundle.linearIsometryEquivAt (F := F) V x⟩
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := (FiberBundle.orthonormalFramePrebundle (F := F) V).toFiberBundle
    letI := FiberBundle.orthonormalFrameChartedSpace (F := F) V I ∞
    letI := FiberBundle.orthonormalFrame_isPrincipalBundle (F := F) V
    letI := FiberBundle.orthonormalFrame_isManifold (F := F) V I ∞
    ∀ (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))
      (U : TangentSpace (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) p),
      (LinearIsometryEquiv.groupLieAlgebraEquiv
        ((cov.orthonormalFramePrincipalConnectionForm hcov hsmooth).toFun p U) : F →L[ℝ] F) =
        cov.orthonormalFrameConnectionForm (by simp) p U := by
  intro p U
  exact congrArg Subtype.val
    (LinearIsometryEquiv.groupLieAlgebraEquiv.apply_symm_apply _)

end CovariantDerivative
