import DifferentialGeometry.Geometry.Connection.OrthonormalFrame.Hom
import DifferentialGeometry.Geometry.LieGroup.Representation.SelfAdjoint

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]

private local instance selfAdjointNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (F →L[ℝ] F)) :=
  (selfAdjoint.submodule ℝ (F →L[ℝ] F)).normedAddCommGroup
private local instance selfAdjointNormedSpace :
    NormedSpace ℝ (selfAdjoint.submodule ℝ (F →L[ℝ] F)) :=
  (selfAdjoint.submodule ℝ (F →L[ℝ] F)).normedSpace

theorem coframe_homBundleCovariantDerivative_selfAdjointConjugation
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (q : ∀ x, V x ≃ₗᵢ[ℝ] F) {x : M}
    (hq : ∀ w : F, ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun y => TotalSpace.mk' F y ((q y).symm w)) x)
    (A : ∀ y, V y →L[ℝ] V y)
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F)) 1
      (fun y => TotalSpace.mk' (F →L[ℝ] F) y (A y)) x)
    (B : M → selfAdjoint.submodule ℝ (F →L[ℝ] F))
    (hB : MDifferentiableAt I 𝓘(ℝ, selfAdjoint.submodule ℝ (F →L[ℝ] F)) B x)
    (hBA : (fun y => (B y : F →L[ℝ] F)) =ᶠ[𝓝 x] fun y =>
      (q y).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((A y).comp (q y).symm.toContinuousLinearEquiv.toContinuousLinearMap))
    (X : TangentSpace I x) :
    (q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V
        cov cov A x X).comp (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      ((mvfderiv I B x X - mvfderiv 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))
        (fun g : F ≃ₗᵢ[ℝ] F => ContRepresentation.selfAdjointConjugation g) 1
        (LinearIsometryEquiv.groupLieAlgebraEquiv.symm
          ⟨cov.coframeConnectionForm q x X, hcov.coframeConnectionForm_mem_skewAdjoint q hq X⟩)
        (B x)) : F →L[ℝ] F) := by
  have hd := congrArg (fun L => L X)
    ((mdifferentiableAt_const (c := (selfAdjoint.submodule ℝ (F →L[ℝ] F)).subtypeL)).mvfderiv_clm_apply
      hB)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hd
  change mvfderiv I (fun y => (B y : F →L[ℝ] F)) x X =
    (mvfderiv I B x X : F →L[ℝ] F) at hd
  change _ = (mvfderiv I B x X : F →L[ℝ] F) - _
  rw [ContRepresentation.coe_mvfderiv_selfAdjointConjugation_one_apply,
    LinearIsometryEquiv.groupLieAlgebraEquiv.apply_symm_apply, ← hd]
  have hderiv : mvfderiv I (fun y => (B y : F →L[ℝ] F)) x =
      mvfderiv I (fun y => (q y).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((A y).comp (q y).symm.toContinuousLinearEquiv.toContinuousLinearMap)) x := by
    unfold mvfderiv
    rw [hBA.mfderiv_eq]
    rfl
  have hpoint : (B x : F →L[ℝ] F) =
      (q x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((A x).comp (q x).symm.toContinuousLinearEquiv.toContinuousLinearMap) :=
    hBA.self_of_nhds
  rw [hderiv, hpoint, cov.coframe_homBundleCovariantDerivative q hq hA]
  abel

end CovariantDerivative
