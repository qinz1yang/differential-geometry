import DifferentialGeometry.Geometry.Metric.SelfAdjointConjugate
import DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction

noncomputable section

open Bundle
open DifferentialGeometry.HomConnectionGen
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ I] [IsContMDiffRiemannianBundle I ∞ F₂ V₂]

namespace CovariantDerivative

theorem map_selfAdjoint_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0) :
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯)
      (x : M) (X : TangentSpace I x),
      (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (D.selfAdjoint hD (ContMDiffSection.selfAdjointConjugate φ hφ A) x X :
          V₁ x →L[ℝ] V₁ x) =
      (C.selfAdjoint hC A x X : V₂ x →L[ℝ] V₂ x).comp
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap := by
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  dsimp only
  intro A x X
  let B := ContMDiffSection.selfAdjointConjugate φ hφ A
  let a := fun y => (A y : V₂ y →L[ℝ] V₂ y)
  let b := fun y => (B y : V₁ y →L[ℝ] V₁ y)
  have ha := (S₂.contMDiff_section_iff A).mp A.contMDiff
  have hb := (S₁.contMDiff_section_iff B).mp B.contMDiff
  have hφx := (hφ x).mdifferentiableAt (by simp)
  have hl := homBundleCovariantDerivativeGen_comp D D C
    ((hb x).mdifferentiableAt (by simp)) hφx X
  have hr := homBundleCovariantDerivativeGen_comp D C C
    hφx ((ha x).mdifferentiableAt (by simp)) X
  have heq : (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap.comp (b y)) =
      (fun y => (a y).comp (φ y).toContinuousLinearEquiv.toContinuousLinearMap) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    exact (φ y).apply_symm_apply (a y (φ y v))
  change homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
    (fun y => (φ y).toContinuousLinearEquiv.toContinuousLinearMap.comp (b y)) x X = _ at hl
  rw [hparallel] at hl hr
  simp only [Pi.zero_apply, zero_apply, ContinuousLinearMap.zero_comp, zero_add,
    ContinuousLinearMap.comp_zero, add_zero] at hl hr
  rw [D.selfAdjoint_subtypeVal hD, C.selfAdjoint_subtypeVal hC]
  exact hl.symm.trans
    ((congrArg (fun s => homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C s x X) heq).trans hr)

end CovariantDerivative
