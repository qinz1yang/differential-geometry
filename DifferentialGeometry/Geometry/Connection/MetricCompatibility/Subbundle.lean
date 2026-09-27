import DifferentialGeometry.Geometry.Metric.Subbundle
import DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

namespace CovariantDerivative

theorem IsMetricCompatible.restrict
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞))
    (hS : DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily cov S.fiber) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    letI := S.contMDiffVectorBundle
    letI := S.isContMDiffRiemannianBundle (by simp : (1 : WithTop ℕ∞) ≤ ∞)
    (cov.restrict S hS).IsMetricCompatible := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  let _ := S.isContMDiffRiemannianBundle (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  unfold CovariantDerivative.IsMetricCompatible
  funext x
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  apply ContinuousLinearMap.ext
  intro X
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := Fin S.rank → ℝ) (V := fun y => S.fiber y) (n := (⊤ : ℕ∞)) x a
  obtain ⟨τ, hτ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := Fin S.rank → ℝ) (V := fun y => S.fiber y) (n := (⊤ : ℕ∞)) x b
  let W := FiberBundle.extend E X
  have hW : W x = X := by simp [W]
  let σ' : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (σ y : V y), (S.contMDiff_section_iff σ).mp σ.contMDiff⟩
  let τ' : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => (τ y : V y), (S.contMDiff_section_iff τ).mp τ.contMDiff⟩
  rw [← hσ, ← hτ, ← hW,
    (cov.restrict S hS).derivMetricTensor_apply x σ.mdifferentiableAt τ.mdifferentiableAt]
  change mvfderiv I (fun y => inner ℝ (σ' y) (τ' y)) x (W x) -
    inner ℝ (cov.restrict S hS σ x (W x) : V x) (τ' x) -
    inner ℝ (σ' x) (cov.restrict S hS τ x (W x) : V x) = 0
  rw [cov.restrict_subtypeVal S hS σ, cov.restrict_subtypeVal S hS τ,
    hcov.mvfderiv_inner_eq W σ'.mdifferentiableAt τ'.mdifferentiableAt]
  dsimp only [σ', τ', ContMDiffSection.coeFn_mk]
  abel

end CovariantDerivative
