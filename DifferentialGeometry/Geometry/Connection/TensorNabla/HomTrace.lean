import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Hom
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section

open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

section Identity

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem homBundleCovariantDerivativeGen_id
    (cov : CovariantDerivative I F V) :
    homBundleCovariantDerivativeGen I M F V F V cov cov
      (fun y => ContinuousLinearMap.id ℝ (V y)) = 0 := by
  funext x
  ext v w
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x w
  let Id : Cₛ^∞⟮I; F →L[ℝ] F, (fun y => V y →L[ℝ] V y)⟯ :=
    ⟨fun y => ContinuousLinearMap.id ℝ (V y), contMDiff_id.clm_bundle_id⟩
  have hh := homBundleCovariantDerivativeGen_apply I M F V F V cov cov Id Y x v
  change homBundleCovariantDerivativeGen I M F V F V cov cov
    (fun y => ContinuousLinearMap.id ℝ (V y)) x v (Y x) = cov Y x v - cov Y x v at hh
  simpa only [hY, sub_self, Pi.zero_apply, zero_apply] using hh

end Identity

private theorem hilbertSchmidtInner_id {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (A : W →L[ℝ] W) :
    ContinuousLinearMap.hilbertSchmidtInner A (ContinuousLinearMap.id ℝ W) =
      LinearMap.trace ℝ W A.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ W)]
  simp only [ContinuousLinearMap.hilbertSchmidtInner, ContinuousLinearMap.id_apply,
    real_inner_comm, ContinuousLinearMap.coe_coe]

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem mvfderiv_trace_of_isMetricCompatible
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    {A : ∀ y, V y →L[ℝ] V y} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, F →L[ℝ] F))
      (fun y => (⟨y, A y⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y => LinearMap.trace ℝ (V y) (A y).toLinearMap) x v =
      LinearMap.trace ℝ (V x)
        (homBundleCovariantDerivativeGen I M F V F V cov cov A x v).toLinearMap := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  have hId : MDifferentiableAt I (I.prod 𝓘(ℝ, F →L[ℝ] F))
      (fun y => (⟨y, ContinuousLinearMap.id ℝ (V y)⟩ : TotalSpace (F →L[ℝ] F)
        (fun y => V y →L[ℝ] V y))) x := mdifferentiableAt_id.clm_bundle_id
  have h := mvfderiv_hilbertSchmidtInner cov hcov cov hcov hA hId v
  dsimp only at h
  simp only [homBundleCovariantDerivativeGen_id, Pi.zero_apply, zero_apply,
    hilbertSchmidtInner_id] at h
  rw [show ContinuousLinearMap.hilbertSchmidtInner (A x) 0 = 0 by simp [ContinuousLinearMap.hilbertSchmidtInner]] at h
  simpa using h


end DifferentialGeometry.HomConnectionGen
