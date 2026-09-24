import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Bundle.TangentSpace

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lVelocity_comp_of_hasDerivAt
    {gamma : ℝ → M} {r : ℝ → ℝ} {u v : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (r u))
    (hr : HasDerivAt r v u) :
    lVelocity (I := I) (gamma ∘ r) u = v • lVelocity (I := I) gamma (r u) := by
  let A : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (r u) :=
    modelLinearMapToTangent (x := u) (y := r u)
      (A := ContinuousLinearMap.toSpanSingleton ℝ v)
  have hrM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r u A :=
    HasFDerivAt.hasMFDerivAt_model hr.hasFDerivAt
  have hcomp := hgamma.hasMFDerivAt.comp u hrM
  have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
  rw [tangentLinearMapToModel_comp] at hmodel
  have hA : tangentLinearMapToModel A = ContinuousLinearMap.toSpanSingleton ℝ v :=
    tangentLinearMapToModel_modelLinearMapToTangent
  rw [hA] at hmodel
  have happ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hmodel
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (gamma (r u))).injective
  have hscalar : (tangentLinearMapToModel (mfderiv 𝓘(ℝ, ℝ) I gamma (r u))) v =
      v • tangentLinearMapToModel (mfderiv 𝓘(ℝ, ℝ) I gamma (r u)) 1 := by
    let D := tangentLinearMapToModel (mfderiv 𝓘(ℝ, ℝ) I gamma (r u))
    exact (congrArg D (mul_one v).symm).trans (map_smul D v (1 : ℝ))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] at happ
  have h := happ.trans hscalar
  simpa only [lVelocity, tangentLinearMapToModel_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply, map_smul] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman
