import DifferentialGeometry.Geometry.Connection.ConnectionForm.CurvatureBounds
import DifferentialGeometry.Geometry.Connection.ConnectionForm.FiniteRegularity

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def connectionFormCurvatureCLM (A : V → V →L[ℝ] E →L[ℝ] E) (x : V) :
    V →L[ℝ] V →L[ℝ] E →L[ℝ] E :=
  let C := (ContinuousLinearMap.compL ℝ E E E).bilinearComp (A x) (A x)
  fderiv ℝ A x - (fderiv ℝ A x).flip + C - C.flip

@[simp]
theorem connectionFormCurvatureCLM_apply
    (A : V → V →L[ℝ] E →L[ℝ] E) (x X Y : V) (u : E) :
    connectionFormCurvatureCLM A x X Y u = connectionFormCurvature A x X Y u := rfl

@[simp]
theorem connectionFormCurvatureCLM_flip
    (A : V → V →L[ℝ] E →L[ℝ] E) (x : V) :
    (connectionFormCurvatureCLM A x).flip = -connectionFormCurvatureCLM A x := by
  ext X Y u
  simp only [ContinuousLinearMap.flip_apply, neg_apply, connectionFormCurvatureCLM_apply,
    connectionFormCurvature]
  abel

theorem connectionFormCurvatureCLM_contDiffAt
    {n : ℕ∞ω} {A : V → V →L[ℝ] E →L[ℝ] E} {x : V}
    (hA : ContDiffAt ℝ (n + 1) A x) :
    ContDiffAt ℝ n (connectionFormCurvatureCLM A) x := by
  have hD : ContDiffAt ℝ n (fderiv ℝ A) x := hA.fderiv_right (le_refl _)
  have hA' : ContDiffAt ℝ n A x := hA.of_le (le_add_of_nonneg_right (by simp))
  let L : (V →L[ℝ] V →L[ℝ] E →L[ℝ] E) ≃ₗᵢ[ℝ]
      (V →L[ℝ] V →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.flipₗᵢ ℝ V V (E →L[ℝ] E)
  let K : (V →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E) ≃ₗᵢ[ℝ]
      ((E →L[ℝ] E) →L[ℝ] V →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.flipₗᵢ ℝ V (E →L[ℝ] E) (E →L[ℝ] E)
  have hfirst := (contDiffAt_const.clm_comp hA' :
    ContDiffAt ℝ n (fun y => (ContinuousLinearMap.compL ℝ E E E).comp (A y)) x)
  have hflipped := K.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hfirst
  have hcomposed := hflipped.clm_comp hA'
  have hC := L.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hcomposed
  have hDf := L.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hD
  have hCf := L.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hC
  exact ((hD.sub hDf).add hC).sub hCf

theorem norm_connectionFormCurvatureCLM_le
    (A : V → V →L[ℝ] E →L[ℝ] E) (x : V) :
    ‖connectionFormCurvatureCLM A x‖ ≤ 2 * ‖fderiv ℝ A x‖ + 2 * ‖A x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro Y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  exact norm_connectionFormCurvature_le A x X Y u

theorem norm_connectionFormCurvatureCLM_sub_le
    (A B : V → V →L[ℝ] E →L[ℝ] E) (x : V) :
    ‖connectionFormCurvatureCLM A x - connectionFormCurvatureCLM B x‖ ≤
      2 * ‖fderiv ℝ A x - fderiv ℝ B x‖ +
        2 * (‖A x‖ + ‖B x‖) * ‖A x - B x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro Y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  exact norm_connectionFormCurvature_sub_le A B x X Y u

theorem connectionFormCurvatureCLM_pullback
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {C : E → E →L[ℝ] W →L[ℝ] W} {F : V → E} {x : V}
    (hC : DifferentiableAt ℝ C (F x)) (hF : ContDiffAt ℝ 2 F x) :
    connectionFormCurvatureCLM (pullbackConnectionForm C F) x =
      (connectionFormCurvatureCLM C (F x)).bilinearComp (fderiv ℝ F x) (fderiv ℝ F x) := by
  ext X Y u
  exact connectionFormCurvature_pullback hC hF X Y u

end DifferentialGeometry.Geometry.Connection
