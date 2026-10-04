import DifferentialGeometry.Geometry.Connection.ConnectionForm.CurvatureOperator

set_option autoImplicit false

noncomputable section

open Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

open private bundleMapCovDeriv_curvature from
  DifferentialGeometry.Geometry.Connection.ConnectionForm.Curvature

@[simp]
theorem pullbackConnectionForm_id
    (C : E → E →L[ℝ] W →L[ℝ] W) :
    pullbackConnectionForm C id = C := by
  funext x
  simp only [pullbackConnectionForm, id_eq, fderiv_id, ContinuousLinearMap.comp_id]

theorem pullbackConnectionForm_comp
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (C : E → E →L[ℝ] W →L[ℝ] W) {F : V → E} {G : U → V} {x : U}
    (hF : DifferentiableAt ℝ F (G x)) (hG : DifferentiableAt ℝ G x) :
    pullbackConnectionForm C (F ∘ G) x =
      pullbackConnectionForm (pullbackConnectionForm C F) G x := by
  simp only [pullbackConnectionForm, fderiv_comp x hF hG, Function.comp_apply,
    ContinuousLinearMap.comp_assoc]

theorem pullbackConnectionForm_contDiffAt
    {n : ℕ∞ω} {C : E → E →L[ℝ] W →L[ℝ] W} {F : V → E} {x : V}
    (hC : ContDiffAt ℝ n C (F x)) (hF : ContDiffAt ℝ (n + 1) F x) :
    ContDiffAt ℝ n (pullbackConnectionForm C F) x :=
  (hC.comp x (hF.of_le (le_add_of_nonneg_right zero_le_one))).clm_comp
    (hF.fderiv_right (le_refl _))

theorem connectionFormCurvatureCLM_intertwines_of_parallel
    {A : V → V →L[ℝ] E →L[ℝ] E} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → E →L[ℝ] W} {x : V}
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x)
    (hJ : ContDiffAt ℝ 2 J x)
    (hparallel : ∀ᶠ y in 𝓝 x, ∀ X u, bundleMapCovDeriv A C J y X u = 0)
    (X Y : V) :
    (connectionFormCurvatureCLM C x X Y).comp (J x) =
      (J x).comp (connectionFormCurvatureCLM A x X Y) := by
  have hp := hparallel.self_of_nhds
  have hzero (Z v : V) (u : E) :
      connectionFormCovDeriv C (fun y => bundleMapCovDeriv A C J y Z u) v x = 0 := by
    have heq : (fun y => bundleMapCovDeriv A C J y Z u) =ᶠ[𝓝 x] (fun _ => 0) :=
      hparallel.mono (fun y hy => hy Z u)
    have hd : fderiv ℝ (fun y => bundleMapCovDeriv A C J y Z u) x = 0 :=
      heq.fderiv_eq.trans (fderiv_const_apply (0 : W))
    simp only [connectionFormCovDeriv, hd, hp, zero_apply, map_zero, add_zero]
  ext u
  have h := bundleMapCovDeriv_curvature hA hC hJ X Y u
  simp only [ContinuousLinearMap.comp_apply, connectionFormCurvatureCLM_apply]
  simpa only [hp, hzero, add_zero, sub_zero] using h

end DifferentialGeometry.Geometry.Connection
