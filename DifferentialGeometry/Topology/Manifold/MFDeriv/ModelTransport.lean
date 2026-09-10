import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import DifferentialGeometry.Topology.Manifold.ContMDiff.Interior

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace Poincare.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [IsManifold I ∞ M]
  (e : E ≃L[𝕜] F)


theorem mfderiv_transContinuousLinearEquiv {f : M → G}
    (hf : ContMDiff I 𝓘(𝕜, G) ∞ f) {x : M} (hx : I.IsInteriorPoint x) :
    (show F →L[𝕜] G from mfderiv (I.transContinuousLinearEquiv e) 𝓘(𝕜, G) f x) =
      (show E →L[𝕜] G from mfderiv I 𝓘(𝕜, G) f x).comp e.symm.toContinuousLinearMap := by
  have hf' : ContMDiff (I.transContinuousLinearEquiv e) 𝓘(𝕜, G) ∞ f := by simpa using hf
  have hx' : (I.transContinuousLinearEquiv e).IsInteriorPoint x :=
    ((ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e (n := ∞)).isLocalDiffeomorph x).isInteriorPoint_iff (by simp) |>.mp hx
  have hg := contDiffAt_comp_extChartAt_symm_of_isInteriorPoint I hf hx
  erw [mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
    (I.transContinuousLinearEquiv e) (hf'.mdifferentiableAt (by simp)) hx',
    mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint
      I (hf.mdifferentiableAt (by simp)) hx]
  change fderiv 𝕜 ((fun y => f ((extChartAt I x).symm y)) ∘ e.symm)
    (e (extChartAt I x x)) = _
  rw [fderiv_comp _ (by simpa using hg.differentiableAt (by simp)) e.symm.differentiableAt,
    e.symm.fderiv, e.symm_apply_apply]

end Poincare.Manifold
