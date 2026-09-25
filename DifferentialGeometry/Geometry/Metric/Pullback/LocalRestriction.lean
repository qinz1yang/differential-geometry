import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry
variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_restrictOpenOfSubset_eq
    (g : SmoothRiemannianMetric J N) {U V : Opens M} (hUV : U ≤ V)
    (f : V → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (fU : U → N) (hfU : IsLocalDiffeomorph I J ∞ fU)
    (heq : fU = f ∘ Opens.inclusion hUV) :
    (localPullMetric g f hf).restrictOpenOfSubset hUV = localPullMetric g fU hfU := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hinc : IsLocalDiffeomorph I I ∞ (Opens.inclusion hUV) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : U => hUV z.property)
      (isLocalDiffeomorph_subtype_val U y)
  have hd : mfderiv I J fU x = mfderiv I J f (Opens.inclusion hUV x) := by
    rw [heq, mfderiv_comp x (hf.contMDiff.mdifferentiableAt (by decide))
      (hinc.contMDiff.mdifferentiableAt (by decide)), mfderiv_opens_incl]
    exact ContinuousLinearMap.comp_id _
  change g.inner (f (Opens.inclusion hUV x))
    (mfderiv I J f (Opens.inclusion hUV x) v)
    (mfderiv I J f (Opens.inclusion hUV x) w) = _
  rw [localPullMetric_inner, hd, heq]
  rfl

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_restrictOpenOfSubset_eq_of_comp_eq
    (g : SmoothRiemannianMetric J N) {U V W : Opens M} (hWU : W ≤ U) (hWV : W ≤ V)
    (f : U → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (f' : V → N) (hf' : IsLocalDiffeomorph I J ∞ f')
    (heq : f ∘ Opens.inclusion hWU = f' ∘ Opens.inclusion hWV) :
    (localPullMetric g f hf).restrictOpenOfSubset hWU =
      (localPullMetric g f' hf').restrictOpenOfSubset hWV := by
  have hincU : IsLocalDiffeomorph I I ∞ (Opens.inclusion hWU) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : W => hWU z.property)
      (isLocalDiffeomorph_subtype_val W y)
  have hincV : IsLocalDiffeomorph I I ∞ (Opens.inclusion hWV) := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : W => hWV z.property)
      (isLocalDiffeomorph_subtype_val W y)
  rw [localPullMetric_restrictOpenOfSubset_eq g hWU f hf _
    (isLocalDiffeomorph_comp hf hincU) rfl,
    localPullMetric_restrictOpenOfSubset_eq g hWV f' hf' _
    (isLocalDiffeomorph_comp hf' hincV) rfl]
  congr 1

end DifferentialGeometry
