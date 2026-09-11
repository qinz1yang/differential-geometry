import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.ODE
  (curveAt_integralCurve integralCurve_eq_of_agree_zero)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalFlowMap_const
    (g : SmoothRiemannianMetric I M) (c sigma : Real)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g (ContMDiffMap.const c) sigma)
    (s : Real) (x : M) :
    canonicalFlowMap g (ContMDiffMap.const c) sigma hcomplete hsol s x = x := by
  have hcurve : IsMIntegralCurve (fun _ : Real => x)
      (fun y => gradFun (I := I) g (fun _ : M => c) y) := by
    exact isMIntegralCurve_const (gradFun_const g c x)
  have hcanonical : IsMIntegralCurve
      (fun r : Real => canonicalFlowMap g (ContMDiffMap.const c) sigma hcomplete hsol r x)
      (fun y => gradFun (I := I) g (fun _ : M => c) y) := by
    unfold canonicalFlowMap
    exact curveAt_integralCurve _ _ x
  have hregular :=
    (DifferentialGeometry.Geometry.Connection.gradFun_contMDiff_total_section
      g (ContMDiffMap.const (I := I) (I' := 𝓘(Real, Real)) c).contMDiff).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hinitial : canonicalFlowMap g (ContMDiffMap.const c) sigma hcomplete hsol 0 x = x :=
    congrFun (canonicalFlowMap_zero g (ContMDiffMap.const c) sigma hcomplete hsol) x
  exact congrFun (integralCurve_eq_of_agree_zero _ hregular hcanonical hcurve hinitial) s

theorem canonicalFlowDiffeomorph_const
    (g : SmoothRiemannianMetric I M) (c sigma : Real)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g (ContMDiffMap.const c) sigma)
    (s : Real) :
    canonicalFlowDiffeomorph g (ContMDiffMap.const c) sigma hcomplete hsol s =
      Diffeomorph.refl I M ∞ := by
  ext x
  rw [canonicalFlowDiffeomorph_apply, canonicalFlowMap_const]
  rfl

theorem canonicalMetric_const
    (g : SmoothRiemannianMetric I M) (c sigma : Real)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g (ContMDiffMap.const c) sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    canonicalMetric g (ContMDiffMap.const c) sigma hcomplete hsol ht =
      scaleMetric (1 - sigma * t) (mem_canonicalTimeDomain_iff.mp ht) g := by
  rw [canonicalMetric, canonicalFlowDiffeomorph_const, Diffeomorph.pullbackMetric_refl]

end DifferentialGeometry.PDE.RicciFlow.Soliton
