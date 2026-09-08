import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Metric.Pullback.Product

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Soliton
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.ODE (curveAt_integralCurve integralCurve_eq_of_agree_zero)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G} [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

theorem canonicalFlowMap_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (σ : Real)
    (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hsolg : gradientRicciSoliton g f σ) (hsolh : gradientRicciSoliton h k σ)
    (s : Real) (x : M × N) :
    canonicalFlowMap (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ
      (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) s x =
      (canonicalFlowMap g f σ hg hsolg s x.1, canonicalFlowMap h k σ hh hsolh s x.2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompleteSpace F := FiniteDimensional.complete Real F
  let u := f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd
  let V := fun q : M × N => gradFun (g.prod h) u q
  have hcurve : IsMIntegralCurve
      (fun r : Real => (canonicalFlowMap g f σ hg hsolg r x.1,
        canonicalFlowMap h k σ hh hsolh r x.2)) V := by
    intro r
    have h₁ : IsMIntegralCurve (fun r : Real => canonicalFlowMap g f σ hg hsolg r x.1)
        (fun y => gradFun g f y) := by
      unfold canonicalFlowMap
      exact curveAt_integralCurve _ _ x.1
    have h₂ : IsMIntegralCurve (fun r : Real => canonicalFlowMap h k σ hh hsolh r x.2)
        (fun y => gradFun h k y) := by
      unfold canonicalFlowMap
      exact curveAt_integralCurve _ _ x.2
    have hc := (h₁ r).prodMk (h₂ r)
    have hgrad := gradFun_prod g h f k
      (canonicalFlowMap g f σ hg hsolg r x.1, canonicalFlowMap h k σ hh hsolh r x.2)
    change gradFun (g.prod h) u _ = _ at hgrad
    dsimp only [IsMIntegralCurve, V]
    rw [hgrad]
    have hclm : (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
        (gradFun g f (canonicalFlowMap g f σ hg hsolg r x.1),
          gradFun h k (canonicalFlowMap h k σ hh hsolh r x.2))) =
      (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
        (gradFun g f (canonicalFlowMap g f σ hg hsolg r x.1))).prod
      (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
        (gradFun h k (canonicalFlowMap h k σ hh hsolh r x.2))) := by
      rfl
    erw [hclm]
    exact hc
  have hcanonical : IsMIntegralCurve
      (fun r : Real => canonicalFlowMap (g.prod h) u σ
        (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) r x) V := by
    unfold canonicalFlowMap
    exact curveAt_integralCurve _ _ x
  have hregular := (DifferentialGeometry.Geometry.Connection.gradFun_contMDiff_total_section
    (g.prod h) u.contMDiff).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hinitial : canonicalFlowMap (g.prod h) u σ
      (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) 0 x =
      (canonicalFlowMap g f σ hg hsolg 0 x.1, canonicalFlowMap h k σ hh hsolh 0 x.2) := by
    simp only [canonicalFlowMap_zero]
    rfl
  exact congrFun (integralCurve_eq_of_agree_zero _ hregular hcanonical hcurve hinitial) s

theorem canonicalFlowDiffeomorph_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (σ : Real)
    (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hsolg : gradientRicciSoliton g f σ) (hsolh : gradientRicciSoliton h k σ)
    (s : Real) :
    canonicalFlowDiffeomorph (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ
      (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) s =
      (canonicalFlowDiffeomorph g f σ hg hsolg s).prodCongr
        (canonicalFlowDiffeomorph h k σ hh hsolh s) := by
  apply Diffeomorph.ext
  intro x
  change canonicalFlowDiffeomorph (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ
      (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) s x =
    (canonicalFlowDiffeomorph g f σ hg hsolg s x.1,
      canonicalFlowDiffeomorph h k σ hh hsolh s x.2)
  simp only [canonicalFlowDiffeomorph_apply]
  exact canonicalFlowMap_prod g h f k σ hg hh hsolg hsolh s x

theorem canonicalMetric_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (σ : Real)
    (hg : RiemannianMetricComplete g) (hh : RiemannianMetricComplete h)
    (hsolg : gradientRicciSoliton g f σ) (hsolh : gradientRicciSoliton h k σ)
    {t : Real} (ht : t ∈ canonicalTimeDomain σ) :
    canonicalMetric (g.prod h)
      (f.comp ContMDiffMap.fst + k.comp ContMDiffMap.snd) σ
      (RiemannianMetricComplete.prod hg hh) (gradientRicciSoliton_prod hsolg hsolh) ht =
      (canonicalMetric g f σ hg hsolg ht).prod (canonicalMetric h k σ hh hsolh ht) := by
  have hscale : scaleMetric (1 - σ * t) (mem_canonicalTimeDomain_iff.mp ht) (g.prod h) =
      (scaleMetric (1 - σ * t) (mem_canonicalTimeDomain_iff.mp ht) g).prod
        (scaleMetric (1 - σ * t) (mem_canonicalTimeDomain_iff.mp ht) h) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner, SmoothRiemannianMetric.prod_inner,
      SmoothRiemannianMetric.prod_inner, scaleMetric_inner, scaleMetric_inner]
    ring
  rw [canonicalMetric, canonicalFlowDiffeomorph_prod, hscale,
    Diffeomorph.pullbackMetric_prodCongr]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Soliton
