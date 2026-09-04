import DifferentialGeometry.Geometry.Exponential.NormalBall.Metric
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype
import DifferentialGeometry.Geometry.Geodesic.PullbackCross

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [T2Space (TangentBundle I M)]

namespace NormalBallChart

def inner {p : M} (c : NormalBallChart (I := I) p) : Opens E :=
  ⟨Metric.ball (0 : E) (c.radius / 4), Metric.isOpen_ball⟩

def innerImage {p : M} (c : NormalBallChart (I := I) p) : Opens M :=
  ⟨c.restrictBall '' (c.inner : Set E), image_opens_isOpen c.restrictBall
    (by
      convert! c.inner_subset using 1)⟩

noncomputable def innerDiffeo {p : M}
    (c : NormalBallChart (I := I) p) :
    Diffeomorph (modelWithCornersSelf Real E) I c.inner c.innerImage ∞ := by
  have hsub : (c.inner : Set E) ⊆ c.restrictBall.source := by
    convert! c.inner_subset using 1
  let V : Opens M :=
    ⟨c.restrictBall '' (c.inner : Set E), image_opens_isOpen c.restrictBall hsub⟩
  have hV : V = c.innerImage := by
    apply Opens.ext
    rfl
  rw [← hV]
  exact PartialDiffeomorph.toOpensDiffeo c.restrictBall hsub

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem innerSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.inner := by
  let : LocallyCompactSpace c.inner := c.inner.2.locallyCompactSpace
  infer_instance

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem innerImageSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.innerImage := by
  let : SigmaCompactSpace c.inner := c.innerSigma
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (c.innerDiffeo : c.inner → c.innerImage) = Set.univ :=
    Set.range_eq_univ.mpr c.innerDiffeo.surjective
  rw [← hrange]
  exact isSigmaCompact_range c.innerDiffeo.continuous

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem innerDiffeo_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : c.inner) :
    ((c.innerDiffeo z : c.innerImage) : M) = c.hom (z : E) := by
  change c.restrictBall (z : E) = c.hom (z : E)
  exact c.restrict_ball_apply (z : E)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem innerDiffeo_mfd {p : M}
    (c : NormalBallChart (I := I) p) (z : c.inner) (v : E) :
    mfderiv (modelWithCornersSelf Real E) I
        (c.innerDiffeo : c.inner → c.innerImage) z v =
      mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => c.hom u) (z : E) v := by
  have h := PartialDiffeomorph.mfderiv_toOpensDiffeo c.restrictBall
    (by
      convert! c.inner_subset using 1) z v
  convert! h using 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem metric_ext
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold (modelWithCornersSelf Real E) ∞ N]
    {g g' : SmoothRiemannianMetric (modelWithCornersSelf Real E) N}
    (h : ∀ (z : N) (v w : TangentSpace (modelWithCornersSelf Real E) z),
      g.inner z v w = g'.inner z v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun z => ContinuousLinearMap.ext fun v =>
      ContinuousLinearMap.ext fun w => h z v w
  subst hi
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_inner_eq
    (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    letI : SigmaCompactSpace c.inner := c.innerSigma
    letI : SigmaCompactSpace c.innerImage := c.innerImageSigma
    (c.totalMetric g).restrictOpen
        (I := modelWithCornersSelf Real E) c.inner =
      Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) c.innerImage) c.innerDiffeo := by
  let : SigmaCompactSpace c.inner := c.innerSigma
  let : SigmaCompactSpace c.innerImage := c.innerImageSigma
  apply metric_ext
  intro z v w
  let vE := tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersSelf Real E) z v
  let wE := tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersSelf Real E) z w
  have hv : (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z).symm vE = v := by
    exact ContinuousLinearEquiv.symm_apply_apply _ v
  have hw : (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z).symm wE = w := by
    exact ContinuousLinearEquiv.symm_apply_apply _ w
  rw [← hv, ← hw]
  have hleft :
      ((c.totalMetric g).restrictOpen
        (I := modelWithCornersSelf Real E) c.inner).inner z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm vE)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm wE) =
        c.metric g (z : E) vE wE := by
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      c.totalMetric_inner g (z : E) z.2 vE wE
  have hright :
      (Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) c.innerImage) c.innerDiffeo).inner z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm vE)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm wE) =
        c.metric g (z : E) vE wE := by
    rw [Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner, innerDiffeo_apply]
    rw [show mfderiv (modelWithCornersSelf Real E) I
        (c.innerDiffeo : c.inner → c.innerImage) z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm vE) =
        mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => c.hom u) (z : E) vE by
      simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        c.innerDiffeo_mfd z vE]
    rw [show mfderiv (modelWithCornersSelf Real E) I
        (c.innerDiffeo : c.inner → c.innerImage) z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm wE) =
        mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => c.hom u) (z : E) wE by
      simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        c.innerDiffeo_mfd z wE]
    exact c.metric_apply g (z : E) vE wE
  exact hleft.trans hright.symm

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cov_map_germ
    (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p)
    (V : ContMDiffSection (modelWithCornersSelf Real E) E
      (∞ : WithTop ℕ∞)
      (TangentSpace (modelWithCornersSelf Real E) : E → Type _))
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (z : c.inner) (v : E)
    (hEq :
      (fun u : E => Z (c.hom u)) =ᶠ[nhds (z : E)]
        (fun u : E =>
          mfderiv (modelWithCornersSelf Real E) I c.hom u (V u))) :
    mfderiv (modelWithCornersSelf Real E) I c.hom (z : E)
        (((DifferentialGeometry.Geometry.Curvature.metricCov
          (I := modelWithCornersSelf Real E) (M := E)
          (c.totalMetric g)).toFun (fun u : E => V u) (z : E)) v) =
      ((DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g).toFun
        (fun y : M => Z y) (c.hom (z : E)))
        (mfderiv (modelWithCornersSelf Real E) I c.hom (z : E) v) := by
  classical
  let : SigmaCompactSpace c.inner := c.innerSigma
  let : SigmaCompactSpace c.innerImage := c.innerImageSigma
  let U := c.inner
  let W := c.innerImage
  let Phi := c.innerDiffeo
  let VU := DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection
    (I := modelWithCornersSelf Real E) U V
  let PW := DifferentialGeometry.Geometry.Curvature.pushFwdSectionCross
    (I := modelWithCornersSelf Real E) (J := I) Phi VU
  have hback :
      Filter.Tendsto (fun a : W => ((Phi.symm a : U) : E))
        (nhds (Phi z)) (nhds (z : E)) := by
    have hc : ContinuousAt (fun a : W => ((Phi.symm a : U) : E))
        (Phi z) :=
      (continuous_subtype_val.comp Phi.symm.continuous).continuousAt
    have hz : ((Phi.symm (Phi z) : U) : E) = (z : E) := by
      simpa only using congrArg Subtype.val (Phi.symm_apply_apply z)
    rw [← hz]
    exact hc
  have hEqOpen :
      (fun y : W =>
        Geometry.Curvature.restrictOpenTangentSection (I := I) W Z y) =ᶠ[
          nhds (Phi z)]
        (fun y : W => PW y) := by
    filter_upwards [hback.eventually hEq] with a ha
    let u : U := Phi.symm a
    have hau : Phi u = a := Phi.apply_symm_apply a
    rw [← hau]
    simp only [PW, VU,
      Geometry.Curvature.restrictOpenTangentSection_apply,
      Geometry.Curvature.pushFwdSectionCross_apply_at_image]
    rw [c.innerDiffeo_apply u, c.innerDiffeo_mfd u (V (u : E))]
    exact ha
  have hres := Geometry.Curvature.metricCov_restrictOpen_globalSection
    (I := modelWithCornersSelf Real E) (c.totalMetric g) U V z v
  rw [c.totalMetric_inner_eq g] at hres
  have hpull := Geometry.Curvature.metricCov_pullbackCross
    (I := modelWithCornersSelf Real E) (J := I)
    (g.restrictOpen (I := I) W) Phi VU z v
  have hfield :
      (Geometry.Curvature.metricCov (I := I) (M := W)
        (g.restrictOpen (I := I) W)).toFun
          (Geometry.Curvature.restrictOpenTangentField (I := I) W
            (fun y : M => Z y)) (Phi z) =
        (Geometry.Curvature.metricCov (I := I) (M := W)
          (g.restrictOpen (I := I) W)).toFun
            (fun y : W => PW y) (Phi z) := by
    apply Geometry.Curvature.metricCov_congr_nhds
      (I := I) (M := W) (g.restrictOpen (I := I) W)
      (Geometry.Curvature.mdiffAt_restrictOpen_section (I := I) W Z (Phi z))
      (PW.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    convert! hEqOpen using 1
  have htgt := Geometry.Curvature.metricCov_restrictOpen_globalSection
    (I := I) g W Z (Phi z)
      (mfderiv (modelWithCornersSelf Real E) I (Phi : U → W) z v)
  have htoAmbient :
      ((Geometry.Curvature.metricCov (I := I) (M := W)
          (g.restrictOpen (I := I) W)).toFun
        (fun y : W => PW y) (Phi z))
        (mfderiv (modelWithCornersSelf Real E) I (Phi : U → W) z v) =
      ((Geometry.Curvature.metricCov (I := I) (M := M) g).toFun
        (fun y : M => Z y) (Phi z : M))
        (mfderiv (modelWithCornersSelf Real E) I (Phi : U → W) z v) := by
    rw [← hfield]
    exact htgt
  have hpbAmbient := htoAmbient
  rw [← hpull] at hpbAmbient
  have hleft := c.innerDiffeo_mfd z
    (((Geometry.Curvature.metricCov
      (I := modelWithCornersSelf Real E) (M := E)
      (c.totalMetric g)).toFun (fun u : E => V u) (z : E)) v)
  have hdir := c.innerDiffeo_mfd z v
  have hbase := c.innerDiffeo_apply z
  rw [← hleft, ← hres, ← hdir, ← hbase]
  exact hpbAmbient

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem geo_map (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p)
    (gamma : Real → E) (s : Set Real) (hs : IsOpen s)
    (hmem : ∀ t ∈ s, gamma t ∈ (c.inner : Set E))
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) ∞ gamma s)
    (hgeo : Geodesic.IsGeodesicOn (I := modelWithCornersSelf Real E)
      (c.totalMetric g) gamma s) :
    Geodesic.IsGeodesicOn (I := I) g (fun t ↦ c.hom (gamma t)) s := by
  classical
  let : SigmaCompactSpace c.inner := c.innerSigma
  let : SigmaCompactSpace c.innerImage := c.innerImageSigma
  let z0 : c.inner := ⟨0, by
    change (0 : E) ∈ Metric.ball (0 : E) (c.radius / 4)
    rw [Metric.mem_ball, dist_self]
    exact div_pos c.radius_pos (by norm_num)⟩
  let gammaQ : Real → c.inner := fun t ↦
    if ht : t ∈ s then ⟨gamma t, hmem t ht⟩ else z0
  have hval : ∀ t ∈ s, (gammaQ t : E) = gamma t := by
    intro t ht
    simp only [gammaQ, dif_pos ht]
  have hbaseSmooth : ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) ∞ (fun t ↦ (gammaQ t : E)) s :=
    hgamma.congr hval
  have hqSmooth : ContMDiffOn (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) ∞ gammaQ s := by
    intro t ht
    exact (codRestr_contMDiffAt
      (I := modelWithCornersSelf Real Real)
      (J := modelWithCornersSelf Real E)
      (V := c.inner) (f := fun r ↦ (gammaQ r : E))
      (fun r ↦ (gammaQ r).2)
      ((hbaseSmooth t ht).contMDiffAt (hs.mem_nhds ht))).contMDiffWithinAt
  have hqGeoAmbient : Geodesic.IsGeodesicOn
      (I := modelWithCornersSelf Real E) (c.totalMetric g)
      (fun t ↦ (gammaQ t : E)) s := by
    intro t ht
    have hev : (fun r ↦ (gammaQ r : E)) =ᶠ[nhds t] gamma :=
      Set.EqOn.eventuallyEq_of_mem hval (hs.mem_nhds ht)
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hval t ht) hev (hgeo t ht)
  have hqGeoRestr : Geodesic.IsGeodesicOn
      (I := modelWithCornersSelf Real E)
      ((c.totalMetric g).restrictOpen
        (I := modelWithCornersSelf Real E) c.inner) gammaQ s :=
    (Geodesic.geodesicOn_open_iff
      (I := modelWithCornersSelf Real E) (c.totalMetric g)
      c.inner gammaQ s).2 hqGeoAmbient
  rw [c.totalMetric_inner_eq g] at hqGeoRestr
  have hmapRestr := Geodesic.geodesicOn_mapLocal
    (I := modelWithCornersSelf Real E) (J := I)
    (g.restrictOpen (I := I) c.innerImage)
    c.innerDiffeo gammaQ s hs hqSmooth hqGeoRestr
  have hmapAmbient : Geodesic.IsGeodesicOn (I := I) g
      (fun t ↦ ((c.innerDiffeo (gammaQ t) : c.innerImage) : M)) s :=
    (Geodesic.geodesicOn_open_iff (I := I) g c.innerImage
      (fun t ↦ c.innerDiffeo (gammaQ t)) s).1 hmapRestr
  intro t ht
  have hev : (fun r ↦ c.hom (gamma r)) =ᶠ[nhds t]
      (fun r ↦ ((c.innerDiffeo (gammaQ r) : c.innerImage) : M)) := by
    filter_upwards [hs.mem_nhds ht] with r hr
    rw [← hval r hr]
    exact (c.innerDiffeo_apply (gammaQ r)).symm
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    hev.self_of_nhds hev (hmapAmbient t ht)

end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
