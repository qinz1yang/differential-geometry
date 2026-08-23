import DifferentialGeometry.Analysis.ODE.TubeStability
import DifferentialGeometry.Geometry.Comparison.CGTConvexity
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Geodesic.LocalIsometry
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrPullBall (E := E) R).isOpen)

noncomputable def intrCut (R : Real) (hR : 0 < R) :
    ContDiffBump (0 : E) :=
  ⟨3 * R / 4, 7 * R / 8, by linarith, by linarith⟩

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_smooth (R : Real) (hR : 0 < R) :
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (intrCut (E := E) R hR : E → Real) :=
  (intrCut (E := E) R hR).contDiff.contMDiff

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_range (R : Real) (hR : 0 < R) (z : E) :
    intrCut (E := E) R hR z ∈ Set.Icc (0 : Real) 1 :=
  ⟨(intrCut (E := E) R hR).nonneg,
    (intrCut (E := E) R hR).le_one⟩

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_support (R : Real) (hR : 0 < R) :
    tsupport (intrCut (E := E) R hR : E → Real) ⊆
      (intrPullBall (E := E) R : Set E) := by
  rw [(intrCut (E := E) R hR).tsupport_eq]
  change Metric.closedBall (0 : E) (7 * R / 8) ⊆
    Metric.ball (0 : E) R
  exact Metric.closedBall_subset_ball (by linarith)

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_compact (R : Real) (hR : 0 < R) :
    IsCompact (tsupport (intrCut (E := E) R hR : E → Real)) := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  rw [(intrCut (E := E) R hR).tsupport_eq]
  exact isCompact_closedBall (0 : E) (7 * R / 8)

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_one (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (3 * R / 4)) :
    intrCut (E := E) R hR z = 1 :=
  (intrCut (E := E) R hR).one_of_mem_closedBall
    (Metric.ball_subset_closedBall hz)

omit [NeZero (Module.finrank Real E)] in
theorem intrCut_one_closed (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    intrCut (E := E) R hR z = 1 :=
  (intrCut (E := E) R hR).one_of_mem_closedBall hz

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrInner_subset (R : Real) (hR : 0 < R) :
    Metric.ball (0 : E) (3 * R / 4) ⊆
      (intrPullBall (E := E) R : Set E) :=
  Metric.ball_subset_ball (by linarith)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrClosed_subset (R : Real) (hR : 0 < R) :
    Metric.closedBall (0 : E) (3 * R / 4) ⊆
      (intrPullBall (E := E) R : Set E) :=
  Metric.closedBall_subset_ball (by linarith)

def intrAgree (R : Real) : Opens (intrPullBall (E := E) R) :=
  ⟨Subtype.val ⁻¹' Metric.ball (0 : E) (3 * R / 4),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrAgree (E := E) R).isOpen)

noncomputable def intrExtMetric
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) E :=
  (flatModelMetric E).bumpExtendOpen
    (intrPullBall (E := E) R)
    (intrPullMetric (I := I) g hEnorm p hloc)
    (intrCut (E := E) R hR : E → Real)
    (intrCut_smooth (E := E) R hR)
    (intrCut_range (E := E) R hR)
    (intrCut_support (E := E) R hR)

theorem intrExt_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4))
    (v w : E) :
    (intrExtMetric (I := I) g hEnorm p hR hloc).inner z v w =
      (intrPullMetric (I := I) g hEnorm p hloc).inner
        ⟨z, intrClosed_subset (E := E) R hR hz⟩ v w := by
  simpa only [intrExtMetric] using
    bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
      (flatModelMetric E) (intrPullBall (E := E) R)
      (intrPullMetric (I := I) g hEnorm p hloc)
      (intrCut (E := E) R hR : E → Real)
      (intrCut_smooth (E := E) R hR)
      (intrCut_range (E := E) R hR)
      (intrCut_support (E := E) R hR)
      (Metric.closedBall (0 : E) (3 * R / 4))
      (fun z hz => intrCut_one_closed (E := E) R hR hz)
      (intrClosed_subset (E := E) R hR) z hz v w

theorem intrExt_restrict
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ((intrExtMetric (I := I) g hEnorm p hR hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrPullBall (E := E) R)).restrictOpen
          (I := 𝓘(Real, E)) (intrAgree (E := E) R) =
      (intrPullMetric (I := I) g hEnorm p hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrAgree (E := E) R) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  have hz :
      ((z : intrPullBall (E := E) R) : E) ∈
        Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall z.2
  simpa only using
    intrExt_inner (I := I) g hEnorm p hR hloc hz v w

theorem intrPull_geo_of_ext
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s, ‖((γ t : intrPullBall (E := E) R) : E)‖ <
      3 * R / 4)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrPullBall (E := E) R) : E)) s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (intrPullMetric (I := I) g hEnorm p hloc) γ s := by
  classical
  let U := intrPullBall (E := E) R
  let V := intrAgree (E := E) R
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  let z₀ : V :=
    ⟨intrZero (E := E) hR, by
      change (0 : E) ∈ Metric.ball (0 : E) (3 * R / 4)
      simpa only [Metric.mem_ball, dist_self] using
        (show 0 < 3 * R / 4 by positivity)⟩
  let γV : Real → V := fun t =>
    if ht : γ t ∈ V then ⟨γ t, ht⟩ else z₀
  have hmem : ∀ t ∈ s, γ t ∈ V := by
    intro t ht
    change ((γ t : intrPullBall (E := E) R) : E) ∈
      Metric.ball (0 : E) (3 * R / 4)
    simpa only [Metric.mem_ball, dist_zero_right] using hstay t ht
  have heq : ∀ t ∈ s,
      (fun r => ((γV r : V) : U)) =ᶠ[𝓝 t] γ := by
    intro t ht
    have hpre : γ ⁻¹' (V : Set U) ∈ 𝓝 t :=
      hγ.continuous.continuousAt
        (V.isOpen.mem_nhds (hmem t ht))
    filter_upwards [hpre] with r hr
    change γ r ∈ V at hr
    simp only [γV, dif_pos hr]
  have hgeoU :
      IsGeodesicOn (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U) γ s := by
    exact (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) gExt U γ s).2 hgeo
  have hgeoUV :
      IsGeodesicOn (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U)
        (fun t => ((γV t : V) : U)) s := by
    intro t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (heq t ht).eq_of_nhds (heq t ht) (hgeoU t ht)
  have hgeoV :
      IsGeodesicOn (I := 𝓘(Real, E))
        ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
          (I := 𝓘(Real, E)) V) γV s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E))
      (gExt.restrictOpen (I := 𝓘(Real, E)) U) V γV s).2 hgeoUV
  have hgeoV' := hgeoV
  rw [show
    ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
        (I := 𝓘(Real, E)) V) =
      gPull.restrictOpen (I := 𝓘(Real, E)) V by
        simpa only [U, V, gExt, gPull] using
          intrExt_restrict (I := I) g hEnorm p hR hloc] at hgeoV'
  have hgeoPullV :
      IsGeodesicOn (I := 𝓘(Real, E)) gPull
        (fun t => ((γV t : V) : U)) s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) gPull V γV s).1 hgeoV'
  intro t ht
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (heq t ht).eq_of_nhds.symm (heq t ht).symm (hgeoPullV t ht)

theorem intrExt_geo_of_pull
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s, ‖((γ t : intrPullBall (E := E) R) : E)‖ <
      3 * R / 4)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) γ s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (intrExtMetric (I := I) g hEnorm p hR hloc)
      (fun t => ((γ t : intrPullBall (E := E) R) : E)) s := by
  classical
  let U := intrPullBall (E := E) R
  let V := intrAgree (E := E) R
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  let z₀ : V :=
    ⟨intrZero (E := E) hR, by
      change (0 : E) ∈ Metric.ball (0 : E) (3 * R / 4)
      simpa only [Metric.mem_ball, dist_self] using
        (show 0 < 3 * R / 4 by positivity)⟩
  let γV : Real → V := fun t =>
    if ht : γ t ∈ V then ⟨γ t, ht⟩ else z₀
  have hmem : ∀ t ∈ s, γ t ∈ V := by
    intro t ht
    change ((γ t : intrPullBall (E := E) R) : E) ∈
      Metric.ball (0 : E) (3 * R / 4)
    simpa only [Metric.mem_ball, dist_zero_right] using hstay t ht
  have heq : ∀ t ∈ s,
      (fun r => ((γV r : V) : U)) =ᶠ[𝓝 t] γ := by
    intro t ht
    have hpre : γ ⁻¹' (V : Set U) ∈ 𝓝 t :=
      hγ.continuous.continuousAt
        (V.isOpen.mem_nhds (hmem t ht))
    filter_upwards [hpre] with r hr
    change γ r ∈ V at hr
    simp only [γV, dif_pos hr]
  have hgeoPullV :
      IsGeodesicOn (I := 𝓘(Real, E)) gPull
        (fun t => ((γV t : V) : U)) s := by
    intro t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (heq t ht).eq_of_nhds (heq t ht) (hgeo t ht)
  have hgeoV :
      IsGeodesicOn (I := 𝓘(Real, E))
        (gPull.restrictOpen (I := 𝓘(Real, E)) V) γV s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) gPull V γV s).2 hgeoPullV
  have hgeoV' := hgeoV
  rw [show
    gPull.restrictOpen (I := 𝓘(Real, E)) V =
      (gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
        (I := 𝓘(Real, E)) V by
      simpa only [U, V, gExt, gPull] using
        (intrExt_restrict (I := I) g hEnorm p hR hloc).symm] at hgeoV'
  have hgeoExtU :
      IsGeodesicOn (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U)
        (fun t => ((γV t : V) : U)) s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E))
      (gExt.restrictOpen (I := 𝓘(Real, E)) U) V γV s).1 hgeoV'
  have hgeoExt :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt
        (fun t => (((γV t : V) : U) : E)) s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) gExt U
      (fun t => ((γV t : V) : U)) s).1 hgeoExtU
  intro t ht
  have heqE :
      (fun r => (((γV r : V) : U) : E)) =ᶠ[𝓝 t]
        (fun r => ((γ r : U) : E)) :=
    (heq t ht).fun_comp (fun z : U => (z : E))
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    heqE.eq_of_nhds.symm heqE.symm (hgeoExt t ht)

theorem intrExt_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {γ : Real → E} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
      (Set.Icc a b))
    (hstay : ∀ t ∈ Set.Icc a b,
      γ t ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) γ a b =
      Manifold.pathELength I
        ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  change Manifold.pathELength 𝓘(Real, E) γ a b =
    Manifold.pathELength I
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t
      ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
  have hFt : MDifferentiableAt 𝓘(Real, E) I
      (intrinsicFramedExp (I := I) g hEnorm p) (γ t) :=
    (intrFrame_smooth (I := I) g hEnorm p).mdifferentiableAt
      (by decide)
  have hcomp :
      mfderiv 𝓘(Real, Real) I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) t =
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t)).comp
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t) :=
    mfderiv_comp t hFt hγt
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, Real) I
        ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) t 1‖ₑ
  rw [hcomp]
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (γ t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1)‖ₑ
  let v : TangentSpace 𝓘(Real, E) (γ t) :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1
  have hExtNorm :
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner (γ t) v v)) := by
    simpa only using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt (γ t) v)
  have hBaseNorm :
      ‖mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v‖ₑ =
        ENNReal.ofReal (Real.sqrt
          (g.inner (intrinsicFramedExp (I := I) g hEnorm p (γ t))
            (mfderiv 𝓘(Real, E) I
              (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v)
            (mfderiv 𝓘(Real, E) I
              (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v))) :=
    hEnorm _ _
  change ‖v‖ₑ = ‖mfderiv 𝓘(Real, E) I
    (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v‖ₑ
  rw [hExtNorm, hBaseNorm]
  congr 2
  calc
    gExt.inner (γ t) v v =
        (intrPullMetric (I := I) g hEnorm p hloc).inner
          ⟨γ t, intrClosed_subset (E := E) R hR
            (hstay t ⟨ht.1.le, ht.2.le⟩)⟩ v v :=
      intrExt_inner (I := I) g hEnorm p hR hloc
        (hstay t ⟨ht.1.le, ht.2.le⟩) v v
    _ = intrFrameMetric (I := I) g hEnorm p (γ t) v v :=
      intrPullMetric_inner (I := I) g hEnorm p hloc _ v v
    _ = g.inner
        (intrinsicFramedExp (I := I) g hEnorm p (γ t))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v)
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v) := by
      rw [intrFrameMetric_apply]

theorem intrExt_radial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ ≤ 3 * R / 4) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun t : Real => Real.smoothTransition t • z) 0 1 =
      ENNReal.ofReal ‖z‖ := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  let γ : Real → E := fun t => Real.smoothTransition t • z
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    intro t
    rw [contMDiffAt_iff_contDiffAt]
    exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
  have hγone : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
      (Set.Icc (0 : Real) 1) :=
    (hγinf.of_le (by norm_num)).contMDiffOn
  have hstay : ∀ t ∈ Set.Icc (0 : Real) 1,
      γ t ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro t _
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖Real.smoothTransition t • z‖ ≤ 3 * R / 4
    rw [norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg z)
        (Real.smoothTransition.le_one t)).trans hz
  have hext :
      Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) 0 1 := by
    simpa only [gExt] using
      (intrExt_pathLen (I := I) g hEnorm p hR hloc hγone hstay)
  let zU : intrPullBall (E := E) R :=
    ⟨z, intrClosed_subset (E := E) R hR (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz)⟩
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have hradC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
        (intrRadial (E := E) zU) (Set.Icc (0 : Real) 1) :=
    ((intrRadial_smooth (E := E) zU).of_le (by norm_num)).contMDiffOn
  have hpull :=
    intrPull_pathLen (I := I) g hEnorm p hloc hradC1
  have hrad :=
    intrRadial_len (I := I) g hEnorm p hloc zU
  calc
    Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) 0 1 := hext
    _ = Manifold.pathELength 𝓘(Real, E)
        (intrRadial (E := E) zU) 0 1 := by
      simpa only [γ, zU, intrRadial, intrExpOn, Function.comp_apply] using hpull
    _ = ENNReal.ofReal ‖z‖ := by
      simpa only [zU] using hrad

theorem intrExt_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (ha : a ≤ 3 * R / 4) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) x y ≤
      ENNReal.ofReal (2 * a) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E :=
    ⟨fun _ _ => rfl⟩
  change Manifold.riemannianEDist 𝓘(Real, E) x y ≤
    ENNReal.ofReal (2 * a)
  have hdist_zero :
      ∀ z : E, ‖z‖ ≤ 3 * R / 4 →
        Manifold.riemannianEDist 𝓘(Real, E) 0 z ≤
          ENNReal.ofReal ‖z‖ := by
    intro z hz
    let γz : Real → E := fun t => Real.smoothTransition t • z
    have hγzinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γz := by
      intro t
      rw [contMDiffAt_iff_contDiffAt]
      exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
    have hγz :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γz
          (Set.Icc (0 : Real) 1) :=
      (hγzinf.of_le (by norm_num)).contMDiffOn
    have hdist :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := (0 : E)) (y := z)
        hγz (by
          simp only [γz, Real.smoothTransition.zero_of_nonpos le_rfl,
            zero_smul])
        (by
          simp only [γz, Real.smoothTransition.one_of_one_le le_rfl,
            one_smul])
        zero_le_one
    rw [intrExt_radial_len (I := I) g hEnorm p hR hloc hz] at hdist
    exact hdist
  have hx_inner : ‖x‖ ≤ 3 * R / 4 := hx.trans ha
  have hy_inner : ‖y‖ ≤ 3 * R / 4 := hy.trans ha
  calc
    Manifold.riemannianEDist 𝓘(Real, E) x y ≤
        Manifold.riemannianEDist 𝓘(Real, E) x 0 +
          Manifold.riemannianEDist 𝓘(Real, E) 0 y :=
      Manifold.riemannianEDist_triangle
    _ = Manifold.riemannianEDist 𝓘(Real, E) 0 x +
          Manifold.riemannianEDist 𝓘(Real, E) 0 y := by
      rw [Manifold.riemannianEDist_comm]
    _ ≤ ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖y‖ :=
      add_le_add (hdist_zero x hx_inner) (hdist_zero y hy_inner)
    _ = ENNReal.ofReal (‖x‖ + ‖y‖) :=
      (ENNReal.ofReal_add (norm_nonneg x) (norm_nonneg y)).symm
    _ ≤ ENNReal.ofReal (2 * a) := by
      exact ENNReal.ofReal_le_ofReal (by linarith)

theorem intrExt_complete
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    RiemannianMetricComplete (I := 𝓘(Real, E))
      (intrExtMetric (I := I) g hEnorm p hR hloc) := by
  simpa only [intrExtMetric] using
    RiemannianMetricComplete.bumpExtend_complete
      (I := 𝓘(Real, E)) (flatModelMetric E)
      (RiemannianMetricComplete.flatModel_complete (E := E))
      (intrPullBall (E := E) R)
      (intrPullMetric (I := I) g hEnorm p hloc)
      (intrCut (E := E) R hR : E → Real)
      (intrCut_smooth (E := E) R hR)
      (intrCut_range (E := E) R hR)
      (intrCut_support (E := E) R hR)
      (intrCut_compact (E := E) R hR)

noncomputable def intrExtJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) : Real → E := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  exact minJoin (I := 𝓘(Real, E)) gExt hExt x y

@[simp] theorem intrExtJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrExtJoin (I := I) g hEnorm p hR hloc x y 0 = x := by
  simp only [intrExtJoin, minJoin_zero]

@[simp] theorem intrExtJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrExtJoin (I := I) g hEnorm p hR hloc x y 1 = y := by
  simp only [intrExtJoin, minJoin_one]

theorem intrExtJoin_smooth
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (intrExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  simpa only [intrExtJoin, gExt] using
    intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

theorem intrExtJoin_geo
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    IsGeodesic (I := 𝓘(Real, E))
      (intrExtMetric (I := I) g hEnorm p hR hloc)
      (intrExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  simpa only [intrExtJoin, gExt, minJoin] using
    intrinsicGeodesic_isGeodesic
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

private theorem intrExtJoin_budget
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hL : 0 ≤ L)
    (hdist :
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) x y ≤
          ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtJoin (I := I) g hEnorm p hR hloc x y t‖ <
        3 * R / 4 := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  have hγinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  have hγcont : Continuous γ := hγinf.continuous
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haB : a < 3 * R / 4 := by linarith
  have haInner : a ≤ 3 * R / 4 := haB.le
  have hdist' :
      Manifold.riemannianEDist 𝓘(Real, E) x y ≤
        ENNReal.ofReal L := by
    simpa only [gExt, riemannianEDistOf] using hdist
  have hdist_top :
      Manifold.riemannianEDist 𝓘(Real, E) x y ≠
        (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist'
  have hfull :
      Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        ENNReal.ofReal
          ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := by
    simpa only [γ] using
      (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt x y)
  intro t ht
  by_contra hnot
  have hcross :
      3 * R / 4 ≤ ‖γ t‖ := by
    simpa only [γ, intrExtJoin] using (not_lt.mp hnot)
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    simpa only [γ, minJoin_zero] using hx.trans_lt haB
  obtain ⟨τ, hτ, hτeq, hbefore⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc
      zero_le_one hγcont.norm.continuousOn hstart ⟨t, ht, hcross⟩
  have hτ0 : 0 ≤ τ := hτ.1
  let f : Real → Real := fun s => τ * Real.smoothTransition s
  have hfIcc : ∀ s : Real, f s ∈ Set.Icc (0 : Real) τ := by
    intro s
    dsimp only [f]
    constructor
    · exact mul_nonneg hτ0 (Real.smoothTransition.nonneg s)
    · nlinarith [Real.smoothTransition.nonneg s,
        Real.smoothTransition.le_one s]
  let η : Real → E := γ ∘ f
  have hηinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
    apply hγinf.comp
    rw [contMDiff_iff_contDiff]
    dsimp only [f]
    fun_prop
  have hηstay :
      ∀ s : Real, η s ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbefore (f s) (hfIcc s)
  have hηmem : ∀ s : Real, η s ∈ intrPullBall (E := E) R := by
    intro s
    exact intrClosed_subset (E := E) R hR (hηstay s)
  let ηU : Real → intrPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := intrPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
        (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
        (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  let xU : intrPullBall (E := E) R :=
    ⟨x, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : intrPullBall (E := E) R :=
    ⟨γ τ, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hη0 : η 0 = x := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, γ,
      minJoin_zero]
  have hη1 : η 1 = γ τ := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have hηU0 : ηU 0 = xU := by
    apply Subtype.ext
    exact hη0
  have hηU1 : ηU 1 = zU := by
    apply Subtype.ext
    exact hη1
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen :
      Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    simpa only [ηU, intrExpOn, Function.comp_apply] using
      (intrPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen :
      Manifold.pathELength 𝓘(Real, E) η 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (intrExt_pathLen (I := I) g hEnorm p hR hloc hηC1
        (fun s _ => hηstay s))
  have hmonoF : MonotoneOn f (Set.Icc (0 : Real) 1) := by
    intro s _ u _ hsu
    dsimp only [f]
    exact mul_le_mul_of_nonneg_left
      (Real.smoothTransition.monotone hsu) hτ0
  have hfDiff : DifferentiableOn Real f (Set.Icc (0 : Real) 1) := by
    dsimp only [f]
    exact
      ((contDiff_const.mul (Real.smoothTransition.contDiff (n := 1))).differentiable
        one_ne_zero).differentiableOn
  have hηPrefix :
      Manifold.pathELength 𝓘(Real, E) η 0 1 =
        Manifold.pathELength 𝓘(Real, E) γ 0 τ := by
    convert Manifold.pathELength_comp_of_monotoneOn
      (I := 𝓘(Real, E)) (γ := γ) (f := f)
      (a := 0) (b := 1) zero_le_one hmonoF hfDiff
      (hγinf.mdifferentiable (by simp)).mdifferentiableOn using 1
    all_goals
      simp only [f, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl, mul_zero, mul_one]
  have hprefix :
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
        ENNReal.ofReal L := by
    calc
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
        Manifold.pathELength_mono le_rfl hτ.2
      _ = ENNReal.ofReal
          ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := hfull
      _ = Manifold.riemannianEDist 𝓘(Real, E) x y :=
        ENNReal.ofReal_toReal hdist_top
      _ ≤ ENNReal.ofReal L := hdist'
  have hdist_xz :
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
        ENNReal.ofReal L := by
    have hpath :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := xU) (y := zU)
        hηUC1 hηU0 hηU1 zero_le_one
    calc
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
          Manifold.pathELength 𝓘(Real, E) ηU 0 1 := hpath
      _ = Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := hpullLen
      _ = Manifold.pathELength 𝓘(Real, E) η 0 1 := hextLen.symm
      _ = Manifold.pathELength 𝓘(Real, E) γ 0 τ := hηPrefix
      _ ≤ ENNReal.ofReal L := hprefix
  have hx0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc xU
  have hz0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc zU
  have hx0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
          (intrZero (E := E) hR) xU =
      ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
          (intrZero (E := E) hR) zU =
      ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have htri :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) zU ≤
        Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
    Manifold.riemannianEDist_triangle
  have hB :
      ENNReal.ofReal (3 * R / 4) ≤ ENNReal.ofReal (a + L) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU := htri
      _ = ENNReal.ofReal ‖x‖ +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU := by
        rw [hx0']
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal L :=
        add_le_add (ENNReal.ofReal_le_ofReal hx) hdist_xz
      _ = ENNReal.ofReal (a + L) := by
        rw [← ENNReal.ofReal_add ha hL]
  have hreal : 3 * R / 4 ≤ a + L :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha hL)).mp hB
  exact (not_le_of_gt hbudget) hreal

theorem intrExtJoin_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtJoin (I := I) g hEnorm p hR hloc x y t‖ <
        3 * R / 4 := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) x y ≤
        ENNReal.ofReal (2 * a) :=
    intrExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
  exact intrExtJoin_budget (I := I) g hEnorm p hR hloc hx
    (mul_nonneg (by norm_num) ha) hdist (by linarith)

private theorem exists_join_curve
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hγfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E) t‖ <
          3 * R / 4) :
    ∃ γU : Real → intrPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : intrPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E))
        (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  classical
  let γ : Real → E :=
    intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrExtJoin_smooth (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγgeo :
      IsGeodesic (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ := by
    simpa only [γ] using
      intrExtJoin_geo (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγfence' : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖γ t‖ < 3 * R / 4 := by
    simpa only [γ] using hγfence
  have hγ0_ball : γ 0 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, intrExtJoin_zero] using x.property
  have hγ1_ball : γ 1 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, intrExtJoin_one] using y.property
  have hpre0 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (0 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ0_ball)
  have hpre1 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (1 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ1_ball)
  obtain ⟨ε0, hε0, hε0sub⟩ := Metric.mem_nhds_iff.mp hpre0
  obtain ⟨ε1, hε1, hε1sub⟩ := Metric.mem_nhds_iff.mp hpre1
  let ε : Real := min ε0 ε1
  have hε : 0 < ε := by
    simpa only [ε] using lt_min hε0 hε1
  have hε_le0 : ε ≤ ε0 := by
    exact min_le_left ε0 ε1
  have hε_le1 : ε ≤ ε1 := by
    exact min_le_right ε0 ε1
  have hstayExt : ∀ t ∈ Set.Icc (-ε / 2) (1 + ε / 2),
      γ t ∈ Metric.ball (0 : E) R := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hε0sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht0]
      have hhalf : ε / 2 < ε0 := by
        linarith [hε, hε_le0]
      linarith [ht.1, hhalf]
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      by_cases ht1 : t ≤ 1
      · rw [Metric.mem_ball, dist_zero_right]
        exact (hγfence' t ⟨ht0', ht1⟩).trans (by linarith)
      · have ht1' : 1 < t := lt_of_not_ge ht1
        apply hε1sub
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1')]
        have hhalf : ε / 2 < ε1 := by
          linarith [hε, hε_le1]
        linarith [ht.2, hhalf]
  let c : Real := 1 / 2
  let lam : Real := 1 / 2 + ε / 2
  let clipLeft : Real := -1 / 2 - ε / 4
  let clipRight : Real := 1 / 2 + ε / 4
  have hlam : 0 < lam := by
    dsimp only [lam]
    linarith
  have hclipLeft : -lam < clipLeft := by
    dsimp only [lam, clipLeft]
    linarith
  have hclipRight : clipRight < lam := by
    dsimp only [lam, clipRight]
    linarith
  obtain ⟨σ, hσinf, hσid, hσrange⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
      hlam hclipLeft hclipRight
  let τ : Real → Real := fun t => c + σ (t - c)
  have hτinf : ContDiff Real (∞ : WithTop ℕ∞) τ := by
    dsimp only [τ]
    exact contDiff_const.add
      (hσinf.comp (contDiff_id.sub contDiff_const))
  have hτrange : ∀ t, τ t ∈ Set.Icc (-ε / 2) (1 + ε / 2) := by
    intro t
    have hσbounds := (abs_le.mp (hσrange (t - c)))
    dsimp only [τ, c, lam] at hσbounds ⊢
    constructor <;> linarith
  have hτid :
      Set.EqOn τ id (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    have htClip : t - c ∈ Set.Icc clipLeft clipRight := by
      dsimp only [c, clipLeft, clipRight]
      constructor <;> linarith [ht.1, ht.2]
    have hσ := hσid htClip
    change σ (t - c) = t - c at hσ
    dsimp only [τ]
    rw [hσ]
    dsimp only [c, id]
    ring
  let γU : Real → intrPullBall (E := E) R := fun t =>
    ⟨γ (τ t), hstayExt (τ t) (hτrange t)⟩
  have hγUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU := by
    have hcomp :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (fun t => γ (τ t)) := by
      apply hγinf.comp
      rw [contMDiff_iff_contDiff]
      exact hτinf
    intro t
    exact codRestr_contMDiffAt
      (V := intrPullBall (E := E) R)
      (fun s => hstayExt (τ s) (hτrange s)) (hcomp t)
  have hEqLarge :
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E)) γ
        (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    change γ (τ t) = γ t
    rw [hτid ht]
    rfl
  have hEq :
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E)) γ
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    exact hEqLarge ⟨by linarith [ht.1, hε], by linarith [ht.2, hε]⟩
  have hγUgeoExt :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γU t : intrPullBall (E := E) R) : E))
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    have hlarge_nhds :
        Set.Icc (-ε / 4) (1 + ε / 4) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith [ht.1, hε])
        (by linarith [ht.2, hε])
    have heq :
        (fun s => ((γU s : intrPullBall (E := E) R) : E)) =ᶠ[𝓝 t] γ :=
      hEqLarge.eventuallyEq_of_mem hlarge_nhds
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.eq_of_nhds heq (hγgeo t)
  have hγUfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖((γU t : intrPullBall (E := E) R) : E)‖ < 3 * R / 4 := by
    intro t ht
    calc
      ‖((γU t : intrPullBall (E := E) R) : E)‖ = ‖γ t‖ :=
        congrArg norm (hEq ht)
      _ < 3 * R / 4 := hγfence' t ht
  have hγUgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) :=
    intrPull_geo_of_ext (I := I) g hEnorm p hR hloc γU
      (Set.Icc (0 : Real) 1) hγUinf hγUfence hγUgeoExt
  refine ⟨γU, hγUinf, hγUgeo, ?_, ?_, hγUfence, ?_⟩
  · apply Subtype.ext
    simpa only [γ, intrExtJoin_zero] using
      hEq (x := (0 : Real)) (by norm_num)
  · apply Subtype.ext
    simpa only [γ, intrExtJoin_one] using
      hEq (x := (1 : Real)) (by norm_num)
  · simpa only [γ] using hEq

theorem exists_fenced_curve
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hx : x ∈ intrCore (E := E) R a)
    (hy : y ∈ intrCore (E := E) R a) :
    ∃ γU : Real → intrPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : intrPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E))
        (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  apply exists_join_curve (I := I) g hEnorm p hR hloc
  exact intrExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy

theorem intrPull_edist_eq_ext_of_budget
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hx : ‖(x : E)‖ ≤ a)
    (hd :
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) <
          ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI (z : intrPullBall (E := E) R) :
      NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : intrPullBall (E := E) R) :
      NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : intrPullBall (E := E) R,
      ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace (intrPullBall (E := E) R) :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E)
      (intrPullBall (E := E) R)
  letI : IsRiemannianManifold 𝓘(Real, E)
      (intrPullBall (E := E) R) :=
    ⟨fun _ _ => rfl⟩
  change
    Manifold.riemannianEDist 𝓘(Real, E) x y =
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E)
  have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx
  have hExtLt :
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) <
        ENNReal.ofReal L := by
    simpa only [gExt, riemannianEDistOf] using hd
  have hLPos : 0 < L :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hExtLt)
  have hExtBound :
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
        ENNReal.ofReal L :=
    hExtLt.le
  have hExtTop :
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≠
        (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hExtBound
  have hlen_of_stay :
      ∀ {γ : Real → intrPullBall (E := E) R} {s t : Real},
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t) →
        (∀ u ∈ Set.Icc s t,
          ‖((γ u : intrPullBall (E := E) R) : E)‖ ≤ 3 * R / 4) →
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength 𝓘(Real, E)
            (fun u => ((γ u : intrPullBall (E := E) R) : E)) s t := by
    intro γ s t hγ hstay
    let η : Real → E :=
      fun u => ((γ u : intrPullBall (E := E) R) : E)
    have hη :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγ
    have hpull :
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      simpa only [η, intrExpOn, Function.comp_apply] using
        (intrPull_pathLen (I := I) g hEnorm p hloc hγ).symm
    have hext :
        Manifold.pathELength 𝓘(Real, E) η s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      simpa only [gExt] using
        (intrExt_pathLen (I := I) g hEnorm p hR hloc hη
          (fun u hu => by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hstay u hu))
    exact hpull.trans hext.symm
  apply le_antisymm
  · obtain ⟨γ, hγinf, _, hγ0, hγ1, hγstay, hγeq⟩ :=
      exists_join_curve (I := I) g hEnorm p hR hloc
        (intrExtJoin_budget (I := I) g hEnorm p hR hloc
          (x := (x : E)) (y := (y : E)) hx hLPos.le hd.le hbudget)
    have hγC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
          (Set.Icc (0 : Real) 1) :=
      (hγinf.of_le (by decide)).contMDiffOn
    have hpath :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := x) (y := y)
        hγC1 hγ0 hγ1 zero_le_one
    have hlen :
        Manifold.pathELength 𝓘(Real, E) γ 0 1 =
          Manifold.pathELength 𝓘(Real, E)
            (fun t => ((γ t : intrPullBall (E := E) R) : E)) 0 1 :=
      hlen_of_stay hγC1 (fun t ht => (hγstay t ht).le)
    have hjoin :
        Manifold.pathELength 𝓘(Real, E)
            (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
            0 1 =
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := by
      calc
        Manifold.pathELength 𝓘(Real, E)
              (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
              0 1 =
            ENNReal.ofReal
              ((Manifold.riemannianEDist 𝓘(Real, E)
                (x : E) (y : E)).toReal) := by
          simpa only [intrExtJoin, gExt] using
            (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E))
        _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
          ENNReal.ofReal_toReal hExtTop
    calc
      Manifold.riemannianEDist 𝓘(Real, E) x y ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := hpath
      _ = Manifold.pathELength 𝓘(Real, E)
          (fun t => ((γ t : intrPullBall (E := E) R) : E)) 0 1 := hlen
      _ = Manifold.pathELength 𝓘(Real, E)
          (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
          0 1 :=
        Manifold.pathELength_congr hγeq
      _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := hjoin
  · by_contra hnot
    have hlt :
        Manifold.riemannianEDist 𝓘(Real, E) x y <
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    have hstay :
        ∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((γ t : intrPullBall (E := E) R) : E)‖ ≤ 3 * R / 4 := by
      intro t ht
      have hγC1pre :
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc 0 t) :=
        hγC1.mono (Set.Icc_subset_Icc le_rfl ht.2)
      have hdist_pre :
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
            Manifold.pathELength 𝓘(Real, E) γ 0 t :=
        Manifold.riemannianEDist_le_pathELength
          (I := 𝓘(Real, E)) (x := x) (y := γ t)
          hγC1pre hγ0 rfl ht.1
      have hdist_lt :
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) <
            ENNReal.ofReal L := by
        calc
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
              Manifold.pathELength 𝓘(Real, E) γ 0 t := hdist_pre
          _ ≤ Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
            Manifold.pathELength_mono le_rfl ht.2
          _ < Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
            hγlen
          _ ≤ ENNReal.ofReal L := hExtBound
      have hx0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc x
      have hz0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc (γ t)
      have hnormE :
          ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ <
            ENNReal.ofReal (a + L) := by
        calc
          ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ =
              Manifold.riemannianEDist 𝓘(Real, E)
                (intrZero (E := E) hR) (γ t) := by
            change
              ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ =
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                  (intrZero (E := E) hR) (γ t)
            exact hz0.symm
          _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
                (intrZero (E := E) hR) x +
              Manifold.riemannianEDist 𝓘(Real, E) x (γ t) :=
            Manifold.riemannianEDist_triangle
          _ < ENNReal.ofReal a + ENNReal.ofReal L := by
            have hx0' :
                Manifold.riemannianEDist 𝓘(Real, E)
                    (intrZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖ := by
              change
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                    (intrZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖
              exact hx0
            rw [hx0']
            exact ENNReal.add_lt_add_of_le_of_lt
              ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hx) hdist_lt
          _ = ENNReal.ofReal (a + L) := by
            rw [← ENNReal.ofReal_add ha hLPos.le]
      have hnorm :
          ‖((γ t : intrPullBall (E := E) R) : E)‖ < a + L :=
        (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos ha hLPos)).mp
          hnormE
      exact (hnorm.trans hbudget).le
    let η : Real → E :=
      fun t => ((γ t : intrPullBall (E := E) R) : E)
    have hηC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
          (Set.Icc (0 : Real) 1) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγC1
    have hη0 : η 0 = (x : E) := by
      simp only [η, hγ0]
    have hη1 : η 1 = (y : E) := by
      simp only [η, hγ1]
    have hExtPath :
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
          Manifold.pathELength 𝓘(Real, E) η 0 1 :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := (x : E)) (y := (y : E))
        hηC1 hη0 hη1 zero_le_one
    have hlen :
        Manifold.pathELength 𝓘(Real, E) γ 0 1 =
          Manifold.pathELength 𝓘(Real, E) η 0 1 := by
      simpa only [η] using hlen_of_stay hγC1 hstay
    exact (not_lt_of_ge (hExtPath.trans_eq hlen.symm)) hγlen

theorem intrCore_edist_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hx : x ∈ intrCore (E := E) R a)
    (hy : y ∈ intrCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) := by
  let L : Real := (a + 3 * R / 4) / 2
  have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hLPos : 0 < L := by
    dsimp only [L]
    linarith
  have h2aL : 2 * a < L := by
    dsimp only [L]
    linarith
  have hdistLe :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) ≤
        ENNReal.ofReal (2 * a) :=
    intrExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
  have hdistLt :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) <
        ENNReal.ofReal L :=
    hdistLe.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hLPos).2 h2aL)
  apply intrPull_edist_eq_ext_of_budget
    (I := I) g hEnorm p hR hloc hx hdistLt
  dsimp only [L]
  linarith

noncomputable def intrExtLaunch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x : E) (v : TangentSpace 𝓘(Real, E) x) : Real → E := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  exact intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v

theorem intrExt_shortLaunch_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x : E} (hx : ‖x‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtLaunch (I := I) g hEnorm p hR hloc x v t‖ <
        3 * R / 4 := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x v
  have hγcont : Continuous γ := hγinf.continuous
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hspeedNonneg : 0 ≤ Real.sqrt (gExt.inner x v v) :=
    Real.sqrt_nonneg _
  have hL : 0 ≤ L := hspeedNonneg.trans (by simpa only [gExt] using hv)
  let cap : Real := 3 * R / 4 - a
  let Lstar : Real := (L + cap) / 2
  have hLcap : L < cap := by
    dsimp only [cap]
    linarith
  have hLstar : L < Lstar := by
    dsimp only [Lstar]
    linarith
  have hstarCap : Lstar < cap := by
    dsimp only [Lstar]
    linarith
  have hstarPos : 0 < Lstar := lt_of_le_of_lt hL hLstar
  have hbudgetStar : a + Lstar < 3 * R / 4 := by
    dsimp only [cap] at hstarCap
    linarith
  have haB : a < 3 * R / 4 := by linarith
  have haInner : a ≤ 3 * R / 4 := haB.le
  intro t ht
  by_contra hnot
  have hcross : 3 * R / 4 ≤ ‖γ t‖ := by
    simpa only [γ, gExt, hExt, intrExtLaunch] using (not_lt.mp hnot)
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    simpa only [γ, intrinsicGeodesic_zero] using hx.trans_lt haB
  obtain ⟨τ, hτ, hτeq, hbefore⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc
      zero_le_one hγcont.norm.continuousOn hstart ⟨t, ht, hcross⟩
  have hτone : τ ≤ 1 := hτ.2
  have hdistStep :
      Manifold.riemannianEDist 𝓘(Real, E) x (γ τ) ≤
        ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * τ) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := 𝓘(Real, E)) gExt hExt x v
        (s := 0) (t := τ) hτ.1
    simpa only [γ, intrinsicGeodesic_zero, sub_zero] using h
  have hspeed : Real.sqrt (gExt.inner x v v) ≤ L := by
    simpa only [gExt] using hv
  have hmul : Real.sqrt (gExt.inner x v v) * τ ≤ L := by
    nlinarith
  have hdistLt :
      Manifold.riemannianEDist 𝓘(Real, E) x (γ τ) <
        ENNReal.ofReal Lstar :=
    hdistStep.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hstarPos).2
        (hmul.trans_lt hLstar))
  let xU : intrPullBall (E := E) R :=
    ⟨x, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : intrPullBall (E := E) R :=
    ⟨γ τ, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hdistEq :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrPullMetric (I := I) g hEnorm p hloc) xU zU =
        riemannianEDistOf (I := 𝓘(Real, E)) gExt x (γ τ) := by
    apply intrPull_edist_eq_ext_of_budget
      (I := I) g hEnorm p hR hloc (a := a) (L := Lstar)
    · exact hx
    · simpa only [gExt, riemannianEDistOf] using hdistLt
    · exact hbudgetStar
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hdistPull :
      Manifold.riemannianEDist 𝓘(Real, E) xU zU <
        ENNReal.ofReal Lstar := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull xU zU <
      ENNReal.ofReal Lstar
    rw [hdistEq]
    simpa only [gExt, riemannianEDistOf] using hdistLt
  have hx0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc xU
  have hz0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc zU
  have hx0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull
        (intrZero (E := E) hR) xU =
      ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull
        (intrZero (E := E) hR) zU =
      ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have hB :
      ENNReal.ofReal (3 * R / 4) <
        ENNReal.ofReal (a + Lstar) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
              (intrZero (E := E) hR) xU +
            Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
        Manifold.riemannianEDist_triangle
      _ = ENNReal.ofReal ‖x‖ +
            Manifold.riemannianEDist 𝓘(Real, E) xU zU := by
        rw [hx0']
      _ < ENNReal.ofReal a + ENNReal.ofReal Lstar :=
        ENNReal.add_lt_add_of_le_of_lt ENNReal.ofReal_ne_top
          (ENNReal.ofReal_le_ofReal hx) hdistPull
      _ = ENNReal.ofReal (a + Lstar) := by
        rw [← ENNReal.ofReal_add ha hstarPos.le]
  have hreal : 3 * R / 4 < a + Lstar :=
    (ENNReal.ofReal_lt_ofReal_iff
      (add_pos_of_nonneg_of_pos ha hstarPos)).mp hB
  exact (not_lt_of_ge hbudgetStar.le) hreal

theorem intrExt_scale_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hbudget : a + L < 3 * R / 4)
    (hend : intrExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤
        a + L / 2 := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  let ell : Real := Real.sqrt (gExt.inner x v v)
  have hγ1 : γ 1 = y := by
    simpa only [γ, gExt, hExt, intrExtLaunch] using hend
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hell : 0 ≤ ell := Real.sqrt_nonneg _
  have hell_le : ell ≤ L := by
    simpa only [ell, gExt] using hv
  have hL : 0 ≤ L := hell.trans hell_le
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hfence :
      ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ < 3 * R / 4 := by
    simpa only [γ, gExt, hExt, intrExtLaunch] using
      intrExt_shortLaunch_fenced (I := I) g hEnorm p hR hloc hx v hv
        hbudget
  let cap : Real := 3 * R / 4 - a
  let Lstar : Real := (L + cap) / 2
  have hLStar : L < Lstar := by
    dsimp only [Lstar, cap]
    linarith
  have hstarPos : 0 < Lstar := lt_of_le_of_lt hL hLStar
  have hbudgetStar : a + Lstar < 3 * R / 4 := by
    dsimp only [Lstar, cap]
    linarith
  intro t ht
  let xU : intrPullBall (E := E) R :=
    ⟨x, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let yU : intrPullBall (E := E) R :=
    ⟨y, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hy.trans haInner)⟩
  let zU : intrPullBall (E := E) R :=
    ⟨γ t, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hfence t ht).le)⟩
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hnorm_of_dist :
      ∀ (wU : intrPullBall (E := E) R) (hw : ‖(wU : E)‖ ≤ a)
          (B : Real) (hB : 0 ≤ B) (hBL : B ≤ L),
        riemannianEDistOf (I := 𝓘(Real, E)) gExt (wU : E) (zU : E) ≤
            ENNReal.ofReal B →
          ‖(zU : E)‖ ≤ a + B := by
    intro wU hw B hB hBL hdist
    have hdistLt :
        riemannianEDistOf (I := 𝓘(Real, E)) gExt (wU : E) (zU : E) <
          ENNReal.ofReal Lstar :=
      hdist.trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hstarPos).2
          (hBL.trans_lt hLStar))
    have hdistEq :
        riemannianEDistOf (I := 𝓘(Real, E)) gPull wU zU =
          riemannianEDistOf (I := 𝓘(Real, E)) gExt (wU : E) (zU : E) :=
      intrPull_edist_eq_ext_of_budget
        (I := I) g hEnorm p hR hloc hw hdistLt hbudgetStar
    have hw0 :=
      intrPull_dist_zero (I := I) g hEnorm p hR hloc wU
    have hz0 :=
      intrPull_dist_zero (I := I) g hEnorm p hR hloc zU
    have hbound :
        ENNReal.ofReal ‖(zU : E)‖ ≤ ENNReal.ofReal (a + B) := by
      calc
        ENNReal.ofReal ‖(zU : E)‖ =
            riemannianEDistOf (I := 𝓘(Real, E)) gPull
              (intrZero (E := E) hR) zU := hz0.symm
        _ ≤ riemannianEDistOf (I := 𝓘(Real, E)) gPull
              (intrZero (E := E) hR) wU +
            riemannianEDistOf (I := 𝓘(Real, E)) gPull wU zU :=
          Manifold.riemannianEDist_triangle
        _ = ENNReal.ofReal ‖(wU : E)‖ +
            riemannianEDistOf (I := 𝓘(Real, E)) gExt (wU : E) (zU : E) := by
          rw [hw0, hdistEq]
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal B :=
          add_le_add (ENNReal.ofReal_le_ofReal hw) hdist
        _ = ENNReal.ofReal (a + B) := by
          rw [← ENNReal.ofReal_add ha hB]
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha hB)).mp hbound
  have hpre :
      riemannianEDistOf (I := 𝓘(Real, E)) gExt x (γ t) ≤
        ENNReal.ofReal (ell * t) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := 𝓘(Real, E)) gExt hExt x v
        (s := 0) (t := t) ht.1
    simpa only [γ, ell, intrinsicGeodesic_zero, sub_zero] using h
  have hsuf :
      riemannianEDistOf (I := 𝓘(Real, E)) gExt y (γ t) ≤
        ENNReal.ofReal (ell * (1 - t)) := by
    have h :=
      intrinsicGeodesic_riemannianEDist_le
        (I := 𝓘(Real, E)) gExt hExt x v
        (s := t) (t := 1) ht.2
    change
      Manifold.riemannianEDist 𝓘(Real, E) y (γ t) ≤
        ENNReal.ofReal (ell * (1 - t))
    rw [Manifold.riemannianEDist_comm]
    change
      Manifold.riemannianEDist 𝓘(Real, E) (γ t) (γ 1) ≤
        ENNReal.ofReal (ell * (1 - t)) at h
    simpa only [hγ1] using h
  have hBt : 0 ≤ ell * t := mul_nonneg hell ht.1
  have hBt_le : ell * t ≤ L := by
    calc
      ell * t ≤ ell * 1 := mul_le_mul_of_nonneg_left ht.2 hell
      _ = ell := mul_one ell
      _ ≤ L := hell_le
  have hBtail : 0 ≤ ell * (1 - t) :=
    mul_nonneg hell (sub_nonneg.mpr ht.2)
  have hBtail_le : ell * (1 - t) ≤ L := by
    calc
      ell * (1 - t) ≤ ell * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [ht.1]) hell
      _ = ell := mul_one ell
      _ ≤ L := hell_le
  have hxBound : ‖γ t‖ ≤ a + ell * t := by
    simpa only [xU, zU] using
      hnorm_of_dist xU hx (ell * t) hBt hBt_le hpre
  have hyBound : ‖γ t‖ ≤ a + ell * (1 - t) := by
    simpa only [yU, zU] using
      hnorm_of_dist yU hy (ell * (1 - t)) hBtail hBtail_le hsuf
  simpa only [γ, gExt, hExt, intrExtLaunch] using
    (show ‖γ t‖ ≤ a + L / 2 by nlinarith)

theorem intrExt_short_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        2 * a)
    (hend : intrExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤ 2 * a := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  intro t ht
  have hbound :=
    intrExt_scale_bound (I := I) g hEnorm p hR hloc hx hy v hv
      (by linarith) hend t ht
  nlinarith

private theorem intrExt_quad_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4)
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p z) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (J V : E) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    gExt.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
          z J V V)
        J ≤
      K * gExt.inner z J J * gExt.inner z V V := by
  let U := intrPullBall (E := E) R
  let Vopen := intrAgree (E := E) R
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  have hzBall : z ∈ Metric.ball (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzClosed : z ∈ Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall hzBall
  let zU : U := ⟨z, intrInner_subset (E := E) R hR hzBall⟩
  let zV : Vopen := ⟨zU, hzBall⟩
  have hmetric :
      ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
          (I := 𝓘(Real, E)) Vopen) =
        gPull.restrictOpen (I := 𝓘(Real, E)) Vopen := by
    simpa only [U, Vopen, gExt, gPull] using
      intrExt_restrict (I := I) g hEnorm p hR hloc
  have hquad :=
    intrPull_quad_le (I := I) g hEnorm p hloc zU hRm J V
  dsimp only at hquad
  calc
    gExt.inner z
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
            z J V V)
          J =
        gExt.inner z J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
            z J V V) := gExt.symm _ _ _
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := E) gExt z J V V J := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := U)
          (gExt.restrictOpen (I := 𝓘(Real, E)) U) zU J V V J :=
      (Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E)) gExt U zU J V V J).symm
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := Vopen)
          ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
            (I := 𝓘(Real, E)) Vopen) zV J V V J :=
      (Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U)
        Vopen zV J V V J).symm
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := Vopen)
          (gPull.restrictOpen (I := 𝓘(Real, E)) Vopen)
          zV J V V J := by rw [hmetric]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := U) gPull zU J V V J :=
      Geometry.Curvature.metricRm04StdAt_restrictOpen
        (I := 𝓘(Real, E)) gPull Vopen zV J V V J
    _ = gPull.inner zU J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            zU J V V) := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = gPull.inner zU
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            zU J V V)
          J := gPull.symm _ _ _
    _ ≤ K * gPull.inner zU J J * gPull.inner zU V V := hquad
    _ = K * gExt.inner z J J * gExt.inner z V V := by
      rw [intrExt_inner (I := I) g hEnorm p hR hloc hzClosed J J,
        intrExt_inner (I := I) g hEnorm p hR hloc hzClosed V V]

theorem intrExt_not_conj_of_shortLaunch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x : E} (v : TangentSpace 𝓘(Real, E) x)
    (hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtLaunch (I := I) g hEnorm p hR hloc x v t‖ <
          3 * R / 4)
    (hv :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (intrExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E) := by
  classical
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E)
  have hzero :
      ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (0 : E) := by
    simpa only [IsConjVec, not_not,
      mfderiv_expMapIntrinsic_at_zero (I := 𝓘(Real, E)) gExt hExt x] using
      (Function.injective_id : Function.Injective (fun z : E => z))
  intro hconj
  have hvne : (v : E) ≠ 0 := by
    intro hv0
    apply hzero
    simpa only [hv0] using hconj
  rw [isConjVec_iff_jacobi
    (I := 𝓘(Real, E)) gExt hExt x (v : E)] at hconj
  obtain ⟨w, hw, hwend⟩ := hconj
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  let J : Real → E :=
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x v w
  let DJ : Real → E := fun t =>
    CovariantDerivativeAlong.covDerivAlong
      (I := 𝓘(Real, E)) gExt γ J t
  let f : Real → Real := fun t => gExt.inner (γ t) (J t) (J t)
  have hγ :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x v
  have hJ0 : J 0 = 0 := by
    simpa only [J] using
      intrinsicJacobi_zero
        (I := 𝓘(Real, E)) gExt hExt x v w
  have hJ1 : J 1 = 0 := by
    simpa only [J, intrinsicJacobi] using hwend
  obtain ⟨B0, hB0⟩ :=
    branch_of_not_conj (I := 𝓘(Real, E)) gExt hExt hzero
  have hline :
      Continuous (fun t : Real => t • (v : E)) :=
    continuous_id.smul continuous_const
  have hsrc_ev :
      ∀ᶠ t in 𝓝 (0 : Real), t • (v : E) ∈ B0.hom.source := by
    have hsrc0 : (0 : Real) • (v : E) ∈ B0.hom.source := by
      simpa only [zero_smul] using hB0
    exact hline.continuousAt (B0.hom.open_source.mem_nhds hsrc0)
  have hsrc_gt :
      ∀ᶠ t in 𝓝[>] (0 : Real), t • (v : E) ∈ B0.hom.source :=
    hsrc_ev.filter_mono inf_le_left
  have hIoo :
      ∀ᶠ t in 𝓝[>] (0 : Real), t ∈ Set.Ioo (0 : Real) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨t0, ht0src, ht0⟩ := (hsrc_gt.and hIoo).exists
  have ht0inj :
      Function.Injective
        (mfderiv 𝓘(Real, E) 𝓘(Real, E)
          (fun z : E =>
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
              (show TangentSpace 𝓘(Real, E) x from z))
          (t0 • (v : E))) := by
    simpa only [IsConjVec, not_not] using B0.not_conj ht0src
  have hJt0 : J t0 ≠ 0 := by
    intro hJt0
    have hjat :
        J t0 =
          mfderiv 𝓘(Real, E) 𝓘(Real, E)
            (fun z : E =>
              expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
                (show TangentSpace 𝓘(Real, E) x from z))
            (t0 • (v : E)) (t0 • w) := by
      simpa only [J, intrinsicJacobi] using
        intrinsic_jacobi_at
          (I := 𝓘(Real, E)) gExt hExt x (v : E) w t0
    have hker :
        mfderiv 𝓘(Real, E) 𝓘(Real, E)
            (fun z : E =>
              expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
                (show TangentSpace 𝓘(Real, E) x from z))
            (t0 • (v : E)) (t0 • w) = 0 := by
      rw [← hjat]
      exact hJt0
    have htw : t0 • w = 0 := by
      apply ht0inj
      rw [hker]
      exact (map_zero _).symm
    exact hw ((smul_eq_zero.mp htw).resolve_left ht0.1.ne')
  have hJdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γ J t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x v w t).1
  have hfderiv (t : Real) :
      HasDerivAt f
        (gExt.inner (γ t) (DJ t) (J t) +
          gExt.inner (γ t) (J t) (DJ t)) t := by
    simpa only [f, DJ] using
      Variation.metric_compat_hasDerivAt_inner
        (I := 𝓘(Real, E)) (n := ∞) (by simp)
        gExt γ J J t hγ (hJdiff t) (hJdiff t)
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hfderiv t).continuousAt
  obtain ⟨c, hc, hcmax⟩ :=
    (isCompact_Icc (a := (0 : Real)) (b := 1)).exists_isMaxOn
      (Set.nonempty_Icc.2 zero_le_one) hfcont.continuousOn
  have hft0pos : 0 < f t0 :=
    gExt.pos (γ t0) (J t0) hJt0
  have hfcpos : 0 < f c :=
    hft0pos.trans_le
      (Filter.eventually_principal.mp hcmax t0
        ⟨ht0.1.le, ht0.2.le⟩)
  have hinner00 (z : E) :
      gExt.inner z (0 : E) (0 : E) = 0 :=
    (gExt.inner z (0 : E)).map_zero
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    simp only [f, hJ0, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hc1 : c ≠ 1 := by
    intro hc1
    subst c
    simp only [f, hJ1, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hcIoo : c ∈ Set.Ioo (0 : Real) 1 :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0),
      lt_of_le_of_ne hc.2 hc1⟩
  have hJc : J c ≠ 0 := by
    intro hJc
    simp only [f, hJc, hinner00] at hfcpos
    exact lt_irrefl (0 : Real) hfcpos
  have hlocal : IsLocalMax f c := by
    filter_upwards [Icc_mem_nhds hcIoo.1 hcIoo.2] with t ht
    exact Filter.eventually_principal.mp hcmax t ht
  have hsum0 :
      gExt.inner (γ c) (DJ c) (J c) +
          gExt.inner (γ c) (J c) (DJ c) = 0 :=
    hlocal.hasDerivAt_eq_zero (hfderiv c)
  have hpair0 : gExt.inner (γ c) (DJ c) (J c) = 0 := by
    rw [gExt.symm (γ c) (J c) (DJ c)] at hsum0
    linarith
  have hperp : gExt.inner x v w = 0 := by
    have hp :=
      intrinsicJacobi_perp
        (I := 𝓘(Real, E)) gExt hExt x v w
    have hJ1' :
        intrinsicJacobi
            (I := 𝓘(Real, E)) gExt hExt x v w 1 = 0 := by
      simpa only [J] using hJ1
    rw [hJ1'] at hp
    have hz :
        gExt.inner
            (intrinsicGeodesic
              (I := 𝓘(Real, E)) gExt hExt x v 1)
            (intrinsicVelocityLift
              (I := 𝓘(Real, E)) gExt hExt x v 1).snd
            (0 : E) = 0 :=
      (gExt.inner
        (intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x v 1)
        (intrinsicVelocityLift
          (I := 𝓘(Real, E)) gExt hExt x v 1).snd).map_zero
    exact hp.symm.trans hz
  let γc : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x (c • v)
  let Jc : Real → E :=
    intrinsicJacobi
      (I := 𝓘(Real, E)) gExt hExt x (c • v) (c • w)
  have hGeoScale (t : Real) : γc t = γ (c * t) := by
    dsimp only [γc, γ]
    calc
      intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t =
        intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x (t • (c • v)) 1 :=
        (intrinsicGeodesic_smul
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t).symm
      _ = intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x ((c * t) • v) 1 := by
        rw [smul_smul, mul_comm]
      _ = intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x v (c * t) :=
        intrinsicGeodesic_smul
          (I := 𝓘(Real, E)) gExt hExt x v (c * t)
  have hJacScale (t : Real) : Jc t = J (c * t) := by
    have hleft :=
      intrinsic_jacobi_at
        (I := 𝓘(Real, E)) gExt hExt x
        (c • (v : E)) (c • w) t
    have hright :=
      intrinsic_jacobi_at
        (I := 𝓘(Real, E)) gExt hExt x
        (v : E) w (c * t)
    have hleft' :
        Jc t =
          mfderiv 𝓘(Real, E) 𝓘(Real, E)
            (fun z : E =>
              expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
                (show TangentSpace 𝓘(Real, E) x from z))
            (t • (c • (v : E))) (t • (c • w)) := by
      simpa only [Jc, intrinsicJacobi] using hleft
    have hright' :
        J (c * t) =
          mfderiv 𝓘(Real, E) 𝓘(Real, E)
            (fun z : E =>
              expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
                (show TangentSpace 𝓘(Real, E) x from z))
            ((c * t) • (v : E)) ((c * t) • w) := by
      simpa only [J, intrinsicJacobi] using hright
    have hbase :
        t • (c • (v : E)) = (c * t) • (v : E) := by
      module
    have hdir : t • (c • w) = (c * t) • w := by
      module
    rw [hbase, hdir] at hleft'
    exact hleft'.trans hright'.symm
  have hγc :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γc := by
    simpa only [γc] using
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x (c • v)
  have hgeoc :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt γc
        (Set.Icc (0 : Real) 1) := by
    simpa only [γc] using
      (intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x (c • v)).isGeodesicOn
          (Set.Icc (0 : Real) 1)
  have hJcdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γc Jc t) t := by
    simpa only [γc, Jc] using
      (intrJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x
        (c • v) (c • w) t).1
  have hDJcdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γc
          (fun s =>
            CovariantDerivativeAlong.covDerivAlong
              (I := 𝓘(Real, E)) gExt γc Jc s) t) t := by
    simpa only [γc, Jc] using
      (intrJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x
        (c • v) (c • w) t).2
  have hJacc :
      Variation.IsJacobiAlong
        (I := 𝓘(Real, E)) gExt γc Jc := by
    simpa only [γc, Jc, intrinsicJacobi] using
      intrinsic_jacobi
        (I := 𝓘(Real, E)) gExt hExt x
        (c • (v : E)) (c • w)
  have hJc0 : Jc 0 = 0 := by
    simpa only [Jc] using
      intrinsicJacobi_zero
        (I := 𝓘(Real, E)) gExt hExt x
        (c • v) (c • w)
  have hJc1 : Jc 1 ≠ 0 := by
    intro hz
    apply hJc
    calc
      J c = J (c * 1) := by rw [mul_one]
      _ = Jc 1 := (hJacScale 1).symm
      _ = 0 := hz
  have hscaledPerp :
      gExt.inner x (c • v) (c • w) = 0 := by
    calc
      gExt.inner x (c • v) (c • w) =
          c * gExt.inner x v (c • w) := by
        rw [map_smul (gExt.inner x), ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      _ = c * (c * gExt.inner x v w) := by
        exact congrArg (fun r : Real => c * r)
          (by
            simpa only [smul_eq_mul] using
              (gExt.inner x v).map_smul c w)
      _ = 0 := by rw [hperp]; ring
  have hJperpc :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        gExt.inner (γc t) (Jc t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hJc0, gExt.symm]
      exact
        (gExt.inner (γc 0)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γc 0)).map_zero
    · rw [gExt.symm]
      exact intrJacobi_perp_ne
        (I := 𝓘(Real, E)) gExt hExt x
        (c • v) (c • w) ht0 hscaledPerp
  have hcvne : (c • v : E) ≠ 0 :=
    smul_ne_zero hcIoo.1.ne' hvne
  have hspeedc :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        0 < gExt.inner (γc t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) := by
    intro t ht
    change
      0 < gExt.inner
        (intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x (c • v)) t 1)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x (c • v)) t 1)
    rw [intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x (c • v) t]
    exact gExt.pos x (c • v) hcvne
  let ell : Real := Real.sqrt (gExt.inner x v v)
  have hell0 : 0 ≤ ell := Real.sqrt_nonneg _
  have hellL : ell ≤ L := by
    simpa only [ell, gExt] using hv
  have hL0 : 0 ≤ L := hell0.trans hellL
  have hcell0 : 0 ≤ c * ell :=
    mul_nonneg hcIoo.1.le hell0
  have hcellL : c * ell ≤ L := by
    calc
      c * ell ≤ 1 * ell :=
        mul_le_mul_of_nonneg_right hc.2 hell0
      _ = ell := one_mul ell
      _ ≤ L := hellL
  have hsqLe : (c * ell) ^ 2 ≤ L ^ 2 := by
    nlinarith
  have hvnn : 0 ≤ gExt.inner x v v :=
    (gExt.pos x v hvne).le
  have hscaleSq :
      gExt.inner x (c • v) (c • v) = (c * ell) ^ 2 := by
    calc
      gExt.inner x (c • v) (c • v) =
          c * gExt.inner x v (c • v) := by
        rw [map_smul (gExt.inner x), ContinuousLinearMap.smul_apply,
          smul_eq_mul]
      _ = c * (c * gExt.inner x v v) := by
        exact congrArg (fun r : Real => c * r)
          (by
            simpa only [smul_eq_mul] using
              (gExt.inner x v).map_smul c v)
      _ = (c * ell) ^ 2 := by
        rw [← Real.sq_sqrt hvnn]
        dsimp only [ell]
        ring
  let κ : Real := K * (c * ell) ^ 2
  have hκ0 : 0 ≤ κ :=
    mul_nonneg hK (sq_nonneg _)
  have hκπ : κ < (Real.pi / 2) ^ 2 := by
    exact
      (mul_le_mul_of_nonneg_left hsqLe hK).trans_lt hsmall
  have hfenceγ :
      ∀ t ∈ Set.Icc (0 : Real) 1, ‖γ t‖ < 3 * R / 4 := by
    intro t ht
    simpa only [γ, gExt, hExt, intrExtLaunch] using hfence t ht
  have hcurvc :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        gExt.inner (γc t)
            (Geometry.Curvature.riemannOp
              (Geometry.Connection.LeviCivita
                (I := 𝓘(Real, E)) gExt)
              (γc t) (Jc t)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γc t))
            (Jc t) ≤
          κ * gExt.inner (γc t) (Jc t) (Jc t) := by
    intro t ht
    have hct : c * t ∈ Set.Icc (0 : Real) 1 :=
      ⟨mul_nonneg hcIoo.1.le ht.1,
        mul_le_one₀ hc.2 ht.1 ht.2⟩
    have hz : ‖γc t‖ < 3 * R / 4 := by
      rw [hGeoScale t]
      exact hfenceγ (c * t) hct
    have hquad :=
      intrExt_quad_le
        (I := I) g hEnorm p hR hloc hz (hRm (γc t) hz)
          (Jc t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
    have hspeedEq :
        gExt.inner (γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) =
          gExt.inner x (c • v) (c • v) := by
      simpa only [γc, Variation.curveVelocity] using
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x (c • v) t
    calc
      _ ≤ K * gExt.inner (γc t) (Jc t) (Jc t) *
          gExt.inner (γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γc t) := by
        simpa only [gExt] using hquad
      _ = κ * gExt.inner (γc t) (Jc t) (Jc t) := by
        rw [hspeedEq, hscaleSq]
        dsimp only [κ]
        ring
  have hpos :=
    Variation.jacobi_pair_pos
      (I := 𝓘(Real, E)) gExt γc Jc hγc hgeoc
      hJcdiff hDJcdiff
      (fun t ht => hJacc t) hJc0 hJc1 hspeedc hJperpc
      hκ0 hκπ hcurvc
  have hγcfun :
      γc = fun t : Real => γ (c * t + 0) := by
    funext t
    simpa only [add_zero] using hGeoScale t
  have hJcfun :
      Jc = fun t : Real => J (c * t + 0) := by
    funext t
    simpa only [add_zero] using hJacScale t
  have hDscale :
      CovariantDerivativeAlong.covDerivAlong
          (I := 𝓘(Real, E)) gExt γc Jc 1 =
        c • DJ c := by
    rw [hγcfun, hJcfun]
    have haff :=
      covDeriv_comp_affine
        (I := 𝓘(Real, E)) gExt γ J c 0 1
    have hc10 : c * 1 + 0 = c := by ring
    rw [hc10] at haff
    simpa only [DJ] using haff
  have hγc1 : γc 1 = γ c := by
    simpa only [mul_one] using hGeoScale 1
  have hJc1eq : Jc 1 = J c := by
    simpa only [mul_one] using hJacScale 1
  have hpos' :
      0 < c * gExt.inner (γ c) (DJ c) (J c) := by
    calc
      0 < gExt.inner (γc 1)
          (CovariantDerivativeAlong.covDerivAlong
            (I := 𝓘(Real, E)) gExt γc Jc 1)
          (Jc 1) := hpos
      _ = c * gExt.inner (γ c) (DJ c) (J c) := by
        rw [hγc1, hDscale, hJc1eq]
        calc
          gExt.inner (γ c) (c • DJ c) (J c) =
              (c • gExt.inner (γ c) (DJ c)) (J c) := by
            exact congrArg (fun A : E →L[Real] Real => A (J c))
              ((gExt.inner (γ c)).map_smul c (DJ c))
          _ = c * gExt.inner (γ c) (DJ c) (J c) := by
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hpairpos :
      0 < gExt.inner (γ c) (DJ c) (J c) := by
    nlinarith [hcIoo.1]
  exact (ne_of_gt hpairpos) hpair0

theorem intrExt_pair_pos
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x : E} (u w : TangentSpace 𝓘(Real, E) x)
    (hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtLaunch (I := I) g hEnorm p hR hloc x u t‖ <
          3 * R / 4)
    (hu :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x u u) ≤
        L)
    (hune : (u : E) ≠ 0) (hwne : (w : E) ≠ 0)
    (hperp :
      (intrExtMetric (I := I) g hEnorm p hR hloc).inner x u w = 0)
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v₁ v₂; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (intrExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    let γ : Real → E :=
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
    let J : Real → E :=
      intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
    0 < gExt.inner (γ 1)
      (CovariantDerivativeAlong.covDerivAlong
        (I := 𝓘(Real, E)) gExt γ J 1) (J 1) := by
  classical
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v₁ v₂; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
  let J : Real → E :=
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
  have hnot :
      ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (u : E) := by
    simpa only [gExt, hExt] using
      intrExt_not_conj_of_shortLaunch
        (I := I) g hEnorm p hR hloc u hfence hu hK hRm hsmall
  have hJ1 : J 1 ≠ 0 := by
    intro hzero
    apply hnot
    rw [isConjVec_iff_jacobi
      (I := 𝓘(Real, E)) gExt hExt x (u : E)]
    refine ⟨w, hwne, ?_⟩
    simpa only [J, intrinsicJacobi] using hzero
  have hγ :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x u
  have hgeo :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt γ
        (Set.Icc (0 : Real) 1) := by
    simpa only [γ] using
      (intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x u).isGeodesicOn
          (Set.Icc (0 : Real) 1)
  have hJdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γ J t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x u w t).1
  have hDJdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γ
          (fun s => CovariantDerivativeAlong.covDerivAlong
            (I := 𝓘(Real, E)) gExt γ J s) t) t := by
    simpa only [γ, J] using
      (intrJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x u w t).2
  have hJac :
      Variation.IsJacobiAlong (I := 𝓘(Real, E)) gExt γ J := by
    simpa only [γ, J, intrinsicJacobi] using
      intrinsic_jacobi
        (I := 𝓘(Real, E)) gExt hExt x (u : E) (w : E)
  have hJ0 : J 0 = 0 := by
    simpa only [J] using
      intrinsicJacobi_zero
        (I := 𝓘(Real, E)) gExt hExt x u w
  have hJperp :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        gExt.inner (γ t) (J t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hJ0, gExt.symm]
      exact
        (gExt.inner (γ 0)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ 0)).map_zero
    · rw [gExt.symm]
      exact intrJacobi_perp_ne
        (I := 𝓘(Real, E)) gExt hExt x u w ht0 hperp
  have hspeed :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        0 < gExt.inner (γ t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
          (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) := by
    intro t _ht
    change
      0 < gExt.inner
        (intrinsicGeodesic
          (I := 𝓘(Real, E)) gExt hExt x u t)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x u) t 1)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (intrinsicGeodesic
            (I := 𝓘(Real, E)) gExt hExt x u) t 1)
    rw [intrinsicGeodesic_speedSq_eq
      (I := 𝓘(Real, E)) gExt hExt x u t]
    exact gExt.pos x u hune
  let ell : Real := Real.sqrt (gExt.inner x u u)
  have hell0 : 0 ≤ ell := Real.sqrt_nonneg _
  have hellL : ell ≤ L := by
    simpa only [ell, gExt] using hu
  have hvnn : 0 ≤ gExt.inner x u u :=
    (gExt.pos x u hune).le
  have hsqLe : ell ^ 2 ≤ L ^ 2 := by
    have hL0 : 0 ≤ L := hell0.trans hellL
    nlinarith
  have hellSq : gExt.inner x u u = ell ^ 2 := by
    dsimp only [ell]
    exact (Real.sq_sqrt hvnn).symm
  let κ : Real := K * ell ^ 2
  have hκ0 : 0 ≤ κ := mul_nonneg hK (sq_nonneg ell)
  have hκπ : κ < (Real.pi / 2) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsqLe hK).trans_lt hsmall
  have hcurv :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        gExt.inner (γ t)
            (Geometry.Curvature.riemannOp
              (Geometry.Connection.LeviCivita
                (I := 𝓘(Real, E)) gExt)
              (γ t) (J t)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ t))
            (J t) ≤
          κ * gExt.inner (γ t) (J t) (J t) := by
    intro t ht
    have hz : ‖γ t‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, intrExtLaunch] using hfence t ht
    have hquad :=
      intrExt_quad_le
        (I := I) g hEnorm p hR hloc hz (hRm (γ t) hz)
          (J t) (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
    have hspeedEq :
        gExt.inner (γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) =
          gExt.inner x u u := by
      simpa only [γ, Variation.curveVelocity] using
        intrinsicGeodesic_speedSq_eq
          (I := 𝓘(Real, E)) gExt hExt x u t
    calc
      _ ≤ K * gExt.inner (γ t) (J t) (J t) *
          gExt.inner (γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) := by
        simpa only [gExt] using hquad
      _ = κ * gExt.inner (γ t) (J t) (J t) := by
        rw [hspeedEq, hellSq]
        dsimp only [κ]
        ring
  exact
    Variation.jacobi_pair_pos
      (I := 𝓘(Real, E)) gExt γ J hγ hgeo hJdiff hDJdiff
      (fun t _ht => hJac t) hJ0 hJ1 hspeed hJperp hκ0 hκπ hcurv

theorem exists_fenced_ext
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ∃ γ : Real → E,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ ∧
      IsGeodesic (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ ∧
      γ 0 = x ∧ γ 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1, ‖γ t‖ < 3 * R / 4) ∧
      Variation.arcLength (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) γ 0 1 =
        (riemannianEDistOf (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) x y).toReal := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · simpa only [γ, minJoin] using
      intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x
          (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · exact minJoin_zero (I := 𝓘(Real, E)) gExt hExt x y
  · exact minJoin_one (I := 𝓘(Real, E)) gExt hExt x y
  · simpa only [γ, gExt, intrExtJoin] using
      intrExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy
  · simpa only [γ, gExt, riemannianEDistOf] using
      minJoin_arcLength (I := 𝓘(Real, E)) gExt hExt x y

theorem exists_fenced_min
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ∃ join :
        intrPullBall (E := E) R →
        intrPullBall (E := E) R →
        Real → intrPullBall (E := E) R,
      ∀ x ∈ intrCore (E := E) R a,
      ∀ y ∈ intrCore (E := E) R a,
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (join x y) ∧
        IsGeodesicOn (I := 𝓘(Real, E))
          (intrPullMetric (I := I) g hEnorm p hloc)
          (join x y) (Set.Icc (0 : Real) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((join x y t : intrPullBall (E := E) R) : E)‖ <
            3 * R / 4) ∧
        Set.EqOn
          (fun t => ((join x y t : intrPullBall (E := E) R) : E))
          (intrExtJoin (I := I) g hEnorm p hR hloc
            (x : E) (y : E))
          (Set.Icc (0 : Real) 1) := by
  classical
  let join :
      intrPullBall (E := E) R →
      intrPullBall (E := E) R →
      Real → intrPullBall (E := E) R :=
    fun x y =>
      if hx : x ∈ intrCore (E := E) R a then
        if hy : y ∈ intrCore (E := E) R a then
          Classical.choose
            (exists_fenced_curve (I := I) g hEnorm p hR h4aR hloc
              (x := x) (y := y) hx hy)
        else fun _ => x
      else fun _ => x
  refine ⟨join, ?_⟩
  intro x hx y hy
  have hspec :=
    Classical.choose_spec
      (exists_fenced_curve (I := I) g hEnorm p hR h4aR hloc
        (x := x) (y := y) hx hy)
  simpa only [join, dif_pos hx, dif_pos hy] using hspec

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
