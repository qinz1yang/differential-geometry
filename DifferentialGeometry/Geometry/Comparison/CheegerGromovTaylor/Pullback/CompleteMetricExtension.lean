import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.EndpointPositivity
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.CurvatureBound
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve
import DifferentialGeometry.Geometry.Curvature.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Analysis.ODE.Stability.Tube
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Core.Geometry
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.Basic
import DifferentialGeometry.Geometry.Exponential.Variation.EndpointShape
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic
import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential Geodesic NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)

noncomputable def intrinsicCut (R : Real) (hR : 0 < R) :
    ContDiffBump (0 : E) :=
  ⟨3 * R / 4, 7 * R / 8, by linarith, by linarith⟩

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_smooth (R : Real) (hR : 0 < R) :
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (intrinsicCut (E := E) R hR : E → Real) :=
  (intrinsicCut (E := E) R hR).contDiff.contMDiff

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_range (R : Real) (hR : 0 < R) (z : E) :
    intrinsicCut (E := E) R hR z ∈ Set.Icc (0 : Real) 1 :=
  ⟨(intrinsicCut (E := E) R hR).nonneg,
    (intrinsicCut (E := E) R hR).le_one⟩

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_support (R : Real) (hR : 0 < R) :
    tsupport (intrinsicCut (E := E) R hR : E → Real) ⊆
      (intrinsicPullBall (E := E) R : Set E) := by
  rw [(intrinsicCut (E := E) R hR).tsupport_eq]
  change Metric.closedBall (0 : E) (7 * R / 8) ⊆
    Metric.ball (0 : E) R
  exact Metric.closedBall_subset_ball (by linarith)

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_compact (R : Real) (hR : 0 < R) :
    IsCompact (tsupport (intrinsicCut (E := E) R hR : E → Real)) := by
  let _ : ProperSpace E := FiniteDimensional.proper Real E
  rw [(intrinsicCut (E := E) R hR).tsupport_eq]
  exact isCompact_closedBall (0 : E) (7 * R / 8)

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_one (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (3 * R / 4)) :
    intrinsicCut (E := E) R hR z = 1 :=
  (intrinsicCut (E := E) R hR).one_of_mem_closedBall
    (Metric.ball_subset_closedBall hz)

omit [NeZero (Module.finrank Real E)] in
theorem intrinsicCut_one_closed (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    intrinsicCut (E := E) R hR z = 1 :=
  (intrinsicCut (E := E) R hR).one_of_mem_closedBall hz

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrinsicInner_subset (R : Real) (hR : 0 < R) :
    Metric.ball (0 : E) (3 * R / 4) ⊆
      (intrinsicPullBall (E := E) R : Set E) :=
  Metric.ball_subset_ball (by linarith)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
theorem intrinsicClosed_subset (R : Real) (hR : 0 < R) :
    Metric.closedBall (0 : E) (3 * R / 4) ⊆
      (intrinsicPullBall (E := E) R : Set E) :=
  Metric.closedBall_subset_ball (by linarith)

def intrinsicAgree (R : Real) : Opens (intrinsicPullBall (E := E) R) :=
  ⟨Subtype.val ⁻¹' Metric.ball (0 : E) (3 * R / 4),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrinsicAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrinsicAgree (E := E) R).isOpen)

noncomputable def intrinsicExtMetric
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
    (intrinsicPullBall (E := E) R)
    (intrinsicPullMetric (I := I) g hEnorm p hloc)
    (intrinsicCut (E := E) R hR : E → Real)
    (intrinsicCut_smooth (E := E) R hR)
    (intrinsicCut_range (E := E) R hR)
    (intrinsicCut_support (E := E) R hR)

theorem intrinsicExt_inner
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
    (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner z v w =
      (intrinsicPullMetric (I := I) g hEnorm p hloc).inner
        ⟨z, intrinsicClosed_subset (E := E) R hR hz⟩ v w := by
  simpa only [intrinsicExtMetric] using
    bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
      (flatModelMetric E) (intrinsicPullBall (E := E) R)
      (intrinsicPullMetric (I := I) g hEnorm p hloc)
      (intrinsicCut (E := E) R hR : E → Real)
      (intrinsicCut_smooth (E := E) R hR)
      (intrinsicCut_range (E := E) R hR)
      (intrinsicCut_support (E := E) R hR)
      (Metric.closedBall (0 : E) (3 * R / 4))
      (fun z hz => intrinsicCut_one_closed (E := E) R hR hz)
      (intrinsicClosed_subset (E := E) R hR) z hz v w

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem enorm_eq_sqrt_inner_self
    (q : SmoothRiemannianMetric 𝓘(Real, E) E)
    (z : E) (v : TangentSpace 𝓘(Real, E) z) :
    letI : RiemannianBundle
        (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
      ⟨q.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (q.inner z v v)) := by
  let _ : RiemannianBundle
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨q.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem tangent_eq_zero_model_self
    {z : E} {v : TangentSpace 𝓘(Real, E) z} (hv : v = 0) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z v = 0 := by
  rw [hv, map_zero]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] in
private theorem tangent_eq_zero_of_model_self
    {z : E} {v : TangentSpace 𝓘(Real, E) z}
    (hv : tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) z v = 0) :
    v = 0 := by
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(Real, E)) z).injective
  simpa only [map_zero] using hv

theorem intrinsicExt_restrict
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrinsicPullBall (E := E) R)).restrictOpen
          (I := 𝓘(Real, E)) (intrinsicAgree (E := E) R) =
      (intrinsicPullMetric (I := I) g hEnorm p hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrinsicAgree (E := E) R) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  have hz :
      ((z : intrinsicPullBall (E := E) R) : E) ∈
        Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall z.2
  let zU : intrinsicPullBall (E := E) R := z
  let vU : TangentSpace 𝓘(Real, E) zU :=
    (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) zU).symm
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) z v)
  let wU : TangentSpace 𝓘(Real, E) zU :=
    (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) zU).symm
      (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) z w)
  calc
    ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrinsicPullBall (E := E) R)).inner zU vU wU =
      (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner
        (zU : E) vU wU := by
      simpa only [mfderiv_subtype_val_apply,
        tangentSpaceModelContinuousLinearEquiv_apply,
        tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        SmoothRiemannianMetric.restrictOpen_inner
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
          (intrinsicPullBall (E := E) R) zU vU wU
    _ = (intrinsicPullMetric (I := I) g hEnorm p hloc).inner zU vU wU := by
      simpa only [zU, vU, wU,
        tangentSpaceModelContinuousLinearEquiv_apply,
        tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        intrinsicExt_inner (I := I) g hEnorm p hR hloc hz
          (tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z v)
          (tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z w)

private theorem intrinsicExt_geodesicOn_iff
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrinsicPullBall (E := E) R) (s : Set Real)
    (hstay : ∀ t ∈ s, ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ <
      3 * R / 4) :
    IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrinsicPullBall (E := E) R) : E)) s ↔
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) γ s := by
  let U := intrinsicPullBall (E := E) R
  let V := intrinsicAgree (E := E) R
  let gExt := intrinsicExtMetric g hEnorm p hR hloc
  let gPull := intrinsicPullMetric g hEnorm p hloc
  have hiff : IsGeodesicOn (gExt.restrictOpen U) γ s ↔ IsGeodesicOn gPull γ s := by
    apply isGeodesicOn_iff_of_metric_eventuallyEq
    intro t ht
    have hmem : γ t ∈ V := by
      change (γ t : E) ∈ Metric.ball (0 : E) (3 * R / 4)
      simpa only [Metric.mem_ball, dist_zero_right] using hstay t ht
    filter_upwards [V.isOpen.mem_nhds hmem] with z hz
    intro v w
    exact congrArg
      (fun metric : SmoothRiemannianMetric 𝓘(Real, E) V => metric.inner ⟨z, hz⟩ v w)
      (intrinsicExt_restrict g hEnorm p hR hloc)
  exact (geodesicOn_open_iff gExt U γ s).symm.trans hiff

theorem intrinsicPull_geo_of_ext
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrinsicPullBall (E := E) R) (s : Set Real)
    (hstay : ∀ t ∈ s, ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ <
      3 * R / 4)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrinsicPullBall (E := E) R) : E)) s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (intrinsicPullMetric (I := I) g hEnorm p hloc) γ s := by
  exact (intrinsicExt_geodesicOn_iff g hEnorm p hR hloc γ s hstay).mp hgeo

theorem intrinsicExt_geo_of_pull
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrinsicPullBall (E := E) R) (s : Set Real)
    (hstay : ∀ t ∈ s, ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ <
      3 * R / 4)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) γ s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
      (fun t => ((γ t : intrinsicPullBall (E := E) R) : E)) s := by
  exact (intrinsicExt_geodesicOn_iff g hEnorm p hR hloc γ s hstay).mpr hgeo

theorem intrinsicExt_pathLen
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
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) γ a b =
      Manifold.pathELength I
        ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  change Manifold.pathELength 𝓘(Real, E) γ a b =
    Manifold.pathELength I ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b
  symm
  apply Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq (intrinsicFramedExp g hEnorm p)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact Filter.Eventually.of_forall
      (fun _ => (intrinsicFrame_smooth g hEnorm p).mdifferentiableAt (by decide))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    symm
    let v : TangentSpace 𝓘(Real, E) (γ t) :=
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1
    have hExtNorm :
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner (γ t) v v)) := by
      exact enorm_eq_sqrt_inner_self (E := E) gExt (γ t) v
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
          (intrinsicPullMetric (I := I) g hEnorm p hloc).inner
            ⟨γ t, intrinsicClosed_subset (E := E) R hR
              (hstay t ⟨ht.1.le, ht.2.le⟩)⟩ v v :=
        intrinsicExt_inner (I := I) g hEnorm p hR hloc
          (hstay t ⟨ht.1.le, ht.2.le⟩) v v
      _ = intrinsicFrameMetric (I := I) g hEnorm p (γ t) v v :=
        intrinsicPullMetric_inner (I := I) g hEnorm p hloc _ v v
      _ = g.inner
          (intrinsicFramedExp (I := I) g hEnorm p (γ t))
          (mfderiv 𝓘(Real, E) I
            (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v)
          (mfderiv 𝓘(Real, E) I
            (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v) := by
        simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
          intrinsicFrameMetric_apply (I := I) g hEnorm p (γ t)
            (tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (γ t) v)
            (tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (γ t) v)

theorem intrinsicExt_radial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ ≤ 3 * R / 4) :
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun t : Real => Real.smoothTransition t • z) 0 1 =
      ENNReal.ofReal ‖z‖ := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
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
      (intrinsicExt_pathLen (I := I) g hEnorm p hR hloc hγone hstay)
  let zU : intrinsicPullBall (E := E) R :=
    ⟨z, intrinsicClosed_subset (E := E) R hR (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz)⟩
  let _ : RiemannianBundle
      (fun y : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have hradC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
        (intrinsicRadial (E := E) zU) (Set.Icc (0 : Real) 1) :=
    ((intrinsicRadial_smooth (E := E) zU).of_le (by norm_num)).contMDiffOn
  have hpull :=
    intrinsicPull_pathLen (I := I) g hEnorm p hloc hradC1
  have hrad :=
    intrinsicRadial_len (I := I) g hEnorm p hloc zU
  calc
    Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) 0 1 := hext
    _ = Manifold.pathELength 𝓘(Real, E)
        (intrinsicRadial (E := E) zU) 0 1 := by
      rw [show
        (intrinsicFramedExp (I := I) g hEnorm p) ∘ γ =
          intrinsicExpOn (I := I) g hEnorm p R ∘ intrinsicRadial (E := E) zU by
        funext t
        rfl]
      exact hpull
    _ = ENNReal.ofReal ‖z‖ := by
      simpa only [zU] using hrad

theorem intrinsicExt_edist_le
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) x y ≤
      ENNReal.ofReal (2 * a) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E :=
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
    rw [intrinsicExt_radial_len (I := I) g hEnorm p hR hloc hz] at hdist
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

theorem intrinsicExt_complete
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    RiemannianMetricComplete (I := 𝓘(Real, E))
      (intrinsicExtMetric (I := I) g hEnorm p hR hloc) := by
  simpa only [intrinsicExtMetric] using
    RiemannianMetricComplete.bumpExtend_complete
      (I := 𝓘(Real, E)) (flatModelMetric E)
      (RiemannianMetricComplete.flatModel_complete (E := E))
      (intrinsicPullBall (E := E) R)
      (intrinsicPullMetric (I := I) g hEnorm p hloc)
      (intrinsicCut (E := E) R hR : E → Real)
      (intrinsicCut_smooth (E := E) R hR)
      (intrinsicCut_range (E := E) R hR)
      (intrinsicCut_support (E := E) R hR)
      (intrinsicCut_compact (E := E) R hR)

noncomputable def intrinsicExtJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) : Real → E := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  exact minJoin (I := 𝓘(Real, E)) gExt hExt x y

@[simp] theorem intrinsicExtJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrinsicExtJoin (I := I) g hEnorm p hR hloc x y 0 = x := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  change minJoin (I := 𝓘(Real, E)) gExt hExt x y 0 = x
  exact minJoin_zero (I := 𝓘(Real, E)) gExt hExt x y

@[simp] theorem intrinsicExtJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrinsicExtJoin (I := I) g hEnorm p hR hloc x y 1 = y := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  change minJoin (I := 𝓘(Real, E)) gExt hExt x y 1 = y
  exact minJoin_one (I := 𝓘(Real, E)) gExt hExt x y

theorem intrinsicExtJoin_smooth
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
      (intrinsicExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  exact intrinsicGeodesic_contMDiff
    (I := 𝓘(Real, E)) gExt hExt x
      (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

theorem intrinsicExtJoin_geo
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
      (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
      (intrinsicExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  exact intrinsicGeodesic_isGeodesic
    (I := 𝓘(Real, E)) gExt hExt x
      (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

private theorem intrinsicExtJoin_budget
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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) x y ≤
          ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtJoin (I := I) g hEnorm p hR hloc x y t‖ <
        3 * R / 4 := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  have hγzero : γ 0 = x := by
    dsimp only [γ]
    exact minJoin_zero (I := 𝓘(Real, E)) gExt hExt x y
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
    simpa only [γ, intrinsicExtJoin] using (not_lt.mp hnot)
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    rw [hγzero]
    exact hx.trans_lt haB
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
  have hηmem : ∀ s : Real, η s ∈ intrinsicPullBall (E := E) R := by
    intro s
    exact intrinsicClosed_subset (E := E) R hR (hηstay s)
  let ηU : Real → intrinsicPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := intrinsicPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
        (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
        (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  let xU : intrinsicPullBall (E := E) R :=
    ⟨x, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : intrinsicPullBall (E := E) R :=
    ⟨γ τ, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hη0 : η 0 = x := by
    dsimp only [η, f, Function.comp_apply]
    rw [Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, hγzero]
  have hη1 : η 1 = γ τ := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have hηU0 : ηU 0 = xU := by
    apply Subtype.ext
    exact hη0
  have hηU1 : ηU 1 = zU := by
    apply Subtype.ext
    exact hη1
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let _ : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen :
      Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    rw [show
      (intrinsicFramedExp (I := I) g hEnorm p) ∘ η =
        intrinsicExpOn (I := I) g hEnorm p R ∘ ηU by
      funext t
      rfl]
    exact (intrinsicPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen :
      Manifold.pathELength 𝓘(Real, E) η 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (intrinsicExt_pathLen (I := I) g hEnorm p hR hloc hηC1
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
    intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc xU
  have hz0 :=
    intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc zU
  have hx0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrinsicZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
          (intrinsicZero (E := E) hR) xU =
      ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrinsicZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
          (intrinsicZero (E := E) hR) zU =
      ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have htri :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrinsicZero (E := E) hR) zU ≤
        Manifold.riemannianEDist 𝓘(Real, E)
            (intrinsicZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
    Manifold.riemannianEDist_triangle
  have hB :
      ENNReal.ofReal (3 * R / 4) ≤ ENNReal.ofReal (a + L) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrinsicZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
            (intrinsicZero (E := E) hR) xU +
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

theorem intrinsicExtJoin_fenced
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
      ‖intrinsicExtJoin (I := I) g hEnorm p hR hloc x y t‖ <
        3 * R / 4 := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc) x y ≤
        ENNReal.ofReal (2 * a) :=
    intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
  exact intrinsicExtJoin_budget (I := I) g hEnorm p hR hloc hx
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
    {x y : intrinsicPullBall (E := E) R}
    (hγfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E) t‖ <
          3 * R / 4) :
    ∃ γU : Real → intrinsicPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : intrinsicPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : intrinsicPullBall (E := E) R) : E))
        (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  classical
  let γ : Real → E :=
    intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicExtJoin_smooth (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγgeo :
      IsGeodesic (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ := by
    simpa only [γ] using
      intrinsicExtJoin_geo (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγfence' : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖γ t‖ < 3 * R / 4 := by
    simpa only [γ] using hγfence
  let U := intrinsicPullBall (E := E) R
  let η : ℝ → U := fun t => if ht : γ t ∈ U then ⟨γ t, ht⟩ else x
  have hV : IsOpen (γ ⁻¹' (U : Set E)) := U.isOpen.preimage hγinf.continuous
  have hηEq (t : ℝ) (ht : γ t ∈ U) : (Subtype.val ∘ η) =ᶠ[𝓝 t] γ := by
    filter_upwards [hV.mem_nhds ht] with s hs
    change γ s ∈ U at hs
    simp only [η, Function.comp_apply, dif_pos hs]
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η (γ ⁻¹' (U : Set E)) := by
    intro t ht
    have hval : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ η) t :=
      hγinf.contMDiffAt.congr_of_eventuallyEq (hηEq t ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff U η t).mp hval).contMDiffWithinAt
  have hstay : MapsTo γ (uIcc (0 : ℝ) 1) U := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    change γ t ∈ Metric.ball (0 : E) R
    rw [Metric.mem_ball, dist_zero_right]
    exact (hγfence' t ht).trans (by linarith)
  obtain ⟨γU, hγUinf, hGerm⟩ := hη.exists_extension_uIcc hV hstay
  have hGermVal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Subtype.val ∘ γU) =ᶠ[𝓝 t] γ := by
    exact ((hGerm t (by rwa [uIcc_of_le zero_le_one])).fun_comp Subtype.val).trans
      (hηEq t (hstay (by rwa [uIcc_of_le zero_le_one])))
  have hEq : EqOn (fun t => (γU t : E)) γ (Icc (0 : ℝ) 1) :=
    fun t ht => (hGermVal t ht).eq_of_nhds
  have hγUgeoExt :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => (γU t : E)) (Icc (0 : ℝ) 1) := by
    intro t ht
    have heq := hGermVal t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.eq_of_nhds heq (hγgeo t)
  have hγUfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖((γU t : intrinsicPullBall (E := E) R) : E)‖ < 3 * R / 4 := by
    intro t ht
    calc
      ‖((γU t : intrinsicPullBall (E := E) R) : E)‖ = ‖γ t‖ :=
        congrArg norm (hEq ht)
      _ < 3 * R / 4 := hγfence' t ht
  have hγUgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) :=
    intrinsicPull_geo_of_ext (I := I) g hEnorm p hR hloc γU
      (Set.Icc (0 : Real) 1) hγUfence hγUgeoExt
  refine ⟨γU, hγUinf, hγUgeo, ?_, ?_, hγUfence, ?_⟩
  · apply Subtype.ext
    simpa only [γ, intrinsicExtJoin_zero] using
      hEq (x := (0 : Real)) (by norm_num)
  · apply Subtype.ext
    simpa only [γ, intrinsicExtJoin_one] using
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
    {x y : intrinsicPullBall (E := E) R}
    (hx : x ∈ intrinsicCore (E := E) R a)
    (hy : y ∈ intrinsicCore (E := E) R a) :
    ∃ γU : Real → intrinsicPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : intrinsicPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : intrinsicPullBall (E := E) R) : E))
        (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  apply exists_join_curve (I := I) g hEnorm p hR hloc
  exact intrinsicExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy

theorem intrinsicPull_edist_eq_ext_of_budget
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrinsicPullBall (E := E) R}
    (hx : ‖(x : E)‖ ≤ a)
    (hd :
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) <
          ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  let _ : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let _ (z : intrinsicPullBall (E := E) R) :
      NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let _ (z : intrinsicPullBall (E := E) R) :
      NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let _ : ∀ z : intrinsicPullBall (E := E) R,
      ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let _ : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : PseudoEMetricSpace (intrinsicPullBall (E := E) R) :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E)
      (intrinsicPullBall (E := E) R)
  let _ : IsRiemannianManifold 𝓘(Real, E)
      (intrinsicPullBall (E := E) R) :=
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
      ∀ {γ : Real → intrinsicPullBall (E := E) R} {s t : Real},
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t) →
        (∀ u ∈ Set.Icc s t,
          ‖((γ u : intrinsicPullBall (E := E) R) : E)‖ ≤ 3 * R / 4) →
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength 𝓘(Real, E)
            (fun u => ((γ u : intrinsicPullBall (E := E) R) : E)) s t := by
    intro γ s t hγ hstay
    let η : Real → E :=
      fun u => ((γ u : intrinsicPullBall (E := E) R) : E)
    have hη :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrinsicPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγ
    have hpull :
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      rw [show
        (intrinsicFramedExp (I := I) g hEnorm p) ∘ η =
          intrinsicExpOn (I := I) g hEnorm p R ∘ γ by
        funext u
        rfl]
      exact (intrinsicPull_pathLen (I := I) g hEnorm p hloc hγ).symm
    have hext :
        Manifold.pathELength 𝓘(Real, E) η s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      simpa only [gExt] using
        (intrinsicExt_pathLen (I := I) g hEnorm p hR hloc hη
          (fun u hu => by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hstay u hu))
    exact hpull.trans hext.symm
  apply le_antisymm
  · obtain ⟨γ, hγinf, _, hγ0, hγ1, hγstay, hγeq⟩ :=
      exists_join_curve (I := I) g hEnorm p hR hloc
        (intrinsicExtJoin_budget (I := I) g hEnorm p hR hloc
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
            (fun t => ((γ t : intrinsicPullBall (E := E) R) : E)) 0 1 :=
      hlen_of_stay hγC1 (fun t ht => (hγstay t ht).le)
    have hjoin :
        Manifold.pathELength 𝓘(Real, E)
            (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
            0 1 =
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := by
      calc
        Manifold.pathELength 𝓘(Real, E)
              (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
              0 1 =
            ENNReal.ofReal
              ((Manifold.riemannianEDist 𝓘(Real, E)
                (x : E) (y : E)).toReal) := by
          simpa only [intrinsicExtJoin, gExt] using
            (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E))
        _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
          ENNReal.ofReal_toReal hExtTop
    calc
      Manifold.riemannianEDist 𝓘(Real, E) x y ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := hpath
      _ = Manifold.pathELength 𝓘(Real, E)
          (fun t => ((γ t : intrinsicPullBall (E := E) R) : E)) 0 1 := hlen
      _ = Manifold.pathELength 𝓘(Real, E)
          (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
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
          ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ ≤ 3 * R / 4 := by
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
      have hx0 := intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc x
      have hz0 := intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc (γ t)
      have hnormE :
          ENNReal.ofReal ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ <
            ENNReal.ofReal (a + L) := by
        calc
          ENNReal.ofReal ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ =
              Manifold.riemannianEDist 𝓘(Real, E)
                (intrinsicZero (E := E) hR) (γ t) := by
            change
              ENNReal.ofReal ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ =
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                  (intrinsicZero (E := E) hR) (γ t)
            exact hz0.symm
          _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
                (intrinsicZero (E := E) hR) x +
              Manifold.riemannianEDist 𝓘(Real, E) x (γ t) :=
            Manifold.riemannianEDist_triangle
          _ < ENNReal.ofReal a + ENNReal.ofReal L := by
            have hx0' :
                Manifold.riemannianEDist 𝓘(Real, E)
                    (intrinsicZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖ := by
              change
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                    (intrinsicZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖
              exact hx0
            rw [hx0']
            exact ENNReal.add_lt_add_of_le_of_lt
              ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hx) hdist_lt
          _ = ENNReal.ofReal (a + L) := by
            rw [← ENNReal.ofReal_add ha hLPos.le]
      have hnorm :
          ‖((γ t : intrinsicPullBall (E := E) R) : E)‖ < a + L :=
        (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos ha hLPos)).mp
          hnormE
      exact (hnorm.trans hbudget).le
    let η : Real → E :=
      fun t => ((γ t : intrinsicPullBall (E := E) R) : E)
    have hηC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
          (Set.Icc (0 : Real) 1) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrinsicPullBall (E := E) R)).of_le
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

theorem intrinsicCore_edist_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrinsicPullBall (E := E) R}
    (hx : x ∈ intrinsicCore (E := E) R a)
    (hy : y ∈ intrinsicCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicPullMetric (I := I) g hEnorm p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) := by
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
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) ≤
        ENNReal.ofReal (2 * a) :=
    intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
  have hdistLt :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) <
        ENNReal.ofReal L :=
    hdistLe.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hLPos).2 h2aL)
  apply intrinsicPull_edist_eq_ext_of_budget
    (I := I) g hEnorm p hR hloc hx hdistLt
  dsimp only [L]
  linarith

noncomputable def intrinsicExtLaunch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x : E) (v : TangentSpace 𝓘(Real, E) x) : Real → E := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => enorm_eq_sqrt_inner_self (E := E) gExt z w
  exact intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v

theorem intrinsicExt_shortLaunch_fenced
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
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ <
        3 * R / 4 := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => enorm_eq_sqrt_inner_self (E := E) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγzero : γ 0 = x := by
    dsimp only [γ]
    exact intrinsicGeodesic_zero (I := 𝓘(Real, E)) gExt hExt x v
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
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using (not_lt.mp hnot)
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    rw [hγzero]
    exact hx.trans_lt haB
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
    change Manifold.riemannianEDist 𝓘(Real, E) (γ 0) (γ τ) ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (τ - 0)) at h
    rw [hγzero, sub_zero] at h
    exact h
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
  let xU : intrinsicPullBall (E := E) R :=
    ⟨x, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : intrinsicPullBall (E := E) R :=
    ⟨γ τ, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hdistEq :
      riemannianEDistOf (I := 𝓘(Real, E))
          (intrinsicPullMetric (I := I) g hEnorm p hloc) xU zU =
        riemannianEDistOf (I := 𝓘(Real, E)) gExt x (γ τ) := by
    apply intrinsicPull_edist_eq_ext_of_budget
      (I := I) g hEnorm p hR hloc (a := a) (L := Lstar)
    · exact hx
    · simpa only [gExt, riemannianEDistOf] using hdistLt
    · exact hbudgetStar
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let _ : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hdistPull :
      Manifold.riemannianEDist 𝓘(Real, E) xU zU <
        ENNReal.ofReal Lstar := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull xU zU <
      ENNReal.ofReal Lstar
    rw [hdistEq]
    simpa only [gExt, riemannianEDistOf] using hdistLt
  have hx0 := intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc xU
  have hz0 := intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc zU
  have hx0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrinsicZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull
        (intrinsicZero (E := E) hR) xU =
      ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrinsicZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E)) gPull
        (intrinsicZero (E := E) hR) zU =
      ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have hB :
      ENNReal.ofReal (3 * R / 4) <
        ENNReal.ofReal (a + Lstar) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrinsicZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
              (intrinsicZero (E := E) hR) xU +
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

theorem intrinsicExt_scale_bound
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
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hbudget : a + L < 3 * R / 4)
    (hend : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤
        a + L / 2 := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => enorm_eq_sqrt_inner_self (E := E) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγzero : γ 0 = x := by
    dsimp only [γ]
    exact intrinsicGeodesic_zero (I := 𝓘(Real, E)) gExt hExt x v
  let ell : Real := Real.sqrt (gExt.inner x v v)
  have hγ1 : γ 1 = y := by
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using hend
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hell : 0 ≤ ell := Real.sqrt_nonneg _
  have hell_le : ell ≤ L := by
    simpa only [ell, gExt] using hv
  have hL : 0 ≤ L := hell.trans hell_le
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hfence :
      ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ < 3 * R / 4 := by
    simpa only [γ, gExt, hExt, intrinsicExtLaunch] using
      intrinsicExt_shortLaunch_fenced (I := I) g hEnorm p hR hloc hx v hv
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
  let xU : intrinsicPullBall (E := E) R :=
    ⟨x, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let yU : intrinsicPullBall (E := E) R :=
    ⟨y, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hy.trans haInner)⟩
  let zU : intrinsicPullBall (E := E) R :=
    ⟨γ t, intrinsicClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hfence t ht).le)⟩
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let _ : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hnorm_of_dist :
      ∀ (wU : intrinsicPullBall (E := E) R) (hw : ‖(wU : E)‖ ≤ a)
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
      intrinsicPull_edist_eq_ext_of_budget
        (I := I) g hEnorm p hR hloc hw hdistLt hbudgetStar
    have hw0 :=
      intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc wU
    have hz0 :=
      intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc zU
    have hbound :
        ENNReal.ofReal ‖(zU : E)‖ ≤ ENNReal.ofReal (a + B) := by
      calc
        ENNReal.ofReal ‖(zU : E)‖ =
            riemannianEDistOf (I := 𝓘(Real, E)) gPull
              (intrinsicZero (E := E) hR) zU := hz0.symm
        _ ≤ riemannianEDistOf (I := 𝓘(Real, E)) gPull
              (intrinsicZero (E := E) hR) wU +
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
    change Manifold.riemannianEDist 𝓘(Real, E) (γ 0) (γ t) ≤
      ENNReal.ofReal (ell * (t - 0)) at h
    rw [hγzero, sub_zero] at h
    exact h
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
  simpa only [γ, gExt, hExt, intrinsicExtLaunch] using
    (show ‖γ t‖ ≤ a + L / 2 by nlinarith)

theorem intrinsicExt_short_bound
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
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        2 * a)
    (hend : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤ 2 * a := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  intro t ht
  have hbound :=
    intrinsicExt_scale_bound (I := I) g hEnorm p hR hloc hx hy v hv
      (by linarith) hend t ht
  nlinarith

private theorem intrinsicExt_quad_le
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
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
    gExt.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gExt)
          z J V V)
        J ≤
      K * gExt.inner z J J * gExt.inner z V V := by
  let U := intrinsicPullBall (E := E) R
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  have hzBall : z ∈ Metric.ball (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzClosed : z ∈ Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall hzBall
  let zU : U := ⟨z, intrinsicInner_subset (E := E) R hR hzBall⟩
  have hmetric : ∀ᶠ y in 𝓝 zU, ∀ v w : TangentSpace 𝓘(Real, E) y,
      (gExt.restrictOpen U).inner y v w = gPull.inner y v w := by
    have hnear : ∀ᶠ y : U in 𝓝 zU, (y : E) ∈ Metric.ball (0 : E) (3 * R / 4) :=
      (continuous_subtype_val.continuousAt.tendsto)
        (Metric.isOpen_ball.mem_nhds hzBall)
    filter_upwards [hnear] with y hy v w
    exact intrinsicExt_inner g hEnorm p hR hloc
      (Metric.ball_subset_closedBall hy) v w
  have hcurv := Geometry.Curvature.metricRm04At_eq_of_metric_eventuallyEq
    (gExt.restrictOpen U) gPull zU hmetric
  have hcurv' := congrArg (fun T => T (Geometry.Curvature.vec4 J V V J)) hcurv
  have hrest := Geometry.Curvature.metricRm04StandardAt_restrictOpen
    gExt U zU
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm J)
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm V)
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm V)
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm J)
  simp only [mfderiv_subtype_val_apply] at hrest
  have hcurvEq : Geometry.Curvature.metricRm04StandardAt gExt z J V V J =
      Geometry.Curvature.metricRm04StandardAt gPull zU J V V J := by
    have hrest' : Geometry.Curvature.metricRm04StandardAt
        (gExt.restrictOpen U) zU J V V J =
        Geometry.Curvature.metricRm04StandardAt gExt z J V V J := by
      simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using hrest
    exact hrest'.symm.trans hcurv'
  have hquad : gPull.inner zU
      (Geometry.Curvature.riemannOp (Geometry.Connection.LeviCivita gPull) zU J V V) J ≤
      K * gPull.inner zU J J * gPull.inner zU V V := by
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using!
      intrinsicPull_quad_le g hEnorm p hloc zU hRm J V
  have hinner : gExt.inner z
      (Geometry.Curvature.riemannOp
        (Geometry.Connection.LeviCivita gExt) z J V V) J =
      gPull.inner zU
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita gPull) zU J V V) J := by
    exact (gExt.symm z _ _).trans
      ((Geometry.Curvature.rm04_eq_inner gExt z J V J).symm.trans
        (hcurvEq.trans ((Geometry.Curvature.rm04_eq_inner gPull zU J V J).trans
          (gPull.symm zU _ _))))
  change gExt.inner z _ J ≤ _
  rw [hinner]
  exact hquad.trans_eq (by
    rw [intrinsicExt_inner g hEnorm p hR hloc hzClosed J J,
      intrinsicExt_inner g hEnorm p hR hloc hzClosed V V])

theorem intrinsicExt_not_conj_of_shortLaunch
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
        ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ <
          3 * R / 4)
    (hv :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
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
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
      (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w => enorm_eq_sqrt_inner_self (E := E) gExt z w
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (v : E) := by
  classical
  let eNormedAddCommGroup : NormedAddCommGroup E := inferInstance
  let eNormedSpace : NormedSpace Real E := inferInstance
  let eENormSMulClass : ENormSMulClass Real E := inferInstance
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w => enorm_eq_sqrt_inner_self (E := E) gExt z w
  let _ (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    eNormedAddCommGroup
  let _ (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    eNormedSpace
  let _ (z : E) : ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    eENormSMulClass
  let vModel : E :=
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) x v
  have hvModelT :
      (show TangentSpace 𝓘(Real, E) x from vModel) = v := by
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) x).injective
    simp only [vModel, tangentSpaceModelContinuousLinearEquiv_apply]
    rfl
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x vModel
  let γ : ℝ → E := intrinsicGeodesic (I := 𝓘(ℝ, E)) gExt hExt x v
  have hradial : VolumeComparison.radialCurve (I := 𝓘(ℝ, E)) gExt x vModel = γ := by
    have h := radialCurve_eq_intrinsicGeodesic (I := 𝓘(ℝ, E)) gExt hExt x vModel
    rw [hvModelT] at h
    exact h
  have hvnn : 0 ≤ gExt.inner x v v := metric_inner_self_nonneg gExt x v
  have hvL : gExt.inner x v v ≤ L ^ 2 := by
    have hv' : Real.sqrt (gExt.inner x v v) ≤ L := hv
    have hsqrt0 := Real.sqrt_nonneg (gExt.inner x v v)
    have hL0 : 0 ≤ L := hsqrt0.trans hv'
    nlinarith [Real.sq_sqrt hvnn]
  have hcurv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ W : TangentSpace 𝓘(ℝ, E) (γ t),
      gExt.inner (γ t)
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(ℝ, E)) gExt) (γ t) W
          (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t)
          (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t)) W ≤
        (K * L ^ 2) * gExt.inner (γ t) W W := by
    intro t ht W
    have hz : ‖γ t‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, intrinsicExtLaunch] using hfence t (Ioo_subset_Icc_self ht)
    have hquad := intrinsicExt_quad_le (I := I) g hEnorm p hR hloc hz
      (hRm (γ t) hz) W (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t)
    have hspeed : gExt.inner (γ t)
        (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t)
        (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t) = gExt.inner x v v := by
      simpa only [γ, Variation.curveVelocity] using!
        intrinsicGeodesic_speedSq_eq (I := 𝓘(ℝ, E)) gExt hExt x v t
    have hWn : 0 ≤ gExt.inner (γ t) W W := metric_inner_self_nonneg gExt (γ t) W
    calc
      _ ≤ K * gExt.inner (γ t) W W * gExt.inner (γ t)
          (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t)
          (Variation.curveVelocity (I := 𝓘(ℝ, E)) γ t) := hquad
      _ = K * gExt.inner (γ t) W W * gExt.inner x v v := by rw [hspeed]
      _ ≤ K * gExt.inner (γ t) W W * L ^ 2 :=
        mul_le_mul_of_nonneg_left hvL (mul_nonneg hK hWn)
      _ = (K * L ^ 2) * gExt.inner (γ t) W W := by ring
  have hxdom : (show TangentSpace 𝓘(ℝ, E) x from vModel) ∈
      expDomain (I := 𝓘(ℝ, E)) gExt x := by
    rw [expDomain_eq_univ_of_completeSpace (I := 𝓘(ℝ, E)) gExt hExt x]
    exact mem_univ _
  have hinj := injective_mfderiv_expMap_of_curvature_upper_bound
    (I := 𝓘(ℝ, E)) gExt x vModel hxdom hsmall (by
      rw [hradial]
      exact hcurv)
  have heq : (fun b : E => expMapIntrinsic (I := 𝓘(ℝ, E)) gExt hExt x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm b)) =
      (fun b : E => expMap (I := 𝓘(ℝ, E)) gExt x
        (show TangentSpace 𝓘(ℝ, E) x from b)) := by
    funext b
    rw [tangentSpaceModelContinuousLinearEquiv_symm_apply,
      expMap_eq_expMapIntrinsic (I := 𝓘(ℝ, E)) gExt hExt x]
  unfold IsConjVec
  rw [not_not, heq]
  exact hinj.comp (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) vModel).symm.injective

theorem intrinsicExt_pair_pos
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
        ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x u t‖ <
          3 * R / 4)
    (hu :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x u u) ≤
        L)
    (hwne : (w : E) ≠ 0)
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2) :
    let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
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
      (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
    let γ : Real → E :=
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
    let J : Real → E :=
      intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
    0 < gExt.inner (γ 1)
      (CovariantDerivativeAlong.covDerivAlong
        (I := 𝓘(Real, E)) gExt γ J 1) (J 1) := by
  classical
  let eNormedAddCommGroup : NormedAddCommGroup E := inferInstance
  let eNormedSpace : NormedSpace Real E := inferInstance
  let eENormSMulClass : ENormSMulClass Real E := inferInstance
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v₁ v₂; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  let _ (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    eNormedAddCommGroup
  let _ (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    eNormedSpace
  let _ (z : E) : ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    eENormSMulClass
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
  let J : Real → E :=
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w
  have hnot :
      ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x (u : E) := by
    simpa only [gExt, hExt] using
      intrinsicExt_not_conj_of_shortLaunch
        (I := I) g hEnorm p hR hloc u hfence hu hK hRm hsmall
  have hJ1 : J 1 ≠ 0 := by
    intro hzero
    apply hnot
    apply (isConjVec_iff_jacobi
      (I := 𝓘(Real, E)) gExt hExt x (u : E)).mpr
    refine ⟨w, hwne, ?_⟩
    have hzeroT :
        intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u w 1 = 0 := by
      apply tangent_eq_zero_of_model_self (E := E)
      convert hzero using 1; rfl
    change intrinsicJacobi
      (I := 𝓘(Real, E)) gExt hExt x u w 1 = 0
    exact hzeroT
  have hγ :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x u
  have hJdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γ J t) t := by
    simpa only [γ, J] using
      (intrinsicJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x u w t).1
  have hDJdiff (t : Real) :
      DifferentiableAt Real
        (CovariantDerivativeAlong.chartRepAt
          (I := 𝓘(Real, E)) γ
          (fun s => CovariantDerivativeAlong.covDerivAlong
            (I := 𝓘(Real, E)) gExt γ J s) t) t := by
    simpa only [γ, J] using
      (intrinsicJacobi_diff
        (I := 𝓘(Real, E)) gExt hExt x u w t).2
  have hJacobian :
      Variation.IsJacobiAlong (I := 𝓘(Real, E)) gExt γ J := by
    exact intrinsic_jacobi
      (I := 𝓘(Real, E)) gExt hExt x (u : E) (w : E)
  have hJ0 : J 0 = 0 := by
    simpa only [J, tangentSpaceModelContinuousLinearEquiv_apply] using
      tangent_eq_zero_model_self (E := E)
        (intrinsicJacobi_zero
          (I := 𝓘(Real, E)) gExt hExt x u w)
  let ell : Real := Real.sqrt (gExt.inner x u u)
  have hell0 : 0 ≤ ell := Real.sqrt_nonneg _
  have hellL : ell ≤ L := by
    simpa only [ell, gExt] using hu
  have hvnn : 0 ≤ gExt.inner x u u :=
    metric_inner_self_nonneg gExt x u
  have hsqLe : ell ^ 2 ≤ L ^ 2 := by
    have hL0 : 0 ≤ L := hell0.trans hellL
    nlinarith
  have hellSq : gExt.inner x u u = ell ^ 2 := by
    dsimp only [ell]
    exact (Real.sq_sqrt hvnn).symm
  let κ : Real := K * ell ^ 2
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
      simpa only [γ, gExt, hExt, intrinsicExtLaunch] using hfence t ht
    have hquad :=
      intrinsicExt_quad_le
        (I := I) g hEnorm p hR hloc hz (hRm (γ t) hz)
          (J t) (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
    have hspeedEq :
        gExt.inner (γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t)
            (Variation.curveVelocity (I := 𝓘(Real, E)) γ t) =
          gExt.inner x u u := by
      change gExt.inner
          (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u) t 1)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
            (intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u) t 1) =
        gExt.inner x u u
      convert intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x u t using 1
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
  exact Variation.jacobi_pair_pos
    (I := 𝓘(Real, E)) gExt γ J zero_le_one isOpen_univ (subset_univ _)
    (hγ.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)).contMDiffOn
    (fun t _ => hJdiff t) (fun t _ => hDJdiff t) (fun t _ => hJacobian t) hJ0
    (fun hz => hJ1 (hz 1 (right_mem_Icc.mpr zero_le_one)))
    (by simpa only [sub_zero, one_pow, mul_one] using hκπ)
    (fun t ht => hcurv t (Ioo_subset_Icc_self ht))

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
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ ∧
      γ 0 = x ∧ γ 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1, ‖γ t‖ < 3 * R / 4) ∧
      Variation.arcLength (I := 𝓘(Real, E))
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ 0 1 =
        (riemannianEDistOf (I := 𝓘(Real, E))
          (intrinsicExtMetric (I := I) g hEnorm p hR hloc) x y).toReal := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let _ : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let _ : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let _ : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let _ : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let _ : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => enorm_eq_sqrt_inner_self (E := E) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · exact intrinsicGeodesic_isGeodesic
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · exact minJoin_zero (I := 𝓘(Real, E)) gExt hExt x y
  · exact minJoin_one (I := 𝓘(Real, E)) gExt hExt x y
  · simpa only [γ, gExt, intrinsicExtJoin] using
      intrinsicExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy
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
        intrinsicPullBall (E := E) R →
        intrinsicPullBall (E := E) R →
        Real → intrinsicPullBall (E := E) R,
      ∀ x ∈ intrinsicCore (E := E) R a,
      ∀ y ∈ intrinsicCore (E := E) R a,
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (join x y) ∧
        IsGeodesicOn (I := 𝓘(Real, E))
          (intrinsicPullMetric (I := I) g hEnorm p hloc)
          (join x y) (Set.Icc (0 : Real) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((join x y t : intrinsicPullBall (E := E) R) : E)‖ <
            3 * R / 4) ∧
        Set.EqOn
          (fun t => ((join x y t : intrinsicPullBall (E := E) R) : E))
          (intrinsicExtJoin (I := I) g hEnorm p hR hloc
            (x : E) (y : E))
          (Set.Icc (0 : Real) 1) := by
  classical
  let join :
      intrinsicPullBall (E := E) R →
      intrinsicPullBall (E := E) R →
      Real → intrinsicPullBall (E := E) R :=
    fun x y =>
      if hx : x ∈ intrinsicCore (E := E) R a then
        if hy : y ∈ intrinsicCore (E := E) R a then
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

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry

end
