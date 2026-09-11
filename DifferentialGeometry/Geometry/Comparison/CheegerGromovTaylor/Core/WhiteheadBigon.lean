import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Pullback.CompleteMetricExtension
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convexity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Geometry.Operator

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

theorem exists_short_scale
    {R a K : Real} (h4aR : 4 * a < R)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2) :
    ∃ L : Real,
      2 * a < L ∧
      a + L < 3 * R / 4 ∧
      K * L ^ 2 < (Real.pi / 2) ^ 2 := by
  let cap : Real := 3 * R / 4 - a
  have h2aCap : 2 * a < cap := by
    dsimp only [cap]
    linarith
  have hcont :
      Continuous (fun L : Real => K * L ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  have hcurv :
      ∀ᶠ L in 𝓝 (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcont.continuousAt (Iio_mem_nhds hsmall)
  have hcurvGT :
      ∀ᶠ L in 𝓝[>] (2 * a), K * L ^ 2 < (Real.pi / 2) ^ 2 :=
    hcurv.filter_mono inf_le_left
  have hwindow :
      ∀ᶠ L in 𝓝[>] (2 * a), L ∈ Set.Ioo (2 * a) cap :=
    Ioo_mem_nhdsGT h2aCap
  obtain ⟨L, hcurvL, hL, hLcap⟩ :=
    (hcurvGT.and hwindow).exists
  refine ⟨L, hL, ?_, hcurvL⟩
  dsimp only [cap] at hLcap
  linarith

theorem intrinsicCore_min_regular
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    {pt q : intrinsicPullBall (E := E) R}
    (hpt : pt ∈ intrinsicCore (E := E) R a)
    (hq : q ∈ intrinsicCore (E := E) R a) :
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
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    let u :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let u :=
    minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  change
    ¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ :=
    exists_short_scale h4aR hsmall
  have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist :
      riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (q : E) ≤
        ENNReal.ofReal (2 * a) :=
    intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hpt hq haInner
  have hdistReal :
      (riemannianEDistOf
        (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal ≤
          2 * a :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
  have hu2a :
      Real.sqrt (gExt.inner (pt : E) u u) ≤ 2 * a := by
    rw [minimizingVec_len
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)]
    exact hdistReal
  have huL : Real.sqrt (gExt.inner (pt : E) u u) ≤ L :=
    hu2a.trans h2aL.le
  have hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc
          (pt : E) u t‖ < 3 * R / 4 :=
    intrinsicExt_shortLaunch_fenced
      (I := I) g hEnorm p hR hloc hpt u huL hbudget
  have hnot :=
    intrinsicExt_not_conj_of_shortLaunch
      (I := I) g hEnorm p hR hloc u hfence huL hK hRm hsmallL
  change
    ¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) at hnot
  exact hnot


theorem intrinsicExt_minVec_mem
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {pt q u : E} :
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
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    ∀ (B : ExponentialInverseBranch (I := 𝓘(Real, E)) gExt hExt pt),
      u ∈ B.hom.source →
      (∀ v : E,
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q →
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal →
        v = u) →
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E) ∈
          B.hom.source := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  let : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  let : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E :=
    (intrinsicExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  dsimp only
  intro B hu huniq
  exact tendsto_minimizingVec_of_unique gExt hExt huniq (B.hom.open_source.mem_nhds hu)

theorem branchEnergy_min_germ
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {pt q : M} (B : ExponentialInverseBranch (I := I) g hEnorm pt)
    (hmem :
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := I) g hEnorm pt z : E) ∈
          B.hom.source) :
    branchEnergy (I := I) g B =ᶠ[𝓝 q]
      (fun z =>
        (1 / 2 : Real) *
          (riemannianEDist I pt z).toReal ^ 2) := by
  exact Exponential.branchEnergy_min_germ g hEnorm B hmem

private theorem intrinsicExtMetric_eq_framedExpMap_pullback
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : ℝ} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (intrinsicFramedExp g hEnorm p) (Metric.ball (0 : E) R))
    (z : E) (hz : ‖z‖ ≤ 3 * R / 4) (v w : E) :
    (intrinsicExtMetric g hEnorm p hR hloc).inner z v w =
      g.inner (framedExpMap g p z)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
        (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z w) := by
  have hagree : framedExpMap g p = intrinsicFramedExp g hEnorm p := by
    funext y
    rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]
  have hz' : z ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [intrinsicExt_inner g hEnorm p hR hloc hz' v w]
  rw [hagree]
  have h := intrinsicPullMetric_inner g hEnorm p hloc
    ⟨z, intrinsicClosed_subset R hR hz'⟩ v w
  simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply,
    intrinsicFrameMetric_apply] using h

theorem intrinsicExt_radial_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    intrinsicExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z t =
      t • z := by
  exact intrinsicGeodesic_zero_eq_smul_of_pullback_extension g p (intrinsicExtMetric g hEnorm p hR hloc)
    (intrinsicExt_complete g hEnorm p hR hloc) (B := 3 * R / 4)
    (fun z _ => by
      rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
      exact mem_univ _) (intrinsicExtMetric_eq_framedExpMap_pullback g hEnorm p hR hloc)
    (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz)

theorem intrinsicExt_exp_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ < 3 * R / 4) :
    intrinsicExtLaunch (I := I) g hEnorm p hR hloc (0 : E) z 1 = z := by
  simpa only [one_smul] using
    intrinsicExt_radial_eq (I := I) g hEnorm p hR hloc hz
      (t := (1 : Real)) ⟨zero_le_one, le_rfl⟩

private noncomputable def intrinsicOriginHom {R : Real} :
    PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ where
  toPartialEquiv :=
    PartialEquiv.ofSet (Metric.ball (0 : E) (3 * R / 4))
  open_source := Metric.isOpen_ball
  open_target := Metric.isOpen_ball
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

section OriginEnergy

variable
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))

theorem intrinsicExt_inner_zero (v w : E) :
    (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) v w =
      Inner.inner Real v w := by
  have hzero :
      (0 : E) ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    linarith
  rw [intrinsicExt_inner (I := I) g hEnorm p hR hloc hzero]
  have hinner := intrinsicPullMetric_inner (I := I) g hEnorm p hloc
    ⟨(0 : E), intrinsicClosed_subset (E := E) R hR hzero⟩ v w
  have hinner' :
      (intrinsicPullMetric (I := I) g hEnorm p hloc).inner
          ⟨(0 : E), intrinsicClosed_subset (E := E) R hR hzero⟩ v w =
        innerSL Real v w := by
    with_unfolding_all
      simpa only [intrinsicFrameMetric_zero,
        tangentSpaceModelContinuousLinearEquiv_symm_apply] using hinner
  exact hinner'.trans (innerSL_apply_apply Real v w)

theorem intrinsicOrigin_energy (z : E) :
    (1 / 2 : Real) *
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner (0 : E) z z =
      (1 / 2 : Real) * ‖z‖ ^ 2 := by
  rw [intrinsicExt_inner_zero (I := I) g hEnorm p hR hloc,
    real_inner_self_eq_norm_sq]

theorem intrinsicOrigin_hess_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (Y : E) :
    hessFun (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) 0 Y Y =
      ‖Y‖ ^ 2 := by
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let hcomplete := intrinsicExt_complete (I := I) g hEnorm p hR hloc
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.toRiemannianMetric⟩
  let (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstance
  let : ∀ x : E, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    fun _ => inferInstance
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : IsRiemannianManifold 𝓘(ℝ, E) E := ⟨fun _ _ => rfl⟩
  let : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  let : CompleteSpace E := hcomplete.complete
  let hExt : IsMetricNorm gExt :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gExt x v
  let β : ExponentialInverseBranch gExt hExt (0 : E) :=
    { hom := intrinsicOriginHom (E := E) (R := R)
      hom_eq := by
        intro z hz
        have hz' : ‖z‖ < 3 * R / 4 := by
          simpa only [intrinsicOriginHom, PartialEquiv.ofSet_source,
            Metric.mem_ball, dist_zero_right] using hz
        change intrinsicGeodesic gExt hExt (0 : E) z 1 = z
        exact intrinsicExt_exp_zero g hEnorm p hR hloc hz' }
  have hzero : (0 : E) ∈ β.hom.source := by
    change (0 : E) ∈ Metric.ball (0 : E) (3 * R / 4)
    exact Metric.mem_ball_self (by positivity)
  have henergy : branchEnergy gExt β = fun z : E => (1 / 2 : ℝ) * ‖z‖ ^ 2 := by
    funext z
    exact intrinsicOrigin_energy g hEnorm p hR hloc z
  have h := Exponential.branchEnergy_hess_zero gExt hExt (0 : E) β hzero Y Y
  rw [henergy] at h
  exact h.trans (by
    rw [intrinsicExt_inner_zero g hEnorm p hR hloc, real_inner_self_eq_norm_sq])

theorem intrinsicOrigin_hess_pos
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {z Y : E} (hz : ‖z‖ < 3 * R / 4) (hzL : ‖z‖ ≤ L)
    (hz0 : z ≠ 0) (hY : Y ≠ 0) :
    0 <
      hessFun (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  apply hess_half_norm_sq_pos_of_pullback_extension g p (intrinsicExtMetric g hEnorm p hR hloc)
    (intrinsicExt_complete g hEnorm p hR hloc) (B := 3 * R / 4)
    (fun z _ => by
      rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
      exact mem_univ _) (intrinsicExtMetric_eq_framedExpMap_pullback g hEnorm p hR hloc)
    (fun z hz v w =>
      intrinsicExtMetric_riemannOp_inner_le g hEnorm p hR hloc hz (hRm z hz) v w) hz ?_ Y hY
  exact (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_pos_iff.mpr hz0).le
      ((norm_nonneg z).trans hzL)).mpr hzL) hK).trans_lt hsmall

theorem intrinsicOrigin_hess_all
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {z Y : E} (hz : ‖z‖ < 3 * R / 4) (hzL : ‖z‖ ≤ L)
    (hY : Y ≠ 0) :
    0 <
      hessFun (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc)
        (fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) z Y Y := by
  by_cases hz0 : z = 0
  · subst z
    rw [intrinsicOrigin_hess_zero (I := I) g hEnorm p hR hloc Y]
    exact sq_pos_of_pos (norm_pos_iff.mpr hY)
  · exact
      intrinsicOrigin_hess_pos (I := I) g hEnorm p hR hloc
        hK hRm hsmall hz hzL hz0 hY

theorem intrinsicOrigin_strict
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    {D : Set Real}
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ
        (interior D))
    (hD : Convex Real D)
    (hfence : ∀ t ∈ interior D, ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ interior D, ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ interior D,
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0) :
    StrictConvexOn Real D
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) := by
  apply strictConvexOn_half_norm_sq_of_pullback_extension g p (intrinsicExtMetric g hEnorm p hR hloc)
    (intrinsicExt_complete g hEnorm p hR hloc) (B := 3 * R / 4)
    (fun z _ => by
      rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
      exact mem_univ _) (intrinsicExtMetric_eq_framedExpMap_pullback g hEnorm p hR hloc)
    (fun z hz v w =>
      intrinsicExtMetric_riemannOp_inner_le g hEnorm p hR hloc hz (hRm z hz) v w) hγ hgeo hD hfence ?_ hvel
  intro t ht
  exact (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hbound t ht))).mpr
      (hbound t ht)) hK).trans_lt hsmall

theorem intrinsicExtendedGeodesic_stays_in_ball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) ≤
        L)
    (hend : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v t‖ ≤ a := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hL : 0 ≤ L := (Real.sqrt_nonneg _).trans hv
  have hbound : a + L / 2 ≤ L := by linarith
  apply norm_intrinsicGeodesic_le_of_pullback_extension g p (intrinsicExtMetric g hEnorm p hR hloc)
    (intrinsicExt_complete g hEnorm p hR hloc) (B := 3 * R / 4)
    (fun z _ => by
      rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
      exact mem_univ _) (intrinsicExtMetric_eq_framedExpMap_pullback g hEnorm p hR hloc)
    (fun z hz v w =>
      intrinsicExtMetric_riemannOp_inner_le g hEnorm p hR hloc hz (hRm z hz) v w) hbudget ?_ hx hy v hv hend
  exact (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (by positivity) hL).mpr hbound) hK).trans_lt hsmall

theorem intrinsicOrigin_no_return
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R K L T : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (hT : 0 < T)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrinsicExtMetric (I := I) g hEnorm p hR hloc) γ
        (Set.Ioo (0 : Real) (2 * T)))
    (hfence :
      ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ Set.Ioo (0 : Real) (2 * T),
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0)
    (h0T : γ 0 = γ T) (hT2 : γ T = γ (2 * T)) :
    False := by
  have hstrict :=
    intrinsicOrigin_strict (I := I) g hEnorm p hR hloc hK hRm hsmall
      hγ (D := Set.Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hgeo)
      (convex_Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hfence)
      (by simpa only [interior_Icc] using hbound)
      (by simpa only [interior_Icc] using hvel)
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  have hlt :
      (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ)
          ((1 / 2 : Real) • (0 : Real) +
            (1 / 2 : Real) • (2 * T))) <
        (1 / 2 : Real) •
            (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) 0) +
          (1 / 2 : Real) •
            (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) (2 * T)) := by
    exact hstrict.2
      ⟨le_rfl, h2T.le⟩ ⟨h2T.le, le_rfl⟩
      (ne_of_lt h2T) (by norm_num) (by norm_num) (by norm_num)
  have hmid :
      (1 / 2 : Real) • (0 : Real) +
          (1 / 2 : Real) • (2 * T) = T := by
    simp only [smul_eq_mul]
    ring
  rw [hmid] at hlt
  simp only [Function.comp_apply, smul_eq_mul] at hlt
  rw [h0T, ← hT2] at hlt
  linarith

theorem intrinsicCore_short_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4)
    {x y u v : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (huL :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x u u) <
        L)
    (hvL :
      Real.sqrt
          ((intrinsicExtMetric (I := I) g hEnorm p hR hloc).inner x v v) <
        L)
    (huEnd : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x u 1 = y)
    (hvEnd : intrinsicExtLaunch (I := I) g hEnorm p hR hloc x v 1 = y) :
    u = v := by
  exact intrinsicGeodesic_initial_velocity_eq_of_pullback_extension g p (intrinsicExtMetric g hEnorm p hR hloc)
    (intrinsicExt_complete g hEnorm p hR hloc) (B := 3 * R / 4)
    (fun z _ => by
      rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
      exact mem_univ _) (intrinsicExtMetric_eq_framedExpMap_pullback g hEnorm p hR hloc)
    (fun z hz v w =>
      intrinsicExtMetric_riemannOp_inner_le g hEnorm p hR hloc hz (hRm z hz) v w) hbudget h2aL hsmall x y u v hx hy huL hvL huEnd hvEnd

end OriginEnergy

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry

end
