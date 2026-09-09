import DifferentialGeometry.Geometry.CenterOfMass.Basic
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Core.MinimizingVector
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

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

private theorem branchEnergy_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, Real) ∞
      (branchEnergy (I := I) g B) B.dom := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hgp : ContMDiffOn I
      𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun _ : M => gp) B.dom :=
    contMDiffOn_const
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom :=
    B.inv_contMDiffOn
  have hinner : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z : M => g.inner p (B.inv z) (B.inv z)) B.dom := by
    with_unfolding_all exact (hgp.clm_apply hinv).clm_apply hinv
  with_unfolding_all exact contMDiffOn_const.mul hinner

def IsCoreMinJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (join :
      intrinsicPullBall (E := E) R →
      intrinsicPullBall (E := E) R →
      Real → intrinsicPullBall (E := E) R) : Prop :=
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
      (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
      (Set.Icc (0 : Real) 1) ∧
    ∀ t ∈ Set.Icc (0 : Real) 1,
      join x y t ∈ intrinsicCore (E := E) R a

private def intrinsicCoreJensenMinProp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) : Prop :=
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ∃ join :
        intrinsicPullBall (E := E) R →
        intrinsicPullBall (E := E) R →
        Real → intrinsicPullBall (E := E) R,
      IsCoreMinJoin (I := I) (a := a) g hEnorm p hR hloc join ∧
        ∀ pt ∈ intrinsicCore (E := E) R a,
          CenterOfMass.StrictMidJensenOn join
            (intrinsicCore (E := E) R a) (CenterOfMass.halfSqDist pt)

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCore_jensen_min
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
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K) :
    intrinsicCoreJensenMinProp (I := I) g hEnorm p (a := a) hR hloc := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  dsimp only [intrinsicCoreJensenMinProp]
  change
    ∃ join :
        intrinsicPullBall (E := E) R →
        intrinsicPullBall (E := E) R →
        Real → intrinsicPullBall (E := E) R,
      IsCoreMinJoin (I := I) (a := a) g hEnorm p hR hloc join ∧
        ∀ pt ∈ intrinsicCore (E := E) R a,
          CenterOfMass.StrictMidJensenOn join
            (intrinsicCore (E := E) R a) (CenterOfMass.halfSqDist pt)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ :=
    exists_short_scale h4aR hsmall
  obtain ⟨join, hjoin⟩ :=
    exists_fenced_min (I := I) g hEnorm p hR h4aR hloc
  let gExt := intrinsicExtMetric (I := I) g hEnorm p hR hloc
  let : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  let : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
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
  have haR : a < R := by linarith
  have hcoreJoin :
      ∀ x ∈ intrinsicCore (E := E) R a,
      ∀ y ∈ intrinsicCore (E := E) R a,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        join x y t ∈ intrinsicCore (E := E) R a := by
    intro x hx y hy t ht
    let v : E :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx
    have haInner : a ≤ 3 * R / 4 := by linarith
    have hdist :
        riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (x : E) (y : E) ≤
          ENNReal.ofReal (2 * a) :=
      intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
    have hdistReal :
        (riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal ≤
            2 * a :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
    have hvL : Real.sqrt (gExt.inner (x : E) v v) ≤ L := by
      rw [show
        Real.sqrt (gExt.inner (x : E) v v) =
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal by
        simpa only [v, riemannianEDistOf] using
          minimizingVec_len
            (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)]
      exact hdistReal.trans h2aL.le
    have hvEnd :
        intrinsicExtLaunch (I := I) g hEnorm p hR hloc
            (x : E) v 1 = (y : E) := by
      with_unfolding_all
        change expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt
          (x : E) v = (y : E)
        exact minimizingVec_exp
          (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have hcoreExt :=
      intrinsicExtendedGeodesic_stays_in_ball
        (I := I) g hEnorm p hR hloc hK hRm hsmallL h2aL hbudget
          hx hy v hvL hvEnd t ht
    have hEq := (hjoin x hx y hy).2.2.2.2.2 ht
    have hEq' :
        ((join x y t : intrinsicPullBall (E := E) R) : E) =
          intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E) t := by
      simpa only using hEq
    change ‖((join x y t : intrinsicPullBall (E := E) R) : E)‖ ≤ a
    rw [hEq']
    simpa only [gExt, hExt, v, intrinsicExtJoin, minJoin, intrinsicExtLaunch] using
      hcoreExt
  refine ⟨join, ?_, ?_⟩
  · intro x hx y hy
    refine ⟨(hjoin x hx y hy).1, (hjoin x hx y hy).2.1,
      (hjoin x hx y hy).2.2.1, (hjoin x hx y hy).2.2.2.1,
      (hjoin x hx y hy).2.2.2.2.1,
      (hjoin x hx y hy).2.2.2.2.2, ?_⟩
    exact hcoreJoin x hx y hy
  intro pt hpt
  apply CenterOfMass.jensen_of_strict
  · intro x hx y hy hxy
    exact hcoreJoin x hx y hy (1 / 2 : Real) (by constructor <;> norm_num)
  · intro x hx y hy
    exact (hjoin x hx y hy).2.2.1
  · intro x hx y hy
    exact (hjoin x hx y hy).2.2.2.1
  · intro x hx y hy hxy
    let γ : Real → E :=
      intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E)
    let uxy : E :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have huxy : uxy ≠ 0 := by
      intro hu0
      apply hxy
      apply Subtype.ext
      have hzero :=
        expMapIntrinsic_zero
          (I := 𝓘(Real, E)) gExt hExt (x : E)
      have hend :=
        minimizingVec_exp
          (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
      calc
        (x : E) =
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (x : E) 0 :=
          hzero.symm
        _ =
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (x : E) uxy := by
          rw [hu0]
          rfl
        _ = (y : E) := by simpa only [uxy] using hend
    have hγsmooth :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
      simpa only [γ] using
        intrinsicExtJoin_smooth (I := I) g hEnorm p hR hloc (x : E) (y : E)
    have hγgeo :
        IsGeodesic (I := 𝓘(Real, E)) gExt γ := by
      simpa only [γ, gExt] using
        intrinsicExtJoin_geo (I := I) g hEnorm p hR hloc (x : E) (y : E)
    have hvel (t : Real) :
        mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) ≠ 0 := by
      with_unfolding_all
        exact intrinsicGeo_velocity_ne
          (I := 𝓘(Real, E)) gExt hExt (x : E) uxy huxy t
    let f : E → Real := fun z =>
      (1 / 2 : Real) *
        (riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (pt : E) z).toReal ^ 2
    have hfinite :
        {z : E |
          riemannianEDist 𝓘(Real, E) (pt : E) z ≠ (⊤ : ENNReal)} =
          Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact riemannianEDist_ne_top (I := 𝓘(Real, E)) (pt : E) z
    have hdistCont :
        Continuous fun z : E =>
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) z).toReal := by
      have hOn :=
        continuousOn_riemannianEDist_toReal_on_finite gExt (pt : E)
      rw [hfinite] at hOn
      simpa only [riemannianEDistOf] using continuousOn_univ.mp hOn
    have hfcont : Continuous f := by
      exact continuous_const.mul (hdistCont.pow 2)
    have hstrictExt :
        StrictConvexOn Real (Set.Icc (0 : Real) 1) (f ∘ γ) := by
      apply strictConvexOn_of_deriv2_pos
        (convex_Icc (0 : Real) 1)
        (hfcont.comp hγsmooth.continuous).continuousOn
      intro t ht
      rw [interior_Icc] at ht
      have htIcc : t ∈ Set.Icc (0 : Real) 1 := ⟨ht.1.le, ht.2.le⟩
      have hqtJoin :=
        hcoreJoin x hx y hy t htIcc
      have hEq := (hjoin x hx y hy).2.2.2.2.2 htIcc
      have hEq' :
          ((join x y t : intrinsicPullBall (E := E) R) : E) = γ t := by
        simpa only [γ] using hEq
      have hqtNorm : ‖γ t‖ ≤ a := by
        change ‖((join x y t : intrinsicPullBall (E := E) R) : E)‖ ≤ a at hqtJoin
        rw [hEq'] at hqtJoin
        simpa only [γ] using hqtJoin
      let qU : intrinsicPullBall (E := E) R :=
        ⟨γ t, by
          change γ t ∈ Metric.ball (0 : E) R
          rw [Metric.mem_ball, dist_zero_right]
          exact hqtNorm.trans_lt haR⟩
      have hqU : qU ∈ intrinsicCore (E := E) R a := by
        exact hqtNorm
      let v : E :=
        minimizingVec
          (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
      obtain ⟨B, hvB, hgerm⟩ :=
        intrinsicCore_dist_germ
          (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm hpt hqU
      have hgermF :
          branchEnergy (I := 𝓘(Real, E)) gExt B =ᶠ[𝓝 (γ t)] f := by
        simpa only [gExt, hExt, v, qU, f] using hgerm
      have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt
      have haInner : a ≤ 3 * R / 4 := by linarith
      have hdist :
          riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) (qU : E) ≤
            ENNReal.ofReal (2 * a) :=
        intrinsicExt_edist_le (I := I) g hEnorm p hR hloc hpt hqU haInner
      have hdistReal :
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (qU : E)).toReal ≤
              2 * a :=
        ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
      have hvL : Real.sqrt (gExt.inner (pt : E) v v) ≤ L := by
        rw [show
          Real.sqrt (gExt.inner (pt : E) v v) =
            (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) (qU : E)).toReal by
          simpa only [v, riemannianEDistOf] using
            minimizingVec_len
              (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)]
        exact hdistReal.trans h2aL.le
      have hvEnd :
          expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (pt : E) v =
            (qU : E) := by
        simpa only [v] using
          minimizingVec_exp
            (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
      have hvFence :
          ∀ s ∈ Set.Icc (0 : Real) 1,
            ‖intrinsicExtLaunch (I := I) g hEnorm p hR hloc
              (pt : E) v s‖ < 3 * R / 4 := by
        simpa only [gExt, hExt, v, intrinsicExtJoin, minJoin, intrinsicExtLaunch] using
          intrinsicExtJoin_fenced
            (I := I) g hEnorm p hR h4aR hloc hpt hqU
      let Y : E :=
        tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) (γ t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real))
      have hY : Y ≠ 0 := by
        intro hYzero
        apply hvel t
        apply (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) (γ t)).injective
        simpa only [map_zero, Y] using hYzero
      have hposRaw :=
        intrinsicBranch_hess_pos
          (I := I) g hEnorm p hR hloc hK hRm hsmallL
            (x := (pt : E)) v hvFence hvL B hvB (Y := Y) hY
      have hvEndγ :
          expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (pt : E) v =
            γ t := by
        simpa only [qU] using hvEnd
      rw [hvEndγ] at hposRaw
      have hpos :
          0 < hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            (γ t) Y Y := by
        simpa only [gExt, hExt, Y] using hposRaw
      have hBmap : B.hom (v : E) = (qU : E) :=
        (B.hom_eq hvB).symm.trans hvEnd
      have hqDom : (γ t) ∈ B.dom := by
        change (qU : E) ∈ B.dom
        rw [← hBmap]
        exact B.hom.map_source hvB
      have hbranch :
          ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
            (branchEnergy (I := 𝓘(Real, E)) gExt B) B.dom :=
        branchEnergy_inf (I := 𝓘(Real, E)) B
      have hd2Branch :=
        deriv2_geo_on_at
          (I := 𝓘(Real, E)) gExt B.hom.open_target hbranch hγsmooth
            (hγgeo t) hqDom
      have hcomp :
          (branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ =ᶠ[𝓝 t]
            f ∘ γ :=
        hγsmooth.continuous.continuousAt.eventually hgermF
      have hd2Eq :
          (deriv^[2] (f ∘ γ)) t =
            (deriv^[2]
              ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) t :=
        Filter.EventuallyEq.deriv_eq hcomp.symm.deriv
      rw [hd2Eq, hd2Branch]
      exact hpos
    apply hstrictExt.congr
    intro t ht
    have hqt := hcoreJoin x hx y hy t ht
    have hEq := (hjoin x hx y hy).2.2.2.2.2 ht
    have hEq' :
        ((join x y t : intrinsicPullBall (E := E) R) : E) = γ t := by
      simpa only [γ] using hEq
    have hdistPull :
        dist (join x y t) pt =
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (γ t)).toReal := by
      calc
        dist (join x y t) pt = dist pt (join x y t) := dist_comm _ _
        _ = (riemannianEDist 𝓘(Real, E) pt (join x y t)).toReal :=
          HopfRinow.riemMetric_dist_eq
            (I := 𝓘(Real, E))
            (M := intrinsicPullBall (E := E) R) pt (join x y t)
        _ = (riemannianEDistOf
              (I := 𝓘(Real, E)) gPull pt (join x y t)).toReal := by
          rfl
        _ = (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E)
                ((join x y t : intrinsicPullBall (E := E) R) : E)).toReal := by
          rw [intrinsicCore_edist_eq
            (I := I) g hEnorm p hR h4aR hloc hpt hqt]
        _ = (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) (γ t)).toReal := by
          rw [hEq']
    simp only [Function.comp_apply, f, CenterOfMass.halfSqDist]
    rw [hdistPull]

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem coreJoin_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {join :
      intrinsicPullBall (E := E) R →
      intrinsicPullBall (E := E) R →
      Real → intrinsicPullBall (E := E) R}
    (hjoin : IsCoreMinJoin (I := I) (a := a)
      g hEnorm p hR hloc join)
    {x y : intrinsicPullBall (E := E) R}
    (hx : x ∈ intrinsicCore (E := E) R a)
    (hy : y ∈ intrinsicCore (E := E) R a) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) (join x y) 0 1 =
      riemannianEDistOf (I := 𝓘(Real, E)) gPull x y := by
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let γU : Real → intrinsicPullBall (E := E) R := join x y
  let γE : Real → E := fun t => (γU t : E)
  have hspec := hjoin x hx y hy
  have hγU :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γU
        (Set.Icc (0 : Real) 1) :=
    (hspec.1.of_le (by decide)).contMDiffOn
  have hγE :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γE
        (Set.Icc (0 : Real) 1) := by
    exact
      ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
        (I := 𝓘(Real, E))
        (U := intrinsicPullBall (E := E) R)).of_le
          (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
        ).comp_contMDiffOn hγU
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
  have hpull :
      Manifold.pathELength 𝓘(Real, E) γU 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γE) 0 1 := by
    have hraw := (intrinsicPull_pathLen (I := I) g hEnorm p hloc hγU).symm
    have hcurve :
        (intrinsicExpOn (I := I) g hEnorm p R ∘ γU) =
          (intrinsicFramedExp (I := I) g hEnorm p) ∘ γE := by
      funext t
      with_unfolding_all rfl
    exact hraw.trans
      (congrArg (fun c : Real → M => Manifold.pathELength I c 0 1) hcurve)
  have hext :
      Manifold.pathELength 𝓘(Real, E) γE 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γE) 0 1 := by
    simpa only [gExt] using
      (intrinsicExt_pathLen (I := I) g hEnorm p hR hloc hγE
        (fun t ht => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hspec.2.2.2.2.1 t ht).le))
  have hjoinLen :
      Manifold.pathELength 𝓘(Real, E)
          (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
          0 1 =
        riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (x : E) (y : E) := by
    calc
      Manifold.pathELength 𝓘(Real, E)
            (intrinsicExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
            0 1 =
          ENNReal.ofReal
            ((riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal) := by
        simpa only [intrinsicExtJoin, gExt, riemannianEDistOf] using
          (minJoin_pathLen
            (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E))
      _ = riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (x : E) (y : E) := by
        apply ENNReal.ofReal_toReal
        exact riemannianEDist_ne_top (I := 𝓘(Real, E)) (x : E) (y : E)
  calc
    Manifold.pathELength 𝓘(Real, E) (join x y) 0 1 =
        Manifold.pathELength 𝓘(Real, E) γE 0 1 := by
      change Manifold.pathELength 𝓘(Real, E) γU 0 1 = _
      exact hpull.trans hext.symm
    _ = Manifold.pathELength 𝓘(Real, E)
          (intrinsicExtJoin (I := I) g hEnorm p hR hloc
            (x : E) (y : E)) 0 1 :=
      Manifold.pathELength_congr hspec.2.2.2.2.2.1
    _ = riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (x : E) (y : E) := hjoinLen
    _ = riemannianEDistOf
          (I := 𝓘(Real, E)) gPull x y := by
      symm
      exact intrinsicCore_edist_eq
        (I := I) g hEnorm p hR h4aR hloc hx hy

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCore_jensen
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
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ∃ join :
        intrinsicPullBall (E := E) R →
        intrinsicPullBall (E := E) R →
        Real → intrinsicPullBall (E := E) R,
      ∀ pt ∈ intrinsicCore (E := E) R a,
        CenterOfMass.StrictMidJensenOn join
          (intrinsicCore (E := E) R a) (CenterOfMass.halfSqDist pt) := by
  obtain ⟨join, _, hjensen⟩ :=
    intrinsicCore_jensen_min (I := I) g hEnorm p hR h4aR hloc
      hK hsmall hRm
  exact ⟨join, hjensen⟩

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry

end
