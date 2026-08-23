import DifferentialGeometry.Geometry.Comparison.CenterOfMass
import DifferentialGeometry.Geometry.Comparison.CGTWhiteheadProducer
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

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

private theorem branchEnergy_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, Real) ∞
      (branchEnergy (I := I) g B) B.dom := by
  let gp : E →L[Real] E →L[Real] Real := g.inner p
  have hgp : ContMDiffOn I
      𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun _ : M => gp) B.dom :=
    contMDiffOn_const
  have hinv : ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom :=
    B.inv_inf
  have hinner : ContMDiffOn I 𝓘(Real, Real) ∞
      (fun z : M => g.inner p (B.inv z) (B.inv z)) B.dom := by
    simpa only [gp] using (hgp.clm_apply hinv).clm_apply hinv
  simpa only [branchEnergy] using
    (contMDiffOn_const.mul hinner)

private theorem quad_deriv2 (c t : Real) :
    (deriv^[2] (fun s : Real => (1 / 2 : Real) * s ^ 2 * c)) t = c := by
  have hfirst :
      deriv (fun s : Real => (1 / 2 : Real) * s ^ 2 * c) =
        fun s : Real => s * c := by
    funext s
    have hd :
        HasDerivAt (fun r : Real => (1 / 2 : Real) * r ^ 2 * c)
          (s * c) s := by
      convert
        (((hasDerivAt_id s).pow 2).const_mul (1 / 2 : Real)).mul_const c
          using 1
      all_goals simp only [id_eq]
      all_goals ring
    exact hd.deriv
  change
    deriv (deriv (fun s : Real => (1 / 2 : Real) * s ^ 2 * c)) t = c
  rw [hfirst]
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const c).deriv

private theorem branch_hess_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : ExpInvBranch (I := I) g hEnorm p)
    (hzero : (0 : E) ∈ B.hom.source) (Y : TangentSpace I p) :
    hessFun (I := I) g (branchEnergy (I := I) g B) p Y Y =
      g.inner p Y Y := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)
  let J : TangentSpace I p → ∀ t, TangentSpace I (γ t) := fun W =>
    intrinsicJacobi (I := I) g hEnorm p (0 : TangentSpace I p) W
  have hγ (t : Real) : γ t = p := by
    have hs :=
      intrinsicGeodesic_smul
        (I := I) g hEnorm p (0 : TangentSpace I p) t
    rw [smul_zero] at hs
    have hzero :
        intrinsicGeodesic (I := I) g hEnorm p
            (0 : TangentSpace I p) 1 = p := by
      simpa only [expMapIntrinsic_def] using
        expMapIntrinsic_zero (I := I) g hEnorm p
    exact hs.symm.trans hzero
  have hJ (W : TangentSpace I p) (t : Real) :
      (J W t : E) = t • (W : E) := by
    have hraw :=
      intrinsic_jacobi_at
        (I := I) g hEnorm p (0 : E) (W : E) t
    rw [smul_zero] at hraw
    change
      (J W t : E) =
        (mfderiv 𝓘(Real, E) I
          (fun v : E =>
            expMapIntrinsic (I := I) g hEnorm p
              (show TangentSpace I p from v))
          (0 : E)) (t • (W : E)) at hraw
    rw [mfderiv_expMapIntrinsic_at_zero
      (I := I) g hEnorm p] at hraw
    simpa only [ContinuousLinearMap.id_apply] using hraw
  have hcurve :
      γ =ᶠ[𝓝 (1 : Real)] fun _ : Real => p :=
    Filter.Eventually.of_forall hγ
  have hfield :
      ∀ᶠ t in 𝓝 (1 : Real),
        (J Y t : E) =
          ((show TangentSpace I p from t • (Y : E)) : E) :=
    Filter.Eventually.of_forall (hJ Y)
  have hcongr :=
    covDerivAlong_congr_curve
      (I := I) g (J Y)
        (fun t : Real => show TangentSpace I p from t • (Y : E))
        hcurve hfield
  have hline :
      HasDerivAt (fun t : Real => t • (Y : E)) (Y : E) 1 := by
    simpa only [one_smul] using
      ((hasDerivAt_id (1 : Real)).smul_const (Y : E))
  have hconst :=
    covDerivAlong_const
      (I := I) g p
        (fun t : Real => show TangentSpace I p from t • (Y : E))
        1 hline.differentiableAt
  have hcov :
      (covDerivAlong (I := I) g γ (J Y) 1 : E) = (Y : E) :=
    hcongr.trans (hconst.trans hline.deriv)
  have hh :=
    branchEnergy_hess
      (I := I) B (u := (0 : TangentSpace I p))
        (w₁ := Y) (w₂ := Y) hzero
  change
    hessFun (I := I) g (branchEnergy (I := I) g B)
        (γ 1) (J Y 1) (J Y 1) =
      g.inner (γ 1) (covDerivAlong (I := I) g γ (J Y) 1) (J Y 1) at hh
  rw [hγ 1, hJ Y 1, one_smul, hcov] at hh
  exact hh

theorem intrBranch_hess_pos
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
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {x : E} (u : E)
    (hfence :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖intrExtLaunch (I := I) g hEnorm p hR hloc x u t‖ <
          3 * R / 4)
    (huL :
      Real.sqrt
          ((intrExtMetric (I := I) g hEnorm p hR hloc).inner x u u) ≤
        L) :
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
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      (u : E) ∈ B.hom.source →
      ∀ {Y : E}, Y ≠ 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y := by
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
  change
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt x),
      u ∈ B.hom.source →
      ∀ {Y : E}, Y ≠ 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y
  intro B huB Y hY
  have hzeroCase :
      u = 0 →
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B)
          (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u) Y Y := by
    intro hu0
    subst u
    have hh :=
      branch_hess_zero
        (I := 𝓘(Real, E)) gExt hExt x B huB Y
    have hpos :
        0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B) x Y Y := by
      rw [hh]
      exact gExt.pos x Y hY
    have hexp :
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
            (0 : TangentSpace 𝓘(Real, E) x) =
          x :=
      expMapIntrinsic_zero (I := 𝓘(Real, E)) gExt hExt x
    exact Eq.mpr
      (congrArg
        (fun z : E =>
          0 < hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) z Y Y)
        hexp)
      hpos
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x u
  let J : E → Real → E := fun W =>
    intrinsicJacobi (I := 𝓘(Real, E)) gExt hExt x u W
  let q : E :=
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x u
  have hq :
      q = intrinsicGeodesic
        (I := 𝓘(Real, E)) gExt hExt x u 1 := by
    rfl
  have hqDom : q ∈ B.dom := by
    rw [show q = B.hom (u : E) by
      exact B.hom_eq huB]
    exact B.hom.map_source huB
  have hsmooth :
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (branchEnergy (I := 𝓘(Real, E)) gExt B) B.dom :=
    branchEnergy_inf (I := 𝓘(Real, E)) B
  obtain ⟨F, hF, hFgerm⟩ :=
    DifferentialGeometry.exists_smooth_germ
      (I := 𝓘(Real, E)) B.hom.open_target hqDom hsmooth
  let expf : E → E := fun v =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x v
  let D : E →L[Real] E :=
    mfderiv 𝓘(Real, E) 𝓘(Real, E) expf u
  let w : E :=
    mfderiv 𝓘(Real, E) 𝓘(Real, E) B.inv q Y
  have hJone (V : E) :
      J V 1 = D V := by
    have hraw :=
      intrinsic_jacobi_one
        (I := 𝓘(Real, E)) gExt hExt x (u : E) V
    simpa only [J, intrinsicJacobi, expf, D] using hraw
  have hJw : J w 1 = Y := by
    have hright :=
      exp_inv_mfderiv
        (I := 𝓘(Real, E)) B hqDom Y
    have hinv : B.inv q = (u : E) := by
      change
        B.inv
            (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x
              (show TangentSpace 𝓘(Real, E) x from u)) =
          u
      exact B.left_inv huB
    have hright' :
        mfderiv 𝓘(Real, E) 𝓘(Real, E) expf (B.inv q) w = Y := by
      simpa only [expf, w] using hright
    have hbase :
        D w =
          mfderiv 𝓘(Real, E) 𝓘(Real, E) expf (B.inv q) w := by
      dsimp only [D]
      rw [hinv]
      rfl
    exact (hJone w).trans (hbase.trans hright')
  have hwne : w ≠ 0 := by
    intro hw
    apply hY
    calc
      Y = J w 1 := hJw.symm
      _ = J 0 1 := congrArg (fun V : E => J V 1) hw
      _ = D 0 := hJone 0
      _ = 0 := map_zero _
  by_cases hu0 : (u : E) = 0
  · exact hzeroCase hu0
  · let uE : E := u
    let d : Real := gExt.inner x u u
    let α : Real := gExt.inner x u w / d
    let W : E := w - α • uE
    have hdpos : 0 < d := by
      dsimp only [d]
      exact gExt.pos x u hu0
    have hperp : gExt.inner x u W = 0 := by
      calc
        gExt.inner x u W =
            gExt.inner x u w - gExt.inner x u (α • uE) := by
          exact (gExt.inner x u).map_sub w (α • uE)
        _ = gExt.inner x u w - α * gExt.inner x u uE := by
          exact congrArg (fun z : Real => gExt.inner x u w - z)
            (by
              simpa only [smul_eq_mul] using
                (gExt.inner x u).map_smul α uE)
        _ = 0 := by
          change
            gExt.inner x u w -
                (gExt.inner x u w / d) * d =
              0
          rw [div_mul_cancel₀ _ (ne_of_gt hdpos), sub_self]
    have hwdecomp : w = W + α • uE := by
      dsimp only [W]
      abel
    have hYdecomp :
        Y = J W 1 + α • J uE 1 := by
      calc
        Y = J w 1 := hJw.symm
        _ = D w := hJone w
        _ = D (W + α • uE) := by rw [← hwdecomp]
        _ =
            D W + α • D uE := by
          calc
            _ = D W + D (α • uE) := D.map_add W (α • uE)
            _ = _ := congrArg
              (fun z : E => D W + z) (D.map_smul α uE)
        _ = J W 1 + α • J uE 1 := by
          rw [hJone W, hJone uE]
    have hγsmooth :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ :=
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x u
    have hlineCont :
        ContinuousAt (fun t : Real => t • uE) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hsrc :
        ∀ᶠ t in 𝓝 (1 : Real), t • uE ∈ B.hom.source := by
      have hnhds := B.hom.open_source.mem_nhds huB
      have hnhds' :
          B.hom.source ∈ 𝓝 ((fun t : Real => t • uE) 1) := by
        simpa only [uE, one_smul] using hnhds
      exact hlineCont hnhds'
    have henergy :
        (branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ =ᶠ[𝓝 (1 : Real)]
          fun t : Real => (1 / 2 : Real) * t ^ 2 * gExt.inner x u u := by
      filter_upwards [hsrc] with t ht
      calc
        branchEnergy (I := 𝓘(Real, E)) gExt B (γ t) =
            branchEnergy (I := 𝓘(Real, E)) gExt B
              (expMapIntrinsic
                (I := 𝓘(Real, E)) gExt hExt x (t • u)) := by
          exact congrArg
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            (intrinsicGeodesic_smul
              (I := 𝓘(Real, E)) gExt hExt x u t).symm
        _ = (1 / 2 : Real) * gExt.inner x (t • u) (t • u) :=
          branchEnergy_exp (I := 𝓘(Real, E)) B ht
        _ = (1 / 2 : Real) * t ^ 2 * gExt.inner x u u := by
          have hleftMap := (gExt.inner x).map_smul t u
          have hleft :
              gExt.inner x (t • u) (t • u) =
                t * gExt.inner x u (t • u) := by
            calc
              _ = (t • gExt.inner x u) (t • u) :=
                congrArg
                  (fun L : TangentSpace 𝓘(Real, E) x →L[Real] Real =>
                    L (t • u))
                  hleftMap
              _ = _ := by
                simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
          have hright := (gExt.inner x u).map_smul t u
          calc
            _ = (1 / 2 : Real) *
                (t * gExt.inner x u (t • u)) := by
              exact congrArg (fun r : Real => (1 / 2 : Real) * r)
                hleft
            _ = (1 / 2 : Real) *
                (t * (t * gExt.inner x u u)) := by
              exact congrArg (fun r : Real => (1 / 2 : Real) * (t * r))
                (by simpa only [smul_eq_mul] using hright)
            _ = _ := by ring
    have hd2Energy :
        (deriv^[2]
          ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) 1 =
            gExt.inner x u u := by
      exact
        (Filter.EventuallyEq.deriv_eq henergy.deriv).trans
          (quad_deriv2 (gExt.inner x u u) 1)
    have hd2Geo :=
      deriv2_geo_on_at
        (I := 𝓘(Real, E)) gExt B.hom.open_target hsmooth hγsmooth
          ((intrinsicGeodesic_isGeodesic
            (I := 𝓘(Real, E)) gExt hExt x u) 1) hqDom
    have hJu :
        J uE 1 =
          Variation.curveVelocity (I := 𝓘(Real, E)) γ 1 := by
      simpa only [γ, J, uE] using
        intrJacobi_self
          (I := 𝓘(Real, E)) gExt hExt x u
    have hdiag :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J uE 1) (J uE 1) =
          gExt.inner x u u := by
      rw [hJu]
      have hd2Geo' :
          (deriv^[2]
              ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) 1 =
            hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B)
              q
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ 1)
              (Variation.curveVelocity (I := 𝓘(Real, E)) γ 1) := by
        simpa only [γ, q, expMapIntrinsic_def] using hd2Geo
      exact hd2Geo'.symm.trans hd2Energy
    have hcross :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J W 1) (J uE 1) = 0 := by
      have hh :=
        branchEnergy_hess
          (I := 𝓘(Real, E)) B
            (u := u) (w₁ := W) (w₂ := uE) huB
      dsimp only at hh
      have hdperp :=
        intrJacobi_dperp
          (I := 𝓘(Real, E)) gExt hExt x u W one_ne_zero hperp
      have hpair :
          gExt.inner (γ 1)
              (CovariantDerivativeAlong.covDerivAlong
                (I := 𝓘(Real, E)) gExt γ (J W) 1)
              (J uE 1) = 0 := by
        rw [hJu, gExt.symm]
        simpa only [γ, J] using hdperp
      simpa only [γ, J, q, expMapIntrinsic_def] using hh.trans hpair
    have hcross' :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J uE 1) (J W 1) = 0 := by
      calc
        _ = hessFun (I := 𝓘(Real, E)) gExt F q
              (J uE 1) (J W 1) := by
          rw [hessFun_congr (I := 𝓘(Real, E)) gExt hFgerm]
        _ = hessFun (I := 𝓘(Real, E)) gExt F q
              (J W 1) (J uE 1) :=
          hessFun_symm_of_boundaryless
            (I := 𝓘(Real, E)) gExt hF q (J uE 1) (J W 1)
        _ = hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B)
              q (J W 1) (J uE 1) := by
          rw [hessFun_congr (I := 𝓘(Real, E)) gExt hFgerm]
        _ = 0 := hcross
    have hscale :
        hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (α • J uE 1) (α • J uE 1) =
          α ^ 2 *
            hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (J uE 1) := by
      have hleft :=
        LinearMap.map_smul₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
          α (J uE 1) (α • J uE 1)
      have hright :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J uE 1)).map_smul α (J uE 1)
      calc
        _ = α * hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (α • J uE 1) := by
          simpa only [smul_eq_mul] using hleft
        _ = α * (α * hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J uE 1) (J uE 1)) := by
          exact congrArg (fun r : Real => α * r)
            (by simpa only [smul_eq_mul] using hright)
        _ = _ := by ring
    change
      0 < hessFun (I := 𝓘(Real, E)) gExt
        (branchEnergy (I := 𝓘(Real, E)) gExt B) q Y Y
    have hJzero : J 0 1 = 0 := by
      exact (hJone 0).trans (D.map_zero)
    by_cases hW : W = 0
    · have hα : α ≠ 0 := by
        intro hα
        apply hY
        rw [hYdecomp, hW, hJzero, hα, zero_smul, add_zero]
      rw [hYdecomp, hW, hJzero, zero_add, hscale, hdiag]
      exact mul_pos (sq_pos_of_ne_zero hα) hdpos
    · have hpair :=
        intrExt_pair_pos
          (I := I) g hEnorm p hR hloc u W hfence huL
            hu0 hW hperp hK hRm hsmall
      have hh :=
        branchEnergy_hess
          (I := 𝓘(Real, E)) B
            (u := u) (w₁ := W) (w₂ := W) huB
      have hWW :
          0 < hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B)
            q (J W 1) (J W 1) := by
        dsimp only at hh hpair
        simpa only [γ, J, q, expMapIntrinsic_def] using hh.symm ▸ hpair
      have hcrossA :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J W 1) (α • J uE 1) = 0 := by
        have hs :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J W 1)).map_smul α (J uE 1)
        calc
          _ = α * hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (J uE 1) := by
            simpa only [smul_eq_mul] using hs
          _ = 0 := by rw [hcross, mul_zero]
      have hcrossA' :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (α • J uE 1) (J W 1) = 0 := by
        have hs :=
          LinearMap.map_smul₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
            α (J uE 1) (J W 1)
        calc
          _ = α * hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J uE 1) (J W 1) := by
            simpa only [smul_eq_mul] using hs
          _ = 0 := by rw [hcross', mul_zero]
      have hexpand :
          hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q
              (J W 1 + α • J uE 1)
              (J W 1 + α • J uE 1) =
            (hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (J W 1) +
              hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (J W 1) (α • J uE 1)) +
            (hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (α • J uE 1) (J W 1) +
              hessFun (I := 𝓘(Real, E)) gExt
                (branchEnergy (I := 𝓘(Real, E)) gExt B) q
                (α • J uE 1) (α • J uE 1)) := by
        have hleft :=
          LinearMap.map_add₂
            (hessFun (I := 𝓘(Real, E)) gExt
              (branchEnergy (I := 𝓘(Real, E)) gExt B) q)
            (J W 1) (α • J uE 1)
            (J W 1 + α • J uE 1)
        have hrightW :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (J W 1)).map_add (J W 1) (α • J uE 1)
        have hrightA :=
          (hessFun (I := 𝓘(Real, E)) gExt
            (branchEnergy (I := 𝓘(Real, E)) gExt B) q
            (α • J uE 1)).map_add
              (J W 1) (α • J uE 1)
        exact hleft.trans
          (congrArg₂ (fun a b : Real => a + b) hrightW hrightA)
      have hrad : 0 ≤ α ^ 2 * gExt.inner x u u :=
        mul_nonneg (sq_nonneg α) hdpos.le
      rw [hYdecomp, hexpand, hcrossA, hcrossA', hscale, hdiag,
        add_zero, zero_add]
      exact add_pos_of_pos_of_nonneg hWW hrad

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
      intrPullBall (E := E) R →
      intrPullBall (E := E) R →
      Real → intrPullBall (E := E) R) : Prop :=
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
      (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
      (Set.Icc (0 : Real) 1) ∧
    ∀ t ∈ Set.Icc (0 : Real) 1,
      join x y t ∈ intrCore (E := E) R a

private def intrCoreJensenMinProp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) : Prop :=
    let gPull := intrPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (intrPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrPullBall (E := E) R)
    ∃ join :
        intrPullBall (E := E) R →
        intrPullBall (E := E) R →
        Real → intrPullBall (E := E) R,
      IsCoreMinJoin (I := I) (a := a) g hEnorm p hR hloc join ∧
        ∀ pt ∈ intrCore (E := E) R a,
          CenterOfMass.StrictMidJensenOn join
            (intrCore (E := E) R a) (CenterOfMass.halfSqDist pt)

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrCore_jensen_min
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
    intrCoreJensenMinProp (I := I) g hEnorm p (a := a) hR hloc := by
  classical
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : ConnectedSpace (intrPullBall (E := E) R) :=
    Subtype.connectedSpace (isConnected_ball hR)
  letI : MetricSpace (intrPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrPullBall (E := E) R)
  dsimp only [intrCoreJensenMinProp]
  change
    ∃ join :
        intrPullBall (E := E) R →
        intrPullBall (E := E) R →
        Real → intrPullBall (E := E) R,
      IsCoreMinJoin (I := I) (a := a) g hEnorm p hR hloc join ∧
        ∀ pt ∈ intrCore (E := E) R a,
          CenterOfMass.StrictMidJensenOn join
            (intrCore (E := E) R a) (CenterOfMass.halfSqDist pt)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ :=
    exists_short_scale h4aR hsmall
  obtain ⟨join, hjoin⟩ :=
    exists_fenced_min (I := I) g hEnorm p hR h4aR hloc
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
  have haR : a < R := by linarith
  have hcoreJoin :
      ∀ x ∈ intrCore (E := E) R a,
      ∀ y ∈ intrCore (E := E) R a,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        join x y t ∈ intrCore (E := E) R a := by
    intro x hx y hy t ht
    let v : E :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx
    have haInner : a ≤ 3 * R / 4 := by linarith
    have hdist :
        riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (x : E) (y : E) ≤
          ENNReal.ofReal (2 * a) :=
      intrExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
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
        intrExtLaunch (I := I) g hEnorm p hR hloc
            (x : E) v 1 = (y : E) := by
      simpa only [gExt, hExt, v, intrExtLaunch, expMapIntrinsic_def] using
        minimizingVec_exp
          (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have hcoreExt :=
      intrExt_edge_core
        (I := I) g hEnorm p hR hloc hK hRm hsmallL h2aL hbudget
          hx hy v hvL hvEnd t ht
    have hEq := (hjoin x hx y hy).2.2.2.2.2 ht
    have hEq' :
        ((join x y t : intrPullBall (E := E) R) : E) =
          intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E) t := by
      simpa only using hEq
    change ‖((join x y t : intrPullBall (E := E) R) : E)‖ ≤ a
    rw [hEq']
    simpa only [gExt, hExt, v, intrExtJoin, minJoin, intrExtLaunch] using
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
      intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E)
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
        intrExtJoin_smooth (I := I) g hEnorm p hR hloc (x : E) (y : E)
    have hγgeo :
        IsGeodesic (I := 𝓘(Real, E)) gExt γ := by
      simpa only [γ, gExt] using
        intrExtJoin_geo (I := I) g hEnorm p hR hloc (x : E) (y : E)
    have hvel (t : Real) :
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0 := by
      simpa only [γ, uxy, gExt, hExt, intrExtJoin, minJoin] using
        intrGeo_vel_ne
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
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
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
          ((join x y t : intrPullBall (E := E) R) : E) = γ t := by
        simpa only [γ] using hEq
      have hqtNorm : ‖γ t‖ ≤ a := by
        change ‖((join x y t : intrPullBall (E := E) R) : E)‖ ≤ a at hqtJoin
        rw [hEq'] at hqtJoin
        simpa only [γ] using hqtJoin
      let qU : intrPullBall (E := E) R :=
        ⟨γ t, by
          change γ t ∈ Metric.ball (0 : E) R
          rw [Metric.mem_ball, dist_zero_right]
          exact hqtNorm.trans_lt haR⟩
      have hqU : qU ∈ intrCore (E := E) R a := by
        exact hqtNorm
      let v : E :=
        minimizingVec
          (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
      obtain ⟨B, hvB, hgerm⟩ :=
        intrCore_dist_germ
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
        intrExt_edist_le (I := I) g hEnorm p hR hloc hpt hqU haInner
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
            ‖intrExtLaunch (I := I) g hEnorm p hR hloc
              (pt : E) v s‖ < 3 * R / 4 := by
        simpa only [gExt, hExt, v, intrExtJoin, minJoin, intrExtLaunch] using
          intrExtJoin_fenced
            (I := I) g hEnorm p hR h4aR hloc hpt hqU
      let Y : E :=
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E)
      have hY : Y ≠ 0 := by
        simpa only [Y] using hvel t
      have hposRaw :=
        intrBranch_hess_pos
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
        ((join x y t : intrPullBall (E := E) R) : E) = γ t := by
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
            (M := intrPullBall (E := E) R) pt (join x y t)
        _ = (riemannianEDistOf
              (I := 𝓘(Real, E)) gPull pt (join x y t)).toReal := by
          rfl
        _ = (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E)
                ((join x y t : intrPullBall (E := E) R) : E)).toReal := by
          rw [intrCore_edist_eq
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
      intrPullBall (E := E) R →
      intrPullBall (E := E) R →
      Real → intrPullBall (E := E) R}
    (hjoin : IsCoreMinJoin (I := I) (a := a)
      g hEnorm p hR hloc join)
    {x y : intrPullBall (E := E) R}
    (hx : x ∈ intrCore (E := E) R a)
    (hy : y ∈ intrCore (E := E) R a) :
    let gPull := intrPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) (join x y) 0 1 =
      riemannianEDistOf (I := 𝓘(Real, E)) gPull x y := by
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let γU : Real → intrPullBall (E := E) R := join x y
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
        (U := intrPullBall (E := E) R)).of_le
          (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
        ).comp_contMDiffOn hγU
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
  have hpull :
      Manifold.pathELength 𝓘(Real, E) γU 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γE) 0 1 := by
    simpa only [γU, γE, intrExpOn, Function.comp_apply] using
      (intrPull_pathLen (I := I) g hEnorm p hloc hγU).symm
  have hext :
      Manifold.pathELength 𝓘(Real, E) γE 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γE) 0 1 := by
    simpa only [gExt] using
      (intrExt_pathLen (I := I) g hEnorm p hR hloc hγE
        (fun t ht => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hspec.2.2.2.2.1 t ht).le))
  have hjoinLen :
      Manifold.pathELength 𝓘(Real, E)
          (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
          0 1 =
        riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (x : E) (y : E) := by
    calc
      Manifold.pathELength 𝓘(Real, E)
            (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
            0 1 =
          ENNReal.ofReal
            ((riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal) := by
        simpa only [intrExtJoin, gExt, riemannianEDistOf] using
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
          (intrExtJoin (I := I) g hEnorm p hR hloc
            (x : E) (y : E)) 0 1 :=
      Manifold.pathELength_congr hspec.2.2.2.2.2.1
    _ = riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (x : E) (y : E) := hjoinLen
    _ = riemannianEDistOf
          (I := 𝓘(Real, E)) gPull x y := by
      symm
      exact intrCore_edist_eq
        (I := I) g hEnorm p hR h4aR hloc hx hy

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrCore_jensen
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
    let gPull := intrPullMetric (I := I) g hEnorm p hloc
    letI : RiemannianBundle
        (fun z : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (intrPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrPullBall (E := E) R)
    ∃ join :
        intrPullBall (E := E) R →
        intrPullBall (E := E) R →
        Real → intrPullBall (E := E) R,
      ∀ pt ∈ intrCore (E := E) R a,
        CenterOfMass.StrictMidJensenOn join
          (intrCore (E := E) R a) (CenterOfMass.halfSqDist pt) := by
  obtain ⟨join, _, hjensen⟩ :=
    intrCore_jensen_min (I := I) g hEnorm p hR h4aR hloc
      hK hsmall hRm
  exact ⟨join, hjensen⟩

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
