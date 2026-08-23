import DifferentialGeometry.Geometry.Comparison.CGTWhiteheadBigon

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Integral.Connection

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

theorem intrCore_minimizingVec_regular_unique
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
    {pt q : intrPullBall (E := E) R}
    (hpt : pt ∈ intrCore (E := E) R a)
    (hq : q ∈ intrCore (E := E) R a) :
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
    let u :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    (¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E)) ∧
      ∀ v : E,
        expMapIntrinsic
            (I := 𝓘(Real, E)) gExt hExt (pt : E) v = (q : E) →
        Real.sqrt (gExt.inner (pt : E) v v) =
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal →
        v = u := by
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
  let u :=
    minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  dsimp only
  constructor
  · simpa only [gExt, hExt, u] using
      intrCore_min_regular
        (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm hpt hq
  · intro v hvEnd hvMin
    obtain ⟨L, h2aL, hbudget, hsmallL⟩ :=
      exists_short_scale h4aR hsmall
    have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt
    have haInner : a ≤ 3 * R / 4 := by linarith
    have hdist :
        riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (q : E) ≤
          ENNReal.ofReal (2 * a) :=
      intrExt_edist_le (I := I) g hEnorm p hR hloc hpt hq haInner
    have hdistReal :
        (riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal ≤
            2 * a :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
    have huMin :
        Real.sqrt (gExt.inner (pt : E) u u) =
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal := by
      simpa only [riemannianEDistOf] using
        minimizingVec_len
          (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    have huL : Real.sqrt (gExt.inner (pt : E) u u) < L := by
      rw [huMin]
      exact hdistReal.trans_lt h2aL
    have hvL : Real.sqrt (gExt.inner (pt : E) v v) < L := by
      rw [hvMin]
      exact hdistReal.trans_lt h2aL
    have huEnd :
        intrExtLaunch (I := I) g hEnorm p hR hloc
            (pt : E) u 1 = (q : E) := by
      simpa only [gExt, hExt, intrExtLaunch, expMapIntrinsic_def] using
        minimizingVec_exp
          (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    have hvEnd' :
        intrExtLaunch (I := I) g hEnorm p hR hloc
            (pt : E) v 1 = (q : E) := by
      simpa only [gExt, hExt, intrExtLaunch, expMapIntrinsic_def] using hvEnd
    exact (intrCore_short_inj
      (I := I) g hEnorm p hR hloc hK hRm hsmallL h2aL hbudget
        (x := (pt : E)) (y := (q : E)) (u := u) (v := v)
        hpt hq huL hvL huEnd hvEnd').symm

private def intrCoreDistGermProp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {pt q : intrPullBall (E := E) R} : Prop :=
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
    let u :=
      minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ∃ B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt (pt : E),
      (u : E) ∈ B.hom.source ∧
      branchEnergy (I := 𝓘(Real, E)) gExt B =ᶠ[𝓝 (q : E)]
        (fun z =>
          (1 / 2 : Real) *
            (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) z).toReal ^ 2)

theorem intrCore_dist_germ
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
    {pt q : intrPullBall (E := E) R}
    (hpt : pt ∈ intrCore (E := E) R a)
    (hq : q ∈ intrCore (E := E) R a) :
    intrCoreDistGermProp (I := I) g hEnorm p hR hloc (pt := pt) (q := q) := by
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
  let u :=
    minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  dsimp only [intrCoreDistGermProp]
  have hru :=
    intrCore_minimizingVec_regular_unique
      (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm hpt hq
  change
    (¬ IsConjVec
      (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E)) ∧
      ∀ v : E,
        expMapIntrinsic
            (I := 𝓘(Real, E)) gExt hExt (pt : E) v = (q : E) →
        Real.sqrt (gExt.inner (pt : E) v v) =
          (riemannianEDistOf
            (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal →
        v = u at hru
  obtain ⟨B, huB⟩ :=
    branch_of_not_conj
      (I := 𝓘(Real, E)) gExt hExt hru.1
  have huniq :
      ∀ v : E,
        expMapIntrinsic
            (I := 𝓘(Real, E)) gExt hExt (pt : E) v = (q : E) →
        Real.sqrt (gExt.inner (pt : E) v v) =
          (riemannianEDist 𝓘(Real, E) (pt : E) (q : E)).toReal →
        v = u := by
    intro v hv hlen
    apply hru.2 v hv
    simpa only [riemannianEDistOf] using hlen
  have hmem :=
    intrExt_minVec_mem
      (I := I) g hEnorm p hR hloc
        (pt := (pt : E)) (q := (q : E)) (u := u) B huB huniq
  refine ⟨B, huB, ?_⟩
  have hgerm :=
    branchEnergy_min_germ
      (I := 𝓘(Real, E)) gExt hExt B hmem
  simpa only [riemannianEDistOf] using hgerm

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
