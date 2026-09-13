import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeLocalCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CollapsedReducedVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance reducedVolumeBoundTopology
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    TopologicalSpace F.M := F.topology
private local instance reducedVolumeBoundCharted
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    ChartedSpace H F.M := F.charted
private local instance reducedVolumeBoundSmooth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I ∞ F.M := F.smooth
private local instance reducedVolumeBoundC1
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
private local instance reducedVolumeBoundT2
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    T2Space F.M := F.t2
private local instance reducedVolumeBoundSigma
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    SigmaCompactSpace F.M := F.sigmaCompact


def AncientKappaReducedVolumeLowerBound : Prop :=
  ∀ (kappa : ℝ) (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
    IsAncientKappaSolution (I := I) kappa F → Module.finrank ℝ E = 3 →
      ¬ IsShrinkingSphericalSpaceFormFlow (I := I) F → ∀ p : F.M,
        ∀ tau0 : ℝ, 0 < tau0 →
          ENNReal.ofReal (Real.exp (-1)) ≤ intrinsicReducedVolume F.S 0 p tau0


def AncientKappaReducedVolumeUpperBound : Prop :=
  ∀ (kappa : ℝ) (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
    IsAncientKappaSolution (I := I) kappa F → Module.finrank ℝ E = 3 →
      ∀ p : F.M, ∀ {r v theta : ℝ}, 0 < r → 0 < v → 0 < theta →
        (∀ x ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p r,
          r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) →
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
            (riemannianBallOf (I := I) (F.S.base.metric 0) p r) <
          ENNReal.ofReal (v * r ^ 3) →
        intrinsicReducedVolume F.S 0 p (theta * r ^ 2) ≤
          ENNReal.ofReal ((4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) *
            Real.exp ((27 / 2 : ℝ) * theta) * v +
              collapsedReducedVolumeTail (27 / 2) theta)


def AncientKappaReducedVolumeBound : Prop :=
  AncientKappaReducedVolumeLowerBound.{u, uE, uH} (I := I) ∧
    AncientKappaReducedVolumeUpperBound.{u, uE, uH} (I := I)


omit [I.Boundaryless] in
theorem ancientKappaThree_terminal_universal_noncollapsed_of_reducedVolume
    (hlower : AncientKappaReducedVolumeLowerBound.{u, uE, uH} (I := I))
    (hupper : AncientKappaReducedVolumeUpperBound.{u, uE, uH} (I := I))
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow (I := I) F) (p : F.M)
    {r : ℝ} (hr : 0 < r)
    (hcontrol : ∀ x ∈ riemannianBallOf (I := I) (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) :
    ENNReal.ofReal (universalKappaConstant * r ^ 3) ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
        (riemannianBallOf (I := I) (F.S.base.metric 0) p r) := by
  by_contra hvolume
  have htheta := universalKappaTheta_spec.1
  have hlower' := hlower kappa F hF hdim hnotround p
    (universalKappaTheta * r ^ 2) (mul_pos htheta (sq_pos_of_pos hr))
  have hupper' := hupper kappa F hF hdim p hr
    universalKappaConstant_pos htheta hcontrol (lt_of_not_ge hvolume)
  rw [universalKappaConstant_normalization] at hupper'
  have hsmall : Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta < Real.exp (-1) := by
    have htail := universalKappaTheta_spec.2.2
    have he := Real.exp_pos (-1 : ℝ)
    linarith
  have hnonneg : 0 ≤ Real.exp (-1) / 4 +
      collapsedReducedVolumeTail (27 / 2) universalKappaTheta :=
    add_nonneg (by positivity) (collapsedReducedVolumeTail_nonneg (27 / 2) htheta)
  exact not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).mpr hsmall)
    (hlower'.trans hupper')


theorem ancientKappaThree_universal_noncollapsed_of_reducedVolume
    (hlower : AncientKappaReducedVolumeLowerBound.{u, uE, uH} (I := I))
    (hupper : AncientKappaReducedVolumeUpperBound.{u, uE, uH} (I := I))
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    PointedFlowNoncollapsedAllScales (I := I) F universalKappaConstant := by
  intro t B hRm
  let Q : ℝ := F.S.scalar t B.center
  have hQ : 0 < Q := ancientKappa_scalar_pos F hdim hF t.2 B.center
  let G := curvatureNormalizedFlow F rfl rfl t Q hQ t.2 B.center
  have hG : IsAncientKappaSolution (I := I) kappa G :=
    isAncientKappaSolution_curvatureNormalizedFlow F hF t Q hQ t.2 B.center rfl
  have hnotroundG : ¬ IsShrinkingSphericalSpaceFormFlow (I := I) G := by
    intro hround
    exact hnotround (round_of_curvatureNormalizedFlow_round F hdim hF.connected
      t Q hQ t.2 B.center hround)
  let s : (parabolicInterval ancientTimeInterval t Q t.2).FlowTime :=
    ⟨0, by
      change parabolicTime t Q 0 ≤ 0
      rw [parabolicTime_zero]
      exact t.2⟩
  let B0 : FlowMetricBall F.S (parabolicFlowTime t Q t.2 s) :=
    ⟨B.center, B.radius, B.radius_pos⟩
  have hRm0 : B0.IsSpatiallyRmControlled := by
    simpa only [FlowMetricBall.IsSpatiallyRmControlled, FlowMetricBall.set,
      FlowMetricBall.setAt, B0, parabolicFlowTime_coe, s, parabolicTime_zero] using hRm
  let Bhat := parabolicBall F.S t Q hQ t.2 s B0
  have hRmhat : Bhat.IsSpatiallyRmControlled :=
    parabolicBall_spatial_rm F.S t Q hQ t.2 s B0 hRm0
  have hcontrol : ∀ x ∈ riemannianBallOf (I := I) (G.S.base.metric 0) Bhat.center Bhat.radius,
      Bhat.radius ^ 4 * G.rmNormSq (I := I) 0 x ≤ 1 := hRmhat
  have hvolume := ancientKappaThree_terminal_universal_noncollapsed_of_reducedVolume
    hlower hupper G hG hdim hnotroundG Bhat.center Bhat.radius_pos hcontrol
  dsimp (config := { instances := true }) only [G, curvatureNormalizedFlow,
    curvatureNormalizedSolution, SolutionOn.timeRestrict] at hvolume
  have hscaled : Bhat.IsKappaNoncollapsed universalKappaConstant := by
    refine ⟨universalKappaConstant_pos, ?_⟩
    rw [hdim]
    simpa only [ENNReal.ofReal_mul universalKappaConstant_pos.le,
      ENNReal.ofReal_pow Bhat.radius_pos.le, FlowMetricBall.volume,
      volumeMeasureOn, MetricConnectionFamilyOn.metricAt, SolutionOn.family,
      FlowMetricBall.set, FlowMetricBall.setAt, riemannianBallOf, s, G,
      curvatureNormalizedFlow, curvatureNormalizedSolution,
      SolutionOn.timeRestrict] using hvolume
  have hback := (parabolicBall_kappa_iff F.S t Q hQ t.2 s B0 universalKappaConstant).mp hscaled
  simpa only [FlowMetricBall.IsKappaNoncollapsed, FlowMetricBall.volume,
    volumeMeasureOn, MetricConnectionFamilyOn.metricAt, SolutionOn.family,
    FlowMetricBall.set, FlowMetricBall.setAt,
    B0, parabolicFlowTime_coe, s, parabolicTime_zero] using hback


theorem ancientKappaThree_universal_kappa_gap_of_reducedVolume
    (hlower : AncientKappaReducedVolumeLowerBound.{u, uE, uH} (I := I))
    (hupper : AncientKappaReducedVolumeUpperBound.{u, uE, uH} (I := I))
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    IsShrinkingSphericalSpaceFormFlow (I := I) F ∨
      IsAncientKappaSolution (I := I) universalKappaConstant F := by
  by_cases hround : IsShrinkingSphericalSpaceFormFlow (I := I) F
  · exact Or.inl hround
  · exact Or.inr
      { kappa_pos := universalKappaConstant_pos
        carrier_eq := hF.carrier_eq
        regular_eq := hF.regular_eq
        connected := hF.connected
        complete := hF.complete
        nonnegativeCurvatureOperator := hF.nonnegativeCurvatureOperator
        globalScalarBound := hF.globalScalarBound
        noncollapsed := ancientKappaThree_universal_noncollapsed_of_reducedVolume
          hlower hupper F hF hdim hround
        notFlat := hF.notFlat }


theorem ancientKappaUniversalKappaGap_of_reducedVolumeBound
    (hdim : Module.finrank ℝ E = 3)
    (h : AncientKappaReducedVolumeBound.{u, uE, uH} (I := I)) :
    AncientKappaUniversalKappaGap.{u, uE, uH} (I := I) := by
  intro kappa F hF
  exact ancientKappaThree_universal_kappa_gap_of_reducedVolume
    h.1 h.2 F hF hdim

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
