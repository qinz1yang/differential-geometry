import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactPointedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaConstant
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedRoundRigidity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance universalGapTopology : TopologicalSpace F.M := F.topology
local instance universalGapCharted : ChartedSpace H F.M := F.charted
local instance universalGapSmooth : IsManifold I ∞ F.M := F.smooth
local instance universalGapC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance universalGapT2 : T2Space F.M := F.t2
local instance universalGapSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancientKappaThree_universal_noncollapsed
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) :
    PointedFlowNoncollapsedAllScales F universalKappaConstant := by
  intro t B hRm
  let Q : ℝ := F.S.scalar t B.center
  have hQ : 0 < Q := ancientKappa_scalar_pos F hF t.2 B.center
  let G := curvatureNormalizedFlow F rfl rfl t Q hQ t.2 B.center
  have hG : IsAncientKappaSolution kappa G :=
    isAncientKappaSolution_curvatureNormalizedFlow F hF t Q hQ t.2 B.center rfl
  have hnotroundG : ¬ IsShrinkingSphericalSpaceFormFlow G := by
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
  have hcontrol : ∀ x ∈ riemannianBallOf (G.S.base.metric 0) Bhat.center Bhat.radius,
      Bhat.radius ^ 4 * G.rmNormSq (I := I) 0 x ≤ 1 := hRmhat
  have hvolume := ancientKappaThree_terminal_universal_noncollapsed G hG hdim
    hnotroundG Bhat.center Bhat.radius_pos hcontrol
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


theorem ancientKappaThree_universal_kappa_gap
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    IsShrinkingSphericalSpaceFormFlow F ∨ IsAncientKappaSolution universalKappaConstant F := by
  by_cases hround : IsShrinkingSphericalSpaceFormFlow F
  · exact Or.inl hround
  · exact Or.inr
      { kappa_pos := universalKappaConstant_pos
        carrier_eq := hF.carrier_eq
        regular_eq := hF.regular_eq
        connected := hF.connected
        complete := hF.complete
        nonnegativeCurvatureOperator := hF.nonnegativeCurvatureOperator
        globalScalarBound := hF.globalScalarBound
        noncollapsed := ancientKappaThree_universal_noncollapsed F hF hdim hround
        notFlat := hF.notFlat }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

section
set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem IsAncientKappaSolution.universal_kappa_of_noncompact
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M) :
    IsAncientKappaSolution universalKappaConstant F := by
  rcases ancientKappaThree_universal_kappa_gap F hF (by simp [ThreeSpace]) with hround | hgap
  · obtain ⟨_T, _hT, Q, e, _hmetric⟩ := hround
    let _ : CompactSpace Q.Q := Q.proj_surjective.compactSpace Q.proj_smooth.continuous
    have hcompact : CompactSpace F.M := e.symm.surjective.compactSpace e.symm.continuous
    exact (hnoncompact.noncompact_univ hcompact.isCompact_univ).elim
  · exact hgap

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
