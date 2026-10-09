import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FiniteAscrPositiveAvr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeRatioInvariant
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerAvr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAsymptoticVolumeRatio

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientAscrTopology : TopologicalSpace F.M := F.topology
local instance ancientAscrCharted : ChartedSpace H F.M := F.charted
local instance ancientAscrSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientAscrT2 : T2Space F.M := F.t2
local instance ancientAscrSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientAscrTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

theorem ancientKappaThree_terminal_ascr_eq_top {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (p : F.M) :
    asymptoticScalarCurvatureRatio (I := I) (F.S.base.metric 0) p = ⊤ := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  by_contra hfinite
  have hcomplete (t : ℝ) (ht : t ≤ 0) :
      RiemannianMetricComplete (I := I) (F.S.base.metric t) := ⟨hF.complete t ht⟩
  have hoperator (t : ℝ) (ht : t ≤ 0) (x : F.M) :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  have hRicBelow (t : ℝ) (ht : t ≤ 0) :
      RicciBoundedBelow (I := I) (F.S.base.metric t) 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x (hoperator t ht x) v
  have hnc : ∀ (x : F.M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r,
        r ^ 4 * normSq0S (I := I) (F.S.base.metric 0) y 4
          (metricRm04At (I := I) (F.S.base.metric 0) y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
          (riemannianBallOf (I := I) (F.S.base.metric 0) x r) := by
    intro x r hr hcontrol
    let time : ancientTimeInterval.FlowTime := ⟨0, by simp⟩
    let ball : FlowMetricBall F.S time := ⟨x, r, hr⟩
    have hball : ball.IsSpatiallyRmControlled := by
      intro y hy
      simpa only [ball, time, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
        metricRm04_apply, SolutionOn.family] using hcontrol y hy
    exact (hF.noncollapsed time ball hball).2
  let v := asymptoticVolumeRatio (I := I) (F.S.base.metric 0) p
  have hv : 0 < v :=
    (finite_ascr_positive_avr (F.S.base.metric 0) (hcomplete 0 le_rfl)
      (hoperator 0 le_rfl) kappa hF.kappa_pos hnc p hfinite).2.2.2
  have hdecay := scalar_decay_of_ascr_ne_top (F.S.base.metric 0) p hfinite
  have hK := ancientKappaThree_toKLim F hF hdim
  have htime (t : ℝ) (ht : t < 0) :
      asymptoticVolumeRatio (I := I) (F.S.base.metric t) p = v := by
    exact ancient_asymptoticVolumeRatio_eq_of_later_scalar_decay F.S F.isSolution
      (by omega) hcomplete hoperator hK.traceHarnack ht le_rfl p hdecay
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := by
    intro i
    dsimp only [tau]
    positivity
  have hescape : Tendsto tau atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  obtain ⟨q, L, phi, _, Phi, C, _, hreference, hcompleteLimit, hgeometry⟩ :=
    exists_noncompact_backward_three_limit_avr_zero F hF hdim hnoncompact tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨_, _, hzero⟩ := hgeometry
  have hsource (i : ℕ) :
      v ≤ asymptoticVolumeRatio (I := I) (M := F.M)
        ((backwardSliceSequence F tau htau q).obj i).metric (q i) := by
    change v ≤ asymptoticVolumeRatio (I := I)
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) (q i)
    rw [asymptoticVolumeRatio_scaleMetric,
      asymptoticVolumeRatio_basepoint_eq (F.S.base.metric (-tau i))
        (hcomplete (-tau i) (neg_nonpos.mpr (htau i).le))
        (hRicBelow (-tau i) (neg_nonpos.mpr (htau i).le)) (q i) p,
      htime (-tau i) (neg_lt_zero.mpr (htau i))]
  have hlower := asymptoticVolumeRatio_lower_of_pointed_metric_convergence
    C hreference hcompleteLimit v hsource
  rw [hzero L.basepoint] at hlower
  exact (not_le_of_gt hv) hlower

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
