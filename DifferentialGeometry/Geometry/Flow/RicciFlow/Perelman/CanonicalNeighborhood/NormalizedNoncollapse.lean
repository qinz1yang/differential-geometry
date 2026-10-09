import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceNoncollapse
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem NormalizedSequence.metric_noncollapsed_of_canonical_convergence
    {eps kappa sigma kappa' : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (hnc : X.TerminalSliceNoncollapsed kappa')
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) P f)
    (conv : MetricConvergenceData F)
    (hcanonical : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (hcomplete : MetricComplete P) :
    MetricNoncollapsed P kappa' (Set.Ioc 0 1) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hev := hf.tendsto_atTop.eventually hnc.eventually_metricNoncollapsed
  intro p r hr hrpos hcurv
  have h :=
    KappaSolutions.tensor_noncollapsed_below_scale_of_eventually_pointed_canonical_convergence
      (Φ := F) conv hcanonical hcomplete kappa' 1 (fun s hs hs1 => by
        filter_upwards [hev] with i hi q hcurv'
        have hq := hi q s ⟨hs, hs1⟩ hs hcurv'
        rw [ENNReal.ofReal_mul' (pow_nonneg hs.le 3), ENNReal.ofReal_pow hs.le] at hq
        simp only [hdim]
        with_unfolding_all exact hq) p r hrpos hr.2 hcurv
  simpa only [hdim, ENNReal.ofReal_mul' (pow_nonneg hrpos.le 3),
    ENNReal.ofReal_pow hrpos.le] using h

open Set in
theorem NormalizedSequence.TerminalSliceNoncollapsed.eventually_metricNoncollapsed_scaleMetric
    {eps kappa sigma kappa' : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (hnc : X.TerminalSliceNoncollapsed kappa') :
    ∀ᶠ i in Filter.atTop, ∀ (Q : ℝ) (hQ : 0 < Q) (p : (X.term i).M),
      MetricNoncollapsed
        { (X.term i).atTime 0 with
          basepoint := p
          metric := scaleMetric Q hQ ((X.term i).S.base.metric 0) }
        kappa' (Ioc 0 (Real.sqrt Q)) := by
  filter_upwards [hnc.2] with i hi
  intro Q hQ p
  let _ : IsManifold I3 1 (X.term i).M := IsManifold.of_le (n := ∞) (by decide)
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  let P := parabolicSolution (X.term i).S 0 Q hQ hzero
  have hPzero : (0 : ℝ) ∈ (parabolicInterval (X.interval i) 0 Q hzero).carrier := by
    change parabolicTime 0 Q 0 ∈ (X.interval i).carrier
    rwa [parabolicTime_zero]
  have hmetric : P.base.metric 0 = scaleMetric Q hQ ((X.term i).S.base.metric 0) := by
    change scaleMetric Q hQ ((X.term i).S.base.metric (parabolicTime 0 Q 0)) = _
    rw [parabolicTime_zero]
  intro y r hrs hr hcurv
  let B : FlowMetricBall P ⟨0, hPzero⟩ := ⟨y, r, hr⟩
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    change r ^ 4 * Tensor0SBundle.normSq0S (P.base.metric 0) z 4
      (metricRm04At (P.base.metric 0) z) ≤ 1
    change riemannianEDistOf (P.base.metric 0) y z < ENNReal.ofReal r at hz
    rw [hmetric] at hz ⊢
    exact hcurv z hz
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hback : (backBall (X.term i).S 0 Q hQ hzero ⟨0, hPzero⟩ B).radius ≤ 1 := by
    change r / Real.sqrt Q ≤ 1
    rw [div_le_one hsqrt]
    exact hrs.2
  have htime : ((parabolicFlowTime 0 Q hzero ⟨0, hPzero⟩ : (X.interval i).FlowTime) : ℝ) = 0 := by
    rw [parabolicFlowTime_coe]
    exact parabolicTime_zero 0 Q
  have hk₀ := hi _ htime _ hback
    (backBall_spatial_rm (X.term i).S 0 Q hQ hzero ⟨0, hPzero⟩ B hcontrol)
  have hv := parabolicBall_kappa (X.term i).S 0 Q hQ hzero ⟨0, hPzero⟩ _ kappa' hk₀
  rw [parabolicBall_back] at hv
  have hvol : ENNReal.ofReal (kappa' * r ^ 3) ≤
      riemannianVolumeMeasure I3 (X.term i).M (P.base.metric 0)
        (riemannianBallOf (P.base.metric 0) y r) := by
    rw [ENNReal.ofReal_mul hv.1.le, ENNReal.ofReal_pow hr.le]
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    simpa only [hdim, B, FlowMetricBall.volume, FlowMetricBall.set,
      FlowMetricBall.setAt, volumeMeasureOn_eq_metric, SolutionOn.family_metric,
      riemannianBallOf] using hv.2
  rw [hmetric] at hvol
  exact hvol

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
