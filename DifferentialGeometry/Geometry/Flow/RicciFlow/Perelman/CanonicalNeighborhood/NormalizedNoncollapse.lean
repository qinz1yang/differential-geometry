import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GrowingScaleNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
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

theorem NormalizedSequence.metric_noncollapsed_atTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) (t : ℝ)
    (ht : t ∈ (X.interval i).carrier) :
    MetricNoncollapsed ((X.term i).atTime t) kappa
      (Set.Ioc 0 (Real.sqrt (X.scale i) * sigma)) := by
  intro x r hrscale hr hcurv
  let s : (X.interval i).FlowTime := ⟨t, ht⟩
  let B : FlowMetricBall (X.term i).S s := ⟨x, r, hr⟩
  have hc : B.IsSpatiallyRmControlled := by
    intro y hy
    change r ^ 4 * Tensor0SBundle.normSq0S (I := I3)
      ((X.term i).S.base.metric t) y 4
      (metricRm04At ((X.term i).S.base.metric t) y) ≤ 1
    simpa only [PointedFlowData.atTime, SolutionOn.family_metric] using hcurv y hy
  have hn := (X.noncollapse i).2 s B hrscale.2 hc
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  change ENNReal.ofReal (kappa * r ^ 3) ≤ B.volume
  rw [ENNReal.ofReal_mul hn.1.le, ENNReal.ofReal_pow hr.le]
  simpa only [hdim] using hn.2

theorem NormalizedSequence.metric_noncollapsed_of_canonical_convergence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (P : PointedRiemannianManifold.{u, 0, 0} I3) (f : ℕ → ℕ) (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) P f)
    (conv : MetricConvergenceData F)
    (hcanonical : ∀ k,
      conv.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    (hcomplete : MetricComplete P) :
    MetricNoncollapsed P kappa Set.univ := by
  have hsigma : 0 < sigma := by
    nlinarith [Real.sqrt_nonneg (X.scale 0), (X.noncollapse 0).1]
  have hradii : Filter.Tendsto (fun i => Real.sqrt (X.scale (f i)) * sigma)
      Filter.atTop Filter.atTop :=
    ((Real.tendsto_sqrt_atTop.comp X.scale_tendsto).atTop_mul_const hsigma).comp
      hf.tendsto_atTop
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsource (i : ℕ) (p : ((X.term i).atTime 0).M) (r : ℝ) (hr : 0 < r)
      (hle : r ≤ Real.sqrt (X.scale i) * sigma)
      (hcurv : ∀ y ∈ riemannianBallOf ((X.term i).atTime 0).metric p r,
        r ^ 4 * Tensor0SBundle.normSq0S ((X.term i).atTime 0).metric y 4
          (metricRm04At ((X.term i).atTime 0).metric y) ≤ 1) :
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ ThreeSpace ≤
        riemannianVolumeMeasure I3 ((X.term i).atTime 0).M ((X.term i).atTime 0).metric
          (riemannianBallOf ((X.term i).atTime 0).metric p r) := by
    have h0 : (0 : ℝ) ∈ (X.interval i).carrier := by
      rw [X.carrier_eq i]
      exact ⟨by linarith [X.depth_pos i], le_rfl⟩
    simpa only [hdim, ENNReal.ofReal_mul' (pow_nonneg hr.le 3),
      ENNReal.ofReal_pow hr.le] using
      X.metric_noncollapsed_atTime i 0 h0 p r ⟨hr, hle⟩ hr hcurv
  intro p r _ hr hcurv
  have h := tensor_noncollapsed_of_growing_scales conv hcanonical hcomplete kappa
    (fun i => Real.sqrt (X.scale i) * sigma) hradii hsource p r hr hcurv
  simpa only [hdim, ENNReal.ofReal_mul' (pow_nonneg hr.le 3),
    ENNReal.ofReal_pow hr.le] using h

open Set in
theorem NormalizedSequence.metric_noncollapsed_scaleMetric
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    {Q : ℝ} (hQ : 0 < Q) (p : (X.term i).M) :
    MetricNoncollapsed
      { (X.term i).atTime 0 with
        basepoint := p
        metric := scaleMetric Q hQ ((X.term i).S.base.metric 0) }
      kappa (Ioc 0 (Real.sqrt Q * (Real.sqrt (X.scale i) * sigma))) := by
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
  have hnc := parabolic_spatial_noncollapse (X.term i).S 0 Q hQ hzero kappa
    (Real.sqrt (X.scale i) * sigma) (X.noncollapse i)
  intro y r hrs hr hcurv
  let B : FlowMetricBall P ⟨0, hPzero⟩ := ⟨y, r, hr⟩
  have hcontrol : B.IsSpatiallyRmControlled := by
    intro z hz
    change r ^ 4 * Tensor0SBundle.normSq0S (P.base.metric 0) z 4
      (metricRm04At (P.base.metric 0) z) ≤ 1
    change riemannianEDistOf (P.base.metric 0) y z < ENNReal.ofReal r at hz
    rw [hmetric] at hz ⊢
    exact hcurv z hz
  have hv := hnc.2 ⟨0, hPzero⟩ B hrs.2 hcontrol
  have hvol : ENNReal.ofReal (kappa * r ^ 3) ≤
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
