import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GrowingScaleNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
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

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
