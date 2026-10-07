import DifferentialGeometry.Analysis.Integration.Measure.BallContinuity
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.ContinuityHGI
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianBallOf_volume_continuity_data
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun r : ℝ => riemannianVolumeMeasure I M g (riemannianBallOf g p r)) R ∧
      riemannianVolumeMeasure I M g (riemannianBallOf g p R) ≠ ⊤ := by
  let _ : ConnectedSpace M := ⟨⟨p⟩⟩
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    let _ : CompactSpace M := inferInstance
    let _ : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
    have hball (r : ℝ) (hr : 0 < r) : riemannianBallOf g p r = univ := by
      apply eq_univ_of_forall
      intro q
      change riemannianEDistOf g p q < ENNReal.ofReal r
      rw [show q = p from Subsingleton.elim _ _, riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr
    refine ⟨?_, measure_ne_top _ _⟩
    have heq : (fun r : ℝ =>
        riemannianVolumeMeasure I M g (riemannianBallOf g p r)) =ᶠ[𝓝 R]
          fun _ => riemannianVolumeMeasure I M g univ := by
      filter_upwards [Ioi_mem_nhds hR] with r hr
      rw [hball r hr]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (n := ∞) (by decide)
    let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let _ : T3Space M := inferInstance
    let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let _ : CompleteSpace M := hcomplete.complete
    have hEnorm : Geometry.Riemannian.IsMetricNorm (I := I) g := fun x v =>
      Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    exact ⟨Geometry.Riemannian.VolumeComparison.segmentBall_vol_cont_HGI g hEnorm p hR,
      (Geometry.Riemannian.VolumeComparison.segmentBall_vol_fin g hEnorm p (R := R)).ne⟩

theorem continuousAt_riemannianBallOf_volume
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun z : M × ℝ =>
      riemannianVolumeMeasure I M g (riemannianBallOf g z.1 z.2)) (p, R) := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  have hball (x : M) (r : ℝ) : Metric.ball x r = riemannianBallOf g x r := by
    ext y
    change dist y x < r ↔ edist x y < ENNReal.ofReal r
    rw [edist_lt_ofReal, dist_comm]
  have hrad : ContinuousAt (fun r : ℝ =>
      riemannianVolumeMeasure I M g (Metric.ball p r)) R := by
    simpa only [hball] using (riemannianBallOf_volume_continuity_data g hcomplete p hR).1
  simpa only [hball] using
    MeasureTheory.continuousAt_measure_ball_of_continuousAt_radius
      (riemannianVolumeMeasure I M g) hrad

theorem continuousAt_riemannianBallOf_realVolume
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun z : M × ℝ =>
      (riemannianVolumeMeasure I M g (riemannianBallOf g z.1 z.2)).toReal) (p, R) := by
  let f : M × ℝ → ℝ≥0∞ := fun z =>
    riemannianVolumeMeasure I M g (riemannianBallOf g z.1 z.2)
  change ContinuousAt (fun z => (f z).toReal) (p, R)
  have hf : ContinuousAt f (p, R) :=
    continuousAt_riemannianBallOf_volume g hcomplete p hR
  have hfinite : f (p, R) ≠ ⊤ :=
    (riemannianBallOf_volume_continuity_data g hcomplete p hR).2
  exact (ENNReal.tendsto_toReal hfinite).comp hf


end DifferentialGeometry.Integral.Measure
