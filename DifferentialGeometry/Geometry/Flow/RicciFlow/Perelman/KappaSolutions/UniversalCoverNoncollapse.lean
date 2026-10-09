import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverCurvatureNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CoverBallVolume
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [CompleteSpace E] [T2Space M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M] in
private theorem coverNoncollapseSecondCountable (I : ModelWithCorners ℝ E H) :
    SecondCountableTopology M := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact H M

private local instance coverNoncollapseMeasurable : MeasurableSpace M := borel M
private local instance coverNoncollapseBorel : BorelSpace M := ⟨rfl⟩
private local instance coverNoncollapseLiftMeasurable :
    MeasurableSpace (UniversalCover M) := borel (UniversalCover M)
private local instance coverNoncollapseLiftBorel :
    BorelSpace (UniversalCover M) := ⟨rfl⟩
private local instance coverNoncollapseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance coverNoncollapseLiftC1 :
    IsManifold I 1 (UniversalCover M) := IsManifold.of_le (n := ∞) (by decide)

theorem universalCover_tensor_noncollapsed
    (g : SmoothRiemannianMetric I M) (kappa : ℝ)
    (hnoncollapse : ∀ (p : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g p r,
        r ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (riemannianBallOf (I := I) g p r))
    (x : UniversalCover M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈
      riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r,
      r ^ 4 * normSq0S (I := I) (UniversalCover.liftedMetric (I := I) g) y 4
        (metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) y) ≤ 1) :
    let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) g)
        (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) := by
  let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
  have himage := universalCover_image_ball_liftedMetric g x r hr
  have hbase : ∀ y ∈ riemannianBallOf (I := I) g (UniversalCover.proj x) r,
      r ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1 := by
    intro y hy
    rw [← himage] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    simpa only [UniversalCover.normSq0S_metricRm04At_liftedMetric] using hcurvature y' hy'
  have hopen : IsOpen
      (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) :=
    isOpen_lt
      (continuous_riemannianEDist (I := I) (UniversalCover.liftedMetric (I := I) g) x)
      continuous_const
  have hvolume := universalCover_volume_image_le g
    (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) hopen
  rw [himage] at hvolume
  exact (hnoncollapse (UniversalCover.proj x) r hr hbase).trans hvolume

theorem universalCover_solution_slice_noncollapsed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (kappa : ℝ)
    (hnoncollapse : ∀ (time : RealTimeInterval.FlowTime D)
      (B : FlowMetricBall (I := I) (M := M) S time),
      B.IsSpatiallyKappaNoncollapsed kappa)
    (time : RealTimeInterval.FlowTime D) (x : UniversalCover M)
    (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈ riemannianBallOf (I := I)
      (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) x r,
      r ^ 4 * normSq0S (I := I)
        (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) y 4
        (metricRm04At (I := I)
          (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) y) ≤ 1) :
    let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ)))
        (riemannianBallOf (I := I)
          (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) x r) := by
  let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
  apply universalCover_tensor_noncollapsed (S.base.metric (time : ℝ))
    kappa ?_ x r hr hcurvature
  intro p rho hrho hRm
  let B : FlowMetricBall (I := I) (M := M) S time := ⟨p, rho, hrho⟩
  have hB : B.IsSpatiallyRmControlled := by
    intro y hy
    simpa only [B, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      metricRm04_apply] using hRm y hy
  have hvolume := (hnoncollapse time B hB).2
  change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : ℝ))
      (riemannianBallOf (I := I) (S.base.metric (time : ℝ)) p rho) at hvolume
  exact hvolume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
