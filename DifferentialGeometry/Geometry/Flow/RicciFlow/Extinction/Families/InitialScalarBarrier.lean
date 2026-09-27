import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry.Curvature

def InitialScalarBarrier {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) (c : ℝ) : Prop :=
  ∀ x : M, -3 / (2 * c) ≤ metricScalarAt g x

theorem initialScalarBarrier_of_nonnegScalarAt {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {g : SmoothRiemannianMetric ThreeModel M} {c : ℝ} (hc : 0 < c)
    (h : ∀ x : M, 0 ≤ metricScalarAt g x) : InitialScalarBarrier g c :=
  fun x =>
    (div_neg_of_neg_of_pos (by norm_num) (by positivity : (0 : ℝ) < 2 * c)).le.trans (h x)

theorem InitialIdentification.metricScalarAt_map {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H : ObservedHistory.{u}} (d : InitialIdentification P g H) (x : P.Carrier) :
    metricScalarAt (H.initialMetric 0) (d.map x) = metricScalarAt g x := by
  have hmetric : g = Diffeomorph.pullbackMetric (I := ThreeModel) (H.initialMetric 0) d.map := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact (d.metric_eq y v w).symm
  have h := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_pullback
    (I := ThreeModel) (H.initialMetric 0) d.map x
  rw [← hmetric] at h
  exact h.symm

theorem InitialIdentification.stageZero_scalarLowerBound {P : OrientedThreeStage.{u}}
    {g : P.Metric} {H : ObservedHistory.{u}} (d : InitialIdentification P g H) {c : ℝ}
    (h : InitialScalarBarrier g c) :
    ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) y := by
  intro y
  obtain ⟨x, rfl⟩ := d.map.toEquiv.surjective y
  have hmap : metricScalarAt (H.initialMetric 0) (d.map.toEquiv x) = metricScalarAt g x :=
    d.metricScalarAt_map x
  rw [hmap, H.time_zero, zero_add]
  exact h x

theorem InitialIdentification.historyScalarLowerBound {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H : ObservedHistory.{u}} (d : InitialIdentification P g H) {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c : ℝ} (hc : 0 < c) (h : InitialScalarBarrier g c) :
    HistoryScalarLowerBound H c :=
  (DifferentialGeometry.PDE.RicciFlow.historyScalarLowerBound_of_history cutoff hc
    (d.stageZero_scalarLowerBound h)).1

theorem ObservationTower.historyScalarLowerBound_of_initialScalarBarrier
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c) (h : InitialScalarBarrier g c) :
    ∀ (b : ℝ) (hb : 0 < b), HistoryScalarLowerBound (T.observe b hb.le) c :=
  fun b hb => (T.observeInitial b hb.le).historyScalarLowerBound (cutoff b hb) hc h

theorem roundThreeSphereShrinkerMetric_initialScalarBarrier {c : ℝ} (hc : 0 < c) :
    InitialScalarBarrier DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric c := by
  intro x
  rw [DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature x]
  exact (div_neg_of_neg_of_pos (by norm_num) (by positivity : (0 : ℝ) < 2 * c)).le.trans
    (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
