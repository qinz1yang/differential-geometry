import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctionTimeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreUniformRecords
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_initialScalarBarrier_of_compact
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel 1 M] [CompactSpace M] [T2Space M]
    [Nonempty M] (g : SmoothRiemannianMetric ThreeModel M) :
    ∃ c : ℝ, 0 < c ∧ InitialScalarBarrier g c := by
  obtain ⟨x₀, -, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn Set.univ_nonempty
      (DifferentialGeometry.Geometry.Curvature.metricScalar_smooth g).continuous.continuousOn
  have hkey : -3 * |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀| ≤
      2 * DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ := by
    linarith [abs_nonneg (DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀),
      neg_le_abs (DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀)]
  refine ⟨1 / (1 + |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀|),
    by positivity, fun x => ?_⟩
  have hx : DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ ≤
      DifferentialGeometry.Geometry.Curvature.metricScalarAt g x := hmin (Set.mem_univ x)
  have hmid : -3 * (1 + |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀|) / 2 ≤
      DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ := by linarith
  rw [mul_one_div, div_div_eq_mul_div]
  linarith

theorem exists_initialScalarBarrier_of_connectedClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    ∃ c : ℝ, 0 < c ∧ InitialScalarBarrier g c :=
  letI : Nonempty M.Carrier := M.connected.toNonempty
  exists_initialScalarBarrier_of_compact g

private def scaffoldDeepRadius : ℝ :=
  min (min (standardCapL / 2) (standardCapRadiusOfZ (-2) / 2)) (1 / 2)

private theorem scaffoldDeepRadius_pos : 0 < scaffoldDeepRadius :=
  lt_min (lt_min (half_pos standardCapL_pos) (half_pos (Function.invFun
    standardCapConformalCoordinate (-2 : ℝ)).2)) (by norm_num)

private def standardCapScaffoldWitness : StaticCapScaffold where
  collarLength := 1
  collar_pos := one_pos
  positiveRadius := scaffoldDeepRadius / 2
  deepRadius := scaffoldDeepRadius
  positiveRadius_pos := half_pos scaffoldDeepRadius_pos
  positive_lt_deep := half_lt_self scaffoldDeepRadius_pos
  deep_lt_one := (min_le_right _ _).trans_lt (by norm_num)
  deep_lt_cap := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt
    (half_lt_self standardCapL_pos)
  deep_tip_side := by
    rw [mul_one]
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt
      (half_lt_self (Function.invFun standardCapConformalCoordinate (-2 : ℝ)).2)

theorem nonempty_cutoffParameters : Nonempty CutoffParameters :=
  ⟨{ delta := fun _ => 1 / 2
     neckRadius := fun _ => 1
     protectedRadius := fun _ => 1
     delta_pos := fun _ _ => by norm_num
     delta_lt_one := fun _ _ => by norm_num
     neckRadius_pos := fun _ _ => one_pos
     protectedRadius_pos := fun _ _ => one_pos
     fixed := standardCapScaffoldWitness
     modelRadius := 1
     modelRadius_pos := one_pos
     modelOrder := 0
     modelAccuracy := 1
     modelAccuracy_pos := one_pos
     recenterConstant := 4
     recenterConstant_ge_four := le_rfl }⟩

def RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (c : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c

def HasSurgeryContinuationTower (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters)
    (_cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b)),
    T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded

def HasMorganTianExtinctionInput (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters)
    (_cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    (c : ℝ),
    0 < c ∧ T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
      T.HasUniformHistoryScalarLowerBound c

def HasUniformRecordsSurgeryTower (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (c A : ℝ),
    T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
      T.toObservationTower.UniformRecordsAbove c A

theorem hasSurgeryContinuationTower_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasSurgeryContinuationTower P g := by
  obtain ⟨q⟩ := nonempty_cutoffParameters
  refine ⟨RetainedCoreObservationTower.empty P g, fun _ => q, ?_,
    (fun _ j => Fin.elim0 j), (fun _ j => Fin.elim0 j)⟩
  intro b hb i
  exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_observe_eventCount P g b hb.le) i)

theorem hasMorganTianExtinctionInput_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasMorganTianExtinctionInput P g := by
  obtain ⟨q⟩ := nonempty_cutoffParameters
  refine ⟨RetainedCoreObservationTower.empty P g, fun _ => q, ?_, 1, one_pos,
    (fun _ j => Fin.elim0 j), (fun _ j => Fin.elim0 j), ?_⟩
  · intro b hb i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_observe_eventCount P g b hb.le) i)
  · intro b hb
    exact fun _ _ x => (hP.false x).elim

theorem hasUniformRecordsSurgeryTower_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasUniformRecordsSurgeryTower P g :=
  ⟨RetainedCoreObservationTower.empty P g, 1, 1, (fun _ j => Fin.elim0 j),
    (fun _ j => Fin.elim0 j), ObservationTower.uniformRecordsAbove_empty P g 1 1⟩

theorem hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower
    {P : OrientedThreeStage.{u}} [Nonempty P.Carrier] {g : P.Metric}
    (h : HasSurgeryContinuationTower P g) : HasMorganTianExtinctionInput P g := by
  obtain ⟨T, parameters, cutoff, hbfr, hctrl⟩ := h
  obtain ⟨c, hc, hbarrier⟩ := exists_initialScalarBarrier_of_compact g
  exact ⟨T, parameters, cutoff, c, hc, hbfr, hctrl,
    T.toObservationTower.historyScalarLowerBound_of_initialScalarBarrier
      parameters cutoff hc hbarrier⟩

theorem hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasUniformRecordsSurgeryTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨T, _c, _A, hbfr, hctrl, hrec⟩ := h
  exact RetainedCoreObservationTower.hasExtinctRetainedCoreHistory M T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_uniformRecordsAbove hrec)

theorem hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput
    {P : OrientedThreeStage.{u}} [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (h : HasMorganTianExtinctionInput P g) :
    HasUniformRecordsSurgeryTower P g := by
  obtain ⟨T, parameters, cutoff, c, hc, hbfr, hctrl, hscalar⟩ := h
  obtain ⟨Γ₀, hrec⟩ := T.toObservationTower.uniformRecordsAbove_of_scalarLowerBound
    parameters cutoff hc hscalar
  exact ⟨T, c, Extinction.Width.familyMaximum g Γ₀.1, hbfr, hctrl, hrec⟩

theorem hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier]
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasMorganTianExtinctionInput
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    HasExtinctRetainedCoreHistory M g :=
  letI : ConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected
  letI : SimplyConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := inferInstanceAs (SimplyConnectedSpace M.Carrier)
  hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower M g
    (hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
