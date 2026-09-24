import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionExistenceReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def HasUniformWidthBound (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∀ (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters)
    (_cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    (c : ℝ), 0 < c → T.HasUniformHistoryScalarLowerBound c →
      ∃ A : ℝ, 0 ≤ A ∧ T.toObservationTower.UniformRecordsAbove c A

namespace ObservationTower

theorem isEmpty_final_stage_of_isEmpty_carrier {P : OrientedThreeStage.{u}} [IsEmpty P.Carrier]
    {g : P.Metric} (T : ObservationTower P g) (b : ℝ) (hb : 0 ≤ b) :
    IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier := by
  have h0 : IsEmpty ((T.observe b hb).stage 0).Carrier :=
    (T.observeInitial b hb).map.toEquiv.symm.isEmpty
  have hlast := (T.observe b hb).empty_stage_is_last 0
  rw [← hlast]
  exact h0

end ObservationTower

theorem hasUniformWidthBound_of_isEmpty (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) : HasUniformWidthBound P g := by
  intro T parameters cutoff c hc hscalar
  refine ⟨0, le_rfl, fun b hb _hlt _terminal => ?_⟩
  exact ((ConnectedComponents.isEmpty_iff_isEmpty.mpr
    (T.toObservationTower.isEmpty_final_stage_of_isEmpty_carrier b hb.le)).false _terminal).elim

theorem hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput_of_uniformWidthBound
    {P : OrientedThreeStage.{u}} {g : P.Metric} (h : HasMorganTianExtinctionInput P g)
    (hw : HasUniformWidthBound P g) : HasUniformRecordsSurgeryTower P g := by
  obtain ⟨T, parameters, cutoff, c, hc, hbfr, hctrl, hscalar⟩ := h
  obtain ⟨A, hA, hrec⟩ := hw T parameters cutoff c hc hscalar
  exact ⟨T, c, A, hbfr, hctrl, hrec⟩

theorem hext_of_hasMorganTianExtinctionInput_of_uniformWidthBound
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasMorganTianExtinctionInput
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hw : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasUniformWidthBound
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  hext_of_hasUniformRecordsSurgeryTower fun M hsc g =>
    let _ := hsc
    hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput_of_uniformWidthBound
      (h M g) (hw M g)

theorem smoothPoincareConjecture_of_hasMorganTianExtinctionInput_of_uniformWidthBound
    (hsum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasMorganTianExtinctionInput
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hw : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasUniformWidthBound
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower hsum fun M hsc g =>
    let _ := hsc
    hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput_of_uniformWidthBound
      (h M g) (hw M g)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
