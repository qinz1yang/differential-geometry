import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialProviders
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDistanceBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecursion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ClosedBirthConstantsStrongC12X

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal
namespace GC.GeneralFlow
universe u

open private reserve_quality_of_same_prepared_class from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialReserveQualityData

/-- Genuine original-data chains retaining the same pre-fine class, radius and windows. -/
theorem exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin_with_reserve_quality
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    C.epsilon ≤ DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.εStrong_C12X.{u} ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.prepared.HasReserveQuality Dstar εReserve ∧
      base.DistanceData Cdist ∧
      ∀ (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ),
      (∀ n L future r, 0 < r →
        0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
        0 < (request n L future r).2.2.2) →
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      (∀ n, (future n).HasReserveQuality Dstar εReserve) ∧
      (∀ n, (S.state n).prepared.HasReserveQuality Dstar εReserve) ∧
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, fixed, recenter, C, hεs, _, prepareClass, analytic, makeBase⟩ :=
    exists_closedBirthConstants_strong_C12X.{u} Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, C, hεs, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl⟩ :=
    exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, prepared, _, hpreparedQuality, _,
    hfixed, hrecenter, hprepared, hExtension, _, _⟩ :=
    makeBase P g
  obtain ⟨base, hDistance, hState⟩ :=
    exists_prepared_spatial_base_with_distance_scalars_and_small_test_margin
      Cdist cMax hcMax pBase C P g prepared hprepared hExtension
  obtain ⟨hHistory, hInitial, hStage, hMetric, _, _, _, hPrepared, hShift, hOffset,
    hRadius, hFit, _, hRadiusConstant⟩ := hState
  have hbaseQuality : base.prepared.HasReserveQuality Dstar εReserve :=
    reserve_quality_of_same_prepared_class hStage.symm hMetric.symm
      (by rw [hShift, sub_zero]) hPrepared.symm hpreparedQuality
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hbaseQuality, hDistance, ?_⟩
  intro request hrequest
  exact exists_prepared_spatial_chain_with_quality_and_distance_scalars_and_small_test_margin_with_reserve_quality
    Dstar εReserve hDstar hεReserve
    Cdist cMax hcMax pBase C (by simpa only [hfixed, hrecenter] using prepareClass)
    analytic base hHistory hbaseQuality hDistance hRadius hFit request hrequest

/-- Preserve the original margin API by forgetting only reserve quality. -/
theorem exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.DistanceData Cdist ∧
      ∀ (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ),
      (∀ n L future r, 0 < r →
        0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
        0 < (request n L future r).2.2.2) →
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, (S.state n).radius * Real.sqrt (S.state n).prepared.Qall ≤ 100 * cMax) ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, C, -, makeInitial⟩ :=
    exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin_with_reserve_quality.{u}
      1 1 one_pos one_pos
  refine ⟨Cdist, hCdist, C, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, _, hDistance, makeChain⟩ := makeBase cMax hcMax
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hDistance, ?_⟩
  intro request hrequest
  obtain ⟨S, future, r, _, _, hChain⟩ := makeChain request hrequest
  exact ⟨S, future, r, hChain⟩

/-- Forget only the margin from the same genuine original-data construction. -/
theorem exists_prepared_spatial_quality_chains_from_initial :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ C : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase C P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.offset = 0 ∧ base.radius ≤ 1 ∧ base.DistanceData Cdist ∧
      ∀ (request : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase C P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase C
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ),
      (∀ n L future r, 0 < r →
        0 < (request n L future r).1 ∧ 0 < (request n L future r).2.1 ∧
        0 < (request n L future r).2.2.2) →
    ∃ (S : PreparedSpatialChain pBase C P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase C
        ((S.state n).native.stage (Fin.last (S.state n).native.eventCount))
        ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))
        ((3 : ℝ) ^ (n + 1) -
          (S.state n).history.time (Fin.last (S.state n).history.eventCount)))
      (r : ℕ → ℝ),
      S.state 0 = base ∧
      (∀ n, (S.state n).DistanceData Cdist) ∧
      (∀ n, 0 < r n ∧ (S.state (n + 1)).radius = r n ∧
        HEq (S.state (n + 1)).prepared (future n) ∧
        (S.state (n + 1)).shift =
          (S.state n).history.time (Fin.last (S.state n).history.eventCount) ∧
        (S.state (n + 1)).offset = (S.state n).history.eventCount ∧
        (S.state (n + 1)).nativeStage =
          (S.state n).native.stage (Fin.last (S.state n).native.eventCount) ∧
        HEq (S.state (n + 1)).nativeMetric
          ((S.state n).native.initialMetric (Fin.last (S.state n).native.eventCount))) ∧
      (∀ n, S.accuracy n ≤
        (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) ∧
      (∀ n, S.accuracy n ≤ (request n (S.state n) (future n) (r n)).2.2.2) ∧
      Nonempty (∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (request n (S.state n) (future n) (r n)).1
        (request n (S.state n) (future n) (r n)).2.1
        (request n (S.state n) (future n) (r n)).2.2.1) := by
  obtain ⟨Cdist, hCdist, C, makeInitial⟩ :=
    exists_prepared_spatial_quality_chains_from_initial_with_small_test_margin.{u}
  refine ⟨Cdist, hCdist, C, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  obtain ⟨pBase, base, hHistory, hInitial, _, hOffset, hRadius, _, _, hDistance,
    makeChain⟩ := makeBase 1 one_pos
  refine ⟨a₀, ha₀, initialControl, pBase, base, hHistory, hInitial,
    hOffset, hRadius, hDistance, ?_⟩
  intro request hrequest
  obtain ⟨S, future, r, hInitial, _, hDistance, hState, hQuarter, hRequest, hW⟩ :=
    makeChain request hrequest
  exact ⟨S, future, r, hInitial, hDistance, hState, hQuarter, hRequest, hW⟩

end GC.GeneralFlow
