import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

/-!
# Deep backward necks: history-level transports (C12X, S16 round 3, O-C12X-S16K G1c)

Deep analogues (`IncomingBackwardNeckDeep_C12X`, depth factor `θ`) of the history-level
operations on backward necks used when record families are moved between histories:

* `IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X` (initial embedding of histories,
  ST/CutoffRecordEventExtension) and `appendEvent_C12X` (old events after appending an event);
* `IncomingBackwardNeckDeep_C12X.ofPrefix_C12X` (history prefix, ST/RetainedCoreHistoryPrefix);
* `RecordHypFar_C12X.prefixRecords_C12X`: the route β′ record hypothesis passes to the prefix
  record family `H.prefixRecords k records` (needed by the class `strongControl` preparer, which
  works on `V.prefixAt (Fin.last _)`).

Each deep transport extends the depth-one transport (`toIncomingBackwardNeck`).
-/

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private castStageMap castStageMap_smooth crossing_transport metric_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension

open private RetainedCoreHistory.incomingBackwardNeckOfPrefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix

/-- Deep analogue of `IncomingBackwardNeck.ofInitialEmbedding`. -/
def IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X
    {H J : ObservedHistory.{u}} (hcount : H.eventCount ≤ J.eventCount)
    (htime : ∀ j : Fin (H.eventCount + 1),
      J.time (j.castLE (Nat.succ_le_succ hcount)) = H.time j)
    (hstage : ∀ j : Fin (H.eventCount + 1),
      J.stage (j.castLE (Nat.succ_le_succ hcount)) = H.stage j)
    (hevent : ∀ j : Fin H.eventCount,
      HEq (J.event (j.castLE hcount)) (H.event j))
    {i : Fin H.eventCount} {δ r θ : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ k}
    {N' : NormalizedNeck (J.event (i.castLE hcount)).terminal.metric δ k}
    (hneck : HEq N' N) (D : IncomingBackwardNeckDeep_C12X H i N r θ) :
    IncomingBackwardNeckDeep_C12X J (i.castLE hcount) N' r θ := by
  let old (j : Fin J.eventCount) (hj : j.val ≤ i.val) : Fin H.eventCount :=
    ⟨j.val, lt_of_le_of_lt hj i.isLt⟩
  have htimeSucc (j : Fin H.eventCount) :
      J.time (j.castLE hcount).succ = H.time j.succ := htime j.succ
  have htimeOldSucc (j : Fin J.eventCount) (hj : j.val ≤ i.val) :
      J.time j.succ = H.time (old j hj).succ := htime (old j hj).succ
  have htimeOldCast (j : Fin J.eventCount) (hj : j.val ≤ i.val) :
      J.time j.castSucc = H.time (old j hj).castSucc := htime (old j hj).castSucc
  let deepChart (j : Fin J.eventCount) (hj : j.val ≤ (i.castLE hcount).val)
      (ha : J.time (i.castLE hcount).succ - θ * r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap (hstage (old j hj).castSucc).symm
      (D.deepChart (old j hj) hj
        (by rwa [htimeSucc, htimeOldSucc j hj] at ha))
  refine {
    toIncomingBackwardNeck :=
      D.toIncomingBackwardNeck.ofInitialEmbedding hcount htime hstage hevent hneck
    one_le_depth := D.one_le_depth
    deep_left_nonneg := by rw [htimeSucc]; exact D.deep_left_nonneg
    deepChart := deepChart
    deepChart_smooth := fun j hj ha => castStageMap_smooth _ _ (D.deepChart_smooth _ _ _)
    deepChart_eq := ?_
    deep_crossing := ?_
    deep_metric_on_slab := ?_
    deepJet := D.deepJet
    deepJet_eq := D.deepJet_eq
    deep_closeness := D.deep_closeness
    deep_metric_smooth := D.deep_metric_smooth }
  · intro j hj ha ha'
    exact congrArg (castStageMap (hstage (old j hj).castSucc).symm)
      (D.deepChart_eq (old j hj) hj _ _)
  · intro j hj
    change j.val < i.val at hj
    dsimp only
    intro ha hn
    let j₀ := old j hj.le
    let next₀ : Fin H.eventCount := ⟨j.val + 1, by dsimp [old] at *; omega⟩
    have ha₀ : H.time i.succ - θ * r ^ 2 < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj.le] at ha
    have hn₀ : H.time i.succ - θ * r ^ 2 < H.time next₀.succ := by
      rw [htimeSucc] at hn
      have ht : J.time ⟨j.val + 1 + 1, by omega⟩ = H.time next₀.succ := htime next₀.succ
      exact ht ▸ hn
    exact crossing_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htime j₀.castSucc).symm (htime j₀.succ).symm (hevent j₀).symm
      (D.deepChart j₀ hj.le ha₀)
      (D.deepChart next₀ (by change j.val + 1 ≤ i.val; omega) hn₀)
      (D.deep_crossing j₀ hj ha₀ hn₀)
  · intro j hj ha v hv hlo hhi x V W
    let j₀ := old j hj
    have ha₀ : H.time i.succ - θ * r ^ 2 < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj] at ha
    have hlo₀ : H.time j₀.castSucc ≤ H.time i.succ + r ^ 2 * v := by
      rwa [htimeSucc, htimeOldCast j hj] at hlo
    have hhi₀ : H.time i.succ + r ^ 2 * v < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj] at hhi
    change (D.metric v).inner x V W = (r ^ 2)⁻¹ *
      ((J.event j).incoming.flow.base.metric (J.time (i.castLE hcount).succ + r ^ 2 * v)).inner
      (castStageMap (hstage j₀.castSucc).symm (D.deepChart j₀ hj ha₀) x)
      (mfderiv NeckCylinderModel ThreeModel
        (castStageMap (hstage j₀.castSucc).symm (D.deepChart j₀ hj ha₀)) x V)
      (mfderiv NeckCylinderModel ThreeModel
        (castStageMap (hstage j₀.castSucc).symm (D.deepChart j₀ hj ha₀)) x W)
    rw [show J.time (i.castLE hcount).succ = H.time i.succ from htime i.succ]
    have hmetric := metric_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htime j₀.castSucc).symm (htime j₀.succ).symm (hevent j₀).symm (D.deepChart j₀ hj ha₀)
      (H.time i.succ + r ^ 2 * v) x V W
    exact (D.deep_metric_on_slab j₀ hj ha₀ v hv hlo₀ hhi₀ x V W).trans
      (congrArg ((r ^ 2)⁻¹ * ·) hmetric.symm)

/-- Deep analogue of `IncomingBackwardNeck.appendEvent` (an old event after appending). -/
def IncomingBackwardNeckDeep_C12X.appendEvent_C12X
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {δ r θ : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.toHistory.event i).terminal.metric δ k}
    {N' : NormalizedNeck
      ((H.appendEvent hs E hinit).toHistory.event i.castSucc).terminal.metric δ k}
    (hneck : HEq N' N) (D : IncomingBackwardNeckDeep_C12X H.toHistory i N r θ) :
    IncomingBackwardNeckDeep_C12X (H.appendEvent hs E hinit).toHistory i.castSucc N' r θ := by
  refine IncomingBackwardNeckDeep_C12X.ofInitialEmbedding_C12X (Nat.le_succ H.eventCount)
    (fun j => H.appendEvent_time_castSucc hs E hinit j)
    (fun j => H.appendEvent_stage_castSucc hs E hinit j) ?_ hneck D
  intro j
  change HEq ((H.extendCoreEventFamily E j.castSucc).toMetricCutCapEvent) (H.toHistory.event j)
  rw [H.extendCoreEventFamily_toMetricCutCapEvent]
  exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit j

/-- Deep analogue of the prefix transport of backward necks
(`RetainedCoreHistory.incomingBackwardNeckOfPrefix`). -/
def IncomingBackwardNeckDeep_C12X.ofPrefix_C12X (H : RetainedCoreHistory.{u})
    (k : Fin (H.eventCount + 1))
    {i : Fin (H.prefixAt k).eventCount} {δ r θ : ℝ} {m : ℕ}
    {neck : NormalizedNeck ((H.prefixAt k).toHistory.event i).terminal.metric δ m}
    (D : IncomingBackwardNeckDeep_C12X H.toHistory (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)
      neck r θ) :
    IncomingBackwardNeckDeep_C12X (H.prefixAt k).toHistory i neck r θ where
  toIncomingBackwardNeck :=
    RetainedCoreHistory.incomingBackwardNeckOfPrefix H k D.toIncomingBackwardNeck
  one_le_depth := D.one_le_depth
  deep_left_nonneg := D.deep_left_nonneg
  deepChart j hj ha := D.deepChart (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha
  deepChart_smooth j hj ha :=
    D.deepChart_smooth (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha
  deepChart_eq j hj ha ha' :=
    D.deepChart_eq (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha ha'
  deep_crossing j hj ha hn x :=
    D.deep_crossing (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha hn x
  deep_metric_on_slab j hj ha v hv h1 h2 x V W :=
    D.deep_metric_on_slab (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) hj ha v hv h1 h2 x V W
  deepJet := D.deepJet
  deepJet_eq := D.deepJet_eq
  deep_closeness := D.deep_closeness
  deep_metric_smooth := D.deep_metric_smooth

/-- The route β′ record hypothesis passes to the prefix record family. -/
theorem RecordHypFar_C12X.prefixRecords_C12X {θ : ℝ} {H : RetainedCoreHistory.{u}}
    {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (h : RecordHypFar_C12X θ H records) (k : Fin (H.eventCount + 1)) :
    RecordHypFar_C12X θ (H.prefixAt k) (H.prefixRecords k records) := by
  refine ⟨fun i α => ?_, fun i b => h.2 (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) b⟩
  obtain ⟨D⟩ := h.1 (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) α
  exact ⟨IncomingBackwardNeckDeep_C12X.ofPrefix_C12X H k D⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
