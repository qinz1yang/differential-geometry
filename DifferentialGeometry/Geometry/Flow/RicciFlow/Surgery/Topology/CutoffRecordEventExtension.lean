import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation

noncomputable section

open Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def castStageMap {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {X : Type*} [TopologicalSpace X] (f : C(X, P.Carrier)) : C(X, Q.Carrier) := h ▸ f

private theorem castStageMap_smooth {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {δ : ℝ} (f : C(neckBuffer δ, P.Carrier))
    (hf : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ f) :
    IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ (castStageMap h f) := by
  cases h
  exact hf

private theorem neck_normalizedMetric_eq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ} {k : ℕ}
    {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck F.terminal.metric δ k}
    (hN : HEq N N') : N.normalizedMetric = N'.normalizedMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hN
  rfl

private theorem neck_chart_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ} {k : ℕ}
    {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck F.terminal.metric δ k}
    (hN : HEq N N') (f : C(neckBuffer δ, P.Carrier))
    (hf : ∀ x, f x = (N.chart x).1) :
    ∀ x, castStageMap hP f x = (N'.chart x).1 := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  cases eq_of_heq hN
  exact hf

private theorem crossing_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (g : C(neckBuffer δ, Q.Carrier))
    (hf : ∀ x, E.RegularCrossing (f x) (g x)) :
    ∀ x, F.RegularCrossing (castStageMap hP f x) (castStageMap hQ g x) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact hf

private theorem metric_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (hE : HEq E F) {δ : ℝ}
    (f : C(neckBuffer δ, P.Carrier)) (t : ℝ) (x : neckBuffer δ)
    (V W : TangentSpace NeckCylinderModel x) :
    (F.incoming.flow.base.metric t).inner (castStageMap hP f x)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP f) x V)
      (mfderiv NeckCylinderModel ThreeModel (castStageMap hP f) x W) =
    (E.incoming.flow.base.metric t).inner (f x)
      (mfderiv NeckCylinderModel ThreeModel f x V)
      (mfderiv NeckCylinderModel ThreeModel f x W) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl


def IncomingBackwardNeck.ofInitialEmbedding
    {H J : ObservedHistory.{u}} (hcount : H.eventCount ≤ J.eventCount)
    (htime : ∀ j : Fin (H.eventCount + 1),
      J.time (j.castLE (Nat.succ_le_succ hcount)) = H.time j)
    (hstage : ∀ j : Fin (H.eventCount + 1),
      J.stage (j.castLE (Nat.succ_le_succ hcount)) = H.stage j)
    (hevent : ∀ j : Fin H.eventCount,
      HEq (J.event (j.castLE hcount)) (H.event j))
    {i : Fin H.eventCount} {δ r : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.event i).terminal.metric δ k}
    {N' : NormalizedNeck (J.event (i.castLE hcount)).terminal.metric δ k}
    (hneck : HEq N' N) (B : IncomingBackwardNeck H i N r) :
    IncomingBackwardNeck J (i.castLE hcount) N' r := by
  let old (j : Fin J.eventCount) (hj : j.val ≤ i.val) : Fin H.eventCount :=
    ⟨j.val, lt_of_le_of_lt hj i.isLt⟩
  have htimeSucc (j : Fin H.eventCount) :
      J.time (j.castLE hcount).succ = H.time j.succ := htime j.succ
  have htimeOldSucc (j : Fin J.eventCount) (hj : j.val ≤ i.val) :
      J.time j.succ = H.time (old j hj).succ := htime (old j hj).succ
  have htimeOldCast (j : Fin J.eventCount) (hj : j.val ≤ i.val) :
      J.time j.castSucc = H.time (old j hj).castSucc := htime (old j hj).castSucc
  let chart (j : Fin J.eventCount) (hj : j.val ≤ (i.castLE hcount).val)
      (ha : J.time (i.castLE hcount).succ - r ^ 2 < J.time j.succ) :
      C(neckBuffer δ, (J.stage j.castSucc).Carrier) :=
    castStageMap (hstage (old j hj).castSucc).symm
      (B.stageChart (old j hj) hj
        (by rwa [htimeSucc, htimeOldSucc j hj] at ha))
  refine {
    radius_pos := B.radius_pos
    left_nonneg := by rw [htimeSucc]; exact B.left_nonneg
    stageChart := chart
    stageChart_smooth := fun j hj ha => castStageMap_smooth _ _ (B.stageChart_smooth _ _ _)
    terminal_chart := ?_
    crossing := ?_
    metric := B.metric
    terminal_metric := B.terminal_metric.trans ?_
    metric_on_slab := ?_
    timeDifferenceJet := B.timeDifferenceJet
    timeDifferenceJet_eq := B.timeDifferenceJet_eq
    parabolic_closeness := B.parabolic_closeness
    metric_smooth := B.metric_smooth }
  · intro ha
    exact neck_chart_transport (hstage i.castSucc).symm (hstage i.succ).symm
      (htime i.castSucc).symm (htime i.succ).symm (hevent i).symm hneck.symm
      (B.stageChart i le_rfl (by rwa [htimeSucc] at ha))
      (B.terminal_chart _)
  · intro j hj
    change j.val < i.val at hj
    dsimp only
    intro ha hn
    let j₀ := old j hj.le
    let next₀ : Fin H.eventCount := ⟨j.val + 1, by dsimp [old] at *; omega⟩
    have ha₀ : H.time i.succ - r ^ 2 < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj.le] at ha
    have hn₀ : H.time i.succ - r ^ 2 < H.time next₀.succ := by
      rw [htimeSucc] at hn
      have ht : J.time ⟨j.val + 1 + 1, by omega⟩ = H.time next₀.succ := htime next₀.succ
      exact ht ▸ hn
    exact crossing_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htime j₀.castSucc).symm (htime j₀.succ).symm (hevent j₀).symm
      (B.stageChart j₀ hj.le ha₀) (B.stageChart next₀ (by change j.val + 1 ≤ i.val; omega) hn₀)
      (B.crossing j₀ hj ha₀ hn₀)
  · exact neck_normalizedMetric_eq (hstage i.castSucc).symm (hstage i.succ).symm
      (htime i.castSucc).symm (htime i.succ).symm (hevent i).symm hneck.symm
  · intro j hj ha v hv hlo hhi x V W
    let j₀ := old j hj
    have ha₀ : H.time i.succ - r ^ 2 < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj] at ha
    have hlo₀ : H.time j₀.castSucc ≤ H.time i.succ + r ^ 2 * v := by
      rwa [htimeSucc, htimeOldCast j hj] at hlo
    have hhi₀ : H.time i.succ + r ^ 2 * v < H.time j₀.succ := by
      rwa [htimeSucc, htimeOldSucc j hj] at hhi
    change (B.metric v).inner x V W = (r ^ 2)⁻¹ *
      ((J.event j).incoming.flow.base.metric (J.time (i.castLE hcount).succ + r ^ 2 * v)).inner
      (castStageMap (hstage j₀.castSucc).symm (B.stageChart j₀ hj ha₀) x)
      (mfderiv NeckCylinderModel ThreeModel
        (castStageMap (hstage j₀.castSucc).symm (B.stageChart j₀ hj ha₀)) x V)
      (mfderiv NeckCylinderModel ThreeModel
        (castStageMap (hstage j₀.castSucc).symm (B.stageChart j₀ hj ha₀)) x W)
    rw [show J.time (i.castLE hcount).succ = H.time i.succ from htime i.succ]
    have hmetric := metric_transport (hstage j₀.castSucc).symm (hstage j₀.succ).symm
      (htime j₀.castSucc).symm (htime j₀.succ).symm (hevent j₀).symm (B.stageChart j₀ hj ha₀) (H.time i.succ + r ^ 2 * v) x V W
    exact (B.metric_on_slab j₀ hj ha₀ v hv hlo₀ hhi₀ x V W).trans
      (congrArg ((r ^ 2)⁻¹ * ·) hmetric.symm)


def IncomingBackwardNeck.appendEvent
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {δ r : ℝ} {k : ℕ}
    {N : NormalizedNeck (H.toHistory.event i).terminal.metric δ k}
    {N' : NormalizedNeck ((H.appendEvent hs E hinit).toHistory.event i.castSucc).terminal.metric δ k}
    (hneck : HEq N' N) (B : IncomingBackwardNeck H.toHistory i N r) :
    IncomingBackwardNeck (H.appendEvent hs E hinit).toHistory i.castSucc N' r := by
  refine IncomingBackwardNeck.ofInitialEmbedding (Nat.le_succ H.eventCount)
    (fun j => H.appendEvent_time_castSucc hs E hinit j)
    (fun j => H.appendEvent_stage_castSucc hs E hinit j) ?_ hneck B
  intro j
  change HEq ((H.extendCoreEventFamily E j.castSucc).toMetricCutCapEvent) (H.toHistory.event j)
  rw [H.extendCoreEventFamily_toMetricCutCapEvent]
  exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit j

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private structure CutoffFields {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s)
    (backwardFamily : {δ : ℝ} → {k : ℕ} →
      NormalizedNeck E.terminal.metric δ k → ℝ → Type u)
    (parameters : CutoffParameters) where
  singular : E.incoming.SingularEndpoint
  nominalRadius : Nonempty E.transition.trace.tubes.Index → ℝ
  nominal_pos : ∀ h, 0 < nominalRadius h
  nominal_small : ∀ h, nominalRadius h <
    (parameters.delta s)^2 * parameters.neckRadius s
  nominal_time : ∀ h, (nominalRadius h)^2 ≤ s
  delta : E.transition.trace.tubes.Index → ℝ
  delta_pos : ∀ α, 0 < delta α
  delta_le : ∀ α, delta α ≤ parameters.delta s
  order : E.transition.trace.tubes.Index → ℕ
  order_lower : ∀ α, max (parameters.modelOrder + 6) (2 * ⌊(delta α)⁻¹⌋₊ + 4) ≤ order α
  neck : ∀ α, NormalizedNeck E.terminal.metric (delta α) (order α)
  scale_eq : ∀ α, (neck α).scale = ((nominalRadius ⟨α⟩) ^ 2)⁻¹
  buffer_disjoint : Pairwise fun α β => Disjoint (Set.range (neck α).chart) (Set.range (neck β).chart)
  tube_eq : ∀ α, ∀ x : TubeDomain, ∀ hx : (x.1, x.2.1) ∈ neckBuffer (delta α),
    E.transition.trace.tubes.tube α x = ((neck α).chart ⟨(x.1, x.2.1), hx⟩).1
  tube_in_buffer : ∀ α, ∀ x : TubeDomain, (x.1, x.2.1) ∈ neckBuffer (delta α)
  backward : ∀ α, backwardFamily (neck α) (nominalRadius ⟨α⟩)
  retained_terminal : ∀ x ∈ E.transition.trace.retainedCore,
    x.1 ∈ E.incoming.terminalRegularRegion
  protected_interior : ∀ x : E.incoming.terminalRegularOpen,
    metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius s) ^ 2)⁻¹ →
    x.1 ∈ interior (Subtype.val '' E.transition.trace.retainedCore)
  retained_meets_protected : ∀ c : ConnectedComponents E.transition.trace.tubes.core,
    (∃ x : E.transition.trace.tubes.core,
      ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
    ∃ x : E.incoming.terminalRegularOpen,
      ∃ hx : x.1 ∈ E.transition.trace.tubes.core,
        ConnectedComponents.mk ⟨x.1, hx⟩ = c ∧
          metricScalarAt E.terminal.metric x ≤
            ((parameters.protectedRadius s) ^ 2)⁻¹
  one_retained_side : ∀ α,
    E.RetainedBoundary (α, true) ↔ ¬ E.RetainedBoundary (α, false)
  no_cuts_discard : IsEmpty E.transition.trace.tubes.Index →
    ∃ x : E.transition.trace.tubes.core, x ∉ E.transition.trace.retainedCore
  static : ∀ b : E.RetainedBoundaryIndex,
    MetricCutCapEvent.PresentedStaticCap E parameters.fixed parameters.modelRadius parameters.modelOrder
      parameters.modelAccuracy b
  recenter_scale : ∀ b : E.RetainedBoundaryIndex,
    (static b).neck.scale = metricScalarAt E.terminal.metric ((static b).neck.center)
  recenter_mark : ∀ b : E.RetainedBoundaryIndex,
    (static b).neck.sphereMark = (neck b.1.1).sphereMark
  recenter_delta : ∀ b : E.RetainedBoundaryIndex,
    (static b).delta = parameters.recenterConstant * delta b.1.1
  recenter_scale_comparison : ∀ b : E.RetainedBoundaryIndex,
    |(static b).neck.scale / (neck b.1.1).scale - 1| ≤
      parameters.recenterConstant * delta b.1.1
  recenter_chart : ∀ b : E.RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
    ∀ hx : (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1),
      (static b).neck.chart x = (neck b.1.1).chart
        ⟨(x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)), hx⟩
  recenter_in_buffer : ∀ b : E.RetainedBoundaryIndex,
    ∀ x : neckBuffer (static b).delta,
      (x.1.1, (if b.1.2 then 1 else -1) * (1 + x.1.2)) ∈ neckBuffer (delta b.1.1)
  old_eq_retained : E.old = E.transition.trace.retainedCore
  curvature_preserving : ∀ a : ℝ, 0 < a →
    (∀ x : E.incoming.terminalRegularOpen,
      InFixedHamiltonIveyRegion E.terminal.metric a x) →
    ∀ x : Q.Carrier, InFixedHamiltonIveyRegion E.outputMetric a x
  scalar_preserving : ∀ L : ℝ, L ≤ 0 →
    (∀ x : E.incoming.terminalRegularOpen,
      L ≤ metricScalarAt E.terminal.metric x) →
    ∀ x : Q.Carrier, L ≤ metricScalarAt E.outputMetric x


private def CutoffFields.ofRecord
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) :
    CutoffFields (H.event i) (fun {δ} {k} N r => @IncomingBackwardNeck H i δ k N r) p where
  singular := R.singular
  nominalRadius := R.nominalRadius
  nominal_pos := R.nominal_pos
  nominal_small := R.nominal_small
  nominal_time := R.nominal_time
  delta := R.delta
  delta_pos := R.delta_pos
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_eq := R.scale_eq
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  tube_in_buffer := R.tube_in_buffer
  backward := R.backward
  retained_terminal := R.retained_terminal
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static := R.static
  recenter_scale := R.recenter_scale
  recenter_mark := R.recenter_mark
  recenter_delta := R.recenter_delta
  recenter_scale_comparison := R.recenter_scale_comparison
  recenter_chart := R.recenter_chart
  recenter_in_buffer := R.recenter_in_buffer
  old_eq_retained := R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving

private def CutoffFields.toRecord
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : CutoffFields (H.event i) (fun {δ} {k} N r => @IncomingBackwardNeck H i δ k N r) p) :
    GeometricCutoffRecord H i p where
  singular := R.singular
  nominalRadius := R.nominalRadius
  nominal_pos := R.nominal_pos
  nominal_small := R.nominal_small
  nominal_time := R.nominal_time
  delta := R.delta
  delta_pos := R.delta_pos
  delta_le := R.delta_le
  order := R.order
  order_lower := R.order_lower
  neck := R.neck
  scale_eq := R.scale_eq
  buffer_disjoint := R.buffer_disjoint
  tube_eq := R.tube_eq
  tube_in_buffer := R.tube_in_buffer
  backward := R.backward
  retained_terminal := R.retained_terminal
  protected_interior := R.protected_interior
  retained_meets_protected := R.retained_meets_protected
  one_retained_side := R.one_retained_side
  no_cuts_discard := R.no_cuts_discard
  static := R.static
  recenter_scale := R.recenter_scale
  recenter_mark := R.recenter_mark
  recenter_delta := R.recenter_delta
  recenter_scale_comparison := R.recenter_scale_comparison
  recenter_chart := R.recenter_chart
  recenter_in_buffer := R.recenter_in_buffer
  old_eq_retained := R.old_eq_retained
  curvature_preserving := R.curvature_preserving
  scalar_preserving := R.scalar_preserving

private def CutoffFields.transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) : CutoffFields E' F' p := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact { R with backward := fun α => hF HEq.rfl (R.backward α) }

private theorem CutoffFields.transport_neck_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) :
    HEq (CutoffFields.transport (F := F) (F' := F') hP hQ ha hs hE hF R).neck R.neck := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

private theorem CutoffFields.transport_static_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) :
    HEq (CutoffFields.transport (F := F) (F' := F') hP hQ ha hs hE hF R).static R.static := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

private def GeometricCutoffRecord.ofEventHEq
    {H J : ObservedHistory.{u}} {i : Fin H.eventCount} {j : Fin J.eventCount}
    (hP : J.stage j.castSucc = H.stage i.castSucc)
    (hQ : J.stage j.succ = H.stage i.succ)
    (ha : J.time j.castSucc = H.time i.castSucc)
    (hs : J.time j.succ = H.time i.succ)
    (hE : HEq (J.event j) (H.event i))
    (hback : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck (H.event i).terminal.metric δ k}
      {N' : NormalizedNeck (J.event j).terminal.metric δ k},
      HEq N' N → IncomingBackwardNeck H i N r → IncomingBackwardNeck J j N' r)
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p) : GeometricCutoffRecord J j p :=
  (CutoffFields.transport
    (F := fun {δ} {k} N r => @IncomingBackwardNeck H i δ k N r)
    (F' := fun {δ} {k} N r => @IncomingBackwardNeck J j δ k N r)
    hP hQ ha hs hE (fun hNN => fun N => hback hNN N) (CutoffFields.ofRecord R)).toRecord

protected def GeometricCutoffRecord.appendEvent
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i.castSucc p := by
  refine GeometricCutoffRecord.ofEventHEq
    (H.appendEvent_stage_castSucc hs E hinit i.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit i.succ)
    (H.appendEvent_time_castSucc hs E hinit i.castSucc)
    (H.appendEvent_time_castSucc hs E hinit i.succ) ?_
    (fun hNN B => IncomingBackwardNeck.appendEvent H hs E hinit hNN B) R
  change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent) (H.toHistory.event i)
  rw [H.extendCoreEventFamily_toMetricCutCapEvent]
  exact H.toHistory.appendEvent_event_castSucc_heq hs E.toMetricCutCapEvent hinit i

theorem GeometricCutoffRecord.appendEvent_neck_heq
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).neck R.neck := by
  exact CutoffFields.transport_neck_heq _ _ _ _ _ _ _

theorem GeometricCutoffRecord.appendEvent_static_heq
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).static R.static := by
  exact CutoffFields.transport_static_heq _ _ _ _ _ _ _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem CutoffFields.transport_delta_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) :
    HEq (CutoffFields.transport (F := F) (F' := F') hP hQ ha hs hE hF R).delta R.delta := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

theorem GeometricCutoffRecord.appendEvent_delta_heq
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).delta R.delta := by
  exact CutoffFields.transport_delta_heq _ _ _ _ _ _ _

private theorem CutoffFields.transport_order_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {E' : MetricCutCapEvent P' Q' a' s'}
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s) (hE : HEq E' E)
    {F : {δ : ℝ} → {k : ℕ} → NormalizedNeck E.terminal.metric δ k → ℝ → Type u}
    {F' : {δ : ℝ} → {k : ℕ} → NormalizedNeck E'.terminal.metric δ k → ℝ → Type u}
    (hF : ∀ {δ r : ℝ} {k : ℕ}
      {N : NormalizedNeck E.terminal.metric δ k} {N' : NormalizedNeck E'.terminal.metric δ k},
      HEq N' N → F N r → F' N' r)
    {p : CutoffParameters} (R : CutoffFields E F p) :
    HEq (CutoffFields.transport (F := F) (F' := F') hP hQ ha hs hE hF R).order R.order := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  rfl

theorem GeometricCutoffRecord.appendEvent_order_heq
    {Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    HEq (GeometricCutoffRecord.appendEvent hs E hinit R).order R.order := by
  exact CutoffFields.transport_order_heq _ _ _ _ _ _ _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem RetainedCoreHistory.exists_cutoff_records_at_appendEvent
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {p q : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hfixed : q.fixed = p.fixed) (hradius : q.modelRadius = p.modelRadius)
    (horder : q.modelOrder = p.modelOrder) (haccuracy : q.modelAccuracy = p.modelAccuracy)
    (hrecenter : q.recenterConstant = p.recenterConstant) :
    ∃ R : ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
        GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory i (p.spliceAt q s),
      (∀ i : Fin H.eventCount, HEq (R i.castSucc).static (old i).static) ∧
      (∀ i : Fin H.eventCount, HEq (R i.castSucc).neck (old i).neck) ∧
      HEq (R (Fin.last H.eventCount)).static new.static ∧
      HEq (R (Fin.last H.eventCount)).neck new.neck ∧
      (∀ i : Fin H.eventCount, HEq (R i.castSucc).delta (old i).delta) ∧
      (∀ i : Fin H.eventCount, HEq (R i.castSucc).order (old i).order) ∧
      HEq (R (Fin.last H.eventCount)).delta new.delta ∧
      HEq (R (Fin.last H.eventCount)).order new.order := by
  let K := H.appendEvent hs E hinit
  have htime : K.toHistory.time (Fin.last H.eventCount).succ = s :=
    H.appendEvent_time_last hs E hinit
  let hnew := new.spliceParametersAt hfixed hradius horder haccuracy hrecenter
  have hnewstatic := new.spliceParametersAt_static_heq hfixed hradius horder haccuracy hrecenter
  have hnewneck := new.spliceParametersAt_neck_heq hfixed hradius horder haccuracy hrecenter
  have hnewdelta := heq_of_eq (new.spliceParametersAt_delta hfixed hradius horder haccuracy hrecenter)
  have hneworder := heq_of_eq (new.spliceParametersAt_order hfixed hradius horder haccuracy hrecenter)
  have hex : ∃ N : GeometricCutoffRecord K.toHistory (Fin.last H.eventCount) (p.spliceAt q s),
      HEq N.static new.static ∧ HEq N.neck new.neck ∧ HEq N.delta new.delta ∧ HEq N.order new.order := by
    have transfer (t u : ℝ) (h : t = u)
        (N : GeometricCutoffRecord K.toHistory (Fin.last H.eventCount) (p.spliceAt q t))
        (hstatic : HEq N.static new.static) (hneck : HEq N.neck new.neck)
        (hdelta : HEq N.delta new.delta) (horder : HEq N.order new.order) :
        ∃ N' : GeometricCutoffRecord K.toHistory (Fin.last H.eventCount) (p.spliceAt q u),
          HEq N'.static new.static ∧ HEq N'.neck new.neck ∧ HEq N'.delta new.delta ∧ HEq N'.order new.order := by
      cases h
      exact ⟨N, hstatic, hneck, hdelta, horder⟩
    exact transfer _ _ htime hnew hnewstatic hnewneck hnewdelta hneworder
  obtain ⟨N, hNstatic, hNneck, hNdelta, hNorder⟩ := hex
  have hne (i : Fin H.eventCount) : K.toHistory.time i.castSucc.succ ≠ s := by
    have ht : K.toHistory.time i.castSucc.succ = H.time i.succ :=
      H.appendEvent_time_castSucc hs E hinit i.succ
    rw [ht]
    exact ne_of_lt ((H.time_strictMono.monotone (Fin.le_last i.succ)).trans_lt hs)
  let Rold (i : Fin H.eventCount) :=
    ((old i).appendEvent hs E hinit).spliceParametersOfNe (q := q) (hne i)
  let R : ∀ i : Fin (H.eventCount + 1), GeometricCutoffRecord K.toHistory i (p.spliceAt q s) :=
    Fin.lastCases N Rold
  have hRold (i : Fin H.eventCount) : R i.castSucc = Rold i := Fin.lastCases_castSucc i
  have hRnew : R (Fin.last H.eventCount) = N := Fin.lastCases_last
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hRold]
    exact (((old i).appendEvent hs E hinit).spliceParametersOfNe_static_heq (hne i)).trans
      ((old i).appendEvent_static_heq hs E hinit)
  · intro i
    rw [hRold]
    exact (((old i).appendEvent hs E hinit).spliceParametersOfNe_neck_heq (hne i)).trans
      ((old i).appendEvent_neck_heq hs E hinit)
  · rw [hRnew]
    exact hNstatic
  · rw [hRnew]
    exact hNneck
  · intro i
    rw [hRold]
    exact (heq_of_eq (((old i).appendEvent hs E hinit).spliceParametersOfNe_delta (hne i))).trans
      ((old i).appendEvent_delta_heq hs E hinit)
  · intro i
    rw [hRold]
    exact (heq_of_eq (((old i).appendEvent hs E hinit).spliceParametersOfNe_order (hne i))).trans
      ((old i).appendEvent_order_heq hs E hinit)
  · rw [hRnew]
    exact hNdelta
  · rw [hRnew]
    exact hNorder

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
