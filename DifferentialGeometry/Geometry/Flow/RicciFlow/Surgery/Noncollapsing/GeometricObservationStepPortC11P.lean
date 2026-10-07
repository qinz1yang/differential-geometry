import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralCanonicalProduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MarkedContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

/-!
# O-CH11-FIX3 port of astra `GeometricObservationStep`（`PortC11P`）

来源：donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Noncollapsing/`
`GeometricObservationStep.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。B1 里它原是
SKIP-on-`CutoffRecordSplicing`；G1 落地后 verbatim 试编只剩两处 elaboration 失败：
`simpa only [htime] using hδ (Fin.last H.eventCount)`（及 `hρ` 同型）——`simp` 没有把
`(H.appendEvent ⋯ E hinitE).time (Fin.last H.eventCount).succ` 改写成 `s`，"After simplification" 型不符。

本 port 两处修补（同一模式；no statement / definition / proof idea altered）：
* `hδnew`、`hρnew`：`simpa only [htime] using h (Fin.last H.eventCount)` 改为
  `rw [← htime]` 加 `exact h (Fin.last H.eventCount)`（同一等式 `htime`，只换改写方向与位置）。

原路径 `GeometricObservationStep` 是只 import 本文件的 re-export shim（用户 22:2x 扩大的例外：
W1 闭包内的 FAIL 根）。
-/

set_option autoImplicit false

noncomputable section

namespace GC.GeneralFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Manifold
open scoped Manifold ContDiff ENNReal NNReal

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- A finite-horizon surgery step preserves the caller's records and smooth observed tail. -/
theorem exists_geometric_observation_step
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
              H.initialMetric (Fin.last H.eventCount))
            (A' : InitialIdentification P g (H.appendEvent E.incoming.lt E hinit).toHistory)
            (q : CutoffParameters)
            (new : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q)
            (records : ∀ i : Fin (H.appendEvent E.incoming.lt E hinit).eventCount,
              GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory i
                (p.spliceAfter q H.horizon)),
            E.incoming = G ∧ H.horizon < s ∧ A.IsPrefixOf A' ∧
            (q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
              q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
              q.recenterConstant = p₀.recenterConstant) ∧
            q.delta s ≤ δbound ∧ q.neckRadius s ≤ ρbound ∧
            (∀ b, (new.static b).hasCanonicalWindow) ∧
            (H.appendEvent E.incoming.lt E hinit).IsCanonicalCutoffRecordFamily
              p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records i.castSucc).nominalRadius (old i).nominalRadius ∧
              HEq (records i.castSucc).delta (old i).delta ∧
              HEq (records i.castSucc).order (old i).order ∧
              HEq (records i.castSucc).neck (old i).neck ∧
              HEq (records i.castSucc).static (old i).static) ∧
            HEq (records (Fin.last H.eventCount)).nominalRadius new.nominalRadius ∧
            HEq (records (Fin.last H.eventCount)).delta new.delta ∧
            HEq (records (Fin.last H.eventCount)).order new.order ∧
            HEq (records (Fin.last H.eventCount)).neck new.neck ∧
            HEq (records (Fin.last H.eventCount)).static new.static ∧
            E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
  obtain ⟨εbar, hεbar, hcn⟩ := general_strong_canonical P g
  obtain ⟨Λ, hΛ, hstepB⟩ := uniform_debit_surgery_step P g B εbar hB hεbar
  obtain ⟨_, _, _, _, q₀, _, δ₀, ρ₀, ε₀, D₀, m₀, Ctime, _, _, _, -, -, -, -, hq₀, -, hδ₀, hρ₀,
    hε₀, hD₀, -, -, hcl₀⟩ := hcn B (min (1 / 22) εbar) Λ hB (lt_min (by norm_num) hεbar)
      ((min_le_left _ _).trans_lt (by norm_num)) (min_le_right _ _) hΛ
  obtain ⟨ε, hε, hε', hεbarε, hstepε⟩ := hstepB Ctime
  obtain ⟨C1, C2, C1s, C2s, q₁, τmin, δ₁, ρ₁, ε₁, D₁, m₁, _, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s,
    -, hτ, hδ₁, hρ₁, hε₁, -, hκ, ha₀, hcl₁⟩ := hcn B ε Λ hB hε hε' hεbarε hΛ
  obtain ⟨p₀, δbound, ρbound, v, hacc, hD, hm, hδbound, hδle, hρbound, hρle, hΛle, hv, hnext⟩ :=
    hstepε C1 C2 C1s C2s (max q₀ q₁) τmin (min δ₀ δ₁) (min ρ₀ ρ₁) (min ε₀ ε₁) (max D₀ D₁)
      (max m₀ m₁) Cgrad κ a₀ hC1 hC2 hC1s hC2s (lt_max_of_lt_left hq₀) hτ (lt_min hδ₀ hδ₁)
      (lt_min hρ₀ hρ₁) (lt_min hε₀ hε₁) (lt_max_of_lt_left hD₀) hκ ha₀
  rw [le_min_iff] at hacc hδle hρle
  rw [max_le_iff] at hD hm
  refine ⟨p₀, δbound, ρbound, v, hδbound, hρbound, hv, ?_⟩
  intro H A p old hhor hold s G hs hinit hsing
  let J := H.prefixAt (Fin.last H.eventCount)
  let initial : InitialIdentification P g J.toHistory := A.ofStageZero rfl HEq.rfl
  have hJhor : J.horizon < B := H.time_le_horizon.trans_lt hhor
  have hInv : J.hasCanonicalCutoffRecords p₀ δbound ρbound :=
    (J.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mpr
      ⟨p, H.prefixRecords (Fin.last H.eventCount) old,
        H.isCanonicalCutoffRecordFamily_prefixAt (Fin.last H.eventCount) hold⟩
  obtain ⟨hderiv, -, -, -, -, -, hslab₀⟩ :=
    hcl₀ p₀ δbound ρbound hacc.1 hD.1 hm.1 hδle.1 hρle.1 hΛle J initial rfl hJhor hInv
  obtain ⟨-, hgrad, hcan, hspat, hpinch, hnc, hslab₁⟩ :=
    hcl₁ p₀ δbound ρbound hacc.2 hD.2 hm.2 hδle.2 hρle.2 hΛle J initial rfl hJhor hInv
  obtain ⟨hderivG, -⟩ := hslab₀ s G hs hinit hsing
  obtain ⟨-, hgradG, hcanG, hspatG, hncG⟩ := hslab₁ s G hs hinit hsing
  obtain ⟨Q, E, hinitE, _, hEG, hInvK, -, -, -, -, -, -, hbfr, hctrl, hdebit⟩ :=
    hnext J initial rfl hJhor hInv
      (fun j y t ht hR => hderiv j y t ht ((le_max_left _ _).trans_lt hR))
      (fun j => (J.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le
        (le_max_right _ _) (hgrad j))
      (fun j => (J.toHistory.event j).incoming.canonicalBefore_of_threshold_le
        (le_max_right _ _) (hcan j))
      (fun j => (J.toHistory.event j).incoming.spatiallyCanonicalBefore_of_threshold_le
        (le_max_right _ _) (hspat j))
      hpinch hnc s G hs hinit hsing
      (fun y t ht hR => hderivG y t ht ((le_max_left _ _).trans_lt hR))
      (G.gradientBoundBefore_of_threshold_le (le_max_right _ _) hgradG)
      (fun y t ht hR hτ => hcanG y t ht ((le_max_right _ _).trans_lt hR) hτ)
      (G.spatiallyCanonicalBefore_of_threshold_le (le_max_right _ _) hspatG) hncG
  change (H.appendEvent E.incoming.lt E hinitE).hasCanonicalCutoffRecords
    p₀ δbound ρbound at hInvK
  obtain ⟨q, hqf, hqD, hqm, hqε, hqc, fine, hwin, hδ, hρ⟩ := hInvK
  let new : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinitE).toHistory
      (Fin.last H.eventCount) q := fine (Fin.last H.eventCount)
  have hwinNew : ∀ b, (new.static b).hasCanonicalWindow := hwin (Fin.last H.eventCount)
  have htime : (H.appendEvent E.incoming.lt E hinitE).time
      (Fin.last H.eventCount).succ = s := H.appendEvent_time_last E.incoming.lt E hinitE
  have hδnew : q.delta s ≤ δbound := by
    rw [← htime]
    exact hδ (Fin.last H.eventCount)
  have hρnew : q.neckRadius s ≤ ρbound := by
    rw [← htime]
    exact hρ (Fin.last H.eventCount)
  have hsingE : E.incoming.SingularEndpoint := hEG.symm ▸ hsing
  have hfuture : H.horizon < s := actual_singular_event_after_horizon H E hinitE hsingE
  obtain ⟨A', hA⟩ := marked_singular_event_extension H A E hinitE hsingE
  obtain ⟨records, hfamily, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck, hNewStatic⟩ :=
    H.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter E.incoming.lt E hinitE
      hfuture old hold new ⟨hqf, hqD, hqm, hqε, hqc⟩ hwinNew hδnew hρnew
  exact ⟨Q, E, hinitE, A', q, new, records, hEG, hfuture, hA, ⟨hqf, hqD, hqm, hqε, hqc⟩,
    hδnew, hρnew, hwinNew, hfamily, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck,
    hNewStatic, hbfr, hctrl, hdebit⟩

end GC.GeneralFlow

end
