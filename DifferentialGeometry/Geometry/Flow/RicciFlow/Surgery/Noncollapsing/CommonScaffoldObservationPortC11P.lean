import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.NoncollapsedGeometricObservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformScaffoldSurgeryStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedWindowTransportC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRadialCoordinates

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepRecordC12X

/-!
# S-CH11-FIX11 port of astra `CommonScaffoldObservation`（`PortC11P`）

来源：donor `CommonScaffoldObservation.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* 主证明 `cast` 情形的 `hE : HEq (… appendEvent … .event i.castSucc) (H.toHistory.event i)`：
  `rw [H.extendCoreEventFamily_toMetricCutCapEvent]` 失败（`E` 的类型挂在
  `J := H.prefixAt (Fin.last _)` 的 stage 上，`rw` 在 reducible 下无法与 `H.stage (Fin.last _)`
  统一，报 "Application type mismatch … E.outputMetric"）→ 改 term 模式
  `(heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent E i.castSucc)).trans
  (…appendEvent_event_castSucc_heq …)`（同 `TowerInductionStep` l.703 的写法；默认
  transparency 下 `E` 可统一）。

原路径 `CommonScaffoldObservation` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

namespace GC.GeneralFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

universe u

open private observation_initial_budget_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

/-- One scaffold precedes every initial metric; for each finite horizon the
noncollapse radius and coefficient are chosen before the requested quality
packet. The actual constructed history and selected records retain all bounds. -/
theorem exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
    (4 ≤ recenterConstant ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        (∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
        RecordHypFar_C12X (5 / 4) K records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  classical
  obtain ⟨Cdist, hCdist, fixed, Λ, hΛfour, hstep⟩ :=
    exists_uniform_scaffold_surgery_step_with_radial_coordinates_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, Λ, hΛfour, ?_⟩
  intro P g B hB
  obtain ⟨εcanbar, hεcanbar, hcn⟩ := general_strong_canonical P g
  obtain ⟨εregbar, hεregbar, hregular⟩ := exists_regular_observation_noncollapsed P g
  let εbar : ℝ := min εcanbar εregbar
  have hεbar : 0 < εbar := lt_min hεcanbar hεregbar
  have hΛ : 0 < Λ := by linarith
  have hstepB := hstep P g B εbar hB hεbar
  obtain ⟨_, _, _, _, q₀, _, δ₀, ρ₀, ε₀, D₀, m₀, Ctime, _, _, _, -, -, -, -, hq₀, -, hδ₀, hρ₀,
    hε₀, _, -, -, hcl₀⟩ := hcn B (min (1 / 22) εbar) Λ hB (lt_min (by norm_num) hεbar)
      ((min_le_left _ _).trans_lt (by norm_num))
      ((min_le_right _ _).trans (min_le_left _ _)) hΛ
  obtain ⟨ε, hε, hε', hεbarε, hstepε⟩ := hstepB Ctime
  obtain ⟨C1, C2, C1s, C2s, q₁, τmin, δ₁, ρ₁, ε₁, D₁, m₁, _, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s,
    -, hτ, hδ₁, hρ₁, hε₁, -, hκ, ha₀, hcl₁⟩ := hcn B ε Λ hB hε hε'
      (hεbarε.trans (min_le_left _ _)) hΛ
  obtain ⟨δR, ρR, εR, DR, mR, κR, hδR, hρR, hεR, _, hκR, hNCR⟩ :=
    hregular (B + 1) ε Λ (by linarith) hε hε'
      (hεbarε.trans (min_le_right _ _)) hΛ
  refine ⟨ε, κR, hε, hε', hκR, ?_⟩
  intro δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨p₀, δbound, ρbound, v, hpf, hpc, hacc, hD, hm, hδbound, hδle, hρbound, hρle, hΛle, hv, hnext⟩ :=
    hstepε C1 C2 C1s C2s (max q₀ q₁) τmin
      (min (min (min δ₀ δ₁) δR) (min δcut (2 * Λ)⁻¹))
      (min (min (min ρ₀ ρ₁) ρR) ρcut) (min (min (min ε₀ ε₁) εR) (min εcut (1 / 2)))
      (max (max (max D₀ D₁) DR) (max Dcut (standardCapL + 1))) (max (max (max m₀ m₁) mR) mcut) Cgrad κ a₀
      hC1 hC2 hC1s hC2s (lt_max_of_lt_left hq₀) hτ
      (lt_min (lt_min (lt_min hδ₀ hδ₁) hδR) (lt_min hδcut (by positivity)))
      (lt_min (lt_min (lt_min hρ₀ hρ₁) hρR) hρcut)
      (lt_min (lt_min (lt_min hε₀ hε₁) hεR) (lt_min hεcut (by norm_num)))
      (lt_max_of_lt_right (hDcut.trans_le (le_max_left _ _))) hκ ha₀
  obtain ⟨hacc, haccRequest⟩ := le_min_iff.mp hacc
  obtain ⟨haccRequest, haccHalf⟩ := le_min_iff.mp haccRequest
  obtain ⟨hD, hDRequest⟩ := max_le_iff.mp hD
  obtain ⟨hDRequest, hDClosed⟩ := max_le_iff.mp hDRequest
  obtain ⟨hm, hmRequest⟩ := max_le_iff.mp hm
  obtain ⟨hδle, hδRequest⟩ := le_min_iff.mp hδle
  obtain ⟨hρle, hρRequest⟩ := le_min_iff.mp hρle
  obtain ⟨hδRequest, hδΛ⟩ := le_min_iff.mp hδRequest
  have hrec : p₀.recenterConstant * δbound ≤ 1 / 2 := by
    have hprod : δbound * (2 * Λ) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * Λ)).mp (by simpa only [one_div] using hδΛ)
    have hle := mul_le_mul_of_nonneg_right hΛle hδbound.le
    nlinarith
  obtain ⟨hacc, haccR⟩ := le_min_iff.mp hacc
  obtain ⟨hD, hDR⟩ := max_le_iff.mp hD
  obtain ⟨hm, hmR⟩ := max_le_iff.mp hm
  obtain ⟨hδle, hδRle⟩ := le_min_iff.mp hδle
  obtain ⟨hρle, hρRle⟩ := le_min_iff.mp hρle
  rw [le_min_iff] at hacc hδle hρle
  rw [max_le_iff] at hD hm
  have hnoncollapse : ∀ (H : RetainedCoreHistory.{u})
      (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.NoncollapsedBefore κR ε H.horizon := by
    intro H A p records hHB hfamily
    exact hNCR p₀ δbound ρbound haccR hDR hmR hδRle hρRle hΛle
      H A p records (by linarith) hfamily
  have step : ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        (∀ i b, ((old i).static b).witness.HasRadialCoordinates ∧
          ((old i).static b).hasLinkedCanonicalWindow_C12X) →
        RecordHypFar_C12X (5 / 4) H old →
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
            (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
            RecordHypFar_C12X (5 / 4) (H.appendEvent E.incoming.lt E hinit) records ∧
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
            E.toMetricCutCapEvent.HasUniformDistanceScalar Cdist ∧
            E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
    intro H A p old hhor hold hcoordinatesOld hdeepOld s G hs hinit hsing
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
    obtain ⟨Q, E, hinitE, q, hEG, _, hqf, hqD, hqm, hqε, hqc, hrecord,
      hDistance, hbfr, hctrl, hdebit⟩ :=
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
    obtain ⟨new, hwinNew, hcoordinatesNew, hdeepNew, hδnew, hρnew⟩ := hrecord
    have hsingE : E.incoming.SingularEndpoint := hEG.symm ▸ hsing
    have hfuture : H.horizon < s := actual_singular_event_after_horizon H E hinitE hsingE
    obtain ⟨A', hA⟩ := marked_singular_event_extension H A E hinitE hsingE
    obtain ⟨records, hfamily, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck, hNewStatic⟩ :=
      H.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter E.incoming.lt E hinitE
        hfuture old hold new ⟨hqf, hqD, hqm, hqε, hqc⟩
        (fun b => (hwinNew b).hasCanonicalWindow) hδnew hρnew
    have hradial : ∀ i b, ((records i).static b).witness.HasRadialCoordinates := by
      intro i
      cases i using Fin.lastCases with
      | last =>
        exact MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
          rfl rfl rfl rfl HEq.rfl
          (hold.1.trans hqf.symm) (hold.2.1.trans hqD.symm)
          (hold.2.2.1.trans hqm.symm) (hold.2.2.2.1.trans hqε.symm)
          new.static (records (Fin.last H.eventCount)).static hNewStatic hcoordinatesNew
      | cast i =>
        have hE : HEq ((H.appendEvent E.incoming.lt E hinitE).toHistory.event i.castSucc)
            (H.toHistory.event i) := by
          change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent)
            (H.toHistory.event i)
          exact (heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent E i.castSucc)).trans
            (H.toHistory.appendEvent_event_castSucc_heq
              E.incoming.lt E.toMetricCutCapEvent hinitE i)
        exact MetricCutCapEvent.PresentedStaticCap.hasRadialCoordinates_of_family_heq
          (H.appendEvent_stage_castSucc E.incoming.lt E hinitE i.castSucc)
          (H.appendEvent_stage_castSucc E.incoming.lt E hinitE i.succ)
          (H.appendEvent_time_castSucc E.incoming.lt E hinitE i.castSucc)
          (H.appendEvent_time_castSucc E.incoming.lt E hinitE i.succ) hE
          rfl rfl rfl rfl (old i).static (records i.castSucc).static
          (hOld i).2.2.2.2 (fun b => (hcoordinatesOld i b).1)
    have hlinked : ∀ i b, ((records i).static b).hasLinkedCanonicalWindow_C12X := by
      intro i
      cases i using Fin.lastCases with
      | last =>
        exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
          rfl rfl rfl rfl HEq.rfl
          (hold.1.trans hqf.symm) (hold.2.1.trans hqD.symm)
          (hold.2.2.1.trans hqm.symm) (hold.2.2.2.1.trans hqε.symm)
          new.static (records (Fin.last H.eventCount)).static hNewStatic hwinNew
      | cast i =>
        have hE : HEq ((H.appendEvent E.incoming.lt E hinitE).toHistory.event i.castSucc)
            (H.toHistory.event i) := by
          change HEq ((H.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent)
            (H.toHistory.event i)
          exact (heq_of_eq (H.extendCoreEventFamily_toMetricCutCapEvent E i.castSucc)).trans
            (H.toHistory.appendEvent_event_castSucc_heq
              E.incoming.lt E.toMetricCutCapEvent hinitE i)
        exact MetricCutCapEvent.PresentedStaticCap.hasLinkedCanonicalWindow_of_family_heq_C11SL
          (H.appendEvent_stage_castSucc E.incoming.lt E hinitE i.castSucc)
          (H.appendEvent_stage_castSucc E.incoming.lt E hinitE i.succ)
          (H.appendEvent_time_castSucc E.incoming.lt E hinitE i.castSucc)
          (H.appendEvent_time_castSucc E.incoming.lt E hinitE i.succ) hE
          rfl rfl rfl rfl (old i).static (records i.castSucc).static
          (hOld i).2.2.2.2 (fun b => (hcoordinatesOld i b).2)
    have hcoordinates : ∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
        ((records i).static b).hasLinkedCanonicalWindow_C12X :=
      fun i b => ⟨hradial i b, hlinked i b⟩
    have hdeep : RecordHypFar_C12X (5 / 4) (H.appendEvent E.incoming.lt E hinitE) records :=
      RecordHypFar_C12X.appendEvent_family_C12X H E.incoming.lt E hinitE old new records hOld
        hNewNominal hNewDelta hNewOrder hNewNeck hdeepOld.1 hdeepNew hradial
    exact ⟨Q, E, hinitE, A', q, new, records, hEG, hfuture, hA, ⟨hqf, hqD, hqm, hqε, hqc⟩,
      hδnew, hρnew, (fun b => (hwinNew b).hasCanonicalWindow), hfamily, hcoordinates, hdeep,
      hOld, hNewNominal, hNewDelta, hNewOrder,
      hNewNeck, hNewStatic,
      hDistance (hqε.trans_le haccHalf) (hDClosed.trans hqD.symm.le), hbfr, hctrl, hdebit⟩
  obtain ⟨a, ha, hfixed, hlower⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨p₀, δbound, ρbound, v, hpf, hpc, haccRequest, hDRequest, hmRequest,
    hδRequest, hρRequest, hrec, hδbound, hρbound, hv, ?_⟩
  let H₀ := RetainedCoreHistory.atZero P g
  let A₀ := InitialIdentification.atZero P g
  let S : Set (RetainedCoreHistory.{u}) := {K | K.horizon ≤ B ∧
    ∃ (A : InitialIdentification P g K.toHistory), A₀.IsPrefixOf A ∧
    ∃ (p : CutoffParameters)
      (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
      (∀ i : Fin K.eventCount, (K.toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
      (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
      RecordHypFar_C12X (5 / 4) K records ∧
      ∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F}
  have hzero : H₀ ∈ S := by
    refine ⟨hB.le, A₀, InitialIdentification.IsPrefixOf.refl A₀, p₀,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_,
      (fun i => Fin.elim0 i), ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      (fun i => Fin.elim0 i)⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hprefix : ∀ K ∈ S, H₀.toHistory.IsPrefixOf K.toHistory := by
    rintro K ⟨_, A, hA, _⟩
    exact hA.1
  let budget : ℝ := Nat.card (ConnectedComponents (H₀.stage 0).Carrier) +
    2 * (Real.exp ((3 / a) * B) *
      (riemannianVolumeMeasure ThreeModel (H₀.stage 0).Carrier
        (H₀.initialMetric 0) univ).toReal / v)
  have hcount : ∀ K ∈ S, K.eventCount ≤ ⌈budget⌉₊ := by
    intro K hK
    obtain ⟨hKB, A, hA, p, records, _, _, _, _, _, hdebit⟩ := hK
    obtain ⟨hfixedK, hlowerK⟩ := A.fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hlower
    have hb := K.toHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
      records ha hfixedK hlowerK hv hKB hdebit
    rw [observation_initial_budget_eq hA.1 v (3 / a) B] at hb
    exact_mod_cast hb.trans (Nat.le_ceil budget)
  have hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s), s ≤ B →
        G.flow.base.metric (K.time (Fin.last K.eventCount)) =
          K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
            (K.time (Fin.last K.eventCount)) s)
          (hi : E.incoming.flow.base.metric (K.time (Fin.last K.eventCount)) =
            K.initialMetric (Fin.last K.eventCount)),
          E.incoming = G ∧ K.appendEvent E.incoming.lt E hi ∈ S := by
    intro K hK hKB s G hs hG hsing
    obtain ⟨_, A, hA, p, records, hDistanceOld, hcontrol, hclass, hcoordinates, hdeep, hdebit⟩ := hK
    obtain ⟨Q, E, hi, A', q, _, records', hEG, _, hAA', _, _, _, _, hclass', hcoordinates',
      hdeep', _, _, _, _, _, _, hDistanceE, hbfr, hdiscard, hdebitE⟩ :=
      step K A p records hKB hclass hcoordinates hdeep s G hs hG hsing
    have hDistanceAppend : ∀ i : Fin (K.appendEvent E.incoming.lt E hi).eventCount,
        MetricCutCapEvent.HasUniformDistanceScalar
          ((K.appendEvent E.incoming.lt E hi).toHistory.event i) Cdist := by
      intro i
      cases i using Fin.lastCases with
      | last =>
        change MetricCutCapEvent.HasUniformDistanceScalar
          (K.extendCoreEventFamily E (Fin.last K.eventCount)).toMetricCutCapEvent Cdist
        rw [K.extendCoreEventFamily_toMetricCutCapEvent,
          ObservedHistory.extendEventFamily_last, ObservedHistory.extendEventFamilyLast]
        exact (MetricCutCapEvent.transport_samePresentation _ _ _ _
          E.toMetricCutCapEvent).symm.hasUniformDistanceScalar hDistanceE
      | cast i =>
        change MetricCutCapEvent.HasUniformDistanceScalar
          (K.extendCoreEventFamily E i.castSucc).toMetricCutCapEvent Cdist
        rw [K.extendCoreEventFamily_toMetricCutCapEvent,
          ObservedHistory.extendEventFamily_castSucc, ObservedHistory.extendEventFamilyCast]
        exact (MetricCutCapEvent.transport_samePresentation _ _ _ _
          (K.toHistory.event i)).symm.hasUniformDistanceScalar (hDistanceOld i)
    have hcontrolE : SurgeryEventControl E := ⟨hEG.symm ▸ hsing, hbfr, hdiscard⟩
    refine ⟨Q, E, hi, hEG, hs, A', hA.trans hAA', p.spliceAfter q K.horizon, records',
      hDistanceAppend, history_control_append K hcontrol E hi hcontrolE, hclass', hcoordinates',
      hdeep', ?_⟩
    exact K.appendEvent_compact_volume_debit E.incoming.lt E hi v hdebit hdebitE
  obtain ⟨J, hJ, heq | hclosed⟩ :=
    H₀.exists_closedSlab_extension_of_eventCount_bounded S hzero hprefix
      (fun K hK => hK.1) hcount hproduce
  · obtain ⟨hJB, A, hA, p, records, hDistance, hcontrol, hclass, hcoordinates, hdeep, hdebit⟩ := hJ
    have hncJ := hnoncollapse J A p records hJB hclass
    rw [heq] at hncJ
    exact ⟨J, A, p, records, heq, hA, hDistance, hcontrol, hclass, hcoordinates, hdeep, hncJ,
      hdebit⟩
  · obtain ⟨hJB, G, hG, _⟩ := hclosed
    obtain ⟨_, A, hA, p, records, hDistance, hcontrol, hclass, hcoordinates, hdeep, hdebit⟩ := hJ
    obtain ⟨A', hAA'⟩ := marked_closed_extension J A hJB G hG
    let K := J.extendHorizon B hJB G hG
    let records' : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p :=
      fun i => GeometricCutoffRecord.extendHorizon B hJB G hG (records i)
    have hclass' : K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records' := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hclass
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨K, A', p, records', rfl, hA.trans hAA', hDistance,
      history_control_extend J hcontrol hJB G hG, hclass', hcoordinates,
      RecordHypFar_C12X.extendHorizon_C12X B hJB G hG hdeep,
      hnoncollapse K A' p records' le_rfl hclass', hdebit⟩

/-- Forget the distance certificate from the same producer result. -/
theorem exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        (∀ i b, ((records i).static b).witness.HasRadialCoordinates ∧
          ((records i).static b).hasLinkedCanonicalWindow_C12X) ∧
        RecordHypFar_C12X (5 / 4) K records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  obtain ⟨_, _, distanceProjectionSource⟩ :=
    exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates_with_distance_scalars.{u}
  obtain ⟨fixed, recenterConstant, distanceProjectionh1⟩ := distanceProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2.1, ?_⟩
  intro P g B distanceProjectionx4
  have distanceProjectionh5 := @distanceProjectionh3 P g B distanceProjectionx4
  obtain ⟨ε, κ, distanceProjectionh6⟩ := distanceProjectionh5
  refine ⟨ε, κ, ?_⟩
  obtain ⟨distanceProjectionfield7, distanceProjectionfield8, distanceProjectionfield9,
    distanceProjectionh10⟩ := distanceProjectionh6
  refine ⟨distanceProjectionfield7, distanceProjectionfield8, distanceProjectionfield9, ?_⟩
  intro δcut ρcut εcut Dcut mcut distanceProjectionx11 distanceProjectionx12 distanceProjectionx13
    distanceProjectionx14
  have distanceProjectionh15 := @distanceProjectionh10 δcut ρcut εcut Dcut mcut
    distanceProjectionx11 distanceProjectionx12 distanceProjectionx13 distanceProjectionx14
  obtain ⟨p₀, δbound, ρbound, v, distanceProjectionh16⟩ := distanceProjectionh15
  refine ⟨p₀, δbound, ρbound, v, ?_⟩
  obtain ⟨distanceProjectionfield17, distanceProjectionfield18, distanceProjectionfield19,
    distanceProjectionfield20, distanceProjectionfield21, distanceProjectionfield22,
    distanceProjectionfield23, distanceProjectionfield24, distanceProjectionfield25,
    distanceProjectionfield26, distanceProjectionfield27, distanceProjectionh28⟩ :=
    distanceProjectionh16
  refine ⟨distanceProjectionfield17, distanceProjectionfield18, distanceProjectionfield19,
    distanceProjectionfield20, distanceProjectionfield21, distanceProjectionfield22,
    distanceProjectionfield23, distanceProjectionfield24, distanceProjectionfield25,
    distanceProjectionfield26, distanceProjectionfield27, ?_⟩
  obtain ⟨K, A, p, records, distanceProjectionh29⟩ := distanceProjectionh28
  refine ⟨K, A, p, records, ?_⟩
  obtain ⟨distanceProjectionfield30, distanceProjectionfield31, distanceProjectionh32⟩ :=
    distanceProjectionh29
  refine ⟨distanceProjectionfield30, distanceProjectionfield31, ?_⟩
  exact distanceProjectionh32.2

/-- Forget the radial certificate from the same stronger producer result. -/
theorem exists_common_scaffold_noncollapsed_geometric_observation_before_quality :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∃ ε κ : ℝ, 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  have radialProjectionSource :=
    exists_common_scaffold_noncollapsed_geometric_observation_before_quality_with_radial_coordinates.{u}
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  intro P g B radialProjectionx4
  have radialProjectionh5 := @radialProjectionh3 P g B radialProjectionx4
  obtain ⟨ε, κ, radialProjectionh6⟩ := radialProjectionh5
  refine ⟨ε, κ, ?_⟩
  obtain ⟨radialProjectionfield7, radialProjectionfield8, radialProjectionfield9,
    radialProjectionh10⟩ := radialProjectionh6
  refine ⟨radialProjectionfield7, radialProjectionfield8, radialProjectionfield9, ?_⟩
  intro δcut ρcut εcut Dcut mcut radialProjectionx11 radialProjectionx12 radialProjectionx13
    radialProjectionx14
  have radialProjectionh15 := @radialProjectionh10 δcut ρcut εcut Dcut mcut radialProjectionx11
    radialProjectionx12 radialProjectionx13 radialProjectionx14
  obtain ⟨p₀, δbound, ρbound, v, radialProjectionh16⟩ := radialProjectionh15
  refine ⟨p₀, δbound, ρbound, v, ?_⟩
  obtain ⟨radialProjectionfield17, radialProjectionfield18, radialProjectionfield19,
    radialProjectionfield20, radialProjectionfield21, radialProjectionfield22,
    radialProjectionfield23, radialProjectionfield24, radialProjectionfield25,
    radialProjectionfield26, radialProjectionfield27, radialProjectionh28⟩ := radialProjectionh16
  refine ⟨radialProjectionfield17, radialProjectionfield18, radialProjectionfield19,
    radialProjectionfield20, radialProjectionfield21, radialProjectionfield22,
    radialProjectionfield23, radialProjectionfield24, radialProjectionfield25,
    radialProjectionfield26, radialProjectionfield27, ?_⟩
  obtain ⟨K, A, p, records, radialProjectionh29⟩ := radialProjectionh28
  refine ⟨K, A, p, records, ?_⟩
  obtain ⟨radialProjectionfield30, radialProjectionfield31, radialProjectionfield32,
    radialProjectionfield33, radialProjectionh34⟩ := radialProjectionh29
  refine ⟨radialProjectionfield30, radialProjectionfield31, radialProjectionfield32,
    radialProjectionfield33, ?_⟩
  exact radialProjectionh34.2.2

/-- The requested-quality observation interface, obtained from the same common
scaffold callback with its already selected noncollapse radius and coefficient. -/
theorem exists_common_scaffold_noncollapsed_geometric_observation :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ), 0 < B →
    ∀ (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ),
      0 < δcut → 0 < ρcut → 0 < εcut → 0 < Dcut →
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      p₀.fixed = fixed ∧ p₀.recenterConstant = recenterConstant ∧
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  obtain ⟨fixed, c, hc, make⟩ :=
    exists_common_scaffold_noncollapsed_geometric_observation_before_quality.{u}
  refine ⟨fixed, c, hc, ?_⟩
  intro P g B hB δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨ε, κ, hε, hε11, hκ, make⟩ := make P g B hB
  obtain ⟨p₀, δbound, ρbound, v, hpf, hpc, hacc, hD, hm, hδcut', hρcut', hrec,
    hδ, hρ, hv, hK⟩ := make δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  exact ⟨p₀, δbound, ρbound, ε, κ, v, hpf, hpc, hacc, hD, hm,
    hδcut', hρcut', hrec, hδ, hρ, hε, hε11, hκ, hv, hK⟩

end GC.GeneralFlow
