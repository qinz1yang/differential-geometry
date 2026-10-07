import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicyReserveQuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalRequests
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedEventWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingStageWeightedRestart

/-!
# S-CH11-FIX12 patched-at-path `PreparedSpatialClosedEventRestart`

来源：donor `PreparedSpatialClosedEventRestart.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本文件只有 elaboration 层面修补（no statement / definition /
proof idea altered）。
patched-at-path：下游 `PreparedSpatialPositivePoleWeightedPropagation` /
`PreparedSpatialPhysicalVolumeEvent` 对它做
`open private closed_event_weighted_restart_of_fixed_saved_data … from` 原路径，故不做 PortC11P + shim
（原路径文本 = 本文件）：
* **heartbeat exception 800000, lead 04:3x（statement size）**：主定理
  `exists_prepared_spatial_physical_surgery_with_closed_event_weighted_restart` 的陈述单独 110000–160000
  heartbeats（证明换 `sorry` 后 `160000` 过、`110000` 不过），整条（陈述 + ~620 行证明）实测
  `400000` 不过、`600000` 不过、`800000` 过 → 该声明前加 `set_option maxHeartbeats 800000 in`
  （逐声明、不整文件；超出 400000 的一般上限，lead 04:3x 单独批准）；
* **statement 级 "unknown free variable `_fvar.N`"（3 个 private 定理，各报在定理名处）**：根因在各陈述
  最后一个合取 `∀ w ∈ Icc k b, m w ≤ Real.exp (Cweight * (w ^ 2 - k ^ 2) / r ^ 2 + 32 * (w - k) / r)
  * (w / k) * m k ∧ m w ≤ 2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r)`：在
  `let Cweight := …` 之下，未标注的幂次 `k ^ 2` / `r ^ 2` 触发 elaborator 的 fvar 泄漏（二分到该合取；`w ^ 2` 单独、
  `Cweight * (w - k)` 单独都没事，`k ^ 2` 带 `Cweight` 才报）→ 把这两处表达式的指数写成
  `(2 : ℕ)`（同一项，`Monoid.npow` 的默认实例就是 ℕ）；全文同形 13 处一并改；
* 裸名 `normalizedDatum` / `SpatialCanonicalWitness` 在本树 unknown identifier（`open` 不传递）→ 补
  `open DifferentialGeometry.Geometry.Neck` 与 `open …Perelman.CanonicalNeighborhood.FiniteHorn`；
* 2 处 `open private … ObservedHistory.exists_old_seed_and_endpoint_outside_retained_cap_windows` /
  `…traced_weighted_minimum_restarts_on_fixed_incoming_stage` 之后，调用处 `ObservedHistory.xxx`（经
  `open …Topology`）在本树 "Unknown constant" → 写 opened private 全名（FIX3 共性）；
* `hmAt` 的 `dsimp only [m]` 之后目标里是 let 变量 `M`，`rw [hMk]` 找不到 → `dsimp only [m, M]`；
* 3 处相邻 `intro` 合并（introMerge 风格 linter）、`convert … using 1 <;> ring` → 换行 `ring`
  （unnecessarySeqFocus）、24 个 unused binder（`hf` / `hl` / `hle` / `hstart`）加 `_`；
* 遗留（info 级，非 warning）：`ring` 失败后回落 `ring_nf` 的 "Try this: ring_nf" 提示 1 条（donor 原样）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

open private DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_old_seed_and_endpoint_outside_retained_cap_windows from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventWindowEndpointPair

open private DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.traced_weighted_minimum_restarts_on_fixed_incoming_stage from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IncomingStageWeightedRestart

namespace GC.GeneralFlow
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- The same saved callbacks and the same selected raw family pass one
positive-clock event. This bridge makes no new class, request, history or flow choice. -/
private theorem closed_event_weighted_restart_of_query_support
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (constants : ClosedBirthConstants) (pBase : CutoffParameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hRequest : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2)
    (hWindow : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ pBase.recenterConstant →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      )
    (S : PreparedSpatialChain pBase constants P g)
    (radii : ℕ → ℝ)
    (hRadiiPos : ∀ n : ℕ, 0 < radii n)
    (hRadiiNext : ∀ n : ℕ, (S.state (n + 1)).radius = radii n) :
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.2.1
    ∀ W : ∀ n : ℕ, PreparedSpatialStepRetention
      (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
      (εcut n) (Dcut n) (mcut n),
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q)
      (block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ),
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      q.recenterConstant ≤ pBase.recenterConstant →
      (∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount),
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift
        ∀ T : ℝ, T ∈ Icc s (2 * s) → (S.state (m + 1)).radius ≤ q.neckRadius T) →
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        let m := block n j;
        m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)
      ) →
      (
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 / 2 → 2 * r ^ 2 < t.val →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest →
      ∀ (first : Fin (H.eventCount + 1)) (_hle : first ≤ H.activeStage t),
        t.val - v ^ 2 ∈ H.stageDomain first →
      let nodeA : Fin H.eventCount → ℝ := fun i =>
        preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n i)) *
          Real.sqrt (2 * (3 : ℝ) ^ (block n i))
      let nodeE : Fin H.eventCount → ℝ := fun i => Real.sqrt ((3 : ℝ) ^ (block n i))
      let nodeR : Fin H.eventCount → ℝ := fun i => radii (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (radii (block n i) ^ 2)⁻¹
      let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.succ) (_hl : i.succ ≤ H.activeStage t)
        (_hstart : t.val - v ^ 2 ≤ H.time i.succ),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records n j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i
      ) →
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.isParabolicallyRmControlledBall t p r →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ r →
        q.neckRadius t.val / 100 ≤ rhoTest →
        (∀ s ∈ Icc (t.val / 2) t.val,
          q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r →
      (
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, ((records n) j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = (((records n) i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0
      ) →
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w *
          Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ (2 : ℕ) - k ^ (2 : ℕ)) / r ^ (2 : ℕ) + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r)) := by
  classical
  intro εcut Dcut mcut W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n H t p x r A rhoTest hr hA hT hseed htest hSeedScale hTestScale
    hAccuracy aSeed hSeedTime hSeedClock seedTrace htrace hSupportAt a k b ha hak hkb hbhalf
    i hl hevent hentry hclockEnd Cweight Dweight M m f hpreceding
  have hk : 0 < k := ha.trans hak
  have hb : 0 < b := hk.trans hkb
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hkSq : k ^ 2 < b ^ 2 := pow_lt_pow_left₀ hkb hk.le two_ne_zero
  have hkhalf : k ^ 2 < r ^ 2 / 2 := hkSq.trans_le hbhalf
  have hC : 0 ≤ Cweight := by
    apply DifferentialGeometry.Analysis.SingularBarrier.bound_nonneg
    nlinarith only [hA, sq_nonneg DifferentialGeometry.Analysis.CutoffProfile.derivBound]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkr : k / r ≤ 1 / Real.sqrt 2 := by
    apply (div_le_div_iff₀ hr hsqrt).mpr
    have hsq : (k * Real.sqrt 2) ^ 2 ≤ r ^ 2 := by
      rw [mul_pow, hsqrt2]
      nlinarith only [hkhalf.le]
    simpa only [one_mul] using
      (sq_le_sq₀ (mul_nonneg hk.le hsqrt.le) hr.le).mp hsq
  have hquad : Cweight * k ^ 2 / r ^ 2 ≤ Cweight / 2 := by
    apply (div_le_iff₀ hr2).mpr
    have hh := mul_le_mul_of_nonneg_left hkhalf.le hC
    nlinarith only [hh]
  have hlin : 32 * k / r ≤ 32 / Real.sqrt 2 := by
    simpa only [← mul_div_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hkr (by norm_num : (0 : ℝ) ≤ 32)
  have hchi : Cweight * k ^ 2 / r ^ 2 + 32 * k / r ≤
      Cweight / 2 + 32 / Real.sqrt 2 := add_le_add hquad hlin
  have hDthree : 3 ≤ Dweight := by
    have hrootle : Real.sqrt 2 ≤ 2 := by nlinarith only [hsqrt2, hsqrt.le]
    have hlinlo : 2 ≤ 32 / Real.sqrt 2 :=
      (le_div_iff₀ hsqrt).mpr (by linarith only [hrootle])
    have he := Real.add_one_le_exp (Cweight / 2 + 32 / Real.sqrt 2)
    dsimp only [Dweight]
    linarith only [he, hC, hlinlo]
  let upper : ℝ → ℝ := fun w => 2 * r * w *
    Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r)
  have hupper : ContinuousAt upper k := by
    dsimp only [upper]
    fun_prop
  have hbudget : upper k ≤ 2 * r * k * Dweight := by
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * r * k)
    exact (Real.exp_le_exp.mpr hchi).trans (by dsimp only [Dweight]; linarith)
  obtain ⟨hfixed, hscalarInitial⟩ := hInitialData n
  obtain ⟨_hfPost, qEnd, L, mEvent, hMk, hWmin, hMinimum, hCost,
    hInside, hMargin, hmPositive, hmUpper, _hmBudget, hLbound, _hLstrict⟩ :=
    H.exists_closed_event_traced_weighted_minimum_of_preceding_stage_bound q
      (records n) a₀ ha₀ hfixed hscalarInitial t p x r A Dweight a k hr ha hak
      hkhalf.le hT aSeed hSeedTime hSeedClock seedTrace i hl hevent hentry
      upper hupper hbudget hpreceding
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower (records n) ha₀
    hfixed hscalarInitial).1
  have hscalar (j : Fin (H.eventCount + 1)) (s : ℝ) (hs : s ∈ H.stageDomain j)
      (y : (H.stage j).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j s) y := by
    have htime := (H.stageDomain_subset j hs).1
    have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    exact (show -(3 / a₀) ≤ -3 / (a₀ + s) by
      simpa only [neg_div] using neg_le_neg hratio).trans (hHI j s hs y).2
  have hupperDomain : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupperDomain,
      H.le_stageEndTime_of_mem_stageDomain hupperDomain⟩
  have hpast : t.val - k ^ 2 ∈ H.stageDomain i.succ := by
    rw [hevent]
    exact (H.mem_stageDomain_iff (H.stageTime i.succ) i.succ).mpr
      (H.activeStage_stageTime i.succ)
  have hscalarClock (j : H.StageInterval i.succ (H.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val k j.val)) (y : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) y :=
    hscalar j.val _ (H.mapsTo_regularizedStage_Ioo t.val 0 k j.val hs) y
  have hCostC1 := H.regularizedCost_eq_regularizedC1Cost i.succ (H.activeStage t) hl
    t.val (3 / a₀) 0 k hupperDomain hscalarClock x qEnd
  have hfiniteC1 : H.regularizedC1Cost i.succ (H.activeStage t) hl t.val 0 k x qEnd ≠ ⊤ := by
    rw [← hCostC1, hCost]
    exact WithTop.coe_ne_top
  obtain ⟨gamma, hC1, hInt, hPole, hEnd, hNodes, hSumC1⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top i.succ (H.activeStage t) hl
      t.val (3 / a₀) 0 k hupperDomain hscalarClock x qEnd hfiniteC1
  have hAC (j : H.StageInterval i.succ (H.activeStage t)) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val) :=
    Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hC1 j).contMDiffOn
  have hSum : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L := by
    apply WithTop.coe_injective
    exact hSumC1.trans (hCostC1.symm.trans hCost)
  have hAction : H.regularizedExtendedAction i.succ (H.activeStage t)
      t.val (3 / a₀) 0 k gamma = (L : WithTop ℝ) := by
    rw [H.regularizedExtendedAction_eq_sum_action i.succ (H.activeStage t)
      (le_refl 0) hk.le hupperIcc hpast gamma hInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hscalarClock j s hs (gamma j s)), hSum]
  let nodeA : Fin H.eventCount → ℝ := fun j =>
    preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n j)) *
      Real.sqrt (2 * (3 : ℝ) ^ (block n j))
  let nodeE : Fin H.eventCount → ℝ := fun j => Real.sqrt ((3 : ℝ) ^ (block n j))
  let nodeR : Fin H.eventCount → ℝ := fun j => radii (block n j) / 100
  let nodeQ : Fin H.eventCount → ℝ := fun j => (radii (block n j) ^ 2)⁻¹
  let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
  obtain ⟨hDataK, hFitK⟩ := hPhysical n t x r A k rhoTest hr hA hk.le hkhalf.le hT
    hAccuracy htest hTestScale i.succ hl hpast
  obtain ⟨hE, hR, hQ, hRho, hkE, hPoleBall, hDelta, hNeck,
    hLaterDelta, hDerivative, _hSomeCaps⟩ := hDataK i le_rfl hl hevent.le
  have hFitNode : Dweight * r ≤ nodeA i := hFitK i le_rfl hl hevent.le
  let blockIndex := block n i
  obtain ⟨_hBlockLe, nativeIndex, _hCountLo, _hCountHi, hIndex, hBirth,
    _hBirthBand, _hPresentation, _hNativeDelta, hRawRadius, hRawOrder,
    hRawAccuracy, hCaps⟩ := hRaw n i
  choose cNative caps hCapsData using hCaps
  let Dcap := (W blockIndex).fineParameters.modelRadius
  let ncap := (W blockIndex).fineParameters.modelOrder
  let εcap := (W blockIndex).fineParameters.modelAccuracy
  have hCanonical (c : (H.event i).RetainedBoundaryIndex) : (caps c).hasCanonicalWindow :=
    (hCapsData c).2.1
  have hCapIdentity (c : (H.event i).RetainedBoundaryIndex) :
      (caps c).neck.scale = ((records n i).static c).neck.scale ∧
      HEq (cNative c) c ∧
      HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static (cNative c)).neck ∧
      HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static (cNative c)).witness ∧
      HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static (cNative c)).inclusion ∧
      (caps c).witness.windowMetric =
        (((W blockIndex).fineRecords nativeIndex).static (cNative c)).witness.windowMetric ∧
      (∀ z : standardCapWindow Dcap,
        HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static (cNative c)).window z)) ∧
      (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
        ((records n i).static c).inclusion (((records n i).static c).witness.cap z)) := by
    obtain ⟨hLabel, _hCanonical, _hDelta, _hOrder, hNeck, hWitness,
      _hOutput, _hMetric, hInclusion, _hCap, _hRetained, _hCollapse,
      hWindowMetric, hWindowPoints, hScale, hRecordCap, _hRemaining⟩ := hCapsData c
    exact ⟨hScale, hLabel, hNeck, hWitness, hInclusion, hWindowMetric, hWindowPoints, hRecordCap⟩
  let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
  obtain ⟨_hεpos, hεsmall, _hDpos, hDlarge, _hOrderFour, _hδpos⟩ :=
    hRequest (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i) hE hR hQ hRho
  have hReq : εcut blockIndex = req.1 ∧ Dcut blockIndex = req.2.1 ∧
      mcut blockIndex = req.2.2.1 := by
    simpa only [εcut, Dcut, mcut, preparedSpatialPhysicalQualityRequest,
      ite_eq_left (hRadiiPos blockIndex), req, nodeA, nodeE, nodeR, nodeQ, nodeRho, blockIndex]
      using (show εcut blockIndex = εcut blockIndex ∧ Dcut blockIndex = Dcut blockIndex ∧
        mcut blockIndex = mcut blockIndex from ⟨rfl, rfl, rfl⟩)
  have hCapRadius : req.2.1 ≤ Dcap := hReq.2.1.symm.le.trans hRawRadius
  have hCapOrder : req.2.2.1 ≤ ncap := hReq.2.2.symm.le.trans hRawOrder
  have hCapAccuracy : εcap ≤ req.1 := hRawAccuracy.trans hReq.1.le
  have hCapSmall : εcap ≤ 1 / 2 := hCapAccuracy.trans hεsmall
  have hCapLarge : StandardCap.transitionEnd + 10 < Dcap := hDlarge.trans_le hCapRadius
  have hBirthLe : H.time i.succ ≤ t.val :=
    (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
  have hRecent : t.val / 2 < H.time i.succ := by
    rw [← hevent]
    nlinarith only [hkhalf.le, hT]
  have hForward := hRadiusForward blockIndex nativeIndex
  have hReserve : radii blockIndex ≤ q.neckRadius t.val := by
    rw [← hRadiiNext blockIndex]
    apply hForward t.val
    rw [← hBirth]
    exact ⟨hBirthLe, by linarith only [hRecent]⟩
  have hSeedTest : nodeR i ≤ r :=
    (div_le_div_of_nonneg_right hReserve (by norm_num : (0 : ℝ) ≤ 100)).trans hSeedScale
  have hSeedBudget : 3 * r ≤ nodeA i :=
    (mul_le_mul_of_nonneg_right hDthree hr.le).trans hFitNode
  have hEndpoint (pole : (H.stageAt t).Carrier)
      (hball : H.isParabolicallyRmControlledBall t pole (nodeR i))
      (Lcurve : ℝ) (qCurve : (H.stage i.succ).Carrier)
      (hCurve : Lcurve ∈ H.regularizedC1ActionValues i.succ (H.activeStage t) hl
        t.val 0 k pole qCurve) (hBudget : Lcurve ≤ nodeA i)
      (c : (H.event i).RetainedBoundaryIndex) :
      qCurve ∉ (caps c).window ''
        {z : standardCapWindow Dcap | ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
    obtain ⟨_hu, _huv, _hupper, _hpast, curve, hCurveC1, hCurveInt,
      hCurvePole, hCurveEnd, hCurveNodes, hCurveSum⟩ := hCurve
    have hsmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
        H.stageRegularizedAction j.val t.val (curve j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ≤ nodeA i := by
      simpa only [hCurveSum] using hBudget
    have hexclude := hWindow (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
      hE hR hQ hRho H q (records n) hfixed hscalarInitial t i.succ hl k hk.le hkE
      hpast pole hball curve hCurveC1 hCurveInt hCurvePole hCurveNodes hsmall
      i le_rfl hl hevent.le hrecenter hDelta hNeck hLaterDelta hDerivative
      c Dcap εcap ncap (caps c) hCapRadius hCapOrder hCapAccuracy (hCanonical c)
      (hCapIdentity c).1
    have hsqrtClock : Real.sqrt (t.val - H.time i.succ) = k := by
      have hclock : t.val - H.time i.succ = k ^ 2 := by linarith only [hevent]
      rw [hclock, Real.sqrt_sq hk.le]
    simpa only [hsqrtClock, hCurveEnd] using hexclude
  have hsmallGamma : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t.val (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ≤ nodeA i := by
    rw [hSum]
    exact hLbound.trans (by nlinarith only [hFitNode, hr.le])
  obtain ⟨hfSeed, O, z, hOin, hOout, hzout, hOoutside, hzoutside⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_old_seed_and_endpoint_outside_retained_cap_windows
      H q (records n)
      t p x r k (nodeA i) (nodeR i) hr hk hkhalf.le hseed hR hSeedTest hPoleBall
      hSeedBudget aSeed hSeedTime hSeedClock seedTrace htrace i hl hevent caps hCanonical
      hEndpoint gamma hC1 hInt hPole hNodes hsmallGamma
  have hzEnd : (H.event i).oldOutput z = qEnd := hzout.trans hEnd
  have hpostMetric : H.stageMetric i.succ (t.val - k ^ 2) = (H.event i).outputMetric := by
    rw [hevent, H.stageMetric_initial]
    exact (H.event_output i).symm
  have hInsideEvent : riemannianEDistOf (H.event i).outputMetric
      ((H.event i).oldOutput O) ((H.event i).oldOutput z) <
      ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) := by
    simpa only [hpostMetric, hOout, hzEnd] using hInside
  have hCostEvent : H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x
      ((H.event i).oldOutput z) = (L : WithTop ℝ) := by
    simpa only [hzEnd] using hCost
  have hContact : H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x
      ((H.event i).oldOutput O) ((H.event i).oldOutput z) = M k := by
    simpa only [hOout, hzEnd] using hWmin.trans hMk.symm
  obtain ⟨hFiniteK, hmKpos, _hIncoming, hUpperSemi⟩ :=
    H.traced_physical_weighted_minimum_right_control_of_event_window_data q (records n)
      a₀ ha₀ hfixed hscalarInitial t p x r A k hr hk hkhalf hT aSeed hSeedTime
      hSeedClock seedTrace i hfSeed hl hevent caps hCanonical hCapSmall hCapLarge
      O z hOin hOoutside hzoutside L hInsideEvent hCostEvent hContact
  have hIncomingClock : t.val - b ^ 2 ∈ Ioo (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [H.stageEndTime_castSucc, ← hevent]
    exact ⟨hclockEnd, by linarith only [hkSq]⟩
  obtain ⟨hDataB, hFitB⟩ := hPhysical n t x r A b rhoTest hr hA hb.le hbhalf hT
    hAccuracy htest hTestScale i.castSucc (i.castSucc_le_succ.trans hl)
    (H.mem_stageDomain_of_mem_Ioo hIncomingClock)
  have hStart (j : Fin H.eventCount) (hij : i.castSucc ≤ j.castSucc) :
      t.val - b ^ 2 ≤ H.time j.succ := by
    have hindices : i.succ ≤ j.succ := by
      change i.val + 1 ≤ j.val + 1
      change i.val ≤ j.val at hij
      exact Nat.add_le_add_right hij 1
    exact hIncomingClock.2.le.trans
      (by simpa only [H.stageEndTime_castSucc] using H.time_strictMono.monotone hindices)
  have hmAt : m k = mEvent := by
    dsimp only [m, M]
    rw [hMk, WithTop.untopD_coe]
  have hNormalized : f k ≤ 2 * r := by
    have hExpCancel : Real.exp (-Cweight * k ^ 2 / r ^ 2 - 32 * k / r) *
        Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring
    dsimp only [f]
    rw [hmAt]
    apply (div_le_iff₀ hk).mpr
    calc
      Real.exp (-Cweight * k ^ 2 / r ^ 2 - 32 * k / r) * mEvent ≤
          Real.exp (-Cweight * k ^ 2 / r ^ 2 - 32 * k / r) * upper k :=
        mul_le_mul_of_nonneg_left hmUpper (Real.exp_pos _).le
      _ = 2 * r * k := by
        dsimp only [upper]
        calc
          _ = (2 * r * k) * (Real.exp (-Cweight * k ^ 2 / r ^ 2 - 32 * k / r) *
            Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r)) := by ring
          _ = _ := by rw [hExpCancel, mul_one]
  have hRestart :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.traced_weighted_minimum_restarts_on_fixed_incoming_stage
    a₀ constants.Ctime ha₀ request H q (records n)
    hfixed hscalarInitial t p x r A hr hA hT aSeed hSeedTime
    hSeedClock seedTrace hSupportAt k b hk hkb hbhalf i hfSeed hl hevent caps hCanonical
    hCapSmall hCapLarge O z hOin hOoutside hzoutside L hInsideEvent hCostEvent hContact
    hclockEnd nodeA nodeE nodeR nodeQ nodeRho
    (fun j hf hj => hDataB j (hf.trans j.castSucc_le_succ) hj (hStart j hf))
    (fun j hf hj => hFitB j (hf.trans j.castSucc_le_succ) hj (hStart j hf)) hNormalized
  refine ⟨hfSeed, qEnd, L, mEvent, hMk, hWmin, hMinimum, hCost, hInside,
    hMargin, hmPositive, hmUpper, hLbound, gamma, hC1, hAC, hInt, hPole, hEnd,
    hNodes, hSum, hAction, nativeIndex, hIndex, hBirth, caps, hCanonical,
    hCapSmall, hCapLarge, (fun c => (hCapIdentity c).1), ?_, O, z, hOin,
    hOout, hzEnd, hOoutside, hzoutside, hFiniteK, hmKpos, hNormalized,
    hUpperSemi Cweight, hRestart.1, hRestart.2.1, hRestart.2.2⟩
  intro c
  exact ⟨cNative c, (hCapIdentity c).2⟩

private theorem closed_event_weighted_restart_of_fixed_saved_data
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (constants : ClosedBirthConstants) (pBase : CutoffParameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hRequest : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2)
    (hWindow : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ pBase.recenterConstant →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      )
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ pBase.recenterConstant →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0
    )
    (S : PreparedSpatialChain pBase constants P g)
    (radii : ℕ → ℝ)
    (hRadiiPos : ∀ n : ℕ, 0 < radii n)
    (hRadiiNext : ∀ n : ℕ, (S.state (n + 1)).radius = radii n) :
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.2.1
    ∀ W : ∀ n : ℕ, PreparedSpatialStepRetention
      (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
      (εcut n) (Dcut n) (mcut n),
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q)
      (block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ),
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      q.recenterConstant ≤ pBase.recenterConstant →
      (∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount),
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift
        ∀ T : ℝ, T ∈ Icc s (2 * s) → (S.state (m + 1)).radius ≤ q.neckRadius T) →
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        let m := block n j;
        m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)
      ) →
      (
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 / 2 → 2 * r ^ 2 < t.val →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest →
      ∀ (first : Fin (H.eventCount + 1)) (_hle : first ≤ H.activeStage t),
        t.val - v ^ 2 ∈ H.stageDomain first →
      let nodeA : Fin H.eventCount → ℝ := fun i =>
        preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n i)) *
          Real.sqrt (2 * (3 : ℝ) ^ (block n i))
      let nodeE : Fin H.eventCount → ℝ := fun i => Real.sqrt ((3 : ℝ) ^ (block n i))
      let nodeR : Fin H.eventCount → ℝ := fun i => radii (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (radii (block n i) ^ 2)⁻¹
      let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.succ) (_hl : i.succ ≤ H.activeStage t)
        (_hstart : t.val - v ^ 2 ≤ H.time i.succ),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records n j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i
      ) →
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.time (H.activeStage t) < t.val →
        H.isParabolicallyRmControlledBall t p r →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ r →
        q.neckRadius t.val / 100 ≤ rhoTest →
        (∀ s ∈ Icc (t.val / 2) t.val,
          q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r →
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w *
          Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ (2 : ℕ) - k ^ (2 : ℕ)) / r ^ (2 : ℕ) + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r)) := by
  intro εcut Dcut mcut W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n H t p x r A rhoTest hr hA hT hpole hseed htest hSeedScale hTestScale
    hAccuracy aSeed hSeedTime hSeedClock seedTrace htrace
  refine closed_event_weighted_restart_of_query_support
    P g constants pBase a₀ ha₀ request hRequest hWindow S radii hRadiiPos hRadiiNext
    W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n t p x r A rhoTest hr hA hT hseed htest hSeedScale hTestScale hAccuracy
    aSeed hSeedTime hSeedClock seedTrace htrace ?_
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H q (records n) hrecenter (hInitialData n).1 (hInitialData n).2
    t p x r A hr hA hT hseed aSeed hSeedTime hSeedClock seedTrace
    a has hat v hv hhalf hclock hpole hpast

private theorem closed_event_weighted_restart_at_closed_poles_of_fixed_saved_data
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (constants : ClosedBirthConstants) (pBase : CutoffParameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (hRequest : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2)
    (hWindow : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ pBase.recenterConstant →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      )
    (hSupport :
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ pBase.recenterConstant →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0
    )
    (S : PreparedSpatialChain pBase constants P g)
    (radii : ℕ → ℝ)
    (hRadiiPos : ∀ n : ℕ, 0 < radii n)
    (hRadiiNext : ∀ n : ℕ, (S.state (n + 1)).radius = radii n) :
    let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).1
    let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.1
    let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.2.1
    ∀ W : ∀ n : ℕ, PreparedSpatialStepRetention
      (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
      (εcut n) (Dcut n) (mcut n),
    ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q)
      (block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ),
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      q.recenterConstant ≤ pBase.recenterConstant →
      (∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount),
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift
        ∀ T : ℝ, T ∈ Icc s (2 * s) → (S.state (m + 1)).radius ≤ q.neckRadius T) →
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        let m := block n j;
        m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)
      ) →
      (
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 / 2 → 2 * r ^ 2 < t.val →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest →
      ∀ (first : Fin (H.eventCount + 1)) (_hle : first ≤ H.activeStage t),
        t.val - v ^ 2 ∈ H.stageDomain first →
      let nodeA : Fin H.eventCount → ℝ := fun i =>
        preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n i)) *
          Real.sqrt (2 * (3 : ℝ) ^ (block n i))
      let nodeE : Fin H.eventCount → ℝ := fun i => Real.sqrt ((3 : ℝ) ^ (block n i))
      let nodeR : Fin H.eventCount → ℝ := fun i => radii (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (radii (block n i) ^ 2)⁻¹
      let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.succ) (_hl : i.succ ≤ H.activeStage t)
        (_hstart : t.val - v ^ 2 ≤ H.time i.succ),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records n j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i
      ) →
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
          H.isParabolicallyRmControlledBall t p r →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ r →
        q.neckRadius t.val / 100 ≤ rhoTest →
        (∀ s ∈ Icc (t.val / 2) t.val,
          q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r →
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w *
          Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ (2 : ℕ) - k ^ (2 : ℕ)) / r ^ (2 : ℕ) + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r)) := by
  intro εcut Dcut mcut W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n H t p x r A rhoTest hr hA hT hseed htest hSeedScale hTestScale
    hAccuracy aSeed hSeedTime hSeedClock seedTrace htrace
  refine closed_event_weighted_restart_of_query_support
    P g constants pBase a₀ ha₀ request hRequest hWindow S radii hRadiiPos hRadiiNext
    W F q records block hInitialData hrecenter hRadiusForward hRaw hPhysical
    n t p x r A rhoTest hr hA hT hseed htest hSeedScale hTestScale hAccuracy
    aSeed hSeedTime hSeedClock seedTrace htrace ?_
  intro _C _D a has hat v hv hhalf hclock hpast
  exact hSupport H q (records n) hrecenter (hInitialData n).1 (hInitialData n).2
    t p x r A hr hA hT hseed aSeed hSeedTime hSeedClock seedTrace
    a has hat v hv hhalf hclock hpast

set_option maxHeartbeats 800000 in
-- heartbeat exception 800000, lead 04:3x (statement 110k-160k alone; whole 600k-800k)
/-- One saved request and one selected surgery pass a genuine weighted minimum
across a closed positive-clock event and restart on the incoming open stage. -/
theorem exists_prepared_spatial_physical_surgery_with_closed_event_weighted_restart
    (Dstar εReserve : ℝ) (hDstar : 0 < Dstar) (hεReserve : 0 < εReserve) :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧ ∃ constants : ClosedBirthConstants,
    ∀ (P : OrientedThreeStage.{u}) (g : P.Metric),
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
          ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
    ∀ cMax : ℝ, 0 < cMax →
    ∃ (pBase : CutoffParameters) (base : PreparedSpatialState pBase constants P g 0 1),
      base.history = RetainedCoreHistory.atZero P g ∧
      HEq base.initial (InitialIdentification.atZero P g) ∧
      base.shift = 0 ∧ base.offset = 0 ∧ base.radius ≤ 1 ∧
      (∀ t : ℝ, base.parameters.neckRadius t = base.radius) ∧
      base.radius * Real.sqrt base.prepared.Qall ≤ 100 * cMax ∧
      base.prepared.HasReserveQuality Dstar εReserve ∧
      base.DistanceData Cdist ∧
    ∃ request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ,
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
        0 < req.1 ∧ req.1 ≤ 1 / 2 ∧ 0 < req.2.1 ∧ (StandardCap.transitionEnd + 10) < req.2.1 ∧
          4 ≤ req.2.2.1 ∧ 0 < req.2.2.2) ∧
      (∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
        let req := request Aact E rTerm qDeriv ρ
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ pBase.recenterConstant →
      parameters.delta (H.time i.succ) ≤ req.2.2.2 →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ req.2.2.2) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        req.2.1 ≤ Dbig → req.2.2.1 ≤ m → ζ ≤ req.1 → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ (StandardCap.transitionEnd + 10)}
      ) ∧
    (
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      parameters.recenterConstant ≤ pBase.recenterConstant →
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier) (r A : ℝ),
      0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
      H.isParabolicallyRmControlledBall t p r →
    ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
      (aSeed : ℝ) = t.val - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p,
    let C := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (C / 2 + 32 / Real.sqrt 2) + 1
    ∀ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t) (v : ℝ),
      0 < v → v ^ 2 ≤ r ^ 2 / 2 → (a : ℝ) = t.val - v ^ 2 →
      H.time (H.activeStage t) < t.val →
      t.val - v ^ 2 ∈ Ioo (H.time (H.activeStage a)) (H.stageEndTime (H.activeStage a)) →
    let first := H.activeStage a
    let last := H.activeStage t
    let hle := H.activeStage_mono hat
    let O := seedTrace.point first (H.activeStage_mono has) hle
    ∀ (nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ),
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        parameters.delta (H.time i.succ) ≤ req.2.2.2 ∧
        parameters.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records i).static b).neck.scale)) →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last →
        D * r ≤ nodeA i) →
    ∀ q : (H.stage first).Carrier,
      (∀ y : (H.stage first).Carrier,
        H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
          H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O y) →
      H.physicalWeightedCost first last hle t.val (3 / a₀) r A v x O q ≤
        ((2 * r * v * D : ℝ) : WithTop ℝ) →
    ∃ L : ℝ,
      H.regularizedCost first last hle t.val (3 / a₀) 0 v x q = (L : WithTop ℝ) ∧
      L ≤ (D - 1) * r ∧
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ last → L < nodeA i) ∧
      riemannianEDistOf (H.stageMetric first (t.val - v ^ 2)) O q <
        ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ 0 = x ∧
    ∃ hEnd : gamma ⟨first, le_rfl, hle⟩ v = q,
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) ∧
      H.regularizedExtendedAction first last t.val (3 / a₀) 0 v gamma = (L : WithTop ℝ) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        (H.event i).RegularCrossing
          (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)))
          (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time i.succ)))) ∧
      let g := H.stageMetric first (t.val - v ^ 2)
      let V : TangentSpace ThreeModel q :=
        Eq.mp (congrArg (TangentSpace ThreeModel) hEnd)
          (lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v)
      let R := metricScalarAt g q
      ∃ (U : Set ((H.stage first).Carrier × ℝ)) (F : (H.stage first).Carrier × ℝ → ℝ),
        IsOpen U ∧ (q, v) ∈ U ∧
        ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧ F (q, v) = L ∧
        (∀ z ∈ U, H.regularizedCost first last hle t.val (3 / a₀) 0 z.2 x z.1 ≤
          (F z : WithTop ℝ)) ∧
        gradientFun g (fun y => F (y, v)) q = V ∧
        HasDerivAt (fun w => F (q, w))
          (2 * v ^ 2 * R - (1 / 2 : ℝ) * g.inner q V V) v ∧
        laplacian (LeviCivita g) g (fun y => F (y, v)) q <
          3 / v - v * R - L / (2 * v ^ 2) + g.inner q V V / (4 * v) + 1 / (2 * v) ∧
        (∀ᶠ y in 𝓝 q, H.regularizedCost first last hle t.val (3 / a₀) 0 v x y ≠ ⊤) ∧
        let t0 := t.val - v ^ 2
        let actualArg : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          (riemannianEDistOf (H.stageMetric first s) O y).toReal / r -
            A * (1 - 2 * ((t.val - s) / r ^ 2))
        let actualWeighted : ℝ → (H.stage first).Carrier → ℝ := fun s y =>
          DifferentialGeometry.Analysis.SingularBarrier.value (actualArg s y) *
          (2 * Real.sqrt (t.val - s) *
            (H.regularizedCost first last hle t.val (3 / a₀) 0
              (Real.sqrt (t.val - s)) x y).untopD 0 + 2 * r * Real.sqrt (t.val - s))
        IsLocalMin (actualWeighted t0) q ∧
        ∃ W : (H.stage first).Carrier × ℝ → ℝ,
          W (q, t0) = actualWeighted t0 q ∧
          (∀ᶠ y in 𝓝 q, actualWeighted t0 y ≤ W (y, t0)) ∧
          (∀ᶠ s in 𝓝 t0, actualWeighted s q ≤ W (q, s)) ∧
          IsLocalMin (fun y => W (y, t0)) q ∧
          DifferentiableAt ℝ (fun s => W (q, s)) t0 ∧
          0 ≤ laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
          -(C / r ^ 2) * actualWeighted t0 q -
            (7 + r / v) * DifferentialGeometry.Analysis.SingularBarrier.value (actualArg t0 q) ≤
            deriv (fun s => W (q, s)) t0 -
              laplacian (LeviCivita g) g (fun y => W (y, t0)) q ∧
        let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
        let Mstage : ℝ → WithTop ℝ := fun w => sInf (Set.range
          (H.physicalWeightedCost first last hle t.val (3 / a₀) r A w x O))
        let m : ℝ → ℝ := fun w => (M w).untopD 0
        let f : ℝ → ℝ := fun w =>
          Real.exp (-C * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
        (∀ᶠ w in 𝓝 v, M w = Mstage w) ∧
        M v = (actualWeighted t0 q : WithTop ℝ) ∧ m v = actualWeighted t0 q ∧
        (∀ᶠ w in 𝓝 v, M w ≠ ⊤ ∧ 0 ≤ m w ∧ m w ≤ W (q, t.val - w ^ 2)) ∧
        ∃ psi : ℝ → ℝ, ∃ d : ℝ,
          psi v = f v ∧ f ≤ᶠ[𝓝[>] v] psi ∧ HasDerivAt psi d v ∧ d ≤ 0
    ) ∧
    let policy : ∀ (n : ℕ)
      (L : PreparedSpatialState pBase constants P g (preparedSpatialHorizon n) ((3 : ℝ) ^ n)),
      ClosedBirthPreparedClass pBase constants
        (L.native.stage (Fin.last L.native.eventCount))
        (L.native.initialMetric (Fin.last L.native.eventCount))
        ((3 : ℝ) ^ (n + 1) - L.history.time (Fin.last L.history.eventCount)) →
        ℝ → ℝ × ℝ × ℕ × ℝ :=
      fun n _ _ rNext => preparedSpatialPhysicalQualityRequest request n rNext
    ∃ (S : PreparedSpatialChain pBase constants P g)
      (future : ∀ n : ℕ, ClosedBirthPreparedClass pBase constants
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
      (∀ n, S.accuracy n ≤ (policy n (S.state n) (future n) (r n)).2.2.2) ∧
      let εcut : ℕ → ℝ := fun n => (policy n (S.state n) (future n) (r n)).1
      let Dcut : ℕ → ℝ := fun n => (policy n (S.state n) (future n) (r n)).2.1
      let mcut : ℕ → ℕ := fun n => (policy n (S.state n) (future n) (r n)).2.2.1
      ∃ W : ∀ n : ℕ, PreparedSpatialStepRetention
        (S.state n) (S.state (n + 1)) (S.accuracy n) (1 / ((n : ℝ) + 2))
        (εcut n) (Dcut n) (mcut n),
      let rNext := r
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      (
      (
      (
      F.tower = S.tower ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
        ((F.tower.history n).toHistory.event i).HasUniformDistanceScalar Cdist) ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          constants.epsilon (max constants.C1s constants.Cbirth) (max constants.C2s (max constants.Cbirth (constants.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart constants.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) constants.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t
      ) ∧
      (∀ t : ℝ, 0 ≤ t →
        q.delta t = (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t ∧
        q.neckRadius t =
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) ∧
      (∀ t : ℝ, 0 < t → q.delta t < S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
      (∀ n, (∀ x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) ∧
      (∀ m : ℕ, ∀ i : Fin (S.state (m + 1)).native.eventCount,
        let s := (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift;
        s ∈ Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        q.delta s = S.accuracy m ∧
        (∀ u : ℝ, s ≤ u → q.delta u ≤ S.accuracy m) ∧
        (∀ T : ℝ, T ∈ Icc s (2 * s) →
          (S.state (m + 1)).radius ≤ q.neckRadius T) ∧
        (∀ A : ℝ, 0 < A → q.delta s < S.diagonalLargerBallAccuracy A s →
          A < 12 * (3 : ℝ) ^ m) ∧
        ∀ n : ℕ, s ≤ (n : ℝ) →
        ∃ j : Fin (F.tower.history n).eventCount,
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ = s ∧
          HEq (records n j).nominalRadius ((W m).fineRecords i).nominalRadius ∧
          HEq (records n j).delta ((W m).fineRecords i).delta ∧
          HEq (records n j).order ((W m).fineRecords i).order ∧
          HEq (records n j).neck ((W m).fineRecords i).neck ∧
          HEq (records n j).static
            (fun z => translate_presented_static_cap
              ((S.state (m + 1)).native.coreEvent i) (S.state (m + 1)).shift
              ((((W m).fineRecords i).restrictModelWindow ((W m).fineWindows i)
                (S.state m).parameters.modelRadius_pos
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))) ∧
      (∀ (m n : ℕ) (j : Fin ((F.tower.history n).eventCount + 1)),
        (S.state (m + 1)).offset ≤ j.val →
        ∀ (y : ((F.tower.history n).stage j).Carrier) (s : ℝ),
          s ∈ Ioo ((F.tower.history n).time j)
            ((F.tower.history n).toHistory.stageEndTime j) →
          s < (3 : ℝ) ^ (m + 1) →
          ((S.state (m + 1)).radius ^ 2)⁻¹ <
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun u =>
            metricScalarAt ((F.tower.history n).toHistory.stageMetric j u) y) (Iic s) s| ≤
            constants.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
      ) ∧
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        ∃ m : ℕ, m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z))
      ) ∧
      ∃ block : ∀ n : ℕ, Fin (F.tower.history n).eventCount → ℕ,
        (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
          block n j ≤ n ∧
          ∃ i : Fin (S.state (block n j + 1)).native.eventCount,
            j.val = ((S.state (block n j + 1)).affine.eventIndex i).val ∧
            (F.tower.history n).time j.succ =
              (S.state (block n j + 1)).native.time i.succ + (S.state (block n j + 1)).shift ∧
            (F.tower.history n).time j.succ ∈
              Ioc (preparedSpatialHorizon (block n j)) ((3 : ℝ) ^ (block n j))) ∧
      (∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
        let m := block n j;
        m ≤ n ∧ ∃ i : Fin (S.state (m + 1)).native.eventCount,
          (S.state m).history.eventCount ≤ j.val ∧
          j.val < (S.state (m + 1)).history.eventCount ∧
          j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
          (F.tower.history n).time j.succ =
            (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
          (F.tower.history n).time j.succ ∈
            Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
          ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
              ((F.tower.history n).toHistory.event j) ∧
          q.delta ((F.tower.history n).time j.succ) = S.accuracy m ∧
          Dcut m ≤ (W m).fineParameters.modelRadius ∧
          mcut m ≤ (W m).fineParameters.modelOrder ∧
          (W m).fineParameters.modelAccuracy ≤ εcut m ∧
          ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
            ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
              (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order = (((W m).fineRecords i).static b).order ∧
              HEq raw.neck (((W m).fineRecords i).static b).neck ∧
              HEq raw.witness (((W m).fineRecords i).static b).witness ∧
              raw.witness.Output = (((W m).fineRecords i).static b).witness.Output ∧
              HEq raw.witness.metric (((W m).fineRecords i).static b).witness.metric ∧
              HEq raw.inclusion (((W m).fineRecords i).static b).inclusion ∧
              HEq raw.witness.cap (((W m).fineRecords i).static b).witness.cap ∧
              HEq raw.witness.retained (((W m).fineRecords i).static b).witness.retained ∧
              HEq raw.witness.collapse (((W m).fineRecords i).static b).witness.collapse ∧
              raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric ∧
              (∀ x : standardCapWindow (W m).fineParameters.modelRadius,
                HEq (raw.window x) ((((W m).fineRecords i).static b).window x)) ∧
              raw.neck.scale = ((records n j).static b').neck.scale ∧
              (∀ z : ThreeBall,
                raw.inclusion (raw.witness.cap z) =
                  ((records n j).static b').inclusion (((records n j).static b').witness.cap z)) ∧
              (∀ (z : ThreeBall) (y : ((F.tower.history n).stage j.succ).Carrier),
                ((F.tower.history n).toHistory.event j).transition.trace.presentation
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) = Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ = raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)
      ) ∧
      (
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier)
        (r A v rhoTest : ℝ),
        0 < r → 1 ≤ A → 0 ≤ v → v ^ 2 ≤ r ^ 2 / 2 → 2 * r ^ 2 < t.val →
        (∀ s ∈ Icc (t.val / 2) t.val, q.delta s < S.diagonalLargerBallAccuracy A s) →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ rhoTest →
      ∀ (first : Fin (H.eventCount + 1)) (_hle : first ≤ H.activeStage t),
        t.val - v ^ 2 ∈ H.stageDomain first →
      let nodeA : Fin H.eventCount → ℝ := fun i =>
        preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ (block n i)) *
          Real.sqrt (2 * (3 : ℝ) ^ (block n i))
      let nodeE : Fin H.eventCount → ℝ := fun i => Real.sqrt ((3 : ℝ) ^ (block n i))
      let nodeR : Fin H.eventCount → ℝ := fun i => rNext (block n i) / 100
      let nodeQ : Fin H.eventCount → ℝ := fun i => (rNext (block n i) ^ 2)⁻¹
      let nodeRho : Fin H.eventCount → ℝ := fun _ => 1
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.succ) (_hl : i.succ ≤ H.activeStage t)
        (_hstart : t.val - v ^ 2 ≤ H.time i.succ),
        let req := request (nodeA i) (nodeE i) (nodeR i) (nodeQ i) (nodeRho i)
        0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧ 0 < nodeRho i ∧ v ≤ nodeE i ∧
        H.isParabolicallyRmControlledBall t x (nodeR i) ∧
        q.delta (H.time i.succ) ≤ req.2.2.2 ∧
        q.neckRadius (H.time i.succ) ≤ nodeRho i ∧
        (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
          ∀ b, (records n j).delta b ≤ req.2.2.2) ∧
        (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
          ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
            nodeQ i < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
              constants.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i
      ) ∧
      ∀ n : ℕ,
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
        (r A rhoTest : ℝ),
        0 < r → 1 ≤ A → 2 * r ^ 2 < t.val →
        H.time (H.activeStage t) < t.val →
        H.isParabolicallyRmControlledBall t p r →
        H.isParabolicallyRmControlledBall t x rhoTest →
        q.neckRadius t.val / 100 ≤ r →
        q.neckRadius t.val / 100 ≤ rhoTest →
        (∀ s ∈ Icc (t.val / 2) t.val,
          q.delta s < S.diagonalLargerBallAccuracy A s) →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t),
        (aSeed : ℝ) = t.val - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
        (H.activeStage_mono hSeedTime) p,
        seedTrace.isRmControlled (hat := hSeedTime) r →
      ∀ (a k b : ℝ), 0 < a → a < k → k < b → b ^ 2 ≤ r ^ 2 / 2 →
      ∀ (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t),
        t.val - k ^ 2 = H.time i.succ →
        t.val - a ^ 2 < H.stageEndTime i.succ →
        H.time i.castSucc < t.val - b ^ 2 →
      let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
        (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
      let Dweight := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
      let M := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A
      let m : ℝ → ℝ := fun w => (M w).untopD 0
      let f : ℝ → ℝ := fun w =>
        Real.exp (-Cweight * w ^ 2 / r ^ 2 - 32 * w / r) * m w / w
      (∀ w ∈ Ico a k,
        M w ≤ ((2 * r * w *
          Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r) : ℝ) : WithTop ℝ)) →
      ∃ hfSeed : H.activeStage aSeed ≤ i.castSucc,
      let Opost := seedTrace.point i.succ (hfSeed.trans i.castSucc_le_succ) hl
      ∃ (qEnd : (H.stage i.succ).Carrier) (L mEvent : ℝ),
        M k = (mEvent : WithTop ℝ) ∧
        H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd =
          (mEvent : WithTop ℝ) ∧
        (∀ y : (H.stage i.succ).Carrier,
          H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost qEnd ≤
            H.physicalWeightedCost i.succ (H.activeStage t) hl t.val (3 / a₀) r A k x Opost y) ∧
        H.regularizedCost i.succ (H.activeStage t) hl t.val (3 / a₀) 0 k x qEnd =
          (L : WithTop ℝ) ∧
        riemannianEDistOf (H.stageMetric i.succ (t.val - k ^ 2)) Opost qEnd <
          ENNReal.ofReal (r * (A * (1 - 2 * k ^ 2 / r ^ 2) + 1 / 10)) ∧
        r / 4 ≤ L + r ∧ 0 < mEvent ∧
        mEvent ≤ 2 * r * k * Real.exp (Cweight * k ^ 2 / r ^ 2 + 32 * k / r) ∧
        L ≤ (Dweight - 1) * r ∧
      ∃ gamma : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) ∧
        gamma ⟨H.activeStage t, hl, le_rfl⟩ 0 = x ∧
        gamma ⟨i.succ, le_rfl, hl⟩ k = qEnd ∧
        (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc)
          (hj : j.succ ≤ H.activeStage t),
          ∃ z : (H.event j).old,
            z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hj⟩
              (Real.sqrt (t.val - H.time j.succ)) ∧
            (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hj⟩
              (Real.sqrt (t.val - H.time j.succ))) ∧
        (∑ j : H.StageInterval i.succ (H.activeStage t),
          H.stageRegularizedAction j.val t.val (gamma j)
            (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val k j.val)) = L ∧
        H.regularizedExtendedAction i.succ (H.activeStage t) t.val (3 / a₀) 0 k gamma =
          (L : WithTop ℝ) ∧
      let blockIndex := block n i
      let Dcap := (W blockIndex).fineParameters.modelRadius
      let ncap := (W blockIndex).fineParameters.modelOrder
      let εcap := (W blockIndex).fineParameters.modelAccuracy
      ∃ nativeIndex : Fin (S.state (blockIndex + 1)).native.eventCount,
        i.val = ((S.state (blockIndex + 1)).affine.eventIndex nativeIndex).val ∧
        H.time i.succ = (S.state (blockIndex + 1)).native.time nativeIndex.succ +
          (S.state (blockIndex + 1)).shift ∧
      ∃ caps : ∀ c : (H.event i).RetainedBoundaryIndex,
        (H.event i).PresentedStaticCap q.fixed Dcap ncap εcap c,
        (∀ c, (caps c).hasCanonicalWindow) ∧
        εcap ≤ 1 / 2 ∧ StandardCap.transitionEnd + 10 < Dcap ∧
        (∀ c, (caps c).neck.scale = ((records n i).static c).neck.scale) ∧
        (∀ c, ∃ cNative : ((S.state (blockIndex + 1)).native.toHistory.event nativeIndex).RetainedBoundaryIndex,
          HEq cNative c ∧
          HEq (caps c).neck (((W blockIndex).fineRecords nativeIndex).static cNative).neck ∧
          HEq (caps c).witness (((W blockIndex).fineRecords nativeIndex).static cNative).witness ∧
          HEq (caps c).inclusion (((W blockIndex).fineRecords nativeIndex).static cNative).inclusion ∧
          (caps c).witness.windowMetric = (((W blockIndex).fineRecords nativeIndex).static cNative).witness.windowMetric ∧
          (∀ z : standardCapWindow Dcap,
            HEq ((caps c).window z) ((((W blockIndex).fineRecords nativeIndex).static cNative).window z)) ∧
          (∀ z : ThreeBall, (caps c).inclusion ((caps c).witness.cap z) =
            ((records n i).static c).inclusion (((records n i).static c).witness.cap z))) ∧
      ∃ O z : (H.event i).old,
        O.val.val = seedTrace.point i.castSucc hfSeed (i.castSucc_le_succ.trans hl) ∧
        (H.event i).oldOutput O = Opost ∧
        (H.event i).oldOutput z = qEnd ∧
        (∀ c, (H.event i).oldOutput O ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        (∀ c, (H.event i).oldOutput z ∉ (caps c).window ''
          {y : standardCapWindow Dcap | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        M k ≠ ⊤ ∧ 0 < m k ∧ f k ≤ 2 * r ∧
        UpperSemicontinuousWithinAt f (Ici k) k ∧
        (∀ w ∈ Icc k b, M w ≠ ⊤ ∧ 0 ≤ m w) ∧
        AntitoneOn f (Icc k b) ∧
        (∀ w ∈ Icc k b,
          m w ≤ Real.exp (Cweight * (w ^ (2 : ℕ) - k ^ (2 : ℕ)) / r ^ (2 : ℕ) + 32 * (w - k) / r) *
            (w / k) * m k ∧
          m w ≤ 2 * r * w * Real.exp (Cweight * w ^ (2 : ℕ) / r ^ (2 : ℕ) + 32 * w / r)) := by
  classical
  obtain ⟨Cdist, hCdist, constants, makeInitial⟩ :=
    exists_prepared_spatial_physical_request_chains_with_cap_exclusion_and_reserve_quality.{u}
      Dstar εReserve hDstar hεReserve
  refine ⟨Cdist, hCdist, constants, ?_⟩
  intro P g
  obtain ⟨a₀, ha₀, initialControl, makeBase⟩ := makeInitial P g
  refine ⟨a₀, ha₀, initialControl, ?_⟩
  intro cMax hcMax
  obtain ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hBaseDistance,
    request, hRequest, hWindow, hSupport, hChain⟩ := makeBase cMax hcMax
  obtain ⟨S, future, radii, hFutureQuality, hStateQuality,
    hZero, hAllFit, hDistance, hState, hQuarter, hRequested, hW⟩ := hChain
  obtain ⟨W⟩ := hW
  refine ⟨pBase, base, hHistory, hInitial, hShift, hOffset, hRadius,
    hRadiusConstant, hFit, hBaseQuality, hBaseDistance, request, hRequest,
    hWindow, hSupport, S, future, radii, hFutureQuality, hStateQuality,
    hZero, hAllFit, hDistance, hState, hQuarter, hRequested, W, ?_⟩
  let εcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).1
  let Dcut : ℕ → ℝ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.1
  let mcut : ℕ → ℕ := fun n => (preparedSpatialPhysicalQualityRequest request n (radii n)).2.2.1
  obtain ⟨F, q, κ, records, hQualityRaw, block, hBlock, hRaw, hPhysical⟩ :=
    S.exists_surgery_with_closed_start_physical_requests hDistance εcut Dcut mcut W
      (fun n => (hState n).2.2.2.1) (fun n => (hState n).2.2.2.2.1)
      hQuarter a₀ initialControl request radii
      (fun n => ⟨(hState n).1, (hState n).2.1⟩)
      (fun n => ⟨rfl, rfl, rfl, hRequested n⟩)
  refine ⟨F, q, κ, records, hQualityRaw, block, hBlock, hRaw, hPhysical, ?_⟩
  exact closed_event_weighted_restart_of_fixed_saved_data
    P g constants pBase a₀ ha₀ request hRequest hWindow hSupport S radii
    (fun n => (hState n).1) (fun n => (hState n).2.1) W F q records block
    (fun n => hQualityRaw.1.2.2.2.1 n)
    hQualityRaw.1.1.2.2.1.2.2.2.2.le
    (fun m i => (hQualityRaw.1.2.2.2.2.1 m i).2.2.2.1)
    hRaw hPhysical

end GC.GeneralFlow
