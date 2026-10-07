import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRawCaps

/-!
# S-CH11-FIX12 port of astra `PreparedSpatialPhysicalRequests`（`PortC11P`）

来源：donor `PreparedSpatialPhysicalRequests.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* 裸名 `SpatialCanonicalWitness`（`…Perelman.CanonicalNeighborhood.FiniteHorn`）与
  `normalizedDatum`（`DifferentialGeometry.Geometry.Neck`）在本树 unknown identifier（`open` 不传递，
  donor 文件头缺这两行）→ 补 `open DifferentialGeometry.Geometry.Neck` 与
  `open …Perelman.CanonicalNeighborhood.FiniteHorn`（只是名字解析，同 RawCaps 的 open 行）；
* `hRadiusZero` 里 `hParameters 0 0 ⟨le_rfl, le_rfl⟩`：第二个分量是 `0 ≤ ((0 : ℕ) : ℝ)`，`le_rfl`
  在 reducible 下统一不了 `0` 与 `↑0` → `by norm_num`；
* `hBounds` 里 `rw [← hBirth n i] at hEntry`：`hEntry` 整个合取含依赖于 `s = time + shift` 的
  `translate_presented_static_cap` / `restrictModelWindow ⋯` 等，motive 不 type correct（"Application
  type mismatch: `S.state (block n i + 1)` … `preparedSpatialHorizon`"）→ 先取出真正用到的两个分量
  `hEntryRadius := hEntry.2.2.2.1`、`hEntryAccuracy := hEntry.2.2.2.2.1`（只含实数、无依赖类型），
  再对它们 `rw [← hBirth n i]`，下游两处用点改用这两个名字；
* 陈述里只出现、证明不引用的 binder（`hle` / `hf` / `hl` / `hstart`）加 `_` 前缀（unusedVariables；
  binder 名不改变陈述）。

原路径 `PreparedSpatialPhysicalRequests` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace GC.GeneralFlow
universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

open private physical_request_box_bounds_of_le_start from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalPolicy

/-- Keep the same selected surgery and complete birth-block raw certificate,
and attach physical request data also at a closed curve start. -/
theorem PreparedSpatialChain.exists_surgery_with_closed_start_physical_requests
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (hdrop : ∀ n, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (a₀ : ℝ)
    (initialControl : ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (rNext : ℕ → ℝ)
    (hrNext : ∀ m, 0 < rNext m ∧ (S.state (m + 1)).radius = rNext m)
    (hRequested : ∀ m,
      let req := preparedSpatialPhysicalQualityRequest request m (rNext m)
      εcut m = req.1 ∧ Dcut m = req.2.1 ∧ mcut m = req.2.2.1 ∧
        S.accuracy m ≤ req.2.2.2) :
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
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
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
            C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
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
              C.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.succ → i.succ ≤ H.activeStage t →
        t.val - v ^ 2 ≤ H.time i.succ →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i := by
  classical
  obtain ⟨F, q, κ, records, hQuality, hRaw⟩ :=
    S.exists_surgery_with_retained_raw_caps hS εcut Dcut mcut W hshift hoffset
      hdrop a₀ initialControl
  refine ⟨F, q, κ, records, ⟨hQuality, hRaw⟩, ?_⟩
  choose block hBlock nativeIndex hCountLo hCountHi hIndex hBirth hBirthBand
    hPresentation hDelta hRawRadius hRawOrder hRawAccuracy hCap using hRaw
  refine ⟨block, ?_, ?_, ?_⟩
  · intro n j
    exact ⟨hBlock n j, nativeIndex n j, hIndex n j, hBirth n j, hBirthBand n j⟩
  · intro n j
    exact ⟨hBlock n j, nativeIndex n j, hCountLo n j, hCountHi n j,
      hIndex n j, hBirth n j, hBirthBand n j, hPresentation n j, hDelta n j,
      hRawRadius n j, hRawOrder n j, hRawAccuracy n j, hCap n j⟩
  have hForward := hQuality.2.2.2.2.1
  have hDerivative := hQuality.2.2.2.2.2
  obtain ⟨_hTower, _hDistance, _hStatic, _hκpos, _hκanti, hδanti, hRadiusAnti,
    hParameters, _hRecords, _hCanonical, _hWindows, _hNoncollapsed, _hPrefix,
    _hDecay, _hRecent⟩ := hQuality.1
  have hRadiusZero : q.neckRadius 0 ≤ 1 := by
    calc
      q.neckRadius 0 = (S.observation 0).parameters.neckRadius 0 :=
        (hParameters 0 0 ⟨le_rfl, by norm_num⟩).2.1
      _ = (S.state 1).parameters.neckRadius 0 := rfl
      _ = (S.state 0).parameters.neckRadius 0 :=
        ((S.successor 0).parameters_past 0 (by norm_num [preparedSpatialHorizon])).2.1
      _ = (S.state 0).radius :=
        (S.state 0).radius_after 0 (by norm_num [preparedSpatialHorizon])
      _ ≤ 1 := S.initial_radius_le
  intro n H t x r A v rhoTest hr hA hv hhalf hsmall hAccuracy hPoleBall hTest
    _first _hle _hpast nodeA nodeE nodeR nodeQ nodeRho
  have hBounds (i : Fin H.eventCount) (hl : i.succ ≤ H.activeStage t)
      (hstart : t.val - v ^ 2 ≤ H.time i.succ) :
      0 ≤ nodeE i ∧ 0 < nodeR i ∧ 0 < nodeQ i ∧
      t.val < (3 : ℝ) ^ (block n i + 1) ∧ v ≤ nodeE i ∧ nodeR i ≤ rhoTest ∧
      preparedSpatialPhysicalActionFactor A * r < nodeA i := by
    have hbirth : H.time i.succ ≤ t.val :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
    have hrecent : t.val / 2 < H.time i.succ := by
      nlinarith [sq_nonneg r]
    have htwo : t.val ≤ 2 * H.time i.succ := by linarith
    have hEntry := hForward (block n i) (nativeIndex n i)
    dsimp only at hEntry
    have hEntryRadius := hEntry.2.2.2.1
    have hEntryAccuracy := hEntry.2.2.2.2.1
    rw [← hBirth n i] at hEntryRadius hEntryAccuracy
    have hAb : A < 12 * (3 : ℝ) ^ (block n i) :=
      hEntryAccuracy A (by linarith) (hAccuracy _ ⟨hrecent.le, hbirth⟩)
    have hReserve : rNext (block n i) ≤ q.neckRadius t.val := by
      rw [← (hrNext (block n i)).2]
      exact hEntryRadius t.val ⟨hbirth, htwo⟩
    obtain ⟨hE, hR, hQ, _hRecent', _hTwo', hBand, hClock, _hRadius, hRTest, hFit⟩ :=
      physical_request_box_bounds_of_le_start (block n i) A t.val (H.time i.succ) r v
        (rNext (block n i)) (q.neckRadius t.val) rhoTest hA hAb hr hv hhalf hsmall
        hstart hbirth (hBirthBand n i).2 (hrNext (block n i)).1 hReserve hTest
    exact ⟨hE, hR, hQ, hBand, hClock, hRTest, hFit⟩
  refine ⟨?_, fun i _hf hl hstart => (hBounds i hl hstart).2.2.2.2.2.2.le⟩
  intro i _hf hl hstart req
  obtain ⟨hE, hR, hQ, hBand, hClock, hRTest, _hFit⟩ := hBounds i hl hstart
  have hReq := hRequested (block n i)
  simp only [preparedSpatialPhysicalQualityRequest,
    ite_eq_left (hrNext (block n i)).1] at hReq
  change εcut (block n i) = req.1 ∧ Dcut (block n i) = req.2.1 ∧
    mcut (block n i) = req.2.2.1 ∧ S.accuracy (block n i) ≤ req.2.2.2 at hReq
  have hδNode : q.delta (H.time i.succ) ≤ req.2.2.2 :=
    (hDelta n i).le.trans hReq.2.2.2
  have hRadius : q.neckRadius (H.time i.succ) ≤ nodeRho i :=
    (hRadiusAnti (by norm_num) (H.time_nonneg i.succ) (H.time_nonneg i.succ)).trans hRadiusZero
  refine ⟨hE, hR, hQ, by norm_num, hClock, hPoleBall.mono_radius H hR hRTest,
    hδNode, hRadius, ?_, ?_, ?_⟩
  · intro j hij _ b
    have htime : H.time i.succ ≤ H.time j.succ :=
      H.time_strictMono.monotone (hij.trans j.castSucc_le_succ)
    exact ((records n j).delta_le b).trans
      ((hδanti (H.time_nonneg i.succ) (H.time_nonneg j.succ) htime).trans hδNode)
  · intro j hij _ y s hs hsT hscalar
    have hOffset : (S.state (block n i + 1)).offset ≤ j.val := by
      rw [hoffset]
      have hcount := hCountLo n i
      have hval : i.succ.val ≤ j.val := hij
      simp only [Fin.val_succ] at hval
      omega
    have hscalar' : ((S.state (block n i + 1)).radius ^ 2)⁻¹ <
        metricScalarAt (H.stageMetric j s) y := by
      rw [(hrNext (block n i)).2]
      exact hscalar
    exact hDerivative (block n i) n j hOffset y s hs (hsT.trans_lt hBand) hscalar'
  · intro b'
    obtain ⟨_b, raw, _hLabel, hCanonical, _hDelta, _hOrder, _hNeck, _hWitness,
      _hOutput, _hMetric, _hInclusion, _hCap, _hRetained, _hCollapse,
      _hWindowMetric, _hWindowPoints, hScale, _hRemaining⟩ := hCap n i b'
    exact ⟨(W (block n i)).fineParameters.modelRadius,
      (W (block n i)).fineParameters.modelAccuracy,
      (W (block n i)).fineParameters.modelOrder, raw,
      hReq.2.1.symm.le.trans (hRawRadius n i),
      hReq.2.2.1.symm.le.trans (hRawOrder n i),
      (hRawAccuracy n i).trans hReq.1.le, hCanonical, hScale⟩

/-- Recover the original crossed-event interface from the same closed-start
selection without choosing another surgery, block, or raw cap. -/
theorem PreparedSpatialChain.exists_surgery_with_event_local_physical_requests
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0}
    (S : PreparedSpatialChain pBase C P g)
    (hS : ∀ n, (S.state n).DistanceData Cdist)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (hshift : ∀ n, (S.state (n + 1)).shift =
      (S.state n).history.time (Fin.last (S.state n).history.eventCount))
    (hoffset : ∀ n, (S.state (n + 1)).offset = (S.state n).history.eventCount)
    (hdrop : ∀ n, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (a₀ : ℝ)
    (initialControl : ∀ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ)
    (rNext : ℕ → ℝ)
    (hrNext : ∀ m, 0 < rNext m ∧ (S.state (m + 1)).radius = rNext m)
    (hRequested : ∀ m,
      let req := preparedSpatialPhysicalQualityRequest request m (rNext m)
      εcut m = req.1 ∧ Dcut m = req.2.1 ∧ mcut m = req.2.2.1 ∧
        S.accuracy m ≤ req.2.2.2) :
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
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
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
            C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
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
      (∀ (i : Fin H.eventCount) (_hf : first ≤ i.castSucc) (_hl : i.succ ≤ H.activeStage t),
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
              C.Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) ∧
        (∀ b : (H.event i).RetainedBoundaryIndex,
          ∃ (Dbig ζ : ℝ) (m : ℕ)
            (S : (H.event i).PresentedStaticCap q.fixed Dbig m ζ b),
            req.2.1 ≤ Dbig ∧ req.2.2.1 ≤ m ∧ ζ ≤ req.1 ∧ S.hasCanonicalWindow ∧
            S.neck.scale = ((records n i).static b).neck.scale)) ∧
      ∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        preparedSpatialPhysicalActionFactor A * r ≤ nodeA i := by
  obtain ⟨F, q, κ, records, hRaw, block, hBlock, _hBlockRaw, hClosed⟩ :=
    S.exists_surgery_with_closed_start_physical_requests hS εcut Dcut mcut W
      hshift hoffset hdrop a₀ initialControl request rNext hrNext hRequested
  refine ⟨F, q, κ, records, hRaw, block, hBlock, ?_⟩
  intro n H t x r A v rhoTest hr hA hv hhalf hsmall hAccuracy hPoleBall hTest
    first hle hpast _nodeA _nodeE _nodeR _nodeQ _nodeRho
  have hQueries := hClosed n t x r A v rhoTest hr hA hv hhalf hsmall
    hAccuracy hPoleBall hTest first hle hpast
  have hstart (i : Fin H.eventCount) (hf : first ≤ i.castSucc) :
      t.val - v ^ 2 < H.time i.succ := by
    let start : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - v ^ 2, H.stageDomain_subset first hpast⟩
    have hactive : H.activeStage start = first :=
      (H.mem_stageDomain_iff start first).mp hpast
    by_contra hn
    have hi : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
  refine ⟨?_, ?_⟩
  · intro i hf hl
    exact hQueries.1 i (hf.trans i.castSucc_le_succ) hl (hstart i hf).le
  · intro i hf hl
    exact hQueries.2 i (hf.trans i.castSucc_le_succ) hl (hstart i hf).le

end GC.GeneralFlow
