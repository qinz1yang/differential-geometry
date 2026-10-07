import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.P5LRecordRewindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualitySurgery

set_option autoImplicit false

/-!
# O-C12X-P5L (T8) G2：S14 P5Linked 供给 `LateLinkedRecordsSupply_C11E F q`（后缀 `_C12X`）

`lateLinkedRecordsSupply_of_astra_C12X`：astra 链 `S`、retention 族 `W`（fine records 在 native
history 上）、tower 上的 `(F, q, records)` 与 outer tuple（`SH/PreparedSpatialPhysicalVolumeEvent`）
两个子句的子合取：

* `hmi`（outer m-i 子句末项的 tube 部分）：native event `i`（block `m`）在每个 `n ≥` 其时刻的
  tower history 里有像 `j`，`records n j` 的 tube delta / order / neck `≍` fine record 的；
* `hblock`（outer block 子句的 raw 部分）：每个 tower event `j` 来自某 block `m` 的 native event
  `i`（index、时刻、`SamePresentation`），其每个 retained boundary 有 tower 上的 raw cap（fine 窗口，
  canonical window，delta / order / neck / window metric 同 fine static）；

加上两项 **outer 不给的输入**（真缺口，见 `docs/geometrization/chapter8/out/CH12X-S14-GAP.md`）：

* `hcof`：fine 模型窗口共尾（`modelRadius → ∞`、`modelAccuracy → 0`、`modelOrder → ∞`）——outer 的
  `εcut / Dcut / mcut` 来自固定 `request`，只知 `≤ 1/2`、`> transitionEnd + 10`、`≥ 4`；
* `hlink`：晚期 block 的 fine static caps 是 linked（`hasCanonicalWindow` 加 `δ' ≤ S.delta`、
  `2⌊δ'⁻¹⌋₊ ≤ k`；S10-link 同类缺口）。

证明：`T := 3 ^ max k₀ k₁`；晚期 tower event 的 block `≥ max k₀ k₁`（block `m` 的 event 时刻
`≤ 3 ^ m`）；参数 `q.withModelWindow D' m ζ`（`D' = max D (transitionEnd + 1)`）；单 event 由
`exists_rewindowed_linked_record_C12X`（G1）给出。`adapter` `lateLinkedRecordsSupply_of_outer_C12X`
吃 outer 两个子句的全文形。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set

namespace GC.LongTime.Ch11

universe u

/-- **S14 P5Linked 供给**：astra 链 + retention + outer 子句的子合取 + 共尾 fine 窗口 + 晚期 fine
linked windows ⇒ `LateLinkedRecordsSupply_C11E F q`（`a12Enhanced_of_chain_C11P2` 的 `hext`
合取项逐字形）。 -/
theorem lateLinkedRecordsSupply_of_astra_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, GC.GeneralFlow.PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hfixed : q.fixed = pBase.fixed) (hrc : q.recenterConstant = pBase.recenterConstant)
    (hmi : ∀ (m : ℕ) (i : Fin (S.state (m + 1)).native.eventCount) (n : ℕ),
      (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ≤ (n : ℝ) →
      ∃ j : Fin (F.tower.history n).eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        HEq (records n j).delta ((W m).fineRecords i).delta ∧
        HEq (records n j).order ((W m).fineRecords i).order ∧
        HEq (records n j).neck ((W m).fineRecords i).neck)
    (hblock : ∀ (n : ℕ) (j : Fin (F.tower.history n).eventCount),
      ∃ m : ℕ, ∃ i : Fin (S.state (m + 1)).native.eventCount,
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ≤ (3 : ℝ) ^ m ∧
        MetricCutCapEvent.SamePresentation
          (GC.GeneralFlow.translate_retained_event ((S.state (m + 1)).native.coreEvent i)
            (S.state (m + 1)).shift).toMetricCutCapEvent
          ((F.tower.history n).toHistory.event j) ∧
        ∀ b' : ((F.tower.history n).toHistory.event j).RetainedBoundaryIndex,
          ∃ (b : ((S.state (m + 1)).native.toHistory.event i).RetainedBoundaryIndex)
            (raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap q.fixed
              (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
              (W m).fineParameters.modelAccuracy b'),
            HEq b b' ∧ raw.hasCanonicalWindow ∧
            raw.delta = (((W m).fineRecords i).static b).delta ∧
            raw.order = (((W m).fineRecords i).static b).order ∧
            HEq raw.neck (((W m).fineRecords i).static b).neck ∧
            raw.witness.windowMetric = (((W m).fineRecords i).static b).witness.windowMetric)
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder)
    (hlink : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b)) :
    LateLinkedRecordsSupply_C11E F q := by
  intro D ζ m hζ
  obtain ⟨k₁, hk₁⟩ := hlink
  have hD'pos : 0 < max D (StandardCap.transitionEnd + 1) :=
    lt_max_of_lt_right (by linarith [StandardCap.transitionEnd_pos])
  have hcap : StandardCap.transitionEnd < max D (StandardCap.transitionEnd + 1) + 1 := by
    linarith [le_max_right D (StandardCap.transitionEnd + 1)]
  obtain ⟨k₀, hk₀⟩ := hcof (max D (StandardCap.transitionEnd + 1)) ζ m hζ
  refine ⟨(3 : ℝ) ^ max k₀ k₁, fun n => ⟨q.withModelWindow
    (max D (StandardCap.transitionEnd + 1)) m ζ hD'pos hζ, rfl, rfl, rfl, rfl,
    le_max_left _ _, le_rfl, le_rfl, ?_⟩⟩
  have hev : ∀ j : Fin (F.tower.history n).eventCount,
      (3 : ℝ) ^ max k₀ k₁ ≤ (F.tower.history n).time j.succ →
      ∃ R' : GeometricCutoffRecord (F.tower.history n).toHistory j
          (q.withModelWindow (max D (StandardCap.transitionEnd + 1)) m ζ hD'pos hζ),
        ∀ b, linkedCanonicalWindow_C11E (R'.static b) := by
    intro j hj
    obtain ⟨mb, ib, hidx, htime, hle, hsame, hraw⟩ := hblock n j
    have hmb : max k₀ k₁ ≤ mb :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp (hj.trans hle)
    have hs : (S.state (mb + 1)).native.time ib.succ + (S.state (mb + 1)).shift ≤ (n : ℝ) := by
      rw [← htime]
      exact ((F.tower.history n).toHistory.time_le_horizon_at j.succ).trans_eq
        (F.tower.horizon_eq n)
    obtain ⟨j', hj', hδ, ho, hN⟩ := hmi mb ib n hs
    obtain rfl : j' = j := Fin.ext (hj'.trans hidx.symm)
    obtain ⟨hR, hA, hO⟩ := hk₀ mb (le_of_max_le_left hmb)
    exact exists_rewindowed_linked_record_C12X (records n j') ((W mb).fineRecords ib) hsame hδ ho
      hN ((W mb).fine_fixed.trans hfixed.symm) ((W mb).fine_recenter.trans hrc.symm) hraw
      (hk₁ mb (le_of_max_le_right hmb) ib) hD'pos hcap hR hO hA
  choose R' hR' using hev
  exact ⟨R', hR'⟩

section Outer

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck GC.GeneralFlow
open scoped Manifold ContDiff

/-- **adapter**：同 `lateLinkedRecordsSupply_of_astra_C12X`，`hmi / hblock` 换成 outer tuple
（`SH/PreparedSpatialPhysicalVolumeEvent:65` 的结论）里 m-i 子句（l.375–397）与 block 子句
（l.410–470）的全文（只重排换行）；outer 的消费者直接喂两个合取项。 -/
theorem lateLinkedRecordsSupply_of_outer_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) {εcut Dcut : ℕ → ℝ} {mcut : ℕ → ℕ}
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1))
      (S.accuracy n) (1 / ((n : ℝ) + 2)) (εcut n) (Dcut n) (mcut n))
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory i q)
    (hfixed : q.fixed = pBase.fixed) (hrc : q.recenterConstant = pBase.recenterConstant)
    (hmiOuter :
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
                (W m).full_radius (W m).full_order (W m).full_accuracy).static z))))
    (hblockOuter :
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
                (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
                  (W m).fineParameters.modelAccuracy b'),
              HEq b b' ∧ raw.hasCanonicalWindow ∧
              raw.delta = (((W m).fineRecords i).static b).delta ∧ raw.order =
                (((W m).fineRecords i).static b).order ∧
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
                  (((F.tower.history n).toHistory.event j).transition.trace.capping.cap b'.val z) =
                    Sum.inl y →
                raw.inclusion (raw.witness.cap z) = y) ∧
              (∀ x (v z : TangentSpace ThreeModel x), raw.witness.metric.inner x v z =
                ((F.tower.history n).initialMetric j.succ).inner (raw.inclusion x)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x v)
                  (mfderiv ThreeModel ThreeModel raw.inclusion x z)) ∧
              ∃ (x₀ : ((S.state (m + 1)).native.toHistory.event i).incoming.terminalRegularOpen)
                (δ : ℝ) (k : ℕ)
                (d : normalizedDatum ((S.state (m + 1)).native.toHistory.event i).terminal.metric
                  x₀ δ k)
                (w : StandardCap.CanonicalStaticInsertionWitness d
                  (W m).fineParameters.fixed.collarLength (W m).fineParameters.fixed.collar_pos
                  (W m).fineParameters.modelRadius (W m).fineParameters.modelOrder
                    (W m).fineParameters.modelAccuracy),
                metricScalarAt ((S.state (m + 1)).native.toHistory.event i).terminal.metric x₀ =
                  raw.neck.scale ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((S.state (m + 1)).native.toHistory.event i).outputMetric.inner
                    ((((W m).fineRecords i).static b).window x)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x v)
                    (mfderiv ThreeModel ThreeModel (((W m).fineRecords i).static b).window x z)) ∧
                (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
                  raw.neck.scale * ((F.tower.history n).initialMetric j.succ).inner (raw.window x)
                    (mfderiv ThreeModel ThreeModel raw.window x v)
                    (mfderiv ThreeModel ThreeModel raw.window x z)) ∧
                ∀ z : ThreeBall, ∃ x : standardCapWindow (W m).fineParameters.modelRadius,
                  ‖x.val‖ ≤ StandardCap.transitionEnd ∧
                  raw.window x = raw.inclusion (raw.witness.cap z)))
    (hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder)
    (hlink : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → ∀ (i : Fin (S.state (k + 1)).native.eventCount) b,
      linkedCanonicalWindow_C11E (((W k).fineRecords i).static b)) :
    LateLinkedRecordsSupply_C11E F q := by
  refine lateLinkedRecordsSupply_of_astra_C12X S W F q records hfixed hrc ?_ ?_ hcof hlink
  · intro m i n hs
    obtain ⟨-, -, -, -, -, h⟩ := hmiOuter m i
    obtain ⟨j, hj, -, -, hδ, ho, hN, -⟩ := h n hs
    exact ⟨j, hj, hδ, ho, hN⟩
  · intro n j
    obtain ⟨m, -, i, -, -, hidx, htime, hIoc, hsame, -, -, -, -, hraw⟩ := hblockOuter n j
    refine ⟨m, i, hidx, htime, hIoc.2, hsame, fun b' => ?_⟩
    obtain ⟨b, raw, hb, hcan, hd, ho, hn, -, -, -, -, -, -, -, hwm, -⟩ := hraw b'
    exact ⟨b, raw, hb, hcan, hd, ho, hn, hwm⟩

end Outer

end GC.LongTime.Ch11
