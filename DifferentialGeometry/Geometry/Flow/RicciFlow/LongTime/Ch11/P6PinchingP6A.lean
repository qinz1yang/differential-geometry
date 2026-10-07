import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Curvature.OperatorScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit

/-!
# P6 链的 pinching 环节 L2–L3（O-CH11-P6A G2，后缀 `_P6A`）

design `docs/geometrization/chapter8/design-C11-P6-20261006.md` §4 的 L2、L3a、L3b、L3：
KL 84.1(b)(c) 两处 blow-up（(b) 在选出的坏点尺度 `Q = R(y) → ∞`；(c) 在种子尺度
`Q = r⁻²`、`r ≤ r̄√t` 使 `t·Q → ∞`）都需要"重标度后的 slice 极限曲率算子非负"。

* L2 `exists_age_normalized_pinching_P6A`：fixed Hamilton–Ivey region（年龄 `a`）⇒ 重标度
  `scaleMetric Q g` 满足 `rescalePinchingFunction (a·Q) Φ` 型下界（Φ 与 `a, Q, g` 无关）。
* L3a `exists_history_pinching_P6A`：同一 flow 的 records ⇒ 一致 `a₀ > 0`，所有 history 的所有
  stage metric 在年龄 `a₀ + t` 处于 fixed HI region（初始 `a₀` 由初始度量紧性取）。
* L3b `exists_history_slice_rescaled_pinching_P6A`：L2 + L3a，slice 级、`(a₀ + t)·Q` 归一化。
* L3 `curvatureOperator_nonnegative_of_history_slice_limit_P6A`：任意选出的 history slice、基点、
  尺度 `Q n`，只要 `(1 + s n)·Q n → ∞`，重标度序列的 pointed `MetricConvergenceData` 极限曲率算子
  非负。两个 regime 推论：`…_of_scale_P6A`（`Q n → ∞`，(b)）与 `…_of_age_P6A`（`s n·Q n → ∞`，(c)）。

证明思路参照 astra HEAD 的 private WIP `ST/ClosedSlicePinchingLimit.lean`（未搬入，只当 reference）；
这里用树内引理重证，且 L3 不再要求调用者提供初始 pinching（由 L3a 从 records 取）。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-! ## L2：age-normalized pinching（slice 级） -/

/-- **L2**：存在 admissible `Φ`，使任意 3 维度量 `g` 在 fixed HI region（年龄 `a`）内的点 `x`，
重标度 `scaleMetric Q g` 后曲率算子 `≥ -(a·Q)⁻¹ Φ((a·Q)·R_Q)`（`rescalePinchingFunction (a*Q) Φ`）。
先把年龄缩放到 1，再用 `exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion`。 -/
theorem exists_age_normalized_pinching_P6A :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X]
        (g : SmoothRiemannianMetric ThreeModel X) (a Q : ℝ) (hQ : 0 < Q) (x : X),
        0 < a → InFixedHamiltonIveyRegion g a x →
        curvatureOperatorLowerBoundAt (scaleMetric Q hQ g) x
          (metricAlgebraicCurvatureTensorAt (scaleMetric Q hQ g) x)
          (rescalePinchingFunction (a * Q) Phi
            (metricScalarAt (scaleMetric Q hQ g) x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      (a₀ := 1) zero_lt_one
  refine ⟨Phi, hPhi, ?_⟩
  intro X _ _ _ _ g a Q hQ x ha hfixed
  set R := metricScalarAt g x with hRdef
  set ν := leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x)
    with hνdef
  have hpair : (R, 2 * ν) ∈ fixedHamiltonIveyRegion a :=
    (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mp hfixed
  -- 年龄归一：`(R, 2ν) ∈ region a` ⇔ `(a R, a·2ν) ∈ region 1`。
  have hscaled := (mem_fixedHamiltonIveyRegion_scale_iff (inv_pos.mpr ha)
    a R (2 * ν)).mpr hpair
  rw [inv_mul_cancel₀ ha.ne'] at hscaled
  have hunit : (a * R, a * (2 * ν)) ∈ fixedHamiltonIveyRegion 1 := by
    simpa only [div_inv_eq_mul, mul_comm] using hscaled
  have htwo := hbound 1 le_rfl (a * R) (a * (2 * ν)) hunit
  have hpos := hPhi.pos (a * R)
  have hneg : -(a * ν) ≤ Phi (a * R) := by nlinarith
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (scaleMetric Q hQ g) x (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp)
  apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
    basis horth).mpr
  rw [DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric]
  change -(ν / Q) ≤ rescalePinchingFunction (a * Q) Phi
    (metricScalarAt (scaleMetric Q hQ g) x)
  have harg : (a * Q) * (Q⁻¹ * R) = a * R := by
    calc
      _ = a * (Q * Q⁻¹) * R := by ring
      _ = _ := by rw [mul_inv_cancel₀ hQ.ne', mul_one]
  calc
    -(ν / Q) = -(a * ν) / (a * Q) := by
      field_simp [ha.ne', hQ.ne']
    _ ≤ Phi (a * R) / (a * Q) :=
      div_le_div_of_nonneg_right hneg (mul_pos ha hQ).le
    _ = rescalePinchingFunction (a * Q) Phi
        (metricScalarAt (scaleMetric Q hQ g) x) := by
      rw [rescalePinchingFunction, metricScalarAt_scaleMetric]
      change Phi (a * R) / (a * Q) = (a * Q)⁻¹ * Phi ((a * Q) * (Q⁻¹ * R))
      rw [harg, div_eq_mul_inv, mul_comm]

/-! ## L3a：同一 flow 的一致 pinching 年龄 -/

/-- **L3a**：records ⇒ 一致 `a₀ > 0`：对每个 `n`、stage `j`、`t ∈ stageDomain j`，
`(F.tower.history n).toHistory` 的 stage metric 在年龄 `a₀ + t` 处于 fixed HI region，且
`R ≥ -3/(a₀ + t)`。`a₀` 只依赖初始度量 `g`（紧性），不依赖 `n`。 -/
theorem exists_history_pinching_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ n, ∀ j : Fin ((F.tower.history n).toHistory.eventCount + 1),
      ∀ t ∈ (F.tower.history n).toHistory.stageDomain j,
      ∀ x : ((F.tower.history n).toHistory.stage j).Carrier,
        InFixedHamiltonIveyRegion ((F.tower.history n).toHistory.stageMetric j t) (a₀ + t) x ∧
          -3 / (a₀ + t) ≤ metricScalarAt ((F.tower.history n).toHistory.stageMetric j t) x := by
  obtain ⟨a, ha, hfixed, hscalar⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a, ha, fun n => ?_⟩
  have hzero := (F.tower.initial n).fixedHamiltonIveyRegion_and_scalar_lower_bound
    hfixed hscalar
  exact ((F.tower.history n).toHistory.fixedHamiltonIveyRegion_and_scalar_lower
    (records n) ha hzero.1 hzero.2).1

/-! ## L3b：slice 级 rescaled pinching -/

/-- **L3b**：同一 flow 上一致的 `a₀ > 0` 与 admissible `Φ`：任意 `n`、`t ∈ [0, horizon]`、
`Q > 0`、`x`，重标度 slice 度量 `scaleMetric Q g_t` 的曲率算子下界为
`rescalePinchingFunction ((a₀ + t)·Q) Φ`。 -/
theorem exists_history_slice_rescaled_pinching_P6A {P : OrientedThreeStage.{u}}
    {g : P.Metric} (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) :
    ∃ (a₀ : ℝ) (Phi : ℝ → ℝ), 0 < a₀ ∧ AdmissiblePinchingFunction Phi ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (Q : ℝ) (hQ : 0 < Q) (x : (H.stageAt t).Carrier),
        curvatureOperatorLowerBoundAt
          (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) x
          (metricAlgebraicCurvatureTensorAt
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) x)
          (rescalePinchingFunction (((a₀ : ℝ) + t) * Q) Phi
            (metricScalarAt (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) x)) := by
  obtain ⟨a₀, ha₀, hhist⟩ := exists_history_pinching_P6A F records
  obtain ⟨Phi, hPhi, hbound⟩ := exists_age_normalized_pinching_P6A.{u}
  refine ⟨a₀, Phi, ha₀, hPhi, ?_⟩
  intro n H t Q hQ x
  have hage : 0 < a₀ + (t : ℝ) := add_pos_of_pos_of_nonneg ha₀ t.property.1
  have hfixed := (hhist n (H.activeStage t) t (H.activeStage_mem t) x).1
  exact hbound (H.stageAt t).Carrier (H.stageMetric (H.activeStage t) t)
    (a₀ + t) Q hQ x hage hfixed

/-! ## L3：pointed slice 极限曲率算子非负 -/

/-- 同一 flow 的 history slice 序列（指标 `ind n`、时间 `s n`、基点 `x n`）按 `Q n` 重标度后的
pointed 序列 `(M_n, x n, scaleMetric (Q n) g_{s n})`。 -/
def historySliceSeq_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ind : ℕ → ℕ)
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (x : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) : PointedRiemannianSeq.{u, 0, 0} ThreeModel where
  obj n :=
    { M := ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier
      basepoint := x n
      metric := scaleMetric (Q n) (hQ n) ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) }

/-- **L3**：同一 flow 的任意 history slice 序列，若 `(1 + s n)·Q n → ∞`，则
`historySliceSeq_P6A` 的 pointed `MetricConvergenceData`（canonical source domain）极限，
曲率算子处处非负。 -/
theorem curvatureOperator_nonnegative_of_history_slice_limit_P6A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (ind : ℕ → ℕ)
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (x : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps (historySliceSeq_P6A F ind s x Q hQ) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (hgrow : Tendsto (fun n => (1 + (s n : ℝ)) * Q n) atTop atTop) :
    ∀ z : limit.M, metricAlgebraicCurvatureTensorAt limit.metric z ∈
      algebraicCurvatureOperatorNonnegativeCone := by
  obtain ⟨a₀, Phi, ha₀, hPhi, hpin⟩ := exists_history_slice_rescaled_pinching_P6A F records
  let lam : ℕ → ℝ := fun n => (a₀ + (s n : ℝ)) * Q n
  have hlamPos (n : ℕ) : 0 < lam n :=
    mul_pos (add_pos_of_pos_of_nonneg ha₀ (s n).property.1) (hQ n)
  -- `(a₀ + s)·Q ≥ min a₀ 1 · (1 + s)·Q`，故 `lam → ∞`。
  have hc : 0 < min a₀ 1 := lt_min ha₀ one_pos
  have hlam : Tendsto lam atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hgrow.const_mul_atTop hc)
    have hs : (0 : ℝ) ≤ s n := (s n).property.1
    have h1 : min a₀ 1 * (1 + (s n : ℝ)) ≤ a₀ + s n := by
      have hm1 : min a₀ 1 ≤ a₀ := min_le_left _ _
      have hm2 : min a₀ 1 ≤ 1 := min_le_right _ _
      nlinarith
    calc min a₀ 1 * ((1 + (s n : ℝ)) * Q n) = (min a₀ 1 * (1 + (s n : ℝ))) * Q n := by ring
      _ ≤ (a₀ + s n) * Q n := mul_le_mul_of_nonneg_right h1 (hQ n).le
  let X := historySliceSeq_P6A F ind s x Q hQ
  have hpinching (n : ℕ) (z : (X.obj n).M) :
      curvatureOperatorLowerBoundAt (X.obj n).metric z
        (metricAlgebraicCurvatureTensorAt (X.obj n).metric z)
        (rescalePinchingFunction (lam n) Phi (metricScalarAt (X.obj n).metric z)) :=
    hpin (ind n) (s n) (Q n) (hQ n) z
  exact curvatureOperator_nonnegative_of_pointed_admissible_pinching_eventually
    Mconv hcanonical hPhi lam hlamPos (hlam.comp hσ.tendsto_atTop)
    (Eventually.of_forall fun n => hpinching (σ n))

/-- **L3 / (b) regime**：选出的坏点尺度 `Q n → ∞`（不管时间）⇒ 极限曲率算子非负。 -/
theorem curvatureOperator_nonnegative_of_history_slice_limit_of_scale_P6A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (ind : ℕ → ℕ)
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (x : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps (historySliceSeq_P6A F ind s x Q hQ) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (hQtop : Tendsto Q atTop atTop) :
    ∀ z : limit.M, metricAlgebraicCurvatureTensorAt limit.metric z ∈
      algebraicCurvatureOperatorNonnegativeCone := by
  refine curvatureOperator_nonnegative_of_history_slice_limit_P6A F records ind s x Q hQ
    σ hσ limit maps Mconv hcanonical (tendsto_atTop_mono (fun n => ?_) hQtop)
  have hs : (0 : ℝ) ≤ s n := (s n).property.1
  nlinarith [hQ n]

/-- **L3 / (c) regime**：年龄归一尺度 `s n · Q n → ∞`（KL 84.1(c) 中 `r ≤ r̄√t`、`Q = r⁻²`、
`r̄ → 0` 的反例序列）⇒ 极限曲率算子非负。 -/
theorem curvatureOperator_nonnegative_of_history_slice_limit_of_age_P6A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (ind : ℕ → ℕ)
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (x : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps (historySliceSeq_P6A F ind s x Q hQ) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (hage : Tendsto (fun n => (s n : ℝ) * Q n) atTop atTop) :
    ∀ z : limit.M, metricAlgebraicCurvatureTensorAt limit.metric z ∈
      algebraicCurvatureOperatorNonnegativeCone := by
  refine curvatureOperator_nonnegative_of_history_slice_limit_P6A F records ind s x Q hQ
    σ hσ limit maps Mconv hcanonical (tendsto_atTop_mono (fun n => ?_) hage)
  nlinarith [hQ n]

/-- consumer：同一 flow、同一 records 下 (b)/(c) 两个 regime 共用一个 `(a₀, Φ)`
（L3b 的一致性：pinching 函数不随 slice、尺度变）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (n : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (x y : ((F.tower.history n).toHistory.stageAt t).Carrier)
    (Q₁ Q₂ : ℝ) (h₁ : 0 < Q₁) (h₂ : 0 < Q₂) :
    ∃ (a₀ : ℝ) (Phi : ℝ → ℝ), 0 < a₀ ∧ AdmissiblePinchingFunction Phi ∧
      curvatureOperatorLowerBoundAt (scaleMetric Q₁ h₁
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric Q₁ h₁
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) x)
        (rescalePinchingFunction ((a₀ + t) * Q₁) Phi
          (metricScalarAt (scaleMetric Q₁ h₁ ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) x)) ∧
      curvatureOperatorLowerBoundAt (scaleMetric Q₂ h₂
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) y
        (metricAlgebraicCurvatureTensorAt (scaleMetric Q₂ h₂
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) y)
        (rescalePinchingFunction ((a₀ + t) * Q₂) Phi
          (metricScalarAt (scaleMetric Q₂ h₂ ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)) y)) := by
  obtain ⟨a₀, Phi, ha₀, hPhi, hpin⟩ := exists_history_slice_rescaled_pinching_P6A F records
  exact ⟨a₀, Phi, ha₀, hPhi, hpin n t Q₁ h₁ x, hpin n t Q₂ h₂ y⟩

end GC.LongTime.Ch11
