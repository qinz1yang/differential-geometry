import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction

set_option autoImplicit false

/-!
# S-CH11-REPROVE-D (G2)：S5 的传输核（prefix / restrict / closed-buffer / 一步 / 链）

astra 里 S5（`HistoryCanonicalSupply_C11S`）的 producer 是三层：

1. `PreparedSpatialState.canonical`（`SH/PreparedSpatialState.lean:117`，字段）← base（`E = 0`，空真，
   `SH/PreparedSpatialBase.lean:120`）与 step（`SH/PreparedSpatialStep.lean:296–365` 的 `hcanonical`）；
2. `PreparedSpatialChain.observation_canonical`（`SH/PreparedSpatialChain.lean:128`）：从 state 的
   `canonical` 经 `H.restrict a` 传输到整数观测历史；
3. `exists_surgery_with_spatial_control`（`SH/PreparedSpatialSurgery.lean`）末段：
   `diagonal_eq_on_prefix` 换 ρ（G3）。

这些在 reference 里都挂在 `PreparedSpatialChain` / `PreparedSpatialState` 上（reference-only 模块链），
这里用树内引理重证成**对任意历史 / 参数的显式 binder 陈述**（不新建结构 / 命名 Prop）：

* `canonical_of_overlap_C11RD`：两段历史在某时刻的 stage / 度量 / 点 overlap 上传输 canonical witness
  （astra `overlap_spatialWitness_transport` + `overlap_scalar_eq` 的树内重证，二者在 reference 里是
  `SpatialWitnessTransport` 的 private 引理）；
* `canonical_restrict_C11RD`：`observation_canonical` 的一般形（`H.restrict a`，`a < E`）；
* `canonical_old_of_prefix_C11RD`：step 的 `t < E` 分支（旧前缀 `IsPrefixOf`，`ρ` 在 `t ≤ E` 上相同）；
* `canonical_tail_of_closed_C11RD`：step 的 `t ≥ E` 分支（closed-seam receiver `closed` 经 `J.restrict T`
  与阈值 `Q ≤ ρ⁻²`）；
* `canonical_step_C11RD`：step 的 `hcanonical` 全貌；`canonical_vacuous_C11RD`：base（`E = 0`）；
* `canonical_chain_C11RD`：对任意历史链的归纳（`E 0 = 0`）。

**剩余的物理输入** = `closed`（astra `PreparedOverlapExtension.lean:1131`
`exists_spatialCanonicalWitness_on_buffered_same_tail_observation_with_closed_seam`：用
`AffineEventPrefix` 与 `NativeEstimates`，二者在 `CutoffRecordConcatenation`（SKIP）/
`PreparedObservationData` 的闭包里，不在树内）。
G4 在树内重证它的 birth / strict 分支（overlap 假设显式化）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-! ## 点 / 度量 / witness 的传输（overlap） -/

private def overlapPoint_C11RD {P Q : OrientedThreeStage.{u}} (h : P = Q) (x : P.Carrier) :
    Q.Carrier := h ▸ x

private theorem overlapPoint_heq_C11RD {P Q : OrientedThreeStage.{u}} (h : P = Q)
    (x : P.Carrier) : HEq (overlapPoint_C11RD h x) x := by
  cases h
  exact HEq.rfl

private theorem overlap_scalar_eq_C11RD {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {g : P.Metric} {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {y : Q.Carrier}
    (hx : HEq x y) : metricScalarAt g x = metricScalarAt g' y := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

private theorem overlap_witness_C11RD {P Q : OrientedThreeStage.{u}} (h : P = Q)
    {g : P.Metric} {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {y : Q.Carrier}
    (hx : HEq x y) {ε C1 C2 : ℝ}
    (hW : ∃ W : SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness g' ε C1 C2 y, W.capTubeHasNeckChart ε := by
  cases h
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact hW

/-- **overlap 传输**：历史 `A` 在 `tA` 与历史 `B` 在 `tB` 的 active stage、该时刻的度量相同（`HEq`），
则 `B` 一侧 "`Q <` 标量曲率 ⇒ 有带 neck chart 的 spatial canonical witness" 传到 `A` 一侧
（witness 的常数 `ε C1 C2` 不变）。 -/
theorem canonical_of_overlap_C11RD {A B : ObservedHistory.{u}}
    {tA : Icc (0 : ℝ) A.horizon} {tB : Icc (0 : ℝ) B.horizon}
    (hstage : A.stageAt tA = B.stageAt tB)
    (hmetric : HEq (A.stageMetric (A.activeStage tA) tA) (B.stageMetric (B.activeStage tB) tB))
    {Q ε C1 C2 : ℝ}
    (hB : ∀ y : (B.stageAt tB).Carrier,
      Q < metricScalarAt (B.stageMetric (B.activeStage tB) tB) y →
      ∃ W : SpatialCanonicalWitness (B.stageMetric (B.activeStage tB) tB) ε C1 C2 y,
        W.capTubeHasNeckChart ε) :
    ∀ x : (A.stageAt tA).Carrier,
      Q < metricScalarAt (A.stageMetric (A.activeStage tA) tA) x →
      ∃ W : SpatialCanonicalWitness (A.stageMetric (A.activeStage tA) tA) ε C1 C2 x,
        W.capTubeHasNeckChart ε := by
  intro x hx
  have hxy : HEq x (overlapPoint_C11RD hstage x) := (overlapPoint_heq_C11RD hstage x).symm
  have hs := overlap_scalar_eq_C11RD hstage hmetric hxy
  exact overlap_witness_C11RD hstage.symm hmetric.symm hxy.symm (hB _ (by rw [← hs]; exact hx))

/-! ## `observation_canonical` 的一般形 -/

/-- astra `PreparedSpatialChain.observation_canonical`（`SH/PreparedSpatialChain.lean:128`）的一般形：
`H` 在 `t < E` 上有 canonical witness（阈值 `ρ⁻²`），则它在任意 `a < E` 的 restriction `H.restrict a`
上（整个 `Icc 0 a`）有。 -/
theorem canonical_restrict_C11RD (H : RetainedCoreHistory.{u}) (a : Icc (0 : ℝ) H.horizon)
    (ρ : ℝ → ℝ) (E : ℝ) (haE : (a : ℝ) < E) {ε C1 C2 : ℝ}
    (hH : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < E →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρ t ^ 2)⁻¹ < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) (H.restrict a).toHistory.horizon,
      ∀ x : ((H.restrict a).toHistory.stageAt t).Carrier,
        (ρ t ^ 2)⁻¹ < metricScalarAt
          ((H.restrict a).toHistory.stageMetric ((H.restrict a).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((H.restrict a).toHistory.stageMetric ((H.restrict a).toHistory.activeStage t) t)
          ε C1 C2 x, W.capTubeHasNeckChart ε := by
  intro t
  let tH : Icc (0 : ℝ) H.toHistory.horizon := ⟨t, t.2.1, t.2.2.trans a.2.2⟩
  have htE : (tH : ℝ) < E := t.2.2.trans_lt haE
  exact canonical_of_overlap_C11RD (H.toHistory.restrict_stageAt a t)
    (H.toHistory.restrict_sliceMetric a t) (hH tH htE)

/-! ## 一步（`PreparedSpatialStep.lean:296–365` 的 `hcanonical`） -/

/-- step 的 `t < E` 分支：`H` 是 `J` 的前缀（`ObservedHistory.IsPrefixOf`），`ρ` 在 `t ≤ E` 上相同
（`H.horizon = E`），则 `H` 在 `t < E` 的 canonical 传到 `J` 的同一时间段。 -/
theorem canonical_old_of_prefix_C11RD {H J : RetainedCoreHistory.{u}}
    (hIJ : H.toHistory.IsPrefixOf J.toHistory) (ρH ρJ : ℝ → ℝ) (E : ℝ) (hE : H.horizon = E)
    (hρ : ∀ t : ℝ, t ≤ E → ρJ t = ρH t) {ε C1 C2 : ℝ}
    (hH : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < E →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρH t ^ 2)⁻¹ < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < E →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρJ t ^ 2)⁻¹ < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε := by
  intro t htE x hx
  let tOld : Icc (0 : ℝ) H.toHistory.horizon := ⟨t, t.2.1, htE.le.trans_eq hE.symm⟩
  rw [hρ t htE.le] at hx
  exact canonical_of_overlap_C11RD (hIJ.stageAt_eq tOld).symm (hIJ.sliceMetric_heq tOld).symm
    (hH tOld htE) x hx

/-- step 的 `t ≥ E` 分支：closed-seam receiver `closed`（对 `J.restrict T`，`T < J.horizon`，
`b ≤ t`，阈值 `Q`）+ 阈值 `Q ≤ ρ⁻²`（`E ≤ t < B`）⇒ `J` 在 `E ≤ t < B` 上的 canonical。
`closed` 不在树内产生（`PreparedOverlapExtension.lean:1131`），保持显式 binder。 -/
theorem canonical_tail_of_closed_C11RD (J : RetainedCoreHistory.{u}) (ρ : ℝ → ℝ)
    (E B Q b : ℝ) (hJB : J.horizon = B) (hE0 : 0 ≤ E) (hEB : E < B) (hbE : b ≤ E)
    (hthr : ∀ t : ℝ, E ≤ t → t < B → Q ≤ (ρ t ^ 2)⁻¹) {ε C1 C2 : ℝ}
    (closed : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Q < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, E ≤ (t : ℝ) → (t : ℝ) < B →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρ t ^ 2)⁻¹ < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε := by
  intro t hEt htB x hx
  have hmaxB : max E (t : ℝ) < B := max_lt hEB htB
  have hmaxT : max E (t : ℝ) < (max E (t : ℝ) + B) / 2 := by linarith
  let T : Icc (0 : ℝ) J.horizon :=
    ⟨(max E (t : ℝ) + B) / 2, by
      have hnonneg := hE0.trans (le_max_left E (t : ℝ))
      linarith, by rw [hJB]; linarith⟩
  have hbuffer : (T : ℝ) < J.horizon := by
    change (max E (t : ℝ) + B) / 2 < J.horizon
    rw [hJB]
    linarith
  have htT : (t : ℝ) ≤ (T : ℝ) := (le_max_right E (t : ℝ)).trans hmaxT.le
  let tO : Icc (0 : ℝ) (J.restrict T).toHistory.horizon := ⟨(t : ℝ), t.property.1, htT⟩
  exact canonical_of_overlap_C11RD (J.toHistory.restrict_stageAt T tO).symm
    (J.toHistory.restrict_sliceMetric T tO).symm
    (closed T hbuffer tO (hbE.trans hEt)) x (lt_of_le_of_lt (hthr t hEt htB) hx)

/-- **step**（`hcanonical` 全貌）：前缀 `H`（`H.horizon = E`，`t < E` 上 canonical）+ closed receiver
⇒ `J`（`J.horizon = B`）在 `t < B` 上 canonical（阈值 `ρJ⁻²`，`ρJ = ρH` 在 `t ≤ E`）。 -/
theorem canonical_step_C11RD {H J : RetainedCoreHistory.{u}}
    (hIJ : H.toHistory.IsPrefixOf J.toHistory) (ρH ρJ : ℝ → ℝ) (E B Q b : ℝ)
    (hE : H.horizon = E) (hJB : J.horizon = B) (hE0 : 0 ≤ E) (hEB : E < B) (hbE : b ≤ E)
    (hρ : ∀ t : ℝ, t ≤ E → ρJ t = ρH t)
    (hthr : ∀ t : ℝ, E ≤ t → t < B → Q ≤ (ρJ t ^ 2)⁻¹) {ε C1 C2 : ℝ}
    (hH : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < E →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρH t ^ 2)⁻¹ < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε)
    (closed : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Q < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < B →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρJ t ^ 2)⁻¹ < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε := by
  intro t htB x hx
  by_cases htE : (t : ℝ) < E
  · exact canonical_old_of_prefix_C11RD hIJ ρH ρJ E hE hρ hH t htE x hx
  · exact canonical_tail_of_closed_C11RD J ρJ E B Q b hJB hE0 hEB hbE hthr closed t
      (le_of_not_gt htE) htB x hx

/-- base（`PreparedSpatialBase.lean:120`）：`E = 0` 时 canonical 空真（`t ≥ 0`）。 -/
theorem canonical_vacuous_C11RD (H : RetainedCoreHistory.{u}) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ) :
    ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < 0 →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρ t ^ 2)⁻¹ < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε :=
  fun t ht => absurd t.2.1 (not_le.2 ht)

/-! ## 链：对 step 归纳 -/

/-- **链**：历史 `H n`（`horizon = E n`，`E 0 = 0`），相邻两个满足 step 数据（前缀、`ρ` 在 `t ≤ E n`
上相同、阈值、closed receiver）⇒ 每个 `H n` 在 `t < E n` 上 canonical（阈值 `(ρ n)⁻²`）。 -/
theorem canonical_chain_C11RD (H : ℕ → RetainedCoreHistory.{u}) (ρ : ℕ → ℝ → ℝ)
    (E Q b : ℕ → ℝ) {ε C1 C2 : ℝ} (hE0 : E 0 = 0) (hHE : ∀ n, (H n).horizon = E n)
    (hEnonneg : ∀ n, 0 ≤ E n) (hEB : ∀ n, E n < E (n + 1)) (hbE : ∀ n, b n ≤ E n)
    (hprefix : ∀ n, (H n).toHistory.IsPrefixOf (H (n + 1)).toHistory)
    (hρ : ∀ n (t : ℝ), t ≤ E n → ρ (n + 1) t = ρ n t)
    (hthr : ∀ n (t : ℝ), E n ≤ t → t < E (n + 1) → Q n ≤ (ρ (n + 1) t ^ 2)⁻¹)
    (closed : ∀ n, ∀ T : Icc (0 : ℝ) (H (n + 1)).horizon, (T : ℝ) < (H (n + 1)).horizon →
      ∀ t : Icc (0 : ℝ) ((H (n + 1)).restrict T).toHistory.horizon, b n ≤ (t : ℝ) →
        ∀ x : (((H (n + 1)).restrict T).toHistory.stageAt t).Carrier,
          Q n < metricScalarAt
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            (((H (n + 1)).restrict T).toHistory.stageMetric
              (((H (n + 1)).restrict T).toHistory.activeStage t) t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) :
    ∀ n, ∀ t : Icc (0 : ℝ) (H n).toHistory.horizon, (t : ℝ) < E n →
      ∀ x : ((H n).toHistory.stageAt t).Carrier,
        (ρ n t ^ 2)⁻¹ < metricScalarAt
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε := by
  intro n
  induction n with
  | zero =>
    rw [hE0]
    exact canonical_vacuous_C11RD (H 0) (ρ 0) ε C1 C2
  | succ n ih =>
    exact canonical_step_C11RD (hprefix n) (ρ n) (ρ (n + 1)) (E n) (E (n + 1)) (Q n) (b n)
      (hHE n) (hHE (n + 1)) (hEnonneg n) (hEB n) (hbE n) (hρ n) (hthr n) ih (closed n)

/-! ## Consumer -/

/-- consumer：从 base（`E = 0`，`canonical_vacuous_C11RD`）经一步（`canonical_step_C11RD`）到 `J`，
即 astra `state 1`（`E = 0`，`B = 1`）的 `canonical` 字段；`closed` 是剩下的物理输入。 -/
example {H J : RetainedCoreHistory.{u}} (hIJ : H.toHistory.IsPrefixOf J.toHistory)
    (ρH ρJ : ℝ → ℝ) (B Q b : ℝ) {ε C1 C2 : ℝ} (hE : H.horizon = 0) (hJB : J.horizon = B)
    (hB : 0 < B) (hb : b ≤ 0) (hρ : ∀ t : ℝ, t ≤ 0 → ρJ t = ρH t)
    (hthr : ∀ t : ℝ, 0 ≤ t → t < B → Q ≤ (ρJ t ^ 2)⁻¹)
    (closed : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Q < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < B →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρJ t ^ 2)⁻¹ < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t) ε C1 C2 x,
          W.capTubeHasNeckChart ε :=
  canonical_step_C11RD hIJ ρH ρJ 0 B Q b hE hJB le_rfl hB hb hρ hthr
    (canonical_vacuous_C11RD H ρH ε C1 C2) closed

end GC.LongTime.Ch11
