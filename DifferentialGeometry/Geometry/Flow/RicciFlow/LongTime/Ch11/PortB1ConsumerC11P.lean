import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteObservationContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.RegularEndpointBlock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordAccuracy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalDistanceUpperLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniversalCanonicalContinuation

set_option autoImplicit false

/-!
# S-CH11-PORT-B1 G5：B1 汇总 consumer（`_C11P`）

把 astra B1 批次里**已落地**（verbatim、编译通过）且位于 A12 供给链上的主定理各引用一次。
对应关系（digest `CH11-INTAKE-DIGEST-20261006.md` §1 的 producer 表）：

* `diagonal_*` / `spliceAfter_*`（`CutoffParameterGluing`）：outer tuple 的参数拼接，给
  `radius_antitone` 与 `accuracy_eq`（diagonal `q.delta = δ`）；
* `GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le`（`CutoffRecordAccuracy`）：
  放大 accuracy / neck radius 参数时保留 record 的六个几何数据（larger-ball accuracy 链）；
* `exists_localized_canonical_time_control_point_selection`（`CanonicalTimeControlPointSelection`）：
  `hcanonical` 用 history 形 canonical 供给，选出 time-control 点（survival 链 (i)）；
* `exists_uniform_curvature_bound_*`（`HamiltonIveyCurvatureScale`）、
  `exists_scalar_lt_at_initial_metric`（`InitialScalarUpperBound`）、
  `eventually_ambient_edist_le`（`TerminalDistanceUpperLimit`）、
  `exists_test_volume_lower_of_regular_endpoint_block`（`RegularEndpointBlock`）、
  `exists_closedSlab_extension_of_eventCount_bounded`（`FiniteObservationContinuation`）：
  outer tuple 的体积 / 曲率 / 距离数值输入；
* `exists_universal_canonicalNeighborhoodContinuation`（`UniversalCanonicalContinuation`）。

与 O-CH11-SKEL 供给表（`SurgerySuppliesC11S`）的逐项对齐在 `PortB1SkelAlignC11P`（独立文件，
避免本文件依赖 SKEL 的在途模块）。本文件无新声明。
-/

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- Consumer（真用）：`diagonal` 参数的 neck radius 单调（拼接参数族的相容 + 逐段单调）。 -/
example (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).neckRadius t = (p n).neckRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ))) :
    AntitoneOn (CutoffParameters.diagonal p).neckRadius (Ici 0) :=
  CutoffParameters.diagonal_neckRadius_antitone p hcompat hanti

/-- Consumer（真用）：各层 accuracy 相同则 `diagonal` 的 accuracy 也相同。 -/
example (p : ℕ → CutoffParameters) {δ : ℝ → ℝ} (hdelta : ∀ n, (p n).delta = δ) :
    (CutoffParameters.diagonal p).delta = δ :=
  CutoffParameters.diagonal_delta_eq p hdelta

example : type_of% @CutoffParameters.spliceAfter_neckRadius_antitone :=
  @CutoffParameters.spliceAfter_neckRadius_antitone

example : type_of% @GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le :=
  @GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le

example : type_of% @ObservedHistory.exists_localized_canonical_time_control_point_selection :=
  @ObservedHistory.exists_localized_canonical_time_control_point_selection

example : type_of% @exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion :=
  @exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion

example : type_of% @exists_scalar_lt_at_initial_metric := @exists_scalar_lt_at_initial_metric

example :
    type_of% @OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le :=
  @OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le

example : type_of% @exists_test_volume_lower_of_regular_endpoint_block :=
  @exists_test_volume_lower_of_regular_endpoint_block

example : type_of% @RetainedCoreHistory.exists_closedSlab_extension_of_eventCount_bounded :=
  @RetainedCoreHistory.exists_closedSlab_extension_of_eventCount_bounded

example : type_of% @exists_universal_canonicalNeighborhoodContinuation :=
  @exists_universal_canonicalNeighborhoodContinuation
