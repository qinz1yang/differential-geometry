import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RouteWLateSequenceCoreC11R
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12EnhancedC11E

/-!
# A12′ 的端点 re-point consumer（O-CH11-REPOINT G1，后缀 `_C11R`）

Route W 的四层 consumer（`CuspP1/RouteWLateSequenceWA2.lean`）的 `_C11R` 副本，只把 A12
`exists_surgery_with_decaying_accuracy` 换成 A12′，其余逐字。A12′ 按 O-CH11-PROF G2 是 `Prop`
`A12EnhancedFullStatement_C11F`（车道文件不得含占位证明；admission
`exists_surgery_with_decaying_accuracy_enhanced` 由 INT 在用户 GO 后落入 tracked 文件），所以 L2–L4
以显式参数 `hA12' : A12EnhancedFullStatement_C11F` 接收它；端点把 admission 传进来即可（一行）。

* L1 `hasLateSequenceTests_of_thick_thin_and_obstruction_C11R`：binder `hadm` 换成 enhanced profile
  `henh : hasEnhancedAdmissibilityFull_C11F F δ`；A09 / Route W G_final 的 `hadm` 在调用处由投影
  `hasAnalyticAdmissibility_of_full_C11F` 提取，A13 直接吃 `henh`（rev1 = REPOINT2，tracked A13
  改吃 enhanced profile 之后；`RouteWLateSequenceCoreC11R` 的 core）；
* L2 `exists_admissible_surgery_with_late_sequence_tests_C11R`、L3
  `exists_surgery_with_late_sequence_tests_C11R`（`GeometrizationEND0` 的 re-point 点）、L4
  `geometrizes_of_metric_C11R`（`Geometrization` 的 re-point 点）：喂入 `hA12'` 后类型与
  `LateDecomposition` 原件逐字相同（文件末 `rfl`）。

直接 admission（walker）：本文件无直接 admission（A09 / A13 经 `WR/{A09,A13}OfEnhancedC11M` 由 ch12
终端证出：REPOINT3 M4 `a1a0c029e9` 已把 core 的调用点改指 wrapper）；端点喂入 A12′ admission 后，
端点直接 admission = {A12′}（MGL 在 INT 套用 ch12 的真证明块 `exists_thick_ball_volume_lower_C12X`
之后为 0 外部项；套用前另有 MGL）。端点改法见 `docs/geometrization/chapter8/REPOINT-A12enh-20261006.md`，
接线见 `docs/geometrization/chapter8/out/ENDPOINT-AFTER-CH12-20261007.md`。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.MinimalSurface
open GC.Endpoint GC.GraphManifold GC.LongTime Set
open GC.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- L1：A09 / G_final 的前提由 enhanced profile 投影提取，A13 直接吃 enhanced profile。 -/
theorem hasLateSequenceTests_of_thick_thin_and_obstruction_C11R
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K :=
  hasLateSequenceTests_of_thick_thin_and_obstruction_of_enhanced_C11R F K hK δ henh hdec

/-- L2 的 enhanced 结论版：A12′ 的 surgery 连同 enhanced profile 与 late sequence tests。 -/
theorem exists_enhanced_surgery_with_late_sequence_tests_C11R
    (hA12' : A12EnhancedFullStatement_C11F.{u})
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasEnhancedAdmissibilityFull_C11F F δ ∧ hasLateSequenceTests F K :=
  exists_enhanced_surgery_with_late_sequence_tests_of_enhanced_C11R P g (hA12' P g) K hK

/-- L2：`exists_admissible_surgery_with_late_sequence_tests` 的 A12′ 版（A12 → A12′）。 -/
theorem exists_admissible_surgery_with_late_sequence_tests_C11R
    (hA12' : A12EnhancedFullStatement_C11F.{u})
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile⟩ := hA12' P g
  exact ⟨δ, F, ha, hd, hasAnalyticAdmissibility_of_full_C11F hprofile,
    hasLateSequenceTests_of_thick_thin_and_obstruction_C11R F K hK δ hprofile hd⟩

/-- L3：`exists_surgery_with_late_sequence_tests` 的 A12′ 版（`GeometrizationEND0` 的 re-point 点）。 -/
theorem exists_surgery_with_late_sequence_tests_C11R
    (hA12' : A12EnhancedFullStatement_C11F.{u})
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ t : ℝ, 0 ≤ t → 0 < δ t ∧ δ t < 1) ∧
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasCommonNeckAccuracy F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, ⟨H⟩, ht⟩ :=
    exists_admissible_surgery_with_late_sequence_tests_C11R hA12' P g K hK
  exact ⟨δ, F, H.commonNeckAccuracy.bounds, ha, hd, H.commonNeckAccuracy, ht⟩

/-- L4：`geometrizes_of_metric` 的 A12′ 版（`Geometrization.lean` 的 re-point 点）。 -/
theorem geometrizes_of_metric_C11R
    (hA12' : A12EnhancedFullStatement_C11F.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric) :
    Geometrizes M := by
  obtain ⟨δ, F, _, _, _, _, tests⟩ := exists_surgery_with_late_sequence_tests_C11R hA12'
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g
    lateDerivativeOrder le_rfl
  exact geometrizes_of_late_slice_supply M F
    (components_geometrize_of_late_sequence_tests F lateDerivativeOrder
      staticDerivativeOrder_le_lateDerivativeOrder tests)

/-! ### 型对齐：喂入 A12′ 后 L2–L4 与 `LateDecomposition` 原件类型逐字相同 -/

example (hA12' : A12EnhancedFullStatement_C11F.{u}) :
    type_of% (exists_admissible_surgery_with_late_sequence_tests_C11R hA12') =
      AdmissibleLateSequenceExistenceStatement.{u} := rfl

example (hA12' : A12EnhancedFullStatement_C11F.{u}) :
    type_of% (exists_surgery_with_late_sequence_tests_C11R hA12') =
      SurgeryLateSequenceExistenceStatement.{u} := rfl

example (hA12' : A12EnhancedFullStatement_C11F.{u}) :
    type_of% (geometrizes_of_metric_C11R hA12') = GeometrizationFromMetricStatement.{u} := rfl

/-- consumer：re-point 后 `GC.Endpoint.geometrization` 的证明体（`Geometrization.lean` 改一行的
dry run；A12′ admission 以 `hA12'` 代入）。 -/
example (hA12' : A12EnhancedFullStatement_C11F.{u}) (M : ConnectedClosedOrientedManifold.{u} 3) :
    Geometrizes M := by
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric_of_compact (𝓡 3) (M := M.Carrier)
  exact GC.LongTime.Ch11.geometrizes_of_metric_C11R hA12' M g

end GC.LongTime.Ch11
