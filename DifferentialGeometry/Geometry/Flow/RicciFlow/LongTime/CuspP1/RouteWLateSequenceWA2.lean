import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWFinalWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12Enhanced
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A09OfEnhancedC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A13OfEnhancedC11M

/-!
# Route W 的 re-point consumer（O-W-ASSEMBLY-2 G_consumer，后缀 `_WA`）

`LateDecomposition.lean` 里从 `hasExteriorAreaObstructionAfter_of_producers`（经 A08/A10/A11/A14）到
`geometrizes_of_metric` 的四个定理，逐字复制证明体，只把 obstruction 一行换成 G_final
`hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA`：

* `hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA`（直接 admission 恰为
  `exists_late_cut_family`（A09）、`late_derivative_tests_of_flow`（A13））；
* `exists_admissible_surgery_with_late_sequence_tests_routeW_WA`、
  `exists_surgery_with_late_sequence_tests_routeW_WA`、`geometrizes_of_metric_routeW_WA`（再加
  A12′ `exists_surgery_with_decaying_accuracy_enhanced`；REPOINT2 前为 A12）。

REPOINT2（2026-10-07）：L1 的 binder 改为 enhanced profile `henh`，A09 / G_final 经投影
`Ch11.hasAnalyticAdmissibility_of_full_C11F`，A13 直接吃 `henh`；L2 调 A12′。

为什么不直接改 `LateDecomposition.lean`：`hasAttainedExteriorAreaObstructionAfter` 定义在该文件里，Route W
链（`ObstructionOfIncompressible_RB` 起）import 它，所以 `LateDecomposition` 不能反向 import Route W
（循环）。re-point 因此落在下游 `Geometrization.lean`（`geometrization` 的证明体一行）与
`GeometrizationEND0.lean`（`geometrizes_of_metric_END0` 一行），端点声明不变（D-R5-16）；见
`docs/geometrization/chapter8/REPOINT-RouteW-20261006.md`。
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

namespace GC.LongTime.CuspP1

universe u

/-- `hasLateSequenceTests_of_thick_thin_and_obstruction` 的证明体，obstruction 一行换成 G_final。 -/
theorem hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := Ch11.hasAnalyticAdmissibility_of_full_C11F henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := Ch11.exists_late_cut_family_of_enhanced_C11M F K hK δ henh hdec slices htimes
    hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (Ch11.late_derivative_tests_of_flow_of_enhanced_C11M F K hK δ henh hdec slices htimes
      hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j
      ((le_max_right _ _).trans hj) C⟩

/-- `exists_admissible_surgery_with_late_sequence_tests` 的 Route W 版。 -/
theorem exists_admissible_surgery_with_late_sequence_tests_routeW_WA
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile⟩ := exists_surgery_with_decaying_accuracy_enhanced P g
  exact ⟨δ, F, ha, hd, Ch11.hasAnalyticAdmissibility_of_full_C11F hprofile,
    hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA F K hK δ hprofile hd⟩

/-- `exists_surgery_with_late_sequence_tests` 的 Route W 版（`GeometrizationEND0` 的 re-point 点）。 -/
theorem exists_surgery_with_late_sequence_tests_routeW_WA
    (P : OrientedThreeStage.{u}) (g : P.Metric) (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ t : ℝ, 0 ≤ t → 0 < δ t ∧ δ t < 1) ∧
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasCommonNeckAccuracy F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, ⟨H⟩, ht⟩ :=
    exists_admissible_surgery_with_late_sequence_tests_routeW_WA P g K hK
  exact ⟨δ, F, H.commonNeckAccuracy.bounds, ha, hd, H.commonNeckAccuracy, ht⟩

/-- `geometrizes_of_metric` 的 Route W 版（`Geometrization.lean` 的 re-point 点）。 -/
theorem geometrizes_of_metric_routeW_WA
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric) :
    Geometrizes M := by
  obtain ⟨δ, F, _, _, _, _, tests⟩ := exists_surgery_with_late_sequence_tests_routeW_WA
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g
    lateDerivativeOrder le_rfl
  exact geometrizes_of_late_slice_supply M F
    (components_geometrize_of_late_sequence_tests F lateDerivativeOrder
      staticDerivativeOrder_le_lateDerivativeOrder tests)

/-- 型对齐：Route W 版与 `LateDecomposition` 原件陈述逐字相同。 -/
example : type_of% @hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA.{u} =
    LateSequenceTestsFromEnhancedStatement.{u} := rfl

example : type_of% @geometrizes_of_metric_routeW_WA.{u} = GeometrizationFromMetricStatement.{u} :=
  rfl

end GC.LongTime.CuspP1
