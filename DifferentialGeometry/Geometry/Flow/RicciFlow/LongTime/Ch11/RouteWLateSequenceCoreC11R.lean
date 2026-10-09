import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWLateSequenceWA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A09OfEnhancedC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.A13OfEnhancedC11M

/-!
# A12′ re-point 的 core（O-CH11-REPOINT G1a；rev1 = O-CH11-REPOINT2，2026-10-07）

Route W consumer 链（`CuspP1/RouteWLateSequenceWA2.lean`）的 L1/L2，证明体逐字复制，只做两处替换：

* A12 `exists_surgery_with_decaying_accuracy` 换成 A12′ 形的参数 `hA12'`（结论里是 enhanced
  admissibility `Ch11.hasEnhancedAdmissibilityFull_C11F F δ`）；
* L1 的 binder 是 enhanced profile `henh`：A09 `exists_late_cut_family` 与 Route W G_final 的
  `hadm` 由投影 `hasAnalyticAdmissibility_of_full_C11F` 提取，A13 `late_derivative_tests_of_flow`
  直接吃 `henh`（rev1：REPOINT2 把 tracked A13 改成吃 enhanced profile；原版本对任意 enhanced
  谓词与投影的参数化因此特化为 `hasEnhancedAdmissibility_C11E`；M2-pre（O-CH11-MERGE）再换成 v2
  `hasEnhancedAdmissibilityFull_C11F`，tracked A13 与 A12′ 同步）。

另含 R-END1 的 END-RFL：`RouteWLateSequenceWA2.lean` 四层中间两层与 `LateDecomposition` 原件类型逐字
相同的 `rfl` 回归 `example`。见 `docs/geometrization/chapter8/REPOINT-A12enh-20261006.md`。
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

/-- L1 core：`hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA` 的证明体；A09 / G_final 的
`hadm` 由 enhanced profile `henh` 投影提取，A13 直接吃 `henh`。 -/
theorem hasLateSequenceTests_of_thick_thin_and_obstruction_of_enhanced_C11R
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := hasAnalyticAdmissibility_of_full_C11F henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := exists_late_cut_family_of_enhanced_C11M F K hK δ henh hdec slices htimes
    hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (late_derivative_tests_of_flow_of_enhanced_C11M F K hK δ henh hdec slices htimes
      hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    CuspP1.hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j
      ((le_max_right _ _).trans hj) C⟩

/-- L2 core（enhanced 结论）：由 A12′ 形的 `hA12'` 得 surgery，保留 enhanced profile
（供直接吃 P1–P6 字段的下游，例如 ch12 的 A13 binder）并给出 late sequence tests。 -/
theorem exists_enhanced_surgery_with_late_sequence_tests_of_enhanced_C11R
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hA12' : ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasEnhancedAdmissibilityFull_C11F F δ)
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasEnhancedAdmissibilityFull_C11F F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile⟩ := hA12'
  exact ⟨δ, F, ha, hd, hprofile,
    hasLateSequenceTests_of_thick_thin_and_obstruction_of_enhanced_C11R F K hK δ hprofile hd⟩

/-- L2 core（原件结论形）：`exists_admissible_surgery_with_late_sequence_tests` 的 A12′ 版，结论里的
`hasAnalyticAdmissibility F δ` 由 enhanced profile 投影得到。 -/
theorem exists_admissible_surgery_with_late_sequence_tests_of_enhanced_C11R
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hA12' : ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasEnhancedAdmissibilityFull_C11F F δ)
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile, ht⟩ :=
    exists_enhanced_surgery_with_late_sequence_tests_of_enhanced_C11R P g hA12' K hK
  exact ⟨δ, F, ha, hd, hasAnalyticAdmissibility_of_full_C11F hprofile, ht⟩

/-- consumer（rev1）：A12′ admission 喂入 core L2，复现 `LateDecomposition` 原件
`exists_admissible_surgery_with_late_sequence_tests` 的类型。 -/
example : AdmissibleLateSequenceExistenceStatement.{u} :=
  fun P g K hK => exists_admissible_surgery_with_late_sequence_tests_of_enhanced_C11R P g
    (exists_surgery_with_decaying_accuracy_enhanced P g) K hK

/-! ### END-RFL（R-END1）：`RouteWLateSequenceWA2.lean` 中间两层与原件类型逐字相同 -/

example : type_of% @CuspP1.exists_admissible_surgery_with_late_sequence_tests_routeW_WA.{u} =
    AdmissibleLateSequenceExistenceStatement.{u} := rfl

example : type_of% @CuspP1.exists_surgery_with_late_sequence_tests_routeW_WA.{u} =
    SurgeryLateSequenceExistenceStatement.{u} := rfl

end GC.LongTime.Ch11
