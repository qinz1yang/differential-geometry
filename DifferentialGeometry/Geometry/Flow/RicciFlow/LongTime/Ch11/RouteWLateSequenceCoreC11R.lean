import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWLateSequenceWA2

/-!
# A12′ re-point 的参数化 core（O-CH11-REPOINT G1a，后缀 `_C11R`）

Route W consumer 链（`CuspP1/RouteWLateSequenceWA2.lean`）的下面两层，证明体逐字复制，只做两处替换：

* A12 `exists_surgery_with_decaying_accuracy` 换成显式参数 `hA12'`：任意 enhanced admissibility
  `Enh F δ` 形的 surgery 存在性（A12′ 冻结前的显式性质参数形式，COMMON-CH8「关于显式假设」）；
* A09 `exists_late_cut_family`、A13 `late_derivative_tests_of_flow` 与 Route W G_final 的前提
  `hadm : hasAnalyticAdmissibility F δ` 由 enhanced profile 经投影 `proj` 直接提取。

`Enh := hasEnhancedAdmissibility_C11E`、`proj :=` O-CH11-PROF 的 A12′ ⇒ A12 投影、`hA12' :=` A12′ 时即
得闭合的 `_C11R` 四层（`Ch11/RouteWLateSequenceC11R.lean`）。本文件与 PROF 的字段表无关，只用投影。

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

/-- L1 core：`hasLateSequenceTests_of_thick_thin_and_obstruction_routeW_WA` 的证明体，A09 / A13 /
G_final 的 `hadm` 由 enhanced profile `henh` 经 `proj` 提取。 -/
theorem hasLateSequenceTests_of_thick_thin_and_obstruction_of_enhanced_C11R
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {Enh : GC.Interface.RawSurgery P g → (ℝ → ℝ) → Prop}
    (proj : ∀ (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ),
      Enh F δ → hasAnalyticAdmissibility F δ)
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (henh : Enh F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    hasLateSequenceTests F K := by
  have hadm : hasAnalyticAdmissibility F δ := proj F δ henh
  intro slices htimes hnonempty
  obtain ⟨L⟩ := exists_late_cut_family F K hK δ hadm hdec slices htimes hnonempty
  obtain ⟨A, hA, htests⟩ := L.exists_late_tests_of_derivative_bounds
    (late_derivative_tests_of_flow F K hK δ hadm hdec slices htimes hnonempty L)
  refine ⟨A, hA, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := htests w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  exact ⟨L.decomposition j C, hn j ((le_max_left _ _).trans hj) C,
    CuspP1.hasAttainedExteriorAreaObstructionAfter_of_routeW_final_WA K hK δ hadm hdec L j
      ((le_max_right _ _).trans hj) C⟩

/-- L2 core（enhanced 结论）：由 A12′ 形的 `hA12'` 得 surgery，保留 enhanced profile `Enh F δ`
（供将来直接吃 P1–P6 字段的下游，例如 ch12 的 A13 binder）并给出 late sequence tests。 -/
theorem exists_enhanced_surgery_with_late_sequence_tests_of_enhanced_C11R
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    {Enh : GC.Interface.RawSurgery P g → (ℝ → ℝ) → Prop}
    (proj : ∀ (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ),
      Enh F δ → hasAnalyticAdmissibility F δ)
    (hA12' : ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      Enh F δ)
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      Enh F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile⟩ := hA12'
  exact ⟨δ, F, ha, hd, hprofile,
    hasLateSequenceTests_of_thick_thin_and_obstruction_of_enhanced_C11R proj F K hK δ hprofile hd⟩

/-- L2 core（原件结论形）：`exists_admissible_surgery_with_late_sequence_tests` 的 A12′ 版，结论里的
`hasAnalyticAdmissibility F δ` 由 `proj` 从 enhanced profile 投影得到。 -/
theorem exists_admissible_surgery_with_late_sequence_tests_of_enhanced_C11R
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    {Enh : GC.Interface.RawSurgery P g → (ℝ → ℝ) → Prop}
    (proj : ∀ (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ),
      Enh F δ → hasAnalyticAdmissibility F δ)
    (hA12' : ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      Enh F δ)
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ ∧ hasLateSequenceTests F K := by
  obtain ⟨δ, F, ha, hd, hprofile, ht⟩ :=
    exists_enhanced_surgery_with_late_sequence_tests_of_enhanced_C11R P g proj hA12' K hK
  exact ⟨δ, F, ha, hd, proj F δ hprofile, ht⟩

/-- consumer：trivial enhancement（`Enh := hasAnalyticAdmissibility`、`proj := id`、`hA12' := A12`）
复现 `LateDecomposition` 原件 `exists_admissible_surgery_with_late_sequence_tests` 的类型。 -/
example : type_of% @exists_admissible_surgery_with_late_sequence_tests.{u} :=
  fun P g K hK => exists_admissible_surgery_with_late_sequence_tests_of_enhanced_C11R P g
    (fun _ _ h => h) (exists_surgery_with_decaying_accuracy P g) K hK

/-! ### END-RFL（R-END1）：`RouteWLateSequenceWA2.lean` 中间两层与原件类型逐字相同 -/

example : type_of% @CuspP1.exists_admissible_surgery_with_late_sequence_tests_routeW_WA.{u} =
    type_of% @exists_admissible_surgery_with_late_sequence_tests.{u} := rfl

example : type_of% @CuspP1.exists_surgery_with_late_sequence_tests_routeW_WA.{u} =
    type_of% @exists_surgery_with_late_sequence_tests.{u} := rfl

end GC.LongTime.Ch11
