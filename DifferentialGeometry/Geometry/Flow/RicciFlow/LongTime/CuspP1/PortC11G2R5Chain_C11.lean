import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.ForwardPhaseScalarContinuationConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.TwoMapGermClosure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.OrientedForwardPhaseDiskConsumer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryArcADP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchExclusion
import DifferentialGeometry.Topology.Maps.TwoMapLocalCoincidentGerms
import DifferentialGeometry.Topology.Maps.ProperRelationFactor
import DifferentialGeometry.Topology.Maps.PuncturedCompactFactor
import DifferentialGeometry.Analysis.Complex.StrictRadius
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.ConformalHarmonic
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HarmonicConformalOrientation

/-!
# S-MY-C11 G2：R5（MY-3 trimmed Morrey 盘唯一性）链条的「已有 / 缺」标注 + 已有部分的 consumer

R5 = `u = q₂∘φ ∨ u = q₂∘φ∘conj`（`φ` 盘共形自同构）+ 三点归一版 `u = q₂`。链条每一步按
`design-MY-route-rev2-20261006.md` R5 / R5-F1 / R5-B 与 `MY-SHAPES-AUDIT` R5 行，在 **C11 整包搬入
后**重新核对；「已有」项都有下面的 `example := @…` 型检查（精确名见各 `example`）。

* 1 已有：R2 trimmed 盘面积极小（`hFarea` 的来源）= `IsMorreyDisk` 的 `affineSubdisk`（R1 G2）。
* 2 已有：MY-2 oriented forward-phase splice（含 `∘ conj` 分支）
  `actual_morrey_oriented_forward_phase_splice`。
* 3 已有：F1a 全闭盘 smooth extension + 全局 Lipschitz、F1b regular boundary arc
  （`morrey_disk_closed_extension_lipschitz_ADP`、`morrey_disk_regular_boundary_arc_ADP`）。
* 4 已有（C11）：regular arc 上 conormal 抵消 / graph Cauchy data（fold 或 Cauchy 匹配）
  `actual_morrey_forward_phase_conormal_cancellation`、`…graph_cauchy_data`、
  `IsMorreyDisk.equal_area_two_sheet_conormal_sum_eq_zero_on_arc`。
* 5 已有（C11）：boundary UC ⇒ open coincidence patch + image germ（local seed）
  `actual_morrey_forward_phase_scalar_continuation`（G1 consumer 抽出 `yStar` 见证）。
* 6 已有（C11）：image germ 相等在 regular interior 极限点保持（closed 一半；只要求两个极限点
  `mfderiv` 单射）`IsMorreyDisk.image_germs_eq_of_regular_interior_limit`。
* 7 已有：open 一半，coincident-germ 集的第一投影是开集
  `isOpen_fst_image_twoMapCoincidentGerms`（要两个映射局部单射）。
* 8 零件已有、**组装缺**：closed + unique 关系 ⇒ 连续 factor `τ`；punctured 邻域 factor 延拓过
  孤立点；contact germ factor（`exists_continuousMap_of_unique_closed_proper_relation`、
  `exists_local_extension_of_punctured_compact_locallyInjective_factor`、
  `exists_continuous_factor_of_leading_projection_contact_germs`）。没有地方构造 coincident-germ
  关系 `S` 并证 unique partner。
* 9 已有：C² + 稠密共形 ⇒ harmonic ⇒ analytic ∨ anti-analytic（orientation）
  `harmonicOnNhd_of_contDiffOn_of_dense_conformalAt`、
  `analyticOnNhd_or_conj_of_harmonicOnNhd_of_eventually_conformalAt`。
* 10 已有：strict radius `‖f‖ ≤ r ⇒ ‖f‖ < r`
  `norm_lt_of_analyticOnNhd_or_conj_of_conformalAt_of_norm_le`；9 → 10 在本文件串成
  `conformal_disk_map_strict_radius_C11`。
* 11 **缺**：R5-B(i) proper-sheet continuation 到整盘（no escape、inverse germ 沿路径延拓、无
  monodromy，经 R3b）。7 的 open 需要全盘局部单射，但 branch 点处不是 immersion；6 的 closed
  需要极限点 rank。
* 12 **缺**：R5-B(ii) degree-one factor rigidity（单值有界全纯因子填 branch ⇒ 边界次数 1 ⇒
  Möbius）。树里没有任何 degree-one / unit-degree 定理。
* 13 **缺**：R5 本体 `u = q₂∘φ ∨ q₂∘φ∘conj` 与三点归一 `u = q₂`（保向圆周同胚固定三点 ⇒ id）。
  三点归一是纯圆周拓扑，可先做；本体依赖 11、12 与 F1（任意 alternate minimizer 的 interior
  branch removal）。

本文件不声称 11–13；它们由 O-MY-R5 另行证明。不加任何新前提，所有假设逐字取自已有定理。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold

namespace GC.LongTime.CuspP1

/-- 逐字型检查（步骤 2）：oriented forward-phase splice。 -/
example := @IMS03Embeddedness.ConsumerAudit.actual_morrey_oriented_forward_phase_splice

/-- 逐字型检查（步骤 3，F1a）：全闭盘 smooth extension 与全局 Lipschitz。 -/
example := @morrey_disk_closed_extension_lipschitz_ADP

/-- 逐字型检查（步骤 3，F1b）：regular boundary arc。 -/
example := @morrey_disk_regular_boundary_arc_ADP

/-- 逐字型检查（步骤 5）：scalar continuation 的 open coincidence patch。 -/
example := @IMS03ConsumerAudit.actual_morrey_forward_phase_scalar_continuation

/-- 逐字型检查（步骤 6）：image germ 相等在 regular interior 极限点保持。 -/
example := @IsMorreyDisk.image_germs_eq_of_regular_interior_limit

/-- 逐字型检查（步骤 7）：coincident-germ 集的第一投影是开集。 -/
example := @isOpen_fst_image_twoMapCoincidentGerms

/-- 逐字型检查（步骤 8）：closed + unique 关系 ⇒ 连续 factor。 -/
example := @exists_continuousMap_of_unique_closed_proper_relation

/-- 逐字型检查（步骤 8）：punctured 邻域上的 factor 延拓过孤立点。 -/
example := @exists_local_extension_of_punctured_compact_locallyInjective_factor

/-- 逐字型检查（步骤 8）：leading-projection contact germs 的 continuous factor。 -/
example := @exists_continuous_factor_of_leading_projection_contact_germs

/-- 逐字型检查（步骤 9）：C² + 稠密共形 ⇒ harmonic。 -/
example := @harmonicOnNhd_of_contDiffOn_of_dense_conformalAt

/-- 逐字型检查（步骤 9）：一个共形 patch 固定 analytic / anti-analytic orientation。 -/
example := @analyticOnNhd_or_conj_of_harmonicOnNhd_of_eventually_conformalAt

/-- 逐字型检查（步骤 10）：analytic ∨ anti-analytic 的 strict radius。 -/
example := @norm_lt_of_analyticOnNhd_or_conj_of_conformalAt_of_norm_le

/-- R5 链条步骤 9 → 10：连通开集 `D` 上 `C²`、在稠密开子集 `Ω` 上共形、有界 `‖f‖ ≤ r` 的映射，
在 `D` 上严格 `‖f‖ < r`（先 harmonic，再由一个共形点固定 orientation，再 strict radius）。 -/
theorem conformal_disk_map_strict_radius_C11 {f : ℂ → ℂ} {D Ω : Set ℂ} {x : ℂ} {r : ℝ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D)
    (hDense : D ⊆ closure Ω) (hf : ContDiffOn ℝ 2 f D)
    (hconf : ∀ z ∈ Ω, ConformalAt f z) (hx : x ∈ Ω)
    (hbound : ∀ z ∈ D, ‖f z‖ ≤ r) : ∀ z ∈ D, ‖f z‖ < r :=
  norm_lt_of_analyticOnNhd_or_conj_of_conformalAt_of_norm_le hD hconn
    (analyticOnNhd_or_conj_of_harmonicOnNhd_of_eventually_conformalAt hD hconn
      (harmonicOnNhd_of_contDiffOn_of_dense_conformalAt hD hΩ hΩD hDense hf hconf) (hΩD hx)
      (Filter.mem_of_superset (hΩ.mem_nhds hx) hconf))
    (hΩD hx) (hconf x hx) hbound

end GC.LongTime.CuspP1
