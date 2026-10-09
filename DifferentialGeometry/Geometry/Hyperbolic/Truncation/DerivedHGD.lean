import DifferentialGeometry.Geometry.Hyperbolic.Truncation.DepthHGD
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.CaptureHGD
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.TailVolumeHGD

/-!
# HG03 派生项汇总（ch12 D-R3-20 派生项供给；S-HG-DERIV，后缀 `_HGD`）

ch12 D-R3-20：`∀ H, Nonempty (HyperbolicTruncation H)`（`nonempty_hyperbolicTruncation_HG03`）
作显式输入；其派生项 deep-truncation inclusion 与 tail-volume 由本组文件无条件供给：

* depth tower（条件版 / 无条件）：`DepthTowerHGD` / `DepthTowerGlobalHGD`，
  主定理 `exists_depth_tower_HGD`；
* G1 截断深度 ∀ S ≥ 0：`DepthHGD`，`exists_truncation_depth_HGD`；
* G2 紧集捕获 / 度量深度：`CaptureHGD`，`exists_truncation_core_superset_HGD`、
  `exists_truncation_dist_HGD`；
* G3 tail-volume：`TailVolumeHGD`，`exists_truncation_tail_volume_lt_HGD`、
  `exists_core_volume_ge_HGD`。

本文件只放 consumer：一个 `example` 把三类派生项合成 ch12 需要的“深度截断 supply”形状。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- consumer：ch12 对 `HyperbolicTruncation` 的三种用法同时成立——紧集捕获、核心补体积任意小、
深度（核心 = 参考核心 ∪ 深度 `≤ S` 的 collar）。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) :
    (∀ K : Set H.Carrier, IsCompact K → ∃ Tr : HyperbolicTruncation H, K ⊆ range Tr.inclusion) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ Tr : HyperbolicTruncation H,
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion)ᶜ <
        ε) ∧
    (∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      Tr.count = Tr₀.count ∧ range Tr.inclusion =
        range Tr₀.inclusion ∪ ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | p.2.val 0 ≤ S}) := by
  refine ⟨fun K hK => exists_truncation_core_superset_HGD H hK,
    fun ε hε => exists_truncation_tail_volume_lt_HGD H hε, ?_⟩
  obtain ⟨Tr₀, hT⟩ := exists_truncation_depth_HGD H
  refine ⟨Tr₀, fun S hS => ?_⟩
  obtain ⟨Tr, hc, -, hrange⟩ := hT S hS
  exact ⟨Tr, hc, hrange⟩

end DifferentialGeometry.Geometry.Hyperbolic
