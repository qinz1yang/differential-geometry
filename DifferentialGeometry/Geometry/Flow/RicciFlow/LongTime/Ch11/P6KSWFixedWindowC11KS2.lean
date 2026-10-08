import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceSliceTerminalWindow_C11KS2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWShallowConsumerC11KS

/-!
# KSW2 G4 / F7：K-SW 的 LS3 固定窗版——binder X 消去（O-CH11-KSW2，后缀 `_C11KS2`）

KSW G1（`P6KSWShortWindowC11KS`）已把 LS3 `slice_dichotomy_late_Cg_window_P6LS3` 写成固定窗合同
`KSW_C11KS θ₀`（`Bw` 换固定 `θ₀`；非 CWP 分支走 `ShortSLT_C11KS θ₀`，CWP 分支
`capWindow_branch_late_P6L3`，年龄 `θ₀ ≤ 1/2` 单调送入 CWP(1/2) 消费面，D-5），主定理
`ksw_of_shortSLT_C11KS`（PROVISIONAL，binder X = `ShortSLT_C11KS θ₀`）。本文件喂 G3 的
`shortSLT_C11KS2`（F6，R-C11-12 D-4 的正确改造：Age_β + 三处修改）：
* `ksw_C11KS2`：`0 < θ₀ ≤ 1/2` ⇒ `KSW_C11KS θ₀`（无 binder）；
* `ksw_pos_C11KS2`：任意 `θ > 0` ⇒ `KSW_C11KS θ`（`θ ∧ 1/2` 再 `KSW_C11KS.mono`；覆盖 SHALLOW 的
  `θ_* = 1/(2 max(Ctime, 1))`）。
consumer：KSW G1 的 SHALLOW T1 接线 `ObservedHistory.shallowSliceRC_of_ksw_short_C11KS` 的 `hK` 由
`ksw_C11KS2` 付清（剩余前提 = 固定短窗 U 侧供给 `hUVC` 等，属 PICKBALL / SHALLOW I1，D-6 / D-9(2)）。
不声称闭合：hanchor0 仍需 top/terminal adapter（D-8），U 侧 picked-ball/chain 数据另付（D-6）。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **K-SW（LS3 固定窗版，`_C11KS2`，G4，PROVED）**：`0 < θ₀ ≤ 1/2` ⇒ `KSW_C11KS θ₀`
（= `ksw_of_shortSLT_C11KS` 喂 `shortSLT_C11KS2`；binder X 消去）。 -/
theorem ksw_C11KS2 {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) : KSW_C11KS.{u} θ₀ :=
  ksw_of_shortSLT_C11KS hθ₀ hθ₀2 (shortSLT_C11KS2 hθ₀)

/-- **K-SW 对任意正窗（`_C11KS2`）**：`0 < θ` ⇒ `KSW_C11KS θ`（取 `min θ (1/2)` 再单调）。 -/
theorem ksw_pos_C11KS2 {θ : ℝ} (hθ : 0 < θ) : KSW_C11KS.{u} θ :=
  KSW_C11KS.mono (min_le_left θ (1 / 2)) (ksw_C11KS2 (lt_min hθ one_half_pos) (min_le_right _ _))

/-- consumer：SHALLOW T1 接线 `shallowSliceRC_of_ksw_short_C11KS` 的 K-SW binder `hK` 由 `ksw_C11KS2`
付清（`0 < θ₀ ≤ 1/2`）。 -/
example {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) :=
  @ObservedHistory.shallowSliceRC_of_ksw_short_C11KS.{u} θ₀ (ksw_C11KS2 hθ₀ hθ₀2)

/-- consumer：核心形 `hsliceR_lateHI_core_short_C11KS` 同样消去 `hK`（任意 `θ₀ > 0`）。 -/
example {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :=
  @ObservedHistory.hsliceR_lateHI_core_short_C11KS.{u} θ₀ (ksw_pos_C11KS2 hθ₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
