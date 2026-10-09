import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.MGLProofC12X

set_option autoImplicit false

/-!
# External geometric input `hMGL`（admission；lead 裁定 U4，O-CH11-MERGE M4）

ch12 终端 `A09_of_supplies_S153`（`LT/Ch12/A09Final_S153.lean:110`）的外部输入 `hMGL`
（Margulis 型 thick 点的一致 ball-volume 下界；R3 D-R3-21，归一化 −1/4）。陈述逐字 = ch12
`CH12-MERGE-HANDOVER.md` §1.3 的 `hMGL` binder（see CH12-MERGE-HANDOVER §3：本树无 producer；
零件 `Margulis.exists_margulis_constant`、`exists_compact_thickPart_core` 已在树，缺"每个有限体积 H 有一致
thick 点"与"thick ⇒ `ballVolume B(y, 2)` 下界"两段，真证明估 0.5–0.9k 行）。
**external geometric input, see CH12-MERGE-HANDOVER §3**：唯一的 `sorry`；A09 的 REPOINT3 wrapper
`Ch11.exists_late_cut_family_of_enhanced_C11M` 消费它，端点直接 admission 预期 = {A12′, 本定理}。

**C12X 更新**：`sorry` 已由真证明 `exists_thick_ball_volume_lower_C12X`（`MGLProofC12X.lean`：
O-C12X-MGLA 的一致 thick 点 + O-C12X-MGLB 的 thick ⇒ ball-volume 下界，`a = 1`）消去；
本定理现为 THEOREM（standard axioms only），不再是 admission。
-/

noncomputable section

open DifferentialGeometry
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace GC.LongTime.Ch11.External

universe u

/-- **hMGL**（原 external geometric input，see CH12-MERGE-HANDOVER §3；C12X 起为 THEOREM）。 -/
theorem exists_thick_ball_volume_lower_MGL :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ H : FiniteVolumeHyperbolicModel.{u}, ∃ x : H.Carrier,
      ∀ y ∈ riemannianBallOf H.metric x a, ENNReal.ofReal c ≤ ballVolume H.metric y 2 := by
  exact exists_thick_ball_volume_lower_C12X

end GC.LongTime.Ch11.External
