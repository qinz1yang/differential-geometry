import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelC11G7B

/-!
# kernel producer 的 selection 常数约束 `hCtt` 付清（O-CH11-KERNB-A6 / W7 G3h，`_A6K`）

R20 基底上 producer 的 `hCtt : Ctime ≤ Ctime′` 落地为 `Γf.Ctime ≤ p6Ctime_C11G7B Γ`（Dt 常数
`Csel = Γf.Ctime`，hgood 常数 `p6Ctime Γ`）。顶层槽带 `FineOf_C11G2 Γf Γ`，其第四分量
`Γf.Ctime ≤ Γ.Ctime`，再接 `Ctime_le_p6Ctime_C11G7B`（`p6Ctime Γ = max Γ.Ctime …`）即得。PROVED，无新前提。
-/

set_option autoImplicit false

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

open GC.GeneralFlow

/-- **`hCtt` ⇐ `FineOf`（`_A6K`，PROVED）**。 -/
theorem fine_Ctime_le_p6Ctime_A6K {Γf Γ : ClosedBirthConstants} (h : FineOf_C11G2.{u} Γf Γ) :
    Γf.Ctime ≤ p6Ctime_C11G7B.{u} Γ :=
  h.2.2.2.trans (Ctime_le_p6Ctime_C11G7B.{u} Γ)

/-- consumer：`coarsenTo` 形（`Ctime` 原样）同样被支配。 -/
example {Γf Γ : ClosedBirthConstants} (h : FineOf_C11G2.{u} Γf Γ) :
    Γf.Ctime ≤ max Γ.Ctime (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ).toNNReal :=
  fine_Ctime_le_p6Ctime_A6K h

end GC.LongTime.Ch11
