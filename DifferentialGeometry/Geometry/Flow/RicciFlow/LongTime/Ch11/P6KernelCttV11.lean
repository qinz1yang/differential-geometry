import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelC11G7B

set_option autoImplicit false

/-!
# R33 `hCtt` 支配引理（O-CH11-W10，后缀 `_V11`）

KERNB-A6 W7 G3 的 selection 常数行 `hCtt : Ctime ≤ Ctime′` 在 R20 基底的读法是
`Γf.Ctime ≤ p6Ctime_C11G7B Γ`。它由两级关系 `FineOf_C11G2 Γf Γ`（第四合取 `Γf.Ctime ≤ Γ.Ctime`）与
`Ctime_le_p6Ctime_C11G7B`（`p6Ctime Γ = max Γ.Ctime …`）直接得出：不需要取 max 的 ceiling 孪生。
`FineOf_C11G2 Γf Γ` 在所有顶层槽 env 中是前提 `hfine`。PROVED，无 binder。
-/

noncomputable section

open GC.GeneralFlow (ClosedBirthConstants)
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **`hCtt` 于 R20 基底（`_V11`）**：`FineOf Γf Γ ⇒ Γf.Ctime ≤ p6Ctime Γ`。 -/
theorem ctime_le_p6Ctime_of_fine_V11 {Γf Γ : ClosedBirthConstants}
    (hfine : FineOf_C11G2.{u} Γf Γ) : Γf.Ctime ≤ p6Ctime_C11G7B.{u} Γ :=
  hfine.2.2.2.trans (Ctime_le_p6Ctime_C11G7B.{u} Γ)

end GC.LongTime.Ch11
