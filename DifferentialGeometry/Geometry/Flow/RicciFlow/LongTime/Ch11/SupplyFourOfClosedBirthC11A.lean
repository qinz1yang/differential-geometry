import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SuppliesOfAstraC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState

set_option autoImplicit false

/-!
# O-CH11-ASM (G5)：S4 直接由已落地的 astra `ClosedBirthConstants` 给出

`GC.GeneralFlow.ClosedBirthConstants`（`SH/PreparedSpatialState`，O-CH11-FIX3B G3 落地：
`PreparedSpatialStatePortC11P` + 原路径 shim）现在可以 import。astra narrow tuple 用的常数是
`ε = C.epsilon`、`C1 = max C.C1s C.Cbirth`、`C2 = max C.C2s (max C.Cbirth Cgrad)`；这里把 S4
`CanonicalConstantsSupply_C11S` 与 P4 型的 cone 条款 `ε ≤ coneAccuracy` 直接从结构字段读出，
不再需要把它们当作 W1 的 binder。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

/-- **S4 ⇐ `ClosedBirthConstants`**（astra tuple 的常数组合）。 -/
theorem canonicalConstantsSupply_of_closedBirthConstants_C11A
    (C : GC.GeneralFlow.ClosedBirthConstants) :
    CanonicalConstantsSupply_C11S C.epsilon (max C.C1s C.Cbirth)
      (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) :=
  supply4_of_astra_C11A (C.Cgrad : ℝ) C.epsilon_pos C.epsilon_small C.C1s_ge_one C.C2s_ge_one

/-- S4 加 P4 型 cone 条款：`C.epsilon ≤ coneAccuracy`（= ch12 `εKL70_O2`，DIGEST §0.6）。 -/
theorem canonicalConstantsSupply_cone_of_closedBirthConstants_C11A
    (C : GC.GeneralFlow.ClosedBirthConstants) :
    CanonicalConstantsSupply_C11S C.epsilon (max C.C1s C.Cbirth)
      (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) ∧ C.epsilon ≤ coneAccuracy :=
  ⟨canonicalConstantsSupply_of_closedBirthConstants_C11A C, C.epsilon_cone⟩

/-- consumer：任一 `ClosedBirthConstants` 给出 G3 主定理 `hflow` 的第一个合取项所需的常数组。 -/
example (C : GC.GeneralFlow.ClosedBirthConstants) :
    ∃ ε C1 C2 : ℝ, CanonicalConstantsSupply_C11S ε C1 C2 ∧ ε ≤ coneAccuracy :=
  ⟨_, _, _, canonicalConstantsSupply_cone_of_closedBirthConstants_C11A C⟩

end GC.LongTime.Ch11
