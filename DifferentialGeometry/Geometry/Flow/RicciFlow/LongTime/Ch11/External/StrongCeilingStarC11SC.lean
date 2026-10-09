import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.ConstantsTableC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongCeilingC11SC

/-!
# Shared strong ceiling `C1* / C2*` at the uniform engine constants（O-CH11-S16CEIL G1）

`ConstantsTableC12X` 的 shared pair `C1star_C12X C Ccore Cu = max C1⁰ C1S` 与
`C2star_C12X C Ccore Cu = max C2⁰ C2S`，在 `Ccore Cu` 处代入 `StrongCeilingC11SC` 的闭项
`strongCore_C11SC C.epsilon`、`strongWindow_C11SC C.epsilon`：

* `C1ceil_C11SC C`、`C2ceil_C11SC C` 只依赖 `C : ClosedBirthConstants`（及宇宙 `u`），
  在任何 `P / g / B / κ` / native class 之前固定（chain 的所有 state 共享 `C`）；
* 同时支配旧 ceiling `max C.C1s C.Cbirth`、`max C.C2s (max C.Cbirth C.Cgrad)`（canonical 字段的常数）
  与 engine 两个输出式 `strongC1_C11SC C.epsilon C.C1`、`strongC2_C11SC C.epsilon C.C2 C.Cgrad`
  （REVIEW #10）；不假定 `C.C1 ≤ C.C1s` 之类的比较。
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **shared ceiling** `C1* := max (max C.C1s C.Cbirth) (max C.C1 (max Ccore Cu))`，
`Ccore Cu` = uniform engine 的闭项。 -/
def C1ceil_C11SC (C : ClosedBirthConstants) : ℝ :=
  C1star_C12X C (strongCore_C11SC.{u} C.epsilon) (strongWindow_C11SC.{u} C.epsilon)

/-- **shared ceiling** `C2* := max (max C.C2s (max C.Cbirth Cgrad)) (max C.C2 (max (max Ccore Cu)
Cgrad))`。 -/
def C2ceil_C11SC (C : ClosedBirthConstants) : ℝ :=
  C2star_C12X C (strongCore_C11SC.{u} C.epsilon) (strongWindow_C11SC.{u} C.epsilon)

theorem C1ceil_eq_C11SC (C : ClosedBirthConstants) :
    C1ceil_C11SC.{u} C = max (max C.C1s C.Cbirth) (strongC1_C11SC.{u} C.epsilon C.C1) :=
  rfl

theorem C2ceil_eq_C11SC (C : ClosedBirthConstants) :
    C2ceil_C11SC.{u} C = max (max C.C2s (max C.Cbirth (C.Cgrad : ℝ)))
      (strongC2_C11SC.{u} C.epsilon C.C2 C.Cgrad) :=
  rfl

/-- engine 第一个输出式 ≤ shared ceiling（`C1S ≤ C1*`）。 -/
theorem strongC1_le_C1ceil_C11SC (C : ClosedBirthConstants) :
    strongC1_C11SC.{u} C.epsilon C.C1 ≤ C1ceil_C11SC.{u} C :=
  C1S_le_C1star_C12X C _ _

/-- engine 第二个输出式 ≤ shared ceiling（`C2S ≤ C2*`）。 -/
theorem strongC2_le_C2ceil_C11SC (C : ClosedBirthConstants) :
    strongC2_C11SC.{u} C.epsilon C.C2 C.Cgrad ≤ C2ceil_C11SC.{u} C :=
  C2S_le_C2star_C12X C _ _

/-- 旧 ceiling（canonical 字段常数）≤ shared ceiling（`C1⁰ ≤ C1*`）。 -/
theorem oldC1_le_C1ceil_C11SC (C : ClosedBirthConstants) :
    max C.C1s C.Cbirth ≤ C1ceil_C11SC.{u} C :=
  C1zero_le_C1star_C12X C _ _

/-- 旧 ceiling ≤ shared ceiling（`C2⁰ ≤ C2*`）。 -/
theorem oldC2_le_C2ceil_C11SC (C : ClosedBirthConstants) :
    max C.C2s (max C.Cbirth (C.Cgrad : ℝ)) ≤ C2ceil_C11SC.{u} C :=
  C2zero_le_C2star_C12X C _ _

theorem strongCore_le_C1ceil_C11SC (C : ClosedBirthConstants) :
    strongCore_C11SC.{u} C.epsilon ≤ C1ceil_C11SC.{u} C :=
  Ccore_le_C1star_C12X C _ _

theorem strongWindow_le_C1ceil_C11SC (C : ClosedBirthConstants) :
    strongWindow_C11SC.{u} C.epsilon ≤ C1ceil_C11SC.{u} C :=
  Cu_le_C1star_C12X C _ _

theorem strongCore_le_C2ceil_C11SC (C : ClosedBirthConstants) :
    strongCore_C11SC.{u} C.epsilon ≤ C2ceil_C11SC.{u} C :=
  Ccore_le_C2star_C12X C _ _

theorem strongWindow_le_C2ceil_C11SC (C : ClosedBirthConstants) :
    strongWindow_C11SC.{u} C.epsilon ≤ C2ceil_C11SC.{u} C :=
  Cu_le_C2star_C12X C _ _

theorem one_le_C1ceil_C11SC (C : ClosedBirthConstants) : 1 ≤ C1ceil_C11SC.{u} C :=
  one_le_C1star_C12X C _ _

theorem one_le_C2ceil_C11SC (C : ClosedBirthConstants) : 1 ≤ C2ceil_C11SC.{u} C :=
  one_le_C2star_C12X C _ _

/-- shared ceiling 是最小上界形（`C1star_le_of_forall_C12X`）。 -/
theorem C1ceil_le_of_C11SC (C : ClosedBirthConstants) {K : ℝ} (h1 : C.C1s ≤ K)
    (h2 : C.Cbirth ≤ K) (h3 : C.C1 ≤ K) (h4 : strongCore_C11SC.{u} C.epsilon ≤ K)
    (h5 : strongWindow_C11SC.{u} C.epsilon ≤ K) : C1ceil_C11SC.{u} C ≤ K :=
  C1star_le_of_forall_C12X C h1 h2 h3 h4 h5

theorem C2ceil_le_of_C11SC (C : ClosedBirthConstants) {K : ℝ} (h1 : C.C2s ≤ K)
    (h2 : C.Cbirth ≤ K) (h3 : (C.Cgrad : ℝ) ≤ K) (h4 : C.C2 ≤ K)
    (h5 : strongCore_C11SC.{u} C.epsilon ≤ K) (h6 : strongWindow_C11SC.{u} C.epsilon ≤ K) :
    C2ceil_C11SC.{u} C ≤ K :=
  C2star_le_of_forall_C12X C h1 h2 h3 h4 h5 h6

/-- **consumer**：P6 的单一常数 `p6Constant_C12X`（在同一 `Ccore Cu` 处）支配两条 shared ceiling。 -/
example (C : ClosedBirthConstants) (Cε : ℝ) :
    C1ceil_C11SC.{u} C ≤ p6Constant_C12X C (strongCore_C11SC.{u} C.epsilon)
      (strongWindow_C11SC.{u} C.epsilon) Cε ∧
    C2ceil_C11SC.{u} C ≤ p6Constant_C12X C (strongCore_C11SC.{u} C.epsilon)
      (strongWindow_C11SC.{u} C.epsilon) Cε :=
  ⟨C1star_le_p6Constant_C12X C _ _ Cε, C2star_le_p6Constant_C12X C _ _ Cε⟩

end GC.GeneralFlow

end
