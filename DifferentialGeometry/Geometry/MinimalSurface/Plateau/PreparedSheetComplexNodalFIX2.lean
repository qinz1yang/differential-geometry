import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# S-MY-FIX2：S8 `nodal` 的 Ico 版定义 `IsCollisionNodal_FIX2`（`_FIX2`）

R-MY3 / D-R-MY3-12：S-MY-FIX 的 `IsCollisionNodal_FIX` 与 R3a-ω 的逐字定义同样有量词错误——
零集覆盖与 `MapsTo` 用闭区间 `Icc 0 ρ`，外端点 `Γ m ρ` 仍在开邻域内部，那里是 regular zero（transverse 碰撞）
零曲线必须继续延伸，被 `w = xy` 型例子反驳。修正（与 S-MY-R3AW 的 `IsNodalHalfArcsAt_R3AW` 同形）：
`MapsTo` 与 collision-set 覆盖用 `Ico 0 ρ`；`C¹` / `InjOn` / `HasDerivWithinAt` / 初始方向 / 两两只在 `z` 相交
仍在 `Icc 0 ρ`；transversality 条款用 `Ioo 0 ρ`（外端点不在 `ball z ρ` 里，没有可用的 `w'` 邻居）。

这是 **pairwise two-sheet data**：只记录 `z` 邻域的 sheet 与 `w` 邻域的 sheet 之间的碰撞（不是总碰撞集），
所以 cover lift 后“仍碰撞的点对局部关系与横截性不变”（部分点对被 cover 分开）是对的。
本文件只含这个 def（无其他声明）；notion 本体与 fixtures 在 `PreparedSheetComplex{Notion,Local2,Curve2}FIX2.lean`。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

universe u

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- 碰撞对 `(z, w)`（`F z = F w`，`z ≠ w`）的 two-sheet nodal 数据，**Ico 版**：`z` 附近（与 `w` 附近的 sheet
相交的）源碰撞集是 `2k` 条 embedded `C¹` half-arcs（`Γ m` 在 `[0, ρ]` 上 `C¹`、单射、`Γ m 0 = z`，
初始方向 `v m ≠ 0` 两两不同射线、两两只在 `z` 相交），碰撞集只被 `Ico 0 ρ` 上的弧点覆盖（外端点 `Γ m ρ`
不属于集合）；中心外每个碰撞都 transverse（R3a 的 regular zeros，`r ∈ Ioo 0 ρ`）。 -/
def IsCollisionNodal_FIX2 (F : ℂ → M) (z w : ℂ) : Prop :=
  ∃ (ρ : ℝ) (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ), 0 < ρ ∧ 1 ≤ k ∧
    Disjoint (Metric.ball z ρ) (Metric.ball w ρ) ∧
    Metric.ball z ρ ⊆ Metric.ball 0 1 ∧ Metric.ball w ρ ⊆ Metric.ball 0 1 ∧
    InjOn F (Metric.ball z ρ) ∧ InjOn F (Metric.ball w ρ) ∧
    (∀ m, Γ m 0 = z ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
      HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) (Metric.ball z ρ)) ∧
    (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
      ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
    (∀ z' ∈ Metric.ball z ρ,
      (∃ w' ∈ Metric.ball w ρ, F z' = F w') ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z' = Γ m r) ∧
    ∀ m, ∀ r ∈ Ioo 0 ρ, ∀ w' ∈ Metric.ball w ρ, F (Γ m r) = F w' →
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (Γ m r)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w')))

end Generic

end DifferentialGeometry.Geometry
