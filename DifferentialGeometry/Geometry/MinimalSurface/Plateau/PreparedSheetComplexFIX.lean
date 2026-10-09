import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary

/-!
# S-MY-FIX G1：R9 新模型 `IsPreparedSheetComplex`（22 字段）的定义（`_FIX`）

D-R-MY2-13：旧 `T.space = closedBall 0 1`（直线 simplicial complex）不可满足（圆周点都是 extreme point）。
新模型：`T` 是有限**平面 polygonal disk**（`T.space` 任意多边形），显式 `α : ℂ → ℂ` 在 `|T|` 上是到 `D̄` 的
连续双射（边界对边界），`h ∘ |φ| = f ∘ α`。`α` **不**要求 bi-Lipschitz：只要（单向）Lipschitz、在每个
2-面去掉顶点后 `C^∞` 且导数可逆（顶点处允许 cusp 型退化）。下游要的几何作为**字段保存**（D-13 清单）：
R8 的闭盘 rank + smooth extension、collar；relative 3-thickening `A`（组合 3-流形）；碰撞集是子复形；
非横截碰撞源点是顶点；每个碰撞对的 two-sheet nodal 数据。

本文件只含 **notion**（data + invariants 的 Prop），所有字段是显式 Prop，不含新 admission；
“存在性”（R9 producer，analytic）**不在此**；非空性证据是 `PreparedSheetComplexFlatFIX.lean`
里的 `flatDisk_prepared_FIX`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 碰撞对 `(z, w)`（`F z = F w`，`z ≠ w`）的 two-sheet nodal 数据：`z` 附近（`w` 附近的 sheet 与之相交的）
源碰撞集是 `2k` 条 embedded `C¹` half-arcs，初始切向两两不同射线、两两只在 `z` 相交；中心外每个碰撞都
transverse（R3a 的 regular zeros）。这是 R3a-ω 在一对 sheet 上的输出形，pr 局部微分同胚下逐字传给 lift。 -/
def IsCollisionNodal_FIX (F : ℂ → M) (z w : ℂ) : Prop :=
  ∃ (ρ : ℝ) (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ), 0 < ρ ∧ 1 ≤ k ∧
    Disjoint (Metric.ball z ρ) (Metric.ball w ρ) ∧
    Metric.ball z ρ ⊆ Metric.ball 0 1 ∧ Metric.ball w ρ ⊆ Metric.ball 0 1 ∧
    InjOn F (Metric.ball z ρ) ∧ InjOn F (Metric.ball w ρ) ∧
    (∀ m, Γ m 0 = z ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
      HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Icc 0 ρ) (Metric.ball z ρ)) ∧
    (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
      ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
    (∀ z' ∈ Metric.ball z ρ,
      (∃ w' ∈ Metric.ball w ρ, F z' = F w') ↔ ∃ m, ∃ r ∈ Icc 0 ρ, z' = Γ m r) ∧
    ∀ m, ∀ r ∈ Ioc 0 ρ, ∀ w' ∈ Metric.ball w ρ, F (Γ m r) = F w' →
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (Γ m r)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w')))

/-- R9 输出（rev2，D-R-MY2-13/15：data + invariants 的 notion；existence 另由 R9 producer 给出）。
`T` 有限平面 polygonal 复形，`α : |T| ≅ D̄`，`A` 是 relative 3-thickening，`h ∘ |φ| = f ∘ α`。 -/
structure IsPreparedSheetComplex_FIX (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) (N : ℕ)
    (A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (φ : ℂ → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N) → M) : Prop where
  /-- (S1) 有限平面 2-复形。 -/
  faces_finite : T.faces.Finite
  dim_le : ∀ s ∈ T.faces, s.card ≤ 3
  /-- (S2) `α : |T| → D̄` 连续双射、边界对边界（compact → Hausdorff ⇒ homeomorphism）。 -/
  alpha_bij : BijOn α T.space (Metric.closedBall 0 1)
  alpha_cont : ContinuousOn α T.space
  alpha_bdry : ∀ {z : ℂ}, z ∈ T.space → (‖α z‖ = 1 ↔ z ∈ frontier T.space)
  /-- (S3) `α` 单向 Lipschitz；每个 2-面去掉顶点后 `C^∞`、导数可逆（**不**要求 bi-Lipschitz）。 -/
  alpha_lip : ∃ L : ℝ≥0, LipschitzOnWith L α T.space
  alpha_smooth : ∀ s ∈ T.faces, s.card = 3 →
    ContDiffOn ℝ ∞ α (convexHull ℝ (s : Set ℂ) \ (s : Set ℂ))
  alpha_rank : ∀ s ∈ T.faces, s.card = 3 → ∀ z ∈ convexHull ℝ (s : Set ℂ) \ (s : Set ℂ),
    Function.Injective (fderivWithin ℝ α (convexHull ℝ (s : Set ℂ)) z)
  /-- (S4) R8 的正则性保存：闭盘 smooth extension + 闭盘 rank + singleton collar。 -/
  ext : SmoothDiskExtension (E := E) f F
  rank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z)
  collar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w
  /-- (S5) image 2-complex（`φ` 的逐面像，逐面非退化）⊆ relative 3-thickening `A`（组合 3-流形），
  `h` 在 `|A|` 上连续单射；`h ∘ |φ| = f ∘ α`；trace 在 `h(|A|)` 的 frontier、内部盘在 interior。 -/
  A_finite : A.faces.Finite
  A_manifold : IsCombinatorialManifoldWithBoundary 3 A
  h_cont : ContinuousOn h A.space
  h_inj : InjOn h A.space
  face_map : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card
  factor : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z)
  bdry_frontier : ∀ θ, f (diskBoundary θ) ∈ frontier (h '' A.space)
  int_interior : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z ∈ interior (h '' A.space)
  /-- (S6) 源碰撞集经 `α` 是 `T` 的子复形（由 collar 自动在 `D°` 内）。 -/
  collision_subcomplex : ∃ S ⊆ T.faces, α '' (⋃ s ∈ S, convexHull ℝ (s : Set ℂ)) =
    {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧ ∃ w ∈ Metric.closedBall (0 : ℂ) 1, w ≠ z ∧ F w = F z}
  /-- (S7) 非横截（tangential）碰撞源点都是顶点（tangency stratum 有限）。 -/
  tangency_vertices : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w))) →
    ∃ v ∈ T.vertices, α v = z
  /-- (S8) 每个碰撞对的 two-sheet nodal 数据（R3a-ω 输出；R14 消费）。 -/
  nodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
    IsCollisionNodal_FIX (E := E) F z w

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **consumer（R10.1 对齐）**：任意 prepared 数据的 thickening `A`、`h` 直接给出 R10.1
`IsRelRegularNbhd` 的 `Nb = h(|A|)` 部分——`Ab = A` finite、组合 3-流形、`hb = h` 连续单射、
trace 在 `Nb` 的 frontier、内部盘在 `Nb` 的 interior（缺的只是 retraction `R`、deformation `H`、
`π₁` 满射，那些由 R10.1 producer 从 `A` 生产）。 -/
theorem IsPreparedSheetComplex_FIX.nbhd_data {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) :
    (∃ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 Ab ∧ ContinuousOn hb Ab.space ∧ InjOn hb Ab.space ∧
      hb '' Ab.space = h '' A.space) ∧
    (∀ θ, f (diskBoundary θ) ∈ frontier (h '' A.space)) ∧
    (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → f z ∈ interior (h '' A.space)) :=
  ⟨⟨N, A, h, hprep.A_finite, hprep.A_manifold, hprep.h_cont, hprep.h_inj, rfl⟩,
    hprep.bdry_frontier, hprep.int_interior⟩

end Generic

end DifferentialGeometry.Geometry
