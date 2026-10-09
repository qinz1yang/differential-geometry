import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNodalFIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionEdgeSidesR10

/-!
# S-MY-FIX2：`IsPreparedSheetComplex_FIX2`（rev3 notion 草案：22 字段 + `local_product` + `ambient_collar`）

与 `IsPreparedSheetComplex_FIX`（S-MY-FIX）的 22 个字段逐字相同，**唯一改动**：S8 `nodal` 用 Ico 版
`IsCollisionNodal_FIX2`（R-MY3 D-R-MY3-12）。另加两个 rev3 字段（lead 18:0x 裁决，形状取自 O-MY-R10PL 的
`CollisionEdgeSidesR10.lean`）：
* `local_product : HasLocalProductCollapse_R10 f F T α (h '' |A|)`
  （collapse + 两侧 + realized rotation system）；
* `ambient_collar : HasAmbientCollar_R10 (h '' |A|)`。
本文件只含 notion（所有字段是显式 Prop，无新 admission）；inhabitant 见 `PreparedSheetComplexConsFIX2.lean`
（平坦盘，S6–S8 空真）；带碰撞的 F 侧 fixture 见 `PreparedSheetComplex{Local2,Curve2}FIX2.lean`。

**事实记录（rev3 要记）**：带 transverse double *segment*（端点在 `D°` 内或 `∂D` 上）的 immersed disk
**不可能**满足这个 notion：S8 要求每个内部碰撞点附近的碰撞集是 `2k ≥ 2` 条 half-arcs 的并（碰撞弧不能在内部
终止），`collar` 禁止 `‖z‖ > μ` 处有碰撞（端点不能在 `∂D` 上）；所以 double locus 只能是无端点的闭曲线或
even-valence 图。
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

/-- R9 输出（rev2，D-R-MY2-13/15：data + invariants 的 notion；existence 另由 R9 producer 给出）。
`T` 有限平面 polygonal 复形，`α : |T| ≅ D̄`，`A` 是 relative 3-thickening，`h ∘ |φ| = f ∘ α`。 -/
structure IsPreparedSheetComplex_FIX2 (f : C(closedDisk, M)) (F : ℂ → M)
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
    IsCollisionNodal_FIX2 (E := E) F z w
  /-- (S9，rev3 新字段，O-MY-R10PL) local product / sector-controlled collapse：`Nb = h(|A|)` 带 collapse
  `(R, H)`、2-strata 两侧、每条内部边的 realized rotation system（`m = 2` 横截情形：4 个 half-sheet germs 交错）。 -/
  local_product : HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space)
  /-- (S10，rev3 新字段，O-MY-R10PL) ambient collar：开集 `O ⊇ h(|A|)` strong deformation retract 到 `h(|A|)`
  （R11 genuine cover 的 `HO`）。 -/
  ambient_collar : HasAmbientCollar_R10 (h '' A.space)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **consumer（R10.1 对齐）**：任意 prepared 数据的 thickening `A`、`h` 直接给出 R10.1
`IsRelRegularNbhd` 的 `Nb = h(|A|)` 部分——`Ab = A` finite、组合 3-流形、`hb = h` 连续单射、
trace 在 `Nb` 的 frontier、内部盘在 `Nb` 的 interior（缺的只是 retraction `R`、deformation `H`、
`π₁` 满射，那些由 R10.1 producer 从 `A` 生产）。 -/
theorem IsPreparedSheetComplex_FIX2.nbhd_data {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h) :
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
