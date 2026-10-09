import DifferentialGeometry.Geometry.MinimalSurface.Plateau.RelRegularNbhdR10
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# O-MY-R10PL G2：R10.2 sector-controlled collapse（notion，`_R10`）

R-MY3（经 lead 转达）：R10.1 的一般 strong deformation retraction **推不出** R10.2 的两侧结构
（反例 `N = B̄³`、`L = D̄² × {0}`、`R` 把整块北极 cap 压到 `L` 的一个内点）。修正：10.1 与 10.2
**共同选择同一个 witness**
`∃ Nb R, IsRelRegularNbhd_R10 f Nb R ∧ IsSectorControlledCollapse_R10 F T α Nb R`，
即把 collapse 的 **local model** 写进 notion：

* 2-strata（`T` 的每个 2-面 `σ`，开像面 `O_σ = F(α(σ°))`）：`IsTwoSidedFace_R10`——`∂Nb ∩ R⁻¹(O_σ)` 恰两侧，
  不交、各自 preconnected、`R` 在每侧单射并映满 `O_σ`、有连续 section（R4r / caps 的“侧 ↔ 面”识别）。
* 1-strata（`T` 的每条内部边 `e`，开像边 `O_e`）：`HasRealizedRotationSystem_R10`——transverse normal disk
  里的 **realized rotation system**：`2m` 个 half-sheet germs（含某条与 `e` 同开像的边的 2-面）的循环次序
  `germ : Fin (2m) → Finset ℂ`（`finRotate` 给循环后继）、同一 sheet 两条相反 half-rays 的对应
  （`opp`，`sheetEdge (opp j) = sheetEdge j`）、boundary sectors 与相邻 germs 的配对（sector `j` 夹在
  `germ j` 的 `out j` 侧与 `germ (j+1)` 的 `!out (j+1)` 侧之间：两侧闭包在 `R⁻¹(O_e)` 上落在 sector `j` 里且
  与之相交）、此配对沿整条开边一致（`R '' sector j = O_e`），全部由**同一个** `(Nb, R, side)` 实现；
  transverse collision edge 上相邻 germs 属于不同 sheet（`sheetEdge (j+1) ≠ sheetEdge j`）。
  不需要数值角度，也不加 conormal 符号约定（R-MY3：两片 tangent plane 不同即推出 fold 非零）。

开单形用 PL 库的 `openSimplex`（正重心坐标），**不**用 scratch 的 `intrinsicInterior (convexHull ·)`：
对仿射无关顶点两者相同，但 `openSimplex` 有现成的 `face_eq_of_mem_openSimplex`、
`interior_convexHull_eq_openSimplex` 等。这是与 scratch `MYD3/R10R14.lean:78/89` 的唯一措辞偏差。

`IsTransverseCollisionEdge_R10` 与 scratch `:78` 同形（`intrinsicInterior` → `openSimplex`）。
一般 prepared 数据的**联合** producer（derived neighborhood 的 barycentric collapse 满足本 notion）
本文件**不**给出；非空性见 `FlatLensCollapseR10.lean` 的 `flatDisk_sectorControlled_R10`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

section Faces

variable {M : Type u}

/-- 源单形 `s` 的开像 `F(α(s°))`（`s° = openSimplex s`）。 -/
def openImageFace_R10 (F : ℂ → M) (α : ℂ → ℂ) (s : Finset ℂ) : Set M :=
  F '' (α '' openSimplex s)

/-- `σ` 是边 `e` 处的 **half-sheet germ**：`T` 的 2-面，含一条与 `e` 同开像的边 `e'`。 -/
def IsHalfSheetGerm_R10 (F : ℂ → M) (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ)
    (e σ : Finset ℂ) : Prop :=
  σ ∈ T.faces ∧ σ.card = 3 ∧ ∃ e' ∈ T.faces, e'.card = 2 ∧ e' ⊆ σ ∧
    openImageFace_R10 F α e' = openImageFace_R10 F α e

end Faces

section Edge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- `e`（`T` 的 1-面）是 **transverse collision edge**：开边经 `α` 全是 `D°` 内碰撞点，且每个碰撞都 transverse
（任意 multiplicity；与 scratch `MYD3/R10R14.lean:78` 同形，开单形用 `openSimplex`）。 -/
def IsTransverseCollisionEdge_R10 (F : ℂ → M) (α : ℂ → ℂ) (e : Finset ℂ) : Prop :=
  e.card = 2 ∧ ∀ z ∈ α '' openSimplex e,
    z ∈ Metric.ball (0 : ℂ) 1 ∧ (∃ w ∈ Metric.ball (0 : ℂ) 1, w ≠ z ∧ F w = F z) ∧
    ∀ w ∈ Metric.ball (0 : ℂ) 1, w ≠ z → F w = F z →
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w)))

end Edge

section Sides

variable {M : Type u} [TopologicalSpace M]

/-- 2-strata 的 local model：开像面 `O` 在 `∂Nb` 上恰两侧 `sd true`、`sd false`——不交、
并 = `frontier Nb ∩ R⁻¹(O)`、每侧 preconnected、`R` 在每侧单射并映满 `O`，且有连续 section。 -/
def IsTwoSidedFace_R10 (Nb : Set M) (R : M → M) (O : Set M) (sd : Bool → Set M) : Prop :=
  Disjoint (sd true) (sd false) ∧ sd true ∪ sd false = frontier Nb ∩ R ⁻¹' O ∧
  ∀ b, IsPreconnected (sd b) ∧ InjOn R (sd b) ∧ R '' sd b = O ∧
    ∃ sec : M → M, ContinuousOn sec O ∧ ∀ y ∈ O, sec y ∈ sd b ∧ R (sec y) = y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

/-- 1-strata 的 local model（**realized rotation system**，R-MY3）：沿内部边 `e`，
`germ : Fin (2m) → Finset ℂ` 是 half-sheet germs 的循环列举（`finRotate` = 循环后继），`sheetEdge j ⊆ germ j`
是该 germ 里与 `e` 同开像的边，`opp` 配对同一 sheet 的两条相反 half-rays；sector `j ⊆ ∂Nb ∩ R⁻¹(O_e)`
夹在 `germ j` 的 `out j` 侧与 `germ (j+1)` 的 `!out (j+1)` 侧之间（两侧闭包在 `R⁻¹(O_e)` 上落进 sector `j`
且与之相交）；sectors 两两不交、并 = `∂Nb ∩ R⁻¹(O_e)`、各自 preconnected 且 `R` 映满 `O_e`；
`e` 是 transverse collision edge 时相邻 germs 属于不同 sheet。 -/
def HasRealizedRotationSystem_R10 (F : ℂ → M) (T : _root_.Geometry.SimplicialComplex ℝ ℂ)
    (α : ℂ → ℂ) (Nb : Set M) (R : M → M) (side : Finset ℂ → Bool → Set M) (e : Finset ℂ) :
    Prop :=
  ∃ (m : ℕ) (germ sheetEdge : Fin (2 * m) → Finset ℂ) (opp : Fin (2 * m) → Fin (2 * m))
    (out : Fin (2 * m) → Bool) (sector : Fin (2 * m) → Set M),
    0 < m ∧ Function.Injective germ ∧
    (∀ σ, IsHalfSheetGerm_R10 F T α e σ ↔ ∃ j, germ j = σ) ∧
    (∀ j, sheetEdge j ∈ T.faces ∧ (sheetEdge j).card = 2 ∧ sheetEdge j ⊆ germ j ∧
      openImageFace_R10 F α (sheetEdge j) = openImageFace_R10 F α e) ∧
    (∀ j, opp (opp j) = j ∧ opp j ≠ j ∧ sheetEdge (opp j) = sheetEdge j) ∧
    (IsTransverseCollisionEdge_R10 (E := E) F α e →
      ∀ j, sheetEdge (finRotate (2 * m) j) ≠ sheetEdge j) ∧
    (⋃ j, sector j) = frontier Nb ∩ R ⁻¹' openImageFace_R10 F α e ∧
    Pairwise (fun j k => Disjoint (sector j) (sector k)) ∧
    ∀ j, IsPreconnected (sector j) ∧ R '' sector j = openImageFace_R10 F α e ∧
      closure (side (germ j) (out j)) ∩ R ⁻¹' openImageFace_R10 F α e ⊆ sector j ∧
      closure (side (germ (finRotate (2 * m) j)) (!out (finRotate (2 * m) j))) ∩
        R ⁻¹' openImageFace_R10 F α e ⊆ sector j ∧
      (closure (side (germ j) (out j)) ∩ sector j).Nonempty ∧
      (closure (side (germ (finRotate (2 * m) j)) (!out (finRotate (2 * m) j))) ∩
        sector j).Nonempty

/-- **R10.2 notion**（R-MY3）：`(Nb, R)` 是 sector-controlled collapse——存在
`side : Finset ℂ → Bool → Set M`，使每个 2-面满足 2-strata local model、每条内部边
（`α(e°) ⊆ D°`）满足 1-strata realized rotation system。
与 `IsRelRegularNbhd_R10 f Nb R` 对**同一个** `(Nb, R)` 联用。 -/
def IsSectorControlledCollapse_R10 (F : ℂ → M) (T : _root_.Geometry.SimplicialComplex ℝ ℂ)
    (α : ℂ → ℂ) (Nb : Set M) (R : M → M) : Prop :=
  ∃ side : Finset ℂ → Bool → Set M,
    (∀ σ ∈ T.faces, σ.card = 3 → IsTwoSidedFace_R10 Nb R (openImageFace_R10 F α σ) (side σ)) ∧
    ∀ e ∈ T.faces, e.card = 2 → α '' openSimplex e ⊆ Metric.ball (0 : ℂ) 1 →
      HasRealizedRotationSystem_R10 (E := E) F T α Nb R side e

end Sides

/-! ## prepared 数据：开 2-面的像在 `D°` 内 -/

section Prepared

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- prepared 数据：`T` 的每个 2-面的开单形经 `α` 落在开单位盘里（`σ° = interior (conv σ) ⊆ interior |T|`，
再用 `alpha_bdry`）。所以开像面 `O_σ ⊆ f(D°)`。 -/
theorem IsPreparedSheetComplex_FIX.image_openSimplex_subset_ball_R10 {f : C(closedDisk, M)}
    {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) {σ : Finset ℂ}
    (hσ : σ ∈ T.faces) (hcard : σ.card = 3) :
    α '' openSimplex σ ⊆ Metric.ball (0 : ℂ) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  have hfr : Module.finrank ℝ ℂ + 1 = 3 := by rw [Complex.finrank_real_complex]
  rw [← interior_convexHull_eq_openSimplex (T.indep hσ) (hcard.trans hfr.symm)] at hz
  have hzint : z ∈ interior T.space := interior_mono (T.convexHull_subset_space hσ) hz
  have hzT : z ∈ T.space := interior_subset hzint
  have hle : ‖α z‖ ≤ 1 := by
    have := hprep.alpha_bij.mapsTo hzT
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hne : ‖α z‖ ≠ 1 := fun h1 => ((hprep.alpha_bdry hzT).mp h1).2 hzint
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_ne hle hne

/-! ## R9 字段 `local_product`（lead 裁决：rotation system / local product 作 R9 producer 输出）

thickening `Nb = h(|A|)` 自带 collapse `(R, H)`（固定 `L = f(D̄)` 的 strong deformation retraction）与
sector-controlled local model（2-strata 两侧 + 每条内部边的 realized rotation system）。R9 producer 在光滑侧
用 normal I-bundle + transverse crossing 的 cross model 造它；R10 在其上做组合装配（下面的
`relative_regular_nbhd_sector_R10`）。rev3 里应作为 `IsPreparedSheetComplex` 的第 23 个字段
`local_product : HasLocalProductCollapse_R10 f F T α (h '' A.space)`；树内先作独立 Prop 与 `_FIX` 联用。

**义务转移（lead 裁决，明确记录）**：这把 R10.1 / R10.2 的**全部几何义务**（collapse 的存在、2-strata 两侧、
1-strata rotation system、`frontier` 的识别）搬到了 **R9 producer（F4：半解析分层的局部锥结构 ⇒ 带 sector
控制的 collapse）**；R10 本身变成组合装配。rev3 估行须把这部分从 R10 挪到 R9（不是消失）。外审 Q3 红线
"字段里藏待证命题"的对策：字段由 fixture 实际 witness（flat：`flatDisk_localProduct_R10`；带碰撞：S-MY-FIX2），
且 R9 producer 合同须显式列出它生产 `local_product`、`ambient_collar`。collision-edge-only 版本的差距合同
`local_product_of_collision_edge_charts_R10` 只在 scratch
（`build-logs/scratch/O-MY-R10PL/contracts/`）。 -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- R9 字段 `local_product` 的形状：`Nb` 带 collapse `(R, H)` 与 sector-controlled local model。 -/
def HasLocalProductCollapse_R10 (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) (Nb : Set M) : Prop :=
  ∃ (R : M → M) (H : unitInterval × M → M),
    ContinuousOn R Nb ∧ MapsTo R Nb (Set.range f) ∧ (∀ x ∈ Set.range f, R x = x) ∧
    ContinuousOn H (univ ×ˢ Nb) ∧ (∀ x ∈ Nb, H (0, x) = x) ∧ (∀ x ∈ Nb, H (1, x) = R x) ∧
    (∀ t, ∀ x ∈ Set.range f, H (t, x) = x) ∧ (∀ t, MapsTo (fun x => H (t, x)) Nb Nb) ∧
    IsSectorControlledCollapse_R10 (E := E) F T α Nb R

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **R10.1 + R10.2 联合 producer**（同一 witness，R-MY3）：prepared 数据 + R9 字段 `local_product` ⇒
`Nb = h(|A|)` 同时满足 `IsRelRegularNbhd_R10` 与 `IsSectorControlledCollapse_R10`
（compact / manifold / trace 来自 prepared，connected 与 `π₁` 满射由 collapse 推出）。 -/
theorem relative_regular_nbhd_sector_R10 {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hlp : HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space)) :
    ∃ (Nb : Set M) (R : M → M), IsRelRegularNbhd_R10 f Nb R ∧
      IsSectorControlledCollapse_R10 (E := E) F T α Nb R ∧ Nb = h '' A.space := by
  obtain ⟨R, H, hRc, hRm, hRfix, hHc, hH0, hH1, hHfix, hHm, hsc⟩ := hlp
  have hLA : (preparedImageComplex_R10 T φ A).space ⊆ A.space := fun x hx => by
    obtain ⟨t, ht, hxt⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact A.convexHull_subset_space ht.1 hxt
  have hLN : Set.range f ⊆ h '' A.space := by
    rw [hprep.range_eq_R10]
    exact image_mono hLA
  obtain ⟨hman, hbd, hint⟩ := hprep.nbhd_data
  exact ⟨h '' A.space, R, IsRelRegularNbhd_R10.of_collapse
    ((isCompact_space_of_finite_R10 A hprep.A_finite).image_of_continuousOn hprep.h_cont)
    hman hbd hint hLN hRc hRm hRfix H hHc hH0 hH1 hHfix hHm, hsc, rfl⟩

/-! ## R9 字段 `ambient_collar`（R11-step 的 `HO`）

R11 的 genuine cover 需要**开集** `O ⊇ Nb` 与把 `O` strong deformation retract 到 `Nb` 的 `G`
（S-MY-R11PL `exists_double_cover_core_R11PL` 的 `hO … hGmaps`、`TowerEngineR12.hR11` 的 `HO`，同形同序）。
它**不能**从 prepared 数据造：`bdry_frontier` 说 trace `f(S¹) ⊆ frontier (h '' A.space)`，所以任何含 `range f`
的开集都含 `h(|A|)` 外的点，而 prepared 数据对 `M \ h(|A|)` 无任何描述（`h` 只连续单射，`h(|A|)` 在 trace 处
可以是 wild 的）。故作 R9 字段：R9 光滑侧由 trace 的 tubular neighborhood + `A` 沿 `∂` 外延给出。 -/

/-- `O ⊇ Nb` 开，`G` 把 `O` strong deformation retract 到 `Nb`（固定 `Nb`）——与 R11PL `hO … hGmaps` 同形。 -/
def HasAmbientCollar_R10 (Nb : Set M) : Prop :=
  ∃ (O : Set M) (G : unitInterval × M → M), IsOpen O ∧ Nb ⊆ O ∧
    ContinuousOn G (univ ×ˢ O) ∧ (∀ x ∈ O, G (0, x) = x) ∧ (∀ x ∈ O, G (1, x) ∈ Nb) ∧
    (∀ t, ∀ x ∈ Nb, G (t, x) = x) ∧ ∀ t, MapsTo (fun x => G (t, x)) O O

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 联合 producer + ambient collar：prepared + `local_product` + `ambient_collar`（都在 `h(|A|)` 上）⇒
同一 witness `Nb = h(|A|)` 满足 R10.1、R10.2，且带 R11 要的 `HO`。 -/
theorem relative_regular_nbhd_sector_collar_R10 {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hlp : HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space))
    (hcol : HasAmbientCollar_R10 (h '' A.space)) :
    ∃ (Nb : Set M) (R : M → M), IsRelRegularNbhd_R10 f Nb R ∧
      IsSectorControlledCollapse_R10 (E := E) F T α Nb R ∧ HasAmbientCollar_R10 Nb ∧
      Nb = h '' A.space := by
  obtain ⟨Nb, R, hN, hsc, rfl⟩ := relative_regular_nbhd_sector_R10 hprep hlp
  exact ⟨_, R, hN, hsc, hcol, rfl⟩

end Prepared

end DifferentialGeometry.Geometry
