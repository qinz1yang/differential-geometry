import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity

/-!
# S-A08-ATTAIN G1′（Route W）：`morreyLeastArea` 与 `IsMorreyDisk.area_eq_morreyLeastArea`

Route W 用 Morrey（parametrized）disk class 代替 exterior spanning disk class：
`morreyLeastArea g W γ` 是 `riemannianDiskArea g` 在
`{v | DiskWeakJordanTrace γ v ∧ range v ⊆ W ∧ v 是 riemannian-Lipschitz}`
（Lipschitz 条款逐字照 `IsMorreyDisk.minimizesLipschitz` 的竞争者类，再加 `range v ⊆ W`，
使 time-`t` 的 transport 保类）上的下确界。`W := Set.univ` 即无 region 限制的版本。
Mathlib 的 `sInf` 对空集 / 无下界给 `0`；这里下界 `0`（`riemannianDiskArea_nonneg`），
非空性由 Morrey 盘 `u` 本身给出，故等式不依赖该约定。

* `morreyLeastArea_nonneg`、`morreyLeastArea_le`（任何竞争者）；
* `IsMorreyDisk.area_eq_morreyLeastArea_of_lipschitz`：`u` Morrey、`range u ⊆ W` 且 `u` 自身
  Lipschitz ⇒ `riemannianDiskArea g u = morreyLeastArea g W γ`
  （`minimizesLipschitz` 给 `≤`：`area u ≤` 每个竞争者；`u` 作为竞争者给 `≥`）；
* `IsMorreyDisk.area_eq_morreyLeastArea`：`γ` 光滑嵌入、`finrank E = 3` 时，Lipschitz 性由
  边界正则（`IsMorreyDisk.exists_smooth_extension` + `SmoothDiskExtension.lipschitz`）给出。

注意：这里 `g` 同时是 Morrey 盘的度量与竞争者面积的度量（单流形版本）。Top 里的 Morrey 盘在
open target `U` 上关于局部度量 `G`，对应的搬运版本见 `MorreyLeastAreaOpenAT`。
不引入新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry.Topology Set
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Morrey 竞争者类上的最小面积：竞争者是弱 Jordan trace `γ ∘ σ` 的、range 落在 `W` 内的
riemannian-Lipschitz 盘（Lipschitz 条款与 `IsMorreyDisk.minimizesLipschitz` 的类逐字一致）。 -/
def morreyLeastArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M) : ℝ :=
  sInf ((fun v : C(closedDisk, M) => riemannianDiskArea g v) ''
    {v | DiskWeakJordanTrace γ v ∧ Set.range v ⊆ W ∧ ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w})

omit [FiniteDimensional ℝ E] in
theorem morreyLeastArea_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M)
    (γ : freeLoop M) : 0 ≤ morreyLeastArea g W γ := by
  apply Real.sInf_nonneg
  rintro _ ⟨v, _, rfl⟩
  exact riemannianDiskArea_nonneg g v

omit [FiniteDimensional ℝ E] in
/-- 任何竞争者（弱 Jordan trace + range ⊆ `W` + riemannian-Lipschitz）的面积 `≥ morreyLeastArea`。 -/
theorem morreyLeastArea_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {W : Set M} {γ : freeLoop M}
    {v : C(closedDisk, M)} (hv : DiskWeakJordanTrace γ v) (hW : Set.range v ⊆ W)
    (hL : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) :
    morreyLeastArea g W γ ≤ riemannianDiskArea g v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact riemannianDiskArea_nonneg g w
  · exact ⟨v, ⟨hv, hW, hL⟩, rfl⟩

/-- Morrey 盘 `u` 若 range 落在 `W` 内且自身是 riemannian-Lipschitz，则它的面积就是
`morreyLeastArea`。 -/
theorem IsMorreyDisk.area_eq_morreyLeastArea_of_lipschitz
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hW : Set.range u ⊆ W)
    (hlip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea g u = morreyLeastArea g W γ := by
  apply le_antisymm
  · refine le_csInf ⟨riemannianDiskArea g u, u, ⟨hu.trace, hW, hlip⟩, rfl⟩ ?_
    rintro _ ⟨v, ⟨hv, _, hL⟩, rfl⟩
    exact hu.minimizesLipschitz v hv hL
  · exact morreyLeastArea_le g hu.trace hW hlip

/-- **G1′.**  光滑嵌入边界环 + `finrank E = 3` 下，Morrey 盘的面积等于 `morreyLeastArea`：
`u` 的 riemannian-Lipschitz 性来自边界正则 `IsMorreyDisk.exists_smooth_extension`。 -/
theorem IsMorreyDisk.area_eq_morreyLeastArea [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {W : Set M} (hd : Module.finrank ℝ E = 3)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hW : Set.range u ⊆ W) :
    riemannianDiskArea g u = morreyLeastArea g W γ := by
  obtain ⟨U, hU⟩ := hu.exists_smooth_extension g hd hγ
  exact hu.area_eq_morreyLeastArea_of_lipschitz hW (hU.lipschitz g)

/-- Consumer of G1′（"minimizer attained" 形状）：Morrey 盘本身是竞争者类里的 minimizer，
面积等于类的下确界。这是 Route W 里 `hasExteriorDiskMinimizersAfter` 的 Morrey 版本的单时刻内容。 -/
theorem exists_attained_morreyLeastArea_of_morrey_AT [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {W : Set M} (hd : Module.finrank ℝ E = 3)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hW : Set.range u ⊆ W) :
    ∃ v : C(closedDisk, M), DiskWeakJordanTrace γ v ∧ Set.range v ⊆ W ∧
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      riemannianDiskArea g v = morreyLeastArea g W γ := by
  obtain ⟨U, hU⟩ := hu.exists_smooth_extension g hd hγ
  exact ⟨u, hu.trace, hW, hU.lipschitz g, hu.area_eq_morreyLeastArea hd hγ hW⟩

end DifferentialGeometry.Geometry
