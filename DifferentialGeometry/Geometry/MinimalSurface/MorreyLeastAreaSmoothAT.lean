import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaAT
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskSmoothLipschitz
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget

/-!
# S-A08-ATTAIN G1″（Route W）：光滑竞争者类的 `morreyLeastAreaS` 与 open-target 等号

竞争者类改为 `{v | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ v ∧ range v ⊆ W}`
（光滑到边界，替代 riemannian-Lipschitz）。好处：

1. Morrey 盘 `q` 属于类：`IsMorreyDisk.exists_smooth_extension` + `SmoothDiskExtension.comp`；
2. open-target 的 `≥` 不需要 "g-Lipschitz ∧ range ⊆ W ⇒ G-Lipschitz" 的距离比较：
   `v` 的 range 在开集 `U` 内，提升 `vU : C(closedDisk, U)` 仍光滑到边界
   （`contMDiffWithinAt_subtypeVal_comp_iff`），`DiskSmoothUpToBoundary.exists_lipschitz G` 给
   `G`-Lipschitz，再用 `IsMorreyDisk.minimizesLipschitz`；
3. 面积换度量：`G.inner = (g.restrictOpen U).inner` 在 range 上（`hG`）+
   `riemannianDiskArea_restrictOpen`。

* `morreyLeastAreaS`、`_nonneg`、`_le`、`IsMorreyDisk.area_eq_morreyLeastAreaS`（单流形）；
* `morreyLeastAreaS_eq_morreyLeastArea`：有 Morrey 盘时光滑类与 Lipschitz 类的下确界相等（都被它达到）；
* `morreyLeastAreaS_eq_area_open_AT`：open target `U` 上关于 `G` 的 Morrey 盘 `q`，`ι ∘ q` 的
  `g`-面积等于 `morreyLeastAreaS g W γ`（`W ⊆ U`，`G = g.restrictOpen U` 在 `W` 上，`ι ∘ γU = γ`）。

不引入新结构 / 新 Prop；`hG` 只是逐点度量等式（`_HC` 里 `G = canonicalPositiveDomainMetric`，
在 `{ρ ≤ 0}` 上由 `cutoff = 1` 得到）。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 光滑竞争者类上的最小面积：竞争者是光滑到边界、弱 Jordan trace `γ ∘ σ`、
range 落在 `W` 内的盘。 -/
def morreyLeastAreaS (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M) : ℝ :=
  sInf ((fun v : C(closedDisk, M) => riemannianDiskArea g v) ''
    {v | DiskSmoothUpToBoundary (E := E) v ∧ DiskWeakJordanTrace γ v ∧ Set.range v ⊆ W})

omit [FiniteDimensional ℝ E] in
theorem morreyLeastAreaS_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M)
    (γ : freeLoop M) : 0 ≤ morreyLeastAreaS g W γ := by
  apply Real.sInf_nonneg
  rintro _ ⟨v, _, rfl⟩
  exact riemannianDiskArea_nonneg g v

omit [FiniteDimensional ℝ E] in
/-- 任何光滑竞争者的面积 `≥ morreyLeastAreaS`。 -/
theorem morreyLeastAreaS_le (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {W : Set M}
    {γ : freeLoop M} {v : C(closedDisk, M)} (hv : DiskSmoothUpToBoundary (E := E) v)
    (hw : DiskWeakJordanTrace γ v) (hW : Set.range v ⊆ W) :
    morreyLeastAreaS g W γ ≤ riemannianDiskArea g v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact riemannianDiskArea_nonneg g w
  · exact ⟨v, ⟨hv, hw, hW⟩, rfl⟩

/-- **G1″（单流形）.**  光滑嵌入边界环 + `finrank E = 3`：Morrey 盘的面积等于
`morreyLeastAreaS`（`≤` 用 `u` 光滑到边界；`≥` 用光滑 ⇒ Lipschitz + `minimizesLipschitz`）。 -/
theorem IsMorreyDisk.area_eq_morreyLeastAreaS [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {W : Set M} (hd : Module.finrank ℝ E = 3)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hW : Set.range u ⊆ W) :
    riemannianDiskArea g u = morreyLeastAreaS g W γ := by
  obtain ⟨U, hU⟩ := hu.exists_smooth_extension g hd hγ
  apply le_antisymm
  · refine le_csInf ⟨riemannianDiskArea g u, u, ⟨hU.smoothUpToBoundary, hu.trace, hW⟩, rfl⟩ ?_
    rintro _ ⟨v, ⟨hv, hw, _⟩, rfl⟩
    exact hu.minimizesLipschitz v hw (hv.exists_lipschitz g)
  · exact morreyLeastAreaS_le g hU.smoothUpToBoundary hu.trace hW

/-- 有 Morrey 盘时，光滑类与 Lipschitz 类（`morreyLeastArea`）的下确界相等：
Morrey 盘同时达到两者。 -/
theorem morreyLeastAreaS_eq_morreyLeastArea [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {W : Set M} (hd : Module.finrank ℝ E = 3)
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hW : Set.range u ⊆ W) :
    morreyLeastAreaS g W γ = morreyLeastArea g W γ :=
  (hu.area_eq_morreyLeastAreaS hd hγ hW).symm.trans (hu.area_eq_morreyLeastArea hd hγ hW)

section OpenTarget

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

omit [FiniteDimensional ℝ E] in
/-- 面积只依赖度量在 range 上的取值。 -/
theorem riemannianDiskArea_congr_inner_AT {G G' : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {u : closedDisk → M} (h : ∀ z : closedDisk, G.inner (u z) = G'.inner (u z)) :
    riemannianDiskArea G u = riemannianDiskArea G' u := by
  unfold riemannianDiskArea riemannianArea
  congr 1
  funext z
  have h' : G.inner (diskExtension u z) = G'.inner (diskExtension u z) := h (diskRetraction z)
  unfold riemannianAreaDensity tangentTwoJacobian
  rw [h']

/-- 把 range 落在开集 `U` 内的盘提升成 `C(closedDisk, U)`。 -/
def liftToOpen_AT {U : TopologicalSpace.Opens N} (v : C(closedDisk, N))
    (hU : Set.range v ⊆ U) : C(closedDisk, U) :=
  ⟨fun z => ⟨v z, hU (mem_range_self z)⟩, v.continuous.subtype_mk _⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ N] in
/-- 提升保持 "光滑到边界"。 -/
theorem diskSmoothUpToBoundary_liftToOpen_AT {U : TopologicalSpace.Opens N}
    {v : C(closedDisk, N)} (hv : DiskSmoothUpToBoundary (E := E) v) (hU : Set.range v ⊆ U) :
    DiskSmoothUpToBoundary (E := E) (liftToOpen_AT v hU) := by
  intro z hz
  have h := hv z hz
  exact (contMDiffWithinAt_subtypeVal_comp_iff (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U
    (diskExtension (liftToOpen_AT v hU)) (Metric.closedBall (0 : ℂ) 1) z).mp h

/-- 提升保持弱 Jordan trace（`γU` 是 `γ` 的提升）。 -/
theorem diskWeakJordanTrace_liftToOpen_AT {U : TopologicalSpace.Opens N}
    {γU : freeLoop U} {γ : freeLoop N} (hγγ : ∀ θ, (γU θ : N) = γ θ)
    {v : C(closedDisk, N)} (hw : DiskWeakJordanTrace γ v) (hU : Set.range v ⊆ U) :
    DiskWeakJordanTrace γU (liftToOpen_AT v hU) := by
  obtain ⟨σ, hσ, htr⟩ := hw
  refine ⟨σ, hσ, ?_⟩
  ext θ
  have h := congrArg (fun f : freeLoop N => f θ) htr
  change v (diskBoundary θ) = γ (σ θ) at h
  change v (diskBoundary θ) = (γU (σ θ) : N)
  rw [h, hγγ]

/-- 弱 Jordan trace 沿 `U ↪ N` 向前推。 -/
theorem diskWeakJordanTrace_comp_val_AT {U : TopologicalSpace.Opens N}
    {γU : freeLoop U} {γ : freeLoop N} (hγγ : ∀ θ, (γU θ : N) = γ θ)
    {q : C(closedDisk, U)} (hw : DiskWeakJordanTrace γU q) :
    DiskWeakJordanTrace γ
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, N)).comp q) := by
  obtain ⟨σ, hσ, htr⟩ := hw
  refine ⟨σ, hσ, ?_⟩
  ext θ
  have h := congrArg (fun f : freeLoop U => f θ) htr
  change q (diskBoundary θ) = γU (σ θ) at h
  change (q (diskBoundary θ) : N) = γ (σ θ)
  rw [h, hγγ]

/-- **G1″（open target）.**  `q` 是 open target `U` 上关于 `G` 的 Morrey 盘，`G = g|_U` 在 `W` 上，
`W ⊆ U`，`range (ι ∘ q) ⊆ W`，`ι ∘ γU = γ`：则 `ι ∘ q` 的 `g`-面积等于 `morreyLeastAreaS g W γ`。
`≥`：每个光滑竞争者 `v`（range ⊆ `W` ⊆ `U`）提升成 `U` 里的光滑盘，`G`-Lipschitz，
`minimizesLipschitz` 给 `area_G q ≤ area_G ṽ`，再换回 `g`-面积。 -/
theorem morreyLeastAreaS_eq_area_open_AT [T3Space N]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) (U : TopologicalSpace.Opens N)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {W : Set N} (hWU : W ⊆ U)
    (hG : ∀ x : U, (x : N) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    (hd : Module.finrank ℝ E = 3) {γU : freeLoop U} {γ : freeLoop N}
    (hγγ : ∀ θ, (γU θ : N) = γ θ) (hγ : IsSmoothEmbeddedLoop (E := E) γU)
    {q : C(closedDisk, U)} (hq : IsMorreyDisk G γU q)
    (hqW : Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, N)).comp q) ⊆ W) :
    riemannianDiskArea g ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, N)).comp q) =
      morreyLeastAreaS g W γ := by
  let ι : C(U, N) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨Q, hQ⟩ := hq.exists_smooth_extension G hd hγ
  have hQι : SmoothDiskExtension (E := E) (ι.comp q) (ι ∘ Q) := hQ.comp ι contMDiff_subtype_val
  have hqS := hQι.smoothUpToBoundary
  have hweak : DiskWeakJordanTrace γ (ι.comp q) := diskWeakJordanTrace_comp_val_AT hγγ hq.trace
  have hareaq : riemannianDiskArea g (ι.comp q) = riemannianDiskArea G q := by
    have h1 : riemannianDiskArea G q = riemannianDiskArea (g.restrictOpen U) q :=
      riemannianDiskArea_congr_inner_AT (fun z => hG (q z) (hqW ⟨z, rfl⟩))
    rw [h1, riemannianDiskArea_restrictOpen]
    rfl
  apply le_antisymm
  · refine le_csInf ⟨_, ι.comp q, ⟨hqS, hweak, hqW⟩, rfl⟩ ?_
    rintro _ ⟨v, ⟨hv, hw, hWv⟩, rfl⟩
    have hvU : Set.range v ⊆ U := fun x hx => hWU (hWv hx)
    have hvS := diskSmoothUpToBoundary_liftToOpen_AT hv hvU
    have hwU := diskWeakJordanTrace_liftToOpen_AT hγγ hw hvU
    have h1 : riemannianDiskArea G q ≤ riemannianDiskArea G (liftToOpen_AT v hvU) :=
      hq.minimizesLipschitz _ hwU (hvS.exists_lipschitz G)
    have h2 : riemannianDiskArea G (liftToOpen_AT v hvU) = riemannianDiskArea g v := by
      have h3 : riemannianDiskArea G (liftToOpen_AT v hvU) =
          riemannianDiskArea (g.restrictOpen U) (liftToOpen_AT v hvU) :=
        riemannianDiskArea_congr_inner_AT
          (fun z => hG (liftToOpen_AT v hvU z) (hWv ⟨z, rfl⟩))
      rw [h3, riemannianDiskArea_restrictOpen]
      rfl
    rw [hareaq]
    exact h1.trans h2.le
  · exact morreyLeastAreaS_le g hqS hweak hqW

/-- Consumer of G1″（minimizer-attained 形状，open target）：`ι ∘ q` 本身属于光滑类，
面积等于 `morreyLeastAreaS g W γ`。这是 Route W 里 `hasExteriorDiskMinimizersAfter`
的 Morrey 对应物的单时刻内容。 -/
theorem exists_attained_morreyLeastAreaS_open_AT [T3Space N]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) (U : TopologicalSpace.Opens N)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U) {W : Set N} (hWU : W ⊆ U)
    (hG : ∀ x : U, (x : N) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    (hd : Module.finrank ℝ E = 3) {γU : freeLoop U} {γ : freeLoop N}
    (hγγ : ∀ θ, (γU θ : N) = γ θ) (hγ : IsSmoothEmbeddedLoop (E := E) γU)
    {q : C(closedDisk, U)} (hq : IsMorreyDisk G γU q)
    (hqW : Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, N)).comp q) ⊆ W) :
    ∃ v : C(closedDisk, N), DiskSmoothUpToBoundary (E := E) v ∧ DiskWeakJordanTrace γ v ∧
      Set.range v ⊆ W ∧ riemannianDiskArea g v = morreyLeastAreaS g W γ := by
  obtain ⟨Q, hQ⟩ := hq.exists_smooth_extension G hd hγ
  have hQι := hQ.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(U, N)) contMDiff_subtype_val
  exact ⟨_, hQι.smoothUpToBoundary, diskWeakJordanTrace_comp_val_AT hγγ hq.trace, hqW,
    morreyLeastAreaS_eq_area_open_AT g U G hWU hG hd hγγ hγ hq hqW⟩

end OpenTarget

end DifferentialGeometry.Geometry
