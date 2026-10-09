import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# F3-a 定义层：实解析 compatible atlas 与 analytic metric（O-MY-F3A G1，后缀 `_F3A`）

D-R-MY2-14 的接口（scratch 原型 `MYD3/R06R07.lean:38–60`）落树：
- `IsAnalyticCompatibleAtlas_F3A P 𝒜`：chart 都在 maximal `C^∞` atlas 里、覆盖 `P`，transition
  `e' ∘ e.symm` 只在 `e '' (P ∩ e.source ∩ e'.source)` 上 `AnalyticOn ℝ`（`P` 之外的 overlap 不要求）。
- `metricCoeff_F3A`、`IsAnalyticMetricOn_F3A`、`MetricTendstoCInftyOn_F3A`、`IsAnalyticFunOn_F3A`。
- 基本引理：sub-atlas、限制到子集、`restrOpen` 到开集 `P`（D-14 的"令 chart source ⊆ P"写法）、
  开集上 `AnalyticOn` ⇒ `AnalyticOnNhd`。
- 与 Mathlib `IsManifold 𝓘(ℝ, E) ω M` 的双向桥：ω-流形的 maximal ω-atlas（以及 `atlas E M`）对任意 `P`
  是 compatible atlas；反过来 `atlas E M` 在 `univ` 上 compatible ⇒ `IsManifold 𝓘(ℝ, E) ω M`。
- consumer：Mathlib 的 ω-流形 `Metric.sphere` 上 maximal ω-atlas 给 compatible atlas（文件末 `example`）。

不新建 `ChartedSpace` 实例；接口全是显式 `Prop`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

section Atlas

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M]

/-- D-R-MY2-14：开集 `P` 上与原光滑结构兼容的实解析 atlas。chart 都在 maximal `C^∞` atlas 里、覆盖 `P`，
transition `e' ∘ e.symm` 在 `e '' (P ∩ e.source ∩ e'.source)` 上 `AnalyticOn ℝ`
（不要求 `P` 外的 overlap）。 -/
structure IsAnalyticCompatibleAtlas_F3A (P : Set M) (𝒜 : Set (OpenPartialHomeomorph M E)) :
    Prop where
  /-- 每个 chart 都在 maximal `C^∞` atlas 里（与原光滑结构兼容）。 -/
  mem_maximalAtlas : ∀ e ∈ 𝒜, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  /-- chart source 覆盖 `P`。 -/
  subset_iUnion_source : P ⊆ ⋃ e ∈ 𝒜, e.source
  /-- transition 只在 `P` 上的 overlap 解析。 -/
  analyticOn_transition : ∀ e ∈ 𝒜, ∀ e' ∈ 𝒜,
    AnalyticOn ℝ (e' ∘ e.symm) (e '' (P ∩ e.source ∩ e'.source))

/-- 与 scratch 合同 `IsAnalyticCompatibleAtlas_MYD3` 的合取形逐字等价（型对齐用）。 -/
theorem isAnalyticCompatibleAtlas_F3A_iff {P : Set M} {𝒜 : Set (OpenPartialHomeomorph M E)} :
    IsAnalyticCompatibleAtlas_F3A P 𝒜 ↔
      (∀ e ∈ 𝒜, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) ∧ (P ⊆ ⋃ e ∈ 𝒜, e.source) ∧
        ∀ e ∈ 𝒜, ∀ e' ∈ 𝒜, AnalyticOn ℝ (e' ∘ e.symm) (e '' (P ∩ e.source ∩ e'.source)) :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

namespace IsAnalyticCompatibleAtlas_F3A

variable {P Q : Set M} {𝒜 𝒜' : Set (OpenPartialHomeomorph M E)}

/-- `P` 的每一点落在某个 chart 的 source 里。 -/
theorem exists_mem_source (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) {x : M} (hx : x ∈ P) :
    ∃ e ∈ 𝒜, x ∈ e.source := by
  simpa only [mem_iUnion, exists_prop] using h.subset_iUnion_source hx

/-- 子图册：仍覆盖 `P` 的 sub-atlas 仍然 compatible。 -/
theorem mono_atlas (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hsub : 𝒜' ⊆ 𝒜)
    (hcov : P ⊆ ⋃ e ∈ 𝒜', e.source) : IsAnalyticCompatibleAtlas_F3A P 𝒜' where
  mem_maximalAtlas e he := h.mem_maximalAtlas e (hsub he)
  subset_iUnion_source := hcov
  analyticOn_transition e he e' he' := h.analyticOn_transition e (hsub he) e' (hsub he')

/-- 限制到子集 `Q ⊆ P`（特别是开子集）。 -/
theorem mono_set (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hQ : Q ⊆ P) :
    IsAnalyticCompatibleAtlas_F3A Q 𝒜 where
  mem_maximalAtlas := h.mem_maximalAtlas
  subset_iUnion_source := hQ.trans h.subset_iUnion_source
  analyticOn_transition e he e' he' :=
    (h.analyticOn_transition e he e' he').mono
      (image_mono (inter_subset_inter_left _ (inter_subset_inter_left _ hQ)))

/-- 两个 chart 都在 compatible atlas 里时，`P` 开 ⇒ transition 在 `P` 上的 overlap 是 `AnalyticOnNhd`。 -/
theorem analyticOnNhd_transition (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hP : IsOpen P)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (he' : e' ∈ 𝒜) :
    AnalyticOnNhd ℝ (e' ∘ e.symm) (e '' (P ∩ e.source ∩ e'.source)) := by
  have hopen : IsOpen (e '' (P ∩ e.source ∩ e'.source)) :=
    e.isOpen_image_of_subset_source ((hP.inter e.open_source).inter e'.open_source)
      (inter_subset_left.trans inter_subset_right)
  exact hopen.analyticOn_iff_analyticOnNhd.mp (h.analyticOn_transition e he e' he')

/-- 点态版：`x ∈ P ∩ e.source ∩ e'.source` ⇒ transition 在 `e x` 处解析。 -/
theorem analyticAt_transition (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hP : IsOpen P)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (he' : e' ∈ 𝒜) {x : M} (hx : x ∈ P)
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) : AnalyticAt ℝ (e' ∘ e.symm) (e x) :=
  h.analyticOnNhd_transition hP he he' (e x) ⟨x, ⟨⟨hx, hxe⟩, hxe'⟩, rfl⟩

/-- D-14 的"令 chart source ⊆ P"写法：source 都含于 `P` 时，transition 在整个 overlap 上解析。 -/
theorem analyticOn_transition_of_source_subset (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (he' : e' ∈ 𝒜) (hsrc : e.source ⊆ P) :
    AnalyticOn ℝ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have hset : e '' (P ∩ e.source ∩ e'.source) = e.target ∩ e.symm ⁻¹' e'.source := by
    rw [inter_assoc, inter_eq_right.mpr (inter_subset_left.trans hsrc), e.image_source_inter_eq']
  rw [← hset]
  exact h.analyticOn_transition e he e' he'

end IsAnalyticCompatibleAtlas_F3A

/-- 把每个 chart 限制到开集 `U`。 -/
def restrOpenAtlas_F3A (𝒜 : Set (OpenPartialHomeomorph M E)) (U : Set M) :
    Set (OpenPartialHomeomorph M E) :=
  (fun e => e.restr U) '' 𝒜

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem source_subset_of_mem_restrOpenAtlas_F3A {𝒜 : Set (OpenPartialHomeomorph M E)}
    {U : Set M} (hU : IsOpen U) {e : OpenPartialHomeomorph M E}
    (he : e ∈ restrOpenAtlas_F3A 𝒜 U) : e.source ⊆ U := by
  obtain ⟨e₀, -, rfl⟩ := he
  rw [e₀.restr_source' U hU]
  exact inter_subset_right

/-- 限制到开集 `U`：`P` 上 compatible 的 atlas 限制到 `U` 后在 `P ∩ U` 上 compatible，且 source ⊆ `U`。 -/
theorem IsAnalyticCompatibleAtlas_F3A.restrOpen {P U : Set M}
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    (hU : IsOpen U) : IsAnalyticCompatibleAtlas_F3A (P ∩ U) (restrOpenAtlas_F3A 𝒜 U) where
  mem_maximalAtlas := by
    rintro _ ⟨e, he, rfl⟩
    exact restr_mem_maximalAtlas _ (h.mem_maximalAtlas e he) hU
  subset_iUnion_source := by
    rintro x ⟨hxP, hxU⟩
    obtain ⟨e, he, hxe⟩ := h.exists_mem_source hxP
    refine mem_iUnion₂.mpr ⟨e.restr U, ⟨e, he, rfl⟩, ?_⟩
    rw [e.restr_source' U hU]
    exact ⟨hxe, hxU⟩
  analyticOn_transition := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    refine (h.analyticOn_transition e he e' he').mono ?_
    rintro _ ⟨x, ⟨⟨⟨hxP, -⟩, hxe⟩, hxe'⟩, rfl⟩
    rw [e.restr_source' U hU] at hxe
    rw [e'.restr_source' U hU] at hxe'
    exact ⟨x, ⟨⟨hxP, hxe.1⟩, hxe'.1⟩, rfl⟩

/-- `P` 开时，限制到 `P` 本身：source ⊆ `P`，于是 transition 在整个 overlap 上解析（D-14 第二写法）。 -/
theorem IsAnalyticCompatibleAtlas_F3A.restrOpen_self {P : Set M}
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    (hP : IsOpen P) :
    IsAnalyticCompatibleAtlas_F3A P (restrOpenAtlas_F3A 𝒜 P) ∧
      ∀ e ∈ restrOpenAtlas_F3A 𝒜 P, ∀ e' ∈ restrOpenAtlas_F3A 𝒜 P,
        AnalyticOn ℝ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h' : IsAnalyticCompatibleAtlas_F3A P (restrOpenAtlas_F3A 𝒜 P) := by
    simpa only [inter_self] using h.restrOpen hP
  exact ⟨h', fun e he e' he' => h'.analyticOn_transition_of_source_subset he he'
    (source_subset_of_mem_restrOpenAtlas_F3A hP he)⟩

/-! ## 与 Mathlib `IsManifold 𝓘(ℝ, E) ω M` 的桥 -/

/-- maximal ω-atlas 里两个 chart 的 transition 在整个 overlap 上解析。 -/
theorem analyticOn_transition_of_mem_maximalAtlas_omega_F3A {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ω M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ω M) :
    AnalyticOn ℝ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have hc := IsManifold.compatible_of_mem_maximalAtlas he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hc
  have h1 := hc.1
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, id_eq, inter_univ, Function.id_comp, Function.comp_id,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h1
  exact h1.analyticOn

variable (M) in
/-- 桥（正向）：`M` 是 ω-流形 ⇒ maximal ω-atlas 对任意 `P` 是 compatible analytic atlas。 -/
theorem isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A [IsManifold 𝓘(ℝ, E) ω M] (P : Set M) :
    IsAnalyticCompatibleAtlas_F3A P (IsManifold.maximalAtlas 𝓘(ℝ, E) ω M) where
  mem_maximalAtlas _ he := IsManifold.maximalAtlas_subset_of_le le_top he
  subset_iUnion_source x _ :=
    mem_iUnion₂.mpr ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x⟩
  analyticOn_transition e he e' he' :=
    (analyticOn_transition_of_mem_maximalAtlas_omega_F3A he he').mono (by
      rintro _ ⟨x, ⟨⟨-, hxe⟩, hxe'⟩, rfl⟩
      exact ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hxe'⟩)

variable (M) in
/-- 桥（正向，原 atlas 版）：ω-流形自带的 `atlas E M` 对任意 `P` 是 compatible analytic atlas。 -/
theorem isAnalyticCompatibleAtlas_atlas_omega_F3A [IsManifold 𝓘(ℝ, E) ω M] (P : Set M) :
    IsAnalyticCompatibleAtlas_F3A P (atlas E M) :=
  (isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A M P).mono_atlas
    IsManifold.subset_maximalAtlas fun x _ =>
      mem_iUnion₂.mpr ⟨chartAt E x, chart_mem_atlas E x, mem_chart_source E x⟩

/-- 桥（反向）：自带 `atlas E M` 在 `univ` 上 compatible ⇒ `M` 是 ω-流形（不新建 `ChartedSpace`）。 -/
theorem isManifold_omega_of_isAnalyticCompatibleAtlas_F3A
    (h : IsAnalyticCompatibleAtlas_F3A (univ : Set M) (atlas E M)) :
    IsManifold 𝓘(ℝ, E) ω M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have hset : e '' (univ ∩ e.source ∩ e'.source) = e.target ∩ e.symm ⁻¹' e'.source := by
    rw [univ_inter, e.image_source_inter_eq']
  have ha := h.analyticOn_transition e he e' he'
  rw [hset] at ha
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) :=
    e.isOpen_inter_preimage_symm e'.open_source
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id_eq,
    inter_univ, Function.id_comp, Function.comp_id, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.coe_trans]
  exact ha.contDiffOn hopen.uniqueDiffOn

/-- 双向桥合在一起：`IsManifold 𝓘(ℝ, E) ω M` ⇔ 自带 atlas 在 `univ` 上 compatible。 -/
theorem isManifold_omega_iff_isAnalyticCompatibleAtlas_F3A :
    IsManifold 𝓘(ℝ, E) ω M ↔ IsAnalyticCompatibleAtlas_F3A (univ : Set M) (atlas E M) :=
  ⟨fun _ => isAnalyticCompatibleAtlas_atlas_omega_F3A M univ,
    isManifold_omega_of_isAnalyticCompatibleAtlas_F3A⟩

end Atlas

/-! ## analytic 函数、度量系数、`C^∞` 收敛 -/

section Metric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M]

/-- `f : M → F` 在 `P` 上对 atlas `𝒜` 实解析：每个 chart 下 `f ∘ e.symm` 在 `e '' (P ∩ e.source)` 上解析。 -/
def IsAnalyticFunOn_F3A {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (𝒜 : Set (OpenPartialHomeomorph M E)) (P : Set M) (f : M → F) : Prop :=
  ∀ e ∈ 𝒜, AnalyticOn ℝ (f ∘ e.symm) (e '' (P ∩ e.source))

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- chart `e` 中的度量系数 `y ↦ G_{e.symm y}(D(e.symm)_y ξ, D(e.symm)_y η)`（同 `metricCoeff_MYD3`）。 -/
def metricCoeff_F3A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (ξ η : E) (y : E) : ℝ :=
  G.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)

/-- `G` 在 `P` 上对 atlas `𝒜` 实解析：所有系数 `metricCoeff_F3A G e ξ η` 在 `e '' (P ∩ e.source)` 上解析。 -/
def IsAnalyticMetricOn_F3A (𝒜 : Set (OpenPartialHomeomorph M E)) (P : Set M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  ∀ e ∈ 𝒜, ∀ ξ η : E, AnalyticOn ℝ (metricCoeff_F3A G e ξ η) (e '' (P ∩ e.source))

/-- `Gn → G` 在 `C` 上 chart-`C^∞`：maximal `C^∞` atlas 的每个 chart、`e.target ∩ e.symm ⁻¹' C` 内的每个
紧集 `C'`、每阶 `k`，系数的 `k` 阶导数一致收敛（同 `MetricTendstoCInftyOn_MYD3`）。 -/
def MetricTendstoCInftyOn_F3A (Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (C : Set M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M, ∀ C' : Set E, IsCompact C' →
    C' ⊆ e.target ∩ e.symm ⁻¹' C → ∀ (k : ℕ) (ξ η : E),
      TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (metricCoeff_F3A (Gn n) e ξ η))
        (iteratedFDeriv ℝ k (metricCoeff_F3A G e ξ η)) atTop C'

theorem IsAnalyticMetricOn_F3A.mono_atlas {𝒜 𝒜' : Set (OpenPartialHomeomorph M E)} {P : Set M}
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (h : IsAnalyticMetricOn_F3A 𝒜 P G) (hsub : 𝒜' ⊆ 𝒜) :
    IsAnalyticMetricOn_F3A 𝒜' P G :=
  fun e he => h e (hsub he)

theorem IsAnalyticMetricOn_F3A.mono_set {𝒜 : Set (OpenPartialHomeomorph M E)} {P Q : Set M}
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (h : IsAnalyticMetricOn_F3A 𝒜 P G) (hQ : Q ⊆ P) :
    IsAnalyticMetricOn_F3A 𝒜 Q G :=
  fun e he ξ η => (h e he ξ η).mono (image_mono (inter_subset_inter_left _ hQ))

theorem MetricTendstoCInftyOn_F3A.mono {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {C D : Set M} (h : MetricTendstoCInftyOn_F3A Gn G C)
    (hD : D ⊆ C) : MetricTendstoCInftyOn_F3A Gn G D :=
  fun e he C' hC' hsub k ξ η =>
    h e he C' hC' (hsub.trans (inter_subset_inter_right _ (preimage_mono hD))) k ξ η

/-- 常序列在任意 `C` 上 chart-`C^∞` 收敛（`MetricTendstoCInftyOn_F3A` 非空）。 -/
theorem metricTendstoCInftyOn_const_F3A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (C : Set M) :
    MetricTendstoCInftyOn_F3A (fun _ => G) G C :=
  fun _ _ _ _ _ _ _ _ _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

end Metric

/-! ## consumer（G1）：Mathlib 的 ω-流形 `sphere` 上，maximal ω-atlas 对任意 `P` 是 compatible atlas -/

example (n : ℕ) (P : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    IsAnalyticCompatibleAtlas_F3A P
      (IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A _ P

end DifferentialGeometry.Geometry.Analytic
