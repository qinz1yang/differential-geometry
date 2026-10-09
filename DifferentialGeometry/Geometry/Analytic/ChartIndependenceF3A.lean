import DifferentialGeometry.Geometry.Analytic.CompatibleAtlasF3A

/-!
# F3-a：analytic 函数与 analytic metric 的 chart-independence（O-MY-F3A G2a，后缀 `_F3A`）

compatible atlas 内，"chart 下 `AnalyticOn ℝ`" 与 chart 的选取无关：
- 函数：`f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)`，transition 解析 ⇒ 复合解析（`AnalyticAt.comp`）；
  局部判据 `isAnalyticFunOn_iff_forall_exists_F3A`，两个 atlas 的并 compatible ⇒ 解析性互传。
- 度量：换 chart 公式 `metricCoeff_F3A_eq_transition`（`D(e.symm) = D(e'.symm) ∘ Dτ`，`τ = e' ∘ e.symm`），
  用 basis 展开（`metricCoeff_F3A_eq_sum_basis`）把 `G_{e'}` 的系数与 `Dτ` 的系数相乘 ⇒ 解析。
- ω-流形：`ContMDiffOn ω` 的函数在 maximal ω-atlas 下是 `IsAnalyticFunOn_F3A`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

section Fun

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 单点换 chart：`x ∈ P ∩ e.source ∩ e'.source`，`f ∘ e'.symm` 在 `e' x` 解析 ⇒ `f ∘ e.symm` 在 `e x` 解析。 -/
theorem IsAnalyticCompatibleAtlas_F3A.analyticAt_comp_symm {P : Set M}
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    (hP : IsOpen P) {e e' : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (he' : e' ∈ 𝒜) {x : M}
    (hx : x ∈ P) (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) {f : M → F}
    (hf : AnalyticAt ℝ (f ∘ e'.symm) (e' x)) : AnalyticAt ℝ (f ∘ e.symm) (e x) := by
  have hτ := h.analyticAt_transition hP he he' hx hxe hxe'
  have hcomp : AnalyticAt ℝ ((f ∘ e'.symm) ∘ (e' ∘ e.symm)) (e x) :=
    hf.comp_of_eq hτ (by simp only [Function.comp_apply, e.left_inv hxe])
  refine hcomp.congr ?_
  have hmem : e.target ∩ e.symm ⁻¹' e'.source ∈ 𝓝 (e x) :=
    (e.isOpen_inter_preimage_symm e'.open_source).mem_nhds
      ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hxe'⟩
  filter_upwards [hmem] with y hy
  simp only [Function.comp_apply, e'.left_inv hy.2]

/-- 局部判据（chart-independence）：compatible atlas、`P` 开时，`f` 在 `𝒜` 的**每个** chart 下解析 ⇔
`P` 的每点在**某个** chart 下解析。 -/
theorem isAnalyticFunOn_iff_forall_exists_F3A {P : Set M} {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hP : IsOpen P) {f : M → F} :
    IsAnalyticFunOn_F3A 𝒜 P f ↔
      ∀ x ∈ P, ∃ e ∈ 𝒜, x ∈ e.source ∧ AnalyticAt ℝ (f ∘ e.symm) (e x) := by
  constructor
  · intro hf x hx
    obtain ⟨e, he, hxe⟩ := h.exists_mem_source hx
    have hopen : IsOpen (e '' (P ∩ e.source)) :=
      e.isOpen_image_of_subset_source (hP.inter e.open_source) inter_subset_right
    exact ⟨e, he, hxe, hopen.analyticOn_iff_analyticOnNhd.mp (hf e he) (e x) ⟨x, ⟨hx, hxe⟩, rfl⟩⟩
  · rintro hf e he _ ⟨x, ⟨hx, hxe⟩, rfl⟩
    obtain ⟨e', he', hxe', hfx⟩ := hf x hx
    exact (h.analyticAt_comp_symm hP he he' hx hxe hxe' hfx).analyticWithinAt

/-- 两个 atlas 的并 compatible（`𝒜` 覆盖 `P`）⇒ 在 `𝒜` 下解析的函数在 `𝒜'` 下也解析。 -/
theorem IsAnalyticFunOn_F3A.of_union {P : Set M} {𝒜 𝒜' : Set (OpenPartialHomeomorph M E)}
    (h : IsAnalyticCompatibleAtlas_F3A P (𝒜 ∪ 𝒜')) (hcov : P ⊆ ⋃ e ∈ 𝒜, e.source)
    (hP : IsOpen P) {f : M → F} (hf : IsAnalyticFunOn_F3A 𝒜 P f) : IsAnalyticFunOn_F3A 𝒜' P f := by
  have h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜 := h.mono_atlas subset_union_left hcov
  have hloc := (isAnalyticFunOn_iff_forall_exists_F3A h𝒜 hP).mp hf
  have hall : IsAnalyticFunOn_F3A (𝒜 ∪ 𝒜') P f :=
    (isAnalyticFunOn_iff_forall_exists_F3A h hP).mpr fun x hx => by
      obtain ⟨e, he, hxe, hfx⟩ := hloc x hx
      exact ⟨e, Or.inl he, hxe, hfx⟩
  exact fun e he => hall e (Or.inr he)

/-- `ContMDiffOn ω` 的函数在 maximal ω-atlas 下是 `IsAnalyticFunOn_F3A`（ω-流形时 maximal ω-atlas 覆盖 `M`；
本引理本身不需要 `IsManifold ω` 实例）。 -/
theorem isAnalyticFunOn_maximalAtlas_omega_of_contMDiffOn_F3A {P : Set M} {f : M → F}
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ω f P) :
    IsAnalyticFunOn_F3A (IsManifold.maximalAtlas 𝓘(ℝ, E) ω M) P f := by
  intro e he
  have hsymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ω e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  have hmaps : MapsTo e.symm (e '' (P ∩ e.source)) P := by
    rintro _ ⟨x, ⟨hx, hxe⟩, rfl⟩
    simpa only [e.left_inv hxe] using hx
  have hsub : e '' (P ∩ e.source) ⊆ e.target := by
    rintro _ ⟨x, ⟨-, hxe⟩, rfl⟩
    exact e.map_source hxe
  have hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ω (f ∘ e.symm) (e '' (P ∩ e.source)) :=
    hf.comp (hsymm.mono hsub) hmaps
  exact (contMDiffOn_iff_contDiffOn.mp hc).analyticOn

end Fun

section Metric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 双线性形式与线性映射复合后按 basis 展开（`TangentSpace` 与 `E` 只需 defeq，故类型取一般模）。 -/
theorem bilin_comp_eq_sum_basis_F3A {ι V W : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    (B : W →L[ℝ] W →L[ℝ] ℝ) (A : V →L[ℝ] W) (b : Module.Basis ι ℝ V) (ξ η : V) :
    B (A ξ) (A η) = ∑ i, ∑ j, (b.repr ξ i * b.repr η j) * B (A (b i)) (A (b j)) := by
  conv_lhs => rw [← b.sum_repr ξ, ← b.sum_repr η]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `metricCoeff_F3A` 对 `ξ, η` 双线性：按 basis `b` 展开。 -/
theorem metricCoeff_F3A_eq_sum_basis {ι : Type*} [Fintype ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (b : Module.Basis ι ℝ E) (ξ η y : E) :
    metricCoeff_F3A G e ξ η y =
      ∑ i, ∑ j, (b.repr ξ i * b.repr η j) * metricCoeff_F3A G e (b i) (b j) y :=
  bilin_comp_eq_sum_basis_F3A (V := E) (G.inner (e.symm y))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y) b ξ η

private theorem inner_congr_point_F3A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p q : M}
    (hpq : p = q) (v w : E) : G.inner p v w = G.inner q v w := by
  subst hpq
  rfl

/-- 换 chart 公式：`τ = e' ∘ e.symm`，`G_e(ξ, η)(y) = G_{e'}(Dτ_y ξ, Dτ_y η)(τ y)`。 -/
theorem metricCoeff_F3A_eq_transition (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) (ξ η : E) :
    metricCoeff_F3A G e ξ η y =
      metricCoeff_F3A G e' (fderiv ℝ (e' ∘ e.symm) y ξ) (fderiv ℝ (e' ∘ e.symm) y η)
        ((e' ∘ e.symm) y) := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := ENat.LEInfty.out
  have he1 := IsManifold.maximalAtlas_subset_of_le h1 he
  have he'1 := IsManifold.maximalAtlas_subset_of_le h1 he'
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y :=
    mdifferentiableAt_symm_of_mem_maximalAtlas he1 hy
  have hτ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (e' ∘ e.symm) y :=
    (mdifferentiableAt_of_mem_maximalAtlas he'1 hy').comp y hsymm
  have he'symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm ((e' ∘ e.symm) y) :=
    mdifferentiableAt_symm_of_mem_maximalAtlas he'1 (e'.map_source hy')
  have heq : e.symm =ᶠ[𝓝 y] e'.symm ∘ (e' ∘ e.symm) := by
    filter_upwards [(e.isOpen_inter_preimage_symm e'.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
    simp only [Function.comp_apply, e'.left_inv hz.2]
  have hD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm ((e' ∘ e.symm) y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e' ∘ e.symm) y) := by
    rw [heq.mfderiv_eq]
    exact mfderiv_comp y he'symm hτ
  have hDτ : ∀ v : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e' ∘ e.symm) y v = fderiv ℝ (e' ∘ e.symm) y v := by
    intro v
    rw [mfderiv_eq_fderiv]
    rfl
  have hpt : e.symm y = e'.symm ((e' ∘ e.symm) y) := by
    simp only [Function.comp_apply, e'.left_inv hy']
  have hv : ∀ v : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm ((e' ∘ e.symm) y) (fderiv ℝ (e' ∘ e.symm) y v) := by
    intro v
    rw [hD, ← hDτ v]
    rfl
  unfold metricCoeff_F3A
  rw [hv ξ, hv η]
  exact inner_congr_point_F3A G hpt _ _

/-- `Dτ` 的坐标 `y ↦ b.repr (Dτ_y ξ) i`：`τ` 在 `y` 解析 ⇒ 它在 `y` 解析（`AnalyticAt.fderiv`）。 -/
theorem analyticAt_repr_fderiv_apply_F3A [FiniteDimensional ℝ E] {ι : Type*}
    (b : Module.Basis ι ℝ E) {τ : E → E} {y : E} (hτ : AnalyticAt ℝ τ y) (ξ : E) (i : ι) :
    AnalyticAt ℝ (fun z => b.repr (fderiv ℝ τ z ξ) i) y := by
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℝ E ξ)
  have hL : AnalyticAt ℝ (fun z => L (fderiv ℝ τ z)) y := (L.analyticAt _).comp hτ.fderiv
  exact hL.congr (Eventually.of_forall fun z => rfl)

/-- 度量系数换 chart：`τ = e' ∘ e.symm` 在 `e x` 解析，`G` 在 chart `e'` 下系数在 `e' x` 解析 ⇒
在 chart `e` 下系数在 `e x` 解析。 -/
theorem analyticAt_metricCoeff_F3A_of_transition [FiniteDimensional ℝ E]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M} (hxe : x ∈ e.source)
    (hxe' : x ∈ e'.source) (hτ : AnalyticAt ℝ (e' ∘ e.symm) (e x))
    (hG : ∀ ξ η : E, AnalyticAt ℝ (metricCoeff_F3A G e' ξ η) (e' x)) (ξ η : E) :
    AnalyticAt ℝ (metricCoeff_F3A G e ξ η) (e x) := by
  let b := Module.finBasis ℝ E
  have hpt : (e' ∘ e.symm) (e x) = e' x := by simp only [Function.comp_apply, e.left_inv hxe]
  have hR : AnalyticAt ℝ (fun y => ∑ i, ∑ j,
      (b.repr (fderiv ℝ (e' ∘ e.symm) y ξ) i * b.repr (fderiv ℝ (e' ∘ e.symm) y η) j) *
        metricCoeff_F3A G e' (b i) (b j) ((e' ∘ e.symm) y)) (e x) := by
    refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((analyticAt_repr_fderiv_apply_F3A b hτ ξ i).mul
      (analyticAt_repr_fderiv_apply_F3A b hτ η j)).mul ((hG (b i) (b j)).fun_comp_of_eq hτ hpt)
  refine hR.congr ?_
  have hmem : e.target ∩ e.symm ⁻¹' e'.source ∈ 𝓝 (e x) :=
    (e.isOpen_inter_preimage_symm e'.open_source).mem_nhds
      ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hxe'⟩
  filter_upwards [hmem] with y hy
  rw [metricCoeff_F3A_eq_transition G he he' hy.1 hy.2, metricCoeff_F3A_eq_sum_basis G e' b]

/-- compatible atlas 内的度量换 chart（点态）。 -/
theorem IsAnalyticCompatibleAtlas_F3A.analyticAt_metricCoeff [FiniteDimensional ℝ E] {P : Set M}
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    (hP : IsOpen P) (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ 𝒜) (he' : e' ∈ 𝒜) {x : M} (hx : x ∈ P) (hxe : x ∈ e.source)
    (hxe' : x ∈ e'.source) (hG : ∀ ξ η : E, AnalyticAt ℝ (metricCoeff_F3A G e' ξ η) (e' x))
    (ξ η : E) : AnalyticAt ℝ (metricCoeff_F3A G e ξ η) (e x) :=
  analyticAt_metricCoeff_F3A_of_transition G (h.mem_maximalAtlas e he)
    (h.mem_maximalAtlas e' he') hxe hxe' (h.analyticAt_transition hP he he' hx hxe hxe') hG ξ η

/-- 度量的局部判据（chart-independence）：`G` 在 `𝒜` 每个 chart 下解析 ⇔ `P` 每点在某个 chart 下解析。 -/
theorem isAnalyticMetricOn_iff_forall_exists_F3A [FiniteDimensional ℝ E] {P : Set M}
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    (hP : IsOpen P) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} :
    IsAnalyticMetricOn_F3A 𝒜 P G ↔
      ∀ x ∈ P, ∃ e ∈ 𝒜, x ∈ e.source ∧ ∀ ξ η : E, AnalyticAt ℝ (metricCoeff_F3A G e ξ η) (e x) := by
  constructor
  · intro hG x hx
    obtain ⟨e, he, hxe⟩ := h.exists_mem_source hx
    have hopen : IsOpen (e '' (P ∩ e.source)) :=
      e.isOpen_image_of_subset_source (hP.inter e.open_source) inter_subset_right
    exact ⟨e, he, hxe, fun ξ η =>
      hopen.analyticOn_iff_analyticOnNhd.mp (hG e he ξ η) (e x) ⟨x, ⟨hx, hxe⟩, rfl⟩⟩
  · rintro hG e he ξ η _ ⟨x, ⟨hx, hxe⟩, rfl⟩
    obtain ⟨e', he', hxe', hGx⟩ := hG x hx
    exact (h.analyticAt_metricCoeff hP G he he' hx hxe hxe' hGx ξ η).analyticWithinAt

/-- 两个 atlas 的并 compatible（`𝒜` 覆盖 `P`）⇒ 在 `𝒜` 下解析的度量在 `𝒜'` 下也解析。 -/
theorem IsAnalyticMetricOn_F3A.of_union [FiniteDimensional ℝ E] {P : Set M}
    {𝒜 𝒜' : Set (OpenPartialHomeomorph M E)} (h : IsAnalyticCompatibleAtlas_F3A P (𝒜 ∪ 𝒜'))
    (hcov : P ⊆ ⋃ e ∈ 𝒜, e.source) (hP : IsOpen P) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) : IsAnalyticMetricOn_F3A 𝒜' P G := by
  have h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜 := h.mono_atlas subset_union_left hcov
  have hloc := (isAnalyticMetricOn_iff_forall_exists_F3A h𝒜 hP).mp hG
  have hall : IsAnalyticMetricOn_F3A (𝒜 ∪ 𝒜') P G :=
    (isAnalyticMetricOn_iff_forall_exists_F3A h hP).mpr fun x hx => by
      obtain ⟨e, he, hxe, hGx⟩ := hloc x hx
      exact ⟨e, Or.inl he, hxe, hGx⟩
  exact hall.mono_atlas subset_union_right

end Metric

end DifferentialGeometry.Geometry.Analytic
