import DifferentialGeometry.Geometry.Analytic.ChartIndependenceF3A
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# F3-a：R6b 的输入形状——analytic embedding / Euclidean extension 数据（O-MY-F3A G3，后缀 `_F3A`）

D-R-MY2-9/14：R6b 的 F3-b 卷积要的 analytic embedding / extension 数据**不能**从
`IsAnalyticCompatibleAtlas_F3A` 的字段读出，必须单独给。本文件把它写成显式 structure
`AnalyticExtensionData_F3A G P F`：
- `atlas`：`P` 上的 compatible analytic atlas；
- `embed : M → F`：在 `atlas` 下于 `P` 上解析（F3-b 不需要单射 / immersion：`G = embed^* ext` 已迫使 `D embed` 单射）；
- `ext : F → (F →L F →L ℝ)`：`C^∞` 的 Euclidean 延拓，满足 `G = embed^* ext`（chart 系数逐点，
  `metricCoeff_F3A G e = pullbackCoeff_F3A embed ext e`）。
F3-b 的用法（`isAnalyticMetricOn_of_coeff_eq`）：把 `ext` 换成任一解析 `H`（Gaussian 卷积 = 整函数），
系数等于 `pullbackCoeff_F3A embed H` 的度量就对 `atlas` 解析。

生产者：
- `AnalyticExtensionData_F3A.ofOmega`：`M` 是 ω-流形 + **显式前提**（`ContMDiffOn ω` 的 `Φ`、`C^∞` 的 `H`、
  流形层面的延拓恒等式 `G = Φ^* H`）⇒ 数据（`atlas` = maximal ω-atlas）。前提就是 Mathlib 缺的
  analytic Whitney 嵌入 + 管状邻域延拓（Mathlib 只有**光滑**紧 Whitney 嵌入
  `SmoothBumpCovering.exists_embedding_euclidean_of_compact`）。
- `nonempty_analyticExtensionData_of_chart_F3A`：**无前提**的单 chart 情形——`P` 落在一个 ω-chart `e₀` 里且
  `e₀ '' P` 含于 `e₀.target` 中的紧集：取 `Φ = e₀`、`H = χ • (G 在 e₀ 中的系数)`（`χ` 为光滑 cutoff）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Analytic

section Pullback

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `F` 上的双线性场 `H` 经 `Φ : M → F` 拉回后在 chart `e` 中的系数：
`y ↦ H_{Φ(e.symm y)}(D(Φ ∘ e.symm)_y ξ, D(Φ ∘ e.symm)_y η)`。 -/
def pullbackCoeff_F3A (Φ : M → F) (H : F → F →L[ℝ] F →L[ℝ] ℝ) (e : OpenPartialHomeomorph M E)
    (ξ η y : E) : ℝ :=
  H (Φ (e.symm y)) (fderiv ℝ (Φ ∘ e.symm) y ξ) (fderiv ℝ (Φ ∘ e.symm) y η)

omit [TopologicalSpace M] [ChartedSpace E M] in
/-- 解析的 CLM 值函数作用在解析向量上仍解析（`ContinuousLinearMap.analyticAt_bilinear`）。 -/
theorem analyticAt_clm_apply_F3A {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {B : E → W →L[ℝ] X} {u : E → W} {y : E}
    (hB : AnalyticAt ℝ B y) (hu : AnalyticAt ℝ u y) : AnalyticAt ℝ (fun z => B z (u z)) y := by
  have h : AnalyticAt ℝ (fun p : (W →L[ℝ] X) × W => p.1 p.2) (B y, u y) :=
    (ContinuousLinearMap.id ℝ (W →L[ℝ] X)).analyticAt_bilinear (B y, u y)
  exact h.comp (f := fun z => (B z, u z)) (hB.prod hu)

omit [ChartedSpace E M] in
/-- 拉回系数解析：`Φ` 在 `𝒜` 下于 `P`（开）上解析、`H` 在 `Φ(P)` 上解析 ⇒ 每个 chart `e ∈ 𝒜` 中
`pullbackCoeff_F3A Φ H e ξ η` 在 `e '' (P ∩ e.source)` 上 `AnalyticOnNhd`。 -/
theorem analyticOnNhd_pullbackCoeff_F3A [CompleteSpace F] {𝒜 : Set (OpenPartialHomeomorph M E)}
    {P : Set M} (hP : IsOpen P) {Φ : M → F} (hΦ : IsAnalyticFunOn_F3A 𝒜 P Φ)
    {H : F → F →L[ℝ] F →L[ℝ] ℝ} (hH : ∀ x ∈ P, AnalyticAt ℝ H (Φ x))
    {e : OpenPartialHomeomorph M E} (he : e ∈ 𝒜) (ξ η : E) :
    AnalyticOnNhd ℝ (pullbackCoeff_F3A Φ H e ξ η) (e '' (P ∩ e.source)) := by
  have hopen : IsOpen (e '' (P ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hP.inter e.open_source) inter_subset_right
  have hΦe : AnalyticOnNhd ℝ (Φ ∘ e.symm) (e '' (P ∩ e.source)) :=
    hopen.analyticOn_iff_analyticOnNhd.mp (hΦ e he)
  rintro _ ⟨x, ⟨hx, hxe⟩, rfl⟩
  have hy : e x ∈ e '' (P ∩ e.source) := ⟨x, ⟨hx, hxe⟩, rfl⟩
  have hD : ∀ v : E, AnalyticAt ℝ (fun z => fderiv ℝ (Φ ∘ e.symm) z v) (e x) := fun v =>
    analyticAt_clm_apply_F3A (hΦe (e x) hy).fderiv analyticAt_const
  have hHΦ : AnalyticAt ℝ (fun z => H (Φ (e.symm z))) (e x) := by
    have hpt : (Φ ∘ e.symm) (e x) = Φ x := by simp only [Function.comp_apply, e.left_inv hxe]
    exact (hH x hx).fun_comp_of_eq (hΦe (e x) hy) hpt
  exact analyticAt_clm_apply_F3A (analyticAt_clm_apply_F3A hHΦ (hD ξ)) (hD η)

end Pullback

section Data

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **R6b 的输入形状**（D-R-MY2-9/14）：`P` 上 F3-b 卷积所需的 analytic embedding / Euclidean extension
数据。`atlas` 是 `P` 上的 compatible analytic atlas，`embed` 在其下解析，`ext` 是 `F` 上 `C^∞` 的双线性场，
且在 `P` 上 `G = embed^* ext`（每个 chart 的系数逐点相等）。 -/
structure AnalyticExtensionData_F3A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (P : Set M)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- `P` 上的 analytic atlas。 -/
  atlas : Set (OpenPartialHomeomorph M E)
  /-- `atlas` 在 `P` 上 compatible（D-14）。 -/
  isAnalyticCompatibleAtlas : IsAnalyticCompatibleAtlas_F3A P atlas
  /-- analytic embedding（只用到解析性）。 -/
  embed : M → F
  /-- `embed` 在 `atlas` 下于 `P` 上解析。 -/
  isAnalyticFunOn_embed : IsAnalyticFunOn_F3A atlas P embed
  /-- 卷积用的 Euclidean 延拓。 -/
  ext : F → F →L[ℝ] F →L[ℝ] ℝ
  /-- 延拓是 `C^∞`。 -/
  contDiff_ext : ContDiff ℝ ∞ ext
  /-- 在 `P` 上 `G = embed^* ext`（chart 系数）。 -/
  metricCoeff_eq : ∀ e ∈ atlas, ∀ y ∈ e '' (P ∩ e.source), ∀ ξ η : E,
    metricCoeff_F3A G e ξ η y = pullbackCoeff_F3A embed ext e ξ η y

/-- **F3-b 的消费形状**：把 `ext` 换成在 `embed(P)` 上解析的 `H`（Gaussian 卷积给整函数），
任何 chart 系数等于 `pullbackCoeff_F3A embed H` 的度量 `G'` 都对 `D.atlas` 在 `P` 上解析。 -/
theorem AnalyticExtensionData_F3A.isAnalyticMetricOn_of_coeff_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {P : Set M} (D : AnalyticExtensionData_F3A G P F)
    (hP : IsOpen P) {H : F → F →L[ℝ] F →L[ℝ] ℝ} (hH : ∀ x ∈ P, AnalyticAt ℝ H (D.embed x))
    {G' : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG' : ∀ e ∈ D.atlas, ∀ y ∈ e '' (P ∩ e.source), ∀ ξ η : E,
      metricCoeff_F3A G' e ξ η y = pullbackCoeff_F3A D.embed H e ξ η y) :
    IsAnalyticMetricOn_F3A D.atlas P G' := fun e he ξ η =>
  (analyticOnNhd_pullbackCoeff_F3A hP D.isAnalyticFunOn_embed hH he ξ η).analyticOn.congr
    fun y hy => hG' e he y hy ξ η

/-- `ext` 本身在 `embed(P)` 上解析时，`G` 自己对 `D.atlas` 解析（`G' = G`、`H = ext`）。 -/
theorem AnalyticExtensionData_F3A.isAnalyticMetricOn_of_analyticAt_ext {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {P : Set M} (D : AnalyticExtensionData_F3A G P F)
    (hP : IsOpen P) (hext : ∀ x ∈ P, AnalyticAt ℝ D.ext (D.embed x)) :
    IsAnalyticMetricOn_F3A D.atlas P G :=
  D.isAnalyticMetricOn_of_coeff_eq hP hext D.metricCoeff_eq

private theorem inner_eq_of_point_eq_F3A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p q : M}
    (hpq : p = q) (v w : E) : G.inner p v w = G.inner q v w := by
  subst hpq
  rfl

/-- **生产者（ω 情形 + 显式前提）**：`M` 是 ω-流形，`Φ` 在开集 `P` 上 `ContMDiffOn ω`，`H` 是 `C^∞`，
且流形层面 `G_x(v, w) = H_{Φ x}(DΦ_x v, DΦ_x w)`（`x ∈ P`）⇒ R6b 输入数据，`atlas` = maximal ω-atlas。
`Φ`、`H` 与延拓恒等式是 Mathlib 缺的 analytic Whitney 嵌入 + 管状邻域延拓，此处作为显式前提。 -/
def AnalyticExtensionData_F3A.ofOmega [IsManifold 𝓘(ℝ, E) ω M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {P : Set M}
    (hP : IsOpen P) (Φ : M → F) (hΦ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ω Φ P)
    (H : F → F →L[ℝ] F →L[ℝ] ℝ) (hH : ContDiff ℝ ∞ H)
    (hext : ∀ x ∈ P, ∀ v w : TangentSpace 𝓘(ℝ, E) x, G.inner x v w =
      H (Φ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ x w)) :
    AnalyticExtensionData_F3A G P F where
  atlas := IsManifold.maximalAtlas 𝓘(ℝ, E) ω M
  isAnalyticCompatibleAtlas := isAnalyticCompatibleAtlas_maximalAtlas_omega_F3A M P
  embed := Φ
  isAnalyticFunOn_embed := isAnalyticFunOn_maximalAtlas_omega_of_contMDiffOn_F3A hΦ
  ext := H
  contDiff_ext := hH
  metricCoeff_eq := by
    intro e he y hy ξ η
    obtain ⟨x, ⟨hx, hxe⟩, rfl⟩ := hy
    have hxP : e.symm (e x) ∈ P := by rw [e.left_inv hxe]; exact hx
    have he1 := IsManifold.maximalAtlas_subset_of_le (le_top : (1 : ℕ∞ω) ≤ ω) he
    have hsymm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) :=
      mdifferentiableAt_symm_of_mem_maximalAtlas he1 (e.map_source hxe)
    have hΦx : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (e.symm (e x)) :=
      ((hΦ _ hxP).contMDiffAt (hP.mem_nhds hxP)).mdifferentiableAt (by simp)
    have hchain : ∀ v : E, fderiv ℝ (Φ ∘ e.symm) (e x) v =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (e.symm (e x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) v) := by
      intro v
      have hc := mfderiv_comp (e x) hΦx hsymm
      have hf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (Φ ∘ e.symm) (e x) v = fderiv ℝ (Φ ∘ e.symm) (e x) v := by
        rw [mfderiv_eq_fderiv]
        rfl
      rw [← hf, hc]
      rfl
    simp only [metricCoeff_F3A, pullbackCoeff_F3A, hchain]
    exact hext _ hxP _ _

/-- 平坦化引理：`H = χ • B`，`B` 在开集 `U` 上 `C^∞`、`tsupport χ ⊆ U`、`χ` 处处 `C^∞` ⇒ `H` 处处 `C^∞`。 -/
theorem contDiff_smul_of_tsupport_subset_F3A {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : E → ℝ} {B : E → F} {U : Set E} (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hB : ContDiffOn ℝ ∞ B U) (hsupp : tsupport χ ⊆ U) : ContDiff ℝ ∞ (fun z => χ z • B z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.smul (hB.contDiffAt (hU.mem_nhds hz))
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hsupp h)
    refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with w hw
    simp only [hw, Pi.zero_apply, zero_smul]

/-- **生产者（无前提，单 chart 情形）**：`M` 是 ω-流形，`e₀` 是 ω-chart，`P` 开且 `P ⊆ e₀.source`、
`e₀ '' P ⊆ L`，`L` 是 `e₀.target` 里的紧集 ⇒ R6b 输入数据存在（`F = E`，`embed = e₀`，
`ext = χ • (G 在 e₀ 中的系数)`）。对任意光滑 `G` 成立——`AnalyticExtensionData_F3A` 的非空性。 -/
theorem nonempty_analyticExtensionData_of_chart_F3A [IsManifold 𝓘(ℝ, E) ω M]
    [FiniteDimensional ℝ E] (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e₀ : OpenPartialHomeomorph M E} (he₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ω M)
    {L : Set E} (hL : IsCompact L) (hLt : L ⊆ e₀.target) {P : Set M} (hP : IsOpen P)
    (hPs : P ⊆ e₀.source) (hPL : MapsTo e₀ P L) :
    Nonempty (AnalyticExtensionData_F3A G P E) := by
  obtain ⟨V, hVo, hLV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hL e₀.open_target hLt
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVo
    hL.isClosed hLV
  have hinf : (∞ : ℕ∞ω) ≤ ω := le_top
  have heInf := IsManifold.maximalAtlas_subset_of_le hinf he₀
  have he1 := IsManifold.maximalAtlas_subset_of_le (le_top : (1 : ℕ∞ω) ≤ ω) he₀
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := pullbackMetricCoefficients G e₀.symm
  have hB : ContDiffOn ℝ ∞ B e₀.target :=
    contDiffOn_pullback_metric_coefficients G e₀.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas heInf)
  have hsupp : tsupport χ ⊆ e₀.target := by
    rw [tsupport, hχs]
    exact hVU
  refine ⟨AnalyticExtensionData_F3A.ofOmega G hP e₀
    ((contMDiffOn_of_mem_maximalAtlas he₀).mono hPs) (fun z => χ z • B z)
    (contDiff_smul_of_tsupport_subset_F3A e₀.open_target hχ hB hsupp) ?_⟩
  intro x hx v w
  have hxs : x ∈ e₀.source := hPs hx
  have hmd : e₀.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨fun y hy => (mdifferentiableAt_of_mem_maximalAtlas he1 hy).mdifferentiableWithinAt,
      fun z hz => (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hz).mdifferentiableWithinAt⟩
  have hinv : ∀ u : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm (e₀ x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀ x u) = u := fun u =>
    congrArg (fun T : E →L[ℝ] E => T u) (hmd.symm_comp_deriv hxs)
  have hone : χ (e₀ x) = 1 := (hχ1 (e₀ x)).mp (hPL hx)
  simp only [hone, one_smul, B]
  change G.inner x v w = G.inner (e₀.symm (e₀ x))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm (e₀ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀ x v))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm (e₀ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀ x w))
  rw [hinv v, hinv w]
  exact inner_eq_of_point_eq_F3A G (e₀.left_inv hxs).symm v w

end Data

/-! ## consumer（G3）：Euclidean 空间中任意有界开集上的任意光滑度量都有 R6b 输入数据 -/

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) {P : Set E} (hP : IsOpen P)
    (hPc : IsCompact (closure P)) : Nonempty (AnalyticExtensionData_F3A G P E) := by
  obtain ⟨x⟩ : Nonempty E := inferInstance
  refine nonempty_analyticExtensionData_of_chart_F3A G
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ω) x) hPc ?_ hP ?_ ?_
  · rw [chartAt_self_eq]
    exact subset_univ _
  · rw [chartAt_self_eq]
    exact subset_univ _
  · rw [chartAt_self_eq]
    exact fun y hy => subset_closure hy

end DifferentialGeometry.Geometry.Analytic
