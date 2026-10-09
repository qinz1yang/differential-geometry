import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4AMetric
import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3C
import DifferentialGeometry.Geometry.HarmonicMap.ChartTension

/-!
# F4-a（`_F4A`）模块 2：atlas chart 搬运 —— 把 `e ∘ F` 看成模型空间 `E` 里的 conformal harmonic 映射

树里的 tangent-graph height difference 机器（`TangentGraphGerms` / `MinimalGraphDifference`）只对
`M` 的原光滑 chart `chartAt E p` 成立，得到的 height difference `w` 只是 `C^∞`；而 F3C 的解析性
只对 analytic atlas `𝒜` 里的 chart `e` 成立（`chartAt ∘ e⁻¹` 一般不解析）。本模块把 `(G, F)` 经 `e`
搬到模型空间 `E`（`chartAt = refl`，`extChartAt = id`），度量用 cutoff 后的全局光滑度量 `g'`
（在目标点附近等于 `e` 下的度量系数），于是 `X = e ∘ F` 在 `(E, g')` 里仍 conformal + harmonic，
并且 `X` 本身解析——height difference 可以在 `X` 的坐标下做，天然解析。

* `exists_localModelMetric_F4A`：chart `e` 的度量系数在 `c ∈ e.target` 附近的闭球上 = 某全局光滑度量。
* `christoffel_F3A_congr_F4A` / `christoffelBilin_F3C_congr_F4A`：Christoffel 只依赖度量系数的 germ。
* `mfderiv_symm_comp_F4A`、`inner_eq_metricCoeff_F4A`：`D(e.symm)` 拉回、内积 = 度量系数。
* `diskMapTension_eq_zero_of_hzero_F4A`：`ChartTension` 末段，直接吃合并后的 `hzero`。
* **`chart_transfer_F4A`**：`DiskMapConformalAt G F` + `diskMapTension G F = 0` ⇒ `(g', e ∘ F)` 同样。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Analytic DifferentialGeometry.Analysis.Elliptic.HarmonicMap

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- chart `e` 的度量系数在 `c ∈ e.target` 附近的闭球上与某个全局光滑度量 `g'` 一致。 -/
theorem exists_localModelMetric_F4A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {c : E}
    (hc : c ∈ e.target) :
    ∃ (g' : SmoothRiemannianMetric 𝓘(ℝ, E) E) (r : ℝ), 0 < r ∧ closedBall c r ⊆ e.target ∧
      ∀ y ∈ closedBall c r, ∀ v w, g'.inner y v w = metricCoeff_F3A G e v w y := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target c hc
  have hr' : 0 < ε / 2 := half_pos hε
  have hsub : closedBall c (ε / 2) ⊆ e.target :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεsub
  obtain ⟨b, hb, hsymm, hpos, hbeq⟩ := exists_cutoff_form_F4A e.open_target (c := c)
    (r := ε / 4) (r' := ε / 2) (by linarith) (by linarith) hsub
    (b₀ := metricForm_F3C G e)
    (fun y hy => (contDiffAt_metricForm_F3C G he hy).contDiffWithinAt)
    (fun y _ v w => metricForm_F3C_symm G e y v w)
    (fun y hy v hv => by
      rw [metricForm_F3C_apply]
      exact metricCoeff_pos_F3C G he hy hv)
  obtain ⟨g', hg'⟩ := exists_modelMetric_F4A b hb hsymm hpos
  refine ⟨g', ε / 4, by linarith, (closedBall_subset_closedBall (by linarith)).trans hsub, ?_⟩
  intro y hy v w
  rw [hg', hbeq y hy]
  exact metricForm_F3C_apply G e y v w

omit [FiniteDimensional ℝ E] in
/-- Christoffel 系数只依赖度量系数在 `y` 的 germ。 -/
theorem christoffel_F3A_congr_F4A {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold 𝓘(ℝ, E) ∞ M'] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (G' : SmoothRiemannianMetric 𝓘(ℝ, E) M') (e' : OpenPartialHomeomorph M' E)
    (b : Module.Basis ι ℝ E) {y : E}
    (h : ∀ ξ η : E, metricCoeff_F3A G e ξ η =ᶠ[𝓝 y] metricCoeff_F3A G' e' ξ η) (i j k : ι) :
    christoffel_F3A G e b i j k y = christoffel_F3A G' e' b i j k y := by
  have hgram : metricGram_F3A G e b y = metricGram_F3A G' e' b y := by
    ext a c
    exact (h (b a) (b c)).self_of_nhds
  unfold christoffel_F3A
  rw [hgram]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(h (b l) (b j)).fderiv_eq, (h (b l) (b i)).fderiv_eq, (h (b i) (b j)).fderiv_eq]

theorem christoffelBilin_F3C_congr_F4A {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold 𝓘(ℝ, E) ∞ M'] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (G' : SmoothRiemannianMetric 𝓘(ℝ, E) M') (e' : OpenPartialHomeomorph M' E)
    (b : Module.Basis ι ℝ E) {y : E}
    (h : ∀ ξ η : E, metricCoeff_F3A G e ξ η =ᶠ[𝓝 y] metricCoeff_F3A G' e' ξ η) :
    christoffelBilin_F3C G e b y = christoffelBilin_F3C G' e' b y := by
  unfold christoffelBilin_F3C
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [christoffel_F3A_congr_F4A G e G' e' b h]

omit [FiniteDimensional ℝ E] in
/-- 模型空间 `E`（`chartAt = refl`）上的度量系数就是度量本身。 -/
theorem metricCoeff_F3A_model_F4A (g' : SmoothRiemannianMetric 𝓘(ℝ, E) E) (a : E) (ξ η y : E) :
    metricCoeff_F3A g' (chartAt E a) ξ η y = g'.inner y ξ η := by
  have h1 : (⇑(chartAt E a).symm : E → E) = id := by
    rw [chartAt_self_eq]
    rfl
  unfold metricCoeff_F3A
  rw [h1, mfderiv_id]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- chart 下的像的微分经 `e.symm` 的微分拉回原微分。 -/
theorem mfderiv_symm_comp_F4A {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {F : ℂ → M} {z : ℂ}
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z) (hz : F z ∈ e.source) (v : ℂ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (F z)) (fderiv ℝ (e ∘ F) z v) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z v := by
  have he1 := IsManifold.maximalAtlas_subset_of_le (ENat.LEInfty.out : (1 : ℕ∞ω) ≤ ∞) he
  have hXd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (e ∘ F) z := by
    have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e (F z) := contMDiffAt_of_mem_maximalAtlas he hz
    exact (he'.comp z hF).mdifferentiableAt (by simp)
  have hsd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (F z)) :=
    mdifferentiableAt_symm_of_mem_maximalAtlas he1 (e.map_source hz)
  have hloc : F =ᶠ[𝓝 z] e.symm ∘ (e ∘ F) := by
    filter_upwards [hF.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hz)] with w hw
    simp [e.left_inv hw]
  have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (F z))).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (e ∘ F) z) := by
    rw [hloc.mfderiv_eq]
    exact mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) z hsd hXd
  have h3 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (e ∘ F) z v = fderiv ℝ (e ∘ F) z v := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [h2]
  exact congrArg _ h3.symm

omit [FiniteDimensional ℝ E] in
/-- 度量沿 `F` 的内积 = chart 下的度量系数在 `D(e ∘ F)` 上的值。 -/
theorem inner_eq_metricCoeff_F4A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {F : ℂ → M} {z : ℂ} (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z) (hz : F z ∈ e.source)
    (v w : ℂ) :
    G.inner (F z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z w) =
      metricCoeff_F3A G e (fderiv ℝ (e ∘ F) z v) (fderiv ℝ (e ∘ F) z w) (e (F z)) := by
  unfold metricCoeff_F3A
  rw [mfderiv_symm_comp_F4A he hF hz, mfderiv_symm_comp_F4A he hF hz, e.left_inv hz]

open DifferentialGeometry.Geometry.Riemannian.Geodesic in
/-- 与 `diskMapTension_eq_zero_of_chart_laplacian` 同一结论，但直接吃 `hzero`（Euclidean 坐标已合并）。 -/
theorem diskMapTension_eq_zero_of_hzero_F4A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    {z : ℂ} (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source)
    (hzero : Laplacian.laplacian (extChartAt 𝓘(ℝ, E) p ∘ U) z +
      chartChristoffelContraction g p (fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z 1)
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z 1) ((extChartAt 𝓘(ℝ, E) p ∘ U) z) +
      chartChristoffelContraction g p (fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z Complex.I)
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z Complex.I) ((extChartAt 𝓘(ℝ, E) p ∘ U) z) = 0) :
    diskMapTension g U z = 0 := by
  have hchart := chart_planarTension g hU hsrc
  have hb : U z ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  let τ := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  apply (τ.continuousLinearEquivAt ℝ (U z) hb).injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq τ hb, map_zero]
  change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)
    (planarTension g U z) = 0
  exact hchart.trans hzero

open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Tensor.Coordinates in
/-- **chart 搬运**：`e` 是 maximal atlas 里的 chart、`F` 在开集 `s` 上光滑、conformal、harmonic、
像在 `e.source`；则在任意 `x₀ ∈ s` 附近的开集 `s'` 上，`e ∘ F : ℂ → E`（`E` 作为带 `chartAt = refl` 的
流形）对某个全局光滑度量 `g'`（在目标点附近等于 chart `e` 下的度量系数）仍 conformal + harmonic。 -/
theorem chart_transfer_F4A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {F : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (hFs : ∀ z ∈ s, F z ∈ e.source)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F s)
    (hconf : ∀ z ∈ s, DiskMapConformalAt G F z) (hharm : ∀ z ∈ s, diskMapTension G F z = 0)
    {x₀ : ℂ} (hx₀ : x₀ ∈ s) :
    ∃ (g' : SmoothRiemannianMetric 𝓘(ℝ, E) E) (s' : Set ℂ), IsOpen s' ∧ x₀ ∈ s' ∧ s' ⊆ s ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (e ∘ F) s' ∧
      (∀ z ∈ s', DiskMapConformalAt g' (e ∘ F) z) ∧
      (∀ z ∈ s', diskMapTension g' (e ∘ F) z = 0) ∧
      (∀ z' ∈ s, e (F z') = e (F x₀) → z' ∈ s') := by
  have hXs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (e ∘ F) s := by
    intro z hz
    have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z := hF.contMDiffAt (hs.mem_nhds hz)
    exact ((contMDiffAt_of_mem_maximalAtlas he (hFs z hz)).comp z hU).contMDiffWithinAt
  obtain ⟨g', r, hr, hrsub, hg'⟩ := exists_localModelMetric_F4A G he (e.map_source (hFs x₀ hx₀))
  have hcont : ContinuousOn (e ∘ F) s := hXs.continuousOn
  refine ⟨g', s ∩ (e ∘ F) ⁻¹' (ball (e (F x₀)) r), hcont.isOpen_inter_preimage hs isOpen_ball,
    ⟨hx₀, mem_ball_self hr⟩, inter_subset_left, hXs.mono inter_subset_left, ?_, ?_, ?_⟩
  · intro z hz
    have hzs := hz.1
    have hyz : e (F z) ∈ closedBall (e (F x₀)) r := ball_subset_closedBall hz.2
    have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z := hF.contMDiffAt (hs.mem_nhds hzs)
    have key : ∀ v w : ℂ, g'.inner ((e ∘ F) z)
        (diskMapPartial (e ∘ F) z v) (diskMapPartial (e ∘ F) z w) =
        G.inner (F z) (diskMapPartial F z v) (diskMapPartial F z w) := by
      intro v w
      rw [diskMapPartial, diskMapPartial, diskMapPartial, diskMapPartial,
        inner_eq_metricCoeff_F4A G he hU (hFs z hzs)]
      have h3 : ∀ u : ℂ, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (e ∘ F) z u = fderiv ℝ (e ∘ F) z u := by
        intro u
        rw [mfderiv_eq_fderiv]
        rfl
      rw [h3, h3]
      exact hg' _ hyz _ _
    unfold DiskMapConformalAt
    simp only [key]
    exact hconf z hzs
  · intro z hz
    have hzs := hz.1
    have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z := hF.contMDiffAt (hs.mem_nhds hzs)
    have hXz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (e ∘ F) z :=
      (contMDiffAt_of_mem_maximalAtlas he (hFs z hzs)).comp z hU
    have hF3 := laplacian_chart_eq_christoffelBilin_F3C G he (chartModelBasis E) hU
      (hFs z hzs) (hharm z hzs)
    set p : E := (e ∘ F) z with hp
    have hY : extChartAt 𝓘(ℝ, E) p ∘ (e ∘ F) = e ∘ F := by
      rw [extChartAt_model_space_eq_id]
      rfl
    have hbeq : christoffelBilin_F3C g' (chartAt E p) (chartModelBasis E) p =
        christoffelBilin_F3C G e (chartModelBasis E) p := by
      refine (christoffelBilin_F3C_congr_F4A G e g' (chartAt E p) (chartModelBasis E) ?_).symm
      intro ξ η
      filter_upwards [isOpen_ball.mem_nhds hz.2] with y hy
      rw [metricCoeff_F3A_model_F4A]
      exact (hg' y (ball_subset_closedBall hy) ξ η).symm
    refine diskMapTension_eq_zero_of_hzero_F4A g' (hXz.of_le two_le_infty_F3C) (p := p)
      (by simp [chartAt_self_eq]) ?_
    rw [hY]
    rw [chartChristoffelContraction_eq_christoffelBilin_F3C g' p (by simp [chartAt_self_eq]),
      chartChristoffelContraction_eq_christoffelBilin_F3C g' p (by simp [chartAt_self_eq]), hbeq]
    have hpe : p = e (F z) := rfl
    rw [hF3, hpe]
    abel
  · intro z' hz' h
    exact ⟨hz', by
      rw [mem_preimage, Function.comp_apply, h]
      exact mem_ball_self hr⟩

end DifferentialGeometry.Geometry
