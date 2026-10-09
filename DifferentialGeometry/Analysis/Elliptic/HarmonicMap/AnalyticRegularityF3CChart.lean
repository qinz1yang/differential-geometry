import DifferentialGeometry.Geometry.Analytic.ChristoffelBridgeF3A
import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian

/-!
# F3-c (c3)：harmonic map 的 chart 方程推广到任意 maximal-atlas chart（选项 (α)；O-MY-F3C G1）

lead 裁决 R8-AR 选项 (α)：树里的 chart 方程（`chart_planarTension`）只对 `chartAt E p`，而 R6b 的
analytic atlas `𝒜` 一般不含 `chartAt`。本文件对**任意** `e ∈ maximalAtlas ∞`：
* `metricForm_F3C G e y : E →L E →L ℝ`（chart `e` 中的度量形，`= metricCoeff_F3A`），`C^∞`（经 transition 到
  `chartAt`，用树里 `chartGramOnE_contDiffOn`）；
* `christoffelBilin_F3C G e b y : E →L E →L E`（`Σ christoffel_F3A G e b i j k y · ξ_i η_j b_k`）；
  `IsAnalyticMetricOn_F3A` ⇒ 在 `e '' (P ∩ e.source)` 上 `AnalyticOnNhd`；
* Koszul 刻画 `g_e(Γ_e(ξ,η), ζ) = K_e(ξ,η,ζ)` 与 Koszul 换 chart ⇒ **Christoffel 变换律**
  `Dφ Γ_e(ξ,η) = Γ_{e'}(Dφξ, Dφη) + D²φ(ξ,η)`（`φ = e' ∘ e.symm`，与基无关）；
* **chart 方程** `laplacian_chart_eq_christoffelBilin_F3C`：`diskMapTension G U z = 0` ⇒
  `Δ(e ∘ U) z = −(Γ_e(∂₁, ∂₁) + Γ_e(∂₂, ∂₂))`（由 `chartAt` 版经变换律 + `ContDiffAt.laplacian_comp`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Finset
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Analytic

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-! ## 1. 度量系数的线性、对称与光滑 -/

omit [FiniteDimensional ℝ E] in
theorem metricCoeff_F3C_symm (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (u w y : E) :
    metricCoeff_F3A G e u w y = metricCoeff_F3A G e w u y :=
  G.symm _ _ _

/-- 基 `b` 下的常值双线性形 `(u, w) ↦ u_i w_j`。 -/
def coordForm_F3C {ι : Type*} (b : Module.Basis ι ℝ E) (i j : ι) : E →L[ℝ] E →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
    (LinearMap.toContinuousLinearMap (b.coord j))

theorem coordForm_F3C_apply {ι : Type*} (b : Module.Basis ι ℝ E) (i j : ι) (u w : E) :
    coordForm_F3C b i j u w = b.repr u i * b.repr w j := by
  simp [coordForm_F3C]

/-- chart `e` 中的度量形 `y ↦ g_e(y) ∈ E →L E →L ℝ`（用 `Module.finBasis` 展开）。 -/
def metricForm_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, metricCoeff_F3A G e (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) y •
    coordForm_F3C (Module.finBasis ℝ E) i j

theorem metricForm_F3C_apply (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (y u w : E) :
    metricForm_F3C G e y u w = metricCoeff_F3A G e u w y := by
  rw [metricCoeff_F3A_eq_sum_basis G e (Module.finBasis ℝ E)]
  simp only [metricForm_F3C, _root_.sum_apply, smul_apply, smul_eq_mul, coordForm_F3C_apply]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- maximal-atlas transition 在 overlap 上 `C^∞`。 -/
theorem contDiffOn_transition_F3C {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have hc := IsManifold.compatible_of_mem_maximalAtlas he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hc
  have h1 := hc.1
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, id_eq, inter_univ, Function.id_comp, Function.comp_id,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.coe_trans] at h1
  exact h1

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contDiffAt_transition_F3C {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) : ContDiffAt ℝ ∞ (e' ∘ e.symm) y :=
  (contDiffOn_transition_F3C he he').contDiffAt
    ((e.isOpen_inter_preimage_symm e'.open_source).mem_nhds ⟨hy, hy'⟩)

/-- **度量系数光滑**：`e ∈ maximalAtlas ∞`、`y ∈ e.target` ⇒ `metricCoeff_F3A G e u w` 在 `y` 处
`C^∞`（transition 到 `chartAt E (e.symm y)`，树里 `chartGramOnE_contDiffOn`）。 -/
theorem contDiffAt_metricCoeff_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ e.target) (u w : E) : ContDiffAt ℝ ∞ (metricCoeff_F3A G e u w) y := by
  set a : M := e.symm y with ha
  set e₀ := chartAt E a with he₀def
  have he₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas a
  have hya : e.symm y ∈ e₀.source := mem_chart_source E a
  set b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E with hb
  set τ := e₀ ∘ e.symm with hτdef
  have hτ : ContDiffAt ℝ ∞ τ y := contDiffAt_transition_F3C he he₀ hy hya
  have hτy : τ y ∈ e₀.target := e₀.map_source hya
  have hrepr : ∀ (v : E) (i : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ∞ (fun x => b.repr (fderiv ℝ τ x v) i) y := by
    intro v i
    let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℝ E v)
    have hD : ContDiffAt ℝ ∞ (fderiv ℝ τ) y := hτ.fderiv_right (by simp)
    exact (L.contDiff.contDiffAt.comp y hD).congr_of_eventuallyEq
      (Eventually.of_forall fun x => rfl)
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (metricCoeff_F3A G e₀ (b i) (b j)) (τ y) := by
    intro i j
    have htarget : IsOpen e₀.target := e₀.open_target
    have hc := (DifferentialGeometry.Geometry.Operator.chartGramOnE_contDiffOn
      (I := 𝓘(ℝ, E)) G a i j)
    have hext : (extChartAt 𝓘(ℝ, E) a).target = e₀.target := by
      simp [he₀def]
    rw [hext] at hc
    refine (hc.contDiffAt (htarget.mem_nhds hτy)).congr_of_eventuallyEq ?_
    filter_upwards [htarget.mem_nhds hτy] with x hx
    exact (chartGramOnE_eq_metricCoeff_F3A G a hx i j).symm
  have hR : ContDiffAt ℝ ∞ (fun x => ∑ i, ∑ j,
      (b.repr (fderiv ℝ τ x u) i * b.repr (fderiv ℝ τ x w) j) *
        metricCoeff_F3A G e₀ (b i) (b j) (τ x)) y := by
    refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
    exact ((hrepr u i).mul (hrepr w j)).mul ((hgram i j).comp y hτ)
  refine hR.congr_of_eventuallyEq ?_
  filter_upwards [(e.isOpen_inter_preimage_symm e₀.open_source).mem_nhds ⟨hy, hya⟩] with x hx
  rw [metricCoeff_F3A_eq_transition G he he₀ hx.1 hx.2, metricCoeff_F3A_eq_sum_basis G e₀ b]

theorem contDiffAt_metricForm_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ e.target) : ContDiffAt ℝ ∞ (metricForm_F3C G e) y := by
  unfold metricForm_F3C
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
  exact (contDiffAt_metricCoeff_F3C G he hy _ _).smul contDiffAt_const

/-! ## 2. Christoffel 双线性映射与 Koszul 刻画 -/

/-- chart `e`、基 `b` 下的 Christoffel 双线性映射 `(ξ, η) ↦ Σ Γ^k_{ij} ξ_i η_j b_k`。 -/
def christoffelBilin_F3C {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (b : Module.Basis ι ℝ E) (y : E) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i, ∑ j, ∑ k, christoffel_F3A G e b i j k y •
    (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
      ((LinearMap.toContinuousLinearMap (b.coord j)).smulRight (b k))

theorem christoffelBilin_F3C_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (b : Module.Basis ι ℝ E) (y ξ η : E) :
    christoffelBilin_F3C G e b y ξ η =
      ∑ i, ∑ j, ∑ k, (christoffel_F3A G e b i j k y * (b.repr ξ i * b.repr η j)) • b k := by
  simp only [christoffelBilin_F3C, _root_.sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, smul_smul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  congr 1
  ring

theorem christoffelBilin_F3C_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (b : Module.Basis ι ℝ E) (y : E) (i j : ι) :
    christoffelBilin_F3C G e b y (b i) (b j) = ∑ k, christoffel_F3A G e b i j k y • b k := by
  rw [christoffelBilin_F3C_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  simp

/-- `IsAnalyticMetricOn_F3A` ⇒ `christoffelBilin_F3C` 在 `e '' (P ∩ e.source)` 上 `AnalyticOnNhd`。 -/
theorem analyticOnNhd_christoffelBilin_F3C {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒜 : Set (OpenPartialHomeomorph M E)} {P : Set M} {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) (hP : IsOpen P)
    (h𝒜 : ∀ e ∈ 𝒜, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ 𝒜) (b : Module.Basis ι ℝ E) :
    AnalyticOnNhd ℝ (christoffelBilin_F3C G e b) (e '' (P ∩ e.source)) := by
  intro y hy
  unfold christoffelBilin_F3C
  refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ =>
    Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact (hG.analyticOnNhd_christoffel hP h𝒜 he b i j k y hy).smul analyticAt_const

omit [FiniteDimensional ℝ E] in
/-- 三线性 CLM 的基上外延。 -/
theorem trilinear_ext_F3C {ι : Type*} (b : Module.Basis ι ℝ E)
    {T₁ T₂ : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (h : ∀ i j m, T₁ (b i) (b j) (b m) = T₂ (b i) (b j) (b m)) : T₁ = T₂ := by
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun i => ?_
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun j => ?_
  apply ContinuousLinearMap.coe_injective
  exact b.ext fun m => h i j m

/-- Koszul 三线性形 `K(ξ,η,ζ) = ½(Dg(ξ)(η,ζ) + Dg(η)(ξ,ζ) − Dg(ζ)(ξ,η))`（`Dg = fderiv metricForm`）。 -/
def koszulCLM_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (y : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (fderiv ℝ (metricForm_F3C G e) y + (fderiv ℝ (metricForm_F3C G e) y).flip -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.comp
      (fderiv ℝ (metricForm_F3C G e) y).flip)

theorem koszulCLM_F3C_apply (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (y ξ η ζ : E) :
    koszulCLM_F3C G e y ξ η ζ = (1 / 2 : ℝ) * (fderiv ℝ (metricForm_F3C G e) y ξ η ζ +
      fderiv ℝ (metricForm_F3C G e) y η ξ ζ - fderiv ℝ (metricForm_F3C G e) y ζ ξ η) := by
  simp [koszulCLM_F3C]

/-- `metricCoeff` 的方向导数 = `fderiv metricForm`。 -/
theorem fderiv_metricCoeff_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} {y : E}
    (hd : DifferentiableAt ℝ (metricForm_F3C G e) y) (u w ξ : E) :
    fderiv ℝ (metricCoeff_F3A G e u w) y ξ = fderiv ℝ (metricForm_F3C G e) y ξ u w := by
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)
  have hfun : metricCoeff_F3A G e u w = fun x => L (metricForm_F3C G e x) := by
    funext x
    simp [L, metricForm_F3C_apply]
  have h := L.hasFDerivAt.comp y hd.hasFDerivAt
  rw [hfun, show (fun x => L (metricForm_F3C G e x)) = ⇑L ∘ metricForm_F3C G e from rfl, h.fderiv]
  rfl

/-- **Koszul 刻画**：`g_e(Γ_e(ξ,η), ζ) = K_e(ξ,η,ζ)`（`y ∈ e.target`，任意基 `b`）。 -/
theorem metricCoeff_christoffelBilin_F3C {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (b : Module.Basis ι ℝ E) {y : E}
    (hy : y ∈ e.target) (ξ η ζ : E) :
    metricCoeff_F3A G e (christoffelBilin_F3C G e b y ξ η) ζ y = koszulCLM_F3C G e y ξ η ζ := by
  have hd : DifferentiableAt ℝ (metricForm_F3C G e) y :=
    (contDiffAt_metricForm_F3C G he hy).differentiableAt (by simp)
  set A := metricGram_F3A G e b y with hA
  have hdet : IsUnit A.det := (metricGram_F3A_det_ne_zero G he b hy).isUnit
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hT : (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) (metricForm_F3C G e y)).comp
      (christoffelBilin_F3C G e b y) = koszulCLM_F3C G e y := by
    refine trilinear_ext_F3C b fun i j m => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply]
    rw [metricForm_F3C_apply, christoffelBilin_F3C_basis, koszulCLM_F3C_apply,
      ← fderiv_metricCoeff_F3C G hd, ← fderiv_metricCoeff_F3C G hd,
      ← fderiv_metricCoeff_F3C G hd]
    -- 左边 `Σ_k Γ^k_{ij} g_{km}`
    have hlin : metricCoeff_F3A G e (∑ k, christoffel_F3A G e b i j k y • b k) (b m) y =
        ∑ k, christoffel_F3A G e b i j k y * A m k := by
      rw [← metricForm_F3C_apply]
      simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, smul_eq_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [metricForm_F3C_apply, metricCoeff_F3C_symm]
      rfl
    rw [hlin]
    simp only [christoffel_F3A]
    have hcollapse : ∑ k, (1 / 2 : ℝ) * (∑ l, A⁻¹ k l *
        (fderiv ℝ (metricCoeff_F3A G e (b l) (b j)) y (b i) +
          fderiv ℝ (metricCoeff_F3A G e (b l) (b i)) y (b j) -
          fderiv ℝ (metricCoeff_F3A G e (b i) (b j)) y (b l))) * A m k =
        (1 / 2 : ℝ) * (fderiv ℝ (metricCoeff_F3A G e (b m) (b j)) y (b i) +
          fderiv ℝ (metricCoeff_F3A G e (b m) (b i)) y (b j) -
          fderiv ℝ (metricCoeff_F3A G e (b i) (b j)) y (b m)) := by
      have hrow : ∀ l, ∑ k, A m k * A⁻¹ k l = if m = l then 1 else 0 := by
        intro l
        have := congrFun (congrFun hAinv m) l
        rw [Matrix.mul_apply] at this
        rw [this, Matrix.one_apply]
      calc ∑ k, (1 / 2 : ℝ) * (∑ l, A⁻¹ k l *
            (fderiv ℝ (metricCoeff_F3A G e (b l) (b j)) y (b i) +
              fderiv ℝ (metricCoeff_F3A G e (b l) (b i)) y (b j) -
              fderiv ℝ (metricCoeff_F3A G e (b i) (b j)) y (b l))) * A m k
          = (1 / 2 : ℝ) * ∑ l, (∑ k, A m k * A⁻¹ k l) *
            (fderiv ℝ (metricCoeff_F3A G e (b l) (b j)) y (b i) +
              fderiv ℝ (metricCoeff_F3A G e (b l) (b i)) y (b j) -
              fderiv ℝ (metricCoeff_F3A G e (b i) (b j)) y (b l)) := by
            rw [mul_sum]
            simp only [sum_mul, mul_sum]
            rw [sum_comm]
            refine sum_congr rfl fun l _ => sum_congr rfl fun k _ => ?_
            ring
        _ = _ := by
            simp only [hrow, ite_mul, one_mul, zero_mul, sum_ite_eq, Finset.mem_univ, ite_true]
    have hs1 : metricCoeff_F3A G e (b j) (b m) = metricCoeff_F3A G e (b m) (b j) := by
      funext x
      exact metricCoeff_F3C_symm G e _ _ _
    have hs2 : metricCoeff_F3A G e (b i) (b m) = metricCoeff_F3A G e (b m) (b i) := by
      funext x
      exact metricCoeff_F3C_symm G e _ _ _
    rw [hs1, hs2, ← hcollapse]
  have := congrArg (fun T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => T ξ η ζ) hT
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply] at this
  rw [← this, metricForm_F3C_apply]

/-! ## 3. Koszul 换 chart 与 Christoffel 变换律 -/

theorem metricForm_F3C_symm (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (y u w : E) :
    metricForm_F3C G e y u w = metricForm_F3C G e y w u := by
  rw [metricForm_F3C_apply, metricForm_F3C_apply, metricCoeff_F3C_symm]

/-- `metricForm` 的导数换 chart：`φ = e' ∘ e.symm`，
`Dg_e(ξ)(u,w) = g'(Dφu, D²φ(ξ,w)) + g'(D²φ(ξ,u), Dφw) + Dg'(Dφξ)(Dφu, Dφw)`。 -/
theorem fderiv_metricForm_transition_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) (ξ u w : E) :
    fderiv ℝ (metricForm_F3C G e) y ξ u w =
      metricForm_F3C G e' ((e' ∘ e.symm) y) (fderiv ℝ (e' ∘ e.symm) y u)
          (fderiv ℝ (fderiv ℝ (e' ∘ e.symm)) y ξ w) +
        metricForm_F3C G e' ((e' ∘ e.symm) y) (fderiv ℝ (fderiv ℝ (e' ∘ e.symm)) y ξ u)
          (fderiv ℝ (e' ∘ e.symm) y w) +
        fderiv ℝ (metricForm_F3C G e') ((e' ∘ e.symm) y) (fderiv ℝ (e' ∘ e.symm) y ξ)
          (fderiv ℝ (e' ∘ e.symm) y u) (fderiv ℝ (e' ∘ e.symm) y w) := by
  set φ := e' ∘ e.symm with hφdef
  have hφ : ContDiffAt ℝ ∞ φ y := contDiffAt_transition_F3C he he' hy hy'
  have hφy : φ y ∈ e'.target := e'.map_source hy'
  have hdφ : DifferentiableAt ℝ φ y := hφ.differentiableAt (by simp)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hg' : DifferentiableAt ℝ (metricForm_F3C G e') (φ y) :=
    (contDiffAt_metricForm_F3C G he' hφy).differentiableAt (by simp)
  have hB : HasFDerivAt (fun x => metricForm_F3C G e' (φ x))
      ((fderiv ℝ (metricForm_F3C G e') (φ y)).comp (fderiv ℝ φ y)) y :=
    hg'.hasFDerivAt.comp y hdφ.hasFDerivAt
  have hp : ∀ v : E, HasFDerivAt (fun x => fderiv ℝ φ x v)
      ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (fderiv ℝ φ) y)) y := fun v =>
    (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp y hD2.hasFDerivAt
  have h1 := hB.clm_apply (hp u)
  have h2 := h1.clm_apply (hp w)
  have hd : DifferentiableAt ℝ (metricForm_F3C G e) y :=
    (contDiffAt_metricForm_F3C G he hy).differentiableAt (by simp)
  rw [← fderiv_metricCoeff_F3C G hd]
  have heq : metricCoeff_F3A G e u w =ᶠ[𝓝 y]
      fun x => metricForm_F3C G e' (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x w) := by
    filter_upwards [(e.isOpen_inter_preimage_symm e'.open_source).mem_nhds ⟨hy, hy'⟩] with x hx
    rw [metricCoeff_F3A_eq_transition G he he' hx.1 hx.2, metricForm_F3C_apply]
  rw [heq.fderiv_eq, h2.fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]
  ring

/-- **Koszul 换 chart**：`K_e(ξ,η,ζ) = K_{e'}(Dφξ, Dφη, Dφζ) + g_{e'}(D²φ(ξ,η), Dφζ)`。 -/
theorem koszul_transition_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) (ξ η ζ : E) :
    koszulCLM_F3C G e y ξ η ζ =
      koszulCLM_F3C G e' ((e' ∘ e.symm) y) (fderiv ℝ (e' ∘ e.symm) y ξ)
          (fderiv ℝ (e' ∘ e.symm) y η) (fderiv ℝ (e' ∘ e.symm) y ζ) +
        metricCoeff_F3A G e' (fderiv ℝ (fderiv ℝ (e' ∘ e.symm)) y ξ η)
          (fderiv ℝ (e' ∘ e.symm) y ζ) ((e' ∘ e.symm) y) := by
  set φ := e' ∘ e.symm with hφdef
  have hφ : ContDiffAt ℝ ∞ φ y := contDiffAt_transition_F3C he he' hy hy'
  have hsym : ∀ a c : E, fderiv ℝ (fderiv ℝ φ) y a c = fderiv ℝ (fderiv ℝ φ) y c a :=
    fun a c => (hφ.isSymmSndFDerivAt (by simp)) a c
  rw [koszulCLM_F3C_apply, koszulCLM_F3C_apply,
    fderiv_metricForm_transition_F3C G he he' hy hy' ξ η ζ,
    fderiv_metricForm_transition_F3C G he he' hy hy' η ξ ζ,
    fderiv_metricForm_transition_F3C G he he' hy hy' ζ ξ η, ← metricForm_F3C_apply]
  set g' := metricForm_F3C G e' (φ y) with hg'
  set D := fderiv ℝ φ y with hD
  set D2 := fderiv ℝ (fderiv ℝ φ) y with hD2
  have s1 : g' (D η) (D2 ξ ζ) = g' (D2 ζ ξ) (D η) := by
    rw [hg', metricForm_F3C_symm, hsym]
  have s2 : g' (D ξ) (D2 η ζ) = g' (D ξ) (D2 ζ η) := by rw [hsym]
  have s3 : g' (D2 η ξ) (D ζ) = g' (D2 ξ η) (D ζ) := by rw [hsym]
  rw [s1, s2, s3]
  ring

omit [FiniteDimensional ℝ E] in
/-- `y ∈ e.target`、`v ≠ 0` ⇒ `g_e(v, v)(y) > 0`。 -/
theorem metricCoeff_pos_F3C (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ e.target) {v : E} (hv : v ≠ 0) : 0 < metricCoeff_F3A G e v v y :=
  G.pos _ _ fun h0 => hv (mfderiv_symm_injective_F3A he hy (h0.trans (map_zero _).symm))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- transition 的导数满射（逆 transition 的链式法则）。 -/
theorem fderiv_transition_surjective_F3C {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) : Function.Surjective (fderiv ℝ (e' ∘ e.symm) y) := by
  set φ := e' ∘ e.symm with hφdef
  set ψ := e ∘ e'.symm with hψdef
  have hφy : φ y ∈ e'.target := e'.map_source hy'
  have hψφ : ψ (φ y) = y := by
    simp only [hψdef, hφdef, Function.comp_apply, e'.left_inv hy', e.right_inv hy]
  have hsy : e'.symm (φ y) ∈ e.source := by
    simp only [hφdef, Function.comp_apply, e'.left_inv hy']
    exact e.map_target hy
  have hψ : DifferentiableAt ℝ ψ (φ y) :=
    (contDiffAt_transition_F3C he' he hφy hsy).differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ φ (ψ (φ y)) := by
    rw [hψφ]
    exact (contDiffAt_transition_F3C he he' hy hy').differentiableAt (by simp)
  have hid : φ ∘ ψ =ᶠ[𝓝 (φ y)] id := by
    filter_upwards [(e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨hφy, hsy⟩]
      with x hx
    simp only [hφdef, hψdef, Function.comp_apply, e.left_inv hx.2, e'.right_inv hx.1, id]
  have hcomp := fderiv_comp (φ y) hφ hψ
  rw [hid.fderiv_eq, fderiv_id, hψφ] at hcomp
  intro v
  refine ⟨fderiv ℝ ψ (φ y) v, ?_⟩
  have := congrArg (fun L : E →L[ℝ] E => L v) hcomp
  simpa using this.symm

/-- **Christoffel 变换律**（任意两 maximal-atlas chart、任意基）：`φ = e' ∘ e.symm`，
`Dφ(Γ_e(ξ,η)) = Γ_{e'}(Dφξ, Dφη) + D²φ(ξ,η)`。 -/
theorem christoffelBilin_transition_F3C {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (b : Module.Basis ι ℝ E)
    (b' : Module.Basis ι' ℝ E) {y : E} (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source)
    (ξ η : E) :
    fderiv ℝ (e' ∘ e.symm) y (christoffelBilin_F3C G e b y ξ η) =
      christoffelBilin_F3C G e' b' ((e' ∘ e.symm) y) (fderiv ℝ (e' ∘ e.symm) y ξ)
          (fderiv ℝ (e' ∘ e.symm) y η) +
        fderiv ℝ (fderiv ℝ (e' ∘ e.symm)) y ξ η := by
  set φ := e' ∘ e.symm with hφdef
  have hφy : φ y ∈ e'.target := e'.map_source hy'
  set V := fderiv ℝ φ y (christoffelBilin_F3C G e b y ξ η) -
    (christoffelBilin_F3C G e' b' (φ y) (fderiv ℝ φ y ξ) (fderiv ℝ φ y η) +
      fderiv ℝ (fderiv ℝ φ) y ξ η) with hV
  have horth : ∀ ζ : E, metricForm_F3C G e' (φ y) V (fderiv ℝ φ y ζ) = 0 := by
    intro ζ
    have hK := metricCoeff_christoffelBilin_F3C G he b hy ξ η ζ
    rw [metricCoeff_F3A_eq_transition G he he' hy hy', koszul_transition_F3C G he he' hy hy',
      ← metricCoeff_christoffelBilin_F3C G he' b' hφy] at hK
    rw [hV, map_sub, map_add, sub_apply, add_apply,
      metricForm_F3C_apply, metricForm_F3C_apply, metricForm_F3C_apply]
    rw [hφdef] at hK ⊢
    linarith
  obtain ⟨ζ, hζ⟩ := fderiv_transition_surjective_F3C he he' hy hy' V
  have h0 : metricCoeff_F3A G e' V V (φ y) = 0 := by
    rw [← metricForm_F3C_apply]
    have := horth ζ
    rwa [hζ] at this
  by_contra hne
  have hVne : V ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  exact (metricCoeff_pos_F3C G he' hφy hVne).ne' h0

/-! ## 4. 任意 maximal-atlas chart 中的 harmonic map 方程（选项 (α)） -/

open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator InnerProductSpace in
private theorem bilin_trace_std_F3C {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] V) :
    (∑ i : Fin (Module.finrank ℝ ℂ), B (stdOrthonormalBasis ℝ ℂ i)
      (stdOrthonormalBasis ℝ ℂ i)) = B 1 1 + B Complex.I Complex.I := by
  calc
    _ = TensorProduct.lift B (canonicalCovariantTensor ℂ) := by
      rw [canonicalCovariantTensor_eq_sum ℂ (stdOrthonormalBasis ℝ ℂ)]
      simp
    _ = _ := by
      rw [canonicalCovariantTensor_eq_sum ℂ Complex.orthonormalBasisOneI]
      simp

open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator in
/-- 树里的 `chartChristoffelContraction`（chartAt 版）= `christoffelBilin_F3C`（`chartModelBasis`）。 -/
theorem chartChristoffelContraction_eq_christoffelBilin_F3C
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M) {y : E} (hy : y ∈ (chartAt E a).target)
    (v w : E) :
    chartChristoffelContraction (I := 𝓘(ℝ, E)) G a v w y =
      christoffelBilin_F3C G (chartAt E a) (chartModelBasis E) y v w := by
  rw [chartChristoffelContraction_def, christoffelBilin_F3C_apply]
  simp only [sum_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [chartChristoffel_eq_christoffel_F3A G a hy]
  simp only [chartCoord_def]
  congr 1
  ring

theorem two_le_infty_F3C : (2 : ℕ∞ω) ≤ ∞ := ENat.LEInfty.out

open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Tensor.Coordinates
  DifferentialGeometry.Geometry.Operator InnerProductSpace in
/-- **(c3) chart 方程（选项 α）**：`e ∈ maximalAtlas ∞`（任意，不必是 `chartAt`）、
`U` 在 `z` 处 `C^∞`、`U z ∈ e.source`、`diskMapTension G U z = 0` ⇒
`Δ(e ∘ U) z = −(Γ_e(∂₁, ∂₁) + Γ_e(∂₂, ∂₂))`，`Γ_e = christoffelBilin_F3C G e b (e (U z))`，
基 `b` 任意。 -/
theorem laplacian_chart_eq_christoffelBilin_F3C {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (b : Module.Basis ι ℝ E) {U : ℂ → M}
    {z : ℂ} (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z) (hsrc : U z ∈ e.source)
    (hτ : diskMapTension G U z = 0) :
    Laplacian.laplacian (e ∘ U) z =
      -(christoffelBilin_F3C G e b (e (U z)) (fderiv ℝ (e ∘ U) z 1) (fderiv ℝ (e ∘ U) z 1) +
        christoffelBilin_F3C G e b (e (U z)) (fderiv ℝ (e ∘ U) z Complex.I)
          (fderiv ℝ (e ∘ U) z Complex.I)) := by
  have he₀ : chartAt E (U z) ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (U z)
  have hsrc₀ : U z ∈ (chartAt E (U z)).source := mem_chart_source E (U z)
  have hU2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 U z := hU.of_le two_le_infty_F3C
  -- 树里 chartAt 版
  have hch := chart_planarTension G hU2 hsrc₀
  have hτ' : planarTension G U z = 0 := hτ
  rw [hτ', map_zero] at hch
  dsimp only at hch
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀ : ℂ → E, X₀ = extChartAt 𝓘(ℝ, E) (U z) ∘ U := ⟨_, rfl⟩
  rw [← hX₀def] at hch
  have hX₀e : X₀ = chartAt E (U z) ∘ U := by
    funext w
    simp [hX₀def]
  have hX₀ : ContDiffAt ℝ 2 X₀ z := by
    rw [hX₀def]
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 2) hsrc₀).comp z hU2).contDiffAt
  have hy₀ : X₀ z ∈ (chartAt E (U z)).target := by
    rw [hX₀e]
    exact (chartAt E (U z)).map_source hsrc₀
  have hy₀' : (chartAt E (U z)).symm (X₀ z) ∈ e.source := by
    rw [hX₀e, Function.comp_apply, (chartAt E (U z)).left_inv hsrc₀]
    exact hsrc
  have hΔ₀ : Laplacian.laplacian X₀ z = -(christoffelBilin_F3C G (chartAt E (U z))
      (chartModelBasis E) (X₀ z) (fderiv ℝ X₀ z 1) (fderiv ℝ X₀ z 1) +
      christoffelBilin_F3C G (chartAt E (U z)) (chartModelBasis E) (X₀ z)
        (fderiv ℝ X₀ z Complex.I) (fderiv ℝ X₀ z Complex.I)) := by
    have h1 := chartChristoffelContraction_eq_christoffelBilin_F3C G (U z) hy₀
    rw [h1, h1] at hch
    rw [eq_neg_iff_add_eq_zero, ← add_assoc]
    exact hch.symm
  -- transition `φ = e ∘ (chartAt E (U z)).symm`
  obtain ⟨φ, hφdef⟩ : ∃ φ : E → E, φ = e ∘ (chartAt E (U z)).symm := ⟨_, rfl⟩
  have hφ : ContDiffAt ℝ ∞ φ (X₀ z) := by
    rw [hφdef]
    exact contDiffAt_transition_F3C he₀ he hy₀ hy₀'
  have hφ2 : ContDiffAt ℝ 2 φ (X₀ z) := hφ.of_le two_le_infty_F3C
  have hloc : e ∘ U =ᶠ[𝓝 z] φ ∘ X₀ := by
    have hcont : ContinuousAt U z := hU.continuousAt
    filter_upwards [hcont.preimage_mem_nhds ((chartAt E (U z)).open_source.mem_nhds hsrc₀)]
      with w hw
    simp only [hφdef, hX₀e, Function.comp_apply, (chartAt E (U z)).left_inv hw]
  have hφy₀ : φ (X₀ z) = e (U z) := by
    rw [hφdef, hX₀e]
    simp only [Function.comp_apply, (chartAt E (U z)).left_inv hsrc₀]
  have hDX : ∀ v : ℂ, fderiv ℝ (e ∘ U) z v = fderiv ℝ φ (X₀ z) (fderiv ℝ X₀ z v) := by
    intro v
    rw [hloc.fderiv_eq, fderiv_comp z (hφ2.differentiableAt (by norm_num))
      (hX₀.differentiableAt (by norm_num))]
    rfl
  -- Laplacian 链式法则（`stdOrthonormalBasis` 迹换成 `1, I`）
  have hchain := hX₀.laplacian_comp hφ2
  let B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] E := LinearMap.mk₂ ℝ
    (fun v w => fderiv ℝ (fderiv ℝ φ) (X₀ z) (fderiv ℝ X₀ z v) (fderiv ℝ X₀ z w))
    (by intros; simp only [map_add, add_apply])
    (by intros; simp only [map_smul, smul_apply])
    (by intros; simp only [map_add]) (by intros; simp only [map_smul])
  have hsum := bilin_trace_std_F3C B
  simp only [B, LinearMap.mk₂_apply] at hsum
  rw [hsum] at hchain
  rw [(laplacian_congr_nhds hloc).eq_of_nhds, hchain, hΔ₀, hDX, hDX, ← hφy₀]
  have hT1 := christoffelBilin_transition_F3C G he₀ he (chartModelBasis E) b hy₀ hy₀'
    (fderiv ℝ X₀ z 1) (fderiv ℝ X₀ z 1)
  have hTI := christoffelBilin_transition_F3C G he₀ he (chartModelBasis E) b hy₀ hy₀'
    (fderiv ℝ X₀ z Complex.I) (fderiv ℝ X₀ z Complex.I)
  rw [← hφdef] at hT1 hTI
  rw [map_neg, map_add, hT1, hTI]
  abel

/-! ## consumer（G1）：`IsMorreyDisk` 的内部（只用 `smoothInterior` + `harmonic`） -/

open DifferentialGeometry.Topology in
/-- Morrey 盘在任意 maximal-atlas chart 中满足 chart 方程（R8-AR 的 (c3) 输入；conformal / 极小性不用）。 -/
theorem laplacian_chart_eq_of_isMorreyDisk_F3C {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk G γ u) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (b : Module.Basis ι ℝ E) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hsrc : diskExtension u z ∈ e.source) :
    Laplacian.laplacian (e ∘ diskExtension u) z =
      -(christoffelBilin_F3C G e b (e (diskExtension u z))
          (fderiv ℝ (e ∘ diskExtension u) z 1) (fderiv ℝ (e ∘ diskExtension u) z 1) +
        christoffelBilin_F3C G e b (e (diskExtension u z))
          (fderiv ℝ (e ∘ diskExtension u) z Complex.I)
          (fderiv ℝ (e ∘ diskExtension u) z Complex.I)) :=
  laplacian_chart_eq_christoffelBilin_F3C G he b
    (hu.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)) hsrc (hu.harmonic z hz)

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap
