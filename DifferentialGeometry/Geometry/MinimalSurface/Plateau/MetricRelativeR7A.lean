import DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricAreaR7A
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# S-MY-R7A G1 bis：chart `C⁰` 度量收敛（`MetricTendstoCInftyOn_MYD3` 的 `k = 0`）⇒ 相对一致收敛 `hrel`

O-MY-R7C 的接口请求（1）：R6b 给出的 `Gₙ → G` 是 chart 形（`e ∈ maximalAtlas`、紧 `C' ⊆ e.target ∩
e.symm⁻¹' B`、逐 `ξ η` 的系数 `iteratedFDeriv` 一致收敛）；G1 / G4 / G5 / G2 用的是 chart-free 的
`hrel : ∀ ε > 0, ∀ᶠ n, ∀ x ∈ B, ∀ v, |Gₙ(v,v) − G(v,v)| ≤ ε G(v,v)`。本文件证 chart 形 ⇒ `hrel`。

证明：每点 `x ∈ B` 取 `chartAt E x`、紧集 `C'ₓ = closedBall ∩ e.symm⁻¹' B`、开邻域 `Vₓ`；`B` 紧给有限子覆盖；
单个 chart 上：`G` 的二次型 `y, ξ ↦ G(D_y ξ, D_y ξ)` 联合连续（`continuousOn_chart_quadratic_R7A`）且
`D_y` 单射 ⇒ 紧集 `C'ₓ × S` 上有正下界 `λ ‖ξ‖²`（`exists_pos_quadratic_lower_R7A`）；`E` 有限维：
沿基底展开 `Φ(ξ,ξ) = Σ aᵢ aⱼ Φ(bᵢ,bⱼ)`（`bilinear_expand_R7A`）⇒ 只要基底对 `(bᵢ,bⱼ)` 的系数一致小，
二次型一致小（`bilinear_bound_R7A`）；`D_y` 满射（`bijective_mfderiv_chart_symm_R7A`）把任意切向量写成 `D_y ξ`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 有限维空间上的双线性型沿基底展开：`Φ ξ ξ = Σᵢ Σⱼ aᵢ aⱼ Φ(bᵢ, bⱼ)`。 -/
theorem bilinear_expand_R7A (Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ξ : E) :
    Φ ξ ξ = ∑ i, ∑ j, (Module.finBasis ℝ E).repr ξ i * (Module.finBasis ℝ E).repr ξ j *
      Φ (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  set b := Module.finBasis ℝ E with hb
  conv_lhs => rw [← b.sum_repr ξ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 双线性型在基底对上有界 `δ` ⇒ 二次型有界 `δ K² ‖ξ‖²`。 -/
theorem bilinear_bound_R7A : ∃ K : ℝ, 0 ≤ K ∧ ∀ (Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (δ : ℝ), 0 ≤ δ →
    (∀ i j, |Φ (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)| ≤ δ) →
    ∀ ξ : E, |Φ ξ ξ| ≤ δ * K ^ 2 * ‖ξ‖ ^ 2 := by
  set b := Module.finBasis ℝ E with hb
  let A : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖A i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Φ δ hδ hΦ ξ => ?_⟩
  have hcoord : ∀ i, |b.repr ξ i| ≤ ‖A i‖ * ‖ξ‖ := fun i => by
    have := (A i).le_opNorm ξ
    simpa [A] using this
  have hsum : ∑ i, |b.repr ξ i| ≤ (∑ i, ‖A i‖) * ‖ξ‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hcoord i
  rw [bilinear_expand_R7A]
  calc |∑ i, ∑ j, b.repr ξ i * b.repr ξ j * Φ (b i) (b j)|
      ≤ ∑ i, |∑ j, b.repr ξ i * b.repr ξ j * Φ (b i) (b j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |b.repr ξ i * b.repr ξ j * Φ (b i) (b j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |b.repr ξ i| * |b.repr ξ j| * δ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hΦ i j) (by positivity)
    _ = (∑ i, |b.repr ξ i|) ^ 2 * δ := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ((∑ i, ‖A i‖) * ‖ξ‖) ^ 2 * δ := by
        have h0 : 0 ≤ ∑ i, |b.repr ξ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hsum 2) hδ
    _ = δ * (∑ i, ‖A i‖) ^ 2 * ‖ξ‖ ^ 2 := by ring


omit [FiniteDimensional ℝ E] in
/-- 任意 maximal-atlas chart 的 `symm` 的切映射在 `(y, ξ)` 上联合连续。 -/
theorem continuousOn_chart_symm_derivative_R7A {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContinuousOn (fun q : E × E =>
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q.1 q.2 :
        TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _)))
      (Prod.fst ⁻¹' e.target) := by
  have hs := e.open_target
  have ht := (contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    he).continuousOn_tangentMapWithin (by simp) hs.uniqueMDiffOn
  have hv : Continuous (fun q : E × E =>
      (TotalSpace.mk' E q.1 q.2 : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd)
  have hcomp := ht.comp hv.continuousOn (fun q hq => hq)
  apply hcomp.congr
  intro q hq
  dsimp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hq)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
/-- chart 内度量二次型 `(y, ξ) ↦ g(D_y ξ, D_y ξ)` 联合连续。 -/
theorem continuousOn_chart_quadratic_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContinuousOn (fun q : E × E => g.inner (e.symm q.1)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q.1 q.2) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm q.1 q.2))
      (Prod.fst ⁻¹' e.target) := by
  let cg := g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  have hv := continuousOn_chart_symm_derivative_R7A he
  exact hv.inner_bundle hv

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- chart 的 `symm` 在 `e.target` 内的切映射双射。 -/
theorem bijective_mfderiv_chart_symm_R7A {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target) :
    Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y) := by
  have hy' : y ∈ (e.extend 𝓘(ℝ, E)).target := by
    simpa using hy
  have h := isInvertible_mfderivWithin_extend_symm (IsManifold.maximalAtlas_subset_of_le
    (m := 1) (n := ∞) (by simp) he) hy'
  have hsymm : ⇑(e.extend 𝓘(ℝ, E)).symm = ⇑e.symm := by
    ext z
    simp
  rw [hsymm] at h
  have hr : range (𝓘(ℝ, E) : E → E) = univ := by simp
  rw [hr, mfderivWithin_univ] at h
  obtain ⟨L, hL⟩ := h
  rw [← hL]
  exact L.bijective

/-- chart 内度量二次型在紧集 `C' ⊆ e.target` 上有统一正下界 `λ ‖ξ‖²`（紧性 + 正定 + 齐次）。 -/
theorem exists_pos_quadratic_lower_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {C' : Set E} (hC' : IsCompact C') (hCt : C' ⊆ e.target) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ C', ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ g.inner (e.symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) := by
  set q : E × E → ℝ := fun p => g.inner (e.symm p.1)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm p.1 p.2) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm p.1 p.2) with hq
  have hqc : ContinuousOn q (Prod.fst ⁻¹' e.target) := continuousOn_chart_quadratic_R7A g he
  have hqpos : ∀ y ∈ C', ∀ ξ : E, ξ ≠ 0 → 0 < q (y, ξ) := by
    intro y hy ξ hξ
    have hinj := (bijective_mfderiv_chart_symm_R7A he (hCt hy)).1
    have hne : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ ≠ 0 := fun h0 =>
      hξ (hinj (h0.trans (map_zero _).symm))
    exact g.pos _ _ hne
  -- 齐次性
  have hhom : ∀ y ξ (c : ℝ), q (y, c • ξ) = c ^ 2 * q (y, ξ) := by
    intro y ξ c
    have hD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (c • ξ) =
        c • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ :=
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).map_smul c ξ
    change g.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (c • ξ))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (c • ξ)) = c ^ 2 * g.inner (e.symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
    rw [hD]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hq0 : ∀ y ξ, 0 ≤ q (y, ξ) := fun y ξ => metric_inner_self_nonneg g _ _
  have hscale : ∀ y (ξ : E), ξ ≠ 0 → q (y, ξ) = ‖ξ‖ ^ 2 * q (y, ‖ξ‖⁻¹ • ξ) := by
    intro y ξ hξ
    have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have h := hhom y (‖ξ‖⁻¹ • ξ) ‖ξ‖
    rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul] at h
    exact h
  have hsph : ∀ (ξ : E), ξ ≠ 0 → ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : E) 1 := by
    intro ξ hξ
    have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    simp [norm_smul, hnorm.ne']
  by_cases hK : (C' ×ˢ Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := (hC'.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn hK
      (hqc.mono (fun p hp => hCt hp.1))
    have hp₀pos : 0 < q p₀ := hqpos p₀.1 hp₀.1 p₀.2 (by
      intro h0
      have := hp₀.2
      simp [h0] at this)
    refine ⟨q p₀, hp₀pos, fun y hy ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ
      simpa using hq0 y 0
    · have h1 := isMinOn_iff.mp hmin (y, ‖ξ‖⁻¹ • ξ) ⟨hy, hsph ξ hξ⟩
      change q p₀ * ‖ξ‖ ^ 2 ≤ q (y, ξ)
      rw [hscale y ξ hξ, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · refine ⟨1, one_pos, fun y hy ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ
      simpa using hq0 y 0
    · exact absurd ⟨(y, ‖ξ‖⁻¹ • ξ), hy, hsph ξ hξ⟩ hK

/-- 两个度量在 chart 内差的双线性型 `(ξ, η) ↦ H(D ξ, D η) − H'(D ξ, D η)`。 -/
def chartMetricDiff_R7A (H H' : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (y : E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ η : E => H.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η) -
    H'.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η))
    (fun m₁ m₂ η => by
      have hD := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).map_add m₁ m₂
      erw [hD]
      simp only [map_add, add_apply]
      ring)
    (fun c m η => by
      have hD := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).map_smul c m
      erw [hD]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring)
    (fun m η₁ η₂ => by
      have hD := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).map_add η₁ η₂
      erw [hD]
      simp only [map_add]
      ring)
    (fun c m η => by
      have hD := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).map_smul c η
      erw [hD]
      simp only [map_smul, smul_eq_mul]
      ring)

omit [FiniteDimensional ℝ E] in
theorem chartMetricDiff_apply_R7A (H H' : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (y ξ η : E) :
    chartMetricDiff_R7A H H' e y ξ η =
      H.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η) -
      H'.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η) := rfl

/-- **chart 内相对估计**：`Gₙ → G` 在 chart 内的二次型系数（固定 `ξ, η`）于紧集 `C'` 上一致收敛 ⇒
相对一致收敛 `|Gₙ(Dξ, Dξ) − G(Dξ, Dξ)| ≤ ε G(Dξ, Dξ)`（对所有 `ξ`、`y ∈ C'`，`n` 充分大）。 -/
theorem chart_relative_estimate_R7A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {C' : Set E} (hC' : IsCompact C') (hCt : C' ⊆ e.target)
    (hconv : ∀ ξ η : E, TendstoUniformlyOn
      (fun n y => (Gn n).inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η))
      (fun y => G.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)) atTop C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ C', ∀ ξ : E,
      |(Gn n).inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) -
        G.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)| ≤
      ε * G.inner (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) := by
  obtain ⟨lam, hlam, hlow⟩ := exists_pos_quadratic_lower_R7A G he hC' hCt
  obtain ⟨K, hK0, hKb⟩ := bilinear_bound_R7A (E := E)
  set δ : ℝ := ε * lam / (K ^ 2 + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set b := Module.finBasis ℝ E with hb
  have hentry : ∀ᶠ n in atTop, ∀ y ∈ C', ∀ i j,
      |chartMetricDiff_R7A (Gn n) G e y (b i) (b j)| ≤ δ := by
    have h : ∀ i j, ∀ᶠ n in atTop, ∀ y ∈ C',
        |chartMetricDiff_R7A (Gn n) G e y (b i) (b j)| ≤ δ := by
      intro i j
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv (b i) (b j)) δ hδ] with n hn y hy
      have := hn y hy
      rw [Real.dist_eq] at this
      rw [chartMetricDiff_apply_R7A, abs_sub_comm]
      exact this.le
    have h2 : ∀ᶠ n in atTop, ∀ i j, ∀ y ∈ C',
        |chartMetricDiff_R7A (Gn n) G e y (b i) (b j)| ≤ δ :=
      eventually_all.mpr fun i => eventually_all.mpr fun j => h i j
    filter_upwards [h2] with n hn y hy i j using hn i j y hy
  filter_upwards [hentry] with n hn y hy ξ
  have hb1 := hKb (chartMetricDiff_R7A (Gn n) G e y) δ hδ.le (hn y hy) ξ
  rw [chartMetricDiff_apply_R7A] at hb1
  refine hb1.trans ?_
  have h3 : δ * K ^ 2 ≤ ε * lam := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε hlam, sq_nonneg K]
  calc δ * K ^ 2 * ‖ξ‖ ^ 2 ≤ ε * lam * ‖ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = ε * (lam * ‖ξ‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hlow y hy ξ) hε.le

omit [FiniteDimensional ℝ E] in
/-- `iteratedFDeriv ℝ 0` 的一致收敛 ⇒ 值的一致收敛（定义域 `E`，值域 `ℝ`）。 -/
theorem tendstoUniformlyOn_of_iteratedFDeriv_zero_gen_R7A {g : ℕ → E → ℝ} {g₀ : E → ℝ}
    {S : Set E}
    (h : TendstoUniformlyOn (fun n => iteratedFDeriv ℝ 0 (g n)) (iteratedFDeriv ℝ 0 g₀)
      atTop S) :
    TendstoUniformlyOn (fun n x => g n x) (fun x => g₀ x) atTop S := by
  have h1 := (continuousMultilinearCurryFin0 ℝ E ℝ).isometry.uniformContinuous
    |>.comp_tendstoUniformlyOn h
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using h1

/-- **G1 bis**（hGn ⇒ hrel）：`Gₙ → G` 于紧集 `B`（chart 内二次型系数逐 `ξ, η` 一致收敛，
`MetricTendstoCInftyOn_MYD3` 的 `k = 0` 部分）⇒ chart-free 的相对一致收敛。 -/
theorem relative_metric_tendsto_of_chart_tendsto_R7A [T2Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M} (hB : IsCompact B)
    (hGn : ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M, ∀ C' : Set E, IsCompact C' →
      C' ⊆ e.target ∩ e.symm ⁻¹' B → ∀ (k : ℕ) (ξ η : E), TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun y => (Gn n).inner (e.symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)))
        (iteratedFDeriv ℝ k (fun y => G.inner (e.symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)))
        atTop C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v := by
  -- 每点 `x ∈ B` 的 chart `chartAt E x`、紧集 `C'ₓ` 与开邻域 `Vₓ`
  have hex : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt E x x) r ⊆ (chartAt E x).target := by
    intro x
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (chartAt E x).open_target _
      (mem_chart_target E x)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩
  choose r hr hrsub using hex
  let V : M → Set M := fun x => (chartAt E x).source ∩ (chartAt E x) ⁻¹'
    Metric.ball (chartAt E x x) (r x)
  have hV : ∀ x, V x ∈ 𝓝 x := fun x => by
    apply IsOpen.mem_nhds
    · exact (chartAt E x).continuousOn.isOpen_inter_preimage (chartAt E x).open_source
        Metric.isOpen_ball
    · exact ⟨mem_chart_source E x, Metric.mem_ball_self (hr x)⟩
  let C : M → Set E := fun x => Metric.closedBall (chartAt E x x) (r x) ∩ (chartAt E x).symm ⁻¹' B
  have hCc : ∀ x, IsCompact (C x) := fun x => by
    have hcl : IsClosed (C x) :=
      ((chartAt E x).symm.continuousOn.mono (hrsub x)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall hB.isClosed
    exact (isCompact_closedBall _ _).of_isClosed_subset hcl inter_subset_left
  obtain ⟨t, htB, hcover⟩ := hB.elim_nhds_subcover V (fun x _ => hV x)
  -- 每个 chart 上的相对估计
  have hchart : ∀ x ∈ t, ∀ᶠ n in atTop, ∀ y ∈ C x,
      ∀ v : TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y),
      |(Gn n).inner ((chartAt E x).symm y) v v - G.inner ((chartAt E x).symm y) v v| ≤
        ε * G.inner ((chartAt E x).symm y) v v := by
    intro x _
    have hconv : ∀ ξ η : E, TendstoUniformlyOn
        (fun n y => (Gn n).inner ((chartAt E x).symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y ξ)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y η))
        (fun y => G.inner ((chartAt E x).symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y ξ)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm y η)) atTop (C x) := fun ξ η =>
      tendstoUniformlyOn_of_iteratedFDeriv_zero_gen_R7A
        (hGn _ (IsManifold.chart_mem_maximalAtlas x) (C x) (hCc x)
          (fun y hy => ⟨hrsub x hy.1, hy.2⟩) 0 ξ η)
    filter_upwards [chart_relative_estimate_R7A G Gn (IsManifold.chart_mem_maximalAtlas x)
      (hCc x) (fun y hy => hrsub x hy.1) hconv hε] with n hn y hy v
    obtain ⟨ξ, rfl⟩ := (bijective_mfderiv_chart_symm_R7A (IsManifold.chart_mem_maximalAtlas x)
      (hrsub x hy.1)).2 v
    exact hn y hy ξ
  filter_upwards [(eventually_all_finset t).mpr hchart] with n hn x' hx' v
  obtain ⟨x, hxt, hxV⟩ := Set.mem_iUnion₂.mp (hcover hx')
  have hy : (chartAt E x) x' ∈ C x := ⟨Metric.ball_subset_closedBall hxV.2, by
    simpa only [mem_preimage, (chartAt E x).left_inv hxV.1] using hx'⟩
  have h := hn x hxt _ hy
  rw [(chartAt E x).left_inv hxV.1] at h
  exact h v

/-- **G1 bis consumer**：chart 形度量收敛 ⇒ `A_{Gₙ}(q) → A_G(q)`（G1b 的 chart 形前提版）。 -/
theorem area_tendsto_of_chart_metric_tendsto_R7A [T2Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M} (hB : IsCompact B)
    (hGn : ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M, ∀ C' : Set E, IsCompact C' →
      C' ⊆ e.target ∩ e.symm ⁻¹' B → ∀ (k : ℕ) (ξ η : E), TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun y => (Gn n).inner (e.symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)))
        (iteratedFDeriv ℝ k (fun y => G.inner (e.symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y ξ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y η)))
        atTop C')
    {q : C(closedDisk, M)} (hqB : range q ⊆ B)
    (hqint : IntegrableOn (riemannianAreaDensity G (diskExtension q)) (Metric.closedBall 0 1)) :
    Tendsto (fun n => riemannianDiskArea (Gn n) q) atTop (𝓝 (riemannianDiskArea G q)) :=
  area_tendsto_of_metric_tendsto_R7A (fun _ hε => relative_metric_tendsto_of_chart_tendsto_R7A hB
    hGn hε) hqB hqint

end DifferentialGeometry.Geometry
