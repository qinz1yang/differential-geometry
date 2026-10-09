import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckDiskDistPropsNK
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

/-!
# IMS05′ 的 `d_q` 对齐（O-W-IMS06 G1 第 1 部分，后缀 `_IM6`）

S-W-NECK 的 IMS06′（`not_mem_middle_sphere_of_stability_bound_NK`）以多边形内蕴距离
`d_q = diskEDist_NK g q z₀`（线段链的 `q^*g`-长度下确界）陈述 IMS05′ 结论；O-W-GEO-MIN 的极小路径
论证用的是共形因子 `lam = g(∂₁Q, ∂₁Q)` 的线段 Lipschitz 界
`d y ≤ d x + ∫₀¹ √(lam (x + t(y−x))) ‖y − x‖`。本文件把两者对齐（REMAINING-OBLIGATIONS c3 的
"`d_q` 对齐"）：

* `inner_mfderiv_of_conformal_IM6`：`DiskMapConformalAt g U z` ⇒ `|dU v|²_g = ‖v‖² · lam`；
* `riemannianCurveSpeed_seg_conformal_IM6` / `diskSegLength_eq_conformal_IM6`：开盘内线段的
  `q^*g`-长度 = `∫⁻ t ∈ [0,1], √(lam (x + t(y−x))) ‖y − x‖`；
* `diskEDist_le_add_conformal_IM6`：`d_q(z₀, y) ≤ d_q(z₀, x) + ∫⁻ …`（GEO-MIN 的 `hseg`，`ℝ≥0∞` 形）；
* `ims05_radius_bound_of_conformal_IM6`（c3 的通用形）：共形 IMS05′（`lam` 形，显式前提 `hlam`，
  由 S-W-STAB/S-W-EIG/O-W-GEO-MIN/S-W-GEO/O-IFACE G3 合成，尚未到）⇒ NECK G4 `hIMS05` 的 `σ`-版。

不引入新结构 / 新 Prop；`diskConformalFactor_IM6` 只是实值函数的缩写。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 盘映射 `diskExtension q` 在 `z` 处的共形因子 `lam z = g(∂₁, ∂₁)`。 -/
def diskConformalFactor_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M))
    (z : ℂ) : ℝ :=
  g.inner (diskExtension q z) (diskMapPartial (diskExtension q) z 1)
    (diskMapPartial (diskExtension q) z 1)

/-- 共形点处 `|dU v|²_g = ‖v‖² · g(∂₁U, ∂₁U)`（`v = re·1 + im·I`，双线性 + 对称 + 共形两条）。 -/
theorem inner_mfderiv_of_conformal_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    {z : ℂ} (h : DiskMapConformalAt g U z) (v : ℂ) :
    g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) =
      ‖v‖ ^ 2 * g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) := by
  obtain ⟨h01, h11⟩ := h
  let A : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z) := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  change g.inner (U z) (A 1) (A Complex.I) = 0 at h01
  change g.inner (U z) (A 1) (A 1) = g.inner (U z) (A Complex.I) (A Complex.I) at h11
  change g.inner (U z) (A v) (A v) = ‖v‖ ^ 2 * g.inner (U z) (A 1) (A 1)
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hAv : A v = v.re • A 1 + v.im • A Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  have hsym : g.inner (U z) (A Complex.I) (A 1) = 0 := by
    rw [g.symm]
    exact h01
  rw [hAv]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [h01, hsym, ← h11]
  have hn : ‖v‖ ^ 2 = v.re * v.re + v.im * v.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hn]
  ring

theorem diskConformalFactor_nonneg_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) (z : ℂ) : 0 ≤ diskConformalFactor_IM6 g q z := by
  unfold diskConformalFactor_IM6
  by_cases h : diskMapPartial (E := E) (diskExtension q) z 1 = 0
  · rw [h]
    simp
  · exact (g.pos _ _ h).le

/-- 开盘内线段 `t ↦ x + t(y − x)` 经共形盘的 `g`-速率 `= √(lam) · ‖y − x‖`。 -/
theorem riemannianCurveSpeed_seg_conformal_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    {x y : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) 1) (hy : y ∈ Metric.ball (0 : ℂ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    riemannianCurveSpeed g (diskExtension q ∘ fun t : ℝ => x + t • (y - x)) t =
      Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖ := by
  have hmem : x + t • (y - x) ∈ Metric.ball (0 : ℂ) 1 := by
    have h := (convex_ball (0 : ℂ) 1) hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
    have e : x + t • (y - x) = (1 - t) • x + t • y := by module
    rw [e]
    exact h
  have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension q) (Metric.ball (0 : ℂ) 1) :=
    hq.of_le (by exact_mod_cast le_top)
  have hvd : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (x + t • (y - x)) :=
    (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hmem)).mdifferentiableAt one_ne_zero
  have hs := riemannianCurveSpeed_comp (r := diskExtension q)
    (v := fun t : ℝ => x + t • (y - x)) (t := t) g hmd hvd.differentiableAt
  have hd : deriv (F := TangentSpace 𝓘(ℝ, ℂ) (x + t • (y - x)))
      (fun t : ℝ => x + t • (y - x)) t = y - x := hvd.deriv
  rw [hd] at hs
  rw [hs, inner_mfderiv_of_conformal_IM6 g (hconf _ hmem), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), mul_comm]
  rfl

/-- 开盘内线段的 `q^*g`-长度（`diskSegLength_NK`）= `∫⁻ t ∈ [0,1], √(lam (x + t(y−x))) ‖y − x‖`。 -/
theorem diskSegLength_eq_conformal_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    {x y : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) 1) (hy : y ∈ Metric.ball (0 : ℂ) 1) :
    diskSegLength_NK g q x y = ∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖) := by
  unfold diskSegLength_NK riemannianCurveELength
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [riemannianCurveSpeed_seg_conformal_IM6 g hq hconf hx hy ht]

/-- GEO-MIN 的 `hseg`（`ℝ≥0∞` 形）：`d_q(z₀, y) ≤ d_q(z₀, x) + ∫⁻ t ∈ [0,1], √(lam) ‖y − x‖`。 -/
theorem diskEDist_le_add_conformal_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (z₀ : ℂ) {x y : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) 1) (hy : y ∈ Metric.ball (0 : ℂ) 1) :
    diskEDist_NK g q z₀ y ≤ diskEDist_NK g q z₀ x + ∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖) := by
  refine (diskEDist_triangle_NK g q (w := x)).trans (add_le_add le_rfl ?_)
  exact (diskEDist_le_seg_NK g q hx hy).trans_eq (diskSegLength_eq_conformal_IM6 g hq hconf hx hy)

/-- **c3（通用形）**：共形 IMS05′（`lam` 形；`hlam` 是 S-W-STAB G2/G3 + S-W-EIG G2 + O-W-GEO-MIN G1–G3 +
S-W-GEO + O-IFACE G3 的合成结论，对任意满足 `d z₀ = 0` 与线段界 `hseg` 的 `d : ℂ → ℝ≥0∞`）⇒
S-W-NECK G4 的显式参数 `hIMS05`（`σ` 一般；`σ = 1/2` 时逐字）。`d := diskEDist_NK g q z₀`。 -/
theorem ims05_radius_bound_of_conformal_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    {σ : ℝ} (hσ : 0 < σ)
    (hlam : ∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r → 0 < σ →
      d z₀ = 0 →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
        ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g q (x + t • (y - x))) * ‖y - x‖)) →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ))) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) :=
  fun z₀ r hz₀ hr hK hS hR => hlam (diskEDist_NK g q z₀) z₀ r hz₀ hr hσ
    (diskEDist_self_NK g q hz₀)
    (fun _ hx _ hy => diskEDist_le_add_conformal_IM6 g hq hconf z₀ hx hy) hK hS hR

end GC.LongTime
