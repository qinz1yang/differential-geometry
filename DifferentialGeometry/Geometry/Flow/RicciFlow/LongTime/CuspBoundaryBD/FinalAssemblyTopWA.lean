import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.CurvatureAssemblyTopWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BoundaryAssemblyTopWA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop

/-!
# IMS04 / G6（S-A10-BOUNDARY, suffix `_BD`）：边界项 `< π` 的最终组装（曲率输入为 `↥ball` 上的性质参数）

`BoundaryAssembly.boundary_integral_le_TBD`（`|∫ density| ≤ Kc · √(t(1+acc))·L`）+
`CurvatureAssembly.sqrt_curvature_transported_eq_TBD`（stage 曲率 = `(√t)⁻¹ ·` ball 上 `ĝ_t` 曲率）：

`ĝ_t`-曲率 `≤ κ₁` ⇒ `Kc = κ₁ (√t)⁻¹` ⇒ `|∫ density| ≤ κ₁ · √(1 + acc t) · L`。

`↥ball` 上的曲率界（O-W-CURV：`horocycle` 模型曲率 `1/2` + `metric_error` k=1）用显式性质参数 `hcurv`
（对每个 `s` 的数值不等式）进入，不引入新结构；O-W-CURV 交付后 `hcurv` 用其定理实例化。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff Real
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G6（逐 `t`）**：`ĝ_t`-曲率 `≤ κ₁`（`β_B` 沿 `s`）⇒ 边界项 `≤ κ₁·√(1+acc t)·L`。 -/
theorem PrescribedCuspMeridianTop_CPQ.boundary_integral_le_of_ball_curvature_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (hacc : cores.accuracy t < 1)
      (U : ℂ → (postStage F.observation t).Carrier) {s : Set ℂ}, IsOpen s →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U s → Metric.closedBall (0 : ℂ) 1 ⊆ s →
      (∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q) →
      ∀ {φ : ℝ → ℝ}, ContDiff ℝ ∞ φ → Monotone φ → φ π = φ (-π) + 1 →
      U ∘ circleMap 0 1 = loopLift (M.transported t ht) ∘ φ → ∀ {κ₁ : ℝ},
      (∀ x, Real.sqrt
          ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
          (M.sliceBall_TBD t ht x)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_TBD t ht) x)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_TBD t ht) x)) ≤ κ₁) →
      |∫ θ in -π..π, diskMapTraceBoundaryDensity (postMetric F.observation t) U
        (loopLift (M.transported t ht)) φ θ| ≤
        κ₁ * (Real.sqrt (1 + cores.accuracy t) * L) := by
  obtain ⟨L, hL0, hL1, hbd⟩ := M.boundary_integral_le_TBD
  refine ⟨L, hL0, hL1, fun t ht hacc U s hs hU hDs hconf φ hφ hmono hdeg htrace κ₁ hcurv => ?_⟩
  have htpos : 0 < t := cores.start_pos.trans_le (M.exterior.after_cores.trans ht)
  have hκ₁ : 0 ≤ κ₁ := (Real.sqrt_nonneg _).trans (hcurv 0)
  have hK : ∀ x, Real.sqrt ((postMetric F.observation t).inner (loopLift (M.transported t ht) x)
      (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) x)
      (riemannianCurveCurvature (postMetric F.observation t) (loopLift (M.transported t ht)) x))
      ≤ κ₁ * (Real.sqrt t)⁻¹ := by
    intro x
    rw [M.sqrt_curvature_transported_eq_TBD t ht hacc x, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcurv x) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have h := hbd t ht hacc U hs hU hDs hconf hφ hmono hdeg htrace hK
  refine h.trans (le_of_eq ?_)
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
  rw [Real.sqrt_mul htpos.le]
  field_simp

/-- **G6 consumer（边界项 `< π`）**：若 `↥ball` 上 `ĝ_t`-曲率 `≤ 3`（`acc t < 1/12` 时），则 `t` 够大时
`|∫_{-π..π} diskMapTraceBoundaryDensity| < π`——`-2π + 边界项` 与 barrier 的 `-π` 之差。 -/
theorem PrescribedCuspMeridianTop_CPQ.boundary_integral_lt_pi_TBD
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (hcurv : ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (hacc : cores.accuracy t < 1),
      cores.accuracy t < 1 / 12 → ∀ x,
      Real.sqrt ((cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc).inner
          (M.sliceBall_TBD t ht x)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_TBD t ht) x)
          (riemannianCurveCurvature
            (cores.pulledMetric_BD M.model t (M.exterior.after_cores.trans ht) hacc)
            (M.sliceBall_TBD t ht) x)) ≤ 3) :
    ∃ T : ℝ, ∀ (t : ℝ) (ht : M.exterior.start ≤ t), T ≤ t →
      ∀ (U : ℂ → (postStage F.observation t).Carrier) {s : Set ℂ}, IsOpen s →
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 3) ∞ U s → Metric.closedBall (0 : ℂ) 1 ⊆ s →
      (∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (postMetric F.observation t) U q) →
      ∀ {φ : ℝ → ℝ}, ContDiff ℝ ∞ φ → Monotone φ → φ π = φ (-π) + 1 →
      U ∘ circleMap 0 1 = loopLift (M.transported t ht) ∘ φ →
      |∫ θ in -π..π, diskMapTraceBoundaryDensity (postMetric F.observation t) U
        (loopLift (M.transported t ht)) φ θ| < π := by
  obtain ⟨L, hL0, hL1, hfin⟩ := M.boundary_integral_le_of_ball_curvature_TBD
  obtain ⟨T, hT⟩ := cores.accuracy_decay (1 / 12) (by norm_num)
  refine ⟨T, fun t ht hTt U s hs hU hDs hconf φ hφ hmono hdeg htrace => ?_⟩
  have hacc12 := hT t hTt
  have hacc : cores.accuracy t < 1 := hacc12.trans (by norm_num)
  have h := hfin t ht hacc U hs hU hDs hconf hφ hmono hdeg htrace (κ₁ := 3)
    (hcurv t ht hacc hacc12)
  have hpos := cores.accuracy_pos t (M.exterior.after_cores.trans ht)
  have hsq : Real.sqrt (1 + cores.accuracy t) < 1.0466 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
    linarith
  have hpi := Real.pi_gt_d2
  calc _ ≤ 3 * (Real.sqrt (1 + cores.accuracy t) * L) := h
    _ < 3 * (1.0466 * 1) := by
      refine mul_lt_mul_of_pos_left ?_ (by norm_num)
      exact mul_lt_mul'' hsq hL1 (Real.sqrt_nonneg _) hL0.le
    _ < π := by linarith

end GC.LongTime.CuspP1
