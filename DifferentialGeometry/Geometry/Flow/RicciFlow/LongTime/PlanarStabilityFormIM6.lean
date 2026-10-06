import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ims05StabilityIM6

/-!
# 共形稳定性的两种积分形状互换（O-W-IMS06 G7，c3 换写 (a)，后缀 `_IM6`）

S-W-STAB-2 `IsMorreyDisk.planar_stability_WS2` 输出 `0 ≤ ∫_Ω (‖fderiv ℝ ψ x‖² + Wt x ψ x²)`；
S-W-EIG / G6 `ims05_radius_bound_of_planarStability_IM6` 吃 `0 ≤ ∫_Ω ((∂₁ψ)² + (∂_Iψ)²) + ∫_Ω W ψ²`。
* `norm_sq_clm_complex_IM6`：`L : ℂ →L[ℝ] ℝ` ⇒ `‖L‖² = (L 1)² + (L I)²`
  （Riesz：`InnerProductSpace.toDual`）。
* **`stab_components_of_norm_IM6`**：`W` 在开 `Ω` 上连续、`ψ ∈ C_c^∞`、`tsupport ψ ⊆ Ω` ⇒ 单积分形 ⇒ 两积分形
  （两项各自可积：`‖dψ‖²` 连续紧支撑；`W ψ²` 在紧集 `tsupport ψ` 上连续、其外为 0）。
* **`ims05_radius_bound_of_normStability_IM6`**：G6 主定理的 STAB-2 形接口（`hstab` 用 `‖fderiv‖²` 单积分）。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

/-- 实值线性泛函 `L : ℂ →L[ℝ] ℝ` 的范数平方 `= (L 1)² + (L I)²`。 -/
theorem norm_sq_clm_complex_IM6 (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = L 1 ^ 2 + L Complex.I ^ 2 := by
  set w : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm L with hw
  have hL : ∀ z, L z = inner ℝ w z := by
    intro z
    rw [hw, InnerProductSpace.toDual_symm_apply]
  have hn : ‖L‖ = ‖w‖ := by
    rw [hw, LinearIsometryEquiv.norm_map]
  have h1 : L 1 = w.re := by rw [hL]; simp [Complex.inner]
  have hI : L Complex.I = w.im := by rw [hL]; simp [Complex.inner]
  rw [hn, h1, hI, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- 单积分形（`‖fderiv‖²`）⇒ 两积分形（分量），`W` 在开 `Ω` 上连续。 -/
theorem stab_components_of_norm_IM6 {Ω : Set ℂ} (hΩ : IsOpen Ω) {W : ℂ → ℝ}
    (hW : ContinuousOn W Ω) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    (h : 0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + W x * ψ x ^ 2)) :
    0 ≤ (∫ z in Ω, ((fderiv ℝ ψ z 1) ^ 2 + (fderiv ℝ ψ z Complex.I) ^ 2)) +
      ∫ z in Ω, W z * ψ z ^ 2 := by
  have hdψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hf1c : Continuous (fun z => (fderiv ℝ ψ z 1) ^ 2 + (fderiv ℝ ψ z Complex.I) ^ 2) := by
    have h1 : Continuous (fun z => fderiv ℝ ψ z 1) := hdψ.clm_apply continuous_const
    have h2 : Continuous (fun z => fderiv ℝ ψ z Complex.I) := hdψ.clm_apply continuous_const
    exact (h1.pow 2).add (h2.pow 2)
  have hf1s : HasCompactSupport
      (fun z => (fderiv ℝ ψ z 1) ^ 2 + (fderiv ℝ ψ z Complex.I) ^ 2) := by
    refine (hψc.fderiv (𝕜 := ℝ)).mono' fun z hz => ?_
    by_contra hz0
    have h0 : fderiv ℝ ψ z = 0 := image_eq_zero_of_notMem_tsupport hz0
    exact hz (by simp [h0])
  have hf1 : IntegrableOn (fun z => (fderiv ℝ ψ z 1) ^ 2 + (fderiv ℝ ψ z Complex.I) ^ 2) Ω :=
    (hf1c.integrable_of_hasCompactSupport hf1s).integrableOn
  have hK : IsCompact (tsupport ψ) := hψc
  have hf2K : IntegrableOn (fun z => W z * ψ z ^ 2) (tsupport ψ) :=
    ((hW.mono hψΩ).mul (hψ.continuous.pow 2).continuousOn).integrableOn_compact hK
  have hf2 : IntegrableOn (fun z => W z * ψ z ^ 2) Ω := by
    refine hf2K.of_forall_sdiff_eq_zero hΩ.measurableSet fun z hz => ?_
    have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
    simp [this]
  have heq : ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + W x * ψ x ^ 2) =
      ∫ x in Ω, (((fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2) + W x * ψ x ^ 2) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [norm_sq_clm_complex_IM6]
  rw [heq, integral_add hf1 hf2] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **c3（STAB-2 形接口）**：G6 主定理，`hstab` 换成 S-W-STAB-2 `planar_stability_WS2` 的单积分形
（`‖fderiv ℝ ψ x‖² + lam·VJ·ψ²`）。 -/
theorem ims05_radius_bound_of_normStability_IM6 [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hq : DiskSmoothInterior (E := E) q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension q) z)
    (himm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {σ : ℝ} (hσ : 0 < σ) (VJ : ℂ → ℝ)
    (hVJ : ContDiffOn ℝ (⊤ : ℕ∞) VJ (Metric.ball (0 : ℂ) 1))
    (hVJle : ∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤
      -Laplacian.laplacian (fun p => Real.log (diskConformalFactor_IM6 g q p)) z /
        (2 * diskConformalFactor_IM6 g q z) - metricScalarAt g (diskExtension q z) / 2)
    (hstab : ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 →
      ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 +
          diskConformalFactor_IM6 g q x * VJ x * ψ x ^ 2)) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) :=
  ims05_radius_bound_of_planarStability_IM6 g hq hconf himm hσ VJ hVJ hVJle
    fun Ω hΩ hΩb ψ hψ hψc hψΩ => stab_components_of_norm_IM6 hΩ
      ((((contDiffOn_diskConformalFactor_IM6 g hq).mul hVJ).continuousOn).mono hΩb) hψ hψc hψΩ
      (hstab Ω hΩb ψ hψ hψc hψΩ)

end GC.LongTime
