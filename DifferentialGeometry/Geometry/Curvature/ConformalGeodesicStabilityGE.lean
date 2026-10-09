import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus
import DifferentialGeometry.Geometry.Curvature.ConformalPlane

/-!
# IMS05′ 第 (5) 步的纯计算部分：共形曲率公式与指标形式的 `g_Σ` 弧长换算（S-W-GEO G1）

蓝图 IMS05（`master207A.tex` l.18386–18440）：`Σ = (Ω ⊂ ℂ, g_Σ = lam |dz|²)`，`u > 0` 满足
`Δ_Σ u = (K_Σ − q − μ) u`，`ĝ = u² g_Σ = ρ²|dz|²`，`ρ = u √lam`。本文件（全部是显式函数参数，没有新结构 / 新 Prop）：

* `conformalCurvature_eq_GE`（(a)）：`K̂ := −ρ⁻² Δ(log ρ) = u⁻² (q + μ + |∇ log u|²_Σ)`
  （`|∇ v|²_Σ = lam⁻¹((∂₁v)² + (∂_I v)²)`）；点态（`ContDiffAt ℝ 2`）版本，`Δ = Laplacian.laplacian`。
* `planeGaussianCurvature_eq_GE`：与树里 `planeGaussianCurvature (conformalEuclideanMetric f hf)`
  （`Curvature/ConformalPlane.lean`）的衔接（全局光滑 `f` 局部等于 `log ρ`）。
* `sigma_half_add_sq_le_GE`：`q ≥ σ/2`、`μ ≥ 0`、`lam ‖c′‖² = 1` ⇒ `σ/2 + (v′)² ≤ Q`
  （`v′ = dv(c′)`，Cauchy–Schwarz；O-IFACE G3 `mul_sq_le_of_weighted_stability_IF` 的 `hQ`）。
* `weighted_stability_of_second_variation_GE`（(e)，主定理）：以第二变分非负（指标形式，对 `c` 的
  任意正则参数化成立：`∫ (φ′²/ê − K̂ ê φ²)`，`ê = ρ(c)‖c′‖`）为显式假设，`c` 是 `g_Σ` 弧长参数化
  （`lam(c)‖c′‖² = 1`）⇒ `∀ φ ∈ C¹₀[0,L], 0 ≤ ∫₀ᴸ e^{−v}(φ′² − Q φ²)`，这正是 O-IFACE G3
  `mul_sq_le_of_weighted_stability_IF` 的 `hstab` 输入（逐字）。在 `g_Σ` 弧长下 `ê = u(c)`，所以不需要换元。
-/

set_option autoImplicit false
noncomputable section

open Set Filter intervalIntegral InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

/-- `log (u √lam) = log u + log lam / 2` 在 `z` 的邻域上（`u`、`lam` 在 `z` 连续且为正）。 -/
theorem log_conformalFactor_eventuallyEq_GE {u lam ρ : ℂ → ℝ} {z : ℂ}
    (hu : ContinuousAt u z) (hlam : ContinuousAt lam z) (hu0 : 0 < u z) (hlam0 : 0 < lam z)
    (hρ : ∀ p, ρ p = u p * Real.sqrt (lam p)) :
    (fun p => Real.log (ρ p)) =ᶠ[𝓝 z] fun p => Real.log (u p) + Real.log (lam p) / 2 := by
  filter_upwards [hu.eventually (lt_mem_nhds hu0), hlam.eventually (lt_mem_nhds hlam0)]
    with p hp hp'
  rw [hρ p, Real.log_mul hp.ne' (Real.sqrt_pos.2 hp').ne', Real.log_sqrt hp'.le]

/-- (a) 共形曲率公式：`K̂ = −ρ⁻² Δ(log ρ) = u⁻² (q + μ + |∇ log u|²_Σ)`，`ρ = u √lam`，
`Δu = lam (K_Σ − q − μ) u`，`K_Σ = −Δ(log lam)/(2 lam)`。 -/
theorem conformalCurvature_eq_GE {u lam q ρ : ℂ → ℝ} {μ : ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hlam : ContDiffAt ℝ 2 lam z)
    (hu0 : 0 < u z) (hlam0 : 0 < lam z) (hρ : ∀ p, ρ p = u p * Real.sqrt (lam p))
    (hpde : Laplacian.laplacian u z = lam z *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - q z - μ) * u z) :
    -(ρ z)⁻¹ ^ 2 * Laplacian.laplacian (fun p => Real.log (ρ p)) z =
      (u z)⁻¹ ^ 2 * (q z + μ + (lam z)⁻¹ * (fderiv ℝ (fun p => Real.log (u p)) z 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) z Complex.I ^ 2)) := by
  have hlogu : ContDiffAt ℝ 2 (fun p => Real.log (u p)) z :=
    (Real.contDiffAt_log.2 hu0.ne').comp z hu
  have hloglam : ContDiffAt ℝ 2 (fun p => Real.log (lam p)) z :=
    (Real.contDiffAt_log.2 hlam0.ne').comp z hlam
  rw [(laplacian_congr_nhds (log_conformalFactor_eventuallyEq_GE
    (hu.continuousAt) (hlam.continuousAt) hu0 hlam0 hρ)).eq_of_nhds]
  have hhalf : ContDiffAt ℝ 2 (fun p => Real.log (lam p) / 2) z := hloglam.div_const 2
  have hadd : Laplacian.laplacian (fun p => Real.log (u p) + Real.log (lam p) / 2) z =
      Laplacian.laplacian (fun p => Real.log (u p)) z +
        Laplacian.laplacian (fun p => Real.log (lam p)) z / 2 := by
    have h1 := hlogu.laplacian_add hhalf
    have h2 : Laplacian.laplacian (fun p => Real.log (lam p) / 2) z =
        Laplacian.laplacian (fun p => Real.log (lam p)) z / 2 := by
      have h3 := laplacian_smul (E := ℂ) (F := ℝ) (1 / 2 : ℝ) hloglam
      have h4 : (fun p => Real.log (lam p) / 2) = (1 / 2 : ℝ) • (fun p => Real.log (lam p)) := by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [h4, h3]
      simp only [smul_eq_mul]
      ring
    rw [h2] at h1
    exact h1
  rw [hadd, laplacian_log hu hu0.ne']
  set A := fderiv ℝ u z 1
  set B := fderiv ℝ u z Complex.I
  have hdu : fderiv ℝ (fun p => Real.log (u p)) z = (u z)⁻¹ • fderiv ℝ u z := by
    have := (hu.differentiableAt (by norm_num)).hasFDerivAt.log hu0.ne'
    exact this.fderiv
  have hA : fderiv ℝ (fun p => Real.log (u p)) z 1 = A / u z := by
    rw [hdu]; simp [A, div_eq_inv_mul]
  have hB : fderiv ℝ (fun p => Real.log (u p)) z Complex.I = B / u z := by
    rw [hdu]; simp [B, div_eq_inv_mul]
  rw [hA, hB, hρ z]
  have hs : Real.sqrt (lam z) ^ 2 = lam z := Real.sq_sqrt hlam0.le
  set D := Laplacian.laplacian (fun p => Real.log (lam p)) z
  set Δu := Laplacian.laplacian u z
  have hΔu : Δu / u z = -D / 2 - lam z * (q z + μ) := by
    rw [hpde]
    field_simp
    ring
  have hu1 : u z ≠ 0 := hu0.ne'
  have hl1 : lam z ≠ 0 := hlam0.ne'
  have hsq : Real.sqrt (lam z) ≠ 0 := (Real.sqrt_pos.2 hlam0).ne'
  have hmain : -(u z * Real.sqrt (lam z))⁻¹ ^ 2 * (Δu / u z - (A ^ 2 + B ^ 2) / u z ^ 2 + D / 2) =
      (u z)⁻¹ ^ 2 * (q z + μ + (lam z)⁻¹ * ((A / u z) ^ 2 + (B / u z) ^ 2)) := by
    rw [hΔu]
    rw [inv_pow, mul_pow, hs]
    field_simp
    ring
  exact hmain

/-- 衔接：全局光滑 `f` 在 `z` 附近等于 `log ρ` 时，树里的 `planeGaussianCurvature`
（`e^{2f}|dz|²` 的 Gauss 曲率）在 `z` 处等于 (a) 的 `u⁻²(q + μ + |∇ log u|²_Σ)`。 -/
theorem planeGaussianCurvature_eq_GE {u lam q ρ f : ℂ → ℝ} {μ : ℝ} {z : ℂ}
    (hf : ContDiff ℝ ∞ f) (hfρ : f =ᶠ[𝓝 z] fun p => Real.log (ρ p))
    (hu : ContDiffAt ℝ 2 u z) (hlam : ContDiffAt ℝ 2 lam z)
    (hu0 : 0 < u z) (hlam0 : 0 < lam z) (hρ : ∀ p, ρ p = u p * Real.sqrt (lam p))
    (hpde : Laplacian.laplacian u z = lam z *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - q z - μ) * u z) :
    planeGaussianCurvature (conformalEuclideanMetric f hf) z =
      (u z)⁻¹ ^ 2 * (q z + μ + (lam z)⁻¹ * (fderiv ℝ (fun p => Real.log (u p)) z 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) z Complex.I ^ 2)) := by
  rw [planeGaussianCurvature_conformal hf, (laplacian_congr_nhds hfρ).eq_of_nhds,
    ← conformalCurvature_eq_GE hu hlam hu0 hlam0 hρ hpde]
  have hρz : 0 < ρ z := by
    rw [hρ z]
    exact mul_pos hu0 (Real.sqrt_pos.2 hlam0)
  have hfz : f z = Real.log (ρ z) := hfρ.self_of_nhds
  rw [hfz, show -2 * Real.log (ρ z) = -(2 * Real.log (ρ z)) by ring, Real.exp_neg,
    show 2 * Real.log (ρ z) = Real.log (ρ z ^ 2) by
      rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity), inv_pow]

/-- `fderiv` 在 `ℂ` 上按两个坐标偏导数展开：`df(w) = Re w · ∂₁f + Im w · ∂_I f`。 -/
theorem fderiv_apply_eq_GE (f : ℂ → ℝ) (z w : ℂ) :
    fderiv ℝ f z w = w.re * fderiv ℝ f z 1 + w.im * fderiv ℝ f z Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `Q ≥ σ/2 + (v′)²`（O-IFACE G3 的 `hQ`）：`q ≥ σ/2`、`μ ≥ 0`、`lam ‖w‖² = 1`（`w = c′` 是 `g_Σ`
单位切向量）、`v′ = dg(w)`（Cauchy–Schwarz：`(dg w)² ≤ ‖w‖² (g₁² + g_I²) = lam⁻¹ (g₁² + g_I²)`）。 -/
theorem sigma_half_add_sq_le_GE {g : ℂ → ℝ} {z w : ℂ} {lamz qz μ σ : ℝ} (hlam : 0 < lamz)
    (hw : lamz * ‖w‖ ^ 2 = 1) (hq : σ / 2 ≤ qz) (hμ : 0 ≤ μ) :
    σ / 2 + (fderiv ℝ g z w) ^ 2 ≤
      qz + μ + lamz⁻¹ * (fderiv ℝ g z 1 ^ 2 + fderiv ℝ g z Complex.I ^ 2) := by
  rw [fderiv_apply_eq_GE g z w]
  set a := fderiv ℝ g z 1
  set b := fderiv ℝ g z Complex.I
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hinv : lamz⁻¹ = w.re ^ 2 + w.im ^ 2 := by
    rw [← hn]
    field_simp
    linarith
  have hcs : (w.re * a + w.im * b) ^ 2 ≤ (w.re ^ 2 + w.im ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (w.re * b - w.im * a)]
  rw [hinv]
  linarith

/-- (e) 主定理：第二变分非负（指标形式，显式假设 `hd`）⇒ `g_Σ` 弧长参数下的一维稳定性不等式，
逐字是 O-IFACE G3 `mul_sq_le_of_weighted_stability_IF` 的 `hstab`。`v`、`Q` 是任意函数，只要在 `[0,L]` 上
等于 `log u ∘ c`、`(q + μ + |∇ log u|²_Σ) ∘ c`（下游可以先把 `v` 延拓成 `ℝ` 上的 `C¹` 函数）。 -/
theorem weighted_stability_of_second_variation_GE
    {u lam q ρ : ℂ → ℝ} {μ L : ℝ} {c : ℝ → ℂ} {v Q : ℝ → ℝ} (hL : 0 ≤ L)
    (hρ : ∀ p, ρ p = u p * Real.sqrt (lam p))
    (hu0 : ∀ s ∈ Icc 0 L, 0 < u (c s)) (hlam0 : ∀ s ∈ Icc 0 L, 0 < lam (c s))
    (hu : ∀ s ∈ Icc 0 L, ContDiffAt ℝ 2 u (c s))
    (hlam : ∀ s ∈ Icc 0 L, ContDiffAt ℝ 2 lam (c s))
    (hpde : ∀ s ∈ Icc 0 L, Laplacian.laplacian u (c s) = lam (c s) *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) (c s) / (2 * lam (c s)) - q (c s) - μ) *
        u (c s))
    (harc : ∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1)
    (hv : ∀ s ∈ Icc 0 L, v s = Real.log (u (c s)))
    (hQ : ∀ s ∈ Icc 0 L, Q s = q (c s) + μ + (lam (c s))⁻¹ *
      (fderiv ℝ (fun p => Real.log (u p)) (c s) 1 ^ 2 +
        fderiv ℝ (fun p => Real.log (u p)) (c s) Complex.I ^ 2))
    (hd : ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, (φ' s ^ 2 / (ρ (c s) * ‖deriv c s‖) -
        (-(ρ (c s))⁻¹ ^ 2 * Laplacian.laplacian (fun p => Real.log (ρ p)) (c s)) *
          (ρ (c s) * ‖deriv c s‖) * φ s ^ 2)) :
    ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' → φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, Real.exp (-v s) * (φ' s ^ 2 - Q s * φ s ^ 2) := by
  intro φ φ' h1 h2 h3 h4
  refine (hd φ φ' h1 h2 h3 h4).trans_eq (intervalIntegral.integral_congr fun s hs => ?_)
  have hs' : s ∈ Icc 0 L := by rwa [uIcc_of_le hL] at hs
  have hu1 := hu0 s hs'
  have hl1 := hlam0 s hs'
  have hsq : Real.sqrt (lam (c s)) * ‖deriv c s‖ = 1 := by
    rw [← Real.sqrt_sq (norm_nonneg (deriv c s)), ← Real.sqrt_mul hl1.le, harc s hs',
      Real.sqrt_one]
  have hê : ρ (c s) * ‖deriv c s‖ = u (c s) := by
    rw [hρ, mul_assoc, hsq, mul_one]
  have hK := conformalCurvature_eq_GE (q := q) (μ := μ) (hu s hs') (hlam s hs') hu1 hl1 hρ
    (hpde s hs')
  rw [hê, hK, ← hQ s hs', hv s hs', Real.exp_neg, Real.exp_log hu1]
  field_simp

end DifferentialGeometry.Geometry
