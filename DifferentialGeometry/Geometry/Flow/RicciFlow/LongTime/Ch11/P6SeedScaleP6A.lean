import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A

/-!
# P6 链 L10 与 L13a：种子尺度归约与 `r̄(A)` 的 canonical 尺度算术（O-CH11-P6A G3，后缀 `_P6A`）

design `docs/geometrization/chapter8/design-C11-P6-20261006.md` §1.3、§4：

* **L10** `scalar_le_of_threshold_points_P6A`（slice 级，纯 Riemannian + IVT）：全局 KL70.2
  （`ST/BoundedCurvatureAtDistanceBoundedThreshold.lean:900`）与 E-local 的结论都是 "以 `R(y)` 为尺度"
  的形：`R(y) = q` 的点 `y` 周围 `R ≤ K q`。若种子 `p` 处 `R(p) ≤ q`，且 `B(p, ρ)` 内每个 `R(y) = q` 的点都有
  `B(y, 2ρ)` 上 `R ≤ K q`，则 `B(p, ρ)` 上 `R ≤ max q (K q)`。证明：`R(z) > q` 时在路连通球 `B(p, ρ)` 上
  对 `R` 用介值定理找 `R(y) = q`，再用三角不等式 `z ∈ B(y, 2ρ)`。
* **L13a** `canonicalScale_of_small_radius_P6A`（参数算术）：`ρ` 正且 antitone，`0 ≤ t ≤ T`，
  `0 < r ≤ (√(K₁/T)·ρ(T))·√t` ⇒ `ρ(t)⁻² ≤ K₁ r⁻²`。这就是 S8 早期时间的 `r̄(A)` 选择：`t < T(A)` 时阈值
  `K₁ r⁻²` 已在 canonical 尺度 `ρ(t)⁻²` 之上，profile `canonical` 直接给 witness，不需要 δ 的 KL 包络。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

/-! ## L10：种子尺度归约 -/

/-- **L10**：`R(p) ≤ q`，且 `B(p, ρ)` 中每个 `R(y) = q` 的点 `y` 满足 `B(y, 2ρ)` 上 `R ≤ K q`
（"以 `R(y)` 为尺度" 的 curvature-at-distance），则 `B(p, ρ)` 上 `R ≤ max q (K q)`。 -/
theorem scalar_le_of_threshold_points_P6A {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (p : M) {ρ q K : ℝ} (hρ : 0 < ρ)
    (hp : metricScalarAt g p ≤ q)
    (hE : ∀ y ∈ riemannianBallOf g p ρ, metricScalarAt g y = q →
      ∀ z ∈ riemannianBallOf g y (2 * ρ), metricScalarAt g z ≤ K * q) :
    ∀ z ∈ riemannianBallOf g p ρ, metricScalarAt g z ≤ max q (K * q) := by
  intro z hz
  rcases le_or_gt (metricScalarAt g z) q with hzq | hzq
  · exact hzq.trans (le_max_left _ _)
  have hconn := (isPathConnected_riemannianBallOf g p hρ).isConnected.isPreconnected
  have hpmem : p ∈ riemannianBallOf g p ρ := by
    change riemannianEDistOf g p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hcont : Continuous (fun x : M => metricScalarAt g x) := (metricScalar_smooth g).continuous
  obtain ⟨y, hy, hyq⟩ := hconn.intermediate_value hpmem hz hcont.continuousOn ⟨hp, hzq.le⟩
  have hzy : z ∈ riemannianBallOf g y (2 * ρ) := by
    change riemannianEDistOf g y z < ENNReal.ofReal (2 * ρ)
    have h1 : riemannianEDistOf g y p < ENNReal.ofReal ρ := by
      rw [riemannianEDistOf_comm]
      exact hy
    have h2 : riemannianEDistOf g p z < ENNReal.ofReal ρ := hz
    calc riemannianEDistOf g y z ≤ riemannianEDistOf g y p + riemannianEDistOf g p z :=
          riemannianEDistOf_triangle g y p z
      _ < ENNReal.ofReal ρ + ENNReal.ofReal ρ := ENNReal.add_lt_add h1 h2
      _ = ENNReal.ofReal (2 * ρ) := by rw [two_mul, ENNReal.ofReal_add hρ.le hρ.le]
  exact (hE y hy hyq z hzy).trans (le_max_right _ _)

/-! ## L13a：`r̄(A)` 的 canonical 尺度算术 -/

/-- **L13a**：`ρ` 在 `[0, ∞)` 上正且 antitone，`0 ≤ t ≤ T`，`0 < r ≤ (√(K₁/T)·ρ(T))·√t`
⇒ `ρ(t)⁻² ≤ K₁ r⁻²`（即 `r² ≤ K₁ ρ(t)²`）。 -/
theorem canonicalScale_of_small_radius_P6A {ρ : ℝ → ℝ} (hanti : AntitoneOn ρ (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < ρ t) {K₁ T t r : ℝ} (hK₁ : 0 < K₁) (hT : 0 < T)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hr : 0 < r)
    (hrt : r ≤ (Real.sqrt (K₁ / T) * ρ T) * Real.sqrt t) :
    (ρ t ^ 2)⁻¹ ≤ K₁ * (r ^ 2)⁻¹ := by
  have hρt : 0 < ρ t := hpos t ht0
  have hρT : 0 < ρ T := hpos T hT.le
  have hmono : ρ T ≤ ρ t := hanti (mem_Ici.2 ht0) (mem_Ici.2 hT.le) htT
  have hKT : 0 ≤ K₁ / T := div_nonneg hK₁.le hT.le
  -- `r² ≤ (K₁/T)·ρ(T)²·t`
  have hsq : r ^ 2 ≤ (K₁ / T) * ρ T ^ 2 * t := by
    have h := pow_le_pow_left₀ hr.le hrt 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hKT, Real.sq_sqrt ht0] at h
    exact h
  -- `(K₁/T)·ρ(T)²·t ≤ K₁·ρ(t)²`
  have hstep : (K₁ / T) * ρ T ^ 2 * t ≤ K₁ * ρ t ^ 2 := by
    have htT' : t / T ≤ 1 := (div_le_one hT).2 htT
    have hρsq : ρ T ^ 2 ≤ ρ t ^ 2 := pow_le_pow_left₀ hρT.le hmono 2
    have hexp : (K₁ / T) * ρ T ^ 2 * t = K₁ * ρ T ^ 2 * (t / T) := by
      field_simp
    rw [hexp]
    have htT0 : 0 ≤ t / T := div_nonneg ht0 hT.le
    calc K₁ * ρ T ^ 2 * (t / T) ≤ K₁ * ρ T ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left htT' (by positivity)
      _ = K₁ * ρ T ^ 2 := mul_one _
      _ ≤ K₁ * ρ t ^ 2 := mul_le_mul_of_nonneg_left hρsq hK₁.le
  have hfin : r ^ 2 ≤ K₁ * ρ t ^ 2 := hsq.trans hstep
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hρt 2) (pow_pos hr 2)]
  linarith

/-- consumer：L13a 用于 S8 的早期时间：取 `r̄ := √(K₁/T)·ρ(T)`，则 `r ≤ r̄√t`（`t ≤ T`）时
`R(y) ≥ 2K₁ r⁻²` 的点严格高于 canonical 阈值 `ρ(t)⁻²`（profile `canonical` 的前提形）。 -/
example {ρ : ℝ → ℝ} (hanti : AntitoneOn ρ (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < ρ t)
    {K₁ T t r R : ℝ} (hK₁ : 0 < K₁) (hT : 0 < T) (ht0 : 0 ≤ t) (htT : t ≤ T) (hr : 0 < r)
    (hrt : r ≤ (Real.sqrt (K₁ / T) * ρ T) * Real.sqrt t) (hR : 2 * K₁ * (r ^ 2)⁻¹ ≤ R) :
    (ρ t ^ 2)⁻¹ < R := by
  have h := canonicalScale_of_small_radius_P6A hanti hpos hK₁ hT ht0 htT hr hrt
  have hpos' : 0 < K₁ * (r ^ 2)⁻¹ := mul_pos hK₁ (inv_pos.mpr (pow_pos hr 2))
  linarith

/-- consumer：L10 + `hasSmallParabolicCurvature` 的种子界：history slice 上，若 `B(p, ρ)`
（`ρ ≤ r`）中 `R(y) = q`（`q ≥ 3r⁻²`）的点都有 `B(y, 2ρ)` 上 `R ≤ K q`，则 `B(p, ρ)` 上
`R ≤ max q (K q)`（种子 `|R(p)| ≤ 3r⁻²` 由 `hasSmallParabolicCurvature_scalar_abs_le_C11S` 给）。 -/
example {H : ObservedHistory} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r ρ q K : ℝ} (hsmall : hasSmallParabolicCurvature H t p r)
    (hρ : 0 < ρ) (hq : 3 * (r ^ 2)⁻¹ ≤ q)
    (hE : ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      metricScalarAt (H.stageMetric (H.activeStage t) t) y = q →
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (2 * ρ),
        metricScalarAt (H.stageMetric (H.activeStage t) t) z ≤ K * q) :
    ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      metricScalarAt (H.stageMetric (H.activeStage t) t) z ≤ max q (K * q) := by
  have hpmem : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hsmall.1
  have hp := (le_abs_self _).trans (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpmem)
  exact scalar_le_of_threshold_points_P6A _ p hρ (hp.trans hq) hE

end GC.LongTime.Ch11
