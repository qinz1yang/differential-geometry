import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskConformalLengthIM6
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

/-!
# `d_q` 与 IMS05′ 结论在度量缩放下的变换（O-W-IMS06 G8，后缀 `_IM6`）

S-W-TOPGLUE G2 把 NECK G5 的 band 估计搬到 postStage 时用的是归一化 slice 度量
`g′ = scaleMetric (r²)⁻¹ g_post`。IMS06′（S-W-NECK G4）的 `hIMS05` 因而要在 `g′` 下陈述，而 c3
（本车道 G1–G7）在 `g_post` 下产出。本文件：

* `riemannianCurveSpeed_scaleMetric_IM6`、`diskSegLength_scaleMetric_IM6`、
  **`diskEDist_scaleMetric_IM6`**：`d_q^{c g} = √c · d_q^{g}`；
* **`ims05_radius_bound_scale_IM6`**：`g` 下对一切 `σ > 0` 的 `hIMS05` ⇒ `c • g` 下的 `hIMS05`
  （`R_{c g} = c⁻¹ R_g`，半径 `r ↦ r/√c`，`2π√(2/(3cσ)) = 2π√(2/(3σ))/√c`）。
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

theorem riemannianCurveSpeed_scaleMetric_IM6 (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) :
    riemannianCurveSpeed (scaleMetric c hc g) γ t = Real.sqrt c * riemannianCurveSpeed g γ t := by
  unfold riemannianCurveSpeed
  rw [scaleMetric_inner, Real.sqrt_mul hc.le]

theorem diskSegLength_scaleMetric_IM6 (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M)) (p p' : ℂ) :
    diskSegLength_NK (scaleMetric c hc g) q p p' =
      ENNReal.ofReal (Real.sqrt c) * diskSegLength_NK g q p p' := by
  unfold diskSegLength_NK riemannianCurveELength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  rw [riemannianCurveSpeed_scaleMetric_IM6, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- `d_q^{c g} = √c · d_q^{g}`。 -/
theorem diskEDist_scaleMetric_IM6 (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M)) (z w : ℂ) :
    diskEDist_NK (scaleMetric c hc g) q z w =
      ENNReal.ofReal (Real.sqrt c) * diskEDist_NK g q z w := by
  have h0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    simpa using Real.sqrt_pos.mpr hc
  unfold diskEDist_NK
  simp_rw [diskSegLength_scaleMetric_IM6, ← Finset.mul_sum,
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]

/-- **IMS05′ 结论的缩放**：`g` 下对一切 `σ > 0` 成立的 `hIMS05` ⇒ `c • g` 下的 `hIMS05`。 -/
theorem ims05_radius_bound_scale_IM6 [FiniteDimensional ℝ E]
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {q : C(closedDisk, M)}
    (hg : ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)))
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK (scaleMetric c hc g) q z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1,
        diskEDist_NK (scaleMetric c hc g) q z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        diskEDist_NK (scaleMetric c hc g) q z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt (scaleMetric c hc g) (diskExtension q w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)) := by
  intro z₀ r h₀ hr hK hS hR
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c) with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hsc
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr' : ENNReal.ofReal r = a * ENNReal.ofReal (r / Real.sqrt c) := by
    rw [ha, ← ENNReal.ofReal_mul hsc.le, mul_div_cancel₀ _ hsc.ne']
  have hle : ∀ z, diskEDist_NK (scaleMetric c hc g) q z₀ z ≤ ENNReal.ofReal r ↔
      diskEDist_NK g q z₀ z ≤ ENNReal.ofReal (r / Real.sqrt c) := by
    intro z
    rw [diskEDist_scaleMetric_IM6, hr', ENNReal.mul_le_mul_iff_right ha0 hat]
  have heq : ∀ z, diskEDist_NK (scaleMetric c hc g) q z₀ z = ENNReal.ofReal r ↔
      diskEDist_NK g q z₀ z = ENNReal.ofReal (r / Real.sqrt c) := by
    intro z
    rw [diskEDist_scaleMetric_IM6, hr', ENNReal.mul_right_inj ha0 hat]
  have hset : {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
      diskEDist_NK (scaleMetric c hc g) q z₀ z ≤ ENNReal.ofReal r} =
      {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g q z₀ z ≤ ENNReal.ofReal (r / Real.sqrt c)} := by
    ext z
    exact and_congr_right fun _ => hle z
  have key := hg (c * σ) (mul_pos hc hσ) z₀ (r / Real.sqrt c) h₀ (div_pos hr hsc) (hset ▸ hK)
    (by
      obtain ⟨z, hz, hzr⟩ := hS
      exact ⟨z, hz, (heq z).mp hzr⟩)
    (fun z hz hd => (hR z hz ((hle z).mpr hd)).mono fun w hw => by
      rw [metricScalarAt_scaleMetric] at hw
      have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
      calc c * σ ≤ c * (c⁻¹ * metricScalarAt g (diskExtension q w)) :=
            mul_le_mul_of_nonneg_left hw hc.le
        _ = metricScalarAt g (diskExtension q w) := by field_simp)
  have hsq : Real.sqrt (2 / (3 * (c * σ))) = Real.sqrt (2 / (3 * σ)) / Real.sqrt c := by
    rw [← Real.sqrt_div' _ hc.le]
    congr 1
    field_simp
  rw [hsq] at key
  have h2 : r / Real.sqrt c ≤ (2 * Real.pi * Real.sqrt (2 / (3 * σ))) / Real.sqrt c := by
    calc r / Real.sqrt c ≤ 2 * Real.pi * (Real.sqrt (2 / (3 * σ)) / Real.sqrt c) := key
      _ = _ := by ring
  exact (div_le_div_iff_of_pos_right hsc).mp h2

/-- consumer：`c = 1` 时缩放公式退化为恒等。 -/
example (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : C(closedDisk, M)) (z w : ℂ) :
    diskEDist_NK (scaleMetric 1 one_pos g) q z w = diskEDist_NK g q z w := by
  rw [diskEDist_scaleMetric_IM6]
  simp

end GC.LongTime
