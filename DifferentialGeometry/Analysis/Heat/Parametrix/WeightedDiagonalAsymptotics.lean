import DifferentialGeometry.Analysis.Heat.Kernel.Basic
import DifferentialGeometry.Analysis.Heat.Parametrix.UniformBound
import DifferentialGeometry.Geometry.Curvature.Metric

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]


private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem integrable_mul_continuous
    {g : SmoothRiemannianMetric I M} {w f : M → ℝ}
    (hw : Integrable w (riemannianVolumeMeasure (I := I) (M := M) g)) (hf : Continuous f) :
    Integrable (fun x => w x * f x) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact hw.mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun x => hC x (mem_univ x))

private theorem integral_mul_heatKernel_diagonal_sub_leading_eq
    {g : SmoothRiemannianMetric I M} {w : M → ℝ}
    (hw : Integrable w (riemannianVolumeMeasure (I := I) (M := M) g)) {t : ℝ} (ht : 0 < t) :
    (∫ x, w x * (heatKernel g t x x - 1 / (4 * Real.pi * t))
      ∂riemannianVolumeMeasure (I := I) (M := M) g) -
        (∫ x, w x * Geometry.Curvature.metricScalarAt g x
          ∂riemannianVolumeMeasure (I := I) (M := M) g) / (24 * Real.pi) =
      ∫ x, w x * (heatKernel g t x x - 1 / (4 * Real.pi * t) -
        Geometry.Curvature.metricScalarAt g x / (24 * Real.pi))
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have hkernel : Continuous (fun x => heatKernel g t x x) :=
    (continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_id.prodMk continuous_id))
      (fun _ => ⟨ht, mem_univ _⟩)
  have hcurv : Continuous (fun x => Geometry.Curvature.metricScalarAt g x) :=
    (Geometry.Curvature.metricScalar_smooth g).continuous
  have hmain : Integrable (fun x => w x *
      (heatKernel g t x x - 1 / (4 * Real.pi * t)))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_mul_continuous hw
      (hkernel.sub (continuous_const (y := 1 / (4 * Real.pi * t))))
  have hR : Integrable (fun x => w x * Geometry.Curvature.metricScalarAt g x /
      (24 * Real.pi)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_mul_continuous hw hcurv).div_const _
  rw [← integral_div, ← integral_sub hmain hR]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem exists_integral_mul_heatKernel_diagonal_sub_leading_bound_of_local_bound
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ x ∈ U,
        |heatKernel g t x x - 1 / (4 * Real.pi * t) -
          Geometry.Curvature.metricScalarAt g x / (24 * Real.pi)| ≤ t * C) :
    Module.finrank ℝ E = 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : M → ℝ, Integrable w (riemannianVolumeMeasure (I := I) (M := M) g) →
      ∀ t ∈ Ioc 0 T,
        |(∫ x, w x * (heatKernel g t x x - 1 / (4 * Real.pi * t))
          ∂riemannianVolumeMeasure (I := I) (M := M) g) -
            (∫ x, w x * Geometry.Curvature.metricScalarAt g x
              ∂riemannianVolumeMeasure (I := I) (M := M) g) / (24 * Real.pi)| ≤
          t * C * ∫ x, |w x| ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  intro hn
  classical
  choose U hU hp C hC hbound using hlocal
  have hcover : (univ : Set M) ⊆ ⋃ p ∈ (univ : Set M), U p := by
    intro p _
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨mem_univ p, hp p⟩⟩
  obtain ⟨C₀, hC₀, hbound₀⟩ := exists_uniform_linear_time_bound_of_compact_cover
    isCompact_univ (fun p _ => hU p) hcover
    (fun p _ => ⟨C p, hC p, hbound p⟩)
  refine ⟨C₀, hC₀, ?_⟩
  intro w hw t ht
  rw [integral_mul_heatKernel_diagonal_sub_leading_eq hw ht.1]
  have hb := norm_integral_le_of_norm_le (hw.norm.const_mul (t * C₀))
    (show ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      ‖w x * (heatKernel g t x x - 1 / (4 * Real.pi * t) -
        Geometry.Curvature.metricScalarAt g x / (24 * Real.pi))‖ ≤
          t * C₀ * ‖w x‖ from by
      apply Eventually.of_forall
      intro x
      simp only [norm_mul, Real.norm_eq_abs]
      simpa only [mul_comm (t * C₀)] using
        mul_le_mul_of_nonneg_left (hbound₀ t ht x (mem_univ x)) (abs_nonneg (w x)))
  simpa only [Real.norm_eq_abs, integral_const_mul] using hb

theorem tendsto_integral_mul_heatKernel_diagonal_sub_leading_of_local_bound
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ x ∈ U,
        |heatKernel g t x x - 1 / (4 * Real.pi * t) -
          Geometry.Curvature.metricScalarAt g x / (24 * Real.pi)| ≤ t * C)
    {w : M → ℝ} (hw : Integrable w (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Module.finrank ℝ E = 2 →
    Tendsto (fun t => ∫ x, w x * (heatKernel g t x x - 1 / (4 * Real.pi * t))
      ∂riemannianVolumeMeasure (I := I) (M := M) g) (𝓝[>] 0)
        (𝓝 ((∫ x, w x * Geometry.Curvature.metricScalarAt g x
          ∂riemannianVolumeMeasure (I := I) (M := M) g) / (24 * Real.pi))) := by
  intro hn
  obtain ⟨C, _, hbound⟩ :=
    (exists_integral_mul_heatKernel_diagonal_sub_leading_bound_of_local_bound g hlocal) hn
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmajor := (hid.mul_const C).mul_const (∫ x, |w x| ∂riemannianVolumeMeasure (I := I) (M := M) g)
  simp only [zero_mul] at hmajor
  have herr := squeeze_zero_norm' (f := fun t =>
      (∫ x, w x * (heatKernel g t x x - 1 / (4 * Real.pi * t))
        ∂riemannianVolumeMeasure (I := I) (M := M) g) -
          (∫ x, w x * Geometry.Curvature.metricScalarAt g x
            ∂riemannianVolumeMeasure (I := I) (M := M) g) / (24 * Real.pi))
    (by
      filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      simpa only [Real.norm_eq_abs] using hbound w hw t ⟨ht.1, ht.2.le⟩) hmajor
  simpa only [sub_add_cancel, zero_add] using
    herr.add (tendsto_const_nhds (x := (∫ x, w x * Geometry.Curvature.metricScalarAt g x
      ∂riemannianVolumeMeasure (I := I) (M := M) g) / (24 * Real.pi)))

end DifferentialGeometry.Analysis.HeatEquation
