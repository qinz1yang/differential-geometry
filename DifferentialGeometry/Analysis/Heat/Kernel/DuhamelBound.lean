import DifferentialGeometry.Analysis.Heat.Kernel.Positivity
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory Set Filter
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem heatKernel_integrable (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x : M) :
    Integrable (fun y => heatKernel g t x y) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    g ((continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (fun _ => ⟨ht, mem_univ _⟩)) (HasCompactSupport.of_compactSpace _)

theorem norm_integral_heatKernel_mul_le (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x : M) {f : M → Real} {C : Real}
    (hf : ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g, ‖f y‖ ≤ C) :
    ‖∫ y, heatKernel g t x y * f y ∂riemannianVolumeMeasure (I := I) (M := M) g‖ ≤ C := by
  have hi := (heatKernel_integrable g ht x).mul_const C
  have hb := norm_integral_le_of_norm_le hi (show ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g,
      ‖heatKernel g t x y * f y‖ ≤ heatKernel g t x y * C from by
    filter_upwards [hf] with y hy
    rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg g ht x y)]
    exact mul_le_mul_of_nonneg_left hy (heatKernel_nonneg g ht x y))
  simpa only [integral_mul_const, integral_heatKernel g ht x, one_mul] using hb

def heatDuhamel (g : SmoothRiemannianMetric I M) (F : ℝ → M → ℝ) (a t : ℝ) (x : M) : ℝ :=
  ∫ s in Ioo a t, ∫ y, heatKernel g (t - s) x y * F s y
    ∂riemannianVolumeMeasure (I := I) (M := M) g

theorem norm_heatDuhamel_le (g : SmoothRiemannianMetric I M)
    {F : ℝ → M → ℝ} {a t C : ℝ} (hat : a ≤ t) (x : M)
    (hF : ∀ s ∈ Ioo a t, ∀ᵐ y ∂riemannianVolumeMeasure (I := I) (M := M) g, ‖F s y‖ ≤ C) :
    ‖heatDuhamel g F a t x‖ ≤ (t - a) * C := by
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioo a t))
    (f := fun s => ∫ y, heatKernel g (t - s) x y * F s y
      ∂riemannianVolumeMeasure (I := I) (M := M) g)
    (C := C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact norm_integral_heatKernel_mul_le g (sub_pos.mpr hs.2) x (hF s hs))
  simpa only [heatDuhamel, Measure.restrict_apply_univ, Measure.real, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hat), mul_comm C] using hb

end DifferentialGeometry.Analysis.HeatEquation
