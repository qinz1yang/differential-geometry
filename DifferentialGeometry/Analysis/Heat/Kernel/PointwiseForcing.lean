import DifferentialGeometry.Analysis.Heat.Kernel.Semigroup

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_heatKernel_mul_smoothScalar_eq_scalarHeatFlow
    (g : SmoothRiemannianMetric I M) (F : SmoothScalar g)
    {t : ℝ} (ht : 0 < t) (x : M) :
    (∫ y, heatKernel g t x y * F.toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      scalarHeatFlow g (smoothToLp g F) t x := by
  rw [← integral_heatKernel_mul_eq_scalarHeatFlow g (smoothToLp g F) ht x]
  apply integral_congr_ae
  filter_upwards [F.memLp_two.coeFn_toLp] with y hy
  rw [smoothToLp_apply, hy]

end DifferentialGeometry.Analysis.HeatEquation
