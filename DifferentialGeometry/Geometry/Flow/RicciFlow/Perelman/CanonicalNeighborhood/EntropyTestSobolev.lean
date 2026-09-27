import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.Density.FirstOrder

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open MeasureTheory DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]


theorem EntropyTest.memW1pIntrinsicLp {g : SmoothRiemannianMetric I M} (w : EntropyTest g) :
    MemW1pIntrinsicLp g 2 w.value :=
  ⟨w.value_memLp, w.gradient, w.weak_gradient, w.gradient_memLp⟩


theorem EntropyTest.entropy_integrable [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} (w : EntropyTest g)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    Integrable (fun x => w.value x ^ 2 * Real.log (w.value x ^ 2))
      (riemannianVolumeMeasure I M g) :=
  w.memW1pIntrinsicLp.integrable_sq_mul_log_sq hdim


theorem EntropyTest.exists_smooth_chart_approx [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} (w : EntropyTest g)
    (hdim : 2 ≤ Module.finrank ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v ∧
      Chart.wkpNormChart (I := I) 1 2 (fun x => w.value x - v x) ≤ ENNReal.ofReal ε := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  exact Chart.contMDiff_dense_in_WkpChart (by norm_num) (by norm_num)
    (w.memW1pIntrinsicLp.memWkpChart (by norm_num)) hε

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
