import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.ManifoldLimitConv
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A time-forcing carrier for chart Sobolev quotients

`wkpQuot_complete` is intentionally a theorem-valued `CompleteSpace` structure,
not a global instance.  This file records the small local-instance bridge needed
to use that result under a Bochner `L^2` space and under Banach's fixed-point
theorem.

This is only functional-analytic plumbing.  In particular it does not define a
pointwise representative of `WkpChartQuot`, a Nemytskii operator on the
quotient, or a parabolic maximal-regularity solution operator.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Square-integrable time-dependent values in the separated chart Sobolev
space.  The spatial exponent `p` and the time exponent `2` are independent. -/
abbrev WkpTimeL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (T : ℝ) : Type _ :=
  MeasureTheory.Lp
    (WkpChartQuot (I := I) (M := M) g k p hp)
    2
    (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T)

/-- The theorem-valued completeness of `WkpChartQuot` can be installed locally
to make its time-`L²` forcing carrier complete. -/
theorem wkpTime_complete
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (T : ℝ) :
    CompleteSpace (WkpTimeL2 (I := I) (M := M) g k p hp_one T) := by
  letI := wkpQuot_complete (I := I) (M := M) g k hp_one hp_top
  infer_instance

/-- Every contraction on the chart-Sobolev time-forcing carrier has a unique
fixed point.  The `CompleteSpace` input is supplied locally by
`wkpTime_complete`; no global instance is registered. -/
theorem wkpTime_fixed
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (T : ℝ) {K : ℝ≥0}
    {Phi : WkpTimeL2 (I := I) (M := M) g k p hp_one T →
      WkpTimeL2 (I := I) (M := M) g k p hp_one T}
    (hPhi : ContractingWith K Phi) :
    ∃ x, Function.IsFixedPt Phi x ∧
      ∀ y, Function.IsFixedPt Phi y → y = x := by
  letI := wkpTime_complete (I := I) (M := M) g k hp_one hp_top T
  refine ⟨ContractingWith.fixedPoint Phi hPhi,
    ContractingWith.fixedPoint_isFixedPt hPhi, ?_⟩
  intro y hy
  exact ContractingWith.fixedPoint_unique hPhi hy

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
