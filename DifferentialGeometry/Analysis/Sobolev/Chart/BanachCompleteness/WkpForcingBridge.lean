import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.ManifoldLimitConv
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
abbrev WkpTimeL2
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (T : ℝ) : Type _ :=
  MeasureTheory.Lp
    (WkpChartQuot (I := I) (M := M) g k p hp)
    2
    (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure T)

theorem wkpTime_complete
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (T : ℝ) :
    CompleteSpace (WkpTimeL2 (I := I) (M := M) g k p hp_one T) := by
  letI := wkpQuot_complete (I := I) (M := M) g k hp_one hp_top
  infer_instance

theorem wkpTime_fixed
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (T : ℝ) {K : NNReal}
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
