import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SolutionOn

def parabolicClosedWindow {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ) :
    SolutionOn (I := I) (M := M) (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ)) where
  base := parabolicFamily S.base T Q hQ

@[simp] theorem parabolicClosedWindow_metric {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ)
    (s : ℝ) :
    (S.parabolicClosedWindow T Q θ hQ hθ).base.metric s =
      scaleMetric Q hQ (S.base.metric (T + s / Q)) := rfl

theorem parabolicClosedWindow_metric_zero {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 ≤ θ) :
    (S.parabolicClosedWindow T Q θ hQ hθ).base.metric 0 =
      scaleMetric Q hQ (S.base.metric T) := by
  simp only [parabolicClosedWindow_metric, zero_div, add_zero]

end SolutionOn

variable [FiniteDimensional ℝ E] [T2Space M]

theorem isSolutionOn_parabolicClosedWindow {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T Q θ : ℝ} (hQ : 0 < Q) (hθ : 0 ≤ θ)
    (hcarrier : Icc (T - θ / Q) T ⊆ D.carrier)
    (hregular : Ioo (T - θ / Q) T ⊆ D.regular) :
    IsSolutionOn (S.parabolicClosedWindow T Q θ hQ hθ) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hT : T ∈ D.carrier := hcarrier ⟨sub_le_self T (div_nonneg hθ hQ.le), le_rfl⟩
  apply isSolutionOn_timeRestrict (parabolicSolution_isSolutionOn S hS T Q hQ hT)
  · intro s hs
    apply hcarrier
    change T - θ / Q ≤ T + s / Q ∧ T + s / Q ≤ T
    have hlo := div_le_div_of_nonneg_right hs.1 hQ.le
    have hhi := div_le_div_of_nonneg_right hs.2 hQ.le
    simp only [neg_div, zero_div] at hlo hhi
    constructor <;> linarith
  · intro s hs
    apply hregular
    change T - θ / Q < T + s / Q ∧ T + s / Q < T
    have hlo := div_lt_div_of_pos_right hs.1 hQ
    have hhi := div_lt_div_of_pos_right hs.2 hQ
    simp only [neg_div, zero_div] at hlo hhi
    constructor <;> linarith

end DifferentialGeometry.PDE.RicciFlow
