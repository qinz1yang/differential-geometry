import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

def isFiniteActionLCurve (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (gamma : ℝ → M) : Prop :=
  (let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace;
    AbsolutelyContinuousOnInterval gamma a b) ∧
    (∀ᵐ s ∂volume.restrict (Icc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s) ∧
    IntervalIntegrable (lDensity S T gamma) volume a b ∧
    ∀ s ∈ Icc a b, (gamma s, T - s) ∈ Ω

theorem isFiniteActionLCurve.absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (gamma : ℝ → M)
    (hgamma : isFiniteActionLCurve S T Ω a b gamma) :
    let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
    AbsolutelyContinuousOnInterval gamma a b := hgamma.1

theorem isFiniteActionLCurve_congr_region
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    {Ω Ω' : Set (M × ℝ)} {a b : ℝ} (gamma : ℝ → M)
    (hΩ : ∀ r ∈ Icc a b, (gamma r, T - r) ∈ Ω ↔ (gamma r, T - r) ∈ Ω') :
    isFiniteActionLCurve S T Ω a b gamma ↔ isFiniteActionLCurve S T Ω' a b gamma := by
  constructor
  · rintro ⟨hac, hdiff, hint, hgraph⟩
    exact ⟨hac, hdiff, hint, fun r hr => (hΩ r hr).mp (hgraph r hr)⟩
  · rintro ⟨hac, hdiff, hint, hgraph⟩
    exact ⟨hac, hdiff, hint, fun r hr => (hΩ r hr).mpr (hgraph r hr)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
