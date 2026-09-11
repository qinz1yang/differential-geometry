import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem compact_ricciFlow_volumeVariation_on_regular
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s)))
      (∫ x, (deriv (fun s : ℝ => f s x) t - S.scalar t x * f t x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
