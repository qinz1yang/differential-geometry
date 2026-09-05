import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Noncompact
import DifferentialGeometry.Analysis.Integration.CompactExhaustionIntegral

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Analysis
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem tendsto_forward_unique_cutoff_energy
    (K : CompactExhaustion M)
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hden : Integrable
      (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    Tendsto
      (fun n => ∫ x,
        compactExhaustionCutoff (I := I) (M := M) K n x *
          forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t))
      atTop (𝓝 (forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t)) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have h := tendsto_integral_compactExhaustionCutoff_mul
    (I := I) (M := M) K
    (μ := riemannianMeasureFamily (I := I) (M := M) g₁ t)
    (f := fun x => forwardUniqueDensity (I := I) g₁ g₂ t x) hden
  simpa only [forwardUniqueEnergy] using h

end DifferentialGeometry.PDE.RicciFlow
