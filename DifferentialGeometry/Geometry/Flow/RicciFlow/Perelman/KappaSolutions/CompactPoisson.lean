import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem existsUnique_meanZero_smooth_poisson
    (g : SmoothRiemannianMetric I M) (q : C^∞⟮I, M; ℝ⟯)
    (hq : (∫ x, q x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0) :
    ∃! f : C^∞⟮I, M; ℝ⟯,
      (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
        ∀ x : M, ΔG (I := I) g f x = q x := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
