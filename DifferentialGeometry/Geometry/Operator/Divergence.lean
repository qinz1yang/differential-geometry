import DifferentialGeometry.Bundle.ClmSectionSmooth
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.Operators

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem divergence_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (divergence (I := I) cov X) := by
  apply contMDiff_linearMap_trace (F := E) (V := TangentSpace I)
  rw [← contMDiffOn_univ]
  exact hcov.contMDiff.contMDiff X.contMDiff.contMDiffOn

theorem leviCivita_divergence_contMDiff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞
      (divergence (I := I)
        (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) X) :=
  divergence_contMDiff
    (Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
    (Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      (I := I) g) X

end Operator
end Geometry
end DifferentialGeometry
