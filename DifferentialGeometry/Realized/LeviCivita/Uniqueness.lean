import DifferentialGeometry.Realized.LeviCivita.MetricCompatibility
import DifferentialGeometry.Realized.LeviCivita.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Levi-Civita Uniqueness Interface

This file isolates the uniqueness theorem as a precise target.  The hard
Koszul-formula proof will live here; downstream files should consume the
explicit uniqueness predicate until that proof is available.
-/

namespace DifferentialGeometry
namespace Realized
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Uniqueness of the Levi-Civita connection for a fixed metric. -/
def LeviCivitaConnectionUnique
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _),
    IsLeviCivita (I := I) cov g ->
      IsLeviCivita (I := I) cov' g ->
        cov = cov'

/-- Consumer theorem for the uniqueness package. -/
theorem connection_eq_of_leviCivitaConnectionUnique
    {g : SmoothRiemannianMetric I M}
    (huniq : LeviCivitaConnectionUnique (I := I) g)
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g) :
    cov = cov' :=
  huniq cov cov' hcov hcov'

end LeviCivita
end Realized
end DifferentialGeometry
