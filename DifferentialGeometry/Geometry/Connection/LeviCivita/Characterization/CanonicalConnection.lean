import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Torsion

namespace DifferentialGeometry
namespace Geometry
namespace Connection

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivitaConnectionOfMetric_apply_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (leviCivitaConnectionOfMetric (I := I) g).toFun σ x v
      = (LeviCivita (I := I) g).toFun σ x v := by
  refine LeviCivita_unique g (leviCivitaConnectionOfMetric (I := I) g) ?_ ?_ hσ v
  · funext y
    exact (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g).2 y
  · exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g

end Connection
end Geometry
end DifferentialGeometry
