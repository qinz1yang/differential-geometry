import DifferentialGeometry.Topology.Homology.SphereRank



noncomputable section

open Metric Module

universe u

namespace DifferentialGeometry.Topology





def integralSphereTopHomologyEquiv (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 2) :
    integralSingularHomology (n + 1) (sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  induction n generalizing E with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      letI := unitSphere_pathConnected_of_finrank (E := E) (by omega)
      exact (integralSphereHomologyOneReducedEquiv v).trans
        (integralZeroSphereReducedEquiv (unitSpherePoleHyperplane_finrank 1 hd (-v)))
  | succ n ih =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      exact (integralSphereHomologyShiftEquiv n v).trans
        (ih (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
          (unitSpherePoleHyperplane_finrank (n + 2) (by omega) (-v)))

end DifferentialGeometry.Topology
