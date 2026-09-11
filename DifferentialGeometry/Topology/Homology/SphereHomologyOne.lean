import DifferentialGeometry.Topology.Homology.SphereHomologyShift
import DifferentialGeometry.Topology.Homology.ReducedZero
import Mathlib.Analysis.Normed.Module.Connected



noncomputable section

open ContinuousMap Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



def integralSphereHomologyOneReducedEquiv [PathConnectedSpace (sphere (0 : E) 1)]
    (v : sphere (0 : E) 1) :
    integralSingularHomology 1 (sphere (0 : E) 1) ≃ₗ[ℤ]
      integralReducedHomologyZero (sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible (-v)
  exact ((integralSphereHomologyOneKernelEquiv v).trans
    (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion
      (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ)))).trans
        (integralReducedZeroHomotopyEquiv (spherePoleIntersectionHomotopyEquiv v))



theorem unitSphere_pathConnected_of_rank (h : 1 < Module.rank ℝ E) :
    PathConnectedSpace (sphere (0 : E) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h 0 (by norm_num))

end DifferentialGeometry.Topology
