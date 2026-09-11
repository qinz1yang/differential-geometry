import DifferentialGeometry.Topology.Homology.SpherePuncture
import DifferentialGeometry.Topology.Homology.ContractibleCoverOne



noncomputable section

open CategoryTheory ContinuousMap Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



def spherePoleIntersectionHomotopyEquiv (v : sphere (0 : E) 1) :
    subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ ≃ₕ
      sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1 :=
  (sphereDoublePunctureHomeomorph v).toHomotopyEquiv.trans
    (puncturedSpaceSphereHomotopyEquiv _)




def integralSphereHomologyShiftEquiv (n : ℕ) (v : sphere (0 : E) 1) :
    integralSingularHomology (n + 2) (sphere (0 : E) 1) ≃ₗ[ℤ]
      integralSingularHomology (n + 1) (sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact (integralHomologyContractibleCoverEquiv n {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)).trans
      (integralSingularHomologyHomotopyEquiv (n + 1) (spherePoleIntersectionHomotopyEquiv v))



def integralSphereHomologyOneKernelEquiv [PathConnectedSpace (sphere (0 : E) 1)]
    (v : sphere (0 : E) 1) :
    integralSingularHomology 1 (sphere (0 : E) 1) ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0
        (singularSubspaceInclusion (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ))) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact integralHomologyOneContractibleCoverEquiv {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)

end DifferentialGeometry.Topology
