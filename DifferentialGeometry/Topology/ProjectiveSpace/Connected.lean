import DifferentialGeometry.Topology.ProjectiveSpace.SphereQuotient
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.ProjectiveSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem pathConnectedSpace_of_one_lt_rank (h : 1 < Module.rank ℝ E) :
    PathConnectedSpace (Projectivization ℝ E) := by
  let : PathConnectedSpace (Metric.sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h 0 (by norm_num))
  exact sphereProjection_surjective.pathConnectedSpace continuous_sphereProjection


instance pathConnectedSpace_euclidean (n : ℕ) :
    PathConnectedSpace (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 2)))) := by
  apply pathConnectedSpace_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact_mod_cast (show 1 < n + 2 by omega)

end DifferentialGeometry.ProjectiveSpace
