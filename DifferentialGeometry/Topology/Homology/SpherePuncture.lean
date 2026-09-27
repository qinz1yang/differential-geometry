import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture

noncomputable section

open ContinuousMap Set Metric
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integralSingularHomology_subsingleton_of_punctured_sphere (n : ℕ) (hn : n ≠ 0)
    (v : sphere (0 : E) 1) :
    Subsingleton (integralSingularHomology n ({v}ᶜ : Set (sphere (0 : E) 1))) := by
  let := spherePuncture_contractible v
  exact integralSingularHomology_subsingleton_of_contractible n hn _

end DifferentialGeometry.Topology
