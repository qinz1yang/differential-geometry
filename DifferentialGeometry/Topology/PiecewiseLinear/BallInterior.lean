import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPLHomeomorphOn.image_openSimplex_stdVertices {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    f '' openSimplex (stdVertices n) = P \ f '' stdSimplexBoundary (n + 1) := by
  rw [openSimplex_eq_sdiff_simplexBoundary (stdVertices n) (stdVertices_affineIndependent n),
    convexHull_stdVertices, simplexBoundary_stdVertices_space,
    hf.bijOn.injOn.image_sdiff_subset (fun _ hx => hx.1), hf.image_eq]

theorem IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    closure (P \ f '' stdSimplexBoundary (n + 1)) = P := by
  rw [← hf.image_openSimplex_stdVertices,
    ← hf.image_closure (isCompact_stdSimplex ℝ _) openSimplex_stdVertices_subset_stdSimplex]
  have hclosure : closure (openSimplex (stdVertices n)) = stdSimplex ℝ (Fin (n + 2)) := by
    apply Subset.antisymm
      (closure_minimal openSimplex_stdVertices_subset_stdSimplex (isClosed_stdSimplex ℝ _))
    intro x hx
    exact convexHull_subset_closure_openSimplex
      (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (two_le_card_stdVertices n)))
      (by rwa [convexHull_stdVertices])
  rw [hclosure, hf.image_eq]

theorem IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    IsConnected (P \ f '' stdSimplexBoundary (n + 1)) := by
  rw [← hf.image_openSimplex_stdVertices]
  exact ((convex_openSimplex (stdVertices n)).isConnected
    ⟨stdCenter n, stdCenter_mem_openSimplex n⟩).image f
      (hf.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)

end DifferentialGeometry.Topology.PiecewiseLinear
