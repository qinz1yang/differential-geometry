import DifferentialGeometry.Topology.Simplex.Coordinates
import DifferentialGeometry.Topology.Simplex.CubeParametrization
import DifferentialGeometry.Topology.Simplex.VertexContraction

noncomputable section

open Convexity.StdSimplex

namespace DifferentialGeometry.Simplex

theorem vertexContraction_zero_face_zero (t : unitInterval)
    (p : coordinateSet ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, coordinateMap (0 : Fin 3).succAbove p) =
      triangleJoin (unitInterval.symm t, coordinateHomeomorphI p) := by
  apply Subtype.ext
  funext i
  rw [vertexContraction_apply]
  fin_cases i
  · have h := map_succAbove_apply_pivot (0 : Fin 3) p
    change (1 - (t : ℝ)) * (coordinateMap (0 : Fin 3).succAbove p).val 0 +
      (t : ℝ) * 1 = 1 - (1 - (t : ℝ))
    rw [h]
    ring
  · have h := map_succAbove_apply_image (0 : Fin 3) p (0 : Fin 2)
    change (coordinateMap (0 : Fin 3).succAbove p).val 1 = p.val 0 at h
    change (1 - (t : ℝ)) * (coordinateMap (0 : Fin 3).succAbove p).val 1 +
      (t : ℝ) * 0 = (1 - (t : ℝ)) * (1 - p.val 1)
    rw [h]
    have hp := coordinate_add_eq_one p
    change p.val 0 + p.val 1 = 1 at hp
    have hp0 : p.val 0 = 1 - p.val 1 := by linarith
    rw [hp0]
    ring
  · have h := map_succAbove_apply_image (0 : Fin 3) p (1 : Fin 2)
    change (coordinateMap (0 : Fin 3).succAbove p).val 2 = p.val 1 at h
    change (1 - (t : ℝ)) * (coordinateMap (0 : Fin 3).succAbove p).val 2 +
      (t : ℝ) * 0 = (1 - (t : ℝ)) * p.val 1
    rw [h]
    ring

theorem vertexContraction_zero_face_one (t : unitInterval)
    (p : coordinateSet ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, coordinateMap (1 : Fin 3).succAbove p) =
      coordinateMap (1 : Fin 3).succAbove (vertexContraction (0 : Fin 2) (t, p)) := by
  simpa using vertexContraction_map (1 : Fin 3).succAbove (0 : Fin 2) t p

theorem vertexContraction_zero_face_two (t : unitInterval)
    (p : coordinateSet ℝ (Fin 2)) :
    vertexContraction (0 : Fin 3) (t, coordinateMap (2 : Fin 3).succAbove p) =
      coordinateMap (2 : Fin 3).succAbove (vertexContraction (0 : Fin 2) (t, p)) := by
  simpa using vertexContraction_map (2 : Fin 3).succAbove (0 : Fin 2) t p

end DifferentialGeometry.Simplex
