import DifferentialGeometry.Topology.Simplex.Cone
import DifferentialGeometry.Topology.Simplex.VertexContraction

noncomputable section

namespace DifferentialGeometry.Simplex

theorem vertexContraction_zero_face_eq_simplexCone (n : ℕ) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    vertexContraction (0 : Fin (n + 2)) (t, stdSimplex.map (0 : Fin (n + 2)).succAbove p) =
      simplexCone n (t, p) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [vertexContraction_apply, simplexCone_apply_zero, map_succAbove_apply_pivot]
    simp
  · rw [vertexContraction_apply, simplexCone_apply_succ]
    have h := map_succAbove_apply_image (0 : Fin (n + 2)) p j
    simp only [Fin.succAbove_zero] at h ⊢
    rw [h]
    simp [eq_comm]

theorem vertexContraction_zero_face_succ (n : ℕ) (i : Fin (n + 1)) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    vertexContraction (0 : Fin (n + 2)) (t, stdSimplex.map i.succ.succAbove p) =
      stdSimplex.map i.succ.succAbove (vertexContraction (0 : Fin (n + 1)) (t, p)) := by
  simpa only [Fin.succ_succAbove_zero] using
    vertexContraction_map i.succ.succAbove (0 : Fin (n + 1)) t p

end DifferentialGeometry.Simplex
