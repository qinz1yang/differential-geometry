import DifferentialGeometry.Topology.Simplex.Coordinates
import DifferentialGeometry.Topology.Simplex.Face
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

namespace Convexity.StdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] {n : ℕ}

theorem map_succAbove_map_succAbove (i : Fin (n + 2)) (j : Fin (n + 1))
    (p : coordinateSet S (Fin n)) :
    coordinateMap i.succAbove (coordinateMap j.succAbove p) =
      coordinateMap (i.succAbove j).succAbove (coordinateMap (j.predAbove i).succAbove p) := by
  rw [coordinateMap_comp_apply, coordinateMap_comp_apply]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

end Convexity.StdSimplex

open Convexity.StdSimplex (coordinateSet coordinateMap)

namespace DifferentialGeometry.Simplex

variable {n : ℕ}

theorem faceInsert_faceInsert_val (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : coordinateSet ℝ (Fin (n + 1))) :
    (faceInsert i (faceInsert j p).val).val =
      (faceInsert (i.succAbove j) (faceInsert (j.predAbove i) p).val).val :=
  Convexity.StdSimplex.map_succAbove_map_succAbove i j p

theorem boundary_face_point_eq (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : coordinateSet ℝ (Fin (n + 1))) :
    (⟨coordinateMap i.succAbove (coordinateMap j.succAbove p),
      ⟨i, map_succAbove_apply_pivot i _⟩⟩ : boundary (Fin (n + 3))) =
    ⟨coordinateMap (i.succAbove j).succAbove
      (coordinateMap (j.predAbove i).succAbove p),
      ⟨i.succAbove j, map_succAbove_apply_pivot (i.succAbove j) _⟩⟩ :=
  Subtype.ext (Convexity.StdSimplex.map_succAbove_map_succAbove i j p)

theorem face_restriction_compatibility {X : Type*}
    (f : Fin (n + 3) → coordinateSet ℝ (Fin (n + 2)) → X)
    (g : boundary (Fin (n + 3)) → X)
    (hf : ∀ (i : Fin (n + 3)) (q : coordinateSet ℝ (Fin (n + 2))),
      f i q = g ⟨coordinateMap i.succAbove q, ⟨i, map_succAbove_apply_pivot i q⟩⟩)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (p : coordinateSet ℝ (Fin (n + 1))) :
    f i (coordinateMap j.succAbove p) =
      f (i.succAbove j) (coordinateMap (j.predAbove i).succAbove p) := by
  rw [hf, hf, boundary_face_point_eq]

end DifferentialGeometry.Simplex
