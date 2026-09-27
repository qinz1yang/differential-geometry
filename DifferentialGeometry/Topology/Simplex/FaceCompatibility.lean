import DifferentialGeometry.Topology.Simplex.Face
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] {n : ℕ}

theorem map_succAbove_map_succAbove (i : Fin (n + 2)) (j : Fin (n + 1))
    (p : stdSimplex S (Fin n)) :
    map i.succAbove (map j.succAbove p) =
      map (i.succAbove j).succAbove (map (j.predAbove i).succAbove p) := by
  rw [map_comp_apply, map_comp_apply]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

end stdSimplex

namespace DifferentialGeometry.Simplex

variable {n : ℕ}

theorem faceInsert_faceInsert_val (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (faceInsert i (faceInsert j p).val).val =
      (faceInsert (i.succAbove j) (faceInsert (j.predAbove i) p).val).val :=
  stdSimplex.map_succAbove_map_succAbove i j p

theorem boundary_face_point_eq (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (⟨stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p),
      ⟨i, map_succAbove_apply_pivot i _⟩⟩ : boundary (Fin (n + 3))) =
    ⟨stdSimplex.map (i.succAbove j).succAbove
      (stdSimplex.map (j.predAbove i).succAbove p),
      ⟨i.succAbove j, map_succAbove_apply_pivot (i.succAbove j) _⟩⟩ :=
  Subtype.ext (stdSimplex.map_succAbove_map_succAbove i j p)

theorem face_restriction_compatibility {X : Type*}
    (f : Fin (n + 3) → stdSimplex ℝ (Fin (n + 2)) → X)
    (g : boundary (Fin (n + 3)) → X)
    (hf : ∀ (i : Fin (n + 3)) (q : stdSimplex ℝ (Fin (n + 2))),
      f i q = g ⟨stdSimplex.map i.succAbove q, ⟨i, map_succAbove_apply_pivot i q⟩⟩)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (p : stdSimplex ℝ (Fin (n + 1))) :
    f i (stdSimplex.map j.succAbove p) =
      f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
  rw [hf, hf, boundary_face_point_eq]

end DifferentialGeometry.Simplex
