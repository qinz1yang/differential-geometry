import DifferentialGeometry.Topology.Simplex.Face
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Simplex.FaceCompatibility

noncomputable section

namespace DifferentialGeometry.Simplex

open Set

def tetrahedronOneSkeleton : Set (stdSimplex ℝ (Fin 4)) :=
  {p | ∃ i j : Fin 4, i ≠ j ∧ p.val i = 0 ∧ p.val j = 0}

theorem map_succAbove_mem_tetrahedronOneSkeleton (i : Fin 4) (p : boundary (Fin 3)) :
    stdSimplex.map i.succAbove p.val ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := p.property
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    map_succAbove_apply_pivot i p.val, ?_⟩
  rw [map_succAbove_apply_image]
  exact hj

def faceBoundaryIntoTetrahedronOneSkeleton (i : Fin 4) : C(boundary (Fin 3), tetrahedronOneSkeleton) :=
  ⟨fun p => ⟨stdSimplex.map i.succAbove p.val, map_succAbove_mem_tetrahedronOneSkeleton i p⟩,
    ((stdSimplex.continuous_map i.succAbove).comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem faceBoundaryIntoTetrahedronOneSkeleton_val (i : Fin 4) (p : boundary (Fin 3)) :
    (faceBoundaryIntoTetrahedronOneSkeleton i p).val = stdSimplex.map i.succAbove p.val := rfl

theorem faceBoundaryIntoTetrahedronOneSkeleton_edge (i : Fin 4) (j : Fin 3)
    (p : stdSimplex ℝ (Fin 2)) :
    faceBoundaryIntoTetrahedronOneSkeleton i
        ⟨stdSimplex.map j.succAbove p, ⟨j, map_succAbove_apply_pivot j p⟩⟩ =
      faceBoundaryIntoTetrahedronOneSkeleton (i.succAbove j)
        ⟨stdSimplex.map (j.predAbove i).succAbove p,
          ⟨j.predAbove i, map_succAbove_apply_pivot (j.predAbove i) p⟩⟩ :=
  Subtype.ext (stdSimplex.map_succAbove_map_succAbove i j p)

theorem tetrahedronOneSkeleton_restriction_compatibility {X : Type*}
    (f : Fin 4 → stdSimplex ℝ (Fin 3) → X) (g : tetrahedronOneSkeleton → X)
    (hf : ∀ (i : Fin 4) (q : boundary (Fin 3)),
      f i q.val = g (faceBoundaryIntoTetrahedronOneSkeleton i q))
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    f i (stdSimplex.map j.succAbove p) =
      f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
  have hl := hf i ⟨stdSimplex.map j.succAbove p, ⟨j, map_succAbove_apply_pivot j p⟩⟩
  have hr := hf (i.succAbove j)
    ⟨stdSimplex.map (j.predAbove i).succAbove p,
      ⟨j.predAbove i, map_succAbove_apply_pivot (j.predAbove i) p⟩⟩
  exact hl.trans ((congrArg g (faceBoundaryIntoTetrahedronOneSkeleton_edge i j p)).trans hr.symm)

theorem exists_faceBoundaryIntoTetrahedronOneSkeleton_eq (p : tetrahedronOneSkeleton) :
    ∃ (i : Fin 4) (q : boundary (Fin 3)), faceBoundaryIntoTetrahedronOneSkeleton i q = p := by
  obtain ⟨i, j, hij, hi, hj⟩ := p.property
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  let q := faceDelete i ⟨p.val, hi⟩
  have hq : q ∈ boundary (Fin 3) := ⟨j, hj⟩
  refine ⟨i, ⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  change stdSimplex.map i.succAbove q = p.val
  exact congrArg (fun z : face i => z.val) (faceInsert_faceDelete i ⟨p.val, hi⟩)

theorem tetrahedronOneSkeleton_subset_boundary : tetrahedronOneSkeleton ⊆ boundary (Fin 4) := by
  rintro p ⟨i, j, hij, hi, hj⟩
  exact ⟨i, hi⟩

end DifferentialGeometry.Simplex
