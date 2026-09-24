import DifferentialGeometry.Topology.Simplex.BoundaryGluing
import DifferentialGeometry.Topology.Simplex.VertexContraction
import Mathlib.Topology.Homotopy.Contractible

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

theorem boundarySphereDesc_nullhomotopic_of_extension
    (g : Fin 4 → C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      g i (stdSimplex.map j.succAbove p) =
        g (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ i p, F (stdSimplex.map i.succAbove p) = g i p) :
    (boundarySphereDesc g hg).Nullhomotopic := by
  let e := stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  let j : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      stdSimplex ℝ (Fin 4)) :=
    ⟨fun z => (e.symm z).val, continuous_subtype_val.comp e.symm.continuous⟩
  have heq : F.comp j = boundarySphereDesc g hg := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨q, rfl⟩ := e.surjective z
    obtain ⟨i, hi⟩ := q.property
    let p := faceDelete i ⟨q.val, hi⟩
    have hq : q = ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩ :=
      Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨q.val, hi⟩)).symm
    rw [hq, boundarySphereDesc_face]
    change F ((e.symm (e _)).val) = _
    rw [Homeomorph.symm_apply_apply]
    exact hF i p
  let K : ContinuousMap.Homotopy F (ContinuousMap.const _ (F (stdSimplex.vertex (0 : Fin 4)))) :=
    { toContinuousMap := F.comp (vertexContraction (0 : Fin 4))
      map_zero_left := fun p => congrArg F (vertexContraction_zero (0 : Fin 4) p)
      map_one_left := fun p => congrArg F (vertexContraction_one (0 : Fin 4) p) }
  rw [← heq]
  exact (show F.Nullhomotopic from ⟨_, ⟨K⟩⟩).comp_left j

end DifferentialGeometry.Simplex
