import DifferentialGeometry.Topology.Simplex.VertexMap
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]


def reindexHomeomorph (e : ι ≃ κ) : stdSimplex ℝ ι ≃ₜ stdSimplex ℝ κ where
  toFun x := ⟨fun j ↦ x.val (e.symm j), ⟨fun j ↦ x.prop.1 (e.symm j),
    (e.symm.sum_comp x.val).trans x.prop.2⟩⟩
  invFun y := ⟨fun i ↦ y.val (e i), ⟨fun i ↦ y.prop.1 (e i),
    (e.sum_comp y.val).trans y.prop.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.val (e.apply_symm_apply j)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun j ↦ (continuous_apply (e.symm j)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i ↦ (continuous_apply (e i)).comp continuous_subtype_val)


@[simp]
theorem reindexHomeomorph_apply (e : ι ≃ κ) (x : stdSimplex ℝ ι) (j : κ) :
    (reindexHomeomorph e x).val j = x.val (e.symm j) := rfl


@[simp]
theorem reindexHomeomorph_symm_apply (e : ι ≃ κ) (y : stdSimplex ℝ κ) (i : ι) :
    ((reindexHomeomorph e).symm y).val i = y.val (e i) := rfl


theorem reindexHomeomorph_mem_boundary (e : ι ≃ κ) (x : stdSimplex ℝ ι) :
    reindexHomeomorph e x ∈ boundary κ ↔ x ∈ boundary ι := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, hj⟩
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa only [reindexHomeomorph_apply, e.symm_apply_apply] using hi⟩


theorem vertexMap_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ι ≃ κ) (v : κ → E) (x : stdSimplex ℝ ι) :
    vertexMap v (reindexHomeomorph e x) = vertexMap (v ∘ e) x := by
  change (∑ j, x.val (e.symm j) • v j) = ∑ i, x.val i • v (e i)
  simpa only [e.symm_apply_apply] using
    (e.sum_comp (fun j ↦ x.val (e.symm j) • v j)).symm

end DifferentialGeometry.Simplex
