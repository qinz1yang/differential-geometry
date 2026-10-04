import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_isometryEquiv_origin_fixed_boundary_eq
    (ξ η : Metric.sphere (0 : E) 1) :
    ∃ e : Hyperboloid E ≃ᵢ Hyperboloid E,
      e origin = origin ∧ boundaryHomeomorph e ξ = η := by
  let L : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ((ξ : E) - (η : E)))ᗮ.reflection
  have hL : L (ξ : E) = (η : E) :=
    Submodule.reflection_sub ((norm_eq_of_mem_sphere ξ).trans (norm_eq_of_mem_sphere η).symm)
  let A := spatialLorentzEquiv L
  have hA : 0 < (A (1, 0)).1 := by change (0 : ℝ) < 1; norm_num
  let e := lorentzIsometryEquiv A hA
  have he0 : e origin = origin := by
    apply ext
    change L (origin : Hyperboloid E).space = (origin : Hyperboloid E).space
    rw [origin_space, map_zero]
  have hext : lorentzExtension e = A := by
    apply (exists_unique_lorentz_extension e).unique (lorentzExtension_apply _)
    intro x
    rfl
  refine ⟨e, he0, ?_⟩
  apply Subtype.ext
  rw [boundaryHomeomorph_apply_coe, hext]
  change (1 : ℝ)⁻¹ • L (ξ : E) = (η : E)
  rw [inv_one, one_smul, hL]

end DifferentialGeometry.Hyperboloid
