import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.BilinearForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem trivializationAt_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
        ⟨x, φ⟩).2 v w
      = φ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x v)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x w) := by
  let : TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E (TangentSpace I) ℝ (fun _ : M ↦ ℝ)
  rw [hom_trivializationAt_apply (RingHom.id ℝ) (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := E →L[ℝ] ℝ) (E₂ := fun y => TangentSpace I y →L[ℝ] ℝ)]
  rw [ContinuousLinearMap.inCoordinates]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have hone (ψ : TangentSpace I x →L[ℝ] ℝ) :
      (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).continuousLinearMapAt
          ℝ x ψ = ψ.comp ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x) := by
    have hx2 : x ∈
        (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
      rw [hom_trivializationAt (RingHom.id ℝ) x₀,
        Bundle.Trivialization.baseSet_continuousLinearMap]
      exact ⟨hx, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x₀⟩
    ext u
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hx2]
    change ((trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀) ⟨x, ψ⟩).2 u = _
    rw [hom_trivializationAt (RingHom.id ℝ) x₀,
      Bundle.Trivialization.continuousLinearMap_apply]
    simp only [ContinuousLinearMap.comp_apply]
    have hxR : x ∈ (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet := Set.mem_univ x
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hxR]
    rfl
  rw [hone]
  simp only [ContinuousLinearMap.comp_apply]

end DifferentialGeometry.BilinearForm
