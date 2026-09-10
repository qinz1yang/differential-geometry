import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.HasGroupoid

set_option autoImplicit false
noncomputable section
open Set
namespace Poincare.Manifold

variable {H H' M : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]


@[instance_reducible]
def chartedSpaceTransHomeomorph (e : H ≃ₜ H') : ChartedSpace H' M :=
  let _ : ChartedSpace H' H := e.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp H' H M


theorem chartAt_transHomeomorph (e : H ≃ₜ H') (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) e
    chartAt H' x = (chartAt H x).trans e.toOpenPartialHomeomorph := rfl

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
  (e : H ≃ₜ H') (L : E ≃ₜ F)
  (hcompat : ∀ y, J (e y) = L (I y))

include hcompat in
theorem range_model_transHomeomorph : range J = L '' range I := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨I (e.symm z), mem_range_self _, ?_⟩
    rw [← hcompat, e.apply_symm_apply]
  · rintro ⟨z,⟨w,rfl⟩,rfl⟩
    rw [← hcompat]
    exact mem_range_self _

include hcompat in
theorem isInteriorPoint_transHomeomorph_iff (x : M) :
    @ModelWithCorners.IsInteriorPoint 𝕜 _ F _ _ H' _ J M _
      (chartedSpaceTransHomeomorph (M := M) e) x ↔ I.IsInteriorPoint x := by
  change J (e (chartAt H x x)) ∈ interior (range J) ↔ I (chartAt H x x) ∈ interior (range I)
  rw [hcompat, range_model_transHomeomorph I J e L hcompat, ← L.image_interior]
  exact L.injective.mem_set_image

include hcompat in
theorem boundary_transHomeomorph :
    @ModelWithCorners.boundary 𝕜 _ F _ _ H' _ J M _
      (chartedSpaceTransHomeomorph (M := M) e) = I.boundary M := by
  let _ := chartedSpaceTransHomeomorph (M := M) e
  ext x
  simp only [ModelWithCorners.boundary, mem_ofPred_eq]
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_transHomeomorph_iff I J e L hcompat]

end Poincare.Manifold
