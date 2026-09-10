import DifferentialGeometry.Topology.VectorField.IndexSum
import DifferentialGeometry.Topology.VectorField.MorseReferenceField

set_option autoImplicit false
noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_outward_vectorField_interiorIndexSum_eq_eulerChar :
    ∃ V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun x => (⟨x,V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      (∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0) ∧
      ∃ hfinite : {x | V x = 0}.Finite,
      ∃ hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x,
      ∃ hinterior : ∀ x, V x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x,
        ∀ (K : Type) [Field K], Poincare.Homology.finiteHomologyType K (TopCat.of M) ∧
          interiorIndexSum (𝓡∂ (n + 1)) V hfinite hisolated hinterior =
            Poincare.Homology.eulerChar K (TopCat.of M) := by
  obtain ⟨V,hV,_,hout,hfinite,hinterior,hisolated,_,hχ⟩ :=
    exists_outward_vectorField_indexSum_eq_eulerChar (n := n) (M := M)
  exact ⟨V,hV,hout,hfinite,hisolated,hinterior,hχ⟩

end Poincare.VectorField
