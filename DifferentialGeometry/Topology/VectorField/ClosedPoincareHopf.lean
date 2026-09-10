import DifferentialGeometry.Topology.VectorField.ClosedMorseReference
import DifferentialGeometry.Topology.VectorField.IndexComparison

set_option autoImplicit false
noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem interiorIndexSum_eq_eulerChar_of_boundaryless
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hfinite : {x | V x = 0}.Finite)
    (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (K : Type) [Field K] :
    interiorIndexSum I V hfinite hisolated hinterior =
      Poincare.Homology.eulerChar K (TopCat.of M) := by
  obtain ⟨W, hW, hWf, hWi, hWI, hχ⟩ :=
    exists_closed_vectorField_interiorIndexSum_eq_eulerChar I (M := M)
  exact (interiorIndexSum_eq_of_boundary_germ I V W hV hW hfinite hisolated hinterior
    hWf hWi hWI (fun _ hx => (hx BoundarylessManifold.isInteriorPoint).elim)).trans (hχ K)

end Poincare.VectorField
