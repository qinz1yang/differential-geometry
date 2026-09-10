import DifferentialGeometry.Topology.VectorField.MixedPoincareHopf
import DifferentialGeometry.Topology.Homology.RelativeBoundaryDuality

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.VectorField

theorem interiorIndexSum_eq_relativeEulerChar_of_mixed
    {n : ℕ}
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x)
    (hVI : ∀ x, V x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x)
    (B : Set M) (hB : B ⊆ (𝓡∂ (n + 1)).boundary M)
    (hBclopen : IsClopen (((↑) : BoundaryManifold (𝓡∂ (n + 1)) M → M) ⁻¹' B))
    (hin : ∀ p ∈ B, 0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (hout : ∀ p, (𝓡∂ (n + 1)).IsBoundaryPoint p → p ∉ B → (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p) < 0)
    (K : Type) [Field K] :
    interiorIndexSum (𝓡∂ (n + 1)) V hVf hVi hVI =
      Poincare.Homology.relativeEulerChar (TopCat.of M) B K := by
  let I := 𝓡∂ (n + 1)
  let A : Set (BoundaryManifold I M) := ((↑) : BoundaryManifold I M → M) ⁻¹' B
  have hr := mixedPoincareHopf V hV hVf hVi hVI A hBclopen
    (fun p hp => hin p.val hp) (fun p hp => hout p.val p.property hp) K
  have hrange : B ⊆ range ((↑) : BoundaryManifold I M → M) :=
    (BoundaryManifold.range_coe_eq_boundary (I := I) (M := M)).symm ▸ hB
  let e := (show Topology.IsEmbedding ((↑) : BoundaryManifold I M → M) from
    Topology.IsEmbedding.subtypeVal).homeomorphOfSubsetRange hrange
  have he : Poincare.Homology.eulerChar K (TopCat.of A) =
      Poincare.Homology.eulerChar K (TopCat.of B) :=
    Poincare.Homology.eulerChar_eq_of_homeomorph K e
  rw [he] at hr
  exact hr.trans (Poincare.Homology.relativeEulerChar_eq_sub (TopCat.of M) B K
    (Poincare.Homology.finiteHomologyType_of_isClopen_boundary_subset I K B hB hBclopen)
    (Poincare.Homology.finiteHomologyType_of_compact_manifold_withBoundary (n := n + 1) (M := M) K)).symm

end Poincare.VectorField
