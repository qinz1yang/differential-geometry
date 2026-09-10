import DifferentialGeometry.Topology.VectorField.BoundarySplice
import DifferentialGeometry.Topology.VectorField.MorseReferenceIndexSum

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M] in
theorem affineSection_ne_zero_of_outward
    (V W : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    {x : M}
    (hV : (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0)
    (hW : (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (W x) < 0)
    (t : unitInterval) : affineSection (𝓡∂ (n + 1)) V W t x ≠ 0 := by
  let L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
  have hn : (1 - (t : ℝ)) • L (V x) + (t : ℝ) • L (W x) ∈ Iio (0 : ℝ) :=
    convex_Iio 0 hV hW (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  intro hz
  have hh := congrArg L hz
  simp only [affineSection] at hh
  exact (ne_of_lt hn) hh

theorem interiorIndexSum_eq_eulerChar_of_outward
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hout : ∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0)
    (hfinite : {x | V x = 0}.Finite)
    (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x)
    (hinterior : ∀ x, V x = 0 → (𝓡∂ (n + 1)).IsInteriorPoint x)
    (K : Type) [Field K] :
    interiorIndexSum (𝓡∂ (n + 1)) V hfinite hisolated hinterior =
      Poincare.Homology.eulerChar K (TopCat.of M) := by
  obtain ⟨W, hW, hWout, hWfinite, hWisolated, hWinterior, hWχ⟩ :=
    exists_outward_vectorField_interiorIndexSum_eq_eulerChar (n := n) (M := M)
  have he := interiorIndexSum_eq_of_boundary_affine_ne_zero (𝓡∂ (n + 1)) V W hV hW
    hfinite hisolated hinterior hWfinite hWisolated hWinterior (fun x hx t =>
      affineSection_ne_zero_of_outward V W
        (hout x (((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx))
        (hWout x (((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx)) t)
  exact he.trans (hWχ K).2

theorem eulerChar_eq_zero_of_nonzero_outward
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x)
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hout : ∀ x, (𝓡∂ (n + 1)).IsBoundaryPoint x →
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V x) < 0)
    (hn : ∀ x, V x ≠ 0) (K : Type) [Field K] :
    Poincare.Homology.eulerChar K (TopCat.of M) = 0 := by
  have hfinite : {x | V x = 0}.Finite := (Set.eq_empty_of_forall_notMem hn) ▸ finite_empty
  have hi (x : M) (hx : V x = 0) : HasContinuousIsolatedZero (𝓡∂ (n + 1)) V x :=
    (hn x hx).elim
  have hint (x : M) (hx : V x = 0) : (𝓡∂ (n + 1)).IsInteriorPoint x := (hn x hx).elim
  rw [← interiorIndexSum_eq_eulerChar_of_outward V hV hout hfinite hi hint K]
  exact interiorIndexSum_eq_zero_of_nonzero (𝓡∂ (n + 1)) V hfinite hi hint hn

end Poincare.VectorField
