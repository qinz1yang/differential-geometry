import DifferentialGeometry.Topology.PiecewiseLinear.SimplexSlabInterior
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import DifferentialGeometry.Topology.RegularClosed

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem closure_sdiff_slab_eq_subcomplexGeneratedBy_inter
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hreg : closure (interior K.space) = K.space) {T : Finset E} (hT : T ∈ K.faces)
    (hcard : T.card = Module.finrank ℝ E + 1) (ℓ : E →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ v ∈ K.vertices, ℓ v ≠ a ∧ ℓ v ≠ b) :
    closure ((K.space ∩ ℓ ⁻¹' Icc a b) \ (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' Icc a b)) =
      (subcomplexGeneratedBy K {s | ¬s ⊆ T}).space ∩ ℓ ⁻¹' Icc a b := by
  let R := subcomplexGeneratedBy K {s | ¬s ⊆ T}
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K _).to_subtype
  have hRspace : R.space = closure (K.space \ convexHull ℝ (T : Set E)) :=
    (closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy K K Subset.rfl hT).symm
  have hRreg : closure (interior R.space) = R.space := by
    rw [hRspace]
    exact Topology.closure_interior_closure_sdiff hreg (T.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hRslab := closure_interior_space_inter_slab R hRreg ℓ hab
    (fun v hv => havoid v (subcomplexGeneratedBy_faces_subset K _ hv))
  rw [hRspace] at hRslab
  have hTreg : closure (interior (convexHull ℝ (T : Set E))) = convexHull ℝ (T : Set E) := by
    rw [interior_convexHull_eq_openSimplex (K.indep hT) hcard]
    exact Subset.antisymm
      (closure_minimal (openSimplex_subset_convexHull T) (T.finite_toSet.isCompact_convexHull ℝ).isClosed)
      (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hT))
  change _ = R.space ∩ ℓ ⁻¹' Icc a b
  rw [hRspace]
  exact Topology.closure_inter_sdiff_eq_inter_closure_sdiff (isPolyhedron_space K).isClosed
    (isClosed_Icc.preimage ℓ.continuous_of_finiteDimensional) hTreg hRslab

end DifferentialGeometry.Topology.PiecewiseLinear
