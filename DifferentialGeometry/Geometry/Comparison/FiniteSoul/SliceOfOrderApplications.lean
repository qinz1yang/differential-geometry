import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrder

/-!
# Consumers of the finite-order slice definitions (lane CMS3-SLICE, group G0)

* an open set is its own relative interior: relative dimension `dim E`, empty relative boundary;
* the whole carrier is totally geodesic for every finite-order metric of class `C²` or better;
* the smooth suite's slices (`IsEmbeddedSlice`) are order-`k` slices, e.g. affine subspaces of the model.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A nonempty open set has full relative dimension. -/
theorem maxSliceDimOfOrder_of_isOpen {k : ℕ∞} {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    maxSliceDimOfOrder I (k : WithTop ℕ∞) U = Module.finrank ℝ E :=
  le_antisymm (maxSliceDimOfOrder_le U)
    (le_maxSliceDimOfOrder ⟨U, hne, subset_rfl, IsEmbeddedSliceOfOrder.of_isOpen hU⟩)

/-- An open set is its own relative interior. -/
theorem maxSliceLocusOfOrder_of_isOpen {k : ℕ∞} {U : Set M} (hU : IsOpen U) :
    maxSliceLocusOfOrder I (k : WithTop ℕ∞) U = U := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact Subset.antisymm maxSliceLocusOfOrder_subset (empty_subset _)
  refine Subset.antisymm maxSliceLocusOfOrder_subset (subset_maxSliceLocusOfOrder subset_rfl ?_)
  rw [maxSliceDimOfOrder_of_isOpen hU hne]
  exact IsEmbeddedSliceOfOrder.of_isOpen hU

/-- An open set has empty relative boundary. -/
theorem relBoundaryOfOrder_of_isOpen {k : ℕ∞} {U : Set M} (hU : IsOpen U) :
    relBoundaryOfOrder I (k : WithTop ℕ∞) U = ∅ :=
  relBoundaryOfOrder_eq_empty_iff.2 (maxSliceLocusOfOrder_of_isOpen hU)

/-- The whole carrier is totally geodesic. -/
theorem isTotallyGeodesicFinite_univ [T2Space M] {r : ℕ∞} (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) :
    IsTotallyGeodesicFinite g (univ : Set M) :=
  IsTotallyGeodesicFinite.of_isOpen hr g isOpen_univ

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- A smooth affine slice of the model space is a slice of every order `k ≤ ∞`, through the smooth
suite's notion. -/
theorem isEmbeddedSliceOfOrder_affineSubspace_of_smooth {k : ℕ∞} (A : AffineSubspace ℝ E)
    [FiniteDimensional ℝ A.direction] :
    IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (k : WithTop ℕ∞) (Module.finrank ℝ A.direction) (A : Set E) :=
  IsEmbeddedSliceOfOrder.of_isEmbeddedSlice
    (isEmbeddedSliceOfOrder_top_iff.1 (IsEmbeddedSliceOfOrder.of_affineSubspace A))

end DifferentialGeometry.Geometry.FiniteSoul
