import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem SpatialNeck.nonempty_at_of_mem_image_central_band
    {g : SmoothRiemannianMetric I3 M} {eps alpha : ℝ} {p : M}
    (nk : SpatialNeck g eps p) (hsmall : alpha < 1 / 11)
    (hreserve : 13000 * eps ≤ alpha) {x : M}
    (hx : x ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
    Nonempty (SpatialNeck g alpha x) := by
  obtain ⟨⟨u, t⟩, ⟨_, ht⟩, hxt⟩ := hx
  obtain ⟨out, _⟩ := nk.exists_at_coordinate (a := t) hsmall hreserve u (by
    rw [abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact ⟨hxt.symm ▸ out⟩

theorem nonempty_spatial_neck_of_subset_iUnion_central_bands
    {g : SmoothRiemannianMetric I3 M} {eps alpha : ℝ} {ι : Type*}
    (hsmall : alpha < 1 / 11) (hreserve : 13000 * eps ≤ alpha)
    (A : ι → Set M) (point : ι → M) (nk : ∀ i, SpatialNeck g eps (point i))
    (hcover : ∀ i, A i ⊆ (nk i).map '' (univ ×ˢ Icc (-4 : ℝ) 4))
    {U : Set M} (hU : U ⊆ ⋃ i, A i) :
    ∀ x ∈ U, Nonempty (SpatialNeck g alpha x) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hU hx)
  exact (nk i).nonempty_at_of_mem_image_central_band hsmall hreserve (hcover i hi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
