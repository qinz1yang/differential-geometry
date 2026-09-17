import DifferentialGeometry.Topology.PiecewiseLinear.SlabFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem inter_slab_eq_closedStar_inter_of_fiber_subset
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {p : E} (hp : {p} ∈ K.faces) (hstar : closedStar K p ⊆ A.space)
    (ℓ : E →ₗ[ℝ] ℝ) {a b : ℝ} (hpheight : ℓ p ∈ Icc a b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ b < ℓ v)
    (hfiber : A.space ∩ {x | ℓ x = ℓ p} ⊆ closedStar K p) :
    A.space ∩ ℓ ⁻¹' Icc a b = closedStar K p ∩ ℓ ⁻¹' Icc a b := by
  classical
  apply Subset.antisymm _ (inter_subset_inter_left _ hstar)
  rintro x ⟨hxA, hxab⟩
  refine ⟨?_, hxab⟩
  obtain ⟨T, hT, hxT⟩ := A.mem_space_iff.mp hxA
  by_cases hpT : p ∈ T
  · exact mem_iUnion₂.mpr ⟨T, ⟨hAK hT, subset_convexHull ℝ _ hpT⟩, hxT⟩
  have hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v := fun v hv =>
    hgap v (K.down_closed (hAK hT) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
      (fun h => hpT (h ▸ hv))
  obtain ⟨f, hf, hcontrol⟩ := exists_isPLHomeomorphOn_face_slab_prism K (hAK hT) ℓ hpheight hvertices
  have hfx := hf.bijOn.mapsTo ⟨hxT, hxab⟩
  have hqstar := hfiber ⟨A.convexHull_subset_space hT hfx.1.1, hfx.1.2⟩
  have hiff := (hcontrol x ⟨hxT, hxab⟩).1 (starComplex K p) (starComplex_faces_subset K p)
  rw [starComplex_space K p hp] at hiff
  exact hiff.mp hqstar

end DifferentialGeometry.Topology.PiecewiseLinear
