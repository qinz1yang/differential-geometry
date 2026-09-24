import DifferentialGeometry.Geometry.Neck.SpatialRestriction

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Surgery.Topology

theorem section_image_eq_restricted_neck_of_image_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (U : TopologicalSpace.Opens M)
    {g : SmoothRiemannianMetric I3 M} {p : M} {hp : p ∈ U} {eps beta q : ℝ}
    (nk : SpatialNeck g eps p) (parent : SpatialNeck (g.restrictOpen U) beta ⟨p, hp⟩)
    (T : PartialDiffeomorph IC I3 Cylinder U ∞)
    (hmap : ∀ z ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹, (parent.map z : M) = nk.map z)
    (himage : nk.map '' (univ ×ˢ ({0} : Set ℝ)) =
      (Subtype.val : U → M) '' (T '' (univ ×ˢ ({q} : Set ℝ)))) :
    (T '' (univ ×ˢ ({q} : Set ℝ))) = parent.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  have hzero (v : Sphere 2) : (v, (0 : ℝ)) ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹ :=
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr parent.eps_pos), inv_pos.mpr parent.eps_pos⟩
  ext x
  constructor
  · intro hx
    have hximage : (x : M) ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
      rw [himage]
      exact mem_image_of_mem _ hx
    obtain ⟨z, hz, heq⟩ := hximage
    refine ⟨z, hz, Subtype.ext ?_⟩
    have hzdom : z ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹ := by
      have hh : z = (z.1, 0) := Prod.ext rfl hz.2
      rw [hh]
      exact hzero z.1
    exact (hmap z hzdom).trans heq
  · rintro ⟨z, hz, rfl⟩
    have hzdom : z ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹ := by
      have hh : z = (z.1, 0) := Prod.ext rfl hz.2
      rw [hh]
      exact hzero z.1
    have hximage : ((parent.map z : U) : M) ∈ (Subtype.val : U → M) '' (T '' (univ ×ˢ ({q} : Set ℝ))) := by
      rw [← himage, hmap z hzdom]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, heq⟩ := hximage
    exact (Subtype.ext heq : x = parent.map z) ▸ hx

theorem half_slab_subset_restricted_neck
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (U : TopologicalSpace.Opens M)
    {g : SmoothRiemannianMetric I3 M} {p : M} {hp : p ∈ U} {eps beta : ℝ}
    (nk : SpatialNeck g eps p) (parent : SpatialNeck (g.restrictOpen U) beta ⟨p, hp⟩)
    (hmap : ∀ z ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹, (parent.map z : M) = nk.map z)
    {D : Set M} (hD : D ⊆ nk.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2))) :
    (Subtype.val : U → M) ⁻¹' D ⊆ parent.map '' (univ ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := by
  intro x hx
  obtain ⟨z, hz, heq⟩ := hD hx
  refine ⟨z, hz, Subtype.ext ?_⟩
  have hi : 1 < beta⁻¹ := (one_lt_inv₀ parent.eps_pos).mpr (by linarith [parent.eps_small])
  have hzdom : z ∈ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹ :=
    ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  exact (hmap z hzdom).trans heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
