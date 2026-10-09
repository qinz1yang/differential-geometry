/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_cell_dim_eq_of_sphere_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] {n : ℕ} {S : Set E} (dim : ι → ℕ) (cell : ι → Set E)
    (hcell : ∀ i, IsPLBall (dim i) (cell i)) (hcover : S = ⋃ i, cell i)
    (hsphere : IsPLSphere n S) (hdim : ∀ i, dim i ≤ n) {x : E} (hx : x ∈ S) :
    ∃ i, dim i = n ∧ x ∈ cell i := by
  classical
  obtain ⟨L, hLfin, hLspace⟩ := hsphere.isPolyhedron.exists_simplicialComplex
  let : Finite L.faces := hLfin.to_subtype
  have hsub : ∀ i, cell i ⊆ L.space := by
    intro i
    rw [hLspace, hcover]
    exact subset_iUnion cell i
  obtain ⟨T, hTL, hTfin, hpieces⟩ := exists_isSubdivision_subcomplexes L cell
    (fun i => (hcell i).isPolyhedron) hsub
  let : Finite T.faces := hTfin.to_subtype
  have hTspace : T.space = S := hTL.space_eq.trans hLspace
  have hTsphere : IsPLSphere n T.space := hTspace.symm ▸ hsphere
  obtain ⟨s, hs, hxs⟩ := T.mem_space_iff.mp (hTspace.symm ▸ hx)
  obtain ⟨t, ht, hst, htcard⟩ := exists_face_superset_card_eq_of_isPLSphere T hTsphere hs
  have hyt : t.centroid ℝ id ∈ openSimplex t :=
    centroid_mem_openSimplex (T.nonempty_of_mem_faces ht)
  have hyS : t.centroid ℝ id ∈ S :=
    hTspace ▸ T.convexHull_subset_space ht (openSimplex_subset_convexHull t hyt)
  rw [hcover] at hyS
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hyS
  rw [hpieces i] at hyi
  obtain ⟨u, ⟨hu, hui⟩, hyu⟩ := mem_iUnion₂.mp hyi
  have hti : convexHull ℝ (t : Set E) ⊆ cell i :=
    (convexHull_mono (Finset.coe_subset.mpr
      (face_subset_of_mem_openSimplex_of_mem_convexHull T ht hu hyt hyu))).trans hui
  let R := restrict T (cell i)
  let : Finite R.faces := (restrict_faces_finite T (cell i)).to_subtype
  have hRspace : R.space = cell i := restrict_space_of_eq_biUnion T (cell i) (hpieces i)
  have hRball : IsPLBall (dim i) R.space := hRspace.symm ▸ hcell i
  have hcard := card_le_of_isPLBall R hRball (show t ∈ R.faces from ⟨ht, hti⟩)
  refine ⟨i, ?_, hti ((convexHull_mono (Finset.coe_subset.mpr hst)) hxs)⟩
  have := hdim i
  omega

end DifferentialGeometry.Topology.PiecewiseLinear
