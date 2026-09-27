/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.LinkHeightSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.VertexSectionRegularity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem notMem_heightSingularPoints_of_geometricLink_section_encard_le_two_of_injOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hM : IsPLSphere 2 M.space) {p : E} (hp : {p} ∈ M.faces)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ (insert p M.vertices))
    (hcard : ((SimplicialComplex.geometricLink M {p}).space ∩
      {x | ℓ x = ℓ p}).encard ≤ 2) :
    p ∉ heightSingularPoints M.space ℓ := by
  classical
  have hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space :=
    isPLSphere_geometricLink_of_isPLSphere M hM hp
  have havoid : ∀ v ∈ (SimplicialComplex.geometricLink M {p}).vertices,
      ℓ v ≠ ℓ p := by
    intro v hv heq
    have hvM : v ∈ M.vertices := SimplicialComplex.geometricLink_le M {p} hv
    have hvp : v = p := hinj (by simp [hvM]) (by simp) heq
    have hvspace : v ∈ (SimplicialComplex.geometricLink M {p}).space :=
      (SimplicialComplex.geometricLink M {p}).vertices_subset_space hv
    exact notMem_geometricLink_space M (hvp ▸ hvspace)
  have hfiber : ℓ ⁻¹' ({ℓ p} : Set ℝ) = {x | ℓ x = ℓ p} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  have hsection := height_section_eq_empty_or_pair_of_encard_le_two
    (SimplicialComplex.geometricLink M {p}) hlink ℓ (ℓ p) havoid (by rwa [hfiber])
  rcases hsection with hempty | ⟨a, b, hab, hpair⟩
  · apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty M hp ℓ.toLinearMap
    rwa [hfiber] at hempty
  · have ha : a ∈ (SimplicialComplex.geometricLink M {p}).space ∩
        ℓ ⁻¹' ({ℓ p} : Set ℝ) := by
      rw [hpair]
      exact Set.mem_insert a {b}
    obtain ⟨hneg, hpos⟩ :=
      exists_lt_and_gt_of_mem_height_section_of_avoids_vertices
        (SimplicialComplex.geometricLink M {p}) ℓ (ℓ p) havoid ha
    obtain ⟨T, hT, -, -, -, hTnhds⟩ :=
      exists_affineIndependent_openSimplex_subset (n := 2) hdimE p Filter.univ_mem
    let D := convexHull ℝ (T : Set E)
    have hD : IsPolyhedron D := isPolyhedron_convexHull_of_affineIndependent T hT
    obtain ⟨K, hKfinite, hKspace, hKM, -, hKside⟩ :=
      exists_triangulation_union_with_halfSpace_faces M hD ℓ.toLinearMap.toAffineMap (ℓ p)
    let _ : Finite K.faces := hKfinite.to_subtype
    let L := restrict K M.space
    let _ : Finite L.faces := (restrict_faces_finite K M.space).to_subtype
    change IsSubdivision L M at hKM
    have hpL : {p} ∈ L.faces := hKM.singleton_mem hp
    have hKL : L.faces ⊆ K.faces := restrict_faces_subset K M.space
    have hKnhds : K.space ∈ 𝓝 p := by
      rw [hKspace]
      exact Filter.mem_of_superset hTnhds subset_union_right
    have hside : ∀ s ∈ K.faces,
        convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
          convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} := by
      intro s hs
      simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using hKside s hs
    have hlinkL : IsPLSphere 1 (SimplicialComplex.geometricLink L {p}).space :=
      (isPLSphere_geometricLink_iff_of_isSubdivision hKM hp).mpr hlink
    obtain ⟨f, hf, hfzero, hflt, hfgt⟩ :=
      exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign
        hKM hp ℓ.toLinearMap (fun s hs => hside s (hKL hs))
    have hfzero' : f '' ((SimplicialComplex.geometricLink L {p}).space ∩
        {x | ℓ x = ℓ p}) = {a, b} := by
      simpa only [ContinuousLinearMap.coe_coe] using hfzero.trans hpair
    obtain ⟨a', ha', hfa'⟩ : ∃ a' ∈
        (SimplicialComplex.geometricLink L {p}).space ∩ {x | ℓ x = ℓ p}, f a' = a := by
      have : a ∈ f '' ((SimplicialComplex.geometricLink L {p}).space ∩
          {x | ℓ x = ℓ p}) := hfzero'.symm.subset (Set.mem_insert a {b})
      simpa only [Set.mem_image] using this
    obtain ⟨b', hb', hfb'⟩ : ∃ b' ∈
        (SimplicialComplex.geometricLink L {p}).space ∩ {x | ℓ x = ℓ p}, f b' = b := by
      have : b ∈ f '' ((SimplicialComplex.geometricLink L {p}).space ∩
          {x | ℓ x = ℓ p}) := hfzero'.symm.subset (Set.mem_insert_iff.mpr (Or.inr rfl))
      simpa only [Set.mem_image] using this
    have hab' : a' ≠ b' := fun heq => hab (hfa'.symm.trans (heq ▸ hfb'))
    have hpairL : (SimplicialComplex.geometricLink L {p}).space ∩
        {x | ℓ x = ℓ p} = {a', b'} := by
      apply Subset.antisymm
      · intro x hx
        have hfx : f x ∈ ({a, b} : Set E) := hfzero'.subset (mem_image_of_mem f hx)
        rcases hfx with hfx | hfx
        · exact Or.inl (hf.bijOn.injOn hx.1 ha'.1 (hfx.trans hfa'.symm))
        · exact Or.inr (hf.bijOn.injOn hx.1 hb'.1 (hfx.trans hfb'.symm))
      · rintro x (rfl | rfl)
        · exact ha'
        · exact hb'
    have hnegL : ∃ x ∈ (SimplicialComplex.geometricLink L {p}).space, ℓ x < ℓ p := by
      obtain ⟨x, hx, hlt⟩ := hneg
      have hx' : x ∈ (SimplicialComplex.geometricLink M {p}).space ∩
          {x | ℓ x < ℓ p} := ⟨hx, hlt⟩
      obtain ⟨y, hy, hfy⟩ := hflt.symm.subset hx'
      exact ⟨y, hy.1, hy.2⟩
    have hposL : ∃ x ∈ (SimplicialComplex.geometricLink L {p}).space, ℓ p < ℓ x := by
      obtain ⟨x, hx, hlt⟩ := hpos
      have hx' : x ∈ (SimplicialComplex.geometricLink M {p}).space ∩
          {x | ℓ p < ℓ x} := ⟨hx, hlt⟩
      obtain ⟨y, hy, hfy⟩ := hfgt.symm.subset hx'
      exact ⟨y, hy.1, hy.2⟩
    have hcross : HasPLCrossingAt L.space {x | ℓ x = ℓ p} p :=
      hasPLCrossingAt_fiber_of_geometricLink_section_at hdimE K L hKL hpL hKnhds
        ℓ hℓ hside hlinkL hab' hpairL hposL hnegL
    rw [← hKM.space_eq]
    exact notMem_heightSingularPoints_of_hasPLCrossingAt hcross

end DifferentialGeometry.Topology.PiecewiseLinear
