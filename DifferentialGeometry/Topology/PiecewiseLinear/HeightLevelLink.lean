import DifferentialGeometry.Topology.PiecewiseLinear.VertexSectionSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem restrict_space_affine_eq_of_halfSpace_faces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) (r : ℝ)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
      convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x}) :
    (restrict K {x | a x = r}).space = K.space ∩ {x | a x = r} := by
  apply Subset.antisymm
  · exact subset_inter (space_mono_of_faces_subset (restrict_faces_subset K _))
      (restrict_space_subset K _)
  · rintro x ⟨hxK, hxa⟩
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxK
    have hverts : ∀ v ∈ s, a v = r := by
      rcases hside s hs with hle | hge
      · exact (affineMap_eq_iff_of_mem_openSimplex_of_le a hxs
          (fun v hv => hle (subset_convexHull ℝ _ hv))).mp hxa
      · exact (affineMap_eq_iff_of_mem_openSimplex_of_ge a hxs
          (fun v hv => hge (subset_convexHull ℝ _ hv))).mp hxa
    refine (restrict K _).convexHull_subset_space ⟨hs, ?_⟩
      (openSimplex_subset_convexHull s hxs)
    exact convexHull_min hverts ((convex_singleton r).affine_preimage a)

theorem encard_geometricLink_fiber_of_isPLSphere_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hfiber : IsPLSphere 1 (K.space ∩ {x | ℓ x = ℓ p})) :
    ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard = 2 := by
  classical
  obtain ⟨R, hRfin, -, hRK, -, hsideR⟩ :=
    exists_triangulation_union_with_halfSpace_faces K (isPolyhedron_space K) ℓ.toAffineMap (ℓ p)
  let _ : Finite R.faces := hRfin.to_subtype
  let L := restrict R K.space
  let _ : Finite L.faces := (restrict_faces_finite R K.space).to_subtype
  change IsSubdivision L K at hRK
  have hside : ∀ s ∈ L.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} :=
    fun s hs => hsideR s (restrict_faces_subset R K.space hs)
  let Q : Set E := {x | ℓ x = ℓ p}
  let F := restrict L Q
  let _ : Finite F.faces := (restrict_faces_finite L Q).to_subtype
  have hFspace : F.space = K.space ∩ Q := by
    have heq : F.space = L.space ∩ Q :=
      restrict_space_affine_eq_of_halfSpace_faces L ℓ.toAffineMap (ℓ p) hside
    exact heq.trans (congrArg (fun A : Set E => A ∩ Q) hRK.space_eq)
  have hF : IsPLSphere 1 F.space := hFspace.symm ▸ hfiber
  have hpF : {p} ∈ F.faces := by
    refine ⟨hRK.singleton_mem hp, ?_⟩
    simp only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
    rfl
  have hlink : IsPLSphere 0 (SimplicialComplex.geometricLink F {p}).space :=
    isPLSphere_geometricLink_of_isPLSphere F hF hpF
  have hlinkspace : (SimplicialComplex.geometricLink F {p}).space =
      (SimplicialComplex.geometricLink L {p}).space ∩ Q := by
    change (SimplicialComplex.geometricLink (restrict L Q) {p}).space = _
    have hQ : Convex ℝ Q := (convex_singleton (ℓ p)).affine_preimage ℓ.toAffineMap
    rw [geometricLink_restrict_convex L hQ (show p ∈ Q from rfl)]
    exact restrict_space_affine_eq_of_halfSpace_faces _ ℓ.toAffineMap (ℓ p)
      (fun s hs => hside s (geometricLink_faces_subset L {p} hs))
  obtain ⟨a, b, hab, hpair⟩ := isPLSphere_zero_iff.mp hlink
  have hcard : ((SimplicialComplex.geometricLink L {p}).space ∩ Q).encard = 2 := by
    rw [← hlinkspace, hpair, encard_pair hab]
  obtain ⟨f, hf, hflevel, -, -⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign hRK hp ℓ hside
  rw [← hflevel, (hf.bijOn.injOn.mono inter_subset_left).encard_image]
  exact hcard

theorem notMem_heightSingularPoints_of_isPLSphere_one_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices)
    (hfiber : IsPLSphere 1 (K.space ∩ {x | ℓ x = ℓ p})) :
    p ∉ heightSingularPoints K.space ℓ := by
  classical
  have hcard : ((SimplicialComplex.geometricLink K {p}).space ∩
      {x | ℓ x = ℓ p}).encard = 2 :=
    encard_geometricLink_fiber_of_isPLSphere_one K hp ℓ.toLinearMap hfiber
  apply notMem_heightSingularPoints_of_geometricLink_section_encard_le_two_of_injOn
    hdimE K hK hp ℓ hℓ _ hcard.le
  rwa [insert_eq_of_mem hp]

end DifferentialGeometry.Topology.PiecewiseLinear
