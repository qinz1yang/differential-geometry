import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem faceStarComplex_space_union_geometricFaceCostar (K : Geometry.SimplicialComplex ℝ E)
    (s : Finset E) :
    (faceStarComplex K s).space ∪ (SimplicialComplex.geometricFaceCostar K s).space = K.space := by
  apply Subset.antisymm
  · exact union_subset (space_mono_of_faces_subset (faceStarComplex_faces_subset K s))
      (space_mono_of_faces_subset (SimplicialComplex.geometricFaceCostar_le K s))
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hx
    by_cases hst : s ⊆ t
    · exact Or.inl ((faceStarComplex K s).convexHull_subset_space
        ⟨ht, by rwa [Finset.union_eq_left.mpr hst]⟩ hxt)
    · exact Or.inr ((SimplicialComplex.geometricFaceCostar K s).convexHull_subset_space ⟨ht, hst⟩ hxt)

open Classical in
theorem notMem_geometricFaceCostar_of_mem_openSimplex (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s) :
    x ∉ (SimplicialComplex.geometricFaceCostar K s).space := by
  intro hmem
  obtain ⟨t, ht, hxt⟩ := (SimplicialComplex.geometricFaceCostar K s).mem_space_iff.mp hmem
  exact ht.2 (face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht.1 hx hxt)

open Classical in
theorem exists_isPLBall_patches_at_doublePoint [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    {y : F} (hy : y ∈ doublePointSet f K.space) {V : Set F} (hV : V ∈ 𝓝 y) :
    ∃ P Q B : Set E, ∃ U : Set F,
      P ∪ Q = K.space ∧ IsPLBall (n + 1) P ∧ IsPolyhedron Q ∧ IsPLBall (n + 1) B ∧
      B ⊆ Q ∧ Disjoint P B ∧ InjOn f P ∧ InjOn f B ∧
      IsOpen U ∧ y ∈ U ∧ closure U ⊆ V ∧
      (∀ x ∈ P ∩ Q, f x ∉ closure U) ∧ InjOn f (Q ∩ f ⁻¹' U) ∧
      ∀ z ∈ closure U, K.space ∩ f ⁻¹' {z} ⊆ P ∪ B := by
  obtain ⟨R, hR, hRfinite, hinj⟩ := exists_isSubdivision_injOn_starComplex K f hloc
  have : Finite R.faces := hRfinite.to_subtype
  have hKR := hK.of_isSubdivision hR
  have hfR : IsPiecewiseAffineOn f R.space := by rwa [hR.space_eq]
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  have haR : a ∈ R.space := hR.space_eq ▸ ha
  have hbR : b ∈ R.space := hR.space_eq ▸ hb
  obtain ⟨s, hs, has⟩ := exists_face_mem_openSimplex R haR
  obtain ⟨t, ht, hbt⟩ := exists_face_mem_openSimplex R hbR
  let S := faceStarComplex R s
  let T := faceStarComplex R t
  let C := SimplicialComplex.geometricFaceCostar R s
  have hSR : S.faces ⊆ R.faces := faceStarComplex_faces_subset R s
  have hTR : T.faces ⊆ R.faces := faceStarComplex_faces_subset R t
  have hCR : C.faces ⊆ R.faces := SimplicialComplex.geometricFaceCostar_le R s
  have : Finite S.faces := (faceStarComplex_faces_finite R s).to_subtype
  have : Finite T.faces := (faceStarComplex_faces_finite R t).to_subtype
  have hSsub : S.space ⊆ R.space := space_mono_of_faces_subset hSR
  have hTsub : T.space ⊆ R.space := space_mono_of_faces_subset hTR
  have hCsub : C.space ⊆ R.space := space_mono_of_faces_subset hCR
  have hdisj : Disjoint S.space T.space := disjoint_spaces_of_disjoint_faces R S T hSR hTR
    (disjoint_faceStarComplex_faces_of_eq_of_injOn_starComplex R f hinj
      (openSimplex_subset_convexHull s has) (openSimplex_subset_convexHull t hbt) hab (hfa.trans hfb.symm))
  have hinjS : InjOn f S.space := by
    obtain ⟨v, hv⟩ := R.nonempty_of_mem_faces hs
    have hvR := R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvR).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex R hv))
  have hinjT : InjOn f T.space := by
    obtain ⟨v, hv⟩ := R.nonempty_of_mem_faces ht
    have hvR := R.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (hinj v hvR).mono (space_mono_of_faces_subset (faceStarComplex_faces_subset_starComplex R hv))
  have hcoverSC : S.space ∪ C.space = R.space := faceStarComplex_space_union_geometricFaceCostar R s
  have hTC : T.space ⊆ C.space := by
    intro x hx
    have hxR := hTsub hx
    rw [← hcoverSC] at hxR
    exact hxR.resolve_left (fun hxS => Set.disjoint_left.mp hdisj hxS hx)
  have hbT : b ∈ T.space := T.convexHull_subset_space
    ⟨ht, by rwa [Finset.union_self]⟩ (openSimplex_subset_convexHull t hbt)
  have haC : a ∉ C.space := notMem_geometricFaceCostar_of_mem_openSimplex R hs has
  have hfiber : R.space ∩ f ⁻¹' {y} = {a, b} := by
    rw [hR.space_eq]
    exact fiber_eq_pair_of_encard_le_two f K.space ha hb hab hfa hfb (hcard y)
  have hSneigh : S.space ∈ 𝓝[R.space] a := by
    rw [faceStarComplex_space R hs has]
    exact closedStar_mem_nhdsWithin R a
  have hTneigh : T.space ∈ 𝓝[R.space] b := by
    rw [faceStarComplex_space R ht hbt]
    exact closedStar_mem_nhdsWithin R b
  have hcover : ∀ᶠ z in 𝓝 y, R.space ∩ f ⁻¹' {z} ⊆ S.space ∪ T.space :=
    eventually_preimage_subset_union_of_fiber_eq_pair f (isPolyhedron_space R).isCompact
      hfR.continuousOn hfiber hSneigh hTneigh
  have hclosed : IsClosed (f '' (S.space ∩ C.space)) :=
    (((isPolyhedron_space S).isCompact.inter_right (isPolyhedron_space C).isClosed).image_of_continuousOn
      (hfR.continuousOn.mono (inter_subset_left.trans hSsub))).isClosed
  have hyseam : y ∉ f '' (S.space ∩ C.space) := by
    rintro ⟨x, hx, hxy⟩
    have hxpair : x ∈ ({a, b} : Set E) := hfiber ▸ ⟨hSsub hx.1, hxy⟩
    rcases hxpair with rfl | rfl
    · exact haC hx.2
    · exact Set.disjoint_left.mp hdisj hx.1 hbT
  have hbase : V ∩ (f '' (S.space ∩ C.space))ᶜ ∩
      {z | R.space ∩ f ⁻¹' {z} ⊆ S.space ∪ T.space} ∈ 𝓝 y :=
    Filter.inter_mem (Filter.inter_mem hV (hclosed.isOpen_compl.mem_nhds hyseam)) hcover
  obtain ⟨U, ⟨hyU, hU⟩, hUsub⟩ := (hasBasis_opens_closure y).mem_iff.mp hbase
  have hseam : ∀ x ∈ S.space ∩ C.space, f x ∉ closure U := by
    intro x hx hfx
    exact (hUsub hfx).1.2 ⟨x, hx, rfl⟩
  have hrest : C.space ∩ f ⁻¹' U ⊆ T.space := by
    intro x hx
    rcases (hUsub (subset_closure hx.2)).2 ⟨hCsub hx.1, rfl⟩ with hxS | hxT
    · exact False.elim (hseam x ⟨hxS, hx.1⟩ (subset_closure hx.2))
    · exact hxT
  refine ⟨S.space, C.space, T.space, U, hcoverSC.trans hR.space_eq,
    hKR.isPLBall_faceStarComplex R hs, isPolyhedron_space C, hKR.isPLBall_faceStarComplex R ht,
    hTC, hdisj, hinjS, hinjT, hU, hyU, fun z hz => (hUsub hz).1.1, hseam, hinjT.mono hrest, ?_⟩
  intro z hz
  rw [← hR.space_eq]
  exact (hUsub hz).2

open Classical in
theorem exists_isPLBall_postcomp_neighborhood_at_doublePoint [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    {y : F} (hy : y ∈ doublePointSet f K.space) {V : Set F} (hV : V ∈ 𝓝 y) :
    ∃ P : Set E, ∃ U : Set F, IsPLBall (n + 1) P ∧ P ⊆ K.space ∧
      IsOpen U ∧ y ∈ U ∧ closure U ⊆ V ∧
      ∀ h : F → F, IsPiecewiseAffineOn h univ → Function.Injective h → EqOn h id Uᶜ →
        ∃ g : E → F, IsPiecewiseAffineOn g K.space ∧
          IsLocallyInjective (K.space.domRestrict g) ∧
          (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
          EqOn g (h ∘ f) P ∧ EqOn g f Pᶜ ∧
          (∀ x, dist (g x) (f x) ≤ dist (h (f x)) (f x)) ∧
          ∀ z ∉ U, g ⁻¹' {z} = f ⁻¹' {z} := by
  obtain ⟨P, Q, B, U, hPQ, hP, hQ, _, _, _, hinjP, _, hU, hyU, hUV, hseam, hinjQ, _⟩ :=
    exists_isPLBall_patches_at_doublePoint K hK f hf hloc hcard hy hV
  have hPpoly : IsPolyhedron P := by
    obtain ⟨k, hk⟩ := hP
    rw [← hk.image_eq]
    exact (isHPolytope_stdSimplex _).isPolyhedron.image_of_isPiecewiseAffineOn hk.isPiecewiseAffineOn hk.bijOn.injOn
  refine ⟨P, U, hP, hPQ ▸ subset_union_left, hU, hyU, hUV, fun h hh hhinj hfix => ?_⟩
  have hfPQ : IsPiecewiseAffineOn f (P ∪ Q) := by rwa [hPQ]
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict f) := by rwa [hPQ]
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ f ⁻¹' {z}).encard ≤ 2 := by rwa [hPQ]
  obtain ⟨g, hg, hgloc, hgcard, hgP, _, hgQ, hgfiber⟩ :=
    exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective hfPQ hPpoly hQ hlocPQ
      hcardPQ hinjP hh hhinj hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  refine ⟨g, hg, hgloc, hgcard, hgP, hgQ, ?_, hgfiber⟩
  intro x
  by_cases hx : x ∈ P
  · rw [hgP hx]
    exact le_rfl
  · rw [hgQ hx, dist_self]
    exact dist_nonneg
end DifferentialGeometry.Topology.PiecewiseLinear
