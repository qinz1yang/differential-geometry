import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

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
theorem exists_isPLBall_patches_at_doublePoint_of_continuousOn [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (f : E → X)
    (hf : ContinuousOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    {y : X} (hy : y ∈ doublePointSet f K.space) {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ P Q B : Set E, ∃ U : Set X,
      P ∪ Q = K.space ∧ IsPLBall (n + 1) P ∧ IsPolyhedron Q ∧ IsPLBall (n + 1) B ∧
      B ⊆ Q ∧ Disjoint P B ∧ InjOn f P ∧ InjOn f B ∧
      IsOpen U ∧ y ∈ U ∧ closure U ⊆ V ∧
      (∀ x ∈ P ∩ Q, f x ∉ closure U) ∧ InjOn f (Q ∩ f ⁻¹' U) ∧
      ∀ z ∈ closure U, K.space ∩ f ⁻¹' {z} ⊆ P ∪ B := by
  obtain ⟨R, hR, hRfinite, hinj⟩ := exists_isSubdivision_injOn_starComplex K f hloc
  have : Finite R.faces := hRfinite.to_subtype
  have hKR := hK.of_isSubdivision hR
  have hfR : ContinuousOn f R.space := by rwa [hR.space_eq]
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
      hfR hfiber hSneigh hTneigh
  have hclosed : IsClosed (f '' (S.space ∩ C.space)) :=
    (((isPolyhedron_space S).isCompact.inter_right (isPolyhedron_space C).isClosed).image_of_continuousOn
      (hfR.mono (inter_subset_left.trans hSsub))).isClosed
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
  exact exists_isPLBall_patches_at_doublePoint_of_continuousOn K hK f hf.continuousOn hloc hcard hy hV

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
open Classical in
theorem exists_isPLBall_postcomp_neighborhood_at_doublePoint_in_manifold
    {d n m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [RegularSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (f : EuclideanSpace ℝ (Fin d) → X)
    (hf : IsPLOn d m f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    {y : X} (hy : y ∈ doublePointSet f K.space) {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ P : Set (EuclideanSpace ℝ (Fin d)), ∃ U : Set X, IsPLBall (n + 1) P ∧ P ⊆ K.space ∧
      IsOpen U ∧ y ∈ U ∧ closure U ⊆ V ∧
      ∀ h : X → X, IsPL m m h → Function.Injective h → EqOn h id Uᶜ →
        ∃ g : EuclideanSpace ℝ (Fin d) → X, IsPLOn d m g K.space ∧
          IsLocallyInjective (K.space.domRestrict g) ∧
          (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
          EqOn g (h ∘ f) P ∧ EqOn g f Pᶜ ∧ ∀ z ∉ U, g ⁻¹' {z} = f ⁻¹' {z} := by
  have hcont : ContinuousOn f K.space := fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨P, Q, B, U, hPQ, hP, hQ, _, _, _, hinjP, _, hU, hyU, hUV, hseam, hinjQ, _⟩ :=
    exists_isPLBall_patches_at_doublePoint_of_continuousOn K hK f hcont hloc hcard hy hV
  have hPpoly : IsPolyhedron P := by
    obtain ⟨k, hk⟩ := hP
    rw [← hk.image_eq]
    exact (isHPolytope_stdSimplex _).isPolyhedron.image_of_isPiecewiseAffineOn hk.isPiecewiseAffineOn hk.bijOn.injOn
  refine ⟨P, U, hP, hPQ ▸ subset_union_left, hU, hyU, hUV, fun h hh hhinj hfix => ?_⟩
  let g := P.piecewise (h ∘ f) f
  have hsevent : ∀ x ∈ P ∩ Q, ∀ᶠ z in 𝓝 (f x), h z = z := by
    intro x hx
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hseam x hx)] with z hz
    exact hfix (fun hzU => hz (subset_closure hzU))
  have hfPQ : IsPLOn d m f (P ∪ Q) := by rwa [hPQ]
  have hg : IsPLOn d m g K.space := by
    rw [← hPQ]
    exact hfPQ.piecewise_postcomp_of_isClosed hh hPpoly.isClosed hQ.isClosed hsevent
  have hgloc : IsLocallyInjective (K.space.domRestrict g) := by
    have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict f) := by rwa [hPQ]
    have hcontPQ : ContinuousOn f (P ∪ Q) := by rwa [hPQ]
    rw [← hPQ]
    exact IsLocallyInjective.piecewise_postcomp_of_isClosed hlocPQ hcontPQ
      hPpoly.isClosed hQ.isClosed hhinj hsevent
  have hgcard : ∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2 := by
    apply encard_fiber_piecewise_postcomp_le f K.space P hhinj hfix
      (hinjP.mono inter_subset_right) (n := 1)
    · simpa only [one_add_one_eq_two] using hcard
    · intro z hz
      apply encard_le_one_iff_subsingleton.mpr
      intro a ha b hb
      have haS : a ∈ P ∪ Q := hPQ ▸ ha.1.1
      have hbS : b ∈ P ∪ Q := hPQ ▸ hb.1.1
      have hfa : f a = z := ha.2
      have hfb : f b = z := hb.2
      apply hinjQ ⟨haS.resolve_left ha.1.2, ?_⟩ ⟨hbS.resolve_left hb.1.2, ?_⟩ (hfa.trans hfb.symm)
      · change f a ∈ U
        rwa [hfa]
      · change f b ∈ U
        rwa [hfb]
  exact ⟨g, hg, hgloc, hgcard, fun x hx => piecewise_eq_of_mem P (h ∘ f) f hx,
    fun x hx => piecewise_eq_of_notMem P (h ∘ f) f hx,
    fun z hz => piecewise_postcomp_preimage_singleton_of_eqOn_compl P f hhinj hfix hz⟩
end DifferentialGeometry.Topology.PiecewiseLinear
