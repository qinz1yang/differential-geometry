import DifferentialGeometry.Topology.PiecewiseLinear.LocalManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_faces_of_mem_nhdsWithin_space {K L : Geometry.SimplicialComplex ℝ E}
    (hL : L.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hxL : L.space ∈ 𝓝[K.space] x) : s ∈ L.faces := by
  obtain ⟨O, hO, hxO, hOL⟩ := mem_nhdsWithin.mp hxL
  have hxcl := convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs) hx
  obtain ⟨y, hyO, hys⟩ := mem_closure_iff.mp hxcl O hO hxO
  obtain ⟨t, ht, hyt⟩ := L.mem_space_iff.mp
    (hOL ⟨hyO, K.convexHull_subset_space hs (openSimplex_subset_convexHull s hys)⟩)
  exact L.down_closed ht (face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hL ht) hys hyt)
    (K.nonempty_of_mem_faces hs)

section Relative

variable [DecidableEq E] {K A : Geometry.SimplicialComplex ℝ E} (hA : A.faces ⊆ K.faces)

noncomputable def relativeBarycentricSubdivision : Geometry.SimplicialComplex ℝ E :=
  relDerived hA (IsSubdivision.refl A) (centroid_mem_openSimplex_of_mem_faces K)

theorem relativeBarycentricSubdivision_isSubdivision :
    IsSubdivision (relativeBarycentricSubdivision hA) K :=
  relDerived_isSubdivision hA (IsSubdivision.refl A) (centroid_mem_openSimplex_of_mem_faces K)

theorem faces_subset_relativeBarycentricSubdivision :
    A.faces ⊆ (relativeBarycentricSubdivision hA).faces :=
  faces_subset_relDerived hA (IsSubdivision.refl A) (centroid_mem_openSimplex_of_mem_faces K)

theorem relativeBarycentricSubdivision_faces_finite [Finite K.faces] :
    (relativeBarycentricSubdivision hA).faces.Finite := by
  have := ((Set.toFinite K.faces).subset hA).to_subtype
  exact relDerived_faces_finite hA (IsSubdivision.refl A) (centroid_mem_openSimplex_of_mem_faces K)

theorem mem_barycentricSubdivision_of_mem_relative_of_disjoint {s : Finset E}
    (hs : s ∈ (relativeBarycentricSubdivision hA).faces)
    (hdis : Disjoint (convexHull ℝ (s : Set E)) A.space) :
    s ∈ (barycentricSubdivision K).faces := by
  obtain ⟨τ, d, h, rfl⟩ := hs
  have hτ : τ = ∅ := by
    rcases h.base with hτ | hτ
    · exact hτ
    · obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces hτ
      exact (Set.disjoint_left.mp hdis
        (subset_convexHull ℝ _ (Finset.mem_union_left _ hv))
        (A.convexHull_subset_space hτ (subset_convexHull ℝ _ hv))).elim
  have hd : d.Nonempty := h.nonempty.resolve_left (hτ ▸ Finset.not_nonempty_empty)
  exact ⟨d, h.flag, hd, by rw [hτ, Finset.empty_union]⟩

noncomputable def relativeSecondDerived : Geometry.SimplicialComplex ℝ E :=
  relativeBarycentricSubdivision (faces_subset_relativeBarycentricSubdivision hA)

theorem relativeSecondDerived_isSubdivision : IsSubdivision (relativeSecondDerived hA) K :=
  (relativeBarycentricSubdivision_isSubdivision
    (faces_subset_relativeBarycentricSubdivision hA)).trans
      (relativeBarycentricSubdivision_isSubdivision hA)

theorem faces_subset_relativeSecondDerived : A.faces ⊆ (relativeSecondDerived hA).faces :=
  faces_subset_relativeBarycentricSubdivision (faces_subset_relativeBarycentricSubdivision hA)

theorem relativeSecondDerived_faces_finite [Finite K.faces] :
    (relativeSecondDerived hA).faces.Finite := by
  have := (relativeBarycentricSubdivision_faces_finite hA).to_subtype
  exact relativeBarycentricSubdivision_faces_finite (faces_subset_relativeBarycentricSubdivision hA)

theorem relativeSecondDerived_face_subset_or_mem_secondDerived
    {L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    (hdeep : ∀ x ∈ A.space, L.space ∈ 𝓝[K.space] x) {s : Finset E}
    (hs : s ∈ (relativeSecondDerived hA).faces) :
    convexHull ℝ (s : Set E) ⊆ L.space ∨ s ∈ (secondDerived K).faces := by
  let R := relativeBarycentricSubdivision hA
  have hR := relativeBarycentricSubdivision_isSubdivision hA
  have hR₂ := relativeBarycentricSubdivision_isSubdivision
    (faces_subset_relativeBarycentricSubdivision hA)
  obtain ⟨t, ht, hst⟩ := hR₂.exists_face_subset hs
  by_cases hdis : Disjoint (convexHull ℝ (t : Set E)) A.space
  · right
    obtain ⟨τ, d, h, rfl⟩ := hs
    have hτ : τ = ∅ := by
      rcases h.base with hτ | hτ
      · exact hτ
      · obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces hτ
        exact (Set.disjoint_left.mp hdis
          (hst (subset_convexHull ℝ _ (Finset.mem_union_left _ hv)))
          (A.convexHull_subset_space hτ (subset_convexHull ℝ _ hv))).elim
    have hd : d.Nonempty := h.nonempty.resolve_left (hτ ▸ Finset.not_nonempty_empty)
    refine ⟨d, ⟨fun e he => ?_, h.flag.2⟩, hd, by rw [hτ, Finset.empty_union]⟩
    have heR : e ∈ R.faces := h.flag.mem_faces he
    have het : e ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull R heR ht
      (centroid_mem_openSimplex_of_mem_faces R e heR)
      (hst (subset_convexHull ℝ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))))
    exact mem_barycentricSubdivision_of_mem_relative_of_disjoint hA heR
      (hdis.mono_left (convexHull_mono (Finset.coe_subset.mpr het)))
  · left
    obtain ⟨x, hxt, hxA⟩ := Set.not_disjoint_iff.mp hdis
    obtain ⟨u, hu, htu⟩ := hR.exists_face_subset ht
    have huL := mem_faces_of_mem_nhdsWithin_space hL hu (htu hxt) (hdeep x hxA)
    exact hst.trans (htu.trans (L.convexHull_subset_space huL))

variable (L : Geometry.SimplicialComplex ℝ E)

noncomputable def relativeDerivedNeighborhood : Geometry.SimplicialComplex ℝ E :=
  restrict (relativeSecondDerived hA) (derivedNeighborhood K L).space

theorem relativeDerivedNeighborhood_faces_subset :
    (relativeDerivedNeighborhood hA L).faces ⊆ (relativeSecondDerived hA).faces :=
  restrict_faces_subset _ _

theorem relativeDerivedNeighborhood_faces_finite [Finite K.faces] :
    (relativeDerivedNeighborhood hA L).faces.Finite :=
  (relativeSecondDerived_faces_finite hA).subset (relativeDerivedNeighborhood_faces_subset hA L)

theorem relativeDerivedNeighborhood_space_subset :
    (relativeDerivedNeighborhood hA L).space ⊆ K.space :=
  (restrict_space_subset _ _).trans (derivedNeighborhood_space_subset K L)

theorem relativeDerivedNeighborhood_space [Finite K.faces] (hL : L.faces ⊆ K.faces)
    (hdeep : ∀ x ∈ A.space, L.space ∈ 𝓝[K.space] x) :
    (relativeDerivedNeighborhood hA L).space = (derivedNeighborhood K L).space := by
  apply Subset.antisymm (restrict_space_subset _ _)
  intro x hx
  have hxR : x ∈ (relativeSecondDerived hA).space :=
    (relativeSecondDerived_isSubdivision hA).space_eq.symm ▸ derivedNeighborhood_space_subset K L hx
  obtain ⟨s, hs, hxs⟩ := (relativeSecondDerived hA).mem_space_iff.mp hxR
  rcases relativeSecondDerived_face_subset_or_mem_secondDerived hA hL hdeep hs with hsL | hsK
  · refine (relativeDerivedNeighborhood hA L).convexHull_subset_space ⟨hs, fun y hy => ?_⟩ hxs
    exact mem_of_mem_nhdsWithin (space_mono_of_faces_subset hL (hsL hy))
      (derivedNeighborhood_mem_nhdsWithin hL (hsL hy))
  · obtain ⟨t, ht, hxt⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
    have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      rw [Finset.coe_inter]
      exact (secondDerived K).inter_subset_convexHull hsK (derivedNeighborhood_faces_subset K L ht)
        ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h] at hxst
    exact (relativeDerivedNeighborhood hA L).convexHull_subset_space
      ⟨(relativeSecondDerived hA).down_closed hs Finset.inter_subset_left hne,
        (convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right)).trans
          ((derivedNeighborhood K L).convexHull_subset_space ht)⟩ hxst

theorem faces_subset_relativeDerivedNeighborhood [Finite K.faces]
    (hAL : A.faces ⊆ L.faces) (hL : L.faces ⊆ K.faces) :
    A.faces ⊆ (relativeDerivedNeighborhood hA L).faces := by
  intro s hs
  refine ⟨faces_subset_relativeSecondDerived hA hs, fun x hx => ?_⟩
  have hxL := L.convexHull_subset_space (hAL hs) hx
  exact mem_of_mem_nhdsWithin (space_mono_of_faces_subset hL hxL)
    (derivedNeighborhood_mem_nhdsWithin hL hxL)

theorem relativeDerivedNeighborhood_mem_nhdsWithin [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (hdeep : ∀ x ∈ A.space, L.space ∈ 𝓝[K.space] x)
    {x : E} (hx : x ∈ L.space) :
    (relativeDerivedNeighborhood hA L).space ∈ 𝓝[K.space] x := by
  rw [relativeDerivedNeighborhood_space hA L hL hdeep]
  exact derivedNeighborhood_mem_nhdsWithin hL hx

end Relative

variable {K A : Geometry.SimplicialComplex ℝ E} (hA : A.faces ⊆ K.faces)
  (L : Geometry.SimplicialComplex ℝ E)

open Classical in
theorem IsLocallyCombinatorialManifoldWithBoundary.relativeDerivedNeighborhood
    [FiniteDimensional ℝ E] [Finite K.faces] {n : ℕ}
    (h : IsLocallyCombinatorialManifoldWithBoundary n K L.space)
    (hL : L.faces ⊆ K.faces) (hdeep : ∀ x ∈ A.space, L.space ∈ 𝓝[K.space] x) :
    IsCombinatorialManifoldWithBoundary (n + 1)
      (PiecewiseLinear.relativeDerivedNeighborhood hA L) := by
  have := (relativeDerivedNeighborhood_faces_finite hA L).to_subtype
  have := (derivedNeighborhood_faces_finite K L).to_subtype
  have hpa : IsPiecewiseAffineOn (id : E → E) (PiecewiseLinear.derivedNeighborhood K L).space :=
    isPiecewiseAffineOn_space_of_forall_face _ fun _ _ =>
      ⟨AffineMap.id ℝ E, fun _ _ => rfl⟩
  have hinv : IsPiecewiseAffineOn (Function.invFunOn id (PiecewiseLinear.derivedNeighborhood K L).space)
      (PiecewiseLinear.derivedNeighborhood K L).space :=
    hpa.congr fun y hy => (bijOn_id (PiecewiseLinear.derivedNeighborhood K L).space).invOn_invFunOn.1 hy
  have hid : IsPLHomeomorphOn id (PiecewiseLinear.derivedNeighborhood K L).space
      (PiecewiseLinear.relativeDerivedNeighborhood hA L).space := by
    rw [relativeDerivedNeighborhood_space hA L hL hdeep]
    exact ⟨bijOn_id _, hpa, hinv⟩
  exact (h.derivedNeighborhood L).of_isPLHomeomorphOn hid

open Classical in
theorem IsCombinatorialManifoldWithBoundary.relativeDerivedNeighborhood
    [FiniteDimensional ℝ E] [Finite K.faces] {n : ℕ}
    (h : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : L.faces ⊆ K.faces) (hdeep : ∀ x ∈ A.space, L.space ∈ 𝓝[K.space] x) :
    IsCombinatorialManifoldWithBoundary (n + 1)
      (PiecewiseLinear.relativeDerivedNeighborhood hA L) :=
  (h.isLocally L.space).relativeDerivedNeighborhood hA L hL hdeep

end DifferentialGeometry.Topology.PiecewiseLinear
