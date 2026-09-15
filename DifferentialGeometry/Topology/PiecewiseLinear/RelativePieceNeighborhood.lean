import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeMesh

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [T2Space X]

open Classical in
theorem PLPieceIn.isPLSphere_geometricLink_of_mem_interior {Y : Set X}
    (T : PLPieceIn E (m + 1) X Y) {v : E} (hv : {v} ∈ T.complex.faces)
    (hY : T.map v ∈ interior Y) :
    IsPLSphere m (SimplicialComplex.geometricLink T.complex {v}).space := by
  have := T.finite_faces.to_subtype
  obtain ⟨R, hR, hfin, hstars⟩ :=
    exists_isSubdivision_closedStar_subset (n := m + 1) T.complex T.continuousOn
  have := hfin.to_subtype
  have hvR := hR.singleton_mem hv
  obtain ⟨e, he, hstar⟩ := hstars v hvR
  let T' := T.subdivide R hR hfin
  have hvspace : v ∈ R.space := R.convexHull_subset_space hvR (by simp)
  have hlink := T'.isPLSphere_geometricLink_of_image_mem_nhds hvR e he hstar
    (T'.image_mem_nhds_of_mem_nhds hvspace (mem_interior_iff_mem_nhds.mp hY)
      (closedStar_mem_nhdsWithin R v))
  exact (isPLSphere_geometricLink_iff_of_isSubdivision hR hv).mp hlink

open Classical in
theorem PLPieceIn.exists_manifold_neighborhood_preserving_subcomplex {Q : Set X}
    (T : PLPieceIn E (m + 1) X Q) (A : Geometry.SimplicialComplex ℝ E)
    (hA : A.faces ⊆ T.complex.faces)
    (hAQ : T.map '' (regularNeighborhoodIn T.complex A.space).space ⊆ interior Q)
    {C : Set X} (hC : IsCompact C) (hCQ : C ⊆ interior Q) :
    ∃ P : Set X, ∃ T' : PLPieceIn E (m + 1) X P,
      ∃ L : Geometry.SimplicialComplex ℝ E,
        IsCombinatorialManifoldWithBoundary (m + 1) T'.complex ∧
          L.faces ⊆ T'.complex.faces ∧ A.faces ⊆ L.faces ∧ C ⊆ T'.map '' L.space ∧
            C ⊆ interior P ∧ P ⊆ interior Q ∧ T'.map = T.map ∧
              T'.map '' (regularNeighborhoodIn T'.complex L.space).space ⊆ interior P := by
  have := T.finite_faces.to_subtype
  have hcompact := (PiecewiseLinear.isPolyhedron_space T.complex).isCompact
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp T.continuousOn (interior Q) isOpen_interior
  let D := (regularNeighborhoodIn T.complex A.space).space
  let C' := T.complex.space ∩ T.map ⁻¹' C
  have hC' : IsCompact C' := hcompact.of_isClosed_subset
    (T.continuousOn.preimage_isClosed_of_isClosed hcompact.isClosed hC.isClosed) inter_subset_left
  have hD : IsCompact D := (PiecewiseLinear.isPolyhedron_space
    (regularNeighborhoodIn T.complex A.space)).isCompact
  have hC'O : C' ⊆ O := by
    intro x hx
    have hh : x ∈ T.map ⁻¹' interior Q ∩ T.complex.space := ⟨hCQ hx.2, hx.1⟩
    rw [hpre] at hh
    exact hh.1
  have hDO : D ⊆ O := by
    intro x hx
    have hh : x ∈ T.map ⁻¹' interior Q ∩ T.complex.space :=
      ⟨hAQ ⟨x, hx, rfl⟩, space_regularNeighborhoodIn_subset _ _ hx⟩
    rw [hpre] at hh
    exact hh.1
  have hAD : A.space ⊆ D := fun x hx =>
    mem_of_mem_nhdsWithin (space_mono_of_faces_subset hA hx)
      (regularNeighborhoodIn_mem_nhdsWithin T.complex A.space hx)
  obtain ⟨δ, hδ, hthick⟩ := (hC'.union hD).exists_cthickening_subset_open hO
    (union_subset hC'O hDO)
  let ε := δ / 4
  have hε : 0 < ε := div_pos hδ (by norm_num)
  obtain ⟨R, hR, hfinR, hAR, hfaces⟩ := exists_isSubdivision_diam_lt_preserving_subcomplex
    T.complex A hA (fun s hs => card_le_finrank_succ_of_mem_faces T.complex hs) hε
  have := hfinR.to_subtype
  let L₀ := regularNeighborhoodIn R (C' ∪ A.space)
  let L₁ := regularNeighborhoodIn R L₀.space
  have hbase : C' ∪ A.space ⊆ cthickening 0 (C' ∪ D) :=
    (union_subset subset_union_left (hAD.trans subset_union_right)).trans
      (self_subset_cthickening _)
  have hbound₀ : L₀.space ⊆ cthickening ε (C' ∪ D) := by
    simpa only [add_zero] using regularNeighborhoodIn_space_subset_cthickening R hε.le le_rfl
      hfaces subset_union_right hbase
  have hbound₁ : L₁.space ⊆ cthickening (ε + ε) (C' ∪ D) :=
    regularNeighborhoodIn_space_subset_cthickening R hε.le hε.le hfaces subset_union_right hbound₀
  have houter : (regularNeighborhoodIn R L₁.space).space ⊆ O :=
    (regularNeighborhoodIn_space_subset_cthickening R hε.le (add_nonneg hε.le hε.le)
      hfaces subset_union_right hbound₁).trans
        ((cthickening_mono (by dsimp [ε]; linarith) _).trans hthick)
  have hAL₀ : A.faces ⊆ L₀.faces := by
    intro s hs
    exact ⟨hAR hs, s, hAR hs, Finset.Subset.refl s,
      s.centroid ℝ id, s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs),
        Or.inr (A.convexHull_subset_space hs
          (s.centroid_mem_convexHull (A.nonempty_of_mem_faces hs)))⟩
  have hL₀R : L₀.faces ⊆ R.faces := fun _ hs => hs.1
  have hL₁R : L₁.faces ⊆ R.faces := fun _ hs => hs.1
  have hL₀L₁ : L₀.space ⊆ L₁.space := fun x hx =>
    mem_of_mem_nhdsWithin (space_mono_of_faces_subset hL₀R hx)
      (regularNeighborhoodIn_mem_nhdsWithin R L₀.space hx)
  have hdeep : ∀ x ∈ A.space, L₁.space ∈ 𝓝[R.space] x := fun x hx =>
    regularNeighborhoodIn_mem_nhdsWithin R L₀.space (space_mono_of_faces_subset hAL₀ hx)
  have hC'L₀ : C' ⊆ L₀.space := fun x hx =>
    mem_of_mem_nhdsWithin (hR.space_eq.symm ▸ hx.1)
      (regularNeighborhoodIn_mem_nhdsWithin R (C' ∪ A.space) (Or.inl hx))
  have hlocal : IsLocallyCombinatorialManifoldWithBoundary m R L₁.space := by
    rintro v hv ⟨s, hs, hvs, x, hxs, hxL⟩
    have hvO : v ∈ O := houter ((regularNeighborhoodIn R L₁.space).convexHull_subset_space
      ⟨hs, s, hs, Finset.Subset.refl s, x, hxs, hxL⟩ (subset_convexHull ℝ _ hvs))
    have hvK : v ∈ T.complex.space := hR.space_eq ▸ R.convexHull_subset_space hv (by simp)
    have hm : v ∈ O ∩ T.complex.space := ⟨hvO, hvK⟩
    rw [← hpre] at hm
    exact Or.inl ((T.subdivide R hR hfinR).isPLSphere_geometricLink_of_mem_interior hv hm.1)
  let N := relativeDerivedNeighborhood hAR L₁
  have hNspace : N.space = (derivedNeighborhood R L₁).space :=
    relativeDerivedNeighborhood_space hAR L₁ hL₁R hdeep
  have hman : IsCombinatorialManifoldWithBoundary (m + 1) N :=
    hlocal.relativeDerivedNeighborhood hAR L₁ hL₁R hdeep
  have hNsub := relativeDerivedNeighborhood_faces_subset hAR L₁
  have hNfin := relativeSecondDerived_faces_finite hAR
  have hNbase := relativeSecondDerived_isSubdivision hAR
  have hL₀DN : L₀.space ⊆ (derivedNeighborhood R L₁).space := fun x hx =>
    mem_of_mem_nhdsWithin (space_mono_of_faces_subset hL₀R hx)
      (derivedNeighborhood_mem_nhdsWithin hL₁R (hL₀L₁ hx))
  have hNO : N.space ⊆ O := by
    rw [hNspace]
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst
    exact ((regularNeighborhoodIn R L₁.space).convexHull_subset_space
      ⟨ht, t, ht, Finset.Subset.refl t, s.centroid ℝ id, hst,
        L₁.convexHull_subset_space hs (s.centroid_mem_convexHull (L₁.nonempty_of_mem_faces hs))⟩).trans
          houter
  let L := PiecewiseLinear.restrict N L₀.space
  have hLspace : L.space = L₀.space := by
    apply Subset.antisymm (restrict_space_subset _ _)
    intro x hx
    obtain ⟨s, hs, hxs⟩ :=
      (PiecewiseLinear.restrict (relativeSecondDerived hAR) L₀.space).mem_space_iff.mp
      ((hNbase.restrict L₀ hL₀R).space_eq.symm ▸ hx)
    exact L.convexHull_subset_space ⟨⟨hs.1, hs.2.trans hL₀DN⟩, hs.2⟩ hxs
  have hAL : A.faces ⊆ L.faces := by
    intro s hs
    have hsL₀ := L₀.convexHull_subset_space (hAL₀ hs)
    exact ⟨⟨faces_subset_relativeSecondDerived hAR hs, hsL₀.trans hL₀DN⟩, hsL₀⟩
  have hregL : (regularNeighborhoodIn N L.space).space ⊆ L₁.space := by
    have hsub : (regularNeighborhoodIn N L.space).space ⊆
        (regularNeighborhoodIn (relativeSecondDerived hAR) L.space).space := by
      intro x hx
      obtain ⟨s, ⟨hs, t, ht, hst, hmeet⟩, hxs⟩ :=
        (regularNeighborhoodIn N L.space).mem_space_iff.mp hx
      exact (regularNeighborhoodIn (relativeSecondDerived hAR) L.space).convexHull_subset_space
        ⟨hNsub hs, t, hNsub ht, hst, hmeet⟩ hxs
    have hh := hsub.trans (regularNeighborhoodIn_space_subset_of_isSubdivision hNbase L.space)
    simpa only [hLspace] using hh
  let T' := (T.subdivide (relativeSecondDerived hAR) (hNbase.trans hR) hNfin).restrict N hNsub
  have hNK : N.space ⊆ T.complex.space :=
    (relativeDerivedNeighborhood_space_subset hAR L₁).trans hR.space_eq.subset
  have hL₁interior : T.map '' L₁.space ⊆ interior (T.map '' N.space) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxK : x ∈ T.complex.space := hR.space_eq ▸ space_mono_of_faces_subset hL₁R hx
    have hxO : x ∈ O := houter (mem_of_mem_nhdsWithin
      (space_mono_of_faces_subset hL₁R hx) (regularNeighborhoodIn_mem_nhdsWithin R L₁.space hx))
    have hm : x ∈ O ∩ T.complex.space := ⟨hxO, hxK⟩
    rw [← hpre] at hm
    apply mem_interior_iff_mem_nhds.mpr
    apply T.image_mem_nhds_of_mem_nhds hxK (mem_interior_iff_mem_nhds.mp hm.1)
    rw [← hR.space_eq]
    exact relativeDerivedNeighborhood_mem_nhdsWithin hAR L₁ hL₁R hdeep hx
  have hCimage : C ⊆ T'.map '' L.space := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (interior_subset (hCQ hy))
    exact ⟨x, hLspace.symm ▸ hC'L₀ ⟨hx, hy⟩, rfl⟩
  refine ⟨T.map '' N.space, T', L, hman, restrict_faces_subset _ _, hAL, hCimage, ?_, ?_, rfl, ?_⟩
  · exact hCimage.trans ((image_mono (hLspace.subset.trans hL₀L₁)).trans hL₁interior)
  · rintro _ ⟨x, hx, rfl⟩
    have hm : x ∈ O ∩ T.complex.space := ⟨hNO hx, hNK hx⟩
    rw [← hpre] at hm
    exact hm.1
  · exact (image_mono hregL).trans hL₁interior

end DifferentialGeometry.Topology.PiecewiseLinear
