/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FaceStarTrace
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexDiskDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskSubdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [dE : DecidableEq E] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_ne_face_on_simplexBoundary
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    (R K : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces]
    (hR : IsSubdivision R (simplexBoundary T hT)) (hKR : K.faces ⊆ R.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso K L φ ψ)
    (hstars : ∀ u ∈ R.faces, ∃ a ∈ (simplexBoundary T hT).vertices,
      (⋃ v ∈ u, closedStar R v) ⊆ openStar (simplexBoundary T hT) a)
    {t₀ : Finset E} (ht₀ : t₀ ∈ K.faces) (ht₀card : t₀.card = 3)
    (hne : K.space ≠ convexHull ℝ (t₀ : Set E))
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ t : Finset E, t ∈ K.faces ∧ t.card = 3 ∧ t ≠ t₀ ∧
      IsPLBall 2 (eraseTriangleComplex K t).space ∧
      ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
        h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
        h '' K.space = (eraseTriangleComplex K t).space ∧ EqOn h id Uᶜ := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  have hK := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  obtain ⟨t, s, ht, htcard, htt₀, hs, hst, hscard, htrace, hinter, hball⟩ :=
    exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar K L hIso hL ht₀ ht₀card hne
  obtain ⟨hPtrace, hPne⟩ := boundaryComplex_faceStarComplex_inter_convexHull_of_isGlueIso_planar
    hIso hL ht htcard hs hst hscard htrace
  obtain ⟨a, ha, hstar⟩ := hstars t (hKR ht)
  have haT : a ∈ T := ha.1 (Finset.mem_singleton_self a)
  have hPstar : (faceStarComplex K s).space ⊆ openStar (simplexBoundary T hT) a := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (faceStarComplex K s).mem_space_iff.mp hx
    apply hstar
    refine mem_iUnion₂.mpr ⟨v, hst hv, mem_iUnion₂.mpr ⟨u ∪ s, ⟨hKR hu.2, ?_⟩, ?_⟩⟩
    · exact subset_convexHull ℝ _ (Finset.mem_union_right _ hv)
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hxu
  obtain ⟨h, hh, hC, hD, hfix⟩ := exists_isPLHomeomorphOn_eraseTriangleComplex_on_simplexBoundary
    T hT hcard hspan R K hR hKR hK ht htcard hs hst hscard hPtrace hPne hinter haT hPstar hU hTU
  exact ⟨t, ht, htcard, htt₀, hball, h, hh, hC, hD, hfix⟩

open Classical in
theorem exists_isPLHomeomorphOn_straighten_to_face_on_simplexBoundary
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    (R K : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite L.faces]
    (hR : IsSubdivision R (simplexBoundary T hT)) (hKR : K.faces ⊆ R.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso K L φ ψ)
    (hstars : ∀ u ∈ R.faces, ∃ a ∈ (simplexBoundary T hT).vertices,
      (⋃ v ∈ u, closedStar R v) ⊆ openStar (simplexBoundary T hT) a)
    {t₀ : Finset E} (ht₀ : t₀ ∈ K.faces) (ht₀card : t₀.card = 3)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      h '' K.space = convexHull ℝ (t₀ : Set E) ∧ EqOn h id Uᶜ := by
  have hK := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  by_cases heq : K.space = convexHull ℝ (t₀ : Set E)
  · refine ⟨Homeomorph.refl E, ?_, image_id _, (image_id _).trans heq, fun _ _ => rfl⟩
    exact ⟨bijOn_id univ, isPiecewiseAffineOn_id isOpen_univ,
      (isPiecewiseAffineOn_id isOpen_univ).congr fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx⟩
  · obtain ⟨t, ht, htcard, htt₀, hball, g, hg, hgC, hgK, hgfix⟩ :=
      exists_isPLHomeomorphOn_eraseTriangleComplex_ne_face_on_simplexBoundary
        T hT hcard hspan R K L hR hKR hL hIso hstars ht₀ ht₀card heq hU hTU
    let K' := eraseTriangleComplex K t
    let L' := eraseTriangleComplex L (t.image φ)
    let _ : Finite K'.faces := (eraseTriangleComplex_faces_finite K t).to_subtype
    let _ : Finite L'.faces := (eraseTriangleComplex_faces_finite L (t.image φ)).to_subtype
    have hK'R : K'.faces ⊆ R.faces := (eraseTriangleComplex_faces_subset K t).trans hKR
    have hIso' : IsGlueIso K' L' φ ψ := hIso.eraseTriangleComplex ht
    have hL' : IsPLBall 2 L'.space := hball.of_isPLHomeomorphOn hIso'.isPLHomeomorphOn
    have ht₀' : t₀ ∈ K'.faces :=
      (mem_eraseTriangleComplex_triangle_iff K t
        (fun u hu => card_le_of_isPLBall K hK hu) ht₀card).mpr ⟨ht₀, htt₀.symm⟩
    obtain ⟨H, hH, hHC, hHK, hHfix⟩ := exists_isPLHomeomorphOn_straighten_to_face_on_simplexBoundary
      T hT hcard hspan R K' L' hR hK'R hL' hIso' hstars ht₀' ht₀card hU hTU
    refine ⟨g.trans H, hg.trans hH, ?_, ?_, ?_⟩
    · change (fun x => H (g x)) '' convexHull ℝ (T : Set E) = _
      rw [← image_image H g, hgC, hHC]
    · change (fun x => H (g x)) '' K.space = _
      rw [← image_image H g, hgK]
      exact hHK
    · intro x hx
      change H (g x) = x
      rw [hgfix hx, id_eq]
      exact hHfix hx
termination_by {u ∈ K.faces | u.card = 3}.ncard
decreasing_by
  exact ncard_triangles_eraseTriangleComplex_lt K t ht htcard (fun u hu => card_le_of_isPLBall K hK
      hu)

omit [DecidableEq (EuclideanSpace ℝ (Fin 2))] in
open Classical in
theorem exists_isPLHomeomorphOn_straighten_disk_on_simplexBoundary
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    {D : Set E} (hD : IsPLBall 2 D) (hDB : D ⊆ (simplexBoundary T hT).space)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ a ∈ T, ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      h '' D = convexHull ℝ ((T.erase a : Finset E) : Set E) ∧ EqOn h id Uᶜ := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  let B := simplexBoundary T hT
  let _ : Finite B.faces := (simplexBoundary_faces_finite T hT).to_subtype
  obtain ⟨R, K, L, φ, ψ, hR, hRfin, hKR, hKfin, hKD, hLfin, hL, hIso, hstars⟩ :=
    exists_isSubdivision_subcomplex_isGlueIso_planar B hD hDB
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKD.symm ▸ hD
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨u, hu, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t₀, ht₀, -, ht₀card⟩ := exists_face_superset_card_eq_of_isPLBall K hK hu
  obtain ⟨g, hg, hgC, hgK, hgfix⟩ := exists_isPLHomeomorphOn_straighten_to_face_on_simplexBoundary
    T hT hcard hspan R K L hR hKR hL hIso hstars ht₀ ht₀card hU hTU
  obtain ⟨v, hv, ht₀v⟩ := hR.exists_face_subset (hKR ht₀)
  have hnot : ¬T ⊆ v := fun h => hv.2.2 (Finset.Subset.antisymm hv.1 h)
  obtain ⟨a, ha, hav⟩ := Finset.not_subset.mp hnot
  let F := T.erase a
  have hF : AffineIndependent ℝ ((↑) : F → E) := affineIndependent_of_subset hT (Finset.erase_subset
      a T)
  have hFcard : F.card = 3 := by rw [Finset.card_erase_of_mem ha, hcard]
  have hFface : F ∈ B.faces := erase_mem_simplexBoundary_faces hT (by omega) ha
  have ht₀F : convexHull ℝ (t₀ : Set E) ⊆ convexHull ℝ (F : Set E) :=
    ht₀v.trans (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_erase.mpr ⟨hv.1, hav⟩)))
  let J := restrict R (convexHull ℝ (F : Set E))
  let _ : Finite J.faces := (restrict_faces_finite R _).to_subtype
  have hJspace : J.space = convexHull ℝ (F : Set E) :=
    restrict_space_of_eq_biUnion R _ (hR.convexHull_eq_biUnion hFface)
  have hJ : IsPLBall 2 J.space := hJspace.symm ▸ isPLBall_convexHull_of_affineIndependent F hF
      hFcard
  have ht₀J : t₀ ∈ J.faces := ⟨hKR ht₀, ht₀F⟩
  obtain ⟨S, hS, hScard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  obtain ⟨A, hA⟩ := exists_isPLHomeomorphOn_affine_of_card_eq hF hS (hFcard.trans hScard.symm)
  have hJAff : ∀ w ∈ J.faces, ∃ C : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
      EqOn A C (convexHull ℝ (w : Set E)) := fun _ _ => ⟨A, fun _ _ => rfl⟩
  have hAinj : InjOn A J.space := hJspace.symm ▸ hA.bijOn.injOn
  obtain ⟨L', ψ', hL'fin, -, hIso', hA', -, -⟩ := exists_isGlueIso_of_affineOn_faces J hJAff hAinj
  let _ : Finite L'.faces := hL'fin.to_subtype
  have hL' : IsPLBall 2 L'.space := hJ.of_isPLHomeomorphOn hA'
  obtain ⟨H, hH, hHC, hHJ, hHfix⟩ := exists_isPLHomeomorphOn_straighten_to_face_on_simplexBoundary
    T hT hcard hspan R J L' hR (restrict_faces_subset R _) hL' hIso' hstars ht₀J ht₀card hU hTU
  have hHinvC : H.symm '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) := by
    calc
      H.symm '' convexHull ℝ (T : Set E) = H.symm '' (H '' convexHull ℝ (T : Set E)) :=
        congrArg (Set.image H.symm) hHC.symm
      _ = _ := by rw [H.image_symm, H.injective.preimage_image]
  have hHinvD : H.symm '' convexHull ℝ (t₀ : Set E) = convexHull ℝ (F : Set E) := by
    calc
      H.symm '' convexHull ℝ (t₀ : Set E) = H.symm '' (H '' J.space) :=
        congrArg (Set.image H.symm) hHJ.symm
      _ = J.space := by rw [H.image_symm, H.injective.preimage_image]
      _ = _ := hJspace
  refine ⟨a, ha, g.trans H.symm, hg.trans hH.homeomorph_symm, ?_, ?_, ?_⟩
  · change (fun x => H.symm (g x)) '' convexHull ℝ (T : Set E) = _
    rw [← image_image H.symm g, hgC, hHinvC]
  · change (fun x => H.symm (g x)) '' D = _
    rw [← image_image H.symm g, ← hKD, hgK, hHinvD]
  · intro y hy
    change H.symm (g y) = y
    rw [hgfix hy, id_eq]
    have heq := congrArg H.symm (hHfix hy)
    simpa only [Homeomorph.symm_apply_apply, id_eq] using heq.symm

omit dP in
open Classical in
theorem exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3))) (hcard : T.card = 4)
    {D : Set (EuclideanSpace ℝ (Fin 3))} (hD : IsPLBall 2 D)
    (hDC : D ⊆ frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))))
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hTU : convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) ⊆ U) :
    ∃ a ∈ T, ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) =
        convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) ∧
      h '' D = convexHull ℝ ((T.erase a : Finset (EuclideanSpace ℝ (Fin 3))) : Set _) ∧
      EqOn h id Uᶜ := by
  have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one
    rw [Subtype.range_coe] at h
    exact h.mpr (by simpa using hcard)
  have hDB : D ⊆ (simplexBoundary T hT).space := by
    rwa [frontier_convexHull_eq_simplexBoundary hT (by simpa using hcard)] at hDC
  exact exists_isPLHomeomorphOn_straighten_disk_on_simplexBoundary T hT hcard hspan hD hDB hU hTU

end DifferentialGeometry.Topology.PiecewiseLinear
