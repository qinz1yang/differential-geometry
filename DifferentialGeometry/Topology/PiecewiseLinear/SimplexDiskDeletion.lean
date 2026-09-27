/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarChartDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerChart
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [dE : DecidableEq E]

open Classical in
theorem exists_isPLHomeomorphOn_eraseTriangleComplex_on_simplexBoundary
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    (R K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hR : IsSubdivision R (simplexBoundary T hT)) (hKR : K.faces ⊆ R.faces)
    (hK : IsPLBall 2 K.space) {t s : Finset E}
    (ht : t ∈ K.faces) (htcard : t.card = 3) (hs : s ∈ K.faces)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : (boundaryComplex 2 (faceStarComplex K s)).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hne : (faceStarComplex K s).space ≠ convexHull ℝ (t : Set E))
    (hinter : ∀ u ∈ K.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    {a : E} (ha : a ∈ T)
    (hPstar : (faceStarComplex K s).space ⊆ openStar (simplexBoundary T hT) a)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      h '' K.space = (eraseTriangleComplex K t).space ∧ EqOn h id Uᶜ := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  let B := simplexBoundary T hT
  let V := starComplex B a
  let O := convexHull ℝ ((T.erase a : Finset E) : Set E)
  let P := faceStarComplex K s
  let J := triangleSubcomplexIn K V.space
  let _ : Finite P.faces := (faceStarComplex_faces_finite K s).to_subtype
  let _ : Finite J.faces := (triangleSubcomplexIn_faces_finite K V.space).to_subtype
  have hP : IsPLBall 2 P.space := hK.isCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex K
      hs
  have hPV : P.space ⊆ V.space := by
    intro x hx
    have hx' := hPstar hx
    rw [openStar_simplexBoundary_eq_sdiff_boundary T hT (by omega) ha] at hx'
    exact hx'.1
  have htP : t ∈ P.faces := mem_faceStarComplex_faces_of_subset K ht hst
  have htV : convexHull ℝ (t : Set E) ⊆ V.space := (P.convexHull_subset_space htP).trans hPV
  have htJ : t ∈ J.faces := (mem_triangleSubcomplexIn_triangle_iff K V.space htcard).mpr ⟨ht, htV⟩
  have hsJ : s ∈ J.faces := J.down_closed htJ hst (K.nonempty_of_mem_faces hs)
  have hJP : faceStarComplex J s = P := faceStarComplex_triangleSubcomplexIn_eq K V.space s
    (fun u hu => exists_face_superset_card_eq_of_isPLBall P hP hu) hPV
  have hJsub := triangleSubcomplexIn_faces_subset K V.space
  have hJV : J.space ⊆ V.space := triangleSubcomplexIn_space_subset K V.space
  have hcover : ∀ u ∈ K.faces, u.card = 3 →
      convexHull ℝ (u : Set E) ⊆ V.space ∨ convexHull ℝ (u : Set E) ⊆ O := by
    intro u hu _
    obtain ⟨v, hv, huv⟩ := hR.exists_face_subset (hKR hu)
    by_cases hav : a ∈ v
    · exact Or.inl (huv.trans (V.convexHull_subset_space
        ⟨hv, by rwa [Finset.insert_eq_of_mem hav]⟩))
    · exact Or.inr (huv.trans (convexHull_mono
        (Finset.coe_subset.mpr (Finset.subset_erase.mpr ⟨hv.1, hav⟩))))
  have htO : Disjoint (convexHull ℝ (t : Set E)) O := by
    apply Set.disjoint_left.mpr
    intro x hxt hxO
    have hx := hPstar (P.convexHull_subset_space htP hxt)
    exact hx.2 ((avoidingUnion_simplexBoundary_eq_convexHull_erase T hT (by omega) ha).symm ▸ hxO)
  obtain ⟨S, f, hS, -, hf, hAff, hB, hopen⟩ :=
    exists_isPLHomeomorphOn_simplex_vertex_star_euclidean T hT (n := 1) hcard ha
  let Q := convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))
  have hQ : IsPolyhedron Q := (isHPolytope_convexHull_of_affineIndependent S hS).isPolyhedron
  have hJAff : ∀ u ∈ J.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
      EqOn f A (convexHull ℝ (u : Set E)) := by
    intro u hu
    have huR : u ∈ (restrict R V.space).faces :=
      ⟨hKR (hJsub hu), (J.convexHull_subset_space hu).trans hJV⟩
    obtain ⟨v, hv, huv⟩ := (hR.restrict V (starComplex_faces_subset B a)).exists_face_subset huR
    obtain ⟨A, hA⟩ := hAff v hv
    exact ⟨A, hA.mono huv⟩
  have htQ : f '' convexHull ℝ (t : Set E) ⊆ interior Q := by
    rw [← hopen]
    exact image_mono ((P.convexHull_subset_space htP).trans hPstar)
  obtain ⟨g, hg, hgfix, hgJ⟩ :=
    exists_isPLHomeomorphOn_eraseTriangleComplex_in_planar_chart J
      (fun u hu => exists_face_superset_card_eq_triangleSubcomplexIn K V.space hu)
      htJ htcard hsJ hst hscard (hJP.symm ▸ hP)
      (by simpa only [hJP] using htrace) (by simpa only [hJP] using hne)
      (fun u hu => hinter u (hJsub hu)) hJAff (hf.bijOn.injOn.mono hJV) isOpen_interior htQ
  have hgfixQ : EqOn g id Qᶜ := hgfix.mono (compl_subset_compl.mpr interior_subset)
  have hgQbij : BijOn g Q Q := by
    have h := ((bijOn_id Qᶜ).congr hgfixQ.symm).compl g.bijective
    simpa only [compl_compl] using h
  have hgQ : IsPLHomeomorphOn g Q Q := by
    have h := hg.restrict hQ (subset_univ Q)
    rwa [hgQbij.image_eq] at h
  have hgB : ∀ x ∈ (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space, g (f x) = f x := by
    intro x hx
    have hxB : f x ∈ frontier Q := hB ▸ (show f x ∈ f '' _ from ⟨x, hx, rfl⟩)
    exact hgfix hxB.2
  obtain ⟨h, hh, hC, hhf, hhO, hhU, -⟩ :=
    exists_isPLHomeomorphOn_extension_simplex_vertex_star_of_chart T hT (by omega) hspan ha
      hf hgQ hgB hU hTU
  have hJimage : h '' J.space = (eraseTriangleComplex J t).space := by
    have hErV : (eraseTriangleComplex J t).space ⊆ V.space :=
      (space_mono_of_faces_subset (eraseTriangleComplex_faces_subset J t)).trans hJV
    have hinv : EqOn (Function.invFunOn f V.space ∘ f) id (eraseTriangleComplex J t).space :=
      fun x hx => hf.bijOn.invOn_invFunOn.1 (hErV hx)
    calc
      h '' J.space = Function.invFunOn f V.space '' (g '' (f '' J.space)) := by
        rw [(hhf.mono hJV).image_eq]
        simp only [image_image, Function.comp_def, V, B]
      _ = Function.invFunOn f V.space '' (f '' (eraseTriangleComplex J t).space) := by rw [hgJ]
      _ = (eraseTriangleComplex J t).space := by
        rw [image_image]
        exact hinv.image_eq.trans (image_id _)
  have hOimage : h '' (K.space ∩ O) = K.space ∩ O := by
    rw [(hhO.mono inter_subset_right).image_eq, image_id]
  have hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3 :=
    fun u hu => exists_face_superset_card_eq_of_isPLBall K hK hu
  refine ⟨h, hh, hC, ?_, hhU⟩
  calc
    h '' K.space = h '' (J.space ∪ (K.space ∩ O)) :=
      congrArg (Set.image h) (space_eq_triangleSubcomplexIn_union K V.space O hpure hcover)
    _ = (eraseTriangleComplex J t).space ∪ (K.space ∩ O) := by rw [image_union, hJimage, hOimage]
    _ = (eraseTriangleComplex K t).space :=
      (eraseTriangleComplex_space_eq_triangleSubcomplexIn_union K V.space O hpure hcover htO).symm

end DifferentialGeometry.Topology.PiecewiseLinear
