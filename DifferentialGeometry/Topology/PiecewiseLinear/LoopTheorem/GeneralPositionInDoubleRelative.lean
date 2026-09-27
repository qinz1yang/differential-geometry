/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeMesh
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
open Classical in
theorem exists_isSubdivision_injOn_starComplex_preserving_subcomplex
    [FiniteDimensional ℝ E] (K B : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hBK : B.faces ⊆ K.faces) (f : E → F)
    (hloc : IsLocallyInjective (K.space.domRestrict f)) :
    ∃ (R B' : Geometry.SimplicialComplex ℝ E), IsSubdivision R K ∧ R.faces.Finite ∧
      IsSubdivision B' B ∧ B'.faces ⊆ R.faces ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, {v} ∈ B'.faces) → s ∈ B'.faces) ∧
          ∀ v ∈ R.vertices, InjOn f (starComplex R v).space := by
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (isPolyhedron_space K).isCompact
  choose U hU hxU hUinj using hloc
  have hcover : (univ : Set K.space) ⊆ ⋃ x : K.space, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨η, hη, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨R₀, hR₀, hfinite₀, _, hdiam⟩ := exists_isSubdivision_diam_lt K
    (fun s hs => card_le_finrank_succ_of_mem_faces K hs) hη
  let _ : Finite R₀.faces := hfinite₀.to_subtype
  let B' := restrict R₀ B.space
  let A' := restrict R₀ B.spaceᶜ
  have hB' : IsSubdivision B' B := hR₀.restrict B hBK
  have hA' : A'.faces ⊆ R₀.faces := restrict_faces_subset R₀ B.spaceᶜ
  have hB'faces : B'.faces ⊆ R₀.faces := restrict_faces_subset R₀ B.space
  let _ : Finite B'.faces := (restrict_faces_finite R₀ B.space).to_subtype
  have hdis : Disjoint A'.space B'.space := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxnot : x ∉ B.space := restrict_space_subset R₀ B.spaceᶜ hxA
    exact hxnot (hB'.space_eq.symm ▸ hxB)
  obtain ⟨R, hR₁, hfinite, hAfaces, hBfaces, hface, _⟩ :=
    exists_isSubdivision_extension_of_disjoint_with_face_control
      hA' hB'faces hdis (B' := B') (IsSubdivision.refl B')
  have hR : IsSubdivision R K := hR₁.trans hR₀
  refine ⟨R, B', hR, hfinite, hB', hBfaces, hface, ?_⟩
  intro v hv
  have hvK : v ∈ K.space := hR.space_eq ▸ R.convexHull_subset_space hv (by simp)
  obtain ⟨z, hz⟩ := hleb ⟨v, hvK⟩ (mem_univ _)
  have hsub : ∀ x ∈ (starComplex R v).space,
      ∃ hx : x ∈ K.space, (⟨x, hx⟩ : K.space) ∈ U z := by
    intro x hx
    rw [starComplex_space R v hv] at hx
    have hxK : x ∈ K.space := hR.space_eq ▸ closedStar_subset_space R v hx
    refine ⟨hxK, hz ?_⟩
    obtain ⟨s, ⟨hs, hvs⟩, hxs⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hst⟩ := hR₁.exists_face_subset hs
    change dist x v < η
    exact (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      (hst hxs) (hst hvs)).trans_lt
      (hdiam t ht)
  intro x hx y hy hxy
  obtain ⟨hxK, hxU⟩ := hsub x hx
  obtain ⟨hyK, hyU⟩ := hsub y hy
  exact congrArg Subtype.val (hUinj z hxU hyU hxy)

open Classical in
theorem exists_stable_subdivision_relative_to_subcomplex_with_face_control
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K B : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hBK : B.faces ⊆ K.faces) (f : E → F)
    (hf : IsPiecewiseAffineOn f K.space)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) :
    ∃ (R B' : Geometry.SimplicialComplex ℝ E) (δ : ℝ), IsSubdivision R K ∧
      R.faces.Finite ∧ IsSubdivision B' B ∧ B'.faces ⊆ R.faces ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, {v} ∈ B'.faces) → s ∈ B'.faces) ∧
          EqOn (simplicialMap R f) f K.space ∧ 0 < δ ∧
            ∀ φ : E → F, (∀ v ∈ R.vertices, dist (φ v) (f v) < δ) →
              (∀ v ∈ R.vertices, IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
                (simplicialMap R φ '' (starComplex R v).space)) ∧
                IsLocallyInjective (R.space.domRestrict (simplicialMap R φ)) ∧
                  ∀ y : F, (R.space ∩ (simplicialMap R φ) ⁻¹' {y}).encard ≤ 2 := by
  obtain ⟨K₀, hK₀, hfinite₀, hAff⟩ := hf.exists_isSubdivision_affineOn_faces K
  let _ : Finite K₀.faces := hfinite₀.to_subtype
  let B₀ := restrict K₀ B.space
  have hB₀ : IsSubdivision B₀ B := hK₀.restrict B hBK
  have hB₀faces : B₀.faces ⊆ K₀.faces := restrict_faces_subset K₀ B.space
  have hloc₀ : IsLocallyInjective (K₀.space.domRestrict f) := by
    rwa [hK₀.space_eq]
  obtain ⟨R, B', hR₀, hfinite, hB'sub, hBfaces, hface, hstar⟩ :=
    exists_isSubdivision_injOn_starComplex_preserving_subcomplex K₀ B₀ hB₀faces f hloc₀
  have hR : IsSubdivision R K := hR₀.trans hK₀
  have hAffR : ∀ s ∈ R.faces,
      ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hR₀.exists_face_subset hs
    obtain ⟨A, hA⟩ := hAff t ht
    exact ⟨A, hA.mono hst⟩
  have : Finite R.faces := hfinite.to_subtype
  have heq : EqOn (simplicialMap R f) f R.space := by
    exact simplicialMap_eq_of_forall_affineOn R f hAffR
  have heqK : EqOn (simplicialMap R f) f K.space := by
    intro x hx
    exact heq (hR.space_eq.symm ▸ hx)
  have hfR : ContinuousOn f R.space := by
    simpa only [hR.space_eq] using hf.continuousOn
  have hcardR : ∀ y : F, (R.space ∩ f ⁻¹' {y}).encard ≤ 2 := by
    intro y
    rw [hR.space_eq]
    exact hcard y
  have hstar' : ∀ v ∈ R.vertices,
      InjOn (simplicialMap R f) (starComplex R v).space := by
    intro v hv x hx y hy hxy
    apply hstar v hv hx hy
    have hsub := space_mono_of_faces_subset (starComplex_faces_subset R v)
    rw [← heq (hsub hx), ← heq (hsub hy)]
    exact hxy
  obtain ⟨η, hη, hinj⟩ := exists_injOn_starComplex_of_small_vertex_perturbation R f hstar'
  obtain ⟨ε, hε, hbound⟩ := exists_fiber_encard_le_two_of_close_of_injOn_starComplex
    R f hfR hcardR
  let δ := min η ε
  refine ⟨R, B', δ, hR, hfinite, hB'sub.trans hB₀, hBfaces, hface, heqK,
    lt_min hη hε, ?_⟩
  intro φ hφ
  have hφclose : ∀ v ∈ R.vertices, dist (φ v) (f v) < η := by
    intro v hv
    exact (hφ v hv).trans_le (min_le_left η ε)
  have hφstar : ∀ v ∈ R.vertices, InjOn (simplicialMap R φ) (starComplex R v).space :=
    hinj φ hφclose
  have hφε : ∀ x ∈ R.space, dist (simplicialMap R φ x) (f x) < ε := by
    intro x hx
    rw [← heq (hR.space_eq ▸ hx)]
    exact dist_simplicialMap_lt_of_dist_vertices_lt R
      (fun v hv => (hφ v hv).trans_le (min_le_right η ε)) hx
  have hPL : ∀ v ∈ R.vertices,
      IsPLHomeomorphOn (simplicialMap R φ) (starComplex R v).space
        (simplicialMap R φ '' (starComplex R v).space) := by
    intro v hv
    have : Finite (starComplex R v).faces := (starComplex_faces_finite R v).to_subtype
    have hpl : IsPiecewiseAffineOn (simplicialMap R φ) (starComplex R v).space :=
      (isPiecewiseAffineOn_simplicialMap R φ).mono_of_isPolyhedron
        (isPolyhedron_space _) (space_mono_of_faces_subset (starComplex_faces_subset R v))
    obtain ⟨L, _, hspace, hPL⟩ := exists_isPLHomeomorphOn_image (starComplex R v) hpl
      (hφstar v hv)
    rwa [hspace] at hPL
  exact ⟨hPL, isLocallyInjective_of_injOn_starComplex R _ hφstar,
    hbound (simplicialMap R φ) hφε hφstar⟩

end DifferentialGeometry.Topology.PiecewiseLinear
