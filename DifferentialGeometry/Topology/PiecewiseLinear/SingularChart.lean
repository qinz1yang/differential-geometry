/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Analysis.Calculus.Compactness.Superposition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_small_map_doublePointSet_normal_form_in_halfSpace_chart [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (e : OpenPartialHomeomorph F F)
    (he : IsPiecewiseAffineOn e e.source) (f : E → F) (hf : IsPiecewiseAffineOn f K.space)
    (hsource : MapsTo f K.space e.source) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2)
    (hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (e (f x)))
    (hboundary : ∀ x ∈ (boundaryComplex 2 K).space, ℓ (e (f x)) = 0) {ε : ℝ} (hε : 0 < ε) :
    let M := e.symm '' (e.target ∩ {y : F | 0 ≤ ℓ y})
    let B := e.symm '' (e.target ∩ {y : F | ℓ y = 0})
    ∃ (R : Geometry.SimplicialComplex ℝ E) (g : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn g K.space ∧
        (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧ MapsTo g K.space e.source ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn g (starComplex R v).space (g '' (starComplex R
              v).space)) ∧
            IsLocallyInjective (K.space.domRestrict g) ∧
              (∀ y : F, (K.space ∩ g ⁻¹' {y}).encard ≤ 2) ∧ MapsTo g K.space M ∧
                (∀ x ∈ K.space, g x ∈ B ↔ x ∈ (boundaryComplex 2 K).space) ∧
                  G.faces.Finite ∧ G.space = doublePointSet g K.space ∧
                    IsCombinatorialManifoldWithBoundary 1 G ∧
                      (∀ y ∈ G.space, (y ∈ B ∧ HasPLBoundaryDoubleCrossingAt g K.space M y) ∨
                        (y ∉ B ∧ HasPLDoubleCrossingAt g K.space y)) ∧
                          (boundaryComplex 1 G).space = G.space ∩ B := by
  dsimp only
  have hdomain : K.space ∩ f ⁻¹' e.source = K.space := inter_eq_left.mpr hsource
  have hpl := he.comp hf
  rw [hdomain] at hpl
  have hlocal : IsLocallyInjective (K.space.domRestrict (e ∘ f)) := by
    intro x
    obtain ⟨U, hU, hxU, hUinj⟩ := hloc x
    refine ⟨U, hU, hxU, fun y hy z hz hyz => hUinj hy hz ?_⟩
    exact e.injOn (hsource y.property) (hsource z.property) hyz
  have hfib : ∀ y : F, (K.space ∩ (e ∘ f) ⁻¹' {y}).encard ≤ 2 := by
    intro y
    by_cases hy : y ∈ e.target
    · apply (encard_le_encard (s := K.space ∩ (e ∘ f) ⁻¹' {y})
        (t := K.space ∩ f ⁻¹' {e.symm y}) ?_).trans (hcard (e.symm y))
      rintro x ⟨hx, hxy⟩
      refine ⟨hx, ?_⟩
      change f x = e.symm y
      exact e.injOn (hsource hx) (e.map_target hy) ((show e (f x) = y from hxy).trans (e.right_inv
          hy).symm)
    · have hempty : K.space ∩ (e ∘ f) ⁻¹' {y} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxy⟩
        exact hy ((show e (f x) = y from hxy) ▸ e.map_source (hsource hx))
      rw [hempty, encard_empty]
      exact bot_le
  have : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  obtain ⟨δ, hδ, hδinv⟩ := DifferentialGeometry.Analysis.exists_uniform_superposition_radius
    (continuousOn_iff_continuous_domRestrict.mp hpl.continuousOn) e.open_target
    (by rintro y ⟨x, rfl⟩; exact e.map_source (hsource x.property)) e.continuousOn_symm hε
  obtain ⟨R, φ, H, hR, hfinite, hgpl, hgclose, hgstar, _, hgcard, hgnonneg, hgboundary,
      hHfinite, hHspace, hHman, hHcross, _, _, hHboundary⟩ :=
    exists_small_simplicialMap_doublePointSet_with_boundary_in_halfSpace
      K hK hdim ℓ hℓ (e ∘ f) hpl hlocal hfib hnonneg hboundary hδ
  have : Finite R.faces := hfinite.to_subtype
  have : Finite H.faces := hHfinite.to_subtype
  let u := simplicialMap R φ
  let g := e.symm ∘ u
  have hu : MapsTo u K.space e.target := fun x hx => (hδinv ⟨x, hx⟩ (u x) (hgclose x hx)).1
  have hclose : ∀ x ∈ K.space, dist (g x) (f x) < ε := by
    intro x hx
    have h := (hδinv ⟨x, hx⟩ (u x) (hgclose x hx)).2
    change dist (e.symm (u x)) (e.symm (e (f x))) < ε at h
    rw [e.left_inv (hsource hx)] at h
    exact h
  have hgsource : MapsTo g K.space e.source := fun x hx => e.map_target (hu hx)
  have hgd : K.space ∩ u ⁻¹' e.target = K.space := inter_eq_left.mpr hu
  have hgPL : IsPiecewiseAffineOn g K.space := by
    have h := he.symm.comp hgpl
    rwa [hgd] at h
  have hstar : ∀ v ∈ R.vertices,
      IsPLHomeomorphOn g (starComplex R v).space (g '' (starComplex R v).space) := by
    intro v hv
    have hsub : u '' (starComplex R v).space ⊆ e.target := by
      rintro y ⟨x, hx, rfl⟩
      exact hu (hR.space_eq ▸ (space_mono_of_faces_subset (starComplex_faces_subset R v) hx))
    simpa only [g, image_image, Function.comp_def] using (hgstar v
        hv).postcomp_openPartialHomeomorph e.symm he.symm hsub
  have hglocal : IsLocallyInjective (K.space.domRestrict g) := by
    have h := isLocallyInjective_of_injOn_starComplex R g fun v hv => (hstar v hv).bijOn.injOn
    rwa [hR.space_eq] at h
  have hgCard : ∀ y : F, (K.space ∩ g ⁻¹' {y}).encard ≤ 2 := by
    intro y
    by_cases hy : y ∈ e.source
    · apply (encard_le_encard (s := K.space ∩ g ⁻¹' {y})
        (t := K.space ∩ u ⁻¹' {e y}) ?_).trans (hgcard (e y))
      rintro x ⟨hx, hxy⟩
      refine ⟨hx, ?_⟩
      change u x = e y
      exact e.symm.injOn (hu hx) (e.map_source hy) ((show e.symm (u x) = y from hxy).trans
          (e.left_inv hy).symm)
    · have hempty : K.space ∩ g ⁻¹' {y} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxy⟩
        exact hy ((show g x = y from hxy) ▸ hgsource hx)
      rw [hempty, encard_empty]
      exact bot_le
  have hmemZero : ∀ z ∈ e.target,
      e.symm z ∈ e.symm '' (e.target ∩ {y : F | ℓ y = 0}) ↔ ℓ z = 0 := by
    intro z hz
    constructor
    · rintro ⟨w, ⟨hw, hw0⟩, hwz⟩
      exact e.symm.injOn hw hz hwz ▸ hw0
    · intro hz0
      exact ⟨z, ⟨hz, hz0⟩, rfl⟩
  have hgM : MapsTo g K.space (e.symm '' (e.target ∩ {y : F | 0 ≤ ℓ y})) :=
    fun x hx => ⟨u x, ⟨hu hx, hgnonneg x hx⟩, rfl⟩
  have hgBoundary : ∀ x ∈ K.space,
      g x ∈ e.symm '' (e.target ∩ {y : F | ℓ y = 0}) ↔ x ∈ (boundaryComplex 2 K).space := by
    intro x hx
    exact (hmemZero (u x) (hu hx)).trans (hgboundary x hx)
  obtain ⟨G, hGfinite, hGspace, hGman, hGboundary, _⟩ :=
    exists_triangulation_doublePointSet_comp_of_isPLHomeomorphOn H hHman u K.space hHspace
      (isPLHomeomorphOn_openPartialHomeomorph e.symm he.symm) hu
  have hspaceImage : G.space = e.symm '' H.space := by
    rw [hGspace, doublePointSet_comp_of_injOn u e.symm K.space
      (e.symm.injOn.mono (image_subset_iff.mpr hu)), ← hHspace]
  refine ⟨R, g, G, hR, hfinite, hgPL, hclose, hgsource, hstar, hglocal, hgCard, hgM,
    hgBoundary, hGfinite, hGspace, hGman, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hspaceImage ▸ hy
    have hzt : z ∈ e.target := by
      obtain ⟨a, ha, b, _, _, haz, _⟩ := hHspace ▸ hz
      exact haz ▸ hu ha
    rcases hHcross z hz with ⟨hz0, hzcross⟩ | ⟨hzpos, hzcross⟩
    · exact Or.inl ⟨(hmemZero z hzt).mpr hz0,
        hzcross.postcomp_openPartialHomeomorph e.symm he.symm hu⟩
    · exact Or.inr ⟨fun hz0 => (ne_of_gt hzpos) ((hmemZero z hzt).mp hz0),
        hzcross.postcomp_openPartialHomeomorph e.symm he.symm hu⟩
  · rw [hGboundary, hHboundary, hspaceImage]
    ext y
    constructor
    · rintro ⟨z, ⟨hzH, hz0⟩, rfl⟩
      have hzt : z ∈ e.target := by
        obtain ⟨a, ha, b, _, _, haz, _⟩ := hHspace ▸ hzH
        exact haz ▸ hu ha
      exact ⟨⟨z, hzH, rfl⟩, (hmemZero z hzt).mpr hz0⟩
    · rintro ⟨⟨z, hzH, rfl⟩, hz0⟩
      have hzt : z ∈ e.target := by
        obtain ⟨a, ha, b, _, _, haz, _⟩ := hHspace ▸ hzH
        exact haz ▸ hu ha
      exact ⟨z, ⟨hzH, (hmemZero z hzt).mp hz0⟩, rfl⟩

open Classical in
theorem exists_small_map_doublePointSet_normal_form_in_boundary_chart [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (e : OpenPartialHomeomorph F F)
    (he : IsPiecewiseAffineOn e e.source) (M Bd B : Set F)
    (hM : ∀ y ∈ e.source, y ∈ M ↔ 0 ≤ ℓ (e y))
    (hBd : ∀ y ∈ e.source, y ∈ Bd ↔ ℓ (e y) = 0)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hsource : MapsTo f K.space e.source)
    (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ y : F, (K.space ∩ f ⁻¹' {y}).encard ≤ 2) (hfM : MapsTo f K.space M)
    (hfBd : MapsTo f (boundaryComplex 2 K).space Bd)
    (hB : ∀ x ∈ (boundaryComplex 2 K).space, B ∈ 𝓝[Bd] (f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (g : E → F) (G : Geometry.SimplicialComplex ℝ F),
      IsSubdivision R K ∧ R.faces.Finite ∧ IsPiecewiseAffineOn g K.space ∧
        (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧ MapsTo g K.space e.source ∧
          (∀ v ∈ R.vertices, IsPLHomeomorphOn g (starComplex R v).space (g '' (starComplex R
              v).space)) ∧
            IsLocallyInjective (K.space.domRestrict g) ∧
              (∀ y : F, (K.space ∩ g ⁻¹' {y}).encard ≤ 2) ∧ MapsTo g K.space M ∧
                (∀ x ∈ K.space, g x ∈ Bd ↔ x ∈ (boundaryComplex 2 K).space) ∧
                  G.faces.Finite ∧ G.space = doublePointSet g K.space ∧
                    IsCombinatorialManifoldWithBoundary 1 G ∧
                      (∀ y ∈ G.space, (y ∈ Bd ∧ HasPLBoundaryDoubleCrossingAt g K.space M y) ∨
                        (y ∉ Bd ∧ HasPLDoubleCrossingAt g K.space y)) ∧
                          (boundaryComplex 1 G).space = G.space ∩ Bd ∧
                            MapsTo g (boundaryComplex 2 K).space B ∧ G.space ∩ Bd ⊆ B := by
  have : Finite (boundaryComplex 2 K).faces :=
    ((Set.toFinite K.faces).subset (boundaryComplex_faces_subset 2 K)).to_subtype
  let C := f '' (boundaryComplex 2 K).space
  have hC : IsCompact C := (isPolyhedron_space (boundaryComplex 2
      K)).isCompact.image_of_continuousOn
    (hf.continuousOn.mono (boundaryComplex_space_subset 2 K))
  let U := interior (B ∪ Bdᶜ)
  have hCU : C ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨W, hW, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hB x hx)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset hW
    intro z hz
    by_cases hzBd : z ∈ Bd
    · exact Or.inl (hWsub ⟨hz, hzBd⟩)
    · exact Or.inr hzBd
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_cthickening_subset_open isOpen_interior hCU
  have hnonneg : ∀ x ∈ K.space, 0 ≤ ℓ (e (f x)) := fun x hx => (hM (f x) (hsource hx)).mp (hfM hx)
  have hboundary : ∀ x ∈ (boundaryComplex 2 K).space, ℓ (e (f x)) = 0 :=
    fun x hx => (hBd (f x) (hsource (boundaryComplex_space_subset 2 K hx))).mp (hfBd hx)
  obtain ⟨R, g, G, hR, hfinite, hgPL, hgclose, hgsource, hgstar, hgloc, hgcard, hgM, hgbd,
      hGfinite, hGspace, hGman, hGcross, hGboundary⟩ :=
    exists_small_map_doublePointSet_normal_form_in_halfSpace_chart K hK hdim ℓ hℓ e he f hf
      hsource hloc hcard hnonneg hboundary (lt_min hε hδ)
  have hMimage : e.symm '' (e.target ∩ {y : F | 0 ≤ ℓ y}) = e.source ∩ M := by
    have h := e.symm.image_source_inter_eq' {y : F | 0 ≤ ℓ y}
    change e.symm '' (e.target ∩ {y : F | 0 ≤ ℓ y}) = e.source ∩ e ⁻¹' {y : F | 0 ≤ ℓ y} at h
    rw [h]
    ext y
    exact ⟨fun hy => ⟨hy.1, (hM y hy.1).mpr hy.2⟩, fun hy => ⟨hy.1, (hM y hy.1).mp hy.2⟩⟩
  have hBdimage : e.symm '' (e.target ∩ {y : F | ℓ y = 0}) = e.source ∩ Bd := by
    have h := e.symm.image_source_inter_eq' {y : F | ℓ y = 0}
    change e.symm '' (e.target ∩ {y : F | ℓ y = 0}) = e.source ∩ e ⁻¹' {y : F | ℓ y = 0} at h
    rw [h]
    ext y
    exact ⟨fun hy => ⟨hy.1, (hBd y hy.1).mpr hy.2⟩, fun hy => ⟨hy.1, (hBd y hy.1).mp hy.2⟩⟩
  rw [hMimage] at hgM hGcross
  rw [hBdimage] at hgbd hGcross hGboundary
  have hgBoundary : ∀ x ∈ K.space, g x ∈ Bd ↔ x ∈ (boundaryComplex 2 K).space := by
    intro x hx
    simpa only [mem_inter_iff, hgsource hx, true_and] using hgbd x hx
  have hGsource : G.space ⊆ e.source := by
    intro y hy
    obtain ⟨x, hx, z, _, _, hxy, _⟩ := hGspace ▸ hy
    exact hxy ▸ hgsource hx
  have hgB : MapsTo g (boundaryComplex 2 K).space B := by
    intro x hx
    have hxK := boundaryComplex_space_subset 2 K hx
    have hmem := interior_subset (hthick (mem_cthickening_of_dist_le
      (g x) (f x) δ C ⟨x, hx, rfl⟩ ((hgclose x hxK).trans_le (min_le_right ε δ)).le))
    exact hmem.resolve_right (fun hnot => hnot ((hgBoundary x hxK).mpr hx))
  refine ⟨R, g, G, hR, hfinite, hgPL, fun x hx => (hgclose x hx).trans_le (min_le_left ε δ),
    hgsource, hgstar, hgloc, hgcard, fun x hx => (hgM hx).2, hgBoundary, hGfinite, hGspace, hGman,
        ?_, ?_, hgB, ?_⟩
  · intro y hy
    rcases hGcross y hy with ⟨hyBd, hcross⟩ | ⟨hyBd, hcross⟩
    · refine Or.inl ⟨hyBd.2, hcross.congr_target ?_⟩
      filter_upwards [e.open_source.mem_nhds (hGsource hy)] with z hz
      exact and_iff_right hz
    · exact Or.inr ⟨fun hy0 => hyBd ⟨hGsource hy, hy0⟩, hcross⟩
  · rw [hGboundary]
    ext y
    exact ⟨fun hy => ⟨hy.1, hy.2.2⟩, fun hy => ⟨hy.1, hGsource hy.1, hy.2⟩⟩
  · rintro y ⟨hyG, hyBd⟩
    obtain ⟨x, hx, z, _, _, hxy, _⟩ := hGspace ▸ hyG
    exact hxy ▸ hgB ((hgBoundary x hx).mp (hxy.symm ▸ hyBd))

end DifferentialGeometry.Topology.PiecewiseLinear
