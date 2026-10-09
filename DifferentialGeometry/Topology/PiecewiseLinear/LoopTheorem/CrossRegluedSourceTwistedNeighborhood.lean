/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedCell
import DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set Topology
open DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def sideRectangle : Set (ℝ × ℝ) := Icc (-3 / 4 : ℝ) (3 / 4) ×ˢ Icc (0 : ℝ) 1

private noncomputable def sideCoordinates : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ × ℝ :=
  (((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).prod
    (LinearMap.snd ℝ (ℝ × ℝ) ℝ)).comp spliceEmbedding.symm.toLinearMap

private theorem projection_mem_frontier_iff {p : EuclideanSpace ℝ (Fin 3)} :
    halfTurnEuclideanProjection p ∈ frontier twistedStripSide ↔
      sideCoordinates p ∈ frontier sideRectangle := by
  change spliceEmbedding.symm p ∈ halfTurnProjection ⁻¹' frontier twistedStripSide ↔ _
  have hc : IsClosed sideRectangle := isClosed_Icc.prod isClosed_Icc
  rw [halfTurnProjection_preimage_frontier_twistedStripSide,
    isClosed_twistedSideLift.frontier_eq, hc.frontier_eq]
  simp only [twistedSideLift, sideRectangle, interior_prod_eq,
    interior_univ, interior_Icc, mem_sdiff, mem_prod, mem_univ, true_and]
  rfl

private theorem isPolyhedron_frontier_sideRectangle : IsPolyhedron (frontier sideRectangle) := by
  have hp (a b : ℝ) : IsPolyhedron ({a, b} : Set ℝ) := by
    simpa using (isHPolytope_singleton b).isPolyhedron.union
      (isHPolytope_singleton a).isPolyhedron
  rw [sideRectangle, frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
    frontier_Icc (by norm_num : (0 : ℝ) ≤ 1),
    frontier_Icc (by norm_num : (-3 / 4 : ℝ) ≤ 3 / 4)]
  exact (isHPolytope_Icc.isPolyhedron.prod (hp 0 1)).union
    ((hp (-3 / 4) (3 / 4)).prod isHPolytope_Icc.isPolyhedron)

theorem PLPieceIn.isPolyhedron_inter_preimage_frontier_twistedStripSide
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Set halfTurnQuotient} (T : PLPieceIn E 3 halfTurnQuotient Y) :
    IsPolyhedron (T.complex.space ∩ T.map ⁻¹' frontier twistedStripSide) := by
  have hcompact : IsCompact (T.complex.space ∩ T.map ⁻¹' frontier twistedStripSide) :=
    T.isPolyhedron_space.isCompact.of_isClosed_subset
      (T.continuousOn.preimage_isClosed_of_isClosed T.isPolyhedron_space.isClosed
        isClosed_frontier) inter_subset_left
  apply IsLocallyPolyhedral.isPolyhedron_of_isCompact _ hcompact
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin 3)) (T.map x)
  have he := chart_mem_atlas (EuclideanSpace ℝ (Fin 3)) (T.map x)
  have hxe : T.map x ∈ e.source := mem_chart_source _ _
  have hesymm : ⇑e.symm = halfTurnEuclideanProjection := halfTurnChart_symm _
  obtain ⟨ι, hι, P, A, hP, hPx⟩ := T.isPiecewiseAffineOn_chart e he x ⟨hx.1, hxe⟩
  let _ := hι
  let Q : ι → Set E := fun i =>
    P i ∩ (sideCoordinates.toAffineMap.comp (A i)) ⁻¹' frontier sideRectangle
  have hQ : ∀ i, IsPolyhedron (Q i) := fun i =>
    (hP i).1.isPolyhedron.inter_preimage isPolyhedron_frontier_sideRectangle _
  have heq (i : ι) {z : E} (hz : z ∈ P i) :
      halfTurnEuclideanProjection (A i z) = T.map z := by
    rw [← (hP i).2.2 hz]
    change halfTurnEuclideanProjection (e (T.map z)) = T.map z
    rw [← hesymm]
    exact e.left_inv ((hP i).2.1 hz).2
  refine ⟨⋃ i, Q i, IsPolyhedron.iUnion hQ, ?_, ?_⟩
  · rintro z hz
    obtain ⟨i, hz, hzbd⟩ := mem_iUnion.mp hz
    refine ⟨((hP i).2.1 hz).1, ?_⟩
    change T.map z ∈ frontier twistedStripSide
    rw [← heq i hz]
    exact projection_mem_frontier_iff.mpr hzbd
  · have hsrc : T.map ⁻¹' e.source ∈ 𝓝[T.complex.space] x :=
      (T.continuousOn x hx.1).preimage_mem_nhdsWithin (e.open_source.mem_nhds hxe)
    rw [nhdsWithin_inter_of_mem' hsrc] at hPx
    filter_upwards [nhdsWithin_mono x inter_subset_left hPx, self_mem_nhdsWithin] with z hz hzS
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨i, hzi, ?_⟩
    change sideCoordinates (A i z) ∈ frontier sideRectangle
    rw [← projection_mem_frontier_iff, heq i hzi]
    exact hzS.2

private theorem boundary_preimage_polyhedron
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Set halfTurnQuotient} (T : PLPieceIn E 3 halfTurnQuotient Y)
    (hY : Set.range twistedStripCell.boundary ⊆ Y) :
    IsPolyhedron (T.complex.space ∩ T.map ⁻¹' Set.range twistedStripCell.boundary) := by
  have hfront := twistedStripCell.isPLSphere_frontier.isPolyhedron
  have hsub : frontier twistedStripCell.domain ⊆ (⇑twistedStripCell) ⁻¹' Y :=
    fun z hz => hY ⟨⟨z, hz⟩, rfl⟩
  have hpl := T.isPiecewiseAffineOn_invFunOn_comp
    (twistedStripCell.isPLOn.mono_of_isPolyhedron hfront
      twistedStripCell.frontier_subset_domain)
  rw [inter_eq_left.mpr hsub] at hpl
  have himg := hpl.isPolyhedron_image hfront
  convert himg using 1
  ext x
  constructor
  · rintro ⟨hx, z, hz⟩
    refine ⟨z, z.property, ?_⟩
    change Function.invFunOn T.map T.complex.space (twistedStripCell z) = x
    change twistedStripCell z = T.map x at hz
    rw [hz]
    exact T.bijOn.invOn_invFunOn.1 hx
  · rintro ⟨z, hz, rfl⟩
    refine ⟨T.bijOn.surjOn.mapsTo_invFunOn (hsub hz), ?_⟩
    change T.map (Function.invFunOn T.map T.complex.space (twistedStripCell z)) ∈
      Set.range twistedStripCell.boundary
    rw [T.bijOn.invOn_invFunOn.2 (hsub hz)]
    exact ⟨⟨z, hz⟩, rfl⟩

private theorem image_mem_relative_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y Z : Set halfTurnQuotient} (T : PLPieceIn E 3 halfTurnQuotient Y)
    {x : E} (hx : x ∈ T.complex.space) (hY : Y ∈ 𝓝[Z] (T.map x))
    {A : Set E} (hA : A ∈ 𝓝[T.complex.space] x) : T.map '' A ∈ 𝓝[Z] (T.map x) := by
  obtain ⟨O, hO, hxO, hOA⟩ := mem_nhdsWithin.mp hA
  have hc := (T.isPolyhedron_space.isCompact.diff hO).image_of_continuousOn
    (T.continuousOn.mono sdiff_subset)
  have hxnot : T.map x ∉ T.map '' (T.complex.space \ O) := by
    rintro ⟨y, ⟨hy, hyO⟩, hxy⟩
    exact hyO ((T.bijOn.injOn hy hx hxy).symm ▸ hxO)
  apply Filter.mem_of_superset
    (Filter.inter_mem hY (mem_nhdsWithin_of_mem_nhds (hc.isClosed.isOpen_compl.mem_nhds hxnot)))
  rintro y ⟨hyY, hy⟩
  obtain ⟨z, hz, rfl⟩ := T.bijOn.surjOn hyY
  have hzO : z ∈ O := by
    by_contra hzO
    exact hy ⟨z, ⟨hz, hzO⟩, rfl⟩
  exact mem_image_of_mem _ (hOA ⟨hzO, hz⟩)

theorem twistedStripCell_exists_boundary_polyhedralNeighborhood :
    ∃ Y : Set halfTurnQuotient, Nonempty (PLPiece 3 halfTurnQuotient Y) ∧
      Y ⊆ frontier twistedStripSide ∧ Set.range twistedStripCell.boundary ⊆ Y ∧
      ∀ z ∈ Set.range twistedStripCell.boundary, Y ∈ 𝓝[frontier twistedStripSide] z := by
  let _ : CompactSpace (frontier twistedStripCell.domain) :=
    isCompact_iff_compactSpace.mp twistedStripCell.isPLSphere_frontier.isPolyhedron.isCompact
  let _ : Nonempty halfTurnQuotient := ⟨halfTurnProjection ((0, 0), 0)⟩
  have hC : IsCompact (Set.range twistedStripCell.boundary) :=
    isCompact_range twistedStripCell.boundary.continuous
  have hCbd : Set.range twistedStripCell.boundary ⊆ frontier twistedStripSide := by
    rw [← twistedStripCell_image_inter_frontier_side]
    exact inter_subset_right
  obtain ⟨Y, -, ⟨T⟩, hCY, -⟩ :=
    exists_pLPiece_of_isCompact (n := 3) hC isOpen_univ (subset_univ _)
  obtain ⟨P, -, -⟩ := T.piece.exists_restrict_of_isPolyhedron
    T.piece.isPolyhedron_inter_preimage_frontier_twistedStripSide inter_subset_left
  have hpiece : Nonempty (PLPiece 3 halfTurnQuotient (Y ∩ frontier twistedStripSide)) := by
    rw [← T.piece.image_inter_preimage]
    exact P.exists_pLPiece
  refine ⟨Y ∩ frontier twistedStripSide, hpiece, inter_subset_right,
    fun z hz => ⟨interior_subset (hCY hz), hCbd hz⟩, ?_⟩
  intro z hz
  exact Filter.inter_mem
    (mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp (hCY hz))) self_mem_nhdsWithin

private theorem exists_regular_neighborhood_in_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Set halfTurnQuotient} (T : PLPieceIn E 3 halfTurnQuotient Y)
    (hYbd : Y ⊆ frontier twistedStripSide)
    (hCY : Set.range twistedStripCell.boundary ⊆ Y)
    (hYnhds : ∀ z ∈ Set.range twistedStripCell.boundary, Y ∈ 𝓝[frontier twistedStripSide] z) :
    ∃ B : Set halfTurnQuotient, IsCompact B ∧ Nonempty (PLPiece 3 halfTurnQuotient B) ∧
      B ⊆ frontier twistedStripSide ∧ Set.range twistedStripCell.boundary ⊆ B ∧
      (∀ z ∈ Set.range twistedStripCell.boundary, B ∈ 𝓝[frontier twistedStripSide] z) ∧
      Nonempty (StrongDeformationRetract {z : B | (z : halfTurnQuotient) ∈
        Set.range twistedStripCell.boundary}) := by
  classical
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let A := T.complex.space ∩ T.map ⁻¹' Set.range twistedStripCell.boundary
  obtain ⟨K, hK, hKfin, hLspace⟩ := exists_isSubdivision_restrict_space T.complex
    (boundary_preimage_polyhedron T hCY) inter_subset_left
  let _ : Finite K.faces := hKfin.to_subtype
  let L := restrict K A
  have hL : L.faces ⊆ K.faces := restrict_faces_subset K A
  let N := derivedNeighborhood K L
  let P : PLPieceIn E 3 halfTurnQuotient (T.map '' N.space) :=
    (T.subdivide (secondDerived K) ((secondDerived_isSubdivision K).trans hK)
    (Set.toFinite _)).restrict N (derivedNeighborhood_faces_subset K L)
  have hNsub : N.space ⊆ T.complex.space := by
    rw [← hK.space_eq]
    exact derivedNeighborhood_space_subset K L
  have hLC : L.space = A := hLspace
  refine ⟨T.map '' N.space, P.isCompact, P.exists_pLPiece, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    exact hYbd (T.bijOn.mapsTo (hNsub hx))
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (hCY hz)
    refine ⟨x, subcomplex_space_subset_derivedNeighborhood hL ?_, rfl⟩
    rw [hLC]
    exact ⟨hx, hz⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (hCY hz)
    apply image_mem_relative_nhds T hx (hYnhds _ hz)
    rw [← hK.space_eq]
    apply derivedNeighborhood_mem_nhdsWithin hL
    rw [hLC]
    exact ⟨hx, hz⟩
  · have heq : P.homeomorph '' derivedNeighborhoodSubcomplex K L =
        {z : T.map '' N.space | (z : halfTurnQuotient) ∈
          Set.range twistedStripCell.boundary} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change T.map (x : E) ∈
          Set.range twistedStripCell.boundary
        change (x : E) ∈ L.space at hx
        exact (hLC ▸ hx : (x : E) ∈ A).2
      · intro hy
        let x := P.homeomorph.symm y
        have hxy : T.map (x : E) = y := by
          change (P.homeomorph (P.homeomorph.symm y) : halfTurnQuotient) = y
          rw [P.homeomorph.apply_symm_apply]
        refine ⟨x, ?_, P.homeomorph.apply_symm_apply y⟩
        change (x : E) ∈ L.space
        rw [hLC]
        refine ⟨hNsub x.property, ?_⟩
        change T.map (x : E) ∈ Set.range twistedStripCell.boundary
        rw [hxy]
        exact hy
    exact ⟨((derivedNeighborhoodStrongDeformationRetract hL).homeomorphImage
      P.homeomorph).congr heq⟩

theorem twistedStripCell_exists_boundary_regularNeighborhood :
    ∃ B : Set halfTurnQuotient, IsCompact B ∧ Nonempty (PLPiece 3 halfTurnQuotient B) ∧
      B ⊆ frontier twistedStripSide ∧ Set.range twistedStripCell.boundary ⊆ B ∧
      (∀ z ∈ Set.range twistedStripCell.boundary, B ∈ 𝓝[frontier twistedStripSide] z) ∧
      Nonempty (StrongDeformationRetract {z : B | (z : halfTurnQuotient) ∈
        Set.range twistedStripCell.boundary}) := by
  obtain ⟨Y, ⟨T⟩, hYbd, hCY, hYnhds⟩ :=
    twistedStripCell_exists_boundary_polyhedralNeighborhood
  exact exists_regular_neighborhood_in_piece T.piece hYbd hCY hYnhds

end DifferentialGeometry.Topology.PiecewiseLinear
