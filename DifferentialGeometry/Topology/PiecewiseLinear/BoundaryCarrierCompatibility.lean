/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDoubleCrossingChart
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySlideVacuity

/-!
# Ambient boundary compatibility of normal singular cells
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem not_mem_interior_image_of_boundaryDoubleCrossing
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {N : Set F} {y : F}
    (hcross : HasPLBoundaryDoubleCrossingAt f P N y) : y ∉ interior (f '' P) := by
  obtain ⟨A, B, e, _, _, _, _, _, hye, _, he0, _, _, hN, _, hA, hB, _, hcover⟩ :=
    hcross.exists_openPartialHomeomorph_doublePointSet (W := univ) Filter.univ_mem
  intro hyint
  have hNnhds : N ∈ 𝓝 y := by
    filter_upwards [e.open_source.mem_nhds hye, mem_interior_iff_mem_nhds.mp hyint]
      with z hzs hz
    obtain ⟨x, hx, hxz⟩ := hz
    rcases hcover z hzs ⟨hx, hxz⟩ with hxA | hxB
    · exact (hN hzs).mp ((hA hzs).mpr ⟨x, hxA, hxz⟩).2
    · exact (hN hzs).mp ((hB hzs).mpr ⟨x, hxB, hxz⟩).2
  have hzero : (0 : ℝ × ℝ × ℝ) ∈ interior {z : ℝ × ℝ × ℝ | 0 ≤ z.1} := by
    rw [← he0]
    exact (hN.interior hye).mpr (mem_interior_iff_mem_nhds.mpr hNnhds)
  have hinterior : interior {z : ℝ × ℝ × ℝ | 0 ≤ z.1} = {z | 0 < z.1} := by
    change interior ((Prod.fst : ℝ × ℝ × ℝ → ℝ) ⁻¹' Ici 0) = _
    rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Ici]
    rfl
  rw [hinterior] at hzero
  exact lt_irrefl (0 : ℝ) hzero

private theorem not_isImage_of_mem_closure_compl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C Bd : Set X} {x : X} (hC : IsClosed C) (hx : x ∈ closure Cᶜ) (hCB : Cᶜ ⊆ Bd)
    (e : OpenPartialHomeomorph X Y) (hxe : x ∈ e.source)
    {Q : Set Y} (hQ : interior Q = ∅) : ¬e.IsImage Bd Q := by
  intro himage
  obtain ⟨z, hze, hzC⟩ := mem_closure_iff.mp hx e.source e.open_source hxe
  have hzBd : z ∈ interior Bd := interior_maximal hCB hC.isOpen_compl hzC
  have hzQ := (himage.interior hze).mpr hzBd
  rw [hQ] at hzQ
  exact hzQ

private theorem interior_slab_ends_eq_empty (r s : ℝ) :
    interior {z : ℝ × ℝ × ℝ | z.1 = r ∨ z.1 = s} = ∅ := by
  change interior ((Prod.fst : ℝ × ℝ × ℝ → ℝ) ⁻¹' ({r} ∪ {s})) = ∅
  rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst,
    interior_union_isClosed_of_interior_empty isClosed_singleton (interior_singleton s),
    interior_singleton r, preimage_empty]

namespace NormalSingularCellData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

private def of_boundary_eqOn_image (hD : NormalSingularCellData D BdM B) {Bd : Set M}
    (hBd : ∀ y ∈ D '' D.domain, y ∈ Bd ↔ y ∈ BdM) : NormalSingularCellData D Bd B where
  locallyInjective := hD.locallyInjective
  fiber_le_two := hD.fiber_le_two
  boundary_image_subset := hD.boundary_image_subset
  image_inter_boundary := by
    rw [← hD.image_inter_boundary]
    ext y
    exact and_congr_right fun hy => hBd y hy
  singularSet := {
    carrier := hD.singularSet.carrier
    piece := hD.singularSet.piece
    complex := hD.singularSet.complex
    finite_faces := hD.singularSet.finite_faces
    faces_subset := hD.singularSet.faces_subset
    isManifoldWithBoundary := hD.singularSet.isManifoldWithBoundary
    map_space := hD.singularSet.map_space
    map_boundary := by
      rw [hD.singularSet.map_boundary]
      ext y
      apply and_congr_right
      intro hy
      have hyimage : y ∈ D '' D.domain := by
        obtain ⟨x, hx, _, _, _, hxy, _⟩ := hy
        exact ⟨x, hx, hxy⟩
      exact (hBd y hyimage).symm }
  crossing := by
    intro y hy
    obtain ⟨e, he, hye, hcross⟩ := hD.crossing y hy
    refine ⟨e, he, hye, ?_⟩
    have hyimage : y ∈ D '' D.domain := by
      obtain ⟨x, hx, _, _, _, hxy, _⟩ := hy
      exact ⟨x, hx, hxy⟩
    have hmem (Q : Set M) : e y ∈ e '' (e.source ∩ Q) ↔ y ∈ Q := by
      constructor
      · rintro ⟨z, ⟨hz, hzQ⟩, hzy⟩
        exact e.injOn hz hye hzy ▸ hzQ
      · exact fun hyQ => ⟨y, ⟨hye, hyQ⟩, rfl⟩
    have hiff : e y ∈ e '' (e.source ∩ Bd) ↔ e y ∈ e '' (e.source ∩ BdM) := by
      rw [hmem, hmem]
      exact hBd y hyimage
    rcases hcross with ⟨hyBd, N, hcross⟩ | ⟨hyBd, hcross⟩
    · exact Or.inl ⟨hiff.mpr hyBd, N, hcross⟩
    · exact Or.inr ⟨fun h => hyBd (hiff.mp h), hcross⟩

theorem not_mem_interior_image_of_mem_doublePointSet_boundary
    (hD : NormalSingularCellData D BdM B) {y : M}
    (hyd : y ∈ doublePointSet D D.domain) (hyBd : y ∈ BdM) :
    y ∉ interior (D '' D.domain) := by
  obtain ⟨e, he, hye, hcross⟩ := hD.crossing y hyd
  have hyBd' : e y ∈ e '' (e.source ∩ BdM) := ⟨y, ⟨hye, hyBd⟩, rfl⟩
  obtain ⟨N, hcross⟩ : ∃ N, HasPLBoundaryDoubleCrossingAt (e ∘ D)
      (D.domain ∩ D ⁻¹' e.source) N (e y) := by
    rcases hcross with ⟨_, N, h⟩ | ⟨h, _⟩
    · exact ⟨N, h⟩
    · exact (h hyBd').elim
  intro hyint
  have hnhds : e.source ∩ D '' D.domain ∈ 𝓝 y :=
    Filter.inter_mem (e.open_source.mem_nhds hye) (mem_interior_iff_mem_nhds.mp hyint)
  have himage : (e ∘ D) '' (D.domain ∩ D ⁻¹' e.source) =
      e '' (e.source ∩ D '' D.domain) := by
    rw [image_comp, image_inter_preimage, inter_comm]
  apply not_mem_interior_image_of_boundaryDoubleCrossing hcross
  apply mem_interior_iff_mem_nhds.mpr
  rw [himage]
  exact e.image_mem_nhds hye hnhds

theorem exists_boundary_extension_not_isImage_slab_ends [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ hD' : NormalSingularCellData D (BdM ∪ (D '' D.domain)ᶜ) B,
      ∃ c' : hD'.singularSet.Branch, hD'.singularSet.IsBoundaryBranch c' ∧
        hD'.singularSet.branchCarrier c' = hD.singularSet.branchCarrier c ∧
        ∃ y ∈ hD.singularSet.branchCarrier c ∩ BdM,
          ∀ e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ), y ∈ e.source →
            ∀ r s : ℝ, ¬e.IsImage (BdM ∪ (D '' D.domain)ᶜ)
              {z : ℝ × ℝ × ℝ | z.1 = r ∨ z.1 = s} := by
  have hBd : ∀ y ∈ D '' D.domain, y ∈ BdM ∪ (D '' D.domain)ᶜ ↔ y ∈ BdM := by
    intro y hy
    simp only [mem_union, mem_compl_iff, not_true_eq_false, or_false, hy]
  let hD' := of_boundary_eqOn_image hD hBd
  let c' : hD'.singularSet.Branch := c
  have hc' : hD'.singularSet.IsBoundaryBranch c' := hc
  have hcarrier : hD'.singularSet.branchCarrier c' = hD.singularSet.branchCarrier c := rfl
  obtain ⟨y, hy, _, _, _⟩ :=
    hD.branchCarrier_inter_boundary_nontrivial_of_isBoundaryBranch hc
  refine ⟨hD', c', hc', hcarrier, y, hy, ?_⟩
  have hclosed : IsClosed (D '' D.domain) :=
    (D.isPLBall_domain.isPolyhedron.isCompact.image_of_continuousOn D.continuousOn).isClosed
  have hyclosure : y ∈ closure (D '' D.domain)ᶜ := by
    rw [closure_compl]
    exact hD.not_mem_interior_image_of_mem_doublePointSet_boundary
      (hD.singularSet.branchCarrier_subset_doublePointSet c hy.1) hy.2
  intro e hye r s
  exact not_isImage_of_mem_closure_compl hclosed hyclosure subset_union_right e hye
    (interior_slab_ends_eq_empty r s)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
