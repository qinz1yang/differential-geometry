/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ControlledVertexCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentBufferSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterTorusTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁] [T2Space M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem exists_section34_outer_torus_carriers
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (hH : ∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t))
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hman : IsCombinatorialManifoldWithBoundary 3 𝒦'.complex)
    (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
    (hcar : ∀ w, car w ∈ 𝒦.complex.faces)
    (hCcar : ∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆
      Section34CarrierSupport 𝒦 (car w))
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U)
    (hsmall : ∀ w, ∀ x ∈ section34GraphVertexCell 𝒦 𝒦' w,
      ∀ y ∈ section34GraphVertexCell 𝒦 𝒦' w, ∀ z ∈ section34GraphVertexCell 𝒦 𝒦' w,
        dist (h y) (h z) < ψ x)
    (ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3)
    (hct : ∀ s, ct s ∈ (plGroupoid 3).maximalAtlas M₂)
    (Sd : Section34SimplexIndex 𝒦 3 → Set E3)
    (hspine : ∀ s, IsSpine (Sd s) (ct s '' (h '' simplexRim 𝒦 s.1)))
    (hCbuffer : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident w.1 s.1 → h '' section34GraphVertexCell 𝒦 𝒦' w ⊆
        (ct s).source ∩ (ct s) ⁻¹' interior (Sd s)) :
    ∃ Q : Section34VertexIndex 𝒦 𝒦' → Set M₂,
      (∀ w, IsOpen (Q w) ∧ h '' section34GraphVertexCell 𝒦 𝒦' w ⊆ interior (Q w) ∧
        Q w ⊆ H (car w) ∧
        (∀ x ∈ section34GraphVertexCell 𝒦 𝒦' w, ∀ y ∈ Q w, ∀ z ∈ Q w,
          dist y z < ψ x) ∧
        (∀ s : Section34SimplexIndex 𝒦 3,
          (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1) ∧
        ∀ s : Section34SimplexIndex 𝒦 3,
          Section34Incident w.1 s.1 → Q w ⊆ interior (H s.1)) ∧
      Section34OuterTorus 𝒦 𝒦' h Q ct Sd := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  have hcell : ∀ w, IsPLCellOn 3 (C w) (section34GraphVertexBoundary 𝒦 𝒦' w) :=
    isPLCellOn_section34GraphVertexCell hsub hmap hman
  have hCc : ∀ w, IsCompact (C w) := fun w => (hcell w).isCompact
  have hCU : ∀ w, C w ⊆ U := fun w =>
    (section34GraphVertexCell_subset_carrierSupport w).trans
      ((locallyFinite_section34CarrierSupport 𝒦').1 w.1)
  have hCinc : ∀ w (s : Section34SimplexIndex 𝒦 3),
      (C w ∩ simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1 :=
    fun w s => section34GraphVertexCell_inter_simplexBody_nonempty_iff hsub hmap w s.2.1
  have hlf : LocallyFinite fun s : Section34SimplexIndex 𝒦 3 =>
      (Subtype.val : U → M₁) ⁻¹' simplexBody 𝒦 s.1 := by
    let f : Section34SimplexIndex 𝒦 3 → 𝒦.complex.faces := fun s => ⟨s.1, s.2.1⟩
    apply (locallyFinite_simplexBody_subtype 𝒦).comp_injective (g := f)
    intro s t hst
    exact Subtype.ext (congrArg (fun r : 𝒦.complex.faces => r.1) hst)
  have hIfin : ∀ w : Section34VertexIndex 𝒦 𝒦',
      {s : Section34SimplexIndex 𝒦 3 | Section34Incident w.1 s.1}.Finite := by
    intro w
    have hcompact : IsCompact ((Subtype.val : U → M₁) ⁻¹' C w) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (hCU w)]
      exact hCc w
    refine (hlf.finite_nonempty_inter_compact hcompact).subset ?_
    intro s hs
    obtain ⟨x, hxC, hxs⟩ := (hCinc w s).mpr hs
    exact ⟨⟨x, hCU w hxC⟩, hxs, hxC⟩
  let V : Section34VertexIndex 𝒦 𝒦' → Set M₂ := fun w =>
    ⋂ s ∈ {s : Section34SimplexIndex 𝒦 3 | Section34Incident w.1 s.1},
      (ct s).source ∩ (ct s) ⁻¹' interior (Sd s)
  have hV : ∀ w, IsOpen (V w) := fun w => (hIfin w).isOpen_biInter
    fun s _ => (ct s).isOpen_inter_preimage isOpen_interior
  have hCV : ∀ w, h '' C w ⊆ V w := fun w y hy =>
    mem_iInter₂.mpr fun s hs => hCbuffer w s hs hy
  obtain ⟨Q, hQ⟩ := exists_section34_graph_cell_carrier_neighborhoods hU hh hH C
    hCc hCU hCinc car hcar hCcar
    (fun w s => section34GraphVertexCell_subset_incident_carrierSupport hsub hmap w s.2.1)
    V hV hCV ψ hψc hsmall
  have hQbuffer : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident w.1 s.1 → Q w ⊆
        (ct s).source ∩ (ct s) ⁻¹' interior (Sd s) :=
    fun w s hs y hy => mem_iInter₂.mp ((hQ w).2.2.1 hy) s hs
  refine ⟨Q, ?_, section34OuterTorus_of_isSpine ?_ ?_ hspine ?_⟩
  · intro w
    obtain ⟨hopen, hCQ, -, hQH, hdiam, hinc, hQtri⟩ := hQ w
    exact ⟨hopen, hopen.interior_eq.symm ▸ hCQ, hQH, hdiam, hinc, hQtri⟩
  · intro s
    exact ⟨hct s, iUnion₂_subset fun w hw y hy => (hQbuffer w s hw hy).1⟩
  · intro s
    rintro _ ⟨x, hx, rfl⟩
    have hx' := (graphSkeletonSpace_inter_simplexBody_eq_simplexRim 𝒦 s).superset hx
    have hΓcov := subset_of_mem_nhdsSet
      (iUnion_section34GraphVertexCell_mem_nhdsSet hU hsub hmap)
    obtain ⟨w, hw⟩ := mem_iUnion.mp (hΓcov hx'.1)
    exact mem_iUnion₂.mpr ⟨w, (hCinc w s).mp ⟨x, hw, hx'.2⟩,
      (hQ w).2.1 (mem_image_of_mem h hw)⟩
  · intro s
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hy⟩ := mem_iUnion₂.mp hy
    exact (hQbuffer w s hw hy).2

end DifferentialGeometry.Topology.PiecewiseLinear
