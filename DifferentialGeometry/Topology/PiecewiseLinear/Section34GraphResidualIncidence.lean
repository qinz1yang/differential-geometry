/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem section34GraphResidualCell_mono_of_incident {s t : Finset Ea}
    (hst : Section34Incident s t) :
    section34GraphResidualCell 𝒦 𝒦' s ⊆ section34GraphResidualCell 𝒦 𝒦' t := by
  apply closure_mono
  apply sdiff_subset_sdiff_left
  exact image_mono (convexHull_min hst (convex_convexHull ℝ (t : Set Ea)))

variable [T2Space M]

theorem section34GraphResidualCell_subset_carrierSupport {t : Finset Ea}
    (ht : t ∈ 𝒦.complex.faces) :
    section34GraphResidualCell 𝒦 𝒦' t ⊆ Section34CarrierSupport 𝒦 t := by
  obtain ⟨a, ha⟩ := 𝒦.complex.nonempty_of_mem_faces ht
  intro x hx
  exact mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr
    ⟨t, ⟨ht, ha⟩, section34GraphResidualCell_subset_simplexBody ht hx⟩⟩

theorem section34GraphResidualCell_inter_vertex_eq_empty_of_not_incident
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (w : Section34VertexIndex 𝒦 𝒦')
    (hnot : ¬ Section34Incident w.1 t) :
    section34GraphResidualCell 𝒦 𝒦' t ∩ section34GraphVertexCell 𝒦 𝒦' w = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxR, hxC⟩
  exact hnot ((section34GraphVertexCell_inter_simplexBody_nonempty_iff hsub hmap w ht).mp
    ⟨x, hxC, section34GraphResidualCell_subset_simplexBody ht hxR⟩)

theorem section34GraphResidualCell_inter_split_eq_empty_of_not_incident
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (e : Section34EdgeIndex 𝒦 𝒦')
    (hnot : ¬ Section34Incident e.1 t) :
    section34GraphResidualCell 𝒦 𝒦' t ∩ section34GraphSplitCell 𝒦 𝒦' e = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxR, hxC⟩
  exact hnot ((section34GraphSplitCell_inter_simplexBody_nonempty_iff hsub hmap e ht).mp
    ⟨x, hxC, section34GraphResidualCell_subset_simplexBody ht hxR⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
