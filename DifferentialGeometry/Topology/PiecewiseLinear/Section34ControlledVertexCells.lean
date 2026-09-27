/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteGraphCutCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellCarriers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCoreComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphDualIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphImageSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

noncomputable def section34GraphVertexCell (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (w : Section34VertexIndex 𝒦 𝒦') : Set M := by
  classical
  exact 𝒦'.map '' (graphDualCell 𝒦'.complex
    (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)) (w.1.centroid ℝ id)).space

noncomputable def section34GraphVertexBoundary (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (w : Section34VertexIndex 𝒦 𝒦') : Set M := by
  classical
  exact 𝒦'.map '' (boundaryComplex 3 (graphDualCell 𝒦'.complex
    (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)) (w.1.centroid ℝ id))).space

open Classical in
theorem section34VertexIndex_eq_singleton_centroid
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U} (w : Section34VertexIndex 𝒦 𝒦') :
    w.1 = {w.1.centroid ℝ id} := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  simp only [hp, Finset.centroid_singleton, id_eq]

open Classical in
theorem singleton_centroid_mem_section34GraphCore
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U} (w : Section34VertexIndex 𝒦 𝒦') :
    {w.1.centroid ℝ id} ∈
      (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)).faces := by
  rw [← section34VertexIndex_eq_singleton_centroid w]
  exact ⟨w.2.1, fun x hx => w.2.2.2 (mem_image_of_mem _ hx)⟩

open Classical in
theorem iUnion_section34GraphVertexCell (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    (⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w) =
      𝒦'.map '' (derivedNeighborhood 𝒦'.complex
        (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦))).space := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  rw [← iUnion_graphDualCell_space 𝒦'.complex L (restrict_faces_subset _ _)]
  ext y
  constructor
  · intro hy
    obtain ⟨w, x, hx, rfl⟩ := mem_iUnion.mp hy
    exact ⟨x, mem_iUnion₂.mpr
      ⟨w.1.centroid ℝ id, singleton_centroid_mem_section34GraphCore w, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    let w : Section34VertexIndex 𝒦 𝒦' :=
      ⟨{v}, hv.1, by simp, by rintro _ ⟨z, hz, rfl⟩; exact hv.2 hz⟩
    apply mem_iUnion.mpr ⟨w, ?_⟩
    exact ⟨x, by simpa only [w, Finset.centroid_singleton, id_eq] using hxv, rfl⟩

theorem locallyFinite_section34GraphVertexCell
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, {w : Section34VertexIndex 𝒦 𝒦' |
      (section34GraphVertexCell 𝒦 𝒦' w ∩ V).Nonempty}.Finite := by
  classical
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let f : Section34VertexIndex 𝒦 𝒦' → 𝒦'.complex.vertices := fun w =>
    ⟨w.1.centroid ℝ id, (singleton_centroid_mem_section34GraphCore w).1⟩
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    rw [section34VertexIndex_eq_singleton_centroid w,
      section34VertexIndex_eq_singleton_centroid z]
    exact congrArg (fun x => ({x} : Finset Ea)) (congrArg Subtype.val hwz)
  intro x hx
  obtain ⟨V, hV, hfin⟩ := 𝒦'.locallyFinite_image_graphDualCell L x hx
  exact ⟨V, hV, hfin.preimage (f := f) hf.injOn⟩

theorem section34GraphVertexCell_subset_carrierSupport
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U} (w : Section34VertexIndex 𝒦 𝒦') :
    section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦' w.1 := by
  classical
  have hv := (singleton_centroid_mem_section34GraphCore w).1
  have h := image_graphDualCell_subset_section34CarrierSupport
    (IsSubdivision.refl 𝒦'.complex) rfl
    (restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)) hv hv
    (subset_convexHull ℝ _ (Finset.mem_singleton_self _))
  simpa only [section34GraphVertexCell,
    ← section34VertexIndex_eq_singleton_centroid w] using h

theorem simplexBody_subset_section34GraphVertexCell
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U} (w : Section34VertexIndex 𝒦 𝒦') :
    simplexBody 𝒦' w.1 ⊆ section34GraphVertexCell 𝒦 𝒦' w := by
  classical
  have hv := singleton_centroid_mem_section34GraphCore w
  rintro y ⟨x, hx, rfl⟩
  rw [section34VertexIndex_eq_singleton_centroid w, Finset.coe_singleton,
    convexHull_singleton, mem_singleton_iff] at hx
  rw [hx]
  exact mem_image_of_mem _ (mem_graphDualCell_space_of_singleton_mem _ _
    (restrict_faces_subset _ _) hv)

theorem isPLCellOn_section34GraphVertexCell [FiniteDimensional ℝ Ea]
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦'.complex)
    (w : Section34VertexIndex 𝒦 𝒦') :
    IsPLCellOn 3 (section34GraphVertexCell 𝒦 𝒦' w)
      (section34GraphVertexBoundary 𝒦 𝒦' w) := by
  classical
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  exact 𝒦'.isPLCellOn_graphDualCell _ hK (restrict_faces_subset _ _)
    (fun s hs => hcore.card_le
      (fun t ht => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp ht).2) hs)
    (singleton_centroid_mem_section34GraphCore w)

theorem iUnion_section34GraphVertexCell_mem_nhdsSet
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (hmap : 𝒦'.map = 𝒦.map) :
    (⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w) ∈
      nhdsSet (graphSkeletonSpace 𝒦) := by
  classical
  rw [iUnion_section34GraphVertexCell]
  have h := 𝒦'.image_derivedNeighborhood_mem_nhdsSet hU
    (restrict_faces_subset 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦))
  rw [(isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq,
    hmap, image_restrict_preimage_graphSkeletonSpace] at h
  simpa only [hmap] using h

theorem section34GraphVertexCell_inter_simplexBody_nonempty_iff
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w : Section34VertexIndex 𝒦 𝒦') {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    (section34GraphVertexCell 𝒦 𝒦' w ∩ simplexBody 𝒦 t).Nonempty ↔
      Section34Incident w.1 t := by
  classical
  have h := image_graphDualCell_inter_simplexBody_nonempty_iff hsub hmap _
    (restrict_faces_subset _ _) (singleton_centroid_mem_section34GraphCore w) ht
  change _ ↔ (w.1 : Set Ea) ⊆ convexHull ℝ (t : Set Ea)
  rw [section34VertexIndex_eq_singleton_centroid w, Finset.coe_singleton,
    singleton_subset_iff]
  exact h

theorem section34GraphVertexCell_subset_incident_carrierSupport
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w : Section34VertexIndex 𝒦 𝒦') {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces)
    (hwt : Section34Incident w.1 t) :
    section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦 t := by
  classical
  apply image_graphDualCell_subset_section34CarrierSupport hsub hmap _
    (singleton_centroid_mem_section34GraphCore w).1 ht
  apply hwt
  rw [section34VertexIndex_eq_singleton_centroid w, Finset.coe_singleton]
  simp only [Finset.centroid_singleton, id_eq, mem_singleton_iff]

theorem exists_section34_controlled_graph_vertex_cells [FiniteDimensional ℝ Ea] [T2Space M]
    {M₂ : Type u} [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    {h : M → M₂} {W : Set M} (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (H : Finset Ea → Set M₂)
    (hH : ∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t))
    (hW : IsOpen W) (hΓW : graphSkeletonSpace 𝒦 ⊆ W)
    (ψ : M → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
      IsCombinatorialManifold 3 𝒦'.complex ∧
      (∀ w, IsPLCellOn 3 (section34GraphVertexCell 𝒦 𝒦' w)
        (section34GraphVertexBoundary 𝒦 𝒦' w)) ∧
      (⋃ w, section34GraphVertexCell 𝒦 𝒦' w) ∈ nhdsSet (graphSkeletonSpace 𝒦) ∧
      (⋃ w, section34GraphVertexCell 𝒦 𝒦' w) ⊆ W ∧
      (∀ x ∈ U, ∃ V ∈ 𝓝 x, {w : Section34VertexIndex 𝒦 𝒦' |
        (section34GraphVertexCell 𝒦 𝒦' w ∩ V).Nonempty}.Finite) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ section34GraphVertexCell 𝒦 𝒦' w) ∧
      (∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦' w.1) ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w)) ∧
      (∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
      ∀ w, IsOpen (Q w) ∧ h '' section34GraphVertexCell 𝒦 𝒦' w ⊆ interior (Q w) ∧
        Q w ⊆ H (car w) ∧
        (∀ x ∈ section34GraphVertexCell 𝒦 𝒦' w, ∀ y ∈ Q w, ∀ z ∈ Q w,
          dist y z < ψ x) ∧
        (∀ s : Section34SimplexIndex 𝒦 3,
          (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty ↔ Section34Incident w.1 s.1) ∧
        ∀ s : Section34SimplexIndex 𝒦 3,
          Section34Incident w.1 s.1 → Q w ⊆ interior (H s.1) := by
  classical
  obtain ⟨𝒦', car, hsub, hmap, hman, hcar, hbody, hsupp, hfinite, hW', hsmall⟩ :=
    exists_graph_subdivision_with_image_diameter_control hU 𝒦 h𝒦 hW hΓW
      (continuousOn_iff_continuous_domRestrict.mpr hh.continuous) ψ hψc hψpos
  let C := section34GraphVertexCell 𝒦 𝒦'
  have hcell : ∀ w, IsPLCellOn 3 (C w) (section34GraphVertexBoundary 𝒦 𝒦' w) :=
    isPLCellOn_section34GraphVertexCell hsub hmap hman.isCombinatorialManifoldWithBoundary
  have hCsupp : ∀ w, C w ⊆ Section34CarrierSupport 𝒦' w.1 :=
    section34GraphVertexCell_subset_carrierSupport
  have hCU : ∀ w, C w ⊆ U := fun w =>
    (hCsupp w).trans ((locallyFinite_section34CarrierSupport 𝒦').1 w.1)
  have hCcar : ∀ w, C w ⊆ Section34CarrierSupport 𝒦 (car w) :=
    fun w => (hCsupp w).trans (hsupp w)
  obtain ⟨Q, hQ⟩ := exists_section34_graph_cell_carrier_neighborhoods hU hh hH C
    (fun w => (hcell w).isCompact) hCU
    (fun w s => section34GraphVertexCell_inter_simplexBody_nonempty_iff hsub hmap w s.2.1)
    car hcar hCcar
    (fun w s => section34GraphVertexCell_subset_incident_carrierSupport hsub hmap w s.2.1)
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ => subset_univ _) ψ hψc
    (fun w x hx y hy z hz => hsmall w.1 w.2.1 x (hCsupp w hx) y (hCsupp w hy)
      z (hCsupp w hz))
  refine ⟨𝒦', car, Q, hsub, hmap, hman, hcell,
    iUnion_section34GraphVertexCell_mem_nhdsSet hU hsub hmap,
    iUnion_subset (fun w => (hCsupp w).trans (hW' w)),
    locallyFinite_section34GraphVertexCell 𝒦 𝒦', simplexBody_subset_section34GraphVertexCell,
    hCsupp, hcar, hbody, hCcar, hfinite, ?_⟩
  intro w
  obtain ⟨hopen, hCQ, _, hQH, hdiam, hinc, hQtri⟩ := hQ w
  exact ⟨hopen, hopen.interior_eq.symm ▸ hCQ, hQH, hdiam, hinc, hQtri⟩

end DifferentialGeometry.Topology.PiecewiseLinear
