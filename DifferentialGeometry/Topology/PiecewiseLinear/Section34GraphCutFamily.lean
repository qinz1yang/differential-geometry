/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualIncidence

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

noncomputable def section34GraphCutFamily (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    Section34CutLabelOf 𝒦 𝒦' → Set M
  | .vertexBall w => section34GraphVertexCell 𝒦 𝒦' w
  | .tetraBall t => section34GraphResidualCell 𝒦 𝒦' t.1
  | .splitDisk e => section34GraphSplitCell 𝒦 𝒦' e
  | .faceDisk s => section34GraphResidualCell 𝒦 𝒦' s.1
  | .patch x => section34GraphResidualCell 𝒦 𝒦' x.1.1.1 ∩
      section34GraphVertexCell 𝒦 𝒦' x.1.2
  | .faceArc a => section34GraphVertexCell 𝒦 𝒦' a.1.2 ∩
      section34GraphResidualCell 𝒦 𝒦' a.1.1.1
  | .edgeArc i => section34GraphResidualCell 𝒦 𝒦' i.1.1.1 ∩
      section34GraphSplitCell 𝒦 𝒦' i.1.2
  | .markedPoint p => section34GraphSplitCell 𝒦 𝒦' p.1.2 ∩
      section34GraphResidualCell 𝒦 𝒦' p.1.1.1

variable [T2Space M] {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

private theorem section34GraphCutFamily_subset (l : Section34CutLabelOf 𝒦 𝒦') :
    section34GraphCutFamily 𝒦 𝒦' l ⊆ U := by
  have hV : ∀ w, section34GraphVertexCell 𝒦 𝒦' w ⊆ U := fun w =>
    (section34GraphVertexCell_subset_carrierSupport w).trans
      ((locallyFinite_section34CarrierSupport 𝒦').1 w.1)
  have hE : ∀ e, section34GraphSplitCell 𝒦 𝒦' e ⊆ U := by
    intro e
    rintro _ ⟨x, hx, rfl⟩
    exact 𝒦'.bijOn.mapsTo (splittingDisk_space_subset 𝒦'.complex e.2.1 hx)
  cases l with
  | vertexBall w => exact hV w
  | tetraBall t => exact section34GraphResidualCell_subset t.2.1
  | splitDisk e => exact hE e
  | faceDisk s => exact section34GraphResidualCell_subset s.2.1
  | patch x => exact inter_subset_left.trans (section34GraphResidualCell_subset x.1.1.2.1)
  | faceArc a => exact inter_subset_left.trans (hV a.1.2)
  | edgeArc i => exact inter_subset_right.trans (hE i.1.2)
  | markedPoint p => exact inter_subset_left.trans (hE p.1.2)

private theorem locallyFinite_section34GraphCutFamily
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, {l : Section34CutLabelOf 𝒦 𝒦' |
      (section34GraphCutFamily 𝒦 𝒦' l ∩ V).Nonempty}.Finite := by
  classical
  intro x hx
  obtain ⟨Vv, hVv, hfv⟩ := locallyFinite_section34GraphVertexCell 𝒦 𝒦' x hx
  obtain ⟨Ve, hVe, hfe⟩ := locallyFinite_section34GraphSplitCell 𝒦 𝒦' x hx
  obtain ⟨Vf, hVf, hff⟩ := locallyFinite_section34GraphResidualCell 𝒦 𝒦' 3 x hx
  obtain ⟨Vt, hVt, hft⟩ := locallyFinite_section34GraphResidualCell 𝒦 𝒦' 4 x hx
  let Av := {w : Section34VertexIndex 𝒦 𝒦' |
    (section34GraphVertexCell 𝒦 𝒦' w ∩ Vv).Nonempty}
  let Ae := {e : Section34EdgeIndex 𝒦 𝒦' |
    (section34GraphSplitCell 𝒦 𝒦' e ∩ Ve).Nonempty}
  let Af := {s : Section34SimplexIndex 𝒦 3 |
    (section34GraphResidualCell 𝒦 𝒦' s.1 ∩ Vf).Nonempty}
  let At := {t : Section34SimplexIndex 𝒦 4 |
    (section34GraphResidualCell 𝒦 𝒦' t.1 ∩ Vt).Nonempty}
  have hfp : {p : Section34PatchIndex 𝒦 𝒦' | p.1 ∈ At ×ˢ Av}.Finite :=
    (hft.prod hfv).preimage Subtype.val_injective.injOn
  have hfa : {a : Section34ArcIndex 𝒦 𝒦' | a.1 ∈ Af ×ˢ Av}.Finite :=
    (hff.prod hfv).preimage Subtype.val_injective.injOn
  have hfi : {i : Section34EdgeArcIndex 𝒦 𝒦' | i.1 ∈ At ×ˢ Ae}.Finite :=
    (hft.prod hfe).preimage Subtype.val_injective.injOn
  have hfm : {p : Section34MarkIndex 𝒦 𝒦' | p.1 ∈ Af ×ˢ Ae}.Finite :=
    (hff.prod hfe).preimage Subtype.val_injective.injOn
  let F : Fin 8 → Set (Section34CutLabelOf 𝒦 𝒦') :=
    ![Section34Label.vertexBall '' Av, Section34Label.tetraBall '' At,
      Section34Label.splitDisk '' Ae, Section34Label.faceDisk '' Af,
      Section34Label.patch '' {p : Section34PatchIndex 𝒦 𝒦' | p.1 ∈ At ×ˢ Av},
      Section34Label.faceArc '' {a : Section34ArcIndex 𝒦 𝒦' | a.1 ∈ Af ×ˢ Av},
      Section34Label.edgeArc '' {i : Section34EdgeArcIndex 𝒦 𝒦' | i.1 ∈ At ×ˢ Ae},
      Section34Label.markedPoint '' {p : Section34MarkIndex 𝒦 𝒦' | p.1 ∈ Af ×ˢ Ae}]
  have hF : ∀ i, (F i).Finite := by
    intro i
    fin_cases i
    · exact hfv.image _
    · exact hft.image _
    · exact hfe.image _
    · exact hff.image _
    · exact hfp.image _
    · exact hfa.image _
    · exact hfi.image _
    · exact hfm.image _
  refine ⟨(Vv ∩ Ve) ∩ (Vf ∩ Vt), Filter.inter_mem (Filter.inter_mem hVv hVe)
    (Filter.inter_mem hVf hVt), (Set.finite_iUnion hF).subset ?_⟩
  rintro l ⟨y, hy, hyV⟩
  cases l with
  | vertexBall w =>
    exact mem_iUnion.mpr ⟨0, mem_image_of_mem _ ⟨y, hy, hyV.1.1⟩⟩
  | tetraBall t =>
    exact mem_iUnion.mpr ⟨1, mem_image_of_mem _ ⟨y, hy, hyV.2.2⟩⟩
  | splitDisk e =>
    exact mem_iUnion.mpr ⟨2, mem_image_of_mem _ ⟨y, hy, hyV.1.2⟩⟩
  | faceDisk s =>
    exact mem_iUnion.mpr ⟨3, mem_image_of_mem _ ⟨y, hy, hyV.2.1⟩⟩
  | patch p =>
    exact mem_iUnion.mpr ⟨4, mem_image_of_mem _ ⟨⟨y, hy.1, hyV.2.2⟩, ⟨y, hy.2, hyV.1.1⟩⟩⟩
  | faceArc a =>
    exact mem_iUnion.mpr ⟨5, mem_image_of_mem _ ⟨⟨y, hy.2, hyV.2.1⟩, ⟨y, hy.1, hyV.1.1⟩⟩⟩
  | edgeArc i =>
    exact mem_iUnion.mpr ⟨6, mem_image_of_mem _ ⟨⟨y, hy.1, hyV.2.2⟩, ⟨y, hy.2, hyV.1.2⟩⟩⟩
  | markedPoint p =>
    exact mem_iUnion.mpr ⟨7, mem_image_of_mem _ ⟨⟨y, hy.2, hyV.2.1⟩, ⟨y, hy.1, hyV.1.2⟩⟩⟩

private theorem iUnion_section34GraphCutFamily [FiniteDimensional ℝ Ea]
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex) :
    (⋃ l, section34GraphCutFamily 𝒦 𝒦' l) = U := by
  apply Subset.antisymm (iUnion_subset section34GraphCutFamily_subset)
  apply (eq_iUnion_section34GraphVertexCell_union_residuals 𝒦 𝒦' hK).subset.trans
  refine union_subset (iUnion_subset fun w => ?_) (iUnion_subset fun t => ?_)
  · exact subset_iUnion (section34GraphCutFamily 𝒦 𝒦') (.vertexBall w)
  · exact subset_iUnion (section34GraphCutFamily 𝒦 𝒦') (.tetraBall t)

theorem section34GraphCutFamily_source_clauses [FiniteDimensional ℝ Ea]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex) :
    let src := section34GraphCutFamily 𝒦 𝒦'
    (∀ x ∈ U, ∃ V ∈ 𝓝 x, {l | (src l ∩ V).Nonempty}.Finite) ∧
    (⋃ l, src l) = U ∧
    (∀ a : Section34ArcIndex 𝒦 𝒦',
      src (.faceArc a) = src (.vertexBall a.1.2) ∩ src (.faceDisk a.1.1)) ∧
    (∀ p : Section34MarkIndex 𝒦 𝒦',
      src (.markedPoint p) = src (.splitDisk p.1.2) ∩ src (.faceDisk p.1.1)) ∧
    (∀ x : Section34PatchIndex 𝒦 𝒦',
      src (.patch x) = src (.tetraBall x.1.1) ∩ src (.vertexBall x.1.2)) ∧
    (∀ i : Section34EdgeArcIndex 𝒦 𝒦',
      src (.edgeArc i) = src (.tetraBall i.1.1) ∩ src (.splitDisk i.1.2)) ∧
    (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 s.1 → src (.faceDisk s) ∩ src (.vertexBall w) = ∅) ∧
    (∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
      ¬ Section34Incident e.1 s.1 → src (.faceDisk s) ∩ src (.splitDisk e) = ∅) ∧
    (∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 t.1 → src (.tetraBall t) ∩ src (.vertexBall w) = ∅) ∧
    (∀ (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦'),
      ¬ Section34Incident e.1 t.1 → src (.tetraBall t) ∩ src (.splitDisk e) = ∅) ∧
    (∀ l, ∃ m, section34Dim m = 3 ∧ src l ⊆ src m) ∧
    (∀ s : Section34SimplexIndex 𝒦 3, src (.faceDisk s) ⊆ simplexBody 𝒦 s.1) ∧
    (∀ t : Section34SimplexIndex 𝒦 4, src (.tetraBall t) ⊆ Section34CarrierSupport 𝒦 t.1) ∧
    (∀ w : Section34VertexIndex 𝒦 𝒦', simplexBody 𝒦' w.1 ⊆ src (.vertexBall w)) ∧
    (∀ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      (src (.vertexBall w) ∩ src (.splitDisk e)).Nonempty → w.1 ⊆ e.1) ∧
    (∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧
        src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')) ∧
    (∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
      Section34Incident s.1 t.1 → src (.faceDisk s) ⊆ src (.tetraBall t)) ∧
    ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1 := by
  have htop : ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
      Section34Incident s.1 t.1 := by
    intro s
    obtain ⟨t, ht, hst, hcard⟩ := 𝒦.exists_face_superset_card_eq hK s.2.1
    exact ⟨⟨t, ht, hcard⟩, fun p hp => subset_convexHull ℝ _ (hst hp)⟩
  have hsplit : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w : Section34VertexIndex 𝒦 𝒦',
      section34GraphSplitCell 𝒦 𝒦' e ⊆ section34GraphVertexCell 𝒦 𝒦' w := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
    exact ⟨w, heq.subset.trans inter_subset_left⟩
  have hdim : ∀ l : Section34CutLabelOf 𝒦 𝒦', ∃ m, section34Dim m = 3 ∧
      section34GraphCutFamily 𝒦 𝒦' l ⊆ section34GraphCutFamily 𝒦 𝒦' m := by
    intro l
    cases l with
    | vertexBall w => exact ⟨.vertexBall w, rfl, subset_rfl⟩
    | tetraBall t => exact ⟨.tetraBall t, rfl, subset_rfl⟩
    | splitDisk e =>
      obtain ⟨w, hw⟩ := hsplit e
      exact ⟨.vertexBall w, rfl, hw⟩
    | faceDisk s =>
      obtain ⟨t, ht⟩ := htop s
      exact ⟨.tetraBall t, rfl, section34GraphResidualCell_mono_of_incident ht⟩
    | patch x => exact ⟨.tetraBall x.1.1, rfl, inter_subset_left⟩
    | faceArc a => exact ⟨.vertexBall a.1.2, rfl, inter_subset_left⟩
    | edgeArc i => exact ⟨.tetraBall i.1.1, rfl, inter_subset_left⟩
    | markedPoint p =>
      obtain ⟨w, hw⟩ := hsplit p.1.2
      exact ⟨.vertexBall w, rfl, inter_subset_left.trans hw⟩
  exact ⟨locallyFinite_section34GraphCutFamily 𝒦 𝒦', iUnion_section34GraphCutFamily 𝒦 𝒦' hK,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun s w => section34GraphResidualCell_inter_vertex_eq_empty_of_not_incident
      hsub hmap s.2.1 w,
    fun s e => section34GraphResidualCell_inter_split_eq_empty_of_not_incident
      hsub hmap s.2.1 e,
    fun t w => section34GraphResidualCell_inter_vertex_eq_empty_of_not_incident
      hsub hmap t.2.1 w,
    fun t e => section34GraphResidualCell_inter_split_eq_empty_of_not_incident
      hsub hmap t.2.1 e,
    hdim, fun s => section34GraphResidualCell_subset_simplexBody s.2.1,
    fun t => section34GraphResidualCell_subset_carrierSupport t.2.1,
    simplexBody_subset_section34GraphVertexCell,
    vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty hsub hmap,
    exists_section34GraphSplitCell_endpoints hsub hmap,
    fun _ _ => section34GraphResidualCell_mono_of_incident, htop⟩

end DifferentialGeometry.Topology.PiecewiseLinear
