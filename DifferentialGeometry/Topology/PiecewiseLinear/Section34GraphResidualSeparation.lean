/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem section34GraphResidualCell_subset_iff
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {s t : Finset Ea} (hs : s ∈ 𝒦.complex.faces) (ht : t ∈ 𝒦.complex.faces)
    (hcard : 3 ≤ s.card) :
    section34GraphResidualCell 𝒦 𝒦' s ⊆ section34GraphResidualCell 𝒦 𝒦' t ↔ s ⊆ t := by
  classical
  constructor
  · intro hst v hvs
    by_contra hvt
    obtain ⟨q, hvq, hqs, hqcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.singleton_subset_iff.mpr hvs) (by simp : ({v} : Finset Ea).card ≤ 3) hcard
    have hqne : q.Nonempty := Finset.card_pos.mp (by omega)
    have hq := 𝒦.complex.down_closed hs hqs hqne
    have hqR : section34GraphResidualCell 𝒦 𝒦' q ⊆ section34GraphResidualCell 𝒦 𝒦' s :=
      section34GraphResidualCell_mono_of_incident fun x hx =>
        subset_convexHull ℝ _ (hqs hx)
    have hqIt : (q ∩ t).card ≤ 2 := by
      have hne : q ∩ t ≠ q := fun heq =>
        hvt ((Finset.mem_inter.mp (heq.symm ▸ hvq (Finset.mem_singleton_self v))).2)
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.inter_subset_left, hne⟩)
      omega
    have hem : section34GraphResidualCell 𝒦 𝒦' (q ∩ t) = ∅ := by
      rcases (q ∩ t).eq_empty_or_nonempty with hqt | hqt
      · simp [hqt, section34GraphResidualCell, simplexBody]
      · exact section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap
          (𝒦.complex.down_closed hq Finset.inter_subset_left hqt) hqIt
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap
      (⟨q, hq, hqcard⟩ : Section34SimplexIndex 𝒦 3)
    obtain ⟨x, hx⟩ := hB.nonempty
    have hxI : x ∈ section34GraphResidualCell 𝒦 𝒦' q ∩ section34GraphResidualCell 𝒦 𝒦' t :=
      ⟨hx, hst (hqR hx)⟩
    rw [section34GraphResidualCell_inter hsub hmap hq ht, hem] at hxI
    exact hxI
  · intro hst
    exact section34GraphResidualCell_mono_of_incident fun x hx =>
      subset_convexHull ℝ _ (hst hx)

theorem section34GraphResidualCell_not_subset_vertex_union
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (hcard : 3 ≤ t.card) :
    ¬ section34GraphResidualCell 𝒦 𝒦' t ⊆
      ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w := by
  obtain ⟨s, hst, hscard⟩ := Finset.exists_subset_card_eq hcard
  have hs := 𝒦.complex.down_closed ht hst (Finset.card_pos.mp (by omega : 0 < s.card))
  have hRs : section34GraphResidualCell 𝒦 𝒦' s ⊆ section34GraphResidualCell 𝒦 𝒦' t :=
    section34GraphResidualCell_mono_of_incident fun x hx =>
      subset_convexHull ℝ _ (hst hx)
  obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap
    (⟨s, hs, hscard⟩ : Section34SimplexIndex 𝒦 3)
  obtain ⟨x, hx⟩ := closure_nonempty_iff.mp hB.nonempty
  intro h
  exact hx.2 (h (hRs (subset_closure hx)))

theorem section34GraphResidualTetrahedron_subset_iff
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s t : Section34SimplexIndex 𝒦 4) :
    section34GraphResidualCell 𝒦 𝒦' s.1 ⊆ section34GraphResidualCell 𝒦 𝒦' t.1 ↔ s = t := by
  rw [section34GraphResidualCell_subset_iff hsub hmap s.2.1 t.2.1 (by omega)]
  exact ⟨fun h => Subtype.ext (Finset.eq_of_subset_of_card_le h (by rw [s.2.2, t.2.2])),
    fun h => h ▸ subset_rfl⟩

theorem section34GraphCutFamily_subset_strict_on_tetrahedra
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (t : Section34SimplexIndex 𝒦 4) (l : Section34CutLabelOf 𝒦 𝒦')
    (h : section34GraphCutFamily 𝒦 𝒦' (.tetraBall t) ⊆ section34GraphCutFamily 𝒦 𝒦' l) :
    (.tetraBall t : Section34CutLabelOf 𝒦 𝒦') = l := by
  let C := section34GraphVertexCell 𝒦 𝒦'
  let N := ⋃ w, C w
  have hRN : ¬ section34GraphResidualCell 𝒦 𝒦' t.1 ⊆ N :=
    section34GraphResidualCell_not_subset_vertex_union hsub hmap t.2.1 (by omega)
  have hEN (e : Section34EdgeIndex 𝒦 𝒦') : section34GraphSplitCell 𝒦 𝒦' e ⊆ N := by
    obtain ⟨w, z, -, -, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
    exact (heq.subset.trans inter_subset_left).trans (subset_iUnion C w)
  cases l with
  | vertexBall w => exact (hRN (h.trans (subset_iUnion C w))).elim
  | tetraBall s =>
      exact congrArg Section34Label.tetraBall
        ((section34GraphResidualTetrahedron_subset_iff hsub hmap t s).mp h)
  | splitDisk e => exact (hRN (h.trans (hEN e))).elim
  | faceDisk s =>
      have hts := (section34GraphResidualCell_subset_iff hsub hmap t.2.1 s.2.1
        (by omega)).mp h
      have hle := Finset.card_le_card hts
      rw [t.2.2, s.2.2] at hle
      omega
  | patch x => exact (hRN ((h.trans inter_subset_right).trans
      (subset_iUnion C x.1.2))).elim
  | faceArc a => exact (hRN ((h.trans inter_subset_left).trans
      (subset_iUnion C a.1.2))).elim
  | edgeArc i => exact (hRN ((h.trans inter_subset_right).trans (hEN i.1.2))).elim
  | markedPoint p => exact (hRN ((h.trans inter_subset_left).trans (hEN p.1.2))).elim

end DifferentialGeometry.Topology.PiecewiseLinear
