/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualPatchCells
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskChartGluing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

theorem Section34NormalPlus.isPLCellOn_residual_union_vertexBallImage
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hRH : R ⊆ H t.1)
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : Section34Incident w.1 t.1) :
    IsPLCellOn 3 (R ∪ section34VertexBallImage src f₁ w)
      (frontier (R ∪ section34VertexBallImage src f₁ w)) := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨c, hc, hHc, hVc, -⟩ := hdata.exists_chart_tetrahedron t
  have hP := hdata.isPLCellOn_residualPatch_boundary hdisk hR hDR hfr hint hio h7 hw
  exact hR.union_of_inter_eq_of_subset_frontier_in_chart
    (hcut.isPLCellOn_vertexBallImage hf₁ w) hP rfl
    (hR.inter_subset_frontier_of_disjoint_interior_left
      (hint.mono_right (subset_iUnion₂_of_subset w hw subset_rfl)))
    hc (hRH.trans hHc) (hVc w hw)

theorem Section34NormalPlus.isPLCellOn_residual_union_vertexBallImage_pair
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hRH : R ⊆ H t.1)
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {e : Section34EdgeIndex 𝒦 𝒦'} (he : Section34Incident e.1 t.1)
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww' : w ≠ w') (hwe : w.1 ⊆ e.1)
    (hw'e : w'.1 ⊆ e.1) :
    IsPLCellOn 3 (R ∪ (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ w'))
      (frontier (R ∪ (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ w'))) := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hw : Section34Incident w.1 t.1 := fun z hz => he (hwe hz)
  have hw' : Section34Incident w'.1 t.1 := fun z hz => he (hw'e hz)
  have hB1 := hdata.isPLCellOn_residual_union_vertexBallImage hdisk hR hRH hDR hfr hint hio h7 hw
  have hP := hdata.isPLCellOn_residualPatch_boundary hdisk hR hDR hfr hint hio h7 hw'
  have hI := hdata.isPLCellOn_residualEdgeArc hdisk hR hDR hfr hint hio h7 he
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e
  obtain ⟨c, hc, hHc, hVc, -⟩ := hdata.exists_chart_tetrahedron t
  have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
  have hEw' : section34SplitDiskImage src f₁ e ⊆
      section34VertexBallImage src f₁ w' := by
    rw [← hinter]
    exact inter_subset_right
  have hPE : R ∩ section34VertexBallImage src f₁ w' ∩
      section34SplitDiskImage src f₁ e = R ∩ section34SplitDiskImage src f₁ e := by
    rw [inter_assoc, inter_eq_right.mpr hEw']
  have hIq' : R ∩ section34SplitDiskImage src f₁ e ⊆
      (⋃ (a : Section34ArcIndex 𝒦 𝒦')
        (_ : a.1.2 = w' ∧ Section34Incident a.1.1.1 t.1), tgtA a) ∪
      ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.1 = t ∧ w'.1 ⊆ i.1.2.1),
        R ∩ section34SplitDiskImage src f₁ i.1.2 := by
    intro z hz
    exact Or.inr (mem_iUnion₂.mpr ⟨⟨(t, e), he⟩, ⟨rfl, hw'e⟩, hz⟩)
  have hIE := hdata.residual_inter_splitDiskImage_subset hR hint h7 e
  have hD := hP.union_of_inter_eq_arc_in_chart hE hI hPE hIq' hIE hc
    (inter_subset_right.trans (hVc w' hw')) (hEw'.trans (hVc w' hw'))
  have hmeet : (R ∪ section34VertexBallImage src f₁ w) ∩
      section34VertexBallImage src f₁ w' =
      R ∩ section34VertexBallImage src f₁ w' ∪ section34SplitDiskImage src f₁ e := by
    rw [union_inter_distrib_right, hinter]
  have hsubfr : R ∩ section34VertexBallImage src f₁ w' ∪
      section34SplitDiskImage src f₁ e ⊆
        frontier (section34VertexBallImage src f₁ w') :=
    union_subset (hR.inter_subset_frontier_of_disjoint_interior_left
      (hint.mono_right (subset_iUnion₂_of_subset w' hw' subset_rfl)))
      (hcut.splitDiskImage_subset_frontier hf₁ hw'e)
  have h := hB1.union_of_inter_eq_of_subset_frontier_in_chart
    (hcut.isPLCellOn_vertexBallImage hf₁ w') hD hmeet hsubfr
    hc (union_subset (hRH.trans hHc) (hVc w hw)) (hVc w' hw')
  rwa [union_assoc] at h

end DifferentialGeometry.Topology.PiecewiseLinear
