/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactInnermostReturn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_admissible_bigon_of_returning_meridian_arc
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3)
    (e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1})
    {B : Set E3} {η : ℝ → E3} (hη : IsPLHomeomorphOn η (Icc 0 1) B)
    (hB : B ⊆ fblBd s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (hends : ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e.1)
    (hmeet : B ∩ (⋃ i : {i : Section34CompactEdgeIndex K K' // Section34Incident i.1 s.1},
      section34CompactSplitDiskImage srcBd f₁ i.1) = {η 0, η 1}) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactBigonSlide K K' (section34CompactVertexBallImage src f₁)
        (section34CompactVertexBallImage srcBd f₁) (section34CompactSplitDiskImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fblBd t := by
  have hf₁ := hgraph.2.1
  have hBE : B ∩ (⋃ d, section34CompactSplitDiskImage src f₁ d) = {η 0, η 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxE⟩
      obtain ⟨d, hxd⟩ := mem_iUnion.mp hxE
      have hinc : Section34Incident d.1 s.1 := by
        by_contra hd
        exact Set.disjoint_left.mp
          (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s d hd)
          ((hinv.1 s).boundary_subset (hB hxB).1) hxd
      have hbd : x ∈ section34CompactSplitDiskImage srcBd f₁ d := by
        by_contra hx
        exact (hB hxB).2.2 (hcut.splitDiskImage_sdiff_subset_interior hf₁ d ⟨hxd, hx⟩)
      exact hmeet.subset ⟨hxB, mem_iUnion.mpr ⟨⟨d, hinc⟩, hbd⟩⟩
    · intro x hx
      exact ⟨(pair_subset (hη.bijOn.mapsTo (by norm_num))
        (hη.bijOn.mapsTo (by norm_num))) hx,
        mem_iUnion.mpr ⟨e.1, (hcut.isPLCellOn_splitDiskImage hf₁ e.1).boundary_subset
          (hends hx)⟩⟩
  obtain ⟨w, hw⟩ := hcut.exists_vertex_boundary_of_arc_avoiding_split_disks hf₁ hη
    (fun x hx => (hB hx).2) (by
      intro d
      apply Set.disjoint_left.mpr
      rintro x ⟨hxB, hxends⟩ hxd
      exact hxends (hBE.subset ⟨hxB, mem_iUnion.mpr ⟨d, hxd⟩⟩))
  exact exists_admissible_bigon_of_returning_arc hinv hcut hgraph hnc s w e.1 hη
    (fun x hx => (hB hx).1) hw hends hBE

end DifferentialGeometry.Topology.PiecewiseLinear
