/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionInside
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionOutside
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionCases

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactCompression (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hcar : Section34CompactCarrierControl K h ε H)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3)
    (hop : Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  obtain ⟨w, Dj, Jd, hDcell, hDw, hJdb, hDJ, hDE, hDo⟩ := hop
  have hc := StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3)
    (0 : EuclideanSpace ℝ (Fin 3))
  have hfsc : fbl s ⊆ (chartAt (EuclideanSpace ℝ (Fin 3))
      (0 : EuclideanSpace ℝ (Fin 3))).source := by
    rw [chartAt_self_eq]
    exact subset_univ _
  have hDjc : Dj ⊆ (chartAt (EuclideanSpace ℝ (Fin 3))
      (0 : EuclideanSpace ℝ (Fin 3))).source := by
    rw [chartAt_self_eq]
    exact subset_univ _
  rcases subset_interior_or_disjoint_sdiff_of_isPLCellOn hc (hinv.1 s) hDcell hfsc hDjc
    hDJ.subset with hin | hout
  · refine exists_compactCompression_of_subset hcut hgraph hinv s hDcell hDw hDJ hDE
      fun x hx => ?_
    by_cases hxJ : x ∈ Jd
    · exact (hinv.1 s).boundary_subset (hJdb hxJ)
    · exact interior_subset (hin ⟨hx, hxJ⟩)
  · exact exists_compactCompression_of_disjoint hcut hcar hgraph hinv s hDcell hDw hDJ hDE
      hDo hout

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
