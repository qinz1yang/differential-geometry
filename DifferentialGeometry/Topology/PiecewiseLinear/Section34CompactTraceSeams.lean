/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.splitDiskImage_faceTorus_boundary
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) (s : Section34CompactSimplexIndex K 3)
    (e : Section34CompactEdgeIndex K K') (he : Section34Incident e.1 s.1) :
    section34CompactSplitDiskImage src f₁ e ⊆
        section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∧
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩
        section34CompactSplitDiskImage src f₁ e = section34CompactSplitDiskImage srcBd f₁ e ∧
      section34CompactSplitDiskImage src f₁ e \ section34CompactSplitDiskImage srcBd f₁ e ⊆
        interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 1
  obtain ⟨w, w', -, hew, hD⟩ := hcut.splitDiskImage_eq_inter hf₁ e
  have hwe : Section34Incident w.1 s.1 := by
    apply Subset.trans ?_ he
    rw [hew]
    exact subset_union_left
  have hw'e : Section34Incident w'.1 s.1 := by
    apply Subset.trans ?_ he
    rw [hew]
    exact subset_union_right
  let T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  have hVT : ∀ v, Section34Incident v.1 s.1 → section34CompactVertexBallImage src f₁ v ⊆ T :=
    fun v hv x hx => mem_iUnion₂.mpr ⟨⟨(s, v), hv⟩, rfl, hx⟩
  have hpairT : section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ w' ⊆ T :=
    union_subset (hVT w hwe) (hVT w' hw'e)
  have hDT : section34CompactSplitDiskImage src f₁ e ⊆ T :=
    hD.subset.trans (inter_subset_left.trans (hVT w hwe))
  have hcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  obtain ⟨q, hq, hqb⟩ := hcell.exists_isPLHomeomorphOn_stdSimplex
  have hDb : IsPLBall 2 (section34CompactSplitDiskImage src f₁ e) := ⟨q, hq⟩
  have hV : ∀ v, IsPLBall 3 (section34CompactVertexBallImage src f₁ v) :=
    fun v => (hcut.isPLCellOn_vertexBallImage hf₁ v).isPLBall_three
  have hDw : section34CompactSplitDiskImage src f₁ e ⊆
      frontier (section34CompactVertexBallImage src f₁ w) := by
    rw [hD]
    exact (hV w').inter_subset_frontier_of_isPLBall (hD ▸ hDb) (by norm_num)
  have hDw' : section34CompactSplitDiskImage src f₁ e ⊆
      frontier (section34CompactVertexBallImage src f₁ w') := by
    rw [hD, inter_comm]
    exact (hV w).inter_subset_frontier_of_isPLBall ((hD.trans (inter_comm _ _)) ▸ hDb)
      (by norm_num)
  have hDint : section34CompactSplitDiskImage src f₁ e \
      section34CompactSplitDiskImage srcBd f₁ e ⊆ interior T := by
    have hi := sdiff_subset_interior_union_of_inter_eq (hV w) (hV w') hq hD.symm hDw hDw'
    rw [← hqb] at hi
    exact hi.trans (interior_mono hpairT)
  have hfrpair := boundary_subset_frontier_union_of_inter_eq (hV w) (hV w') hcell hD.symm hDw
  let O := (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
    section34CompactVertexBallImage src f₁ u)ᶜ
  have hO : IsOpen O :=
    (isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ =>
      (hV u).isPolyhedron.isClosed).isOpen_compl
  have hDO : section34CompactSplitDiskImage src f₁ e ⊆ O := by
    intro x hx hbad
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hbad
    rcases eq_or_eq_of_section34CompactVertexIndex_subset e hew
        (hcut.subset_of_mem_splitDiskImage hf₁ hx hxu) with h | h
    · exact hu.1 h
    · exact hu.2 h
  have hTO : T ∩ O = (section34CompactVertexBallImage src f₁ w ∪
      section34CompactVertexBallImage src f₁ w') ∩ O := by
    ext x
    constructor
    · rintro ⟨hxT, hxO⟩
      obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hxT
      refine ⟨?_, hxO⟩
      by_cases ha : a.1.2 = w
      · exact Or.inl (ha ▸ hxa)
      by_cases ha' : a.1.2 = w'
      · exact Or.inr (ha' ▸ hxa)
      exact (hxO (mem_iUnion₂.mpr ⟨a.1.2, ⟨ha, ha'⟩, hxa⟩)).elim
    · rintro ⟨hx, hxO⟩
      exact ⟨hpairT hx, hxO⟩
  have hBdT : section34CompactSplitDiskImage srcBd f₁ e ⊆ frontier T := by
    intro x hx
    have hloc : x ∈ frontier (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ w') ∩ O :=
      ⟨hfrpair hx, hDO (hcell.boundary_subset hx)⟩
    rw [← frontier_inter_open_inter hO, ← hTO, frontier_inter_open_inter hO] at hloc
    exact hloc.1
  refine ⟨hDT, ?_, hDint⟩
  apply Subset.antisymm
  · rintro x ⟨hxfr, hxD⟩
    by_contra hxBd
    exact Set.disjoint_left.mp disjoint_interior_frontier (hDint ⟨hxD, hxBd⟩) hxfr
  · intro x hx
    exact ⟨hBdT hx, hcell.boundary_subset hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
