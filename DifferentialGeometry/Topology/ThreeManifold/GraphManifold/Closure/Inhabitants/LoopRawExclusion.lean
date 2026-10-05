import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRawRim
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRawSublevel
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopPieceInteriors

/-!
The genuine global common sublevels avoid the interior of the whole original ball-handle union.
True closed pieces, strict interior signs, and actual common rim centers give the exclusion.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance rawExclusion_diskCharts : ChartedSpace (EuclideanHalfSpace 2)
    (ClosedCell 2) := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

private theorem rawExclusion_single (k : Fin standardLoopBallHandleCycle.len) :
    k = ⟨0, standardLoopBallHandleCycle.len_pos⟩ := by
  apply Fin.ext
  have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
    rw [standardLoopBallHandleCycle_len]
  have hlt := lt_of_lt_of_le k.isLt hbound
  change k.val = 0
  omega

theorem loopRawPieces_single : loopRawPieces =
    Set.range (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map ∪
    Set.range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
  ext p
  constructor
  · rintro (hb | hh)
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hb
      rw [rawExclusion_single k] at hk
      exact Or.inl hk
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hh
      rw [rawExclusion_single k] at hk
      exact Or.inr hk
  · rintro (hb | hh)
    · exact Or.inl (mem_iUnion.mpr ⟨⟨0, standardLoopBallHandleCycle.len_pos⟩,hb⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨0, standardLoopBallHandleCycle.len_pos⟩,hh⟩)

theorem loopRawPieces_closed : IsClosed loopRawPieces := by
  rw [loopRawPieces_single]
  apply IsClosed.union
  · exact (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).isClosedEmbedding_map.isClosed_range
  · exact (isCompact_range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).smooth.continuous).isClosed

theorem loopRawPieces_sublevel_notInterior {z : loopCircleBase}
    (hz : ∀ l : Fin 3, loopDefining l z ≤ 0) : loopCircleSection z ∉ interior loopRawPieces := by
  intro hp
  have hb : loopBallDefining z ≤ 0 := hz 1
  have hh : loopHandleDefining z ≤ 0 := hz 0
  have hbc : IsClosed (Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) :=
    (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).isClosedEmbedding_map.isClosed_range
  have hhc : IsClosed (Set.range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map) :=
    (isCompact_range (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).smooth.continuous).isClosed
  have hpu := hp
  rw [loopRawPieces_single] at hpu
  by_cases hbm : loopCircleSection z ∈ Set.range (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
  · by_cases hhm : loopCircleSection z ∈ Set.range (standardLoopBallHandleCycle.handle
        ⟨0, standardLoopBallHandleCycle.len_pos⟩).map
    · have hb0 := le_antisymm hb (loopBallDefining_raw hbm)
      have hh0 := le_antisymm hh (loopHandleDefining_raw hhm)
      obtain ⟨b,rfl⟩ := loopHandleBall_common_center z hh0 hb0
      have hs : (0,0) ∈ rimBox 2 := by constructor <;> norm_num
      rw [loopCircleSection_rim b hs] at hp
      exact loopRaw_rimCenter_notInterior b 1 hp
    · have hic : loopCircleSection z ∈ interior (Set.range (standardLoopBallHandleCycle.handle
          ⟨0, standardLoopBallHandleCycle.len_pos⟩).map)ᶜ := by
        rw [hhc.isOpen_compl.interior_eq]
        exact hhm
      have hbi := interior_union_inter_interior_compl_right_subset ⟨hpu,hic⟩
      exact (not_lt_of_ge hb) (loopBallDefining_ballInterior hbi)
  · have hic : loopCircleSection z ∈ interior (Set.range (standardLoopBallHandleCycle.ball
        ⟨0, standardLoopBallHandleCycle.len_pos⟩).map)ᶜ := by
      rw [hbc.isOpen_compl.interior_eq]
      exact hbm
    have hhi := interior_union_inter_interior_compl_left_subset ⟨hpu,hic⟩
    exact (not_lt_of_ge hh) (loopHandleDefining_handleInterior hhi)

end GC.GraphManifold.Assembly
