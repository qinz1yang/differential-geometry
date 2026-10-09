import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCapGeometry
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCoreDefining

/-!
The deep core cannot share any zero with either actual global ball or nonempty handle function.
The genuine zero sections lie in the original raw pieces, disjoint from the entire actual core.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance corePairRank2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

private local instance corePairRank3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem loopBallZero_section_range (z : loopCircleBase) (hb : loopBallDefining z = 0) :
    loopCircleSection z ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
  have ht := (loopBallDefining_zero.mp hb).1
  have hn := (loopBallDefining_zero.mp hb).2
  let x := loopActualBallChart.symm (loopCircleSection z)
  let xb : ClosedCell 3 := ⟨x, hn.le⟩
  have hxv : loopActualBallChart x = loopCircleSection z := loopActualBallChart.right_inv ht
  exact ⟨xb,(loopActualBallChart_ball xb).symm.trans hxv⟩

theorem loopHandleZero_section_ranges (z : loopCircleBase) (hh : loopHandleDefining z = 0) :
    loopCircleSection z ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map ∪
      Set.range (standardLoopBallHandleCycle.handle
        ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
  have ht := (loopHandleDefining_zero.mp hh).1
  have hbd := loopHandleDefining_zero_bounds hh
  let x := loopActualHandleChart.symm (loopCircleSection z)
  have hxv : loopActualHandleChart x = loopCircleSection z := loopActualHandleChart.right_inv ht
  by_cases hl : x.2 < 0
  · left
    have he : loopActualHandleChart (neckFlip false x) = loopCircleSection z := by
      rw [neckFlip_false]
      exact hxv
    rw [← he]
    exact loopCapGhost_ballRange false hbd.1 ⟨hbd.2.1, hl⟩
  by_cases hu : 1 < x.2
  · left
    let q : ModelSpace := (x.1, 1 - x.2)
    have heq : neckFlip true q = x := by
      rw [neckFlip_true]
      apply Prod.ext
      · rfl
      · change 1 - (1 - x.2) = x.2
        ring
    have hqt : -3 / 16 < q.2 ∧ q.2 < 0 := by
      dsimp only [q]
      constructor <;> linarith [hbd.2.2]
    have he : loopActualHandleChart (neckFlip true q) = loopCircleSection z :=
      (congrArg loopActualHandleChart heq).trans hxv
    rw [← he]
    exact loopCapGhost_ballRange true (show ‖q.1‖ ≤ 1 from hbd.1) hqt
  · right
    let yh : ClosedCell 2 × Set.Icc (0 : ℝ) 1 :=
      (⟨x.1, hbd.1⟩,⟨x.2, le_of_not_gt hl, le_of_not_gt hu⟩)
    exact ⟨yh,(loopActualHandleChart_handle yh).symm.trans hxv⟩

theorem loopCoreZero_section_range (z : loopCircleBase) (hc : loopCoreDefining z = 0) :
    loopCircleSection z ∈ Set.range loopComplementVertex.map := by
  have hz := loopCoreDefining_zero.mp hc
  have hlift : loopCircleSection z ∈ loopCircleLift (Set.range loopCoreBaseCircle) := by
    refine ⟨⟨loopCircleSection z, loopCircleSection_domain z⟩ , ?_, rfl⟩
    change loopCircleProjection ⟨loopCircleSection z, loopCircleSection_domain z⟩ ∈
      Set.range loopCoreBaseCircle
    rw [loopCircleSection_projection]
    exact hz
  rw [← loopComplementFace_projection, loopComplementFace_height] at hlift
  rw [loopComplementVertex_range]
  exact hlift.ge

theorem loopCoreBall_no_common (z : loopCircleBase)
    (hc : loopCoreDefining z = 0) (hb : loopBallDefining z = 0) : False :=
  Set.disjoint_left.mp (loopBall_core_disjoint ⟨0, standardLoopBallHandleCycle.len_pos⟩)
    (loopBallZero_section_range z hb) (loopCoreZero_section_range z hc)

theorem loopCoreHandle_no_common (z : loopCircleBase)
    (hc : loopCoreDefining z = 0) (hh : loopHandleDefining z = 0) : False := by
  have hp := loopCoreZero_section_range z hc
  rcases loopHandleZero_section_ranges z hh with hb | hH
  · exact Set.disjoint_left.mp
      (loopBall_core_disjoint ⟨0, standardLoopBallHandleCycle.len_pos⟩) hb hp
  · exact Set.disjoint_left.mp
      (loopHandle_core_disjoint ⟨0, standardLoopBallHandleCycle.len_pos⟩) hH hp

end GC.GraphManifold.Assembly
