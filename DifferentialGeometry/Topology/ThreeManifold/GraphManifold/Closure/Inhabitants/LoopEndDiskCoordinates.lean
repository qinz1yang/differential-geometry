import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCapGeometry

/-!
Both entire original handle end disks retain the actual original ball chart inverse coordinates.
The native cap and handle identities give their genuine signed pole height, including the rims.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance endDiskCoord_rank3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem endDiskCap_target (w : ClosedCell 2) : (w.val,(0 : ℝ)) ∈ capTarget := by
  constructor
  · norm_num
  · change ‖w.val‖ < 2
    linarith [w.property]

private theorem endDiskCap_model (b : Bool) (w : ClosedCell 2) :
    loopActualBallChart (capInv b (w.val,0)) =
    (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b) := by
  have ht := endDiskCap_target w
  have hn : ‖capInv b (w.val,0)‖ = 1 := by
    simpa using loopCapInverse_norm b (w.val,0) (by norm_num)
  let x : ClosedCell 3 := ⟨capInv b (w.val,0), hn.le⟩
  have hx : x ∈ neckCapRegion (1/16) b := by
    refine ⟨?_,capInv_mem_capSource ht,?_⟩
    · change 1-2*(1/16 : ℝ) < ‖capInv b (w.val,0)‖
      rw [hn]
      norm_num
    · change ‖(capMap b (capInv b (w.val,0))).1‖ < 1+2*(1/16 : ℝ)
      rw [capMap_capInv ht]
      change ‖w.val‖ < 1+2*(1/16 : ℝ)
      linarith [w.property]
  have hcap := modelBall_cap (by norm_num : 0 < (1 : ℕ))
    (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1/8) (0 : Fin 1) b x hx
  have hk : rimBall 1 (0 : Fin 1) b = 0 := Subsingleton.elim _ _
  rw [hk] at hcap
  change modelBall.{0} 1 (1/16) (0 : Fin 1) x =
    modelNeck.{0} (by norm_num) (by norm_num) (by norm_num) (0 : Fin 1) b
      (capMap b (capInv b (w.val,0))) at hcap
  rw [capMap_capInv ht] at hcap
  have hH := modelHandle_end (by norm_num : 0 < (1 : ℕ))
    (by norm_num : (0 : ℝ) < 1/16) (by norm_num : (1/16 : ℝ) ≤ 1/8)
    (0 : Fin 1) b (w,iccEnd b)
  have he : handleEnd b (w,iccEnd b) = (w.val,(0 : ℝ)) := by
    cases b <;> simp [handleEnd,endCoord,iccEnd]
  rw [he] at hH
  have hmap : (standardLoopBallHandleCycle.ball
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map x =
      (standardLoopBallHandleCycle.handle
        ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b) := hcap.trans hH.symm
  exact (loopActualBallChart_ball x).trans hmap

theorem loopHandleEnd_ballInverse (b : Bool) (w : ClosedCell 2) :
    loopActualBallChart.symm ((standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b)) = capInv b (w.val,0) := by
  have hn : ‖capInv b (w.val,0)‖ = 1 := by
    simpa using loopCapInverse_norm b (w.val,0) (by norm_num)
  have hs : capInv b (w.val,0) ∈ loopActualBallChart.source := by
    rw [loopActualBallChart_source,Metric.mem_ball,dist_zero_right,hn]
    norm_num
  rw [← endDiskCap_model b w]
  exact loopActualBallChart.left_inv hs

theorem loopHandleEnd_ballHeight (b : Bool) (w : ClosedCell 2) :
    (ballCoord (loopActualBallChart.symm ((standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b)))).2 =
    if b then capCos ‖w.val‖ else -capCos ‖w.val‖ := by
  rw [loopHandleEnd_ballInverse,loopCapInverse_height]
  cases b <;> norm_num

end GC.GraphManifold.Assembly
