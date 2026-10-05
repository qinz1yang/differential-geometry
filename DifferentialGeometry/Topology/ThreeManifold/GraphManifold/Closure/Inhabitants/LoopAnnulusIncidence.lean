import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopEndDiskCoordinates
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopAnnulusCoordinates
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcEnds

/-!
The actual entire ball annulus meets both whole original end disks exactly on their genuine rims.
The native original ball inverse and pole-height coordinates force the true interval endpoints.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem annulusIncidence_cos_lower (w : ClosedCell 2) : 3 / 5 ≤ capCos ‖w.val‖ := by
  have hc := capCos_le_capCos (norm_nonneg w.val) w.property
  norm_num [capCos] at hc
  exact hc

theorem loopBallAnnulus_endDisk_coordinates (b : Bool) (θ : Circle)
    (t : Set.Icc (0 : ℝ) 1) (w : ClosedCell 2)
    (he : loopBallAnnulus (θ,t) = (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b)) :
    ‖w.val‖ = 1 ∧ t = iccEnd b := by
  have h := congrArg (fun p => (ballCoord (loopActualBallChart.symm p)).2) he
  rw [loopBallAnnulus_ballInverse,loopHandleEnd_ballHeight] at h
  have hc := loopBallLatitudePoint_coordinates θ t
  have hheight : (ballCoord (loopBallLatitudePoint θ t).val).2 = loopBallArcHeight t := by
    change (ballCoord (loopBallLatitudePoint θ t).val).2 = -3/5+(6/5)*t.val
    exact congrArg Prod.snd hc
  rw [hheight] at h
  have hb := loopBallArcHeight_bounds t
  have hlo := annulusIncidence_cos_lower w
  have hcos : capCos ‖w.val‖ = 3/5 := by
    cases b
    · change loopBallArcHeight t = -capCos ‖w.val‖ at h
      linarith [hb.1]
    · change loopBallArcHeight t = capCos ‖w.val‖ at h
      linarith [hb.2]
  have hone : capCos (1 : ℝ) = 3/5 := by norm_num [capCos]
  have hw := capCos_injOn (norm_nonneg w.val) (by norm_num) (hcos.trans hone.symm)
  refine ⟨hw,?_⟩
  rw [hcos] at h
  apply Subtype.ext
  cases b
  · change t.val = 0
    change loopBallArcHeight t = -(3/5 : ℝ) at h
    dsimp only [loopBallArcHeight] at h
    linarith
  · change t.val = 1
    change loopBallArcHeight t = (3/5 : ℝ) at h
    dsimp only [loopBallArcHeight] at h
    linarith

theorem loopBallAnnulus_endDisk_time (b : Bool) {θ : Circle} {t : Set.Icc (0 : ℝ) 1}
    (hp : loopBallAnnulus (θ,t) ∈ (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).endDisk b) : t = iccEnd b := by
  obtain ⟨w,hw⟩ := hp
  exact (loopBallAnnulus_endDisk_coordinates b θ t w hw.symm).2

theorem loopBallAnnulus_end_rim (b : Bool) :
    Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd b)) =
    (fun w : ClosedCell 2 => (standardLoopBallHandleCycle.handle
      ⟨0, standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b)) '' diskRim := by
  rw [← standardLoopBallHandleCycle.rim_label]
  ext p
  constructor
  · rintro ⟨θ,hθ⟩
    refine ⟨(θ,(0,0)),rfl,?_⟩
    rw [← loopBallAnnulus_end b θ]
    exact hθ
  · rintro ⟨⟨θ,v⟩,hv,he⟩
    change v = (0,0) at hv
    subst v
    refine ⟨θ,?_⟩
    change loopBallAnnulus (θ,iccEnd b) = p
    rw [loopBallAnnulus_end b θ]
    exact he

theorem loopBallAnnulus_endDisk_inter (b : Bool) :
    (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).endDisk b ∩
    Set.range loopBallAnnulus = Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd b)) := by
  ext p
  constructor
  · rintro ⟨hd,⟨⟨θ,t⟩,rfl⟩⟩
    have ht := loopBallAnnulus_endDisk_time b hd
    subst t
    exact ⟨θ,rfl⟩
  · rintro ⟨θ,rfl⟩
    constructor
    · have hr : loopBallAnnulus (θ,iccEnd b) ∈
        Set.range (fun a : Circle => loopBallAnnulus (a,iccEnd b)) := ⟨θ,rfl⟩
      rw [loopBallAnnulus_end_rim] at hr
      obtain ⟨w,hw,he⟩ := hr
      exact ⟨w,he⟩
    · exact ⟨(θ,iccEnd b),rfl⟩

end GC.GraphManifold.Assembly
