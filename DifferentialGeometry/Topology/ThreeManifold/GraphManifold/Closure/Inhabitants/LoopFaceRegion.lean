import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcSublevel
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallSpherePartition

/-!
The SAME circle region meets the entire original ball sphere exactly in its genuine annulus.
Both whole original end disks meet that region in precisely their actual full rims.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallAnnulus_region (θ : Circle) (t : Set.Icc (0 : ℝ) 1) :
    loopBallAnnulus (θ,t) ∈ loopCircleRegion := by
  refine ⟨⟨loopBallAnnulus (θ,t),loopBallAnnulus_domain θ t⟩,?_,rfl⟩
  change loopCircleProjection ⟨loopBallAnnulus (θ,t),loopBallAnnulus_domain θ t⟩
    ∈ loopCircleCornerBase
  rw [loopBallAnnulus_projection]
  exact loopBallArcBase_cornerBase t

theorem loopHandleEnd_region (b : Bool) :
    (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b ∩
      loopCircleRegion = (fun w : ClosedCell 2 => (standardLoopBallHandleCycle.handle
        ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b)) '' diskRim := by
  ext p
  constructor
  · rintro ⟨hdisk,hr⟩
    obtain ⟨q,hq,hqp⟩ := hr
    have hd : p ∈ loopCircleDomain := hqp ▸ q.property
    have hqe : (⟨p,hd⟩ : loopCircleDomain) = q := Subtype.ext hqp.symm
    have hz : loopCircleProjection ⟨p,hd⟩ ∈ loopCircleCornerBase := by
      rw [hqe]
      exact hq
    have hg : loopHandleDefining (loopCircleProjection ⟨p,hd⟩) ≤ 0 :=
      loopCircleCornerBase_family hz 0
    obtain ⟨w,hw⟩ := hdisk
    have hwmap : (standardLoopBallHandleCycle.handle
        ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b) = p := hw
    have hdw : (standardLoopBallHandleCycle.handle
        ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b) ∈ loopCircleDomain := by
      rw [hwmap]
      exact hd
    have he : (⟨(standardLoopBallHandleCycle.handle
        ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,iccEnd b),hdw⟩ : loopCircleDomain) =
        ⟨p,hd⟩ := Subtype.ext hw
    have hm := loopHandleProjection_middle (w,iccEnd b) hdw
    rw [he] at hm
    have hn : ‖w.val‖ = 1 := by
      dsimp only [Prod.fst] at hm
      linarith [w.property]
    exact ⟨w,mem_diskRim_iff.mpr hn,hw⟩
  · intro hrim
    have ha : p ∈ Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd b)) := by
      rwa [loopBallAnnulus_end_rim]
    obtain ⟨θ,rfl⟩ := ha
    refine ⟨?_,loopBallAnnulus_region θ (iccEnd b)⟩
    have ha : loopBallAnnulus (θ,iccEnd b) ∈
        Set.range (fun a : Circle => loopBallAnnulus (a,iccEnd b)) := ⟨θ,rfl⟩
    rw [← loopBallAnnulus_endDisk_inter] at ha
    exact ha.1

theorem loopBallWholeFace_region :
    loopBallWholeFace ∩ loopCircleRegion = Set.range loopBallAnnulus := by
  ext p
  constructor
  · rintro ⟨hf,hr⟩
    rw [loopBallWholeFace_partition] at hf
    rcases hf with (hs | he) | ha
    · have hi := loopHandleEnd_region false
      have hm : p ∈ Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd false)) := by
        rw [loopBallAnnulus_end_rim,← hi]
        exact ⟨hs,hr⟩
      obtain ⟨θ,rfl⟩ := hm
      exact ⟨(θ,iccEnd false),rfl⟩
    · have hi := loopHandleEnd_region true
      have hm : p ∈ Set.range (fun θ : Circle => loopBallAnnulus (θ,iccEnd true)) := by
        rw [loopBallAnnulus_end_rim,← hi]
        exact ⟨he,hr⟩
      obtain ⟨θ,rfl⟩ := hm
      exact ⟨(θ,iccEnd true),rfl⟩
    · exact ha
  · rintro ⟨⟨θ,t⟩,rfl⟩
    exact ⟨loopBallAnnulus_face ⟨(θ,t),rfl⟩,loopBallAnnulus_region θ t⟩

end GC.GraphManifold.Assembly
