import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcSublevel
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopVerticalBase

/-!
Every whole actual handle rim fibre lies in the SAME compact circle-region base and region.
Actual first-circle normalization retains the original closed handle and excludes ball interiors.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem handleSublevel_section_range (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1)
    (hd : (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y
      ∈ loopCircleDomain) : loopCircleSection (loopCircleProjection
        ⟨(standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩)
        ∈ Set.range (standardLoopBallHandleCycle.handle
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).map := by
  let q : ModelSpace := (y.1.val,y.2.val)
  have hy : q ∈ loopActualHandleChart.source := by
    rw [loopActualHandleChart_source]
    change ‖y.1.val‖ < 13/10 ∧ -1/4 < y.2.val ∧ y.2.val < 5/4
    constructor
    · linarith [y.1.property]
    · constructor <;> linarith [y.2.property.1,y.2.property.2]
  have he : loopActualHandleChart q = (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y := loopActualHandleChart_handle y
  have hdq : loopActualHandleChart q ∈ loopCircleDomain := by rw [he]; exact hd
  have hpair : (⟨loopActualHandleChart q,hdq⟩ : loopCircleDomain) =
      ⟨(standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩ :=
    Subtype.ext he
  let r := loopHandleRotation q 1
  let yr : ClosedCell 2 × Set.Icc (0 : ℝ) 1 := (⟨r.1,by
    change ‖(loopHandleRotation q 1).1‖ ≤ 1
    rw [loopHandleRotation_norm]
    exact y.1.property⟩,⟨r.2,y.2.property⟩)
  have hs := loopHandleRotation_section hy hdq
  rw [hpair] at hs
  exact ⟨yr,(loopActualHandleChart_handle yr).symm.trans hs.symm⟩

theorem loopHandleProjection_ballNonpos (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1)
    (hd : (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y
      ∈ loopCircleDomain) : loopBallDefining (loopCircleProjection
        ⟨(standardLoopBallHandleCycle.handle
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩) ≤ 0 := by
  by_contra hn
  have hi := loopBallDefining_positive_interior (lt_of_not_ge hn)
  have hf := loopHandleBall_intersection_face (handleSublevel_section_range y hd)
    (interior_subset hi)
  rw [loopBallWholeFace_frontier] at hf
  exact hf.2 hi

theorem loopHandleProjection_coreNonpos (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1)
    (hd : (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y
      ∈ loopCircleDomain) : loopCoreDefining (loopCircleProjection
        ⟨(standardLoopBallHandleCycle.handle
          ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩) ≤ 0 := by
  let z := loopCircleProjection
    ⟨(standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩
  have hs : loopCircleSection z ∈ solidTorusSet.{0} := by
    rw [← standardLoopBallHandleCycle_union]
    exact standardLoopBallHandleCycle.handle_subset_union
      ⟨0,standardLoopBallHandleCycle.len_pos⟩ (handleSublevel_section_range y hd)
  have hh : cliffordHeight (loopCircleSection z) ≤ 0 := hs
  rw [loopCircleSection_height] at hh
  change 1/8-‖z.val‖^2 ≤ 0
  linarith

theorem loopHandleProjection_rimBase (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1)
    (hr : y.1 ∈ diskRim)
    (hd : (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y
      ∈ loopCircleDomain) : loopCircleProjection
        ⟨(standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩
        ∈ loopCircleCornerBase := by
  apply loopCircleCornerBase_sublevel.mpr
  intro l
  fin_cases l
  · change loopHandleDefining (loopCircleProjection
      ⟨(standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map y,hd⟩) ≤ 0
    rw [loopHandleProjection_middle y hd,mem_diskRim_iff.mp hr]
    norm_num
  · exact loopHandleProjection_ballNonpos y hd
  · exact loopHandleProjection_coreNonpos y hd

theorem loopHandleBase_cornerBase (t : Set.Icc (0 : ℝ) 1) :
    loopHandleBase t ∈ loopCircleCornerBase := by
  let w := circleRimPoint (1 : Circle)
  let p := (standardLoopBallHandleCycle.handle
    ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,t)
  have hr : p ∈ (fun x : ClosedCell 2 => (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (x,t)) '' diskRim :=
    ⟨w,circleRimPoint_mem_diskRim 1,rfl⟩
  rw [loopHandle_vertical_fibre] at hr
  obtain ⟨q,hq,hqp⟩ := hr
  have hpq : q.val = p := hqp
  have hd : p ∈ loopCircleDomain := by rw [← hpq]; exact q.property
  have he : (⟨p,hd⟩ : loopCircleDomain) = q := Subtype.ext hpq.symm
  have hm := loopHandleProjection_rimBase (w,t) (circleRimPoint_mem_diskRim 1) hd
  rw [he] at hm
  have ht : loopCircleProjection q = loopHandleBase t := hq
  rwa [ht] at hm

theorem loopHandle_vertical_region (t : Set.Icc (0 : ℝ) 1) :
    (fun w : ClosedCell 2 => (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map (w,t)) '' diskRim ⊆ loopCircleRegion := by
  rw [loopHandle_vertical_fibre]
  rintro p ⟨q,hq,rfl⟩
  refine ⟨q,?_,rfl⟩
  change loopCircleProjection q ∈ loopCircleCornerBase
  have ht : loopCircleProjection q = loopHandleBase t := hq
  rw [ht]
  exact loopHandleBase_cornerBase t

end GC.GraphManifold.Assembly
