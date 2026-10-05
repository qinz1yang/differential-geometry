import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopAnnulusIncidence
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopProjectionSigns
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopSublevelExact

/-!
Every time of the original ball annulus projects into the SAME genuine compact cornered base.
Actual padded cap exclusion and original whole-enddisk incidence force the global sublevels.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallArcBase_section (t : Set.Icc (0 : ℝ) 1) :
    loopCircleSection (loopBallArcBase t) = loopBallAnnulus (1,t) := by
  have hs := loopCircleSection_inverse (loopBallArcBase t)
  have ha := loopBallAnnulus_orbit_inverse (1 : Circle) t
  have he := congrArg loopCircleCoordinates (hs.trans ha.symm)
  exact (loopCircleCoordinates.right_inv
    (loopCircleSection_domain (loopBallArcBase t))).symm.trans
    (he.trans (loopCircleCoordinates.right_inv (loopBallAnnulus_domain 1 t)))

theorem loopHandlePositive_ballZero_time {z : loopCircleBase}
    (hp : 0 < loopHandleDefining z) (hb : loopBallDefining z = 0) :
    0 ≤ (loopActualHandleChart.symm (loopCircleSection z)).2 ∧
    (loopActualHandleChart.symm (loopCircleSection z)).2 ≤ 1 := by
  let x := loopActualHandleChart.symm (loopCircleSection z)
  have hpos := loopHandleDefining_positive hp
  have hbd : ‖x.1‖ ≤ 1 ∧ -3 / 16 < x.2 ∧ x.2 < 19 / 16 :=
    ⟨hpos.2.1.le, hpos.2.2⟩
  have ht := hpos.1
  have hxv : loopActualHandleChart x = loopCircleSection z := loopActualHandleChart.right_inv ht
  have hd : loopActualHandleChart x ∈ loopCircleDomain := by
    rw [hxv]
    exact loopCircleSection_domain z
  have hzproj : loopCircleProjection ⟨loopActualHandleChart x, hd⟩ = z := by
    have he : (⟨loopActualHandleChart x, hd⟩ : loopCircleDomain) =
        ⟨loopCircleSection z, loopCircleSection_domain z⟩ := Subtype.ext hxv
    rw [he, loopCircleSection_projection]
  constructor
  · by_contra hn
    have hdf : loopActualHandleChart (neckFlip false x) ∈ loopCircleDomain := by
      rw [neckFlip_false]
      exact hd
    have hg := loopCapGhost_ballDefining false hbd.1 ⟨hbd.2.1,lt_of_not_ge hn⟩ hdf
    have he : (⟨loopActualHandleChart (neckFlip false x), hdf⟩ : loopCircleDomain) =
        ⟨loopActualHandleChart x, hd⟩ := Subtype.ext (by
          change loopActualHandleChart (neckFlip false x) = loopActualHandleChart x
          rw [neckFlip_false])
    rw [he,hzproj, hb] at hg
    exact lt_irrefl _ hg
  · by_contra hn
    let q : ModelSpace := (x.1, 1 - x.2)
    have heq : neckFlip true q = x := by
      rw [neckFlip_true]
      apply Prod.ext
      · rfl
      · change 1 - (1 - x.2) = x.2
        ring
    have hdq : loopActualHandleChart (neckFlip true q) ∈ loopCircleDomain := by
      rw [heq]
      exact hd
    have hqt : -3 / 16 < q.2 ∧ q.2 < 0 := by
      dsimp only [q]
      constructor <;> linarith [hbd.2.2]
    have hg := loopCapGhost_ballDefining true (show ‖q.1‖ ≤ 1 from hbd.1) hqt hdq
    have he : (⟨loopActualHandleChart (neckFlip true q), hdq⟩ : loopCircleDomain) =
        ⟨loopActualHandleChart x, hd⟩ := Subtype.ext (congrArg loopActualHandleChart heq)
    rw [he,hzproj, hb] at hg
    exact lt_irrefl _ hg

theorem loopBallArcBase_handleNonpos (t : Set.Icc (0 : ℝ) 1) :
    loopHandleDefining (loopBallArcBase t) ≤ 0 := by
  by_contra hn
  have hp := lt_of_not_ge hn
  let z := loopBallArcBase t
  let y := loopActualHandleChart.symm (loopCircleSection z)
  have hpos := loopHandleDefining_positive hp
  have htime := loopHandlePositive_ballZero_time hp (loopBallArcBase_ballZero t)
  let yh : ClosedCell 2 × Set.Icc (0 : ℝ) 1 := (⟨y.1,hpos.2.1.le⟩,⟨y.2,htime⟩)
  have hyv : loopActualHandleChart y = loopCircleSection z :=
    loopActualHandleChart.right_inv hpos.1
  have hym : (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map yh = loopBallAnnulus (1,t) := by
    rw [← loopBallArcBase_section]
    exact (loopActualHandleChart_handle yh).symm.trans hyv
  have hi : loopBallAnnulus (1,t) ∈ Set.range (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map ∩ Set.range (standardLoopBallHandleCycle.ball
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).map :=
    ⟨⟨yh,hym⟩,⟨loopBallLatitudePoint 1 t,rfl⟩⟩
  rw [standardLoopBallHandleCycle.handle_ball_inter] at hi
  have hend : ∃ b : Bool, loopBallAnnulus (1,t) ∈ (standardLoopBallHandleCycle.handle
      ⟨0,standardLoopBallHandleCycle.len_pos⟩).endDisk b := by
    rcases hi with hstart | hend
    · refine ⟨false,?_⟩
      split_ifs at hstart with hcond
      · exact hstart
      · exact False.elim hstart
    · refine ⟨true,?_⟩
      split_ifs at hend with hcond
      · exact hend
      · exact False.elim hend
  obtain ⟨b,w,hw⟩ := hend
  have he := (standardLoopBallHandleCycle.handle
    ⟨0,standardLoopBallHandleCycle.len_pos⟩).injective (hym.trans hw.symm)
  have hnrm := (loopBallAnnulus_endDisk_coordinates b 1 t w hw.symm).1
  have hnorm := congrArg (fun u : ClosedCell 2 × Set.Icc (0 : ℝ) 1 => ‖u.1.val‖) he
  change ‖y.1‖ = ‖w.val‖ at hnorm
  rw [hnrm] at hnorm
  have hlt : ‖y.1‖ < 1 := hpos.2.1
  linarith

theorem loopBallArcBase_coreNonpos (t : Set.Icc (0 : ℝ) 1) :
    loopCoreDefining (loopBallArcBase t) ≤ 0 := by
  have hs : loopBallAnnulus (1,t) ∈ solidTorusSet.{0} := by
    rw [← standardLoopBallHandleCycle_union]
    exact standardLoopBallHandleCycle.ball_subset_union
      ⟨0,standardLoopBallHandleCycle.len_pos⟩ ⟨loopBallLatitudePoint 1 t,rfl⟩
  have hh : cliffordHeight (loopBallAnnulus (1,t)) ≤ 0 := hs
  rw [← loopBallArcBase_section,loopCircleSection_height] at hh
  change 1/8-‖(loopBallArcBase t).val‖^2 ≤ 0
  linarith

theorem loopBallArcBase_cornerBase (t : Set.Icc (0 : ℝ) 1) :
    loopBallArcBase t ∈ loopCircleCornerBase := by
  apply loopCircleCornerBase_sublevel.mpr
  intro l
  fin_cases l
  · exact loopBallArcBase_handleNonpos t
  · exact (loopBallArcBase_ballZero t).le
  · exact loopBallArcBase_coreNonpos t

end GC.GraphManifold.Assembly
