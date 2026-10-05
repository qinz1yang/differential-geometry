import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCapGeometry
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleRegular

/-!
Common zeros of the actual global ball and nonempty handle functions are the true rim centers.
The original handle incidence and actual first-circle section exclude remote intersections.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance commonCornerRank2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

private local instance commonCornerRank3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem loopHandleBall_common_time (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) :
    0 ≤ (loopActualHandleChart.symm (loopCircleSection z)).2 ∧
    (loopActualHandleChart.symm (loopCircleSection z)).2 ≤ 1 := by
  let x := loopActualHandleChart.symm (loopCircleSection z)
  have hbd := loopHandleDefining_zero_bounds hh
  have ht := (loopHandleDefining_zero.mp hh).1
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

theorem loopHandleBall_common_radius (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) :
    ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖ = 1 := by
  have ht := loopHandleBall_common_time z hh hb
  have hs := (loopHandleDefining_zero_bounds hh).1
  have hg := (loopHandleDefining_zero.mp hh).2
  rw [loopHandleProfile_middle (by linarith) ⟨by linarith [ht.1],by linarith [ht.2]⟩] at hg
  linarith

theorem loopHandleBall_common_ranges (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) : loopCircleSection z ∈
    Set.range (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map ∩
    Set.range (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
  have hht := (loopHandleDefining_zero.mp hh).1
  have hhn := (loopHandleDefining_zero_bounds hh).1
  have htime := loopHandleBall_common_time z hh hb
  let y := loopActualHandleChart.symm (loopCircleSection z)
  let yh : ClosedCell 2 × Set.Icc (0 : ℝ) 1 := (⟨y.1, hhn⟩,⟨y.2, htime⟩)
  have hhv : loopActualHandleChart y = loopCircleSection z := loopActualHandleChart.right_inv hht
  have hhtmap := loopActualHandleChart_handle yh
  have hbt := (loopBallDefining_zero.mp hb).1
  have hbn := (loopBallDefining_zero.mp hb).2
  let x := loopActualBallChart.symm (loopCircleSection z)
  let xb : ClosedCell 3 := ⟨x, hbn.le⟩
  have hbv : loopActualBallChart x = loopCircleSection z := loopActualBallChart.right_inv hbt
  have hbtmap := loopActualBallChart_ball xb
  exact ⟨⟨yh, hhtmap.symm.trans hhv⟩,⟨xb, hbtmap.symm.trans hbv⟩⟩

theorem loopHandleBall_common_end (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) :
    ∃ b : Bool, (loopActualHandleChart.symm (loopCircleSection z)).2 = (iccEnd b).val := by
  let k : Fin standardLoopBallHandleCycle.len := ⟨0, standardLoopBallHandleCycle.len_pos⟩
  have hi := loopHandleBall_common_ranges z hh hb
  change loopCircleSection z ∈ Set.range (standardLoopBallHandleCycle.handle k).map ∩
    Set.range (standardLoopBallHandleCycle.ball k).map at hi
  rw [standardLoopBallHandleCycle.handle_ball_inter k k] at hi
  have he : ∃ b : Bool, loopCircleSection z ∈ (standardLoopBallHandleCycle.handle k).endDisk b := by
    rcases hi with hstart | hend
    · refine ⟨false, ?_⟩
      split_ifs at hstart with hcond
      · exact hstart
      · exact False.elim hstart
    · refine ⟨true, ?_⟩
      split_ifs at hend with hcond
      · exact hend
      · exact False.elim hend
  obtain ⟨b, he⟩ := he
  change ∃ w : ClosedCell 2, (standardLoopBallHandleCycle.handle k).map (w, iccEnd b) =
    loopCircleSection z at he
  obtain ⟨w, hw⟩ := he
  have ht := (loopHandleDefining_zero.mp hh).1
  have hn := (loopHandleDefining_zero_bounds hh).1
  have htime := loopHandleBall_common_time z hh hb
  let y := loopActualHandleChart.symm (loopCircleSection z)
  let yh : ClosedCell 2 × Set.Icc (0 : ℝ) 1 := (⟨y.1, hn⟩,⟨y.2, htime⟩)
  have hyv : loopActualHandleChart y = loopCircleSection z := loopActualHandleChart.right_inv ht
  have hym : (standardLoopBallHandleCycle.handle k).map yh = loopCircleSection z :=
    (loopActualHandleChart_handle yh).symm.trans hyv
  have hyeq := (standardLoopBallHandleCycle.handle k).injective (hym.trans hw.symm)
  have hval := congrArg (fun v : ClosedCell 2 × Set.Icc (0 : ℝ) 1 => v.2.val) hyeq
  exact ⟨b, hval⟩

theorem loopHandleBall_common_center (z : loopCircleBase)
    (hh : loopHandleDefining z = 0) (hb : loopBallDefining z = 0) :
    ∃ b : Bool, z = loopBaseCorner b (0, 0) := by
  obtain ⟨b, htime⟩ := loopHandleBall_common_end z hh hb
  have hrad := loopHandleBall_common_radius z hh hb
  have ht := (loopHandleDefining_zero.mp hh).1
  let y := loopActualHandleChart.symm (loopCircleSection z)
  have hy : y ∈ loopActualHandleChart.source := loopActualHandleChart.symm.map_source ht
  have hyv : loopActualHandleChart y = loopCircleSection z := loopActualHandleChart.right_inv ht
  have hd : loopActualHandleChart y ∈ loopCircleDomain := by
    rw [hyv]
    exact loopCircleSection_domain z
  have hzproj : loopCircleProjection ⟨loopActualHandleChart y, hd⟩ = z := by
    have he : (⟨loopActualHandleChart y, hd⟩ : loopCircleDomain) =
        ⟨loopCircleSection z, loopCircleSection_domain z⟩ := Subtype.ext hyv
    rw [he, loopCircleSection_projection]
  have hsec := loopHandleRotation_section hy hd
  rw [hzproj] at hsec
  have hradY : ‖y.1‖ = 1 := hrad
  have htimeY : y.2 = (iccEnd b).val := htime
  have heval : loopHandleRotation y 1 = neckFlip b (neckRim (1 / 16) ((1 : Circle),(0, 0))) := by
    apply Prod.ext
    · cases b <;> change ‖y.1‖ • planeOfCircle 1 = (1+(1 / 16 : ℝ)*0) • planeOfCircle 1
      all_goals rw [hradY]; norm_num
    · change y.2 = (neckFlip b (neckRim (1 / 16) ((1 : Circle),(0, 0)))).2
      rw [htimeY]
      cases b <;> norm_num [iccEnd, neckFlip_false, neckFlip_true, neckRim]
  rw [heval] at hsec
  have hzero : (0, 0) ∈ rimBox 2 := by constructor <;> norm_num
  have hr := loopActualHandleChart.right_inv (loopActualHandleChart_rim b 1 hzero)
  change loopActualHandleChart (loopActualHandleChart.symm (standardLoopBallHandleCycle.rimChart
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1,(0, 0)))) = _ at hr
  rw [loopActualHandleChart_inverse_rim b 1 hzero] at hr
  have hpoint := hsec.trans hr
  have he : (⟨loopCircleSection z, loopCircleSection_domain z⟩ : loopCircleDomain) =
      ⟨standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1,(0, 0)),
        loopRegionRim_domain b 1 (0, 0) hzero⟩ := Subtype.ext hpoint
  have hproj := congrArg loopCircleProjection he
  rw [loopCircleSection_projection, loopRegionRim_projection b 1 (0, 0) hzero] at hproj
  exact ⟨b, hproj⟩

end GC.GraphManifold.Assembly
