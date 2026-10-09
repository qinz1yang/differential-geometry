import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallOrbit
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleOrbit

/-!
The padded time-end caps of the original nonempty handle lie strictly inside the same ball.
Their actual global ball defining function is positive, excluding remote common zeros.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance capGeometryRank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem loopCapInverse_norm (b : Bool) (q : ModelSpace) (hτ : -1 < q.2) :
    ‖capInv b q‖ = 1 + q.2 := by
  have hp : 0 ≤ 1 + q.2 := by linarith
  cases b
  · change ‖southCapInv q‖ = 1 + q.2
    rw [southCapInv, norm_smul, Real.norm_of_nonneg hp, norm_eq_of_mem_sphere, mul_one]
  · change ‖reflectThree (southCapInv q)‖ = 1 + q.2
    rw [norm_reflectThree, southCapInv, norm_smul,
      Real.norm_of_nonneg hp, norm_eq_of_mem_sphere, mul_one]

theorem loopCapInverse_height (b : Bool) (q : ModelSpace) :
    (ballCoord (capInv b q)).2 =
      if b then (1 + q.2) * capCos ‖q.1‖ else -(1 + q.2) * capCos ‖q.1‖ := by
  have hh : (ballCoord (southCapInv q)).2 = -(1 + q.2) * capCos ‖q.1‖ := by
    rw [ballCoord_snd, southCapInv, inner_smul_right, real_inner_comm,
      DifferentialGeometry.Topology.Handle.inner_stereoChart_symm]
    unfold capCos
    rw [add_comm 4 (‖q.1‖ ^ 2)]
    ring
  cases b
  · exact hh
  · change (ballCoord (reflectThree (southCapInv q))).2 = (1 + q.2) * capCos ‖q.1‖
    rw [ballCoord_reflectThree]
    change -(ballCoord (southCapInv q)).2 = _
    rw [hh]
    ring

private theorem capGhost_target {q : ModelSpace} (hs : ‖q.1‖ ≤ 1)
    (ht : -3 / 16 < q.2 ∧ q.2 < 0) : q ∈ capTarget := by
  exact ⟨by linarith [ht.1], by linarith⟩

private theorem capGhost_source (b : Bool) {q : ModelSpace}
    (ht : -3 / 16 < q.2 ∧ q.2 < 0) : capInv b q ∈ loopActualBallChart.source := by
  rw [loopActualBallChart_source, mem_ball_zero_iff, loopCapInverse_norm b q (by linarith [ht.1])]
  linarith [ht.2]

private theorem capGhost_model (b : Bool) {q : ModelSpace} (hs : ‖q.1‖ ≤ 1)
    (ht : -3 / 16 < q.2 ∧ q.2 < 0) :
    loopActualBallChart (capInv b q) = loopActualHandleChart (neckFlip b q) := by
  let x := capInv b q
  have hq := capGhost_target hs ht
  have hn : ‖x‖ = 1 + q.2 := loopCapInverse_norm b q hq.1
  have hl : 3 / 4 < ‖x‖ := by rw [hn]; linarith [ht.1]
  have hu : ‖x‖ ≤ 4 / 3 := by rw [hn]; linarith [ht.2]
  have hz : ‖(capMap b x).1‖ < 13 / 10 := by rw [capMap_capInv hq]; linarith
  have hcos : 3 / 5 ≤ capCos ‖q.1‖ := by
    have hh := capCos_le_capCos (norm_nonneg q.1) hs
    norm_num [capCos] at hh
    exact hh
  have hp := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 1 + q.2 by linarith [ht.1])
  have hh : if b then 1 / 4 ≤ (ballCoord x).2 else (ballCoord x).2 ≤ -1 / 4 := by
    rw [loopCapInverse_height]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [ht.1, hp]
  rw [loopActualBallChart, modelBallChart_apply, loopActualHandleChart, modelHandleChart_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, ballSphere, zoneSphere]
  change modelSphere.{0} 1 (ballMap (1 / 16) 0 x) =
    modelSphere.{0} 1 (zoneChartMap (1 / 16) 0 (neckFlip b q))
  cases b
  · change (ballCoord x).2 ≤ -1 / 4 at hh
    have he := ballMap_eq_zoneChartMap_south (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) 0 hl hu hh hz
    rw [capMap_capInv hq] at he
    exact congrArg (modelSphere.{0} 1) he
  · change 1 / 4 ≤ (ballCoord x).2 at hh
    have he := ballMap_eq_zoneChartMap_north (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) 0 hl hu hh hz
    rw [capMap_capInv hq] at he
    have hp : modelSphere.{0} 1 (ballMap (1 / 16) (0 + 4) x) =
        modelSphere.{0} 1 (ballMap (1 / 16) 0 x) := by
      rw [ballMap_add]
      simpa only [Nat.cast_one, Int.cast_one, mul_one] using
        modelSphere_add_period.{0} (by norm_num : 0 < 1) (ballMap (1 / 16) 0 x) (1 : ℤ)
    exact hp.symm.trans (congrArg (modelSphere.{0} 1) he)

theorem loopCapGhost_ballRange (b : Bool) {q : ModelSpace} (hs : ‖q.1‖ ≤ 1)
    (ht : -3 / 16 < q.2 ∧ q.2 < 0) : loopActualHandleChart (neckFlip b q) ∈
    Set.range (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map := by
  let x : ClosedCell 3 := ⟨capInv b q, by
    rw [loopCapInverse_norm b q (by linarith [ht.1])]
    linarith [ht.2]⟩
  refine ⟨x, ?_⟩
  rw [← loopActualBallChart_ball x]
  exact capGhost_model b hs ht

theorem loopCapGhost_ballDefining (b : Bool) {q : ModelSpace} (hs : ‖q.1‖ ≤ 1)
    (ht : -3 / 16 < q.2 ∧ q.2 < 0)
    (hd : loopActualHandleChart (neckFlip b q) ∈ loopCircleDomain) :
    0 < loopBallDefining (loopCircleProjection ⟨loopActualHandleChart (neckFlip b q) , hd⟩) := by
  let x := capInv b q
  have hxs := capGhost_source b ht
  have hp : loopActualBallChart x = loopActualHandleChart (neckFlip b q) := capGhost_model b hs ht
  have hdx : loopActualBallChart x ∈ loopCircleDomain := by rw [hp]; exact hd
  let z := loopCircleProjection ⟨loopActualBallChart x , hdx⟩
  have hz : loopCircleProjection ⟨loopActualHandleChart (neckFlip b q) , hd⟩ = z := by
    apply congrArg loopCircleProjection
    exact Subtype.ext hp.symm
  rw [hz]
  have hct : loopCircleSection z ∈ loopActualBallChart.target := by
    rw [loopBallRotation_section hxs hdx]
    exact loopActualBallChart.map_source (loopBallRotation_source hxs 1)
  rw [loopBallDefining_target hct, loopBallRotation_inverse_norm hxs hdx]
  apply loopBallProfile_pos.mpr
  rw [loopCapInverse_norm b q (by linarith [ht.1])]
  linarith [ht.2]

end GC.GraphManifold.Assembly
