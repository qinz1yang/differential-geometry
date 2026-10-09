import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallLatitude
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideCapChart

/-!
The original actual ball chart reads both entire prescribed rim charts by its true cap inverse.
Its inverse norm and pole height retain the exact native corner coordinates.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology InnerProductSpace
namespace GC.GraphManifold.Assembly

private local instance rimInverseFinrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def loopActualBallChart : PartialDiffeomorph (𝓡 3) (𝓡 3)
    (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{0} ∞ :=
  modelBallChart (ε := (1 / 16)) (by norm_num) (by norm_num) (by norm_num) (0 : Fin 1)

theorem loopActualBallChart_source : loopActualBallChart.source =
    Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (6 / 5) :=
  modelBallChart_source (ε := (1 / 16)) (by norm_num) (by norm_num) (by norm_num) (0 : Fin 1)

theorem loopActualBallChart_ball (x : ClosedCell 3) : loopActualBallChart x.val =
    (standardLoopBallHandleCycle.ball ⟨0, standardLoopBallHandleCycle.len_pos⟩).map x :=
  modelBallChart_apply (ε := (1 / 16)) (by norm_num) (by norm_num) (by norm_num) (0 : Fin 1) x.val

private theorem capInv_norm (b : Bool) (q : ModelSpace) (hτ : -1 < q.2) :
    ‖capInv b q‖ = 1 + q.2 := by
  have hp : 0 ≤ 1 + q.2 := by linarith
  cases b
  · change ‖southCapInv q‖ = 1 + q.2
    rw [southCapInv, norm_smul, Real.norm_of_nonneg hp, norm_eq_of_mem_sphere, mul_one]
  · change ‖reflectThree (southCapInv q)‖ = 1 + q.2
    rw [norm_reflectThree, southCapInv, norm_smul,
      Real.norm_of_nonneg hp, norm_eq_of_mem_sphere, mul_one]

private theorem capInv_height (b : Bool) (q : ModelSpace) :
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

private theorem rimCapNorm (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    ‖(neckRim (1 / 16) (θ, v)).1‖ = 1 + (1 / 16) * v.1 := by
  have hp : 0 ≤ 1 + (1 / 16 : ℝ) * v.1 := by linarith [(abs_lt.mp hv.1).1]
  change ‖(1 + (1 / 16 : ℝ) * v.1) • planeOfCircle θ‖ = _
  rw [norm_smul, Real.norm_of_nonneg hp, planeOfCircle,
    LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

private theorem rimCapTarget (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    neckRim (1 / 16) (θ, v) ∈ capTarget := by
  change -1 < (1 / 16 : ℝ) * v.2 ∧ ‖(neckRim (1 / 16) (θ, v)).1‖ < 2
  rw [rimCapNorm θ hv]
  constructor <;> linarith [(abs_lt.mp hv.1).2, (abs_lt.mp hv.2).1]

private theorem rimCapPoint_norm (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    ‖capInv b (neckRim (1 / 16) (θ, v))‖ = 1 + (1 / 16) * v.2 :=
  capInv_norm b _ (rimCapTarget θ hv).1

private theorem rimCapPoint_source (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    capInv b (neckRim (1 / 16) (θ, v)) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (6 / 5) := by
  rw [mem_ball_zero_iff, rimCapPoint_norm b θ hv]
  linarith [(abs_lt.mp hv.2).2]

private theorem rimCapPoint_height_bound (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    if b then 1 / 4 ≤ (ballCoord (capInv b (neckRim (1 / 16) (θ, v)))).2
      else (ballCoord (capInv b (neckRim (1 / 16) (θ, v)))).2 ≤ -1 / 4 := by
  have hc : 2 / 5 < capCos ‖(neckRim (1 / 16) (θ, v)).1‖ :=
    capCos_gt_of_lt (norm_nonneg _) (by rw [rimCapNorm θ hv]; linarith [(abs_lt.mp hv.1).2])
  have ht : 7 / 8 < 1 + (1 / 16 : ℝ) * v.2 := by linarith [(abs_lt.mp hv.2).1]
  rw [capInv_height]
  cases b
  · change -(1 + (1 / 16 : ℝ) * v.2) * capCos ‖(neckRim (1 / 16) (θ, v)).1‖ ≤ -1 / 4
    nlinarith
  · change 1 / 4 ≤ (1 + (1 / 16 : ℝ) * v.2) * capCos ‖(neckRim (1 / 16) (θ, v)).1‖
    nlinarith

private theorem rimCapPoint_model (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopActualBallChart (capInv b (neckRim (1 / 16) (θ, v))) =
      standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v) := by
  let q := neckRim (1 / 16) (θ, v)
  let x := capInv b q
  have hq : q ∈ capTarget := rimCapTarget θ hv
  have hn := rimCapPoint_norm b θ hv
  have hl : 3 / 4 < ‖x‖ := by rw [hn]; linarith [(abs_lt.mp hv.2).1]
  have hu : ‖x‖ ≤ 4 / 3 := by rw [hn]; linarith [(abs_lt.mp hv.2).2]
  have hz : ‖(capMap b x).1‖ < 13 / 10 := by
    rw [capMap_capInv hq, rimCapNorm θ hv]
    linarith [(abs_lt.mp hv.1).2]
  have hh := rimCapPoint_height_bound b θ hv
  rw [loopActualBallChart, modelBallChart_apply]
  change modelSphere.{0} 1 (ballMap (1 / 16) (modelBase (0 : Fin 1)) x) =
    (modelNeck.{0} (len := 1) (ε := (1 / 16))
      (by norm_num) (by norm_num) (by norm_num) 0 b) q
  rw [modelNeck_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb]
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

theorem loopActualBallChart_rim (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)
      ∈ loopActualBallChart.target := by
  rw [← rimCapPoint_model b θ hv]
  apply loopActualBallChart.map_source
  rw [loopActualBallChart_source]
  exact rimCapPoint_source b θ hv

theorem loopActualBallChart_inverse_rim (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    loopActualBallChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)) =
      capInv b (neckRim (1 / 16) (θ, v)) := by
  rw [← rimCapPoint_model b θ hv]
  apply loopActualBallChart.left_inv
  rw [loopActualBallChart_source]
  exact rimCapPoint_source b θ hv

theorem loopActualBallChart_inverse_rim_norm (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    ‖loopActualBallChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v))‖ = 1 + (1 / 16) * v.2 := by
  rw [loopActualBallChart_inverse_rim b θ hv]
  exact rimCapPoint_norm b θ hv

theorem loopActualBallChart_inverse_rim_height (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    (ballCoord (loopActualBallChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)))).2 =
      if b then (1 + (1 / 16) * v.2) * capCos (1 + (1 / 16) * v.1)
        else -(1 + (1 / 16) * v.2) * capCos (1 + (1 / 16) * v.1) := by
  rw [loopActualBallChart_inverse_rim b θ hv, capInv_height, rimCapNorm θ hv]
  rfl

end GC.GraphManifold.Assembly
