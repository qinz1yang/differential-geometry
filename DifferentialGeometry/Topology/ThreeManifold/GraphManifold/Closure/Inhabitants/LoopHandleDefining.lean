import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleSupport
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleProfile

/-!
The same original nonempty handle defines a globally smooth function on the entire true circle base.
The radial and time cutoff extends constantly outside the actual chart with the full rim value.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem handleDefining_chart (y : ModelSpace) :
    loopActualHandleChart y = modelSphere.{0} 1 (zoneChartMap (1 / 16) 0 y) := by
  rw [loopActualHandleChart, modelHandleChart_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, zoneSphere]

private theorem handleDefining_model_bound {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) : ‖(zoneChartMap (1 / 16) 0 y).1‖ ^ 2 ≤ 2 := by
  rw [loopActualHandleChart_source] at hy
  have hm := zoneChartMap_mem_modelSlab (by norm_num : 0 < (1 / 16 : ℝ))
    (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) (by norm_num : 0 < (1 : ℕ)) 0 hy
  have hn := norm_nonneg (zoneChartMap (1 / 16) 0 y).1
  nlinarith [hm.1]

private theorem handleDefining_axis {y : ModelSpace}
    (hy : y ∈ loopActualHandleChart.source) (he : y.1 = 0) :
    sphereFirst (loopActualHandleChart y) = 0 := by
  rw [handleDefining_chart, sphereFirst_modelSphere 1 (handleDefining_model_bound hy),
    zoneChartMap_apply]
  simp [he, modelFirst, modelPlaneComplex]

private theorem handleInverse_first_nonzero {z : loopCircleBase}
    (ht : loopCircleSection z ∈ loopActualHandleChart.target) :
    (loopActualHandleChart.symm (loopCircleSection z)).1 ≠ 0 := by
  intro he
  have hy := loopActualHandleChart.symm.map_source ht
  have hc := handleDefining_axis hy he
  have hr := loopActualHandleChart.right_inv ht
  change loopActualHandleChart (loopActualHandleChart.symm (loopCircleSection z)) =
    loopCircleSection z at hr
  rw [hr] at hc
  exact loopCircleSection_domain z hc

def loopHandleDefining (z : loopCircleBase) : ℝ := by
  classical
  exact if loopCircleSection z ∈ loopActualHandleChart.target then
    loopHandleProfile ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖
      (loopActualHandleChart.symm (loopCircleSection z)).2 else -1

theorem loopHandleDefining_target {z : loopCircleBase}
    (ht : loopCircleSection z ∈ loopActualHandleChart.target) :
    loopHandleDefining z = loopHandleProfile ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖
      (loopActualHandleChart.symm (loopCircleSection z)).2 := by
  simp only [loopHandleDefining, ite_eq_left ht]

theorem loopHandleDefining_outside {z : loopCircleBase} (hz : z ∉ loopHandleBaseSupport) :
    loopHandleDefining z = -1 := by
  by_cases ht : loopCircleSection z ∈ loopActualHandleChart.target
  · rw [loopHandleDefining_target ht]
    exact loopHandleProfile_outer (loopHandleInverse_outside hz ht)
  · simp only [loopHandleDefining, ite_eq_right ht]

theorem loopHandleDefining_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ loopHandleDefining := by
  intro z
  by_cases ht : loopCircleSection z ∈ loopActualHandleChart.target
  · have hi := (loopActualHandleChart.symm.contMDiffOn_toFun.contMDiffAt
      (loopActualHandleChart.open_target.mem_nhds ht)).comp z
      loopCircleSection_smooth.contMDiffAt
    have hfst := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ModelSpace → ModelPlane))
      |>.contMDiff.contMDiffAt.comp z hi
    have hn := (contDiffAt_norm ℝ (handleInverse_first_nonzero ht)).contMDiffAt.comp z hfst
    have htime := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ModelSpace → ℝ))
      |>.contMDiff.contMDiffAt.comp z hi
    have hp := loopHandleProfile_smooth.contDiffAt.contMDiffAt.comp z
      (hn.prodMk_space htime)
    apply hp.congr_of_eventuallyEq
    filter_upwards [(loopActualHandleChart.open_target.preimage
      loopCircleSection_smooth.continuous).mem_nhds ht] with y hy
    exact loopHandleDefining_target hy
  · have hz : z ∉ loopHandleBaseSupport := fun hz => ht (loopHandleBaseSupport_target hz)
    apply (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [loopHandleBaseSupport_closed.isOpen_compl.mem_nhds hz] with y hy
    exact loopHandleDefining_outside hy

theorem loopHandleDefining_rim (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopHandleDefining (loopBaseCorner b v) = -v.1 := by
  have ht : loopCircleSection (loopBaseCorner b v) ∈ loopActualHandleChart.target := by
    rw [loopCircleSection_rim b hv]
    exact loopActualHandleChart_rim b 1 hv
  rw [loopHandleDefining_target ht, loopCircleSection_rim b hv,
    loopActualHandleChart_inverse_rim_norm b 1 hv, loopActualHandleChart_inverse_rim_time b 1 hv]
  exact loopHandleProfile_rim b hv.1 hv.2

theorem loopHandleDefining_zero {z : loopCircleBase} : loopHandleDefining z = 0 ↔
    loopCircleSection z ∈ loopActualHandleChart.target ∧ loopHandleProfile
      ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖
      (loopActualHandleChart.symm (loopCircleSection z)).2 = 0 := by
  by_cases ht : loopCircleSection z ∈ loopActualHandleChart.target
  · rw [loopHandleDefining_target ht]
    simp only [ht, true_and]
  · simp only [loopHandleDefining, ht, false_and]
    norm_num

theorem loopHandleDefining_zero_bounds {z : loopCircleBase} (hz : loopHandleDefining z = 0) :
    ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖ ≤ 1 ∧
    -3 / 16 < (loopActualHandleChart.symm (loopCircleSection z)).2 ∧
    (loopActualHandleChart.symm (loopCircleSection z)).2 < 19 / 16 :=
  loopHandleProfile_zero_bounds (loopHandleDefining_zero.mp hz).2

end GC.GraphManifold.Assembly
