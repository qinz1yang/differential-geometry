import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallSupport
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallProfile

/-!
The actual original ball defines a globally smooth function on the entire true circle base.
Its radial cutoff extends constantly outside its actual chart and has the prescribed rim value.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private theorem ballChart_center_first :
    sphereFirst (loopActualBallChart (0 : EuclideanSpace ℝ (Fin 3))) = 0 := by
  rw [loopActualBallChart, modelBallChart_apply]
  have hb : modelBase (0 : Fin 1) = 0 := by norm_num [modelBase]
  rw [hb, ballSphere]
  have hc : ballCoord (0 : EuclideanSpace ℝ (Fin 3)) = 0 := map_zero ballCoord
  rw [ballMap_apply,hc]
  simp only [Prod.fst_zero, Prod.snd_zero, smul_zero, sub_zero]
  rw [sphereFirst_modelSphere 1 (by simp)]
  simp [modelFirst, modelPlaneComplex]

private theorem ballInverse_nonzero {z : loopCircleBase}
    (ht : loopCircleSection z ∈ loopActualBallChart.target) :
    loopActualBallChart.symm (loopCircleSection z) ≠ 0 := by
  intro he
  have hr := loopActualBallChart.right_inv ht
  change loopActualBallChart (loopActualBallChart.symm (loopCircleSection z)) =
    loopCircleSection z at hr
  rw [he] at hr
  have hc := congrArg sphereFirst hr
  rw [ballChart_center_first] at hc
  exact loopCircleSection_domain z hc.symm

def loopBallDefining (z : loopCircleBase) : ℝ := by
  classical
  exact if loopCircleSection z ∈ loopActualBallChart.target then
    loopBallProfile ‖loopActualBallChart.symm (loopCircleSection z)‖ else -1

theorem loopBallDefining_target {z : loopCircleBase}
    (ht : loopCircleSection z ∈ loopActualBallChart.target) :
    loopBallDefining z = loopBallProfile ‖loopActualBallChart.symm (loopCircleSection z)‖ := by
  simp only [loopBallDefining, ite_eq_left ht]

theorem loopBallDefining_outside {z : loopCircleBase} (hz : z ∉ loopBallBaseSupport) :
    loopBallDefining z = -1 := by
  by_cases ht : loopCircleSection z ∈ loopActualBallChart.target
  · rw [loopBallDefining_target ht]
    exact loopBallProfile_large (loopBallInverse_outside hz ht).le
  · simp only [loopBallDefining, ite_eq_right ht]

theorem loopBallDefining_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ loopBallDefining := by
  intro z
  by_cases ht : loopCircleSection z ∈ loopActualBallChart.target
  · have hi := (loopActualBallChart.symm.contMDiffOn_toFun.contMDiffAt
      (loopActualBallChart.open_target.mem_nhds ht)).comp z
      loopCircleSection_smooth.contMDiffAt
    have hn := (contDiffAt_norm ℝ (ballInverse_nonzero ht)).contMDiffAt.comp z hi
    have hp := loopBallProfile_smooth.contDiffAt.contMDiffAt.comp z hn
    apply hp.congr_of_eventuallyEq
    filter_upwards [(loopActualBallChart.open_target.preimage
      loopCircleSection_smooth.continuous).mem_nhds ht] with y hy
    exact loopBallDefining_target hy
  · have hz : z ∉ loopBallBaseSupport := fun hz => ht (loopBallBaseSupport_target hz)
    apply (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [loopBallBaseSupport_closed.isOpen_compl.mem_nhds hz] with y hy
    exact loopBallDefining_outside hy

theorem loopBallDefining_rim (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopBallDefining (loopBaseCorner b v) = -v.2 := by
  have ht : loopCircleSection (loopBaseCorner b v) ∈ loopActualBallChart.target := by
    rw [loopCircleSection_rim b hv]
    exact loopActualBallChart_rim b 1 hv
  rw [loopBallDefining_target ht, loopCircleSection_rim b hv,
    loopActualBallChart_inverse_rim_norm b 1 hv]
  exact loopBallProfile_rim hv.2

theorem loopBallDefining_zero {z : loopCircleBase} : loopBallDefining z = 0 ↔
    loopCircleSection z ∈ loopActualBallChart.target ∧
    ‖loopActualBallChart.symm (loopCircleSection z)‖ = 1 := by
  by_cases ht : loopCircleSection z ∈ loopActualBallChart.target
  · rw [loopBallDefining_target ht]
    simp only [ht, true_and, loopBallProfile_zero]
  · simp only [loopBallDefining, ht, false_and]
    norm_num

end GC.GraphManifold.Assembly
