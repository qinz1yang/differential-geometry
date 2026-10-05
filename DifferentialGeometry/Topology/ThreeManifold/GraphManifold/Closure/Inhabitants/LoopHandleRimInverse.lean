import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCircleSection
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelCycle

/-!
The same original nonempty handle chart contains both entire mandated rim boxes.
Its genuine inverse has the prescribed radial and time coordinates at both ends.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Manifold Module DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance handleInverseRank :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

def loopActualHandleChart : PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3)
    ModelSpace SphereCarrier.{0} ∞ :=
  modelHandleChart (ε := 1 / 16) (by norm_num) (by norm_num) (by norm_num) (0 : Fin 1)

theorem loopActualHandleChart_source : loopActualHandleChart.source = zoneDomain :=
  modelHandleChart_source _ _ _ _

theorem loopActualHandleChart_handle (y : ClosedCell 2 × Set.Icc (0 : ℝ) 1) :
    loopActualHandleChart (y.1.val, y.2.val) =
      (standardLoopBallHandleCycle.handle ⟨0, standardLoopBallHandleCycle.len_pos⟩).map y := by
  rw [loopActualHandleChart, modelHandleChart_apply]
  rfl

private theorem handleRim_neck_domain (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    neckRim (1 / 16) (θ, v) ∈ neckDomain (1 / 16) := by
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  have hx := abs_lt.mp hv.1
  have hy := abs_lt.mp hv.2
  have hp : 0 < 1 + (1 / 16 : ℝ) * v.1 := by linarith [hx.1]
  constructor
  · change ‖(1 + (1 / 16 : ℝ) * v.1) • planeOfCircle θ‖ < 1 + 2 * (1 / 16)
    rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg hp.le]
    linarith [hx.2]
  · change |(1 / 16 : ℝ) * v.2| < 2 * (1 / 16)
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]

private theorem handleRim_point (b : Bool) (θ : Circle) (v : ℝ × ℝ) :
    loopActualHandleChart (neckFlip b (neckRim (1 / 16) (θ, v))) =
      standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v) := by
  rw [loopActualHandleChart, modelHandleChart_apply]
  change zoneSphere.{0} 1 (1 / 16) (modelBase (0 : Fin 1))
    (neckFlip b (neckRim (1 / 16) (θ, v))) =
    modelNeck (ε := (1/16 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (0 : Fin 1) b (neckRim (1 / 16) (θ, v))
  rw [modelNeck_apply]

theorem loopActualHandleChart_rim (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)
      ∈ loopActualHandleChart.target := by
  rw [← handleRim_point b θ v]
  apply loopActualHandleChart.map_source
  rw [loopActualHandleChart_source]
  exact neckFlip_mapsTo (by norm_num) (by norm_num) b (handleRim_neck_domain θ hv)

theorem loopActualHandleChart_inverse_rim (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) : loopActualHandleChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)) =
      neckFlip b (neckRim (1 / 16) (θ, v)) := by
  rw [← handleRim_point b θ v]
  apply loopActualHandleChart.left_inv
  rw [loopActualHandleChart_source]
  exact neckFlip_mapsTo (by norm_num) (by norm_num) b (handleRim_neck_domain θ hv)

theorem loopActualHandleChart_inverse_rim_norm (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) : ‖(loopActualHandleChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v))).1‖ = 1 + (1 / 16) * v.1 := by
  rw [loopActualHandleChart_inverse_rim b θ hv]
  have hθ : ‖planeOfCircle θ‖ = 1 := by simp [planeOfCircle]
  have hp : 0 < 1+(1/16 : ℝ)*v.1 := by linarith [(abs_lt.mp hv.1).1]
  cases b <;> simp only [neckFlip_false, neckFlip_true, neckRim, norm_smul, hθ, mul_one,
    Real.norm_of_nonneg hp.le]

theorem loopActualHandleChart_inverse_rim_time (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) : (loopActualHandleChart.symm (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v))).2 =
      if b then 1 - (1 / 16) * v.2 else (1 / 16) * v.2 := by
  rw [loopActualHandleChart_inverse_rim b θ hv]
  cases b <;> rfl

end GC.GraphManifold.Assembly
