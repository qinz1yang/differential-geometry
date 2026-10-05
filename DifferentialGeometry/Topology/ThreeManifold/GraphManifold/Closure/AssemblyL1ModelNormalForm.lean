import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelUnion

/-!
# Chapter-14 assembly, item L1, group G3a: the model cycle normal form

**G3a** (`exists_modelCycleNormalForm`, frozen statement of
`build-logs/scratch/ASM-L1/G3Targets.lean`): for every combinatorial length `len ≥ 1` and every
scale `0 < ε ≤ 1/8`, the standard solid torus of `S³` carries a model cycle normal form
(`modelCycleNormalForm`): the balls, handles and necks of the explicit rotationally symmetric model
in Clifford coordinates, with their charts.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsN_ASML1d : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance diskChartsN_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {len : ℕ} {ε : ℝ}

/-- **The model cycle normal form** of the standard solid torus. -/
def modelCycleNormalForm (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ModelCycleNormalForm.{u} len ε where
  ε_pos := hε
  ε_le := hε'
  neck := modelNeck.{u} hlen hε hε'
  neck_source := modelNeck_source hlen hε hε'
  neck_disjoint := modelNeck_disjoint hlen hε hε'
  ball := modelBall.{u} len ε
  ball_smooth := modelBall_smooth hlen hε hε'
  ball_mfderiv := modelBall_mfderiv hlen hε hε'
  ball_injective := modelBall_injective hlen hε hε'
  handle := modelHandle.{u} len ε
  handle_smooth := modelHandle_smooth hlen hε hε'
  handle_mfderiv := modelHandle_mfderiv hlen hε hε'
  handle_injective := modelHandle_injective hlen hε hε'
  ball_cap := modelBall_cap hlen hε hε'
  handle_end := fun k b q _ => modelHandle_end hlen hε hε' k b q
  neck_ball := fun k b _ hq => modelNeck_mem_range_ball_iff hlen hε hε' k b hq
  neck_handle := fun k b _ hq => modelNeck_mem_range_handle_iff hlen hε hε' k b hq
  neck_union := fun k b _ hq => modelNeck_mem_solidTorusSet_iff hlen hε hε' k b hq
  neck_pieces := modelNeck_pieces hlen hε hε'
  ball_disjoint := modelBall_disjoint hlen hε hε'
  handle_disjoint := modelHandle_disjoint hlen hε hε'
  handle_ball_inter := modelHandle_ball_inter hlen hε hε'
  union_eq := solidTorusSet_eq_modelUnion hlen hε hε'
  ballChart := modelBallChart.{u} hlen hε hε'
  ballChart_source := fun k => by
    rw [modelBallChart_source]
    exact closedBall_subset_ball (by norm_num)
  ballChart_eq := fun k x => (modelBallChart_apply hlen hε hε' k x).symm
  handleChart := modelHandleChart.{u} hlen hε hε'
  handleChart_source := fun k q hq => by
    rw [modelHandleChart_source]
    exact ⟨by linarith [hq.1], by linarith [hq.2.1], by linarith [hq.2.2]⟩
  handleChart_eq := fun k q => (modelHandleChart_apply hlen hε hε' k _).symm

/-- **G3a (frozen statement).** The solid torus of `S³` in the cycle normal form, at every scale. -/
theorem exists_modelCycleNormalForm (len : ℕ) (hlen : 0 < len) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / 8) : Nonempty (ModelCycleNormalForm.{u} len ε) :=
  ⟨modelCycleNormalForm hlen hε hε'⟩

end GC.GraphManifold.Assembly
