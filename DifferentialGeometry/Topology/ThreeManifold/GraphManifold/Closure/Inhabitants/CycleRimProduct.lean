import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleInstance
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
The four rims of the actual two-ball cycle have genuine disk and interval product coordinates.
The chosen linear profiles take every handle-quadrant point into the actual handle domain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem standardBallHandleCycle_rimProduct : standardBallHandleCycle.RimProduct := by
  intro k b
  refine ⟨1, by norm_num, by norm_num,
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)),
    fun x : ℝ => 1 + (1 / 16) * x, fun y : ℝ => (1 / 16) * y,
    contDiff_const.add (contDiff_const.mul contDiff_id),
    contDiff_const.mul contDiff_id, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨by dsimp; linarith [hx.1], ?_⟩
    rw [deriv_const_add, deriv_const_mul_id]
    norm_num
  · intro y _hy
    rw [deriv_const_mul_id]
    norm_num
  · intro θ x y w t _hx _hx0 _hy _hy1 hw ht
    have he : handleEnd b (w, t) = neckRim (1 / 16) (θ, (x, y)) := by
      apply Prod.ext
      · exact hw
      · change endCoord b (t : ℝ) = (1 / 16) * y
        rw [ht]
        cases b <;> simp [endCoord]
    change (modelNeck (len := 2) (ε := (1 / 16 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num) k b) (neckRim (1 / 16) (θ, (x, y))) =
      modelHandle 2 (1 / 16) k (w, t)
    rw [← he]
    exact (modelHandle_end (len := 2) (by norm_num) (by norm_num) (by norm_num) k b (w, t)).symm

end GC.GraphManifold.Assembly
